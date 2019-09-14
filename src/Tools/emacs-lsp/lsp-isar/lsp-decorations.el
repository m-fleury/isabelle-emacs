;;; -*- lexical-binding: t; -*-

;; Copyright (C) 2018 Mathias Fleury

;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and-or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included in
;; all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.
;;
;;
;;
;;; Code based on
;; https://github.com/cquery-project/emacs-cquery/blob/master/cquery-semantic-highlighting.el
;; especially cquery--publish-semantic-highlighting
;;
;;
;;
;; emacs has two ways to do syntax highlighting:
;; (i) fontification
;; (ii) overlays
;;
;; (i) is in general more efficient than (ii), which is however more
;; faithful. However, (i) messes up with the prettification of symbols
;; (replacing '\<open>' by its UTF8 counterpart). It also does not
;; provide a way to remove only some fonts, forcing to readd every
;; decoration on the whole buffer at each change. This was way to slow
;; on non-trivial buffers. Therefore, this was killed.
;;
;; (ii) was a bit better (we could open medium-size buffers), but the
;; most simple version (as currently done in cquery, i.e. repainting
;; every overlay at each update from the LSP server) did not scale for
;; large buffers, where editing became unbearably slow. This problem
;; is partly solved in the devel version of emacs (emacs27),
;; especially the noverlay branch.
;;
;;
;;
;; Critical points
;;
;; (i) we repaint only the "diffs" between colorations when receiving
;; the new intervals to be highlighted. This worked even for larger
;; buffers (but can still be slow in some cases).
;;
;; (ii) We don't delete the overlays when we have to remove
;; it. Instead, we remove the properties of the overlays to make the
;; overlay invisible. Then we recycle them, instead of creating new
;; overlays. This is much faster than deleting them. This makes adding
;; overlays less efficient, but basically the cost is smaller.
;;
;; (iii) recycling is done is a timer to avoid blocking the main
;; thread. It is done in small batches (recycling can take a few
;; minutes on a large buffer).
;;
;; TODO:
;;
;;   - how the hell does define-inline work?
;;
;;   - when clausing overlays, we let the GC do its job, but it might
;;   be worth using a timer as for the recyling.
;;
;;
;; Some comments on the faces:
;;
;; 1. setting faces is *hard*. There are currently chosen to play
;; reasonnably with a dark background (monokai-theme or
;; spacemacs). The light colors are based on the solarized (light)
;; color palette.
;;
;; 2. Setting the background make the lines visible, but also means
;; that that highlighting is /broken/: currently when the whole region
;; is highlighted, then the highlighting is not visible. Therefore, we
;; currently only set backgrounds for important messages (running,
;; errors, and unprocessed).
;;
;; More efficient LISP code:
;; https://nullprogram.com/blog/2017/01/30/

;; Because we need tail call optimisation:
(setq lexical-binding 't)

;; file -> type -> [range, decoration] list
(defvar-local lsp-isar--sem-overlays (make-hash-table :test 'equal)
  "decoration cache.")

;; file -> overlays list
(defvar-local lsp-isar--deleted-overlays (make-hash-table :test 'equal)
  "decoration overlays that have to be recycled.")

;; file -> overlays list
(defvar-local lsp-isar--recycled-overlays (make-hash-table :test 'equal)
  "decoration overlays that can be reused.")

;; file -> timer
(defvar-local lsp-isar--recyclers (make-hash-table :test 'equal)
  "timers that recycle overlays or delete them when a buffer is closed.")

;; prettifyng the source
(defgroup lsp-isar-sem nil
  "Isabelle semantic highlighting."
  :group 'tools)


(defface lsp-isar-font-background-unprocessed1
  '((((class color) (background dark)) :background "#610061")
    (((class color) (background light)) :background "#002b36")
    (t :priority 0))
  "The face used to mark inactive regions."
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-unprocessed
  '((((class color) (background dark)) :background "#ffa000")
    (((class color) (background light)) :background "#002b36")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-running1
  '((((class color) (background dark)) :background "#ffa0a0")
    (((class color) (background light)) :background "#eee8d5")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-bad
  '((((class color) (background dark)) :background "#ee7621")
    (((class color) (background light)) :background "#dc322f")
    (t :priority 5))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-intensify
  '((((class color) (background dark)) :foreground "#cc8800")
    (((class color) (background light)) :foreground "#cc8800")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-quoted
  '((((class color) (background dark)) :foreground "#969696")
    (((class color) (background light)) :foreground "#eee8d5")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-antiquoted
  '((((class color) (background dark)) :foreground "#ffd666")
    (((class color) (background light)) :foreground "#ffd666")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-markdown-bullet1
  '((((class color) (background dark)) :foreground "#05c705")
    (((class color) (background light)) :foreground "#268bd2")
    (t :priority 0 :inherit true))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-markdown-bullet2
  '((((class color) (background dark)) :foreground "#cc8f00")
    (((class color) (background light)) :foreground "#2aa198")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-markdown-bullet3
  '((((class color) (background dark)) :foreground "#0000cc")
    (((class color) (background light)) :foreground "#859900")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-markdown-bullet4
  '((((class color) (background dark)) :foreground "#cc0069")
    (((class color) (background light)) :foreground "#cb4b16")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-foreground-quoted
  '((((class color) (background dark)) :background "#402b36")
    (t :priority 0))
  "Font used inside quotes and cartouches"
  :group 'lsp-isar-sem)


(defface lsp-isar-font-foreground-antiquoted
  '((t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-dotted-writeln
  '((((class color) (background dark)) :underline "#c0c0c0")
    (((class color) (background light)) :underline "#c0c0c0")
    (t :priority 2))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-dotted-information
  '((((class color) (background dark)) :underline "#c1dfee")
    (((class color) (background light)) :underline "#c1dfee")
    (t :priority 2))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-dotted-warning
  '((((class color) (background dark)) :underline t)
    (((class color) (background light)) :underline t)
    (t :priority 2))
  ""
  :group 'lsp-isar-sem)


;; this font does not exist,but should allow to discover if
;; some new font was added to isabelle
(defface lsp-isar-font-default
  '((((class color) (background dark)) :foreground "green" :underline t)
    (((class color) (background light)) :foreground "#657b83" :underline t)
    (t :priority 0))
  "Unused default font: useful to see if Isabelle uses new font
classes."
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-main
  '((((class color) (background dark)) :foreground "#d4d4d4")
    (((class color) (background light)) :foreground "#657b83")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-keyword1
  '((((class color) (background dark)) :foreground "#c586c0")
    (((class color) (background light)) :foreground "#268bd2")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-keyword2
  '((((class color) (background dark)) :foreground "#b5cea8")
    (((class color) (background light)) :foreground "#2aa198")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-keyword3
  '((((class color) (background dark)) :foreground "#4ec9b0")
    (((class color) (background light)) :foreground "#cb4b16")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-quasi_keyword
  '((((class color) (background dark)) :foreground "#cd3131")
    (((class color) (background light)) :foreground "#859900")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-improper
  '((((class color) (background dark)) :foreground "#f44747")
    (((class color) (background light)) :foreground "#d33682")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-operator
  '((((class color) (background dark)) :foreground "#d4d4d4")
    (((class color) (background light)) :foreground "#b58900")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-tfree
  '((((class color) (background dark)) :foreground "#a020f0")
    (((class color) (background light)) :foreground "#a020f0")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-tvar
  '((((class color) (background dark)) :foreground "#a020f0")
    (((class color) (background light)) :foreground "#a020f0")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-free
  '((((class color) (background dark)) :foreground "#569cd6")
    (((class color) (background light)) :foreground "#2aa198")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-skolem
  '((((class color) (background dark)) :foreground "#d2691e")
    (((class color) (background light)) :foreground "#d2691e")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-bound
  '((((class color) (background dark)) :foreground "#608b4e")
    (((class color) (background light)) :foreground "#608b4e")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-var
  '((((class color) (background dark)) :foreground "#9cdcfe")
    (((class color) (background light)) :foreground "#268bd2")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-inner_numeral
  '((((class color) (background dark)) :foreground "#b5cea8")
    (((class color) (background light)) :foreground "#b5cea8")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-inner_quoted
  '((((class color) (background dark)) :foreground "#ce9178")
    (((class color) (background light)) :foreground "#ce9178")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-inner_cartouche
  '((((class color) (background dark)) :foreground "#d16969")
    (((class color) (background light)) :foreground "#d16969")
    (t :priority 0 :inherit default))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-inner_comment
  '((((class color) (background dark)) :foreground "#608b4e")
    (((class color) (background light)) :foreground "#608b4e")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-dynamic
  '((((class color) (background dark)) :foreground "#dcdcaa")
    (((class color) (background light)) :foreground "#dcdcaa")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-class_parameter
  '((((class color) (background dark)) :foreground "#d2691e")
    (((class color) (background light)) :foreground "#d2691e")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-antiquote
  '((((class color) (background dark)) :foreground "#c586c0")
    (((class color) (background light)) :foreground "#c586c0")
    (t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defface lsp-isar-font-text-overview-unprocessed
  '((((class color) (background dark)) :background "#610061")
    (((class color) (background light)) :background "#839496")
    (t :priority 5))
  ""
  :group 'lsp-isar-sem)

(defface lsp-isar-font-text-overview-running
  '((((class color) (background dark)))
    (((class color) (background light)))
    (t :priority 5 :box t))
  ""
  :group 'lsp-isar-sem)

(defface lsp-isar-font-text-overview-error
  '((((class color) (background dark)) :background  "#b22222")
    (((class color) (background light)) :background "#b22222" )
    (t :priority 5))
  ""
  :group 'lsp-isar-sem)

(defface lsp-isar-font-text-overview-warning
  '((((class color) (background dark)) :foreground "#ff8c00")
    (((class color) (background light)) :foreground "#ff8c00")
    (t :priority 5))
  ""
  :group 'lsp-isar-sem)

(defface lsp-isar-font-spell-checker
  '((((class color) (background dark)) :foreground "#569cd6")
    (((class color) (background light)) :foreground "#569cd6")
    (t :priority 5))
  ""
  :group 'lsp-isar-sem)

(defface lsp-isar-font-nothing
  '((t :priority 0))
  ""
  :group 'lsp-isar-sem)


(defvar-local lsp-isar-get-font
  '(("background_unprocessed1"  . lsp-isar-font-background-unprocessed1)
    ("background_running1"  . lsp-isar-font-background-running1)
    ("background_bad"  . lsp-isar-font-background-bad)
    ("background_intensify"  . lsp-isar-font-background-intensify)
    ("background_quoted"  . lsp-isar-font-background-quoted)
    ("background_antiquoted"  . lsp-isar-font-background-antiquoted)
    ("background_markdown_bullet1"  . lsp-isar-font-background-markdown-bullet1)
    ("background_markdown_bullet2"  . lsp-isar-font-background-markdown-bullet2)
    ("background_markdown_bullet3"  . lsp-isar-font-background-markdown-bullet3)
    ("background_markdown_bullet4"  . lsp-isar-font-background-markdown-bullet4)


    ("foreground_quoted"  . lsp-isar-font-foreground-quoted)
    ("foreground_antiquoted"  . lsp-isar-font-foreground-antiquoted)
    ("dotted_writeln"  . lsp-isar-font-dotted-writeln)

    ("dotted_information"  . lsp-isar-font-dotted-information)
    ("dotted_warning"  . lsp-isar-font-dotted-warning)


    ("text_main"  . lsp-isar-font-text-main)

    ("text_keyword1"  . lsp-isar-font-text-keyword1)

    ("text_keyword2"  . lsp-isar-font-text-keyword2)
    ("text_keyword3"  . lsp-isar-font-text-keyword3)
    ("text_quasi_keyword"  . lsp-isar-font-text-quasi_keyword)
    ("text_improper"  . lsp-isar-font-text-improper)
    ("text_operator"  . lsp-isar-font-text-operator)
    ("text_tfree"  . lsp-isar-font-text-tfree)
    ("text_tvar"  . lsp-isar-font-text-tvar)
    ("text_free"  . lsp-isar-font-text-free)
    ("text_skolem"  . lsp-isar-font-text-skolem)
    ("text_bound"  . lsp-isar-font-text-bound)
    ("text_var"  . lsp-isar-font-text-var)
    ("text_inner_numeral"  . lsp-isar-font-text-inner_numeral)
    ("text_inner_quoted"  . lsp-isar-font-text-inner_quoted)
    ("text_inner_cartouche"  . lsp-isar-font-text-inner_cartouche)
    ("text_inner_comment"  . lsp-isar-font-text-inner_comment)
    ("text_dynamic"  . lsp-isar-font-text-dynamic)
    ("text_class_parameter"  . lsp-isar-font-text-class_parameter)
    ("text_antiquote"  . lsp-isar-font-text-antiquote)

    ("text_overview_unprocessed"  . lsp-isar-font-text-overview-unprocessed)
    ("text_overview_running"  . lsp-isar-font-text-overview-running)
    ("text_overview_error"  . lsp-isar-font-text-overview-error)
    ("text_overview_warning"  . lsp-isar-font-text-overview-warning)

    ("spell_checker"  . lsp-isar-font-spell-checker)))

(defsubst ranges-are-equal (r1 r2)
  (let ((r2p (car r2))) ;; ignore the overlay
    (let ((x0 (elt r1 0)) (y0 (car r2p)))
      (and (= x0 y0) (= (elt r1 1) (cadr r2p))))))


(defsubst point-is-before (x0 y0 x1 y1)
  (if (/= x0 x1)
      (< x0 x1)
    (< y0 y1)))

;; Ranges cannot overlap
(defsubst range-is-before (r1 r2)
  (let ((r2p (car r2)))
    (and (point-is-before (elt r1 0) (elt r1 1) (car r2p) (cadr r2p))
	 ;;(point-is-before (elt r1 2) (elt r1 3) (caddr r2p) (cadddr r2p))
	 )))


;; This is a full cleaning of all buffers.  This is too costly to run
;; regularly. Therefore, we run it after some time of idling.
;; Remark that this is still important to run.
(defun lsp-isar-kill-all-unused-overlays-file (file)
  "Remove all overlays that are deleted or recycled: They are
deleted from the buffer and from the hashtables where they appear
and should be GC-ed by emacs.

CAUTION: this can be slow."
  (let*
      ((recycled-overlays (gethash file lsp-isar--recycled-overlays nil))
       (deleted-overlays (gethash file lsp-isar--deleted-overlays nil)))
    (puthash file nil lsp-isar--deleted-overlays)
    (puthash file nil lsp-isar--recycled-overlays)
    ;; to allow interuptions.
    (dolist (ov deleted-overlays) (delete-overlay ov))
    (dolist (ov recycled-overlays) (delete-overlay ov))))

(defun lsp-isar-kill-all-unused-overlays ()
  (interactive)
  (message "Cleaning all decorations. Set lsp-isar-cleaner-timer increase the delay two of them.")
  (maphash (lambda (file _v) (lsp-isar-kill-all-unused-overlays-file file)) lsp-isar--deleted-overlays))

(defcustom lsp-isar-full-clean-ran-every 120
  "Full clean every some many seconds. Use nil to deactivate it.")

(defvar lsp-isar--cleaner-timer nil
  "Timer to clean all elements. Set lsp-isar-cleaner-ran-every so to never start the timer.")


;; recycle by batch of a small number of elements. This is run on a
;; regural basis.
(defun lsp-isar-recycle-batch (file)
  (let*
      ((recycled-overlays (gethash file lsp-isar--recycled-overlays nil))
       (deleted-overlays (gethash file lsp-isar--deleted-overlays nil))
       (m (length recycled-overlays))
       (n 0))
    (with-timeout (0.1 nil)
      (while
	  (and
	   (< n 10)
	   deleted-overlays)
	(let ((ov (pop deleted-overlays)))
	  (delete-overlay ov)
	  (if (< m 1000) (push ov recycled-overlays))
	  (setq n (1+ n)))))
    (puthash file deleted-overlays lsp-isar--deleted-overlays)
    (puthash file recycled-overlays lsp-isar--recycled-overlays)))

(defun lsp-isar-recycle-timer (file)
  (lsp-isar-recycle-batch file)
  (let ((deleted-ov (gethash file lsp-isar--deleted-overlays))
	(timer (gethash file lsp-isar--recyclers)))
    (unless deleted-ov
      (progn
	(cancel-timer timer)
	(puthash file nil lsp-isar--recyclers)))))

;; started as a the equivalent of the cquery version. Later changed a lot.
;; ASSUMPTIONS:
;;  * old-overlays it sorted (for performance reasion).
;;  * old-overlays contains all decorations corresponding to 'typ'
;;    in 'buffer' and they have not already been deleted.
;;
;; The number of markup generated by Isabelle is extremely high and
;; overlays are slow. The noverlay branch of emacs devel (emacs27)
;; solves the problem. However, on emacs26, deleting and repainting
;; the markup (as currently done in cquery) is way too slow to be
;; usable. Therefore, we only reprint the markup that changed, which
;; is much more complicated. However, it seems to solves the problem.
;;
;;
;; The core function is 'find-new-and-repaint'. Given the old decoration:
;; A   B   C   D      F   G   H   I  J  K  L  M
;; and the new:
;; A   B   C      E   F   G   H'  I  J
;;
;; we assume that the ranges are sorted and align them as shown. We
;; iterate over the two lists and there are several cases:
;;   1. A = A: nothing to do.
;;   2. there are more old: delete the remaining;
;;   3. there are more new: just print them;
;;   4. D < E: we delete D and continue the iteration (keeping E
;;   in the new decorations);
;;   5. otherwise, the ranges intersect: we delete H' and add H.
;;
;; Exceptional cases:
;;
;;   6. while printing the overlay, we find out that the position is
;;   not valid anymore in the current buffer: we delete all further
;;   old decorations, stop, and wait for the next update from Isabelle.
;;
;; The function 'find-new-and-repaint' iterates over the old
;; decorations and the new ranges. It finds out if a range already had
;; a decoration (which does not require changes), if a range needs a
;; new decoration (which must be added), or if not decoration is
;; required anymore (the old one gets deleted).
;;
;;
;; The end_char_offset is here to improve readability: as we do not
;; merge overlays the error marker will continue at the end of the
;; command. This should help identifying the line with the error.
;;
;; find-range-and-add-to-print contains a 'bug' that is due to the
;; way emacs handles the current point: forward-char and forward-line
;; return (point-max) when overflowing. Except when the current point
;; does not exist anymore, then an exception end-of-buffer is raised.
;;
;;
;; Deleting overlays is so incredibly slow. This is an issue in emacs
;; and there is no proper work-around. Basically, overlays are
;; quadratic in their number.  There is some discussion on
;; https://github.com/cquery-project/cquery/wiki/Emacs.  90% (> 10s)
;; of the time is spent deleting overlays when jumping to the top of
;; buffer and adding a space. In the noverlay branch, it is only 2% of
;; the time.
;;
;; Removed overlays are:
;;    1. first moved to lsp-isar--deleted-overlays
;;    2. then deleted from the overlays
;;    3. added to lsp-isar--recycled-overlays to be reused
;;
;; 2 and 3 are run in lsp-isar-recycle-timer. It is run by a timer to avoid
;; blocking emacs. It then cancels itself when there is nothing to do.
(defun lsp-isar-update-cached-decorations-overlays (params)
  (let* ((file (replace-regexp-in-string (regexp-quote "/local/local") "/local" (lsp--uri-to-path (gethash "uri" params)) nil 'literal))
         (buffer (find-buffer-visiting file))
         (pranges (gethash "content" params nil))
	 (typ (gethash "type" params "default"))
	 (face (cdr (assoc typ lsp-isar-get-font)))
	 (end_char_offset (if (or (equal typ "text_overview_error") (equal typ "text_overview_running")) 1 0))
	 )

    (if (not buffer) ;; buffer was closed/not found
	(let ((timer (gethash file lsp-isar--recyclers)))
	  (if timer
	      (cancel-timer timer))
	  (puthash file nil lsp-isar--recyclers)
	  ;; let the GC kill the decorations for us:
	  (puthash file nil lsp-isar--deleted-overlays)
	  (puthash file nil lsp-isar--recycled-overlays))

      ;; faster adding and deleting of overlays
      (overlay-recenter (point))

      ;; extract the ranges
      (let (ranges point0 point1 (line 0) (curoverlays nil)
		   (inhibit-field-text-motion t))
	(if (equal face 'lsp-isar-font-default)
	    (message "unrecognised color %s" typ))
	(seq-doseq (range pranges)
	  (-let ((cr (gethash "range" range)))
	    (push cr ranges)))

	;; Sort by start-line ASC, start-character ASC.
	;; the ranges are not overlapping
	(setq ranges
	      (sort ranges (lambda (x y)
			     (let ((x0 (elt x 0)) (y0 (elt y 0)))
			       (if (/= x0 y0)
				   (< x0 y0)
				 (< (elt x 1) (elt y 1)))))))

	;; convert array to list if :use-native-json is t
	(setq pranges (append pranges nil))

	;; reprint
	(-let*
	    ((current-file-overlays (gethash file lsp-isar--sem-overlays (make-hash-table :test 'equal)))
	     (old-overlays (gethash typ current-file-overlays nil))
	     (recycled-overlays (gethash file lsp-isar--recycled-overlays nil))
	     (deleted-overlays (gethash file lsp-isar--deleted-overlays nil)))

	  ;; recycle an old overlay by moving and updating it,
	  ;; otherwise, create a new one
	  (defsubst new-or-recycle-overlay (point0 point1 face)
	    (if recycled-overlays
		(progn
		  (let ((ov (pop recycled-overlays)))
		    (move-overlay ov point0 point1)
		    (overlay-put ov 'face face)
		    ov))
	      (let ((ov (make-overlay point0 point1)))
		(overlay-put ov 'face face)
		ov)))

	  ;; if a range is new, find it in the buffer and print it
	  ;; if the current range is already not valid, return nil
	  (defsubst find-range-and-add-to-print (range)
	    (ignore-errors
	      (let ((l0 (elt range 0))
		    (c0 (elt range 1))
		    (l1 (elt range 2))
		    (c1 (elt range 3)))
		(forward-line (- l0 line))
		(forward-char c0)
		(setq point0 (point))
		(forward-line (- l1 l0))
		(forward-char (+ c1 end_char_offset))
		(setq point1 (point))
		(setq line l1)

		(let ((ov (new-or-recycle-overlay point0 point1 face)))
		  (assert (overlayp ov))
		  (push (list (list l0 c0 l1 c1) ov) curoverlays))
		t)))

	  ;; This function iterates over huge lists and therefore
	  ;; requires either tail-call optimisation or a while loop
	  ;; (several thousand elements are common). Therefore, no
	  ;; recursive function works.
	  (defsubst find-new-and-repaint (news olds)
	    (while (or news olds)
	      (if (not news)
		  ;; no news: discard all old decorations
		  (progn
		    ;; faster adding and deleting of overlays
		    (overlay-recenter (point-max))
		    (dolist (x olds)
		      ;;(delete-overlay (cadr x))
		      (overlay-put (cadr x) 'face 'lsp-isar-font-nothing)
		      (push (cadr x) deleted-overlays))
		    (setq olds nil))
		(if (not olds)
		    ;; no olds: print all news
		    (progn
		      (dolist (x news)
			(find-range-and-add-to-print x))
		      (setq news nil))
		  ;; otherwise, compare the first two ranges
		  (let ((r1 (car news))
			(r2 (car olds)))
		    ;; if the ranges are equal no need to repaint
		    (if (ranges-are-equal r1 r2)
			(progn
			  (push r2 curoverlays)
			  (setq news (cdr news))
			  (setq olds (cdr olds)))
		      ;; if r1 < r2, print r1 and continue iteration
		      (if (range-is-before r1 r2)
			  (progn
			    (if (find-range-and-add-to-print r1)
				(setq news (cdr news))
			      ;; else the content is not valid anymore:
			      (progn
				;; faster adding and deleting of overlays
				(overlay-recenter (point-max))
				(cl-loop for x in olds do
					 ;;(delete-overlay (cadr x))
					 (overlay-put (cadr x) 'face 'lsp-isar-font-nothing)
					 (push (cadr x) deleted-overlays))
				(setq news nil)
				(setq olds nil))))
			;; otherwise, r1 is after the beginng of r2,
			;; so remove r2 and continue (r1 might just be later in olds)
			(progn
			  ;;(message "number of elts in olds: %s" (length olds))
			  ;;(message "wanted to print: %s skipped: %s" r1 r2)
			  ;;(delete-overlay (cadr r2))
			  (overlay-put (cadr r2) 'face 'lsp-isar-font-nothing)
			  (push (cadr r2) deleted-overlays)
			  (setq olds (cdr olds))))))))))


	  (save-excursion
	    (with-current-buffer buffer
	      (with-silent-modifications
		;; find all new overlays
		(widen)
		(goto-char 1)
		(find-new-and-repaint ranges old-overlays)

		;; the curoverlays are sorted in reversed order
		(puthash typ (nreverse curoverlays) current-file-overlays)
		(puthash file current-file-overlays lsp-isar--sem-overlays)
		(puthash file recycled-overlays lsp-isar--recycled-overlays)
		(puthash file deleted-overlays lsp-isar--deleted-overlays)))))
	(let ((timer (gethash file lsp-isar--recyclers)))
	  (unless timer
	    (progn
	      (let ((timer (run-with-timer 0 0.5 'lsp-isar-recycle-timer file)))
		(puthash file timer lsp-isar--recyclers)))))))))

(defun lsp-isar-update-and-reprint (_workspace params)
  "Updates the decoration cach and the reprint all decorations"
  (lsp-isar-update-cached-decorations-overlays params))


;; This function can be called several times!
(defun lsp-isar--init-decorations ()
  "Initialise all elements required for the decorations."
  (if (and (> lsp-isar-full-clean-ran-every 0) (not lsp-isar--cleaner-timer))
    (setq lsp-isar--cleaner-timer (run-with-idle-timer lsp-isar-full-clean-ran-every t 'lsp-isar-kill-all-unused-overlays))))

(provide 'lsp-decorations)
