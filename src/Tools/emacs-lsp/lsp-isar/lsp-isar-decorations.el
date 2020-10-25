;;; lsp-isar-decorations.el --- Add syntax highlighting -*- lexical-binding: t; -*-

;; Author: Mathias Fleury <mathias.fleury@protonmail.com>
;; URL: https://bitbucket.org/zmaths/isabelle2019-vsce/

;; Keywords: lisp
;; Version: 0

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
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.
;;
;;
;;

;;; Commentary:

;; Code based on
;; https://github.com/cquery-project/emacs-cquery/blob/master/cquery-semantic-highlighting.el
;; especially cquery--publish-semantic-highlighting
;;
;;
;;
;; Emacs has two ways to do syntax highlighting:
;; (i) fontification
;; (ii) overlays
;;
;; (i) is in general more efficient than (ii), which is however more
;; faithful.  However, (i) messes up with the prettification of symbols
;; (replacing '\<open>' by its UTF8 counterpart).  It also does not
;; provide a way to remove only some fonts, forcing to readd every
;; decoration on the whole buffer at each change.  This was way to slow
;; on non-trivial buffers.  Therefore, this was killed.
;;
;; (ii) was a bit better (we could open medium-size buffers), but the
;; most simple version (as currently done in cquery, i.e.  repainting
;; every overlay at each update from the LSP server) did not scale for
;; large buffers, where editing became unbearably slow.  This problem
;; is partly solved in the devel version of Emacs (Emacs27),
;; especially the noverlay branch.
;;
;;
;; The overlay problem
;;
;; In Emacs, overlays are in a doubly-linked list (the markers).  This
;; means that removing overlays from a buffer is inefficient.  In the
;; current implementation, removing many of them has a quadratic cost
;; (large buffer have 200 000 markers).  However, reusing overalys in
;; the same buffer has no cost, except for a very high memory usage
;; and more work for the code displaying buffers (as far as I know,
;; this is not an issue for us).
;;
;;
;; Critical points
;;
;; (i) we repaint only the "diffs" between colorations when receiving
;; the new intervals to be highlighted.  This worked even for larger
;; buffers (but can still be slow in some cases).
;;
;; (ii) We don't delete the overlays when we have to remove
;; it.  Instead, we remove the properties of the overlays to make the
;; overlay invisible.  Then we reuse (recycle) them, instead of
;; creating new overlays.  This is much faster than deleting them.  This
;; makes adding overlays less efficient, but basically the cost is
;; smaller.  Remark that overlays are only reused in the buffer they
;; were removed from.
;;
;; (iii) after some minutes of inactivity, we delete all unused
;; overlays.
;;
;; (iv) recycling overlays (and keeping only a certain number of some
;; of them) avoids using too much memory (I have seen usage of >10GB).
;; We use only _one_ recycler timer to avoid having too many timers
;; running at the same time (only relevant with many opened files).
;;
;;
;;
;; TODO:
;;
;;   - how the hell does define-inline work?
;;
;;   - when killing overlays, we let the GC do its job, but it might
;;   be worth using a timer for the recyling.
;;
;;   - the timer to delete overlays is not really necessary anymore,
;;   because it is superseeded by the function killing all overlays.
;;   Try that out when running Emacs for a long time without break.
;;
;;
;; Some comments on the faces:
;;
;; 1.  setting faces is *hard*.  There are currently chosen to play
;; reasonnably with a dark background (monokai-theme or
;; spacemacs).  The light colors are based on the solarized (light)
;; color palette.
;;
;; 2.  Setting the background make the lines visible, but also means
;; that that highlighting is /broken/: currently when the whole region
;; is highlighted, then the highlighting is not visible.  Therefore, we
;; currently only set backgrounds for important messages (running,
;; errors, and unprocessed).
;;
;; More efficient LISP code:
;; https://nullprogram.com/blog/2017/01/30/

;;; Code:

(require 'lsp-mode)
(require 'lsp-isar-types)

;; file -> type -> [range, decoration] list
(defvar lsp-isar-decorations--sem-overlays (make-hash-table :test 'equal)
  "Decoration cache.")

;; file -> overlays list
(defvar lsp-isar-decorations--overlays-to-reuse (make-hash-table :test 'equal)
  "Decoration overlays that can be reused.")

;; file -> overlays list
(defvar lsp-isar-decorations--delayed-overlays (make-hash-table :test 'equal)
  "Decoration overlays that can be reused.")

;; file -> timer
(defvar lsp-isar-decorations--recycler nil
  "Timer to slowly delete overlays from the last opened buffer.")

(defcustom lsp-isar-decorations-delayed-printing nil
  "Don't update the decorations of non-visible buffers."
  :group 'isabelle
  :type 'bool)


(defface lsp-isar-font-background-unprocessed1
  `((((class color) (background dark)) :background "#610061")
    (((class color) (background light)) :background "#002b36")
    (t :priority 0))
  "The face used to mark inactive regions."
  :group 'lsp-isar-sem)


(defface lsp-isar-font-background-unprocessed
  `((((class color) (background dark)) :background "#ffa000")
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
  '((((class color) (background dark)) :underline nil)
    (((class color) (background light)) :underline nil)
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


(defvar-local lsp-isar-decorations-get-font
  '(("background_unprocessed1"  .  lsp-isar-font-background-unprocessed1)
    ("background_running1"  .  lsp-isar-font-background-running1)
    ("background_bad"  .  lsp-isar-font-background-bad)
    ("background_intensify"  .  lsp-isar-font-background-intensify)
    ("background_quoted"  .  lsp-isar-font-background-quoted)
    ("background_antiquoted"  .  lsp-isar-font-background-antiquoted)
    ("background_markdown_bullet1"  .  lsp-isar-font-background-markdown-bullet1)
    ("background_markdown_bullet2"  .  lsp-isar-font-background-markdown-bullet2)
    ("background_markdown_bullet3"  .  lsp-isar-font-background-markdown-bullet3)
    ("background_markdown_bullet4"  .  lsp-isar-font-background-markdown-bullet4)

    ("foreground_quoted"  .  lsp-isar-font-foreground-quoted)
    ("foreground_antiquoted"  .  lsp-isar-font-foreground-antiquoted)
    ("dotted_writeln"  .  lsp-isar-font-dotted-writeln)

    ("dotted_information"  .  lsp-isar-font-dotted-information)
    ("dotted_warning"  .  lsp-isar-font-dotted-warning)

    ("text_main"  .  lsp-isar-font-text-main)

    ("text_keyword1"  .  lsp-isar-font-text-keyword1)

    ("text_keyword2"  .  lsp-isar-font-text-keyword2)
    ("text_keyword3"  .  lsp-isar-font-text-keyword3)
    ("text_quasi_keyword"  .  lsp-isar-font-text-quasi_keyword)
    ("text_improper"  .  lsp-isar-font-text-improper)
    ("text_operator"  .  lsp-isar-font-text-operator)
    ("text_tfree"  .  lsp-isar-font-text-tfree)
    ("text_tvar"  .  lsp-isar-font-text-tvar)
    ("text_free"  .  lsp-isar-font-text-free)
    ("text_skolem"  .  lsp-isar-font-text-skolem)
    ("text_bound"  .  lsp-isar-font-text-bound)
    ("text_var"  .  lsp-isar-font-text-var)
    ("text_inner_numeral"  .  lsp-isar-font-text-inner_numeral)
    ("text_inner_quoted"  .  lsp-isar-font-text-inner_quoted)
    ("text_inner_cartouche"  .  lsp-isar-font-text-inner_cartouche)
    ("text_inner_comment"  .  lsp-isar-font-text-inner_comment)
    ("text_dynamic"  .  lsp-isar-font-text-dynamic)
    ("text_class_parameter"  .  lsp-isar-font-text-class_parameter)
    ("text_antiquote"  .  lsp-isar-font-text-antiquote)

    ("text_overview_unprocessed"  .  lsp-isar-font-text-overview-unprocessed)
    ("text_overview_running"  .  lsp-isar-font-text-overview-running)
    ("text_overview_error"  .  lsp-isar-font-text-overview-error)
    ("text_overview_warning"  .  lsp-isar-font-text-overview-warning)

    ("spell_checker"  .  lsp-isar-font-spell-checker)))


;; REMOVE FOR DEBUGGING: performance hacks
(cl-proclaim `(optimize (speed 3) (safety 0)))

(defmacro lsp-isar-decorations--cl-assert (form &optional show-args string &rest args)
  "Verify that FORM returns non-nil; signal an error if not.

Saner version of cl-assert of FORM: no cost if optimizations are activated!
By default it is only when the file is compiling and if it is
not, we just pay for the cost of the test.  The cost is not high,
but still, I want assertions to be done only for debugging."
  (declare (debug (form &rest form)))
  (and (or (< cl--optimize-speed 3) (= cl--optimize-safety 3))
       (let ((sargs (and show-args
                         (delq nil (mapcar (lambda (x)
                                             (unless (macroexp-const-p x)
                                               x))
                                           (cdr-safe form))))))
	 `(progn
            (or ,form
                (cl--assertion-failed
                 ',form ,@(if (or string sargs args)
                              `(,string (list ,@sargs) (list ,@args)))))
            nil))))



;; range  functions
(define-inline lsp-isar-decorations-ranges-are-equal (r1 r2)
  (inline-letevals (r1 r2)
    (inline-quote
     (let ((x0 (lsp-isar-ov-x0 ,r2)) (y0 (lsp-isar-ov-y0 ,r2)))
       (let ((x1 (elt ,r1 0)) (y1 (elt ,r1 1)))
	 (and (= (cl-the fixnum x0) (cl-the fixnum x1))
	      (= (cl-the fixnum y0) (cl-the fixnum y1))))))))

(define-inline lsp-isar-decorations-point-is-before (x0 y0 x1 y1)
  (inline-letevals (x0 y0 x1 y1)
    (inline-quote
     (if (/= (cl-the fixnum ,x0) (cl-the fixnum ,x1))
	 (< (cl-the fixnum ,x0) (cl-the fixnum ,x1))
       (< (cl-the fixnum ,y0) (cl-the fixnum ,y1))))))

;; Ranges of the same type cannot overlap
(define-inline lsp-isar-decorations-range-is-before (r1 r2)
  (inline-letevals (r1 r2)
    (inline-quote
     (and (lsp-isar-decorations-point-is-before (elt ,r1 0) (elt ,r1 1) (lsp-isar-ov-x0 ,r2) (lsp-isar-ov-y0 ,r2))))))


;; This is a full cleaning of all buffers.  This is too costly to run
;; regularly.  Therefore, we run it after some time of idling.
;; Remark that this is still important to run.
(defun lsp-isar-decorations-kill-all-unused-overlays-file (file &rest _)
  "Delete all invisible overlays in file FILE.

Remove all overlays that are deleted or recycled: They are
deleted from the buffer and from the hashtables where they appear
and should be GC-ed by Emacs.

CAUTION: this can be slow."
  (let*
      ((overlays-to-reuse (gethash file lsp-isar-decorations--overlays-to-reuse nil))
       (m (length overlays-to-reuse)))
    (with-silent-modifications
      (message "Cleaning file %s (%s overlays to delete) [use C-g to abort]" file m)
      (remove-overlays (point-min) (point-max) 'face 'lsp-isar-font-nothing)
      (puthash file nil lsp-isar-decorations--overlays-to-reuse))))


(defun lsp-isar-decorations-kill-all-unused-overlays ()
  "Delete all invisible overlays in all files opened by Isabelle."
  (interactive)
  (message "Cleaning all decorations.  Set lsp-isar-decorations-full-clean-after-inactivity \
  increase the delay between two of them, if you have called the function.")
  (maphash 'lsp-isar-decorations-kill-all-unused-overlays-file lsp-isar-decorations--overlays-to-reuse))


(defcustom lsp-isar-decorations-full-clean-after-inactivity 600
  "Full clean every some many seconds.  Use nil to deactivate it."
  :type '(number)
  :group 'isabelle)


(defvar lsp-isar-decorations--cleaner-timer nil
  "Timer to clean all elements.

Set lsp-isar-decorations-cleaner-ran-every to nil in order to
never start the timer.")


;; recycle by batch of a small number of elements.  This is run on a
;; regural basis.
(defvar lsp-isar-decorations--last-updated-file nil
  "Last updated file.")


;; It is only useful to delete the overlays if we do not have a
;; per-buffer reuse of overlays.  Otherwise, we pay the quadratic cost
;; of deleting each time we delete an overlay to only reinsert it
;; later.
;;
;; We only delete a few overlays with a strict timeout to avoid
;; blocking the main thread for too long.
(defun lsp-isar-decorations-recycle-batch (_w)
  "Recycle a few invisible overlays.

A few overlays are deleted.  We keep the numbers lows to avoid
slowing down emacs too much. Removing overlays is quadratic in
the number of overlays while recycling them is cheap (but uses
more memory), so we only remove some with a short timeout."
  (save-excursion
    (when lsp-isar-decorations--last-updated-file
      (with-silent-modifications
        (let*
	    ((overlays-to-reuse (gethash lsp-isar-decorations--last-updated-file lsp-isar-decorations--overlays-to-reuse nil))
	     (m (length overlays-to-reuse))
	     (should-remove (> m 1000))
	     (n 0))
	  (with-timeout (0.1 nil)
	    (if should-remove
	        (while (and (< n 10) overlays-to-reuse)
		  (let ((ov (pop overlays-to-reuse)))
		    (delete-overlay ov))
		  (cl-incf n))))
	  (puthash lsp-isar-decorations--last-updated-file overlays-to-reuse lsp-isar-decorations--overlays-to-reuse)
	  n))
      0)))


;; started as the equivalent of the cquery version.  Later changed a lot.
;; ASSUMPTIONS:
;;  * old-overlays is sorted (for performance reason).
;;  * old-overlays contains all decorations corresponding to 'typ'
;;    in 'buffer' and they have not already been deleted.
;;
;; The number of markup generated by Isabelle is extremely high and overlays are slow.  The noverlay
;; branch of Emacs devel solves the problem, but it is not clear if it can ever be merged (it is
;; based on a version between Emacs26 and Emacs27).  However, on Emacs26, deleting and repainting
;; the markup (as currently done in cquery) is way too slow to be usable.  Therefore, we only
;; reprint the markup that changed, which is much more complicated.  However, it seems to solves the
;; problem.
;;;;
;; The core function is 'find-new-and-repaint'.  Given the old decoration:
;; A   B   C   D      F   G   H   I  J  K  L  M
;; and the new:
;; A   B   C      E   F   G   H'  I  J
;;
;; we assume that the ranges are sorted and align them as shown.  We
;; iterate over the two lists and there are several cases:
;;   1.  A = A: nothing to do.
;;   2.  there are no more new: delete the remaining;
;;   3.  there are no more old: just print them;
;;   4.  D < E: we delete D and continue the iteration (keeping E in the new decorations);
;;   5.  otherwise, the ranges intersect: we delete H' and add H.
;;
;; Exceptional cases:
;;
;;   0a.  When the buffer was closed, we don't print anything and instead delete the corresponding
;;   hash.
;;
;;   0b.  When the buffer is not visible, we don't print it either and instead delay the printing to
;;   the moment when the buffer becomes visible. This is not too critical in general, unless many
;;   buffers are opened and Isabelle is processing many buffers at the same time (e.g., when opening
;;   a large development, changing the first line and going back to the end).
;;
;;   6.  While printing the overlay, we find out that the position is not valid anymore in the
;;   current buffer: we delete all further old decorations, stop, and wait for the next update from
;;   Isabelle.
;;
;;
;; Due to 6, when we are using arrays, we have nil at the end. In a normal language we probably
;; would use a resizable array, but here we use nil for padding.
;;
;; We assume that the ranges are sorted and non-overlapping for performance, but not correctness. If
;; not true, we would miss overalys to reuse.
;;
;; The function 'find-new-and-repaint' iterates over the old decorations and the new ranges.  It
;; finds out if a range already had a decoration (which does not require changes), if a range needs
;; a new decoration (which must be added), or if not decoration is required anymore (the old one
;; gets deleted).
;;
;;
;; The end_char_offset is here to improve readability: as we do not merge overlays the error marker
;; will continue at the end of the command.  This should help identifying the line with the error.
;;
;; find-range-and-add-to-print contains a 'bug' that is due to the way Emacs handles the current
;; point: forward-char and forward-line return (point-max) when overflowing.  Except when the
;; current point does not exist anymore, then an exception end-of-buffer is raised.
;;
;;
;; Deleting overlays is so incredibly slow.  This is an issue in Emacs and there is no proper
;; work-around.  Basically, deleting overlays are quadratic in their number, because it is not
;; possible to iterate over the overlays in the order they are represented internally (instead we
;; the erder in the buffer is used, which, however, requires searching over the internal list).
;; There is some discussion on https://github.com/cquery-project/cquery/wiki/Emacs.  90% (> 10s) of
;; the time is spent deleting overlays when jumping to the top of buffer and adding a space.  In the
;; noverlay branch, it is only 2% of the time.  We now barely delete any overlay.
;;
;; However, reusing overlays in the same buffer is fast, because no update of the internal data
;; structure is required.
;;
;; Removed overlays are:
;;    1.  added to lsp-isar-decorations--overlays-to-reuse to be reused and make them
;;    invisible.
;;    2.  then either reused or deleted from the overlays when emacs is idle
;;
;; 2 are run in lsp-isar-decorations-recycle-timer.  It is run by a timer to avoid blocking Emacs.
;; It then cancels itself when there is nothing to do.
;;
;; Additional comments: cl-assert is nice... until you realize that it does not compile to no-op
;; even with cl--optimize-speed. For sure, the assertion is not evaluated, but this loop is
;; performance critical, so even a function that boils down to evaluating (and nil nil nil) is not
;; something I want to have in the code.

(define-inline lsp-isar-decorations-new-or-recycle-overlay (overlays-to-reuse point0 point1 face)
  (inline-letevals (overlays-to-reuse point0 point1 face)
    (inline-quote
     (if ,overlays-to-reuse
	 (let ((ov (pop ,overlays-to-reuse)))
	   (move-overlay ov ,point0 ,point1)
	   (overlay-put ov 'face ,face)
	   ov)
       (lsp-isar-decorations--cl-assert (numberp ,point0))
       (lsp-isar-decorations--cl-assert (numberp ,point1))
       (let ((ov (make-overlay ,point0 ,point1)))
	 (overlay-put ov 'face ,face)
	 ov)))))

;; if a range is new, find it in the buffer and print it
;; if the current range is already not valid, return nil
(define-inline lsp-isar-decorations-find-range-and-add-to-print (range curoverlays position end_char_offset overlays-to-reuse line face)
  (inline-letevals (range position end_char_offset overlays-to-reuse line face)
    (inline-quote
     (ignore-errors
       (let ((l0 (elt ,range 0))
	     (c0 (elt ,range 1))
	     (l1 (elt ,range 2))
	     (c1 (elt ,range 3))
	     point0 point1)
	 (forward-line (- (cl-the fixnum l0) (cl-the fixnum line)))
	 (forward-char c0)
	 (setq point0 (point))
	 (forward-line (- (cl-the fixnum l1) (cl-the fixnum l0)))
	 (forward-char (+ (cl-the fixnum c1) ,end_char_offset))
	 (setq point1 (point))
	 (setq line l1)

	 (let ((ov (lsp-isar-decorations-new-or-recycle-overlay overlays-to-reuse point0 point1 ,face)))
	   (aset ,curoverlays ,position (lsp-isar-ov-create :x0 l0 :y0 c0 :x1 l1 :y1 c1 :overlay ov))
	   t))))))

;; This function iterates over huge lists and therefore
;; requires either tail-call optimisation or a while loop
;; (several thousand elements are common).  Therefore, no
;; recursive function works.
(define-inline lsp-isar-decorations-find-new-and-repaint (curoverlays news olds end_char_offset overlays-to-reuse face)
  (inline-letevals (news olds end_char_offset overlays-to-reuse face)
    (inline-quote
     (progn
       (declare (cl-optimize (speed 3) (safety 0)))
       (let ((lnews (length ,news))
	     (lolds (length ,olds))
	     (inew 0)
	     (iold 0)
	     (line 0))
	 (setq ,curoverlays (make-vector lnews (lsp-isar-ov-create)))
	 (while (and (< inew lnews) (< iold lolds))
	   ;; otherwise, compare the first two ranges
	   (let ((r1 (aref (cl-the array ,news) (cl-the fixnum inew)))
		 (r2 (aref (cl-the array ,olds) (cl-the fixnum iold))))
	     (if (not (lsp-isar-ov-overlay (elt ,olds iold)))
		 ;; we have reached the padding at the end of the olds
		 (setq lolds iold)
	       ;; if the ranges are equal no need to repaint
	       (if (lsp-isar-decorations-ranges-are-equal r1 r2)
		   (progn
		     (aset ,curoverlays inew r2)
		     (cl-incf (cl-the fixnum inew))
		     (cl-incf (cl-the fixnum iold)))
		 ;; if r1 < r2, print r1 and continue iteration
		 (if (lsp-isar-decorations-range-is-before r1 r2)
		     (if (lsp-isar-decorations-find-range-and-add-to-print r1 ,curoverlays inew ,end_char_offset ,overlays-to-reuse line ,face)
			 (cl-incf inew)
		       ;; else the content is not valid anymore:
		       (progn
			 (cl-loop for x from iold to (1- lolds) do
				  (unless (lsp-isar-ov-overlay (elt ,olds x))
				    (cl-return nil))
				  (overlay-put (lsp-isar-ov-overlay (elt ,olds x)) 'face 'lsp-isar-font-nothing)
				  (push (lsp-isar-ov-overlay (elt ,olds x)) overlays-to-reuse))
			 (setq inew lnews)
			 (setq iold lolds)))
		   ;; otherwise, r1 is after the beginng of r2,
		   ;; so remove r2 and continue (r1 might just be later in olds)
		   ;;(message "number of elts in olds: %s" (length olds))
		   ;;(message "wanted to print: %s skipped: %s" r1 r2)
		   (overlay-put (lsp-isar-ov-overlay r2) 'face 'lsp-isar-font-nothing)
		   (push (lsp-isar-ov-overlay r2) overlays-to-reuse)
		   (cl-incf (cl-the fixnum iold)))))))
	 (when (>= inew lnews)
	   ;; no news: discard all old decorations
	   (cl-loop for x from iold to (1- lolds) do
		    (unless (lsp-isar-ov-overlay (elt ,olds x))
		      (cl-return nil))
		    (overlay-put (lsp-isar-ov-overlay (elt ,olds x)) 'face 'lsp-isar-font-nothing)
		    (push (lsp-isar-ov-overlay (elt ,olds x)) overlays-to-reuse))
	   (setq iold lolds))
	 (when (>= iold lolds)
	   ;; no olds: print all news
	   (cl-loop for x from inew to (1- lnews) do
		    (lsp-isar-decorations-find-range-and-add-to-print (elt ,news x) ,curoverlays x  ,end_char_offset ,overlays-to-reuse line ,face))
	   (setq inew lnews)
	   (lsp-isar-decorations--cl-assert (= iold lolds))
	   (lsp-isar-decorations--cl-assert (= inew lnews))))))))


(lsp-defun lsp-isar-decorations-update-cached-decorations-overlays (params)
  "Update the syntax highlighting as generated by Isabelle given in PARAMS.

It is done by removing the now unused old one and adding the old
one.  This a performance critical function."
  (save-excursion
    (-let [(&lsp-isar:Decorations :uri :type :content) params]
      (-let* (
	      ;; normal function
	      (file (lsp--uri-to-path uri))
	      (buffer (find-buffer-visiting file))
	      (pranges (or content []))
	      (typ type)
	      (face (cdr (assoc typ lsp-isar-decorations-get-font)))
	      (end_char_offset (if (or (equal typ "text_overview_error") (equal typ "text_overview_running")) 1 0)))
	(if (not buffer)
	    ;; buffer was closed or is not properly opened yet
	    ;; the rest will be deleted during the next round of full cleaning
	    (remhash file lsp-isar-decorations--sem-overlays)

	  (if (and lsp-isar-decorations-delayed-printing (not (get-buffer-window buffer 'visible)))
	      (let ((current-file-overlays (gethash file lsp-isar-decorations--delayed-overlays (make-hash-table :test 'equal))))
		(puthash typ params current-file-overlays)
		(puthash file current-file-overlays lsp-isar-decorations--delayed-overlays))

	    ;; faster adding (and deleting) of overlays; see for example
	    ;; discussion on
	    ;; https://github.com/flycheck/flycheck/issues/1168
	    (overlay-recenter (point-max))

	    (let (curoverlays (inhibit-field-text-motion t))
	      (when (equal face 'lsp-isar-font-default)
		(warn "unrecognised color %s. Please report the error." typ))
	      (lsp-isar-decorations--cl-assert (vectorp pranges))

	      ;; extract only the range in the correct order
	      ;; neither mapcar nor seq-map return the correct type!
	      (cl-loop for i from 0 to (1- (length pranges)) do
		       (-let [(&lsp-isar:DecorationRange :range) (aref pranges i)]
			 (aset pranges i range)))
	      (lsp-isar-decorations--cl-assert (vectorp pranges))

	      ;; Sort by start-line ASC, start-character ASC.
	      ;; the ranges are not overlapping
	      ;; (setq ranges
	      ;;       (sort ranges (lambda (x y)
	      ;; 		     (let ((x0 (elt x 0)) (y0 (elt y 0)))
	      ;; 		       (if (/= x0 y0)
	      ;; 			   (< x0 y0)
	      ;; 			 (< (elt x 1) (elt y 1)))))))

	      ;; reprint
	      (let*
		  ((current-file-overlays (gethash file lsp-isar-decorations--sem-overlays (make-hash-table :test 'equal)))
		   (old-overlays (gethash typ current-file-overlays []))
		   (overlays-to-reuse (gethash file lsp-isar-decorations--overlays-to-reuse nil)))

		(lsp-isar-decorations--cl-assert (vectorp old-overlays))
		;; recycle an old overlay by moving and updating it,
		;; otherwise, create a new one

		(with-current-buffer buffer
		  (with-silent-modifications
		    ;; find all new overlays
		    (widen)
		    (goto-char 1)
		    ;; (cl-loop for x in old-overlays do
		    ;; 	       (lsp-isar-decorations--cl-assert (cadr x)))

		    (lsp-isar-decorations-find-new-and-repaint curoverlays pranges old-overlays end_char_offset overlays-to-reuse face)

		    (puthash typ curoverlays current-file-overlays)
		    (puthash file current-file-overlays lsp-isar-decorations--sem-overlays)
		    (puthash file overlays-to-reuse lsp-isar-decorations--overlays-to-reuse)))
		(setq lsp-isar-decorations--last-updated-file file)))))))))

(defun lsp-isar-decorations-update-and-reprint (_workspace params)
  "Reprint all decorations as given by Isabelle in PARAMS."
  (lsp-isar-decorations-update-cached-decorations-overlays params))


;; This function can be called several times!
(defun lsp-isar-decorations--init-decorations ()
  "Initialise all elements required for the decorations."
  ;; (unless lsp-isar-decorations--recycler
  ;;   (setq lsp-isar-decorations--recycler (run-with-timer 0 0.5 'lsp-isar-decorations-recycle-batch nil)))
  (if (and
       (not lsp-isar-decorations--cleaner-timer)
       lsp-isar-decorations-full-clean-after-inactivity
       (> lsp-isar-decorations-full-clean-after-inactivity 0))
      (setq lsp-isar-decorations--cleaner-timer
	    (run-with-idle-timer lsp-isar-decorations-full-clean-after-inactivity t
				 'lsp-isar-decorations-kill-all-unused-overlays))))

(defun lsp-isar-decorations--print-delayed-buffer-decorations (file params)
  "Prints the decorations from buffer FILE that were not printed so far."
  (save-excursion
    (let ((buffer (find-buffer-visiting file)))
      (when (and buffer params (get-buffer-window buffer 'visible))
	(maphash (lambda (_key params) (lsp-isar-decorations-update-cached-decorations-overlays params))
		 params)
	(remhash file lsp-isar-decorations--delayed-overlays)))))

(defun lsp-isar-decorations--print-delayed-buffers-decorations ()
  "Prints the decorations that were not printed so far."
  (maphash 'lsp-isar-decorations--print-delayed-buffer-decorations lsp-isar-decorations--delayed-overlays))

(defun lsp-isar-decorations-activate-delayed-printing ()
  "Activate delayed printing."
  (when lsp-isar-decorations-delayed-printing
    (add-to-list 'window-configuration-change-hook #'lsp-isar-decorations--print-delayed-buffers-decorations)))

(provide 'lsp-isar-decorations)


;;; lsp-isar-decorations.el ends here