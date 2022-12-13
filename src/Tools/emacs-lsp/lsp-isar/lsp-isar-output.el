;;; lsp-isar-output.el --- Update the state and output buffers -*- lexical-binding: t -*-

;; Copyright (C) 2018-2020 Mathias Fleury

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

;;; Commentary:

;; Provides two ways to update the output and state buffer.  Once directly and another
;; asynchronously via the async library.

;; The synchronous version can timeout via `lsp-isar-output-maximal-time'. This is necessary,
;; because the update runs in the main thread.

;;; Code:

(require 'isar-goal-mode)
(require 'lsp-isar-decorations)
(require 'dash)

(require 'dom)
(require 'session-async)
(require 'lsp-protocol)
(require 'lsp-isar-types)

(eval-when-compile (require 'subr-x))

(defvar lsp-isar-output-state-buffer nil "Isabelle state buffer.")
(defvar lsp-isar-output-buffer nil "Isabelle output buffer.")
(defvar lsp-isar-output-output-deco nil "Isabelle decorations.")
(defvar lsp-isar-output-state-deco nil "Isabelle decorations in state buffer.")
(defvar lsp-isar-output-proof-cases-content nil)
(defvar lsp-isar-output-proof-timer nil "Current timer rendering the HTML.")
(defvar lsp-isar-output-session-name nil
  "Async session to send goals to for printing.")

(defcustom lsp-isar-output-maximal-time 3
  "Maximal time in seconds printing can take.

Use nil for infinity"
  :type '(number)
  :group 'isabelle)

(defvar lsp-isar-output--last-start nil "Last start time in seconds.")
(defvar lsp-isar-output--previous-goal nil "Previous outputted goal.")
(defvar lsp-isar-output-current-output-number 0 "Number of the current output.")
(defvar lsp-isar-output-last-seen-prover nil "Name of the prover that was seen last.")

(defcustom lsp-isar-output-use-async nil
  "Use asynchronous goal printing."
  :type '(bool)
  :group 'isabelle)

(defcustom lsp-isar-output-time-before-printing-goal 0.3
  "Time before printing goal.  Use nil to avoid printing."
  :type '(number)
  :group 'isabelle)

(define-error 'abort-rendering "Abort the rendering of the state and output buffer.")


(define-inline lsp-isar-output-remove-quotes-from-string (obj)
  (inline-letevals (obj)
    (inline-quote (string-remove-suffix "'" (string-remove-prefix "'" ,obj)))))

;; The function iterates over the HTML as parsed by the HTML library.  As a side effect, it fills the
;; state buffer and the output buffer with the correct faces.  We cannot make the function recursive,
;; as recursive is slower and fail for deep goals.
;;
;; To shorten the code, we use the define-inline which is inlined
;; during compilation.
;;
;;
;; TODO
;;
;;   - find a big example to play with the recursive function to
;; optimise the code.
;;
;;   - find a proper profiling library.
;;
;;   - don't always use the async version of the printing.  At least for small goals, it should be
;; faster to use the local instance.
;;
;;  - deduplicate functions
;;
;; The (cond ...) compiles down to a jump table, except for the
;; entries that contains (or (eq ...) (eq ...)).  Therefore, I
;; duplicate entries.
;;
;;
;; RESULT OF SOME INVESTIGATIONS
;;
;;   - parsing the goal is not slow during testing but can become a
;; huge issue on Isabelle theories.  And profiling in Emacs is as usual
;; entirely useless to find the problem.
;;
;;
;; Initially, to reduce the overhead of printing (especially when the output contains an error).  The
;; typical situation is that "apply aut" is typed, which means that goal is printer once and another
;; time in the error message.  This is impossible to support.  Therefore, we delay the printing, such
;; that we can cancel it, if another newer version of the goal is coming.  The delay was
;; experimentally set to 0.3s.  If async is used, the processing is moved to another Emacs
;; instance.  We currently do not use any delay, although printing still has a cost on the local
;; Emacs.
;;
;; The choice of async is rather random, but there are not that many options and the
;; documentation is good enough...
;;
(defun lsp-isar-output-parse-output (contents)
  "Parse Isabelle output CONTENTS.

The function iterates over the dynamic output generated by
Isabelle (after preprocessing), in order to generate a goal that
must be printed in Emacs with the syntax highlighting.

This is function is important for performance (not as critical as
the decorations), because goals can become arbitrary long.  Remark
that I have not really tried to optimise it yet.  Even if the
function is less critical, Emacs is single threaded and all these
functions adds up.  So any optimisation would help."
 (while contents
   (let ((content (pop contents)))
     ;; (message "content = %s" content)
     (cond
      ((eq content nil) nil)
      ((eq content 'html) nil)
      ((stringp content) (insert content))
      ((not (listp content))
       ;; (message "unrecognised %s" content)
       (insert (format "%s" content)))
      (t
       (pcase (dom-tag content)
	 ('lsp-isar-output-select-state-buffer
	  (setq lsp-isar-output-state-selected t)
	  (set-buffer lsp-isar-output-state-buffer))
	 ('lsp-isar-output-fontification
	  (let ((start-point (dom-attr content 'start-point))
		(face (dom-attr content 'face)))
	    (if lsp-isar-output-state-selected
		(push (list start-point (point) face) lsp-isar-output-state-deco)
	      (push (list start-point (point) face) lsp-isar-output-output-deco))))
	 ('lsp-isar-output-save-sendback
	  (let ((start-point (dom-attr content 'start-point)))
	    (push (buffer-substring start-point (point)) lsp-isar-output-proof-cases-content)))
	 ('html
	  (setq contents (append (dom-children content) contents)))
	 ('xmlns nil)
	 ('meta nil)
	 ('link nil)
	 ('xml_body nil)
	 ('path nil)

	 ('head
	  (push (car (last (dom-children content))) contents))

	 ('body
	  (setq contents (append (dom-children content) contents)))

	 ('block
	  (insert (if (dom-attr content 'indent) " " ""))
	  (setq contents (append (dom-children content) contents)))

	 ('class
	  (setq contents (append (dom-children content) contents)))

	 ('pre
	  (setq contents (append (dom-children content) contents)))

	 ('state_message
	  (push (dom-node 'break `(('line .  1)) "\n") contents)
	  (setq contents (append (dom-children content) contents)))

	 ('information_message
	  (set-buffer lsp-isar-output-buffer)
	  (setq lsp-isar-output-state-selected nil)
	  (push (dom-node 'lsp-isar-output-select-state-buffer ()) contents)
	  (let ((start-point (point)) (face "dotted_information"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('tracing_message ;; TODO Proper colour
	  (set-buffer lsp-isar-output-buffer)
	  (setq lsp-isar-output-state-selected nil)
	  (push (dom-node 'lsp-isar-output-select-state-buffer ()) contents)
	  (let ((start-point (point)) (face "dotted_information"))
	    (push (dom-node 'break `(('line .  1)) "\n") contents)
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('warning_message
	  (set-buffer lsp-isar-output-buffer)
	  (setq lsp-isar-output-state-selected nil)
	  (push (dom-node 'lsp-isar-output-select-state-buffer ()) contents)
	  (let ((start-point (point)) (face "text_overview_warning"))
	    (push (dom-node 'break `(('line .  1)) "\n") contents)
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('legacy_message
	  (set-buffer lsp-isar-output-buffer)
	  (setq lsp-isar-output-state-selected nil)
	  (push (dom-node 'lsp-isar-output-select-state-buffer ()) contents)
	  (let ((start-point (point)) (face "text_overview_warning"))
	    (push (dom-node 'break `(('line .  1)) "\n") contents)
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('writeln_message
	  (set-buffer lsp-isar-output-buffer)
	  (setq lsp-isar-output-state-selected nil)
	  (push (dom-node 'lsp-isar-output-select-state-buffer ()) contents)
	  (let ((start-point (point)) (face "dotted_writeln"))
	    (push (dom-node 'break `(('line .  1)) "\n") contents)
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('error_message
	  (set-buffer lsp-isar-output-buffer)
	  (setq lsp-isar-output-state-selected nil)
	  (push (dom-node 'lsp-isar-output-select-state-buffer ()) contents)
	  (let ((start-point (point)) (face "text_overview_error"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (push (dom-node 'break `(('line .  1)) "\n") contents)
	    (setq contents (append (dom-children content) contents))))

	 ('b
	  (insert "\\<^bbold>")
	  (setq contents (append (dom-children content)  (list "\\<^ebold>") contents)))

	 ('i
	  (insert "\\<^bitalic>")
	  (setq contents (append (dom-children content)  (list "\\<^eitalic>") contents)))

	 ('text_fold
	  (setq contents (append (dom-children content) contents)))

	 ('subgoal
	  ;;(set-buffer lsp-isar-output-state-buffer)
	  (setq contents (append (dom-children content) contents)))

	 ('span
	  (let ((str (format "%s" (car (last (dom-children content))))))
	    (insert (format "%s"str))))
	 ('position
	  (push (car (last (dom-children content))) contents))

	 ('intensify
	  (let ((start-point (point)) (face "background_intensify"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('keyword1
	  (let ((start-point (point)) (face "text_keyword1"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('keyword2
	  (let ((start-point (point)) (face "text_keyword2"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('keyword3
	  (let ((start-point (point)) (face "text_keyword3"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('keyword4
	  (let ((start-point (point)) (face "text_keyword4"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('fixed ;; this is used to enclose other variables
	  (setq contents (append (dom-children content) contents)))

	 ('free
	  (let ((start-point (point)) (face "text_free"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('inner_string ;; TODO font
	  (setq contents (append (dom-children content) contents)))

	 ('tfree
	  (let ((start-point (point)) (face "text_tfree"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('tvar
	  (let ((start-point (point)) (face "text_tvar"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('var
	  (let ((start-point (point)) (face "text_var"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('bound
	  (let ((start-point (point)) (face "text_bound"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('skolem
	  (let ((start-point (point)) (face "text_skolem"))
	    (push (dom-node 'lsp-isar-output-fontification `((start-point .  ,start-point) (face .  ,face)) nil) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('sendback ;; TODO handle properly
          (insert "|" (format "%s" (1+ (length lsp-isar-output-proof-cases-content))) "|: ")
	  (let ((start-point (point)))
	    (save-excursion
	      (beginning-of-line)
	      (let ((str (buffer-substring (point) start-point)))
		(if (and str (cl-search "Try" str))
		    (setq lsp-isar-output-last-seen-prover str)
		  (setq lsp-isar-output-last-seen-prover
			(concat lsp-isar-output-last-seen-prover "Isar")))))
	    (push (dom-node 'lsp-isar-output-save-sendback `((start-point .  ,start-point) nil)) contents)
	    (setq contents (append (dom-children content) contents))))

	 ('bullet
	  (insert "•")
	  (setq contents (append (dom-children content) contents)))

	 ('language
	  (setq contents (append (dom-children content) contents)))

	 ('literal
	  (setq contents (append (dom-children content) contents)))

	 ('delimiter
	  (setq contents (append (dom-children content) contents)))

	 ('entity
	  (setq contents (append (dom-children content) contents)))

	 ('paragraph
	  (setq contents (append (dom-children content) contents)))

	 ('dynamic_fact
	  (setq contents (append (dom-children content) contents)))

	 ('item
	  (setq contents (append (dom-children content) contents))) ;; TODO line break

	 ('break
	  (let ((children (mapcar 'lsp-isar-output-remove-quotes-from-string (dom-children content))))
	    (insert (if (dom-attr content 'width) " " ""))
	    (insert (if (dom-attr content 'line) "\n" ""))
	    (mapc 'insert children)))

	 ('xml_elem
	  (setq contents (append (dom-children content) contents)))

	 ('emacs_isabelle_symbol
	  (let ((symbol (car (dom-children content))))
	    (setq contents (append (cdr (dom-children content)) contents))
	    (insert "\\<")
	    (insert symbol)
	    (insert ">")))

	 ('sub ;; Heuristically find the difference between sub and bsub...esub
	  (let ((children (dom-children content)))
	    (if (and
		 (not (cdr children))
		 (stringp (car children)))
		(insert (format "\\<^sub>%s" (car children)))
	      (progn
		(insert "\\<^bsub>")
		(push "\\<^esub>" contents))
	      (setq contents (append children contents)))))

	 ('sup ;; Heuristically find the difference between sup and bsup...esup
	  ;; but we cannot do better as the information is not transmitted
	  (let ((children (dom-children content)))
	    (if (and
		 (not (cdr children))
		 (stringp (car children)))
		(insert (format "\\<^sup>%s" (car children)))
	      (insert "\\<^bsup>")
	      (push "\\<^esup>" contents)
	      (setq contents (append children contents)))))

	 ('p nil) ;; libxml odd behaviour

	 (_
	  (if (listp (dom-tag content))
	      (progn
		;; (message "unrecognised node %s" (dom-tag content))
		(insert (format "%s" (dom-tag content)))
		(mapc 'lsp-isar-output-parse-output (dom-children content)))
	    (progn
	      ;; (message "unrecognised content %s; node is: %s; string: %s %s"
	      ;;       content (dom-tag content) (stringp (dom-tag content)) (listp content))
	      (insert (format "%s" (dom-tag content))))))))))))

(defun lsp-isar-output-replace-regexp-all-occs (REGEXP TO-STRING)
  "Replace all occurences of REGEXP by TO-STRING.

Lisp equivalent of 'replace-regexp' as indicated in the help."
  (goto-char (point-min))
  (while (re-search-forward REGEXP nil t)
    (replace-match TO-STRING nil nil)))

(defun lsp-isar-output-update-goal-without-deadline ()
  "Update the goal without time limit."
  (interactive)
  (let ((old-timeout lsp-isar-output-maximal-time))
    (setq lsp-isar-output-maximal-time nil)
    (lsp-isar-output--update-state-and-output-buffer lsp-isar-output--previous-goal)
    (setq lsp-isar-output-maximal-time old-timeout)))


(defun lsp-isar-output--prepare-html ()
  "fixes the html output from Isabelle to match the expectation from emacs"

  (lsp-isar-output-replace-regexp-all-occs "\\\\<\\(\\w*\\)>" "<emacs_isabelle_symbol>\\1</emacs_isabelle_symbol>")
  ;; remove line breaks at beginning
  (lsp-isar-output-replace-regexp-all-occs "\\$\n*<body>\n" "<body>")
  ;; protect spaces and line breaks
  (lsp-isar-output-replace-regexp-all-occs "\s\s\s\s\s"
					   "  ")
  (lsp-isar-output-replace-regexp-all-occs "\n\\( *\\)"
					   "<break line = 1>'\\1'</break>")
  (lsp-isar-output-replace-regexp-all-occs "\\(\\w\\)>\\( *\\)<"
					   "\\1><break>'\\2'</break><")
  )

(defun lsp-isar-output--update-state-and-output-buffer (content)
  "Update state and output buffers with Isabelle's CONTENT."
  (condition-case nil
      (let ((parsed-content nil))
	(setq lsp-isar-output--previous-goal content)
	(save-excursion
	  (with-current-buffer lsp-isar-output-buffer
	    (read-only-mode -1)
	    (erase-buffer))
	  (with-temp-buffer
	    (if content
		(progn
		  (insert "$")
		  (insert content)
		  ;; (message (buffer-string))
		  ;; Isabelle's HTML and Emacs's HMTL disagree, so
		  ;; we preprocess the output.
		  (lsp-isar-output--prepare-html)

		  ;; (message (buffer-string))
		  ;; (message "%s"(libxml-parse-html-region  (point-min) (point-max)))
		  (setq parsed-content (libxml-parse-html-region (point-min) (point-max))))))
	  (with-current-buffer lsp-isar-output-state-buffer
	    (let ((inhibit-read-only t))
	      (erase-buffer)
	      (setq lsp-isar-output-proof-cases-content nil
		    lsp-isar-output-last-seen-prover nil)
	      (lsp-isar-output-parse-output parsed-content)
	      (goto-char (point-min))
	      (ignore-errors
		(search-forward "Proof outline with cases:") ;; TODO this should go to lsp-isar-output-parse-output
		(setq lsp-isar-output-proof-cases-content (buffer-substring (point) (point-max))))))
	  (with-current-buffer lsp-isar-output-buffer
	    (read-only-mode t))))
    ('abort-rendering
     (message "updating goal interrupted (too slow), use lsp-isar-output-update-goal-without-deadline")
     nil)))


(defun lsp-isar-output--caddddr (x)
  "Return the `car' of the `cdr' of the `cdr' of the `cdr' of the `cdr' of X."
  (declare (compiler-macro internal--compiler-macro-cXXr))
  (car (cdr (cdr (cdr (cdr x))))))

(defun lsp-isar-output-give-parsed-goal (lsp-isar-output-current-output-number-res result)
  ;; After evaluating the goal asynchronously, we retrieve it and update it in the current
  ;; window.
  (let* ((lsp-isar-output-state (car result))
	 (lsp-isar-output-output (cadr result))
	 (lsp-isar-output-proof-cases-content-1 (caddr result))
	 (lsp-isar-output-state-deco  (cadddr result))
	 (lsp-isar-output-output-deco (lsp-isar-output--caddddr result)))
    (when (= lsp-isar-output-current-output-number lsp-isar-output-current-output-number-res)
      (cl-incf lsp-isar-output-current-output-number)
      (setq lsp-isar-output-proof-cases-content lsp-isar-output-proof-cases-content-1)
      (when lsp-isar-output-output
	(save-excursion
	  (with-current-buffer lsp-isar-output-buffer
	    (read-only-mode -1)
	    (setf (buffer-string) lsp-isar-output-output)
	    (read-only-mode t))))
      (when lsp-isar-output-state
	(save-excursion
	  (with-current-buffer lsp-isar-output-state-buffer
	    (read-only-mode -1)
	    (setf (buffer-string) lsp-isar-output-state)
	    (read-only-mode t))
	  (with-current-buffer lsp-isar-output-state-buffer
	    (dolist (deco lsp-isar-output-state-deco)
	      (let* ((point0 (car deco))
		     (point1 (cadr deco))
		     (font (caddr deco))
		     (face (cdr (assoc font lsp-isar-decorations-get-font)))
		     (ov (make-overlay point0 point1)))
		(overlay-put ov 'face face))))
	  (with-current-buffer lsp-isar-output-buffer
	    (dolist (deco lsp-isar-output-output-deco)
	      (let* ((point0 (car deco))
		     (point1 (cadr deco))
		     (font (caddr deco))
		     (face (cdr (assoc font lsp-isar-decorations-get-font)))
		     (ov (make-overlay point0 point1)))
		(overlay-put ov 'face face)))))))))

(defun lsp-isar-output--update-state-and-output-buffer-async (lsp-isar-output-current-output-number-res content)
  "Parse Isabelle output CONTENT asynchronously and number
LSP-ISAR-OUTPUT-CURRENT-OUTPUT-NUMBER-RES."
  (save-excursion
    (session-async-start
     `(lambda () (lsp-isar-output-recalculate-async ,content))
     (lambda (content) (lsp-isar-output-give-parsed-goal lsp-isar-output-current-output-number-res content))
     lsp-isar-output-session-name)))

(defun lsp-isar-output-recalculate-sync (content)
  (let
      (;;(lsp-isar-output-output-deco nil)
       (lsp-isar-output-state-deco nil)
       (lsp-isar-output-state-selected t)
       (lsp-isar-output-proof-cases-content nil)
       (lsp-isar-output-last-seen-prover nil)
       (inhibit-message t)
       lsp-isar-output-state
       lsp-isar-output)

    (set-buffer lsp-isar-output-state-buffer)

    (setq lsp-isar-output-maximal-time nil)
    (let ((parsed-content nil))
      (setq lsp-isar-output--previous-goal content)
      (save-excursion
	(with-current-buffer lsp-isar-output-buffer
	  (read-only-mode -1)
	  (erase-buffer))
	(with-temp-buffer
	  (if content
	      (progn
		(insert "$")
		(insert content)
		(lsp-isar-output--prepare-html)
		;; (message "%s" (libxml-parse-html-region  (point-min) (point-max)))
		(setq parsed-content (libxml-parse-html-region (point-min) (point-max))))))

	(with-current-buffer lsp-isar-output-state-buffer
	  (let ((inhibit-read-only t))
	    (erase-buffer)
	    (lsp-isar-output-parse-output parsed-content)
	    (goto-char (point-min))
	    (setq lsp-isar-output-state (buffer-string))))
	(with-current-buffer lsp-isar-output-buffer
	  (read-only-mode t)
	  (setq lsp-isar-output (buffer-string)))
	(list lsp-isar-output-state lsp-isar-output lsp-isar-output-proof-cases-content
	      lsp-isar-output-state-deco lsp-isar-output-output-deco)))))

;; deactivate font-lock-mode because we to the fontification ourselves anyway.
(defun lsp-isar-output-initialize-output-buffer ()
  "Initialize buffers."
  (setq lsp-isar-output-session-name (session-async-new))
  (session-async-start
   `(lambda ()
      (progn
	(require 'dom)
	(require 'subr-x)
	(require 'lsp-isar-output)
	(defun lsp-isar-output-remove-quotes-from-string (obj)
	  (string-remove-suffix "'" (string-remove-prefix "'" obj)))
	(defun lsp-isar-output-replace-regexp-all-occs (REGEXP TO-STRING)
	  "replace-regexp as indicated in the help"
	  (goto-char (point-min))
	  (while (re-search-forward REGEXP nil t)
	    (replace-match TO-STRING nil nil)))
	(defun lsp-isar-output-recalculate-async (content)
	  (let
	      ((lsp-isar-output-output-deco nil)
	       (lsp-isar-output-state-deco nil)
	       (lsp-isar-output-state-selected t)
	       (lsp-isar-output-state-buffer (get-buffer-create "*lsp-isar-state*"))
	       (lsp-isar-output-buffer (get-buffer-create "*lsp-isar-output*"))
	       (lsp-isar-output-proof-cases-content nil)
	       (lsp-isar-output-last-seen-prover nil)
               (inhibit-message t)
	       lsp-isar-output-state
	       lsp-isar-output)

	    (set-buffer lsp-isar-output-state-buffer)

	    (setq lsp-isar-output-maximal-time nil)
	    (let ((parsed-content nil))
	      (setq lsp-isar-output--previous-goal content)
	      (save-excursion
		(with-current-buffer lsp-isar-output-buffer
		  (read-only-mode -1)
		  (erase-buffer))
		(with-temp-buffer
		  (if content
		      (progn
			(insert "$")
			(insert content)
			(lsp-isar-output--prepare-html)
			;; (message "%s" (libxml-parse-html-region  (point-min) (point-max)))
			(setq parsed-content (libxml-parse-html-region (point-min) (point-max))))))

		(with-current-buffer lsp-isar-output-state-buffer
		  (let ((inhibit-read-only t))
		    (erase-buffer)
		    (lsp-isar-output-parse-output parsed-content)
		    (goto-char (point-min))
		    (setq lsp-isar-output-state (buffer-string))))
		(with-current-buffer lsp-isar-output-buffer
		  (read-only-mode t)
		  (setq lsp-isar-output (buffer-string)))
		(list lsp-isar-output-state lsp-isar-output lsp-isar-output-proof-cases-content
		      lsp-isar-output-state-deco lsp-isar-output-output-deco)))))))
   'ignore
   lsp-isar-output-session-name)
  (setq lsp-isar-output-state-buffer (get-buffer-create "*lsp-isar-state*"))
  (setq lsp-isar-output-buffer (get-buffer-create "*lsp-isar-output*"))
  (save-excursion
    (with-current-buffer lsp-isar-output-state-buffer
      (read-only-mode t)
      (isar-goal-mode)
      (font-lock-mode nil))
    (with-current-buffer lsp-isar-output-buffer
      (visual-line-mode t)
      (read-only-mode t)
      (isar-goal-mode)
      (font-lock-mode nil))))

(lsp-defun lsp-isar-output-update-state-and-output-buffer (_workspace (&lsp-isar:DynamicOutput :content))
  "Launch the thread or timer to update the state and the output
panel with CONTENT."
  (setq lsp-isar-output--previous-goal content)
  (cl-incf lsp-isar-output-current-output-number)

  (if lsp-isar-output-time-before-printing-goal
      (progn
	(if lsp-isar-output-proof-timer
	    (cancel-timer lsp-isar-output-proof-timer))
	(setq lsp-isar-output-proof-timer
	      (run-at-time lsp-isar-output-time-before-printing-goal nil
			   (lambda (content)
			     (progn
			       (setq lsp-isar-output--last-start (time-to-seconds))
			       (lsp-isar-output--update-state-and-output-buffer content)))
			   content)))
    (if lsp-isar-output-use-async
	(lsp-isar-output--update-state-and-output-buffer-async lsp-isar-output-current-output-number content)
      (lsp-isar-output-give-parsed-goal lsp-isar-output-current-output-number (lsp-isar-output-recalculate-sync content)))))



(defun lsp-isar-output-set-size (size)
  "Resize line length of output buffer."
  (interactive)
  (let ((my-message (lsp-make-notification "PIDE/set_message_margin" (list :value size))))
    (lsp-send-notification my-message)))

(defun lsp-isar-output-adapt-length ()
  "Adapt the size of the buffer"
  (when lsp-isar-output-buffer
    (save-excursion
      (let
	  ((cols (window-body-width (get-buffer-window lsp-isar-output-buffer))))
	(lsp-isar-output-set-size (- cols 5))))))

(defun lsp-isar-output-adapt-to-change (&optional _frame)
  (lsp-isar-output-adapt-length))

(add-hook 'window-configuration-change-hook 'lsp-isar-output-adapt-to-change)

(modify-coding-system-alist 'file "*lsp-isar-output*" 'utf-8-auto)

(provide 'lsp-isar-output)

;;; lsp-isar-output.el ends here
