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

;;; Code:

(require 'isar-goal-mode)
(require 'lsp-decorations)

(require 'dom)
(eval-when-compile (require 'subr-x))

(defvar isar-output-buffer nil)
(defvar isar-proof-cases-content nil)

(defun isar-parse-output (content)
  ;;(message "content = %s" content)
  (cond
   ((not content) nil)
   ((stringp content)
   ;; (message "stringp %s" content)
    content)
   ((not (listp content))
    (message "unrecognised")
    (format "%s" content))
   (t
    (let
	((node (dom-tag content))
	 (children (dom-children content)))
      (cond
       ((not node) content)
       ((eq node 'html)
	(isar-parse-output (car (last children))))
       ((or (eq node 'xmlns) (eq node 'meta) (eq node 'link)) nil)
       ((eq node 'head)
	(isar-parse-output (car (last children))))
       ((eq node 'body)
	(mapconcat 'isar-parse-output children ""))

       ((eq node 'block)
	(concat
	 (if (dom-attr content 'indent)
	     " "
	   "")
	 (mapconcat 'isar-parse-output children "")))

       ((eq node 'class)
	(mapconcat 'isar-parse-output children ""))
       ((eq node 'pre)
	(mapconcat 'isar-parse-output children ""))

       ((eq node 'state_message)
	(concat "\n" (mapconcat 'isar-parse-output children "") "\n"))

       ((eq node 'information_message)
	(propertize (concat (mapconcat 'isar-parse-output children "") "\n")
		    'font-lock-face (cdr (assoc "dotted_information" isar-get-font))))

       ((eq node 'warning_message)
	(propertize (concat (mapconcat 'isar-parse-output children "") "\n")
		    'font-lock-face (cdr (assoc "text_overview_error" isar-get-font))))

       ((eq node 'error_message)
	(propertize (concat (mapconcat 'isar-parse-output children "") "\n")
		    'font-lock-face (cdr (assoc "dotted_warning" isar-get-font))))

       ((eq node 'text_fold)
	(concat
	 (if (< 1 (length children)) "\n" "")
	 (mapconcat 'isar-parse-output children "")))

       ((eq node 'subgoal)
	(concat "\n" (mapconcat 'isar-parse-output children "")))

       ((eq node 'span)
	(format "%s" (car (last children))))

       ((or (eq node 'position))
	(isar-parse-output (car (last children))))

       ((eq node 'keyword1)
	(propertize (isar-parse-output (car (last children)))
		    'font-lock-face (cdr (assoc "text_keyword1" isar-get-font))))

       ((eq node 'intensify)
	(propertize (isar-parse-output (car (last children)))
		    'font-lock-face (cdr (assoc "background_intensify" isar-get-font))))

       ((eq node 'keyword2)
	(propertize (isar-parse-output (car (last children)))
		    'font-lock-face (cdr (assoc "text_keyword2" isar-get-font))))

       ((eq node 'keyword3)
	(propertize (isar-parse-output (car (last children)))
		    'font-lock-face (cdr (assoc "text_keyword3" isar-get-font))))

       ((eq node 'keyword4)
	(propertize (isar-parse-output (car (last children)))
		    'font-lock-face (cdr (assoc "text_keyword4" isar-get-font))))

       ((eq node 'fixed)
	(isar-parse-output (car (last children))))

       ((eq node 'free)
	(propertize (format "%s" (car (last children)))
		    'font-lock-face (cdr (assoc "text_free" isar-get-font))))

       ((eq node 'tfree)
	(propertize (format "%s" (car (last children)))
		    'font-lock-face (cdr (assoc "text_tfree" isar-get-font))))

       ((eq node 'tvar)
	(propertize (format "%s" (car (last children)))
		    'font-lock-face (cdr (assoc "text_tvar" isar-get-font))))

       ((eq node 'var)
	(propertize (format "%s" (car (last children)))
		    'font-lock-face (cdr (assoc "text_var" isar-get-font))))

       ((eq node 'bound)
	(propertize (format "%s" (car (last children)))
		    'font-lock-face (cdr (assoc "text_bound" isar-get-font))))

       ((eq node 'skolem)
	(propertize (isar-parse-output (car (last children)))
		    'font-lock-face (cdr (assoc "text_skolem" isar-get-font))))

       ((eq node 'sendback)
	(concat (isar-parse-output (car (last children)))))

       ((eq node 'bullet)
	(concat "\n- " (mapconcat 'isar-parse-output children "") "")) ;; TODO proper utf8

       ((or (eq node 'language)
	    (eq node 'literal))
	(mapconcat 'isar-parse-output children ""))

       ((or (eq node 'delimiter))
	(concat (mapconcat 'isar-parse-output children "") ""))

       ((or (eq node 'entity))
        (concat (mapconcat 'isar-parse-output children "") ""))

       ((or (eq node 'writeln_message))
	(propertize (concat (mapconcat 'isar-parse-output children "") "\n")
		    'font-lock-face (cdr (assoc "dotted_writeln" isar-get-font))))

       ((eq node 'paragraph)
	(concat "\n" (mapconcat 'isar-parse-output children "") "\n"))

       ((eq node 'item)
	(message "%s" (mapconcat 'isar-parse-output children ""))
	(concat (mapconcat 'isar-parse-output children "") "\n"))

       ((eq node 'break)
	(let ((children (mapcar (lambda (a) (string-remove-suffix "'" (string-remove-prefix "'" a))) children)))
	 (concat
	 (cond ((dom-attr content 'width) " ")
	      ((dom-attr content 'line) "\n")
	      (t ""))
	 (mapconcat 'isar-parse-output children ""))))

       ((or (eq node 'xml_elem))
	(mapconcat 'isar-parse-output children ""))

       ((or (eq node 'xml_body)) "")

       ((or (eq node 'sub)) (format "%s" (car (last children)))) ;; TODO sub deserves proper support

       (t
	(if (and (listp node))
	    (progn
;;	      (message "ignoring node %s" node)
	      (concat
	       (format "%s" node)
	       (mapconcat 'isar-parse-output children "")))
	  (progn
	    (message "unrecognised content %s; node is: %s" content node)
	    (concat (format "%s" node))))
	)
       )
      ))))

(defun replace-regexp-lisp (REGEXP TO-STRING)
  "replace-regexp as indicated in the help"
   (while (re-search-forward REGEXP nil t)
    (replace-match TO-STRING nil nil)))

(defun isar-update-output-buffer (content)
  "Updates the output progress"
  (setq parsed-content nil)
  (let ((inhibit-read-only t) )
    (save-excursion
      (with-current-buffer isar-output-buffer
	(setq parsed-content
	      (with-temp-buffer
		(if content
		    (progn
		      (insert content)
		      (beginning-of-buffer)
		      (replace-regexp-lisp "\n\\( *\\)" "<break line = 1>'\\1'</break>")
		      (beginning-of-buffer)
		      (replace-regexp-lisp ">\\( *\\)<entity" "><break>'\\1'</break><entity")
		      (beginning-of-buffer)
		      (replace-regexp-lisp ">\\( *\\)<xml" "><break>'\\1'</break><xml")
		      (beginning-of-buffer)
		      (replace-regexp-lisp "xml_elem>\\( *\\)<" "xml_elem><break>'\\1'</break><")
		      (message (buffer-string))
		      ;;(message content)
		      ;;(message "%s"(libxml-parse-html-region  (point-min) (point-max)))
	              (setq parsed-content (libxml-parse-html-region  (point-min) (point-max)))
		      ;; (with-current-buffer "*scratch*"
		      ;; 	(beginning-of-buffer)
		      ;; 	(insert content)
		      ;; 	(beginning-of-buffer)
		      ;; (replace-regexp "\n\\( *\\)" "<break line = 1>'\\1'</break>")
		      ;; 	  )
		  )
		
		)))
;;	(message  "parsed output = %s" (isar-parse-output parsed-content))
	(setf (buffer-string) (isar-parse-output parsed-content))
	(if (buffer-string)
	    (progn))
	(beginning-of-buffer)
	(ignore-errors
	  (progn
	    (search-forward "Proof outline with cases:")
	    (setq isar-proof-cases-content (buffer-substring (point) (point-max)))))))))

(defun lsp-isar-initialize-output-buffer ()
  (setq isar-output-buffer (get-buffer-create "*isar-output*"))
  (save-excursion
    (with-current-buffer isar-output-buffer
      (read-only-mode t)
      (isar-goal-mode))))

(defun lsp-isar-insert-cases ()
    "insert the last seen outline"
  (interactive)
  (insert isar-proof-cases-content))


(modify-coding-system-alist 'file "*isar-output*" 'utf-8-auto)

(provide 'lsp-output)