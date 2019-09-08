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
(defvar isar-output-buffer nil)
(defvar isar-proof-cases-content nil)

(defun isar-parse-output (content)
 ;; (message "content = %s" content)
  (cond
   ((not content) nil)
   ((stringp content)
   ;; (message "stringp %s" content)
    content)
   ((not (listp content))
    ;;(message "listp content")
    (format "%s" content))
   (t
    (let
	((node (dom-tag content))
	 (children (dom-children content)))
      (cond
       ((not node) content)
       ((eq node 'html)
	(isar-parse-output (last children)))
       ((eq node 'xmlns) nil)
       ((eq node 'head)
	(isar-parse-output (children)))
       ((eq node 'body)
	(isar-parse-output (cadr children)))

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
	(concat "info: " (mapconcat 'isar-parse-output children "") "\n"))

       ((eq node 'text_fold)
	(mapconcat 'isar-parse-output children ""))

       ((eq node 'keyword)
	(mapconcat 'isar-parse-output children ""))

       ((eq node 'subgoal)
	(concat "\n" (mapconcat 'isar-parse-output children "")))

       ((eq node 'span)
	(format "%s" (last children)))

       ((or (eq node 'position))
	(isar-parse-output (last children)))

       ((eq node 'keyword1)
	(isar-parse-output (last children)))

       ((eq node 'fixed)
	(isar-parse-output (last children)))

       ((eq node 'free)
	(propertize (isar-parse-output (last children))
		    'font-lock-face (cdr (assoc "text_free" isar-get-font))))

       ((eq node 'tfree)
	(propertize (isar-parse-output (last children))
		    'font-lock-face (cdr (assoc "text_tfree" isar-get-font))))

       ((eq node 'tvar)
	(propertize (isar-parse-output (last children))
		    'font-lock-face (cdr (assoc "text_tvar" isar-get-font))))

       ((eq node 'var)
	(propertize (isar-parse-output (last children))
		    'font-lock-face (cdr (assoc "text_var" isar-get-font))))

       ((eq node 'bound)
	(propertize (isar-parse-output (last children))
		    'font-lock-face (cdr (assoc "text_bound" isar-get-font))))

       ((eq node 'skolem)
	(propertize (isar-parse-output (last children))
		    'font-lock-face (cdr (assoc "text_skolem" isar-get-font))))

       ((eq node 'sendback)
	(concat (isar-parse-output (last children))))

       ((or (eq node 'language) (eq node 'delimiter)
	    (eq node 'entity) (eq node 'literal))
	(isar-parse-output (last children)))

       ((or (eq node 'writeln_message))
	(propertize (concat (mapconcat 'isar-parse-output children "") "\n")
		    'font-lock-face (cdr (assoc "dotted_writeln" isar-get-font))))

       ((eq node 'paragraph)
	(concat "\n" (mapconcat 'isar-parse-output children "") "\n"))

       ((eq node 'break)
	(cond ((dom-attr content 'width) " ")
	      (t "")))

       ((or (eq node 'xml_elem)) (isar-parse-output (last children)))

       ((or (eq node 'sub)) (format "%s" (last children))) ;; TODO sub deserves proper support

       (t
	(if (and (listp node))
	    (progn
;;	      (message "ignoring node %s" node)
	      (concat
	       (format "%s" node)
	       (mapconcat 'isar-parse-output children "")))
	  (progn
;;	    (message "unrecognised content %s; node is: %s" content node)
	    (concat (format "%s" node) (format "%s" content))))
	)
       )
      ))))

(defun isar-update-output-buffer (content)
  "Updates the output progress"
  (setq parsed-content nil)
  (let ((inhibit-read-only t) )
    (save-excursion
      (with-current-buffer isar-output-buffer
	(setq parsed-content
	      (with-temp-buffer
		(insert content)
	        (setq parsed-content (libxml-parse-html-region  (point-min) (point-max)))
		))
	(message  "parsed output = %s" (isar-parse-output parsed-content))
	(setf (buffer-string) (isar-parse-output parsed-content))
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