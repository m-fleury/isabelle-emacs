;;; lsp-isar-progress.el --- Progress buffer for Isabelle ;;; -*- lexical-binding: t; -*-

;; Copyright (C) 2018-2020 Mathias Fleury

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
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

;;
;; The idea is simply to send the progress request regularly (every
;; second or so).
;;
;; Sometimes, the processing takes a lot of time and several request
;; are sent through. To avoid that, we delay the next request from
;; ``lsp-isar-progress-request-max-delay'' seconds
;;

;;; Commentary:

;; blabla

;;; Code:
(require 'lsp-mode)
(require 'dash)
(require 'lsp-isar-types)

;; progress
(defvar lsp-isar-progress-buffer nil "Contains the buffer to that contains the progress.")
(defvar lsp-isar-progress-request-max-delay 3 "Maximum delay for printing.")
(defvar lsp-isar-progress--request-delay 0 "Intial delay before printing.")
(defvar lsp-isar-progress--max-thy-name-length 10 "Longest theory name (and lower bound).")
(defvar lsp-isar-progress--max-goal-number-length 3 "Longest number of goals name (and lower bound).")

(defcustom lsp-isar-progress-theory-name-map (lambda (x) x)
  "Replace theory names in progress buffer.

This function can be set to normalize theory name shown in the
output buffer.  An example of this consists in removing or
shortening prefixes of buffers with the same name."
  :type 'function
  :group 'isabelle)

(lsp-defun lsp-isar-progress--update-buffer (_workspace (&lsp-isar:Progress :nodes-status))
  "Update the progress buffer and centers it on the current edited buffer with STATUS."
  (setq lsp-isar-progress--request-delay 0)
  (let ((inhibit-read-only t)
	(current-thy-name (if (buffer-file-name) (file-name-base (buffer-file-name)) nil))
	(current-thy-point nil)
	(current-thy-line nil)
	(current-thy-line-found nil)
	s)

    ;; if the cursor was already in the buffer store the
    ;; position.
    (if (eq (current-buffer) lsp-isar-progress-buffer)
	(setq current-thy-point (point)))

    (with-current-buffer lsp-isar-progress-buffer
      (setq current-thy-line 0)
      (setq current-thy-line-found nil)
      (setf (buffer-string) "")
      (seq-doseq (theory_status nodes-status)
	(-let [(&lsp-isar:TheoryProgress :name :unprocessed :failed :running :finished :consolidated :warned) theory_status]
	  (-let* ((thyname-raw (file-name-base name))
		  (thyname (funcall lsp-isar-progress-theory-name-map thyname-raw)))
	    (progn
	      (let* ((total (+ unprocessed running warned failed finished))
		     (processed (+ warned finished)))
		(progn
		  (when (or current-thy-line-found
			    (string= thyname-raw current-thy-name))
		    (setq current-thy-line-found t))
		  (unless current-thy-line-found
		    (cl-incf current-thy-line))
		  (setq lsp-isar-progress--max-thy-name-length
			(max lsp-isar-progress--max-thy-name-length
			     (length thyname)))
		  (setq lsp-isar-progress--max-goal-number-length
			(max lsp-isar-progress--max-goal-number-length
			     (length (number-to-string total))))
		  (setq s
			(format
			 (concat
			  "%" (number-to-string lsp-isar-progress--max-thy-name-length)  "s"
			  " %" (number-to-string lsp-isar-progress--max-goal-number-length) "s /"
			  " %" (number-to-string lsp-isar-progress--max-goal-number-length) "s,"
			  " ✖: %2s, ⌛: %2s\n")
			 thyname
			 (number-to-string processed)
			 (number-to-string total)
			 (number-to-string failed)
			 (number-to-string running)))
		  (if (and consolidated (= unprocessed 0) (= failed 0) (= running 0))
		      (insert (propertize s 'font-lock-face '(:foreground "LightSalmon4")))
		    (if (/= failed 0)
			(insert (propertize s 'font-lock-face '(:background "saddle brown")))
		      (if (/= running 0)
			  (insert (propertize s 'font-lock-face '(:background "medium sea green" :foreground "black")))
			(insert s))))))))))
      (when (get-buffer-window lsp-isar-progress-buffer 'visible)
	(with-selected-window (get-buffer-window lsp-isar-progress-buffer)
	  (goto-char (point-min))
	  (if current-thy-point
	      (goto-char current-thy-point)
	    (forward-line current-thy-line))
	  (recenter -1))))))


(defun lsp-isar-progress--request-buffer ()
  "Request progress update."
  (with-demoted-errors
      (progn
	(if (<= lsp-isar-progress--request-delay 0)
	    (let ((my-message (lsp-make-notification "PIDE/progress_request" nil)))
	      (lsp-send-notification my-message)
	      (setq lsp-isar-progress--request-delay lsp-isar-progress-request-max-delay)))
	(setq lsp-isar-progress--request-delay  (- lsp-isar-progress--request-delay 1)))))

(defun lsp-isar-progress-activate-progress-update ()
  "Activate the progress request."
  (setq lsp-isar-progress-buffer (get-buffer-create "*lsp-isar-progress*"))
  (save-excursion
    (with-current-buffer lsp-isar-progress-buffer
      (font-lock-mode)
      (read-only-mode t)))
  (run-at-time 0 1 #'lsp-isar-progress--request-buffer))


(modify-coding-system-alist 'file "*lsp-isar-progress*" 'utf-8-auto)

(provide 'lsp-isar-progress)

;;; lsp-isar-progress.el ends here
