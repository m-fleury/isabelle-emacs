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
;; The idea is simply to send the progress request regularly (every
;; second or so).
;;
;; Sometimes, the processing takes a lot of time and several request
;; are sent through. To avoid that, we delay the next request from
;; ``lsp-isar-progress-request-max-delay'' seconds
;;

;;; Code:


;; progress
(defvar lsp-isar-progress-buffer nil "Contains the buffer to that contains the progress")
(defvar lsp-isar-progress-request-max-delay 3)
(defvar lsp-isar--progress-request-delay 0)

;; TODO requires to iterate over the result
(defun lsp-isar--update-progress-buffer (status)
  "Updates the progress buffer and centers it on the current edited buffer"
  (setq lsp-isar--progress-request-delay 0)
  (let ((inhibit-read-only t)
	(current-thy-name (if (buffer-file-name) (file-name-base) nil)))
    (save-excursion

      ;; if the cursor was already in the buffer store the
      ;; position.
      (if (eq (current-buffer) lsp-isar-progress-buffer)
	  (setq current-thy-point (point))
	(setq current-thy-point nil))
      (with-current-buffer lsp-isar-progress-buffer
	(setq current-thy-line 0)
	(setq current-thy-line-found nil)
	(setf (buffer-string) "")
	(seq-doseq (theory_status status)
	  (progn
	    (let*
		((theory (gethash "name" theory_status))
		 (unprocessed (gethash "unprocessed" theory_status theory_status))
		 (initialized (gethash "initialized" theory_status))
		 (running (gethash "running" theory_status))
		 (finished (gethash "finished" theory_status))
		 (failed (gethash "failed" theory_status))
		 (consolidated (gethash "consolidated" theory_status)))
	      (progn
		(let* ((warned (gethash "warned" theory_status))
		       (total (+ unprocessed running warned failed finished))
		       (processed (+ warned finished)))
		  (progn
		    (if (or current-thy-line-found
			    (string= (file-name-base theory) current-thy-name))
			(progn
			  (setq current-thy-line-found t)))
		    (unless current-thy-line-found
		      (setq current-thy-line (+ 1 current-thy-line)))
		    (setq s (concat (file-name-base theory)
				    " "
				    (number-to-string processed)
				    " / " (number-to-string total)
				    ", ✖: " (number-to-string failed)
				    ", ⌛:" (number-to-string running)
				    "\n"))
		    (if (and consolidated (= unprocessed 0) (= failed 0) (= running 0))
			(insert (propertize s 'font-lock-face '(:foreground "LightSalmon4")))
		      (if (/= failed 0)
			  (progn
			    (setq coloured_text (propertize s 'font-lock-face '(:background "saddle brown")))
			    (insert coloured_text))
			(if (/= running 0)
			    (progn
			      (setq coloured_text (propertize s 'font-lock-face '(:background "medium sea green" :foreground "black")))
			      (insert coloured_text))
			  (insert s))))))))))
	(when (get-buffer-window lsp-isar-progress-buffer 'visible)
	  (with-selected-window (get-buffer-window lsp-isar-progress-buffer)
	    (goto-char (point-min))
	    (if current-thy-point
		(goto-char current-thy-point)
	    (forward-line (1- current-thy-line)))))
	))))


(defun lsp-isar--request-buffer ()
   (with-demoted-errors
       (progn
	 (if (<= lsp-isar--progress-request-delay 0)
	   (let ((my-message (lsp-make-notification "PIDE/progress_request" nil)))
	     (lsp-send-notification my-message)
	     (setq lsp-isar--progress-request-delay lsp-isar-progress-request-max-delay)))
	 (setq lsp-isar--progress-request-delay  (- lsp-isar--progress-request-delay 1))) 
     ))

(defun lsp-isar-activate-progress-update ()
  "Activate the progress request"
  (setq lsp-isar-progress-buffer (get-buffer-create "*lsp-isar-progress*"))
  (save-excursion
    (with-current-buffer lsp-isar-progress-buffer
      (font-lock-mode)
      (read-only-mode t)))
  (run-at-time 0 1 #'lsp-isar--request-buffer)
  )


(modify-coding-system-alist 'file "*lsp-isar-progress*" 'utf-8-auto)

(provide 'lsp-progress)