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
;; ``isar-progress-request-max-delay'' seconds
;;

;;; Code:


;; progress
(defvar isar-progress-buffer nil "Contains the buffer to that contains the progress")
(defvar isar-progress-request-max-delay 3)
(defvar isar--progress-request-delay 0)

;; TODO requires to iterate over the result
(defun isar-update-progress-buffer (status)
  "Updates the progress buffer"
  (setq isar--progress-request-delay 0)
  (let ((inhibit-read-only t))
    (save-excursion
      (with-current-buffer isar-progress-buffer
	(progn
	  (setq current-point (point))
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
		      (setq s (concat (file-name-base  theory)
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
	  (goto-char current-point))))))


(defun isar-request-buffer ()
  (if (<= isar--progress-request-delay 0)
      (let ((my-message (lsp-make-notification "PIDE/progress_request" nil)))
	(lsp-send-notification my-message)
	(setq isar--progress-request-delay isar-progress-request-max-delay)))
  (setq isar--progress-request-delay  (- isar--progress-request-delay 1)))


(defun lsp-isar-activate-progress-update ()
  "Activate the progress request"
  (setq isar-progress-buffer (get-buffer-create "*isar-progress*"))
  (save-excursion
    (with-current-buffer isar-progress-buffer
      (font-lock-mode)
      (read-only-mode t)))
  (run-at-time 0 1 #'isar-request-buffer)
  )


(modify-coding-system-alist 'file "*isar-progress*" 'utf-8-auto)

(provide 'lsp-progress)