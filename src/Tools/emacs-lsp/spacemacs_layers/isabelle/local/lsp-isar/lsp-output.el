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

(defvar isar-output-buffer nil)
(defvar isar-proof-cases-content nil)

(defun isar-update-output-buffer (content)
  "Updates the output progress"
  (let ((inhibit-read-only t))
    (save-excursion
      (with-current-buffer isar-output-buffer
	(setf (buffer-string) content)
	(beginning-of-buffer)
	(ignore-errors
	  (progn
	    (search-forward "Proof outline with cases:")
	    (setq isar-proof-cases-content (buffer-substring (point) (point-max)))))))))

(defun lsp-isar-initialize-output-buffer ()
  (setq isar-output-buffer (get-buffer-create "*isar-output*"))
  (save-excursion
    (with-current-buffer isar-output-buffer
      (read-only-mode t))))

(defun lsp-isar-insert-cases ()
    "insert the last seen outline"
  (interactive)
  (insert isar-proof-cases-content))


(modify-coding-system-alist 'file "*isar-output*" 'utf-8-auto)

(provide 'lsp-output)