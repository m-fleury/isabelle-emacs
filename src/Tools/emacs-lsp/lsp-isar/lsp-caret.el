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


(require 'lsp-mode)

(defcustom lsp-isar-limit-position-updates nil
  "don't send caret updates when the cursor stays in the same word.")

(defvar last-post-command-position 0
  "Holds the cursor position from the last run of post-command-hooks.")

(defvar last-post-command-word ""
  "Holds the cursor position from the last run of post-command-hooks.")

(define-inline lsp-caret_update (uri line char focus)
  "Make a Caret_Update object for the given LINE and CHAR.

interface Caret_Update {
    uri;
    line: number;
    character: number;
    focus: boolean
}"
  (inline-quote (list :uri ,uri :line ,line :character ,char :focus ,focus)))

(define-inline lsp-cur-line ()
  (inline-quote (1- (line-number-at-pos))))

(define-inline lsp-cur-column ()
  (inline-quote (- (point) (line-beginning-position))))

(defun lsp--buffer-uri ()
  "Return URI of the current buffer."
  (or lsp-buffer-uri
      (lsp--path-to-uri
       (or buffer-file-name (ignore-errors (buffer-file-name (buffer-base-buffer)))))))

(defun lsp--path-to-uri (path)
  "Convert PATH to a uri."
  (concat lsp--uri-file-prefix
          (url-hexify-string (replace-regexp-in-string (regexp-quote "/home/salt") "/local/home/salt" (expand-file-name path) nil 'literal)
                             url-path-allowed-chars)))

(define-inline lsp-cur-caret_update ()
  "Make a Caret_Update object for the current point."
  (inline-quote
   (save-restriction
     (widen)
     (lsp-caret_update (or lsp-buffer-uri (lsp--path-to-uri buffer-file-name))
		   (lsp-cur-line)
		   (lsp-cur-column)
		   1
		   ))))

(defun lsp--isar-send-caret-update ()
  (let ((my-message (lsp-make-notification "PIDE/caret_update" (lsp-cur-caret_update))))
    (lsp-send-notification my-message)))

(defun lsp-isar-update-caret ()
  (let ((my-current-word (thing-at-point 'word)))
    (if (and (boundp 'lsp--cur-workspace)
	     (not (equal (point) last-post-command-position))
	     (or
	      (not lsp-isar-limit-position-updates)
	      (equal my-current-word nil)
	      (not (equal my-current-word last-post-command-word)) ; the word has changed
	      (and
	       (> (point) last-post-command-position)
	       (> (- (point) last-post-command-position) 80)) ; or we have moved from around one line
	      (and
	       (< (point) last-post-command-position)
	       (< (- last-post-command-position (point)) 80))))
	(progn
	  (lsp--isar-send-caret-update)
	  (setq last-post-command-position (point))
	  (setq last-post-command-word my-current-word)))))


;; https://stackoverflow.com/questions/26544696/an-emacs-cursor-movement-hook-like-the-javascript-mousemove-event
(defun lsp-isar-activate-caret-update ()
  (add-to-list 'post-command-hook #'lsp-isar-update-caret)
  (lsp--isar-send-caret-update))


(provide 'lsp-caret)
