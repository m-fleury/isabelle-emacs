;;; lsp-isar-caret.el --- Communicate caret position ;;; -*- lexical-binding: t; -*-

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

;;; Commentary:

;; The position of the caret must be updated whenever it moves. This is achieved by instrumenting
;; `post-command-hook' and sending a message.

;;; Code:


(require 'lsp-mode)

(defvar lsp-isar-caret-last-post-command-position 0
  "Holds the cursor position from the last run of post-command-hooks.")

(define-inline lsp-isar-caret-update-struct (uri line char focus)
  "Make a Caret_Update object for the given LINE and CHAR.

interface Caret_Update {
    uri;
    line: number;
    character: number;
    focus: boolean
}"
  (inline-quote (list :uri ,uri :line ,line :character ,char :focus ,focus)))

(define-inline lsp-isar-caret-cur-line ()
  (inline-quote (1- (line-number-at-pos))))

(define-inline lsp-isar-caret-cur-column ()
  (inline-quote (- (point) (line-beginning-position))))

(defun lsp-isar-caret--buffer-uri ()
  "Return URI of the current buffer."
  (or lsp-buffer-uri
      (lsp--path-to-uri
       (or buffer-file-name (ignore-errors (buffer-file-name (buffer-base-buffer)))))))

(define-inline lsp-isar-caret-cur-caret_update ()
  "Make a Caret_Update object for the current point."
  (inline-quote
   (save-restriction
     (widen)
     (lsp-isar-caret-update-struct
      (lsp-isar-caret--buffer-uri)
      (lsp-isar-caret-cur-line)
      (lsp-isar-caret-cur-column)
      1))))

(defun lsp-isar-caret--send-caret-update ()
  "Notify Isabelle about the current caret position."
  (let ((my-message (lsp-make-notification "PIDE/caret_update" (lsp-isar-caret-cur-caret_update))))
    (lsp-send-notification my-message)))

(defun lsp-isar-caret-update-caret-position ()
  "Notify Isabelle about the carrent position if needed.

Test if the position has changed.  If it has changed, then
launch the timer to update send the notification in the near future."
  (when (boundp 'lsp--cur-workspace)
    (lsp-isar-caret--send-caret-update)))


;; https://stackoverflow.com/questions/26544696/an-emacs-cursor-movement-hook-like-the-javascript-mousemove-event
(defun lsp-isar-caret-activate-caret-update ()
  "Initialize automatic update of caret position."
  (add-to-list 'post-command-hook #'lsp-isar-caret-update-caret-position)
  (lsp-isar-caret--send-caret-update))


(provide 'lsp-isar-caret)

;;; lsp-isar-caret.el ends here
