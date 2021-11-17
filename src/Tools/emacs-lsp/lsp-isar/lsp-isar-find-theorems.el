;;; lsp-isar-find-theorems.el --- Initialise and setup LSP protocol for Isabelle -*- lexical-binding: t -*-


;; Copyright (C) 2018-2020 Mathias Fleury
;; URL: https://github.com/m-fleury/isabelle-release/

;; Keywords: lisp
;; Version: 0
;; Package-Requires: ((emacs "25.1") (lsp-mode "7.0") (transient "0.1.0"))

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

;; blabla

;;; Code:
(require 'lsp-isar-types)

(define-inline lsp-isar-find-theorems-struct (strings)
  "Make a Find_Theorems_Request object for the request STRINGS.

interface Find_Theorems_Request {
  value: strings
}"
  (inline-letevals (strings)
    (inline-quote (list :value ,strings))))

(define-inline lsp-isar-find_theorems-create-struct (strings)
  "Make a Find_Theorems_Request object for the current search STRINGS."
  (inline-letevals (strings)
    (inline-quote
     (lsp-isar-find-theorems-struct ,strings))))

(defun lsp-isar-find-theorems-send-request (strings)
  "Notify Isabelle about the current search STRINGS."
  (let ((my-message (lsp--make-notification "PIDE/find-theorems"
					    (lsp-isar-find_theorems-create-struct strings))))
    (lsp-send-notification my-message)))


(defun lsp-isar-find-theorems (strings)
  "Interactively notify Isabelle about the current search STRINGS."
  (interactive "x\nFind theorems: ")
  (if (vectorp strings)
    (lsp-isar-find-theorems-send-request strings)
    (if (stringp strings)
	(lsp-isar-find-theorems-send-request strings)
      (warn "Failed to recognise request. Either use one
    string (\"_ = _\") or a vector '(\"_ = _\" \"_ * (_ + _)\")"))))

(lsp-defun lsp-isar-find-theorems-answer (_workspace (&lsp-isar:FindTheoremOutput :content))
  "Launch the thread or timer to update the state and the output panel with CONTENT."
  (message "received answer %s" content))

(provide 'lsp-isar-find-theorems)

;;; lsp-isar-find-theorems.el ends here
