;;; lsp-isar-types.el --- Interface -*- lexical-binding: t; -*-

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
;;
;;
;;

;;; Commentary:

;; This file defines the types of the various messages that can be sent by Isabelle.
;; We must define them in a separate file (and not in the file we want to use).

;;; Code:

(require 'lsp-mode)

;; types
(cl-defstruct (lsp-isar-ov
	       (:constructor lsp-isar-ov-create)
	       ;; :named is not really useful in our case
	       (:type vector))
  "Syntax highlighting representation.

It contains the overlay that is printed at that position.  The
positions (x0, y0) and (x1, y1) correspond to the beginning and
the end of the overlay."
  (x0 0 :read-only t :type 'int)
  (y0 0 :read-only t :type 'int)
  (x1 0 :read-only t :type 'int)
  (y1 0 :read-only t :type 'int)
  (overlay nil :read-only t))

(lsp-interface
 (lsp-isar:DecorationRange (:range) nil)
 (lsp-isar:Decorations (:uri :type :content) nil))

(lsp-interface
 (lsp-isar:DynamicOutput (:content) nil))

(lsp-interface
 (lsp-isar:Progress (:nodes-status) nil)
 (lsp-isar:TheoryProgress (:name :unprocessed :running :finished :failed :consolidated :warned) nil))


(lsp-interface
 (lsp-isar:FindTheoremOutput (:content) nil))


(provide 'lsp-isar-types)

;;; lsp-isar-types.el ends here