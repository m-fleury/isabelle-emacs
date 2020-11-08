;;; lsp-isar-parse-args.el --- Add isabelle options to emacs -*- lexical-binding: t; -*-

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

;;; Commentary

;; We parse arguments passed to emacs of the sort "--isabelle-S" and
;; "--no-isabelle" and set the arguments passed to Isabelle's LSP
;; server accordingly.

;; Code
(defcustom lsp-isar-parse-use t "Flag to indicate whether the library should be used."
  :type 'boolean
  :group 'isabelle)

(defcustom lsp-isar-parse-args-use-isabelle nil "flag to indicate whether to use Isabelle"
  :type 'boolean
  :group 'isabelle)
(defcustom lsp-isar-parse-args-noafp nil "flag to indicate whether to use Isabelle"
  :type 'boolean
  :group 'isabelle)

(defcustom lsp-isar-parse-args-nollvm t "flag to indicate whether to use Isabelle"
  :type 'boolean
  :group 'isabelle)
(defcustom lsp-isar-parse-args-noisafol nil "flag to indicate whether to use Isabelle"
  :type 'boolean
  :group 'isabelle)
(defcustom lsp-isar-parse-args-base-session nil "flag to indicate whether to use Isabelle"
  :type 'string
  :group 'isabelle)

(defcustom lsp-isar-parse-args-noisabelle nil "flag to indicate whether to use Isabelle"
  :type 'boolean
  :group 'isabelle)

(defcustom isabelle-base-session nil "Base session for Isabelle."
  :type 'string
  :group 'isabelle)

(defcustom lsp-isabelle-options (list "-m" "do_notation")
  "Isabelle options (e.g, AFP)."
  :type '(list string)
  :group 'isabelle)

(defcustom lsp-remote-isabelle-options (list "-m" "do_notation") "Isabelle options (e.g, AFP)."
  :type '(list string)
  :group 'isabelle)

(defcustom lsp-isar-parse-args-tramp nil "Flag to indicate whether the library should be used."
  :type 'boolean
  :group 'isabelle)

(setq lsp-isar-parse-args-noisabelle (member "--noisabelle" command-line-args))
(setq command-line-args (delete "--noisabelle" command-line-args))

(setq lsp-isar-parse-args-noafp (member "--isabelle-noafp" command-line-args))
(setq command-line-args (delete "--isabelle-noafp" command-line-args))


(setq lsp-isar-parse-args-tramp (member "--isabelle-tramp" command-line-args))
(when lsp-isar-parse-args-tramp
  (setq lsp-isar-tramp t))
(setq command-line-args (delete "--isabelle-tramp" command-line-args))

(setq lsp-isar-parse-args-nollvm (member "--isabelle-nollvm" command-line-args))
(setq command-line-args (delete "--isabelle-nollvm" command-line-args))

(setq lsp-isar-parse-args-noisafol (member "--isabelle-noisafol" command-line-args))
(setq command-line-args (delete "--isabelle-noisafol" command-line-args))

(defun lsp-isar-parse-args-flatten (list)
  "Flatten a list of lists as a simple list.

Typically a function that should be defined elsewhere and called
flatten."
  (cl-mapcan (lambda (x) (if (listp x) x (list x))) list))


(defun lsp-isar-parse-lsp-isabelle-options ()
  "Combination of all Isabelle options."
  (lsp-isar-parse-args-flatten
   (list
    (if lsp-isar-parse-args-noafp nil (list "-d" "$AFP"))
    (if lsp-isar-parse-args-nollvm nil (list "-d" "$ISABELLE_LLVM"))
    (if lsp-isar-parse-args-noisafol nil (list "-d" "$ISAFOL"))
    (if lsp-isar-parse-args-base-session nil (list "-R" isabelle-base-session)); "IsaSAT"
    "-m" "do_notation"
    "-o" "vscode_output_delay=1"
    "-o" "vscode_caret_perspective=20"
;;    "-v" "-L" "/tmp/isabelle_log"
   ;; "-v" "-L" "/tmp/isabelle_log"
   )))

(defun lsp-isar-parse-combine-isabelle-args ()
  "Parse the arguments passed to emacs."
  (when lsp-isar-parse-use
    (message "%s" "running isabelle settings")
    (setq isabelle-base-session (pop command-line-args-left))
    (setq lsp-isabelle-options (lsp-isar-parse-lsp-isabelle-options))
    (setq lsp-remote-isabelle-options (lsp-isar-parse-lsp-isabelle-options))))

(add-to-list 'command-switch-alist
	     '("-isabelle-S" .
	       (lambda (_) (lsp-isar-parse-combine-isabelle-args))))

(add-to-list 'command-switch-alist
	     '("-isabelle-R" .
	       (lambda (_) (lsp-isar-parse-combine-isabelle-args))))


(provide 'lsp-isar-parse-args)

;;; lsp-isar-parse-args.el ends here