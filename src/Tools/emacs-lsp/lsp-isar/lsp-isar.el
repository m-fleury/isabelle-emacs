;;; lsp-isar.el --- Initialise and setup LSP protocol for Isabelle -*- lexical-binding: t -*-


;; Copyright (C) 2018-2020 Mathias Fleury
;; URL: https://bitbucket.org/zmaths/isabelle2019-vsce/

;; Keywords: lisp
;; Version: 0
;; Package-Requires: ((emacs "25.1") (lsp-mode "6.0") (transient "0.1.0"))

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

;; blabla

;;; Code:


(require 'lsp-mode)
(require 'lsp-isar-caret)
(require 'lsp-isar-output)
(require 'lsp-isar-progress)
(require 'lsp-isar-decorations)
(require 'lsp-isar-indent)

(defcustom lsp-isar-init-hook nil
  "List of functions to be called after Isabelle has been started."
  :type 'hook
  :group 'isabelle)

(defvar lsp-isar-already-initialised nil
  "boolean to indicate if we have already initialised progress updates,
the output buffer, and the initial hooks.")


(defun lsp-isar-initialise ()
  "Initialise all Isar-related informations."
  (if (equal major-mode 'isar-mode)
      (progn
	(lsp-isar-caret-activate-caret-update)
	(unless lsp-isar-already-initialised
	  (progn
	    (lsp-isar-output-initialize-output-buffer)
	    (lsp-isar-progress-activate-progress-update)
	    (lsp-isar-decorations--init-decorations)
	    (run-hooks 'lsp-isar-init-hook)
	    (setq lsp-isar-already-initialised t))))))

;; lsp-after-initialize-hook might look like the right macro. However, the
;; workspace (lsp--cur-workspace) is not opened yet.
(add-hook 'lsp-after-open-hook
	  'lsp-isar-initialise)

(defvar lsp-isar--already-split nil
  "boolean to indicate if we have already split the window")

(defvar lsp-isar-split-pattern-three-columns 'lsp-isar-split-pattern-three-columns)
(defvar lsp-isar-split-pattern-two-columns 'lsp-isar-split-pattern-two-columns)

(defcustom lsp-isar-split-pattern 'lsp-isar-split-pattern-two-columns
  "split motif for the columns.."
  :type
  '(alist
   :key-type
   (choice (const :tag "Split in two columns" 'lsp-isar-split-pattern-two-columns)
	  (const :tag "Split in three columns (with progress on the right)" 'lsp-isar-split-pattern-three-columns)))
  :group 'isabelle);;

;; unconditionnaly split the window
(defun lsp-isar-open-output-and-progress-right-two-columns ()
  "opens the *lsp-isar-output* and *lsp-isar-progress* buffers on the right"
  (interactive)
  (split-window-right)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-state*")
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-output*")
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-progress*")
  (other-window -3))

(defun lsp-isar-open-output-and-progress-right-three-columns ()
  "opens the *lsp-isar-output* and *lsp-isar-progress* buffers on the right"
  (interactive)
  ;; split first
  (split-window-right)
  (other-window 1)

  ;; split second
  (split-window-right)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-progress*")

  (other-window -1)
  (switch-to-buffer "*lsp-isar-state*")
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-output*")
  (other-window -2))


(defun lsp-isar-open-output-and-progress-right ()
  "opens the *lsp-isar-output* and *lsp-isar-progress* buffers on the right.

It can be used for example by ``(add-hook 'lsp-isar-init-hook
'lsp-isar-open-output-and-progress-right-spacemacs)'"
  (cond
   ((eq lsp-isar-split-pattern 'lsp-isar-split-pattern-two-columns)
    (lsp-isar-open-output-and-progress-right-two-columns))
   ((eq lsp-isar-split-pattern 'lsp-isar-split-pattern-three-columns)
    (lsp-isar-open-output-and-progress-right-three-columns))
   (t (message "unrecognised motif to split window. See variable `lsp-isar-split-pattern'"))))

;; split the window 2 seconds later (the timeout is necessary to give
;; enough time to spacemacs to jump to the theory file).
(defun lsp-isar-open-output-and-progress-right-spacemacs ()
  (run-at-time 2 nil (lambda () (lsp-isar-open-output-and-progress-right))))

(defcustom lsp-isar-path-to-isabelle "/home/zmaths/Documents/isabelle/isabelle2018-vsce"
  "default path to Isabelle (e.g., /path/to/isabelle/folder)"
  :type 'string
  :group 'isabelle)

(defcustom lsp-isabelle-options (list "-m" "do_notation")
  "Isabelle options (e.g, AFP)"
  :type '(list string)
  :group 'isabelle)

(defcustom lsp-vscode-options
  (list
   "-o" "vscode_unicode_symbols"
   "-o" "vscode_pide_extensions"
   "-o" "vscode_caret_perspective=10")
  "Isabelle's LSP server options.

Please refer to the documentation of Isabelle for the full set of
options. In most cases, you should keep the options
`(list \"-o\" \"vscode_unicode_symbols\" \"-o\"
   \"vscode_pide_extensions\")'.

Set `lsp-isabelle-options' for other options (like importing the AFP).
"
  :type '(list string)
  :group 'isabelle)

(defun lsp-full-isabelle-path ()
  "Calculate the full path and the options for Isabelle."
  (append
   (list (concat lsp-isar-path-to-isabelle "/bin/isabelle")
	 "vscode_server")
   lsp-vscode-options
   lsp-isabelle-options))

(defvar lsp-isar--already-defined-client nil
  "Variable testing if the LSP client has already been defined")


;; declare the lsp mode
;;;###autoload
(push  '(isar-mode . "isabelle") lsp-language-id-configuration)

(defcustom lsp-isar-remote-path-to-isabelle
  "/home/zmaths/Documents/isabelle-release"
  "default path to Isabelle (e.g., /path/to/isabelle/folder)"
  :type '(string)
  :group 'isabelle)

(defcustom lsp-remote-isabelle-options (list "-m" "do_notation") "Isabelle options (e.g, AFP)"
  :type '(list string)
  :group 'isabelle)

(defun lsp-full-remote-isabelle-path ()
  "full remote isabelle command"
  (append
   (list (concat lsp-isar-remote-path-to-isabelle "/bin/isabelle")
	 "vscode_server")
   lsp-vscode-options
   lsp-remote-isabelle-options))


(defvar lsp-isar-tramp nil "Use Tramp to edit remote files")

(defun lsp-isar-define-client ()
  "defines the LSP client for isar mode.

If `lsp-isar-tramp' is t, then the lsp client is registered as
remote in order to edit files remotely over tramp. Remember that
`lsp-isar-tramp' uses a different configuration.

Set `lsp-remote-isabelle-options' and `lsp-isabelle-options' to
the AFP and other options."
  (if lsp-isar-tramp
      (lsp-register-client
       (make-lsp-client
	:new-connection
	(lsp-tramp-connection (lambda () (lsp-full-remote-isabelle-path)))
	:major-modes '(isar-mode)
	:server-id 'lsp-isar
	:priority 1
	:remote? t
	:notification-handlers
	(lsp-ht
	 ("PIDE/decoration" 'lsp-isar-decorations-update-and-reprint)
	 ("PIDE/dynamic_output" (lambda (_w p) (lsp-isar-output-update-state-and-output-buffer (gethash "content" p))))
	 ("PIDE/progress" (lambda (_w p) (lsp-isar-progress--update-buffer (gethash "nodes_status" p)))))))

    (lsp-register-client
     (make-lsp-client
      :new-connection
      (lsp-stdio-connection (lambda () (lsp-full-isabelle-path)))
      :major-modes '(isar-mode)
      :server-id 'lsp-isar
      :priority 1
      :notification-handlers
      (lsp-ht
       ("PIDE/decoration" 'lsp-isar-decorations-update-and-reprint)
       ("PIDE/dynamic_output" (lambda (_w p) (lsp-isar-output-update-state-and-output-buffer (gethash "content" p))))
       ("PIDE/progress" (lambda (_w p) (lsp-isar-progress--update-buffer (gethash "nodes_status" p)))))))))



;;;###autoload
(defun lsp-isar-define-client-and-start ()
  "Setup the LSP client if required and starts lsp in the current buffer.

This is the main entry point of the lsp-isar client. To start the
mode automically, use `(add-hook 'isar-mode-hook
#'lsp-isar-define-client-and-start)'"
  (unless lsp-isar--already-defined-client
    (progn
      (lsp-isar-define-client)
      (setq lsp-isar--already-defined-client t)))
  (lsp))


;; although the communication to the LSP server is done using utf-16,
;; we can only use utf-8
(modify-coding-system-alist 'file "\\.thy\\'" 'utf-8-auto)


(defvar lsp-isar-experimental nil
  "experimental settings")

(defun lsp-isar-activate-experimental-features ()
  (if lsp-isar-experimental
      (progn
	(message "activating experimental feature is lsp-isar. Set lsp-isar-experimental to nil to avoid it")
	(set (make-local-variable 'indent-line-function) 'lsp-isar-indent-line))))

(add-hook 'isar-mode-hook #'lsp-isar-activate-experimental-features)


(defun lsp-isar-insert-cases ()
  "insert the last seen outline at the beginning of the next line.

This is meant to be used for skeletons as generated by
`proof (induction)' or `proof cases'."
  (interactive)
  (end-of-line)
  (insert "\n")
  (insert lsp-isar-output-proof-cases-content))


;; https://stackoverflow.com/questions/33442027/how-to-deleteor-kill-the-current-word-in-emacs
(defun lsp-isar-kill-thing-at-point (thing)
  "Kill the `thing-at-point' for the specified kind of THING."
  (let ((bounds (bounds-of-thing-at-point thing)))
    (if bounds
        (kill-region (car bounds) (cdr bounds))
      (error "No %s at point" thing))))

(defun lsp-isar-kill-word-at-point ()
  "Kill the word at point."
  (lsp-isar-kill-thing-at-point 'word))

(defun lsp-isar-insert-sledgehammer (&optional prover isar)
  "Looks at the last sledgehammer result, removes the word
  \"sledgehammer\" if pointed at, then inserts the proofs.

The first parameter is the prover name (or a subset of it) and
the second is t if the Isar proof version should be taken."
  (interactive "P")
  ;;(message "word-at-point= %s %s" (word-at-point) (eq (word-at-point) "sledgehammer"))
  (if (string= (word-at-point) "sledgehammer")
      (lsp-isar-kill-word-at-point))
  (let* ((prover (if prover prover "cvc4"))
	 (sh (alist-get prover lsp-isar-output-proof-cases-content
			nil nil
			(lambda (key prover)
			  (if isar
			      (and (cl-search prover key) (cl-search "Isar" key))
			    (cl-search prover key)))))
	 ;; if no proof was found try to find it with the opposite Isar value
	 (sh (if sh
		 sh
	       (alist-get prover lsp-isar-output-proof-cases-content
			  nil nil
			  (lambda (key prover)
			    (if (not isar)
				(and (cl-search prover key) (cl-search "Isar" key))
			      (cl-search prover key)))))))
    ;; (message "looking for %s in %s (isar? %s), found: %s" prover lsp-isar-output-proof-cases-content isar sh)
    (if sh
	(insert (car sh)))))


(require 'transient)

(defun lsp-isar-is-isar (transient)
  "find out if the --isar option is set"
  (--if-let (--first (string-prefix-p "--isar" it)
                     (transient-args transient))
      t
    nil))

(defun lsp-isar-insert-sledgehammer-cvc4 (isar)
  "Insert CVC4 proofs"
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer)))
  (lsp-isar-insert-sledgehammer "cvc4" isar))

(defun lsp-isar-insert-sledgehammer-z3 (isar)
  "Insert Z3 proofs"
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer)))
  (lsp-isar-insert-sledgehammer "z3" isar))

(defun lsp-isar-insert-sledgehammer-SPASS (isar)
  "Insert SPASS proofs"
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer)))
  (lsp-isar-insert-sledgehammer "SPASS" isar))

(defun lsp-isar-insert-sledgehammer-vampire (isar)
  "Insert vampire proofs"
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer)))
  (lsp-isar-insert-sledgehammer "vampire" isar))

(defun lsp-isar-insert-sledgehammer-E (isar)
  "Insert E proofs"
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer)))
  (lsp-isar-insert-sledgehammer "E" isar))

(defun lsp-isar-insert-sledgehammer-veriT (prefix)
  "Insert veriT proofs"
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer)))
  (lsp-isar-insert-sledgehammer "veriT" isar))

(define-transient-command lsp-isar-sledgehammer ()
  "Interface to insert sledgehammer commands to the theory
  buffer.

The options `--isar' is set automatically set if there only one
choice for the given prover."

  ["Options"
   ("i" "Insert Isar proof" "--isar")]
  ["Insert calls"
   ("c" "CVC4 proofs" lsp-isar-insert-sledgehammer-cvc4)
   ("e" "E proofs" lsp-isar-insert-sledgehammer-E)
   ("s" "SPASS proofs" lsp-isar-insert-sledgehammer-SPASS)
   ("t" "veriT proofs" lsp-isar-insert-sledgehammer-veriT)
   ("z" "Z3 proofs" lsp-isar-insert-sledgehammer-z3)])

(provide 'lsp-isar)

;;; lsp-isar.el ends here