;;; lsp-isar.el --- Initialise and setup LSP protocol for Isabelle -*- lexical-binding: t -*-


;; Copyright (C) 2018-2020 Mathias Fleury
;; URL: https://bitbucket.org/zmaths/isabelle2019-vsce/

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


(require 'lsp-protocol)
(require 'lsp-mode)

(require 'lsp-isar-caret)
(require 'lsp-isar-decorations)
;; (require 'lsp-isar-find-theorems)
(require 'lsp-isar-indent)
(require 'lsp-isar-output)
(require 'lsp-isar-parse-args)
(require 'lsp-isar-progress)

(defcustom lsp-isar-init-hook nil
  "List of functions to be called after Isabelle has been started."
  :type 'hook
  :group 'isabelle)

(defcustom lsp-isar-indentation t
  "Experimental settings."
  :type 'boolean
  :group 'isabelle)

(defcustom lsp-isar-experimental nil
  "Experimental settings."
  :type 'boolean
  :group 'isabelle)

(defvar lsp-isar-already-initialised nil
  "Indicate if initialised.

Boolean to indicate if we have already initialised progress updates,
the output buffer, and the initial hooks.")


(defcustom lsp-isar-tramp nil "Use Tramp to edit remote files."
  :type 'bool
  :group 'isabelle)

(defcustom lsp-isar-file-name-follow-links (lambda (x) x)
  "Function to replace stuff by other stuff.

A typical example is

   (replace-regexp-in-string
      (regexp-quote \"/mnt/doc/isabelle/afp-2020\")
      \"/home/zmaths/Documents/isabelle/afp-2020\"
      path nil 'literal)

where the path are replaced by what you need to be
replaced. Remember that Isabelle canonicalize paths
automatically."
  :type 'function
  :group 'isabelle)

(defcustom lsp-isar-file-name-unfollow-links (lambda (x) x)
  "Function to replace canonical paths by relative paths.

A typical example is

   (replace-regexp-in-string
      (regexp-quote \"/mnt/doc/isabelle/afp-2020\")
      \"/home/zmaths/Documents/isabelle/afp-2020\"
      path nil 'literal)

where the path are replaced by what you need to be
replaced. Remember that Isabelle canonicalize paths
automatically."
  :type 'function
  :group 'isabelle)

(defcustom lsp-isar-use-lsp t
  "Use nil to open files without opening the server.

A potentially easier way to control is to use the option
`--noisabelle' you can pass to Emacs. It has the same effect, but
you can decide at startup what you want."
  :type 'bool
  :group 'isabelle)


(defun lsp-isar-initialise ()
  "Initialise all Isar-related informations."
  (when (equal major-mode 'isar-mode)
    ;; delayed decoration printing
    (lsp-isar-caret-activate-caret-update)
    (lsp-isar-decorations-activate-delayed-printing)
    (unless lsp-isar-already-initialised
      (lsp-isar-output-initialize-output-buffer)
      (lsp-isar-progress-activate-progress-update)
      (lsp-isar-decorations--init-decorations)
      (run-hooks 'lsp-isar-init-hook)
      (setq lsp-isar-already-initialised t))))

;; lsp-after-initialize-hook might look like the right macro.  However, the
;; workspace (lsp--cur-workspace) is not opened yet.
(add-hook 'lsp-after-open-hook
	  'lsp-isar-initialise)

(defvar lsp-isar--already-split nil
  "Boolean to indicate if we have already split the window.")

(defvar lsp-isar-split-pattern-three-columns 'lsp-isar-split-pattern-three-columns)
(defvar lsp-isar-split-pattern-two-columns 'lsp-isar-split-pattern-two-columns)

(defcustom lsp-isar-split-pattern 'lsp-isar-split-pattern-two-columns
  "Split motif for the columns."
  :type
  '(alist
    :key-type
    (choice
     (const :tag "Split in two columns" 'lsp-isar-split-pattern-two-columns)
     (const :tag "Split in three columns (with progress on the right)"
	    'lsp-isar-split-pattern-three-columns)))
  :group 'isabelle);;

;; taken from
;; https://emacs.stackexchange.com/questions/2189/how-can-i-prevent-a-command-from-using-specific-windows
(defun lsp-isar-toggle-window-dedicated ()
  "Dedicate current window to content.

Control whether or not Emacs is allowed to display another
buffer in current window."
  (let ((window (get-buffer-window (current-buffer))))
    (set-window-dedicated-p window (not (window-dedicated-p window)))))

;; unconditionnaly split the window
(defun lsp-isar-open-output-and-progress-right-two-columns ()
  "Opens the *lsp-isar-output* and *lsp-isar-progress* buffers on the right."
  (interactive)
  (split-window-right)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-state*")
  (lsp-isar-toggle-window-dedicated)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-output*")
  (lsp-isar-toggle-window-dedicated)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-progress*")
  (lsp-isar-toggle-window-dedicated)
  (other-window -3))

(defun lsp-isar-open-output-and-progress-right-three-columns ()
  "Opens the *lsp-isar-output* and *lsp-isar-progress* buffers on the right."
  (interactive)
  ;; split first
  (split-window-right)
  (other-window 1)

  ;; split second
  (split-window-right)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-progress*")
  (lsp-isar-toggle-window-dedicated)

  (other-window -1)
  (switch-to-buffer "*lsp-isar-state*")
  (lsp-isar-toggle-window-dedicated)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*lsp-isar-output*")
  (lsp-isar-toggle-window-dedicated)
  (other-window -2))


(defun lsp-isar-open-output-and-progress-right ()
  "Opens the *lsp-isar-output* and *lsp-isar-progress* buffers on the right.

It can be used for example by ``(add-hook 'lsp-isar-init-hook
'lsp-isar-open-output-and-progress-right-spacemacs)'."
  (cond
   ((eq lsp-isar-split-pattern 'lsp-isar-split-pattern-two-columns)
    (lsp-isar-open-output-and-progress-right-two-columns))
   ((eq lsp-isar-split-pattern 'lsp-isar-split-pattern-three-columns)
    (lsp-isar-open-output-and-progress-right-three-columns))
   (t (message "unrecognised motif to split window.  See variable `lsp-isar-split-pattern'"))))

;; split the window 2 seconds later (the timeout is necessary to give
;; enough time to spacemacs to jump to the theory file).
(defun lsp-isar-open-output-and-progress-right-spacemacs ()
  "Split the window with motif defined by `lsp-isar-split-pattern'."
  (run-at-time 2 nil (lambda () (lsp-isar-open-output-and-progress-right))))


(defcustom lsp-isar-path-to-isabelle "/home/zmaths/Documents/isabelle/isabelle2018-vsce"
  "Default path to Isabelle (e.g., /path/to/isabelle/folder)."
  :type 'string
  :group 'isabelle)

(defcustom lsp-vscode-options
  (list
   "-o" "vscode_unicode_symbols"
   "-o" "vscode_pide_extensions"
   "-o" "vscode_caret_perspective=10")
  "Isabelle's LSP server options.

Please refer to the documentation of Isabelle for the full set of
options.  In most cases, you should keep the options
`(list \"-o\" \"vscode_unicode_symbols\" \"-o\"
   \"vscode_pide_extensions\")'.

Set `lsp-isabelle-options' for other options (like importing the AFP)."
  :type '(list string)
  :group 'isabelle)

(defvar lsp-isar--already-defined-client nil
  "Variable testing if the LSP client has already been defined.")


(defcustom lsp-isar-remote-path-to-isabelle
  "isabelle"
  "Default path to Isabelle (e.g., /path/to/isabelle/folder)."
  :type '(string)
  :group 'isabelle)

(defun lsp-full-remote-isabelle-path ()
  "Full remote isabelle command."
  (mapcar (lambda (opt) (replace-regexp-in-string "\\$" "\\$" opt nil 'literal))
	  (append
	   (list lsp-isar-remote-path-to-isabelle
		 "vscode_server")
	   lsp-vscode-options
	   lsp-remote-isabelle-options)))


(defun lsp-full-isabelle-path ()
  "Calculate the full path and the options for Isabelle."
  (append
   (list (concat lsp-isar-path-to-isabelle "/bin/isabelle")
	 "vscode_server")
   lsp-vscode-options
   lsp-isabelle-options))

(defun lsp-isar-define-client ()
  "Defines the LSP client for isar mode.

If `lsp-isar-tramp' is t, then the lsp client is registered as
remote in order to edit files remotely over tramp.  Remember that
`lsp-isar-tramp' uses a different configuration.

Set `lsp-remote-isabelle-options' and `lsp-isabelle-options' to
the AFP and other options."
  ;; declare the lsp mode
  (push  '(isar-mode .  "isabelle") lsp-language-id-configuration)

  (if lsp-isar-tramp
      (lsp-register-client
       (make-lsp-client
	:new-connection (lsp-tramp-connection 'lsp-full-remote-isabelle-path)
	:major-modes '(isar-mode)
	:server-id 'lsp-isar
	:priority 1
	:remote? t
	:notification-handlers
	(lsp-ht
	 ("PIDE/decoration" #'lsp-isar-decorations-update-and-reprint)
	 ("PIDE/dynamic_output" #'lsp-isar-output-update-state-and-output-buffer)
	 ("PIDE/progress" #'lsp-isar-progress--update-buffer)
	 ("PIDE/find-theorems-output" #'lsp-isar-find-theorems-answer))))

    (lsp-register-client
     (make-lsp-client
      :new-connection (lsp-stdio-connection 'lsp-full-isabelle-path)
      :major-modes '(isar-mode)
      :server-id 'lsp-isar
      :priority 1
      :path->uri-fn (lambda (path) (lsp--path-to-uri-1 (funcall lsp-isar-file-name-follow-links path)))
      :uri->path-fn (lambda (path) (funcall lsp-isar-file-name-unfollow-links (lsp--uri-to-path-1 path)))
      :notification-handlers
      (lsp-ht
       ("PIDE/decoration" #'lsp-isar-decorations-update-and-reprint)
       ("PIDE/dynamic_output" #'lsp-isar-output-update-state-and-output-buffer)
       ("PIDE/progress" #'lsp-isar-progress--update-buffer)
       ("PIDE/find-theorems" #'lsp-isar-find-theorems-answer))))))


;;;###autoload
(defun lsp-isar-define-client-and-start ()
  "Setup the LSP client if required and start LSP in the current buffer.

This is the main entry point of the lsp-isar client.  To start the
mode automically, use `(add-hook 'isar-mode-hook
#'lsp-isar-define-client-and-start)'"
  ;; starting lsp
  (when (or (not lsp-isar-use-lsp) lsp-isar-parse-args-noisabelle)
    (message "not starting the server! Set lsp-isar-use-lsp to t for that and do not pass '--noisabelle' as argument to Emacs."))
  (unless (or
           (not lsp-isar-use-lsp)
           lsp-isar-parse-args-noisabelle
           (boundp 'lsp-isar-already-started))
    (set (make-local-variable 'lsp-isar-already-started) t)
    (unless lsp-isar--already-defined-client
      (lsp-isar-define-client)
      (setq lsp-isar--already-defined-client t))
    (lsp)))


;; although the communication to the LSP server is done using utf-16,
;; we can only use utf-8
(modify-coding-system-alist 'file "\\.thy\\'" 'utf-8-auto)

(defun lsp-isar-activate-indentation ()
  "Activate automatic indentation by default."
  (when lsp-isar-indentation
    (set (make-local-variable 'indent-line-function) 'lsp-isar-indent-line)))

(add-hook 'isar-mode-hook #'lsp-isar-activate-indentation)


(defun lsp-isar-activate-experimental-features ()
  "Activate experimental features."
  )

(add-hook 'isar-mode-hook #'lsp-isar-activate-experimental-features)



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

(defun lsp-isar-insert-sendback (&optional proof-command prover isar keep-command)
  "Insert proof from PROVER in ISAR, keeping the command if KEEP-COMMAND.

Looks at the last sledgehammer result, removes the word
PROOF-COMMAND if pointed at, then inserts the proofs if any.

The parameter PROVER is the prover name (or a subset of it) and
the ISAR is t if the Isar proof version should be taken.

If there is no proof, the sledgehammer call is not removed and
the transient is re-opened."
  (interactive "P")
  ;;(message "word-at-point= %s %s" (word-at-point) (eq (word-at-point) "sledgehammer"))
  (let* ((prover (if prover prover "cvc4"))
	 (sh1 (alist-get prover lsp-isar-output-proof-cases-content
			 nil nil
			 (lambda (key prover)
			   (if isar
			       (and (cl-search prover key) (cl-search "Isar" key))
			     (and (cl-search prover key) (not (cl-search "Isar" key)))))))
	 ;; if no proof was found try to find it with the opposite Isar value
	 (sh (if sh1
		 sh1
	       (alist-get prover lsp-isar-output-proof-cases-content
			  nil nil
			  (lambda (key prover)
			    (if (not isar)
				(and (cl-search prover key) (cl-search "Isar" key))
			      (and (cl-search prover key) (not (cl-search "Isar" key)))))))))
    ;; (message "looking for %s in %s (isar? %s), found: %s" prover
    ;; lsp-isar-output-proof-cases-content isar sh)
    (if (not sh)
	(if (string= proof-command "sledgehammer")
	    (lsp-isar-sledgehammer-interface))
      (if (and (not keep-command) (string= (word-at-point) proof-command))
	  (lsp-isar-kill-word-at-point)
        (end-of-line)
	(insert "\n"))
      (insert (car sh)))))

(defun lsp-isar-insert-sledgehammer-proof (prover isar keep-sledgehammer)
  "Insert proof by PROVER found in ISAR, keeping the command if KEEP-SLEDGEHAMMER.

See documentation from `lsp-isar-insert-sendback' for more details"
  (interactive "P")
  (lsp-isar-insert-sendback "sledgehammer" prover isar keep-sledgehammer))


(defun lsp-isar-insert-try0-proof ()
  "Insert proof obtained by try0 and deletes the try0 command."
  (interactive)
  (lsp-isar-insert-sendback "try0" "Try this: " nil nil))


(defun lsp-isar-insert-proof-outline ()
  "Insert proof outline."
  (interactive)
  (end-of-line)
  (let ((begin (point)))
    (lsp-isar-insert-sendback "Isar" "Isar" nil nil)
    (if lsp-isar-experimental
	(indent-region begin (point)))))


(defun lsp-isar-insert-cases ()
  "Insert the last seen outline at the beginning of the next line.

This is meant to be used for skeletons as generated by
`proof (induction)' or `proof cases'."
  (interactive)
  (lsp-isar-insert-proof-outline))

(require 'transient)

(defun lsp-isar-is-isar (transient)
  "Find out if the --isar option is set in TRANSIENT."
  (--if-let (--first (string-prefix-p "--isar" it)
                     (transient-args transient))
      t
    nil))


(defun lsp-isar-keep-sledgehammer (transient)
  "Find out if the --isar option is set in TRANSIENT."
  (--if-let (--first (string-prefix-p "--keep-sledgehammer" it)
                     (transient-args transient))
      t
    nil))

(defun lsp-isar-insert-sledgehammer-proof-cvc4 (isar keep-sledgehammer)
  "Insert CVC4 proofs in ISAR, keeping sh command if KEEP-SLEDGEHAMMER."
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer-interface)
	 (lsp-isar-keep-sledgehammer 'lsp-isar-sledgehammer-interface)))
  (lsp-isar-insert-sledgehammer-proof "cvc4" isar keep-sledgehammer))

(defun lsp-isar-insert-sledgehammer-proof-z3 (isar keep-sledgehammer)
  "Insert Z3 proofs in ISAR, keeping sh command if KEEP-SLEDGEHAMMER."
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer-interface)
	 (lsp-isar-keep-sledgehammer 'lsp-isar-sledgehammer-interface)))
  (lsp-isar-insert-sledgehammer-proof "z3" isar keep-sledgehammer))

(defun lsp-isar-insert-sledgehammer-proof-SPASS (isar keep-sledgehammer)
  "Insert SPASS proofs in ISAR, keeping sh command if KEEP-SLEDGEHAMMER."
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer-interface)
	 (lsp-isar-keep-sledgehammer 'lsp-isar-sledgehammer-interface)))
  (lsp-isar-insert-sledgehammer-proof "spass" isar keep-sledgehammer))

(defun lsp-isar-insert-sledgehammer-proof-vampire (isar keep-sledgehammer)
  "Insert vampire proofs in ISAR, keeping sh command if KEEP-SLEDGEHAMMER."
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer-interface)
	 (lsp-isar-keep-sledgehammer 'lsp-isar-sledgehammer-interface)))
  (lsp-isar-insert-sledgehammer-proof "vampire" isar keep-sledgehammer))

(defun lsp-isar-insert-sledgehammer-proof-E (isar keep-sledgehammer)
  "Insert E proofs in ISAR, keeping sh command if KEEP-SLEDGEHAMMER."
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer-interface)
	 (lsp-isar-keep-sledgehammer 'lsp-isar-sledgehammer-interface)))
  (lsp-isar-insert-sledgehammer-proof "e" isar keep-sledgehammer))

(defun lsp-isar-insert-sledgehammer-proof-veriT (isar keep-sledgehammer)
  "Insert veriT proofs in ISAR, keeping sh command if KEEP-SLEDGEHAMMER."
  (interactive
   (list (lsp-isar-is-isar 'lsp-isar-sledgehammer-interface)
	 (lsp-isar-keep-sledgehammer 'lsp-isar-sledgehammer-interface)))
  (lsp-isar-insert-sledgehammer-proof "veriT" isar keep-sledgehammer))

(defun lsp-isar-delete-sledgehammer-call ()
  "Insert veriT proofs."
  (interactive)
  (if (string= (word-at-point) "sledgehammer")
      (lsp-isar-kill-word-at-point)))


(transient-define-prefix lsp-isar-sledgehammer-interface ()
  "Interface to insert sledgehammer command in theory.

The options `--isar' is set automatically set if there only one
choice for the given prover."

  ["Options"
   ("i" "Insert Isar proof" "--isar")
   ("k" "Keep sledgehammer call if cursor is on it" "--keep-sledgehammer")]
  ["Insert calls"
   ("c" "CVC4 proofs" lsp-isar-insert-sledgehammer-proof-cvc4)
   ("d" "delete sledgehammer call" lsp-isar-delete-sledgehammer-call)
   ("e" "E proofs" lsp-isar-insert-sledgehammer-proof-E)
   ("s" "SPASS proofs" lsp-isar-insert-sledgehammer-proof-SPASS)
   ("t" "veriT proofs" lsp-isar-insert-sledgehammer-proof-veriT)
   ("v" "vampire proofs" lsp-isar-insert-sledgehammer-proof-vampire)
   ("z" "Z3 proofs" lsp-isar-insert-sledgehammer-proof-z3)])


(define-key isar-mode-map (kbd "C-x s") 'lsp-isar-sledgehammer)


(defun lsp-isar-insert-command (command)
  "Insert COMMAND at cursor position.

If there is no whitespace at cursor position, a space is inserted before COMMAND"
  (interactive)
  (unless (string= (word-at-point) command)
    ;; special case for word|
    (when (and (word-at-point) (not (thing-at-point 'whitespace)))
      (forward-word))
    (backward-char)
    (let ((is-space (thing-at-point 'whitespace)))
      (forward-char)
      (unless is-space
        (insert " ")))
    (insert command)))


(defun lsp-isar-insert-sledgehammer ()
  "Insert sledgehammer.

If there is no whitespace at the current point, we insert a space before
the sledgehammer command."
  (interactive)
  (lsp-isar-insert-command "sledgehammer"))


(defun lsp-isar-insert-sledgehammer-and-call ()
  "Insert sledgehammer and open the interface.

If there is no whitespace at the current point, we insert a space before
the sledgehammer command."
  (interactive)
  (lsp-isar-insert-sledgehammer)
  (lsp-isar-sledgehammer-interface))

(define-key isar-mode-map (kbd "C-c C-s") 'lsp-isar-insert-sledgehammer-and-call)


(defun lsp-isar-insert-try0 ()
  "Insert try0 at cursor position.

If there is no whitespace at cursor position, a space is inserted before try0"
  (interactive)
  (lsp-isar-insert-command "try0"))

(define-key isar-mode-map (kbd "C-c C-t") 'lsp-isar-insert-try0)

(defun lsp-isar-insert-simp ()
  "Insert \"by simp\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by simp"))

(define-key isar-mode-map (kbd "C-c C-b C-s") 'lsp-isar-insert-simp)

(defun lsp-isar-insert-auto ()
  "Insert \"by auto\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by auto"))

(define-key isar-mode-map (kbd "C-c C-b C-a") 'lsp-isar-insert-simp)

(defun lsp-isar-insert-blast ()
  "Insert \"by blast\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by blast"))

(define-key isar-mode-map (kbd "C-c C-b C-b") 'lsp-isar-insert-simp)

(defun lsp-isar-insert-metis ()
  "Insert \"by metis\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by metis"))

(define-key isar-mode-map (kbd "C-c C-b C-m") 'lsp-isar-insert-metis)

(defun lsp-isar-insert-argo ()
  "Insert \"by argo\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by argo"))

(define-key isar-mode-map (kbd "C-c C-b C-r") 'lsp-isar-insert-argo)

(defun lsp-isar-insert-linarith ()
  "Insert \"by linarith\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by linarith"))

(define-key isar-mode-map (kbd "C-c C-b C-l") 'lsp-isar-insert-linarith)

(defun lsp-isar-insert-algebra ()
  "Insert \"by algebra\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by algebra"))

(define-key isar-mode-map (kbd "C-c C-b C-g") 'lsp-isar-insert-algebra)

(defun lsp-isar-insert-presburger ()
  "Insert \"by presburger\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by presburger"))

(define-key isar-mode-map (kbd "C-c C-b C-p") 'lsp-isar-insert-presburger)

(defun lsp-isar-insert-fast ()
  "Insert \"by fast\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by fast"))

(define-key isar-mode-map (kbd "C-c C-b C-f C-a") 'lsp-isar-insert-fast)

(defun lsp-isar-insert-fastforce ()
  "Insert \"by fastforce\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by fastforce"))

(define-key isar-mode-map (kbd "C-c C-b C-f C-f") 'lsp-isar-insert-fastforce)

(defun lsp-isar-insert-force ()
  "Insert \"by force\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by force"))

(define-key isar-mode-map (kbd "C-c C-b C-f C-o") 'lsp-isar-insert-force)

(defun lsp-isar-insert-meson ()
  "Insert \"by meson\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by meson"))

(define-key isar-mode-map (kbd "C-c C-b C-e") 'lsp-isar-insert-meson)

(defun lsp-isar-insert-satx ()
  "Insert \"by satx\" at cursor position with whitespace in front if necessary."
  (interactive)
  (lsp-isar-insert-command "by satx"))

(define-key isar-mode-map (kbd "C-c C-b C-s") 'lsp-isar-insert-satx)

;; This needs to be done at the very beginning!
;; (defun lsp-isar-make-buffer-name-absolute ()
;;   "Replace the current path by the full buffer name."
;;   (setq-local lsp-buffer-uri (lsp--path-to-uri (file-truename (buffer-file-name)))))

;; (add-hook 'lsp-before-initialize-hook #'lsp-isar-make-buffer-name-absolute)

(provide 'lsp-isar)

;;; lsp-isar.el ends here
