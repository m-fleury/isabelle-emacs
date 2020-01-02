
;;; lsp-isar.el --- Initialise and setup LSP protocol for Isabelle -*- lexical-binding: t -*-


;; Copyright (C) 2018-2020 Mathias Fleury
;; URL: https://bitbucket.org/zmaths/isabelle2019-vsce/

;; Keywords: lisp
;; Version: 0
;; Package-Requires: ((emacs "25.1") (lsp-mode "6.0"))

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


;; lsp-after-initialize-hook might look like the right macro. However, the
;; workspace (lsp--cur-workspace) is not opened yet.
(add-hook 'lsp-after-open-hook
	  (lambda()
	    (if (equal major-mode 'isar-mode)
		(progn
		  (lsp-isar-caret-activate-caret-update)
		  (unless lsp-isar-already-initialised
		    (progn
		      (lsp-isar-output-initialize-output-buffer)
		      (lsp-isar-progress-activate-progress-update)
		      (lsp-isar--init-decorations)
		      (run-hooks 'lsp-isar-init-hook)
		      (setq lsp-isar-already-initialised t)))))))

(defvar lsp-isar--already-split nil
  "boolean to indicate if we have already split the window")

(defvar lsp-isar-split-pattern-three-columns "three columns");;
(defvar lsp-isar-split-pattern-two-columns "three columns");;

(defcustom lsp-isar-split-pattern lsp-isar-split-pattern-two-columns
  "split motif for the columns. Use either lsp-isar-split-pattern-two-columns or
lsp-isar-split-pattern-three-columns."
  :type 'string
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
   (other-window -3))

(defun lsp-isar-open-output-and-progress-right ()
  "opens the *lsp-isar-output* and *lsp-isar-progress* buffers on the right"
  (cond
   ((eq lsp-isar-split-pattern lsp-isar-split-pattern-two-columns)
    (lsp-isar-open-output-and-progress-right-two-columns))
   ((eq lsp-isar-split-pattern lsp-isar-split-pattern-three-columns)
    (lsp-isar-open-output-and-progress-right-three-columns))
   (t (message "unrecognised motif to split window."))))

;; split the window 2 seconds later (the timeout is necessary to give
;; enough time to spacemacs to jump to the theory file). It can be used
;; for example by ``(add-hook 'lsp-isar-init-hook
;; 'lsp-isar-open-output-and-progress-right-spacemacs)''
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
  "Isabelle's LSP server options"
  :type '(list string)
  :group 'isabelle)

(defun lsp-full-isabelle-path ()
  (append
   (list (concat lsp-isar-path-to-isabelle "/bin/isabelle")
	 "vscode_server")
   lsp-vscode-options
   lsp-isabelle-options))

(defvar lsp-isar-already-defined-client nil)


;; declare the lsp mode
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
   lsp-remote-isabelle-options)
  :type '(string)
  :group 'isabelle)


(defvar lsp-isar-tramp nil "Remote config")

(defun lsp-isar-define-client ()
  "defines the lsp-isar-client"
  (if lsp-isar-tramp
      (lsp-register-client
       (make-lsp-client
	:new-connection
	(lsp-tramp-connection ((lambda () (lsp-full-remote-isabelle-path))))
	:major-modes '(isar-mode)
	:server-id 'lsp-isar
	:priority 1
	:remote? t
	;;    :use-native-json t
	:notification-handlers
	(lsp-ht
	 ("PIDE/decoration" 'lsp-isar-update-and-reprint)
	 ("PIDE/dynamic_output" (lambda (w _p) (lsp-isar-output-update-state-and-output-buffer (gethash "content" _p))))
	 ("PIDE/progress" (lambda (w _p) (lsp-isar-progress--update-buffer (gethash "nodes_status" _p)))))))
    (lsp-register-client
     (make-lsp-client
      :new-connection
      (lsp-stdio-connection ((lambda () (lsp-full-isabelle-path))))
      :major-modes '(isar-mode)
      :server-id 'lsp-isar
      :priority 1
      ;;    :remote? lsp-isar-tramp
      ;;    :use-native-json t
      :notification-handlers
      (lsp-ht
       ("PIDE/decoration" 'lsp-isar-update-and-reprint)
       ("PIDE/dynamic_output" (lambda (w _p) (lsp-isar-output-update-state-and-output-buffer (gethash "content" _p))))
       ("PIDE/progress" (lambda (w _p) (lsp-isar-progress--update-buffer (gethash "nodes_status" _p)))))))))


(defun lsp-isar-define-client-and-start ()
  (unless lsp-isar-already-defined-client
      (progn
        (lsp-isar-define-client)
	(setq lsp-isar-already-defined-client t)))
  (lsp))

;; although the communication to the LSP server is done using utf-16,
;; we can only use utf-18
(modify-coding-system-alist 'file "\\.thy\\'" 'utf-8-auto)


(defvar lsp-isar-experimental nil
  "experimental settings")

(defun lsp-isar-activate-experimental-features ()
  (if lsp-isar-experimental
      (progn
	(message "activating experimental feature is lsp-isar. Set lsp-isar-experimental to nil to avoid it")
	(set (make-local-variable 'indent-line-function) 'lsp-isar-indent-line))))

(add-hook 'isar-mode-hook #'lsp-isar-activate-experimental-features)

(provide 'lsp-isar)

;;; lsp-isar.el ends here