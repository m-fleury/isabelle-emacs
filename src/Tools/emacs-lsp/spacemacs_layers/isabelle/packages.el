;;; packages.el --- isabelle layer packages file for Spacemacs.
;;
;; Copyright (c) 2018-2020 Mathias Fleury
;;
;; Author: Mathias Fleury, Sophie
;; URL: https://bitbucket.org/zmaths/isabelle2019-vsce/
;;
;;; License: Golf3

;;; Commentary:

;; load all lsp-isar related files.

;;; Code:

(defconst isabelle-packages
  '(
    ;; async is in spacemacs-core
    dash
    (isar-mode :location local)
    (isar-goal-mode :location local)
    (lsp-isar :location local)
    yasnippet)
  "The list of Lisp packages required by the isabelle layer.")


(defun isabelle/init-dash ()
  (use-package dash
    :defer t))

;;(defun isabelle/init-yasnippet ()
;;  (use-package yasnippet))

(defun isabelle/init-isar-mode ()
  (use-package isar-mode
    :mode ("\\.thy\\'" . isar-mode)
    :config
    (spacemacs/declare-prefix-for-mode 'lsp-mode "i" "isar")
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ii" 'lsp-isar-insert-sledgehammer-and-call))
  (use-package isar-goal-mode
    :after isar-mode))


(defun isabelle/init-isar-goal-mode ()
  (use-package isar-goal-mode
    :after isar-mode))

(defun isabelle/post-init-yasnippet ()
  )

(defun isabelle/init-lsp-isar ()
  (use-package lsp-isar
    :after isar-mode isar-goal-mode
    :commands lsp-isar-define-client-and-start lsp-isar-open-output-and-progress-right-spacemacs
    :config
    (setq lsp-response-timeout 1200)
    (setq lsp-restart 'ignore)
    (setq lsp-prefer-flymake nil)
    (push (concat lsp-isar-path-to-isabelle "/src/Tools/emacs-lsp/yasnippet") yas-snippet-dirs)
    (yas-reload-all)
        :init
    (add-hook 'isar-mode-hook 'flycheck-mode)
    (add-hook 'isar-mode-hook 'lsp-isar-define-client-and-start)
    (add-hook 'lsp-isar-init-hook 'lsp-isar-open-output-and-progress-right-spacemacs)
    (spacemacs/add-to-hooks 'spacemacs/load-yasnippet '(isar-mode-hook))))

;;; packages.el ends here
