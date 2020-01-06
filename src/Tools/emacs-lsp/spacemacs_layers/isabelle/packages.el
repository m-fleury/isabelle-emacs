;;; packages.el --- isabelle layer packages file for Spacemacs.
;;
;; Copyright (c) 2018-2020 Mathias Fleury
;;
;; Author: Mathias Fleury, Sophie
;; URL: https://github.com/syl20bnr/spacemacshttps://bitbucket.org/zmaths/isabelle2019-vsce/
;;
;;; License: GPLv3

;;; Commentary:

;; See the Spacemacs documentation and FAQs for instructions on how to implement
;; a new layer:
;;
;;   SPC h SPC layers RET
;;
;;
;; Briefly, each package to be installed or configured by this layer should be
;; added to `isabelle-packages'. Then, for each package PACKAGE:
;;
;; - If PACKAGE is not referenced by any other Spacemacs layer, define a
;;   function `isabelle/init-PACKAGE' to load and initialize the package.

;; - Otherwise, PACKAGE is already referenced by another Spacemacs layer, so
;;   define the functions `isabelle/pre-init-PACKAGE' and/or
;;   `isabelle/post-init-PACKAGE' to customize the package as it is loaded.

;; async and yasnippet are already included somewhere else

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

(defun isabelle/init-isar-mode ()
  (use-package isar-mode
    :mode ("\\.thy\\'" . isar-mode))
  (use-package isar-goal-mode
    :after isar-mode))


(defun isabelle/post-init-yasnippet ()
  (push (concat lsp-isar-path-to-isabelle "/src/Tools/emacs-lsp/yasnippet") yas-snippet-dirs))

(defun isabelle/init-isar-goal-mode ()
  (use-package isar-goal-mode
    :after isar-mode))

(defun isabelle/init-lsp-isar ()
  (use-package lsp-isar
    :after isar-mode isar-goal-mode
    :config
    (setq lsp-response-timeout 1200)
    (setq lsp-restart 'ignore)
    (setq lsp-prefer-flymake nil))
  (add-hook 'isar-mode-hook 'flycheck-mode)
  (add-hook 'isar-mode-hook 'lsp-isar-define-client-and-start)
  (add-hook 'lsp-isar-init-hook 'lsp-isar-open-output-and-progress-right-spacemacs))


;;; packages.el ends here
