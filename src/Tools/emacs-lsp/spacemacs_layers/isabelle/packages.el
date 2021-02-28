;;; packages.el --- isabelle layer packages file for Spacemacs.
;;
;; Copyright (c) 2018-2020 Mathias Fleury
;;
;; Author: Mathias Fleury, Sophie
;; URL: https://github.com/m-fleury/isabelle-release/
;;
;;; License: Golf3

;;; Commentary:

;; load all lsp-isar related files.

;;; Code:

(defconst isabelle-packages
  '(
    ;; async is in spacemacs-core
    (isar-mode :location local)
    (isar-goal-mode :location local)
    (lsp-isar :location local)
    (lsp-isar-parse-args :location local)
    yasnippet)
  "The list of Lisp packages required by the isabelle layer.")

;; there is already a better initialisation in the completion layer
;;(defun isabelle/init-yasnippet ()
;;  (use-package yasnippet))

(defun isabelle/init-isar-mode ()
  (use-package isar-mode
    :mode ("\\.thy\\'" . isar-mode)
    :config
    (spacemacs/declare-prefix-for-mode 'lsp-mode "i" "isar")
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ii" 'lsp-isar-insert-sledgehammer-and-call)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "is" 'lsp-isar-insert-sledgehammer)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ic" 'lsp-isar-insert-proof-outline)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "it" 'lsp-isar-insert-try0)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibs" 'lsp-isar-insert-simp)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "iba" 'lsp-isar-insert-auto)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibb" 'lsp-isar-insert-blast)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibm" 'lsp-isar-insert-metis)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibr" 'lsp-isar-insert-argo)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibl" 'lsp-isar-insert-linarith)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibp" 'lsp-isar-insert-presburger)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibg" 'lsp-isar-insert-algebra)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibfa" 'lsp-isar-insert-fast)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibff" 'lsp-isar-insert-fastforce)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibfo" 'lsp-isar-insert-force)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibe" 'lsp-isar-insert-meson)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibs" 'lsp-isar-insert-satx)
    (spacemacs/set-leader-keys-for-minor-mode 'lsp-mode "ibt" 'lsp-isar-insert-try0-proof)


    (defun evil-insert-line-below-and-indent ()
      (interactive)
      (funcall indent-line-function)
      (evil-open-below 1))
    (defun evil-insert-line-above-and-indent ()
      (interactive)
      (funcall indent-line-function)
      (evil-open-above 1))
    (define-key evil-normal-state-map (kbd "o") 'evil-insert-line-below-and-indent)
    (define-key evil-normal-state-map (kbd "O") 'evil-insert-line-above-and-indent)
    )

  (use-package isar-goal-mode
    :after isar-mode)


  ;; https://github.com/m-fleury/isabelle-release/issues/21
  (defun ~/evil-motion-range--wrapper (fn &rest args)
    "Like `evil-motion-range', but override field-beginning for performance.
See URL `https://github.com/ProofGeneral/PG/issues/427'."
    (cl-letf (((symbol-function 'field-beginning)
               (lambda (&rest args) 1)))
      (apply fn args)))

  (advice-add #'evil-motion-range :around #'~/evil-motion-range--wrapper)
  ;;(advice-add #'evil-ret :around #'~/evil-motion-range--wrapper)

  (add-hook 'isar-mode-hook
	          (lambda ()
		          (progn
		            (setq fill-column 100)
		            (spacemacs/toggle-fill-column-indicator-on))))

  )

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
    (spacemacs/add-to-hooks 'spacemacs/load-yasnippet '(isar-mode-hook))
    ;; :custom
    ;; ((lsp-isar-file-name-follow-links
    ;;   (lambda (path)
    ;;     (replace-regexp-in-string
    ;;      "^/local/home/salt/isabelle/afp-devel"
	  ;;      "/home/salt/isabelle/afp-devel"
    ;;      (replace-regexp-in-string
	  ;;       "^/home/salt/isabelle"
	  ;;       "/local/home/salt/isabelle"
	  ;;       path nil 'literal)
	  ;;      nil 'literal)))
    ;;  (lsp-isar-file-name-unfollow-links
    ;;    (lambda (path)
    ;;      (replace-regexp-in-string
	  ;;       "^/local/home/salt"
	  ;;       "/home/salt"
	  ;;       path nil 'literal))))
    ))

(defun isabelle/init-lsp-isar-parse-args ()
  (use-package lsp-isar-parse-args))

(defun isabelle/post-lsp-isar-parse-args ()
  )

;;; packages.el ends here
