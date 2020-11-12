;; initialisation of package
(require 'package)
(package-initialize)

(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)

(unless (package-installed-p 'use-package)
  (message "installing package use-package")
  (package-refresh-contents)
  (package-install 'use-package)

  (unless (package-installed-p 'use-package)
    (error "failed to install use-package"))
  )

;; install quelpa
(use-package quelpa
  :ensure t)

(quelpa
 '(quelpa-use-package
   :fetcher git
   :url "https://github.com/quelpa/quelpa-use-package.git"))

(require 'quelpa-use-package)


(use-package lsp-mode
  :ensure t)

(use-package async
  :ensure t)

(use-package isar-mode
  :ensure t
  :mode "\\.thy\\'"
  :quelpa (isar-mode :fetcher github
		     :repo "m-fleury/isar-mode")
  )

(use-package isar-goal-mode
  :ensure t
  :quelpa (isar-goal-mode :fetcher github
			  :repo "m-fleury/isar-mode"))

(use-package lsp-isar
	     :ensure t
	     :quelpa ((lsp-isar :fetcher github
				:repo "m-fleury/isabelle-release"
				:branch "Isabelle2020-more-vscode"
				:files ("src/Tools/emacs-lsp/lsp-isar/*.el"))
				:upgrade t)
  :after lsp-mode
  :commands lsp-isar-define-client-and-start
  :defer t
  :init
  (add-hook 'isar-mode-hook #'lsp-isar-define-client-and-start)
  (add-hook 'lsp-isar-init-hook 'lsp-isar-open-output-and-progress-right-spacemacs)
  :config

  ;; CHANGE HERE: path to isabelle-release repo
  (setq lsp-isar-path-to-isabelle "~/Documents/isabelle/isabelle-release")

  )
