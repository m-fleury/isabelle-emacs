;;; smartparens-isar.el --- Additional configuration for Isar language  -*- lexical-binding: t; -*-


;; This file is not part of GNU Emacs.

;;; License:

;; This file is part of Smartparens.

;;; Commentary:

;; Based on the ML version from smartparens

;;; Code:

(require 'smartparens)

;;; Local pairs for ML-family languages


(sp-with-modes '(isar-mode)
  ;; Disable ` because it is used for image and image_mset
  (sp-local-pair "`" nil :actions nil)
  ;; Disable ' because it is used in types
  (sp-local-pair "'" nil :actions nil)
  (sp-local-pair "\\<open>" "\\<close>" )
  (sp-local-pair "(*" "*)"))

(provide 'smartparens-isar)
;;; smartparens-isar.el ends here