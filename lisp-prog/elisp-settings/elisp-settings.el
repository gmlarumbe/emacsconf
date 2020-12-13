;;; elisp-settings.el --- Elisp  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package elisp-mode
  :ensure nil
  :bind (:map emacs-lisp-mode-map
              ("C-c C-l" . larumbe/load-file-current-buffer)
              ("C-c C-b" . larumbe/byte-compile-current-buffer)
              ("C-c C-f" . larumbe/elisp-flycheck-mode)
              ("C-c C-t" . hydra-elisp/body)
              ("C-c C-e" . edebug-defun)
              ("C-c h"   . sanityinc/headerise-elisp)
              ("C-M-z"   . eval-region))
  :hook ((emacs-lisp-mode . my-elisp-hook))
  :config
  (use-package edebug
    :ensure nil
    :bind (:map edebug-mode-map
                ("?" . hydra-edebug/body)))

  (setq flycheck-emacs-lisp-load-path 'inherit)
  (setq flycheck-emacs-lisp-initialize-packages t)

  (require 'elisp-utils)
  (require 'elisp-templates)
  (sanityinc/enable-check-parens-on-save))


(provide 'elisp-settings)

;;; elisp-settings.el ends here
