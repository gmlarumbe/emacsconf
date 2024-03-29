;;; init-sh-script.el --- Shell Script  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package sh-script
  :straight nil
  :mode (("\\.bashrc"  . sh-mode)
         ("\\.xinitrc" . sh-mode))
  :hook ((sh-mode . larumbe/sh-mode-hook)
         (sh-mode . eglot-ensure))
  :bind (:map sh-mode-map
         ("C-c C-c" . sh-show-shell)
         ("C-c C-p" . larumbe/sh-send-line-or-region-and-step-vterm)
         ("C-c C-k" . sh-send-line-or-region-and-step)
         ("C-c C-t" . hydra-sh/body)
         ("C-?"     . larumbe/sh-man-thing-at-point))
  :config
  (require 'sh-script-utils)
  (require 'sh-script-templates))


(use-package company-shell
  :after sh-script
  :demand
  :hook ((sh-mode . larumbe/company-shell-hook))
  :config
  (defun larumbe/company-shell-hook ()
    "Hook to set `company-backends' for `sh-mode'."
    (setq-local company-backends (append '(company-files company-shell) ; Add `company-shell' to default list, but ...
                                         (remove 'company-files company-backends))))) ; ... keep `company-files' with higher precedence


(use-package tldr
  :after sh-script
  :bind (:map sh-mode-map
         ("C-M-?" . tldr)))


(provide 'init-sh-script)

;;; init-sh-script.el ends here
