;;; init-sh-script.el --- Shell Script  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package sh-script
  :straight nil
  :hook ((sh-mode . larumbe/sh-mode-hook)
         (sh-mode . eglot-ensure))
  :bind (:map sh-mode-map
         ("C-c C-c" . sh-show-shell)
         ("C-c C-p" . larumbe/sh-send-line-or-region-and-step-vterm)
         ("C-c C-k" . sh-send-line-or-region-and-step)
         ("C-c C-t" . hydra-sh/body)
         ("C-?"     . larumbe/sh-man-thing-at-point)
         ("C-M-?"   . larumbe/sh-bro))
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
    (setq-local company-backends (append '(company-shell) company-backends))))


(provide 'init-sh-script)

;;; init-sh-script.el ends here
