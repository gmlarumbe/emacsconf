;;; sh-script-settings.el --- Shell Script  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package sh-script
  :ensure nil
  :bind (:map sh-mode-map
              ("C-c C-j" . sh-switch-to-process-buffer)
              ("C-c C-k" . sh-send-line-or-region-and-step)
              ("C-c C-p" . larumbe/sh-send-line-or-region-and-step-ansi)
              ("C-c C-s" . larumbe/yas-insert-snippet-dwim) ; Unmaps select skeleton
              ("C-c C-t" . hydra-sh/body))
  :hook ((sh-mode . my-sh-mode-hook))
  :config
  (require 'sh-script-utils)
  (require 'sh-script-templates))


(provide 'sh-script-settings)

;;; sh-script-settings.el ends here
