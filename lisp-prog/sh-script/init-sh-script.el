;;; init-sh-script.el --- Shell Script  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package sh-script
  :ensure nil
  :bind (:map sh-mode-map
              ("C-c C-c" . sh-show-shell)
              ("C-c C-p" . larumbe/sh-send-line-or-region-and-step-ansi)
              ("C-c C-k" . sh-send-line-or-region-and-step)
              ("C-c C-t" . hydra-sh/body))
  :config
  (require 'sh-script-utils)
  (require 'sh-script-templates))


(provide 'init-sh-script)

;;; init-sh-script.el ends here
