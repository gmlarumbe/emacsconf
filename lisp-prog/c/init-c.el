;;; init-c.el --- C/C++   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package cc-mode
  :mode (("\\.ino\\'" . c-or-c++-mode))
  :bind (:map c-mode-map ; Also inherited by c++ buffers, not in the other direction!
              ("C-c f" . semantic-ia-show-summary)
              ("C-c ." . semantic-ia-fast-jump)
              ("C-c ," . pop-global-mark) ; Requires unbinding of <C-c ,> at semantic-mode-map
              )
  :hook ((c-mode-common . my-cc-mode-hook))
  :config
  (use-package semantic
    :bind (:map semantic-mode-map
                ("C-c ," . nil)) ; INFO: Unbinds ALL semantic commands, since C-c , is the prefix
    :hook ((c-mode-common . larumbe/semantic-mode)))

  (setq c-default-style "linux") ; Indent and style
  (setq c-basic-offset 4)

  (require 'c-utils))


(provide 'init-c)

;;; init-c.el ends here
