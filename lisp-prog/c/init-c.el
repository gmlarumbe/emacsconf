;;; init-c.el --- C/C++   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package cc-mode
  :mode (("\\.ino\\'"  . c-mode))
  :diminish hide-ifdef-mode
  :bind (:map c-mode-map ; Also inherited by c++ buffers, not in the other direction!
              ("C-c f" . semantic-ia-show-summary)
              ("C-c ." . semantic-ia-fast-jump)
              ("C-c ," . pop-global-mark) ; Requires unbinding of <C-c ,> at semantic-mode-map
              )
  ;; INFO: Use `c-mode-common-hook' for changes that apply to every c-style language (java, objC, awk,...)
  :hook ((c-mode   . larumbe/c-and-c++-mode-hook)
         (c++-mode . larumbe/c-and-c++-mode-hook))
  :config
  (setq c-default-style "linux") ; Indent and style
  (setq c-basic-offset 4)

  (require 'c-utils))


(provide 'init-c)

;;; init-c.el ends here
