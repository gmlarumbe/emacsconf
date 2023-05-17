;;; init-c.el --- C/C++   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package cc-mode
  :mode (("\\.ino\\'" . c-mode))
  ;; Use `c-mode-common-hook' for changes that apply to every c-style language (java, objC, awk,...)
  :hook ((c-mode   . larumbe/c-and-c++-mode-hook)
         (c++-mode . larumbe/c-and-c++-mode-hook))
  :init
  (setq c-default-style "linux") ; Indent and style
  (setq c-basic-offset 4)
  :config
  (require 'c-utils))


(use-package hideif
  :after cc-mode
  :demand
  :diminish)


(provide 'init-c)

;;; init-c.el ends here
