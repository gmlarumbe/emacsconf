;;; init-c.el --- C/C++   -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Use `c-mode-common-hook' for changes that apply to every c-style language (java, objC, awk,...)
;;
;;; Code:

(use-package cc-mode
  :init
  (setq c-default-style "linux") ; Indent and style
  (setq c-basic-offset 4))


(use-package c-ts-mode
  :straight nil
  :mode (("\\.c\\'"   . c-or-c++-ts-mode)
         ("\\.cpp\\'" . c-or-c++-ts-mode)
         ("\\.h\\'"   . c-or-c++-ts-mode)
         ("\\.hpp\\'" . c-or-c++-ts-mode)
         ("\\.ino\\'" . c-or-c++-ts-mode)))


(use-package c-utils
  :straight nil
  :after c-ts-mode
  :demand
  :hook ((c-mode      . larumbe/c-and-c++-mode-hook)
         (c++-mode    . larumbe/c-and-c++-mode-hook)
         (c-ts-mode   . larumbe/c-and-c++-ts-mode-hook)
         (c++-ts-mode . larumbe/c-and-c++-ts-mode-hook))
  :init
  (setq larumbe/c-utils-use-lsp nil)
  :config
  (larumbe/c-ts-mode-override))


(use-package hideif
  :after c-ts-mode
  :demand
  :diminish)




(provide 'init-c)

;;; init-c.el ends here
