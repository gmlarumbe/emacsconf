;;; init-fpga.el --- FPGA related packages  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package fpga
  :mode (("\\.qpf\\'" . conf-mode))  ; Quartus project file
  :config
  (set-face-attribute 'fpga-utils-compilation-msg-code-face nil :foreground "gray55")
  (set-face-attribute 'fpga-utils-compilation-bin-face nil      :foreground "goldenrod")
  (set-face-attribute 'fpga-utils-brackets-face nil             :foreground "goldenrod")
  (set-face-attribute 'fpga-utils-parenthesis-face nil          :foreground "dark goldenrod")
  (set-face-attribute 'fpga-utils-curly-braces-face nil         :foreground "DarkGoldenrod2")
  (set-face-attribute 'fpga-utils-braces-content-face nil       :foreground "yellow green")
  (set-face-attribute 'fpga-utils-punctuation-face nil          :foreground "burlywood"))

(use-package fpga-larumbe-utils ; provide `larumbe/fpga-uvm-copy-timestamp' derived functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/fpga-larumbe-utils.el")))

(use-package wavedrom-mode
  :config
  (set-face-attribute 'wavedrom-font-lock-brackets-face nil :foreground "goldenrod")
  (set-face-attribute 'wavedrom-font-lock-punctuation-face nil :foreground "burlywood"))

(use-package vunit-mode)

(use-package test-hdl
  :straight (:host github :repo "gmlarumbe/test-hdl" :files (:defaults)))


(provide 'init-fpga)

;;; init-fpga.el ends here
