;;; verilog-which-func.el --- Verilog which func  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defvar-local verilog-ext-which-func-xtra nil
  "Variable to hold extra information for `which-func' to show in the
mode-line. For instance, if point is under \"module top\", `which-func' would
show \"top\" but also show extra information that it's a \"module\".")



(defun verilog-ext-which-func ()
  (setq-local which-func-functions '(verilog-ext-find-module-instance-bwd
                                     verilog-ext-get-header)))


(defun verilog-ext-which-func-update-format ()
  (setq-local which-func-format
              `("["
                (:propertize verilog-ext-which-func-xtra
                 local-map ,which-func-keymap
                 face (which-func :weight bold)
                 mouse-face mode-line-highlight)
                ":"
                (:propertize which-func-current
                 local-map ,which-func-keymap
                 face which-func
                 mouse-face mode-line-highlight)
                "]")))

;;;;; Setup
(add-hook 'verilog-mode-hook #'verilog-ext-which-func)



(provide 'verilog-which-func)

;;; verilog-which-func.el ends here
