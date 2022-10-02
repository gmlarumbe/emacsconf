;;; verilog-which-func.el --- Verilog which func  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'which-func)
(require 'verilog-navigation)


(defvar-local verilog-ext-which-func-xtra nil
  "Variable to hold extra information for `which-func'.")


(defun verilog-ext-which-func-shorten-block (block-type)
  "Try to shorten name of BLOCK-TYPE."
  (cond ((string= "function"  block-type) "func")
        ((string= "task"      block-type) "task")
        ((string= "class"     block-type) "cls")
        ((string= "module"    block-type) "mod")
        ((string= "interface" block-type) "itf")
        ((string= "package"   block-type) "pkg")
        ((string= "program"   block-type) "pgm")
        ((string= "generate"  block-type) "gen")
        (t block-type)))

(defun verilog-ext-which-func-function ()
  "Function to retrieve `which-func' candidates."
  (let (data)
    (cond ((setq data (verilog-ext-instance-at-point))
           (setq verilog-ext-which-func-xtra (cdr data))
           (car data))
          ((setq data (verilog-ext-block-at-point))
           (setq verilog-ext-which-func-xtra (cdr data))
           (verilog-ext-which-func-shorten-block (car data)))
          (t
           (setq verilog-ext-which-func-xtra nil)
           ""))))

(defun verilog-ext-which-func ()
  "Hook for `verilog-mode' to enable `which-func'."
  (setq-local which-func-functions '(verilog-ext-which-func-function))
  (setq-local which-func-format
              `("["
                (:propertize which-func-current
                 face (which-func :weight bold)
                 mouse-face mode-line-highlight)
                ":"
                (:propertize verilog-ext-which-func-xtra
                 face which-func
                 mouse-face mode-line-highlight)
                "]")))

;;;###autoload
(define-minor-mode verilog-ext-which-func-mode
  "Enhanced extensions for `which-func'."
  :lighter ""
  (if verilog-ext-which-func-mode
      (progn
        (add-hook 'verilog-mode-hook #'verilog-ext-which-func)
        (message "Enabled verilog-ext-which-func-mode"))
    (remove-hook 'verilog-mode-hook #'verilog-ext-which-func)
    (message "Disabled verilog-ext-which-func-mode")))



(provide 'verilog-which-func)

;;; verilog-which-func.el ends here
