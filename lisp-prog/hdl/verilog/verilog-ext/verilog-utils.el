;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;; TODO: Add some eval-when-compile?
(defvar verilog-ext-keywords-re (regexp-opt verilog-keywords 'symbols))


(defun verilog-ext-path-join (arg1 arg2)
  "Join path of ARG1 and ARG2.
If more than 2 args are required, use `f-join'"
  (if (and arg1 arg2)
      (concat (file-name-as-directory arg1) arg2)
    (error "Cannot join path with nil arguments.")
    nil))



(provide 'verilog-utils)

;;; verilog-utils.el ends here
