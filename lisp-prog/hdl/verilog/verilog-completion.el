;;; verilog-completion.el --- Verilog Completion   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;; Company keywords for Verilog
(require 'company-keywords)
(add-to-list 'company-keywords-alist (append '(verilog-mode) verilog-keywords))

;; TODO: Add some CAPF improvements?


(provide 'verilog-completion)

;;; verilog-completion.el ends here
