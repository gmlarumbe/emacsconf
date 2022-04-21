;;; verilog-completion.el --- Verilog Completion   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(require 'verilog-mode)
(require 'company-keywords)

;; Company keywords for Verilog
(add-to-list 'company-keywords-alist (append '(verilog-mode) verilog-keywords))

;; TODO: Add some CAPF improvements?
;; `verilog-completion-at-point', `verilog-complete-word' and `verilog-show-completions'
;; are fallbacks for Emacs versions lacking `completion-at-point'
;;
;; Get some idea for words in opened buffers? Like hippie? Is that a backend for company already?

(provide 'verilog-completion)

;;; verilog-completion.el ends here
