;;; verilog-completion.el --- Verilog Completion   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(require 'verilog-mode)
(require 'company-keywords)

;; Company keywords for Verilog
(add-to-list 'company-keywords-alist (append '(verilog-mode) verilog-keywords))

;; TODO: Add some CAPF improvements?
;; `verilog-completion-at-point' is added to CAPF. It calls `verilog-completion' which in turns
;; completes depending on the context. This context is determined based on indentation. Since
;; indentation is changed, this could be the reason why it fails. Or maybe it works fine but I didn't use it properly.
;; Study `verilog-completion'.
;;
;; `verilog-complete-word' and `verilog-show-completions' are fallbacks for Emacs versions lacking `completion-at-point'
;;
;; Get some idea for words in opened buffers? Like hippie? Is that a backend for company already?

(provide 'verilog-completion)

;;; verilog-completion.el ends here
