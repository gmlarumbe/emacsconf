;;; verilog-lsp.el --- Verilog Language Server Protocol  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; INFO: To make it work, just add the following at the end of the file so that verible gets added:
;; (verilog-ext-lsp-configure)
;; (verilog-ext-lsp-set-default-server)
;;
;; And execute M-x lsp RET on a verilog-mode buffer (or add it as a hook)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Language servers:
;; - Supported by `lsp-mode' without additional config:
;;   - hdl_checker: https://github.com/suoto/hdl_checker
;;   - svlangserver: https://github.com/imc-trading/svlangserver
;;
;; - With some additional config:
;;   - verible: https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls
;;   - svls (svlint based): https://github.com/dalance/svls
;;   - veridian: https://github.com/vivekmalneedi/veridian
;;
;; Summary:
;;   - All of them somehow seem a bit simple at least with Emacs integration
;;   (might need a bit of research)
;;
;; Some of these might be using slang (SystemVerilog Language Features), which seems a C++ library:
;; - https://github.com/MikePopoloski/slang
;;
;;
;; INFO: Problems encountered:
;; 'verible-ls gave this error continuosly:
;; Error running timer `lsp--on-idle': (wrong-type-argument number-or-marker-p nil)
;;   - Some error probably relatd to `lsp-headerline--check-breadcrumb' due to 'verible-ls
;;     being still in progress
;;
;;; Code:

(require 'lsp-mode)

;;;; Verible
(defun verilog-ext-lsp-configure ()
  "Configure Verilog for LSP."
  (interactive)
  (lsp-register-client
   (make-lsp-client :new-connection (lsp-stdio-connection "verible-verilog-ls")
                    :major-modes '(verilog-mode)
                    :server-id 'verible-ls)))

;;;; Select default
(defun verilog-ext-lsp-set-default-server ()
  "Select svlangserver by default by disabling others without changing priorities."
  (interactive)
  ;; Assumes native support for lsp-verilog and lsp-svlangserver, and that verible-ls is installed
  (add-to-list 'lsp-disabled-clients 'verible-ls)
  (add-to-list 'lsp-disabled-clients 'verilog))


;;;; Enable
(verilog-ext-lsp-configure)
(verilog-ext-lsp-set-default-server)


(provide 'verilog-lsp)

;; TODO: Add configuration of eglot, that should be in some place in prog-packages or like that...


;;; verilog-lsp.el ends here
