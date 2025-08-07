;;; init-lsp.el --- LSP  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; LSP: lsp & eglot will override some variables/functionality:
;; - For code navigation they use `xref' under the hood, they set the proper value to `xref-backend-functions'
;; - For syntax checking, they override `flymake' and `flycheck' variables, e.g. they execute (flycheck-select-checker 'lsp) or similar
;; - For code completion, they change `company-backends', overriding it with `company-capf' or adding it to existing ones
;; - etc...
;;
;;; Code:

(use-package eglot
  :straight nil
  :config
  ;; Prevent eglot from overriding value of `company-backends' (eglot value of `completion-at-point-functions' still works)
  (setq eglot-stay-out-of '(company eldoc flymake)))


(use-package lsp-mode
  :hook ((lsp-mode . larumbe/lsp-mode-hook))
  :init
  (setq lsp-keymap-prefix "C-x l")
  (setq lsp-headerline-breadcrumb-enable nil)
  (setq lsp-enable-imenu nil)
  (setq lsp-enable-symbol-highlighting nil)
  :config
  (defun larumbe/lsp-mode-hook ()
    "LSP-Mode hook."
    ;; `lsp-diagnostics' function `lsp-diagnostics-flycheck-enable' is called if customizable var `lsp-auto-configure' is non-nil,
    ;; and if diagnostics are enabled. We want that, but not to be activated right after opening buffer.
    (flycheck-mode -1)))


(use-package lsp-bridge
  :straight '(lsp-bridge :type git :host github :repo "manateelazycat/lsp-bridge"
                         :files (:defaults "*.el" "*.py" "acm" "core" "langserver" "multiserver" "resources")
                         :build (:not compile)))


(use-package lspce ; For the time being requires manual building of the Rust dynamic module: check README.md
  :straight (:host github :repo "zbelial/lspce"
             :files (:defaults "lspce-module.so"))
  :init
  (setq lspce-send-changes-idle-time 1)
  :config
  (lspce-set-log-file "/tmp/lspce.log")
  (lspce-enable-logging))


(provide 'init-lsp)

;;; init-lsp.el ends here
