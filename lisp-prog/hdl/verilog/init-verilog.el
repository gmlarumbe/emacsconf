;;; init-verilog.el --- Verilog/SystemVerilog  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package verilog-mode
  :straight (:repo "veripool/verilog-mode"
             :fork (:repo "gmlarumbe/verilog-mode" :branch "bug-sexp"))
  :commands (larumbe/verilog-flycheck-select-linter)
  :mode (;; Emacs will add "\\.[ds]?va?h?\\'" by default
         ("\\.psl\\'"   . verilog-mode)
         ("\\.vams\\'"  . verilog-mode)
         ("\\.vinc\\'"  . verilog-mode))
  :hook ((verilog-mode . larumbe/verilog-hook))
  :bind (:map verilog-mode-map
         ([delete]   . delete-forward-char)
         ("C-%"      . hide/show-comments-toggle)
         ("M-f"      . larumbe/verilog-forward-word)
         ("M-b"      . larumbe/verilog-backward-word)
         ("M-i"      . larumbe/verilog-imenu)
         ("TAB"      . larumbe/electric-verilog-tab)
         ("C-M-a"    . verilog-beg-of-defun)
         ("C-M-e"    . verilog-end-of-defun)
         ("C-M-n"    . larumbe/find-verilog-token-fwd)
         ("C-M-p"    . larumbe/find-verilog-token-bwd)
         ("C-M-u"    . larumbe/find-verilog-module-instance-bwd)
         ("C-M-d"    . larumbe/find-verilog-module-instance-fwd)
         ("C-M-h"    . xah-select-current-block)
         ("C-c i"    . larumbe/verilog-indent-current-module)
         ("C-c b"    . larumbe/verilog-beautify-current-module)
         ("C-c B"    . larumbe/verilog-beautify-current-buffer)
         ("C-c c"    . larumbe/verilog-toggle-connect-port)
         ("C-c C-c"  . larumbe/verilog-connect-ports-recursively)
         ("C-c t"    . larumbe/verilog-time-stamp-work-new-entry)
         ("C-c C-t"  . hydra-verilog/body)
         ("C-c C-p"  . larumbe/verilog-preprocess)
         ("C-c C-f"  . larumbe/verilog-flycheck-mode)
         ("<f9>"     . larumbe/verilog-perl-current-file)
         ("M-RET"    . nil)) ; Leave space for `company-complete'
  :config
  ;; Dependencies
  (require 'xah-lee-functions)
  (require 'ag)
  ;; Bind chords
  (bind-chord "\\\\" #'larumbe/verilog-jump-to-module-at-point verilog-mode-map)
  (bind-chord "\|\|" #'larumbe/verilog-find-parent-module verilog-mode-map)
  ;; Indentation
  (defvar larumbe/verilog-indent-level 4)
  (setq verilog-indent-level             larumbe/verilog-indent-level)
  (setq verilog-indent-level-module      larumbe/verilog-indent-level)
  (setq verilog-indent-level-declaration larumbe/verilog-indent-level)
  (setq verilog-indent-level-behavioral  larumbe/verilog-indent-level)
  (setq verilog-indent-level-directive   larumbe/verilog-indent-level)
  (setq verilog-case-indent              larumbe/verilog-indent-level)
  (setq verilog-cexp-indent              larumbe/verilog-indent-level)
  (setq verilog-indent-lists                    t) ; If set to nil, indentation will not properly detect we are inside a parenthesized expression (instance or ports/parameters)
  (setq verilog-indent-begin-after-if           t)
  (setq verilog-tab-always-indent               t) ; Indent even though we are not at the beginning of line
  (setq verilog-tab-to-comment                nil)
  (setq verilog-date-scientific-format          t)
  (setq verilog-case-fold                     nil) ; Regexps should NOT ignore case
  (setq verilog-align-ifelse                  nil)
  (setq verilog-minimum-comment-distance       10)
  ;; Verilog AUTO
  (setq verilog-auto-delete-trailing-whitespace t) ; ‘delete-trailing-whitespace’ in ‘verilog-auto’.
  (setq verilog-auto-indent-on-newline          t) ; Self-explaining
  (setq verilog-auto-lineup                   nil) ; other options are 'declarations or 'all
  (setq verilog-auto-newline                  nil)
  (setq verilog-auto-endcomments                t)
  ;; Mode config
  (key-chord-mode 1)
  (remove-hook 'compilation-mode-hook 'verilog-error-regexp-add-emacs) ; `verilog-mode' automatically adds useless compilation regexp alists
  (advice-add 'electric-verilog-terminate-line :before-until #'larumbe/newline-advice) ; Quit *xref* buffer with C-m/RET
  ;; Company keywords for Verilog
  (require 'company-keywords)
  (add-to-list 'company-keywords-alist (append '(verilog-mode) verilog-keywords))
  ;; Many thanks to Kaushal Modi (https://scripter.co/)
  (use-package setup-verilog
    :straight (:host github :repo "kaushalmodi/.emacs.d" :local-repo "kmodi"
               :fork (:repo "gmlarumbe/kmodi" :branch "larumbe")
               :files ("setup-files/setup-verilog.el"))
    :demand
    :config
    (require 'verilog-modi))
  ;; Own functions
  (require 'verilog-utils)
  (require 'verilog-templates)
  (require 'verilog-overrides)
  (require 'verilog-navigation)
  (require 'verilog-indentation)
  (require 'verilog-imenu)
  (require 'verilog-vhier)
  (require 'verilog-flycheck)
  (require 'verilog-font-lock)
  (require 'verilog-lsp))


(provide 'init-verilog)

;;; init-verilog.el ends here
