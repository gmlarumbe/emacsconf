;;; init-verilog.el --- Verilog/SystemVerilog  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package verilog-mode
  :mode (("\\.[st]*v[hp]*\\'" . verilog-mode) ;.v, .sv, .svh, .tv, .vp
         ("\\.psl\\'"         . verilog-mode)
         ("\\.vams\\'"        . verilog-mode)
         ("\\.vinc\\'"        . verilog-mode)
         ;; Other custom formats
         ("\\.vsrc\\'"        . verilog-mode)
         ("\\.vsrc.pp\\'"     . verilog-mode)
         ("\\.v.pp\\'"        . verilog-mode)
         ("\\.ppv\\'"         . verilog-mode))
  :hook ((verilog-mode . larumbe/verilog-hook)
         (verilog-mode . larumbe/verilog-flycheck-hook))
  :bind (:map verilog-mode-map
              ("<return>" . larumbe/electric-verilog-terminate-line)
              ([delete]   . delete-forward-char)
              ("C-%"      . hide/show-comments-toggle)
              ("M-s ."    . larumbe/verilog-isearch-forward-symbol-at-point)
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
              ("C-c l"    . larumbe/verilog-insert-instance-from-file)
              ("C-c i"    . larumbe/verilog-indent-current-module)
              ("C-c a"    . larumbe/verilog-align-ports-current-module)
              ("C-c b"    . larumbe/verilog-beautify-current-module)
              ("C-c c"    . larumbe/verilog-toggle-connect-port)
              ("C-c C-t"  . hydra-verilog/body)
              ("C-c C-l"  . larumbe/verilog-align-parameters-current-module)
              ("C-c C-c"  . larumbe/verilog-connect-ports-recursively)
              ("C-c C-p"  . larumbe/verilog-preprocess)
              ("C-c C-f"  . larumbe/verilog-flycheck-mode)
              ("<f8>"     . larumbe/verilog-vhier-current-file))
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
  ;; Many thanks to Kaushal Modi (https://scripter.co/)
  (require 'setup-verilog)
  (require 'verilog-modi)
  ;; Own functions
  (require 'verilog-utils)
  (require 'verilog-templates)
  (require 'verilog-overrides)
  (require 'verilog-navigation)
  (require 'verilog-indentation)
  (require 'verilog-imenu)
  (require 'verilog-vhier)
  (require 'verilog-flycheck)
  (require 'verilog-font-lock))


(provide 'init-verilog)

;;; init-verilog.el ends here
