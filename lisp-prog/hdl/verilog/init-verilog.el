;;; init-verilog.el --- Verilog/SystemVerilog  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package verilog-mode
  :straight (:repo "veripool/verilog-mode"
             :fork (:repo "gmlarumbe/verilog-mode"))
  :mode (;; Emacs will add "\\.[ds]?va?h?\\'" by default
         ("\\.psl\\'"   . verilog-mode)
         ("\\.vams\\'"  . verilog-mode)
         ("\\.vinc\\'"  . verilog-mode))
  :bind (:map verilog-mode-map
         ([delete]  . delete-forward-char)
         ("C-%"     . hide/show-comments-toggle)
         (";"       . nil) ; Unmap automatically indent lines after ;
         ;; TODO: Remove these when proper PR sets them as default?
         ("C-M-a"   . verilog-beg-of-defun)
         ("C-M-e"   . verilog-end-of-defun)
         ("C-M-h"   . verilog-mark-defun)
         ;; End of TODO
         ;; TODO: Checking
         ("C-M-d"   . verilog-ext-find-module-instance-fwd)
         ("C-M-u"   . verilog-ext-find-module-instance-bwd)
         ("M-i"     . verilog-ext-imenu)
         ;; End of TODO
         ("C-c C-o" . verilog-pretty-expr) ; C-c C-i same as C-c TAB that executes `verilog-pretty-declarations'
         ("C-c C-b" . nil)                 ; Unmap `verilog-submit-bug-report', leave space for something else
         ("C-c C-d" . nil)                 ; Unmap `verilog-goto-defun' until it's fixed, leave space for some verilog-ext function
         ("C-c /"   . nil)                 ; Unmap `verilog-star-comment'
         ("M-RET"   . nil)) ; Leave space for `company-complete'
  :config
  ;; Indentation
  (defvar larumbe/verilog-indent-level 4)
  (setq verilog-indent-level             larumbe/verilog-indent-level)
  (setq verilog-indent-level-module      larumbe/verilog-indent-level)
  (setq verilog-indent-level-declaration larumbe/verilog-indent-level)
  (setq verilog-indent-level-behavioral  larumbe/verilog-indent-level)
  (setq verilog-indent-level-directive   larumbe/verilog-indent-level)
  (setq verilog-case-indent              larumbe/verilog-indent-level)
  (setq verilog-cexp-indent              larumbe/verilog-indent-level)
  (setq verilog-indent-lists                  nil)
  (setq verilog-indent-begin-after-if           t)
  (setq verilog-tab-always-indent               t) ; Indent even though we are not at the beginning of line
  (setq verilog-tab-to-comment                nil)
  (setq verilog-date-scientific-format          t)
  (setq verilog-case-fold                     nil) ; Regexps should NOT ignore case
  (setq verilog-align-ifelse                  nil)
  ;; Verilog AUTO
  (setq verilog-auto-delete-trailing-whitespace t) ; ‘delete-trailing-whitespace’ in ‘verilog-auto’.
  (setq verilog-auto-indent-on-newline          t) ; Self-explaining
  (setq verilog-auto-lineup                   nil) ; other options are 'declarations or 'all
  (setq verilog-auto-newline                  nil)
  (setq verilog-auto-endcomments                t)
  (setq verilog-minimum-comment-distance        1) ; INFO: (default 10) Only applies to AUTOs, called in `verilog-set-auto-endcomments'
  ;; Alignment
  (setq verilog-align-assign-expr t)
  (setq verilog-align-typedef-words nil) ; INFO: Set on specific machines
  (setq verilog-align-typedef-regexp (concat "\\<" verilog-identifier-re "_t\\>")) ; INFO: Set on specific machines
  ;; Mode config
  (remove-hook 'compilation-mode-hook 'verilog-error-regexp-add-emacs) ; `verilog-mode' automatically adds useless compilation regexp alists
  (advice-add 'electric-verilog-terminate-line :before-until #'larumbe/newline-advice)) ; Quit *xref* buffer with C-m/RET


;; (use-package verilog-ext
;;   :straight nil
;;   :after verilog-mode
;;   :demand
;;   :commands (verilog-ext-flycheck-select-linter)
;;   :hook ((verilog-mode . verilog-ext-hook))
;;   :bind (:map verilog-mode-map
;;          ("M-f"      . verilog-ext-forward-word)
;;          ("M-b"      . verilog-ext-backward-word)
;;          ("M-i"      . verilog-ext-imenu)
;;          ("TAB"      . verilog-ext-electric-verilog-tab)
;;          ("C-M-."    . verilog-ext-find-parent-module)
;;          ("C-M-n"    . verilog-ext-find-token-fwd)
;;          ("C-M-p"    . verilog-ext-find-token-bwd)
;;          ("C-M-u"    . verilog-ext-find-module-instance-bwd)
;;          ("C-M-d"    . verilog-ext-find-module-instance-fwd)
;;          ;; ("C-M-h"    . xah-select-current-block) ; TODO: Create an analogous utility, that selects current 'defun'
;;          ("C-c i"    . verilog-ext-indent-module-at-point)
;;          ("C-c b"    . verilog-ext-beautify-module-at-point)
;;          ("C-c B"    . verilog-ext-beautify-module-at-point)
;;          ("C-c c"    . verilog-ext-toggle-connect-port)
;;          ("C-c C-c"  . verilog-ext-connect-ports-recursively)
;;          ("C-c t"    . verilog-ext-time-stamp-work-new-entry)
;;          ("C-c C-t"  . hydra-verilog/body)
;;          ("C-c C-p"  . verilog-ext-preprocess)
;;          ("C-c C-f"  . verilog-ext-flycheck-mode)
;;          ("<f9>"     . verilog-ext-vhier-current-file))
;;   ;; :config
;;   ;; Dependencies
;;   ;; (require 'xah-lee-functions)
;;   ;; (require 'ag)
;;   ;; Bind chords
;;   ;; (bind-chord "\\\\" #'verilog-ext-jump-to-module-def-at-point verilog-mode-map)
;;   ;; (bind-chord "\|\|" #'verilog-ext-find-parent-module verilog-mode-map)
;;   ;; (key-chord-mode 1)
;;   )


(provide 'init-verilog)

;;; init-verilog.el ends here
