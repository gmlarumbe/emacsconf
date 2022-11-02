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
         ("C-;"     . nil) ; Leave space for faster buffer switching
         ;; TODO: Remove these when proper PR sets them as default?
         ("C-M-a"   . verilog-beg-of-defun)
         ("C-M-e"   . verilog-end-of-defun)
         ("C-M-h"   . verilog-mark-defun)
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
  (setq verilog-indent-ignore-regexp "// \\*") ; Ignore outshine headings
  ;; Verilog AUTO
  (setq verilog-auto-delete-trailing-whitespace t) ; ‘delete-trailing-whitespace’ in ‘verilog-auto’.
  (setq verilog-auto-indent-on-newline          t) ; Self-explaining
  (setq verilog-auto-lineup                   nil) ; other options are 'declarations or 'all
  (setq verilog-auto-newline                  nil)
  (setq verilog-auto-endcomments              nil)
  (setq verilog-auto-wire-comment             nil)
  (setq verilog-minimum-comment-distance        1) ; INFO: (default 10) Only applies to AUTOs, called in `verilog-set-auto-endcomments'
  ;; Alignment
  (setq verilog-align-assign-expr t)
  (setq verilog-align-typedef-words nil) ; INFO: Set on specific machines
  (setq verilog-align-typedef-regexp (concat "\\<" verilog-identifier-re "_t\\>")) ; INFO: Set on specific machines
  ;; Mode config
  (remove-hook 'compilation-mode-hook 'verilog-error-regexp-add-emacs) ; `verilog-mode' automatically adds useless compilation regexp alists
  (advice-add 'electric-verilog-terminate-line :before-until #'larumbe/newline-advice)) ; Quit *xref* buffer with C-m/RET


(use-package verilog-ext
  :straight (:host github :repo "gmlarumbe/verilog-ext")
  :after verilog-mode
  :demand
  :bind (:map verilog-mode-map
         ;;TODO: Only during development
         ("C-c C-l"       . verilog-ext-tree-sitter-hl-mode-enable)
         ;; End of TODO
         ("TAB"           . verilog-ext-electric-verilog-tab)
         ("M-d"           . verilog-ext-kill-word)
         ("C-<backspace>" . verilog-ext-backward-kill-word)
         ("M-f"           . verilog-ext-forward-word)
         ("M-b"           . verilog-ext-backward-word)
         ("C-M-d"         . verilog-ext-find-module-instance-fwd)
         ("C-M-u"         . verilog-ext-find-module-instance-bwd-2)
         ("C-M-."         . verilog-ext-jump-to-parent-module)
         ("M-i"           . verilog-ext-imenu-list)
         ("C-c a"         . verilog-ext-module-at-point-align-ports)
         ("C-c l"         . verilog-ext-module-at-point-align-params)
         ("C-c i"         . verilog-ext-module-at-point-indent)
         ("C-c b"         . verilog-ext-module-at-point-beautify)
         ("C-c C-f"       . verilog-ext-flycheck-mode-toggle)
         ("C-c C-t"       . verilog-ext-hydra/body)
         ("<f9>"          . verilog-ext-vhier-current-file))
  :config
  (message "Setting up verilog-ext")
  (verilog-ext-which-func-mode)
  (setq verilog-ext-flycheck-eldoc-toggle t)
  (setq verilog-ext-flycheck-verible-rules '("-line-length"))
  (verilog-ext-flycheck-setup)
  (verilog-ext-flycheck-set-linter 'verilog-verible)
  (setq verilog-ext-snippets-dir "~/.emacs.d/straight/repos/verilog-ext/verilog-snippets")
  (verilog-ext-add-snippets))




(provide 'init-verilog)

;;; init-verilog.el ends here
