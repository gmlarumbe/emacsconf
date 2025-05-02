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
         ("C-M-h"   . verilog-mark-defun)
         ("C-c C-o" . verilog-pretty-expr) ; C-c C-i same as C-c TAB that executes `verilog-pretty-declarations'
         ("C-c C-b" . nil)                 ; Unmap `verilog-submit-bug-report', leave space for something else
         ("C-c C-d" . nil)                 ; Unmap `verilog-goto-defun' until it's fixed, leave space for some verilog-ext function
         ("C-c /"   . nil)                 ; Unmap `verilog-star-comment'
         ("M-?"     . nil)                 ; Unmap `completion-help-at-point'
         ("M-RET"   . nil)) ; Leave space for `company-complete'
  :hook ((verilog-mode . larumbe/verilog-mode-hook))
  :init
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
  (setq verilog-minimum-comment-distance        1) ; (default 10) Only applies to AUTOs, called in `verilog-set-auto-endcomments'
  ;; Alignment
  (setq verilog-align-assign-expr t)
  (setq verilog-align-typedef-words nil) ; Rely on `verilog-ext' to automatically update it
  (setq verilog-align-typedef-regexp (concat "\\<" "[a-zA-Z_][a-zA-Z_0-9]*" "_\\(t\\|if\\|vif\\)\\>")) ; INFO: Set on specific machines
  :config
  ;; Mode config
  (remove-hook 'compilation-mode-hook 'verilog-error-regexp-add-emacs) ; `verilog-mode' automatically adds useless compilation regexp alists
  (advice-add 'electric-verilog-terminate-line :before-until #'larumbe/newline-advice) ; Quit *xref* buffer with C-m/RET

  (defun larumbe/verilog-mode-hook ()
    "Verilog hook."
    (setq-local company-backends '(company-files company-capf))))


(use-package verilog-ext
  :hook ((verilog-mode . verilog-ext-mode))
  :init
  (setq verilog-ext-flycheck-verible-rules '("-line-length"
                                             "-parameter-name-style"))
  (setq verilog-ext-beautify-instance-extra nil)
  :config
  ;; Setup
  (verilog-ext-mode-setup)
  ;; Flycheck
  (verilog-ext-flycheck-set-linter 'verilog-verible)
  ;; Faces
  (set-face-attribute 'verilog-ext-font-lock-grouping-keywords-face nil :foreground "dark olive green")
  (set-face-attribute 'verilog-ext-font-lock-punctuation-face nil       :foreground "burlywood")
  (set-face-attribute 'verilog-ext-font-lock-operator-face nil          :foreground "burlywood" :weight 'extra-bold)
  (set-face-attribute 'verilog-ext-font-lock-brackets-face nil          :foreground "goldenrod")
  (set-face-attribute 'verilog-ext-font-lock-parenthesis-face nil       :foreground "dark goldenrod")
  (set-face-attribute 'verilog-ext-font-lock-curly-braces-face nil      :foreground "DarkGoldenrod2")
  (set-face-attribute 'verilog-ext-font-lock-port-connection-face nil   :foreground "bisque2")
  (set-face-attribute 'verilog-ext-font-lock-dot-name-face nil          :foreground "gray70")
  (set-face-attribute 'verilog-ext-font-lock-brackets-content-face nil  :foreground "yellow green")
  (set-face-attribute 'verilog-ext-font-lock-width-num-face nil         :foreground "chartreuse2")
  (set-face-attribute 'verilog-ext-font-lock-width-type-face nil        :foreground "sea green" :weight 'bold)
  (set-face-attribute 'verilog-ext-font-lock-module-face nil            :foreground "green1")
  (set-face-attribute 'verilog-ext-font-lock-instance-face nil          :foreground "medium spring green")
  (set-face-attribute 'verilog-ext-font-lock-time-event-face nil        :foreground "deep sky blue" :weight 'bold)
  (set-face-attribute 'verilog-ext-font-lock-time-unit-face nil         :foreground "light steel blue")
  (set-face-attribute 'verilog-ext-font-lock-preprocessor-face nil      :foreground "pale goldenrod")
  (set-face-attribute 'verilog-ext-font-lock-modport-face nil           :foreground "light blue")
  (set-face-attribute 'verilog-ext-font-lock-direction-face nil         :foreground "RosyBrown3")
  (set-face-attribute 'verilog-ext-font-lock-typedef-face nil           :foreground "light blue")
  (set-face-attribute 'verilog-ext-font-lock-translate-off-face nil     :background "gray20" :slant 'italic)
  (set-face-attribute 'verilog-ext-font-lock-uvm-classes-face nil       :foreground "light blue")
  (set-face-attribute 'verilog-ext-font-lock-xilinx-attributes-face nil :foreground "orange1")
  ;; Compilation faces
  (set-face-attribute 'verilog-ext-compile-msg-code-face nil :foreground "gray55")
  (set-face-attribute 'verilog-ext-compile-bin-face nil      :foreground "goldenrod")
  ;; Imenu
  (set-face-attribute 'verilog-ext-imenu-class-item-face nil :foreground "goldenrod" :weight 'bold))


(use-package verilog-ts-mode
  :mode (("\\.s?vh?\\'" . verilog-ts-mode))
  :init
  (setq verilog-ts-imenu-style 'tree-group)
  (setq verilog-ts-beautify-instance-extra nil)
  :config
  ;; Faces
  (set-face-attribute 'verilog-ts-font-lock-grouping-keywords-face nil :foreground "dark olive green")
  (set-face-attribute 'verilog-ts-font-lock-punctuation-face nil       :foreground "burlywood")
  (set-face-attribute 'verilog-ts-font-lock-operator-face nil          :foreground "burlywood" :weight 'extra-bold)
  (set-face-attribute 'verilog-ts-font-lock-brackets-face nil          :foreground "goldenrod")
  (set-face-attribute 'verilog-ts-font-lock-parenthesis-face nil       :foreground "dark goldenrod")
  (set-face-attribute 'verilog-ts-font-lock-curly-braces-face nil      :foreground "DarkGoldenrod2")
  (set-face-attribute 'verilog-ts-font-lock-port-connection-face nil   :foreground "bisque2")
  (set-face-attribute 'verilog-ts-font-lock-dot-name-face nil          :foreground "gray70")
  (set-face-attribute 'verilog-ts-font-lock-brackets-content-face nil  :foreground "yellow green")
  (set-face-attribute 'verilog-ts-font-lock-width-num-face nil         :foreground "chartreuse2")
  (set-face-attribute 'verilog-ts-font-lock-width-type-face nil        :foreground "sea green" :weight 'bold)
  (set-face-attribute 'verilog-ts-font-lock-module-face nil            :foreground "green1")
  (set-face-attribute 'verilog-ts-font-lock-instance-face nil          :foreground "medium spring green")
  (set-face-attribute 'verilog-ts-font-lock-time-event-face nil        :foreground "deep sky blue" :weight 'bold)
  (set-face-attribute 'verilog-ts-font-lock-time-unit-face nil         :foreground "light steel blue")
  (set-face-attribute 'verilog-ts-font-lock-preprocessor-face nil      :foreground "pale goldenrod")
  (set-face-attribute 'verilog-ts-font-lock-modport-face nil           :foreground "light blue")
  (set-face-attribute 'verilog-ts-font-lock-direction-face nil         :foreground "RosyBrown3")
  (set-face-attribute 'verilog-ts-font-lock-translate-off-face nil     :background "gray20" :slant 'italic)
  (set-face-attribute 'verilog-ts-font-lock-attribute-face nil         :foreground "orange1"))


(provide 'init-verilog)

;;; init-verilog.el ends here
