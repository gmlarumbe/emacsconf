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
  (setq verilog-minimum-comment-distance        1) ; (default 10) Only applies to AUTOs, called in `verilog-set-auto-endcomments'
  ;; Alignment
  (setq verilog-align-assign-expr t)
  (setq verilog-align-typedef-words nil) ; Rely on `verilog-ext' to automatically update it
  (setq verilog-align-typedef-regexp (concat "\\<" verilog-identifier-re "_\\(t\\|if\\|vif\\)\\>")) ; INFO: Set on specific machines
  ;; Mode config
  (remove-hook 'compilation-mode-hook 'verilog-error-regexp-add-emacs) ; `verilog-mode' automatically adds useless compilation regexp alists
  (advice-add 'electric-verilog-terminate-line :before-until #'larumbe/newline-advice)) ; Quit *xref* buffer with C-m/RET


(use-package verilog-ext
  :straight (:host github :repo "gmlarumbe/verilog-ext"
             :files (:defaults "snippets" "ts-mode/*.el"))
  :after verilog-mode
  :demand
  :hook ((verilog-mode . verilog-ext-mode)
         (verilog-mode . larumbe/verilog-ext-mode-hook))
  :mode (("\\.v\\'"   . verilog-ts-mode)
         ("\\.sv\\'"  . verilog-ts-mode)
         ("\\.vh\\'"  . verilog-ts-mode)
         ("\\.svh\\'" . verilog-ts-mode))
  :init
  (setq verilog-ext-feature-list
        '(font-lock
          hierarchy
          eglot
          lsp
          flycheck
          beautify
          navigation
          template
          formatter
          compilation
          imenu
          which-func
          hideshow
          time-stamp
          block-end-comments
          company-keywords
          ports
          typedefs
          ;; xref
          capf))
  :config
  (setq verilog-ext-flycheck-verible-rules '("-line-length"
                                             "-parameter-name-style"))
  (verilog-ext-flycheck-set-linter 'verilog-verible)
  (setq verilog-ext-flycheck-use-open-buffers nil)
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
  ;; Setup
  (verilog-ext-mode-setup)

  (defun larumbe/verilog-ext-mode-hook ()
    "Verilog hook."
    (setq-local company-backends '(company-files company-capf company-gtags))))


(provide 'init-verilog)

;;; init-verilog.el ends here