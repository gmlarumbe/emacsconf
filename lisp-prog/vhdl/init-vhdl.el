;;; init-vhdl.el --- VHDL  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package vhdl-mode
  :straight nil
  :bind (:map vhdl-mode-map
         ("C-M-a" . vhdl-beginning-of-defun)
         ("C-M-e" . vhdl-end-of-defun)
         ("C-M-p" . vhdl-backward-same-indent)
         ("C-M-n" . vhdl-forward-same-indent)
         ("<f5>"  . vhdl-compile)
         ("<f8>"  . sr-speedbar-open))
  :config
  ;; Indentation
  (setq vhdl-basic-offset 4)
  ;; Mode config
  (setq vhdl-clock-edge-condition 'function)
  (setq vhdl-company-name "gmlarumbe")
  (setq vhdl-conditions-in-parenthesis t)
  (setq vhdl-default-library "work")
  (setq vhdl-end-comment-column 120)
  (setq vhdl-platform-spec (capitalize (system-name)))
  (setq vhdl-reset-kind 'sync)
  (setq vhdl-speedbar-auto-open nil)
  (setq vhdl-standard '(08 nil))
  (setq vhdl-modify-date-on-saving nil) ; Use `vhdl-ext' time-stamp instead
  (setq vhdl-hideshow-menu t)
  (setq vhdl-special-syntax-alist nil)  ; Avoid highlighting of _v (variables), _c (constants) and _t (types)
  (vhdl-electric-mode -1)
  (remove-hook 'compilation-mode-hook 'vhdl-error-regexp-add-emacs)
  ;; BUG: With use-package :bind to `vhdl-speedbar-mode-map' this keybinding applied to non-spacebar modes
  (advice-add 'vhdl-speedbar-initialize :after #'(lambda () (define-key vhdl-speedbar-mode-map [? ] #'speedbar-toggle-line-expansion)))
  ;; Newline advice to kill def/refs buffers
  (advice-add 'vhdl-electric-return :before-until #'larumbe/newline-advice)) ; Kill def/refs buffers with C-RET


(use-package vhdl-ext
  :after vhdl-mode
  :demand
  :hook ((vhdl-mode . vhdl-ext-mode))
  :init
  (setq vhdl-ext-feature-list
        '(font-lock
          hierarchy
          eglot
          lsp
          flycheck
          beautify
          navigation
          template
          compilation
          imenu
          which-func
          hideshow
          time-stamp
          company-keywords
          ports))
  (setq vhdl-ext-hierarchy-backend 'builtin)
  :config
  ;; Faces
  (set-face-attribute 'vhdl-ext-font-lock-then-face nil :foreground "dark olive green")
  (set-face-attribute 'vhdl-ext-font-lock-punctuation-face nil :foreground "burlywood")
  (set-face-attribute 'vhdl-ext-font-lock-operator-face nil :inherit 'vhdl-ext-font-lock-punctuation-face :weight 'extra-bold)
  (set-face-attribute 'vhdl-ext-font-lock-brackets-face nil :foreground "goldenrod")
  (set-face-attribute 'vhdl-ext-font-lock-parenthesis-face nil :foreground "dark goldenrod")
  (set-face-attribute 'vhdl-ext-font-lock-curly-braces-face nil :foreground "DarkGoldenrod2")
  (set-face-attribute 'vhdl-ext-font-lock-brackets-content-face nil :foreground "yellow green")
  (set-face-attribute 'vhdl-ext-font-lock-port-connection-face nil :foreground "bisque2")
  (set-face-attribute 'vhdl-ext-font-lock-entity-face nil :foreground "green1")
  (set-face-attribute 'vhdl-ext-font-lock-instance-face nil :foreground "medium spring green")
  (set-face-attribute 'vhdl-ext-font-lock-instance-lib-face nil :foreground "gray70")
  (set-face-attribute 'vhdl-ext-font-lock-translate-off-face nil :background "gray20" :slant 'italic)
  ;; Compilation faces
  (set-face-attribute 'vhdl-ext-compile-msg-code-face nil :foreground "gray55")
  (set-face-attribute 'vhdl-ext-compile-bin-face nil :foreground "goldenrod")
  ;; Setup
  (vhdl-ext-mode-setup)
  (when (executable-find "vhdl_ls")
    (add-hook 'vhdl-mode-hook (lambda () (when (locate-dominating-file default-directory "vhdl_ls.toml") (lsp))))))


(use-package vhdl-ts-mode
  :straight (:host github :repo "gmlarumbe/vhdl-ext"
             :files ("ts-mode/vhdl-ts-mode.el"))
  :config
  ;; Faces
  (set-face-attribute 'vhdl-ts-font-lock-then-face nil :foreground "dark olive green")
  (set-face-attribute 'vhdl-ts-font-lock-punctuation-face nil :foreground "burlywood")
  (set-face-attribute 'vhdl-ts-font-lock-operator-face nil :inherit 'vhdl-ts-font-lock-punctuation-face :weight 'extra-bold)
  (set-face-attribute 'vhdl-ts-font-lock-brackets-face nil :foreground "goldenrod")
  (set-face-attribute 'vhdl-ts-font-lock-parenthesis-face nil :foreground "dark goldenrod")
  (set-face-attribute 'vhdl-ts-font-lock-curly-braces-face nil :foreground "DarkGoldenrod2")
  (set-face-attribute 'vhdl-ts-font-lock-brackets-content-face nil :foreground "yellow green")
  (set-face-attribute 'vhdl-ts-font-lock-port-connection-face nil :foreground "bisque2")
  (set-face-attribute 'vhdl-ts-font-lock-entity-face nil :foreground "green1")
  (set-face-attribute 'vhdl-ts-font-lock-instance-face nil :foreground "medium spring green")
  (set-face-attribute 'vhdl-ts-font-lock-instance-lib-face nil :foreground "gray70")
  (set-face-attribute 'vhdl-ts-font-lock-translate-off-face nil :background "gray20" :slant 'italic))


;; Gathers symbols according to identifier regexps from all `vhdl-mode' buffers.
;; It's somehow inneficient, slow, and better done with `company-gtags'.
(use-package vhdl-capf
  :straight (:repo "sh-ow/vhdl-capf"
             :fork (:repo "gmlarumbe/vhdl-capf"))
  :after vhdl-mode) ; Enable with `:demand' and `:config' with `vhdl-capf-enable'


;; Provides minor-mode `vhdl-tools-mode', with some wrappers for code navigation using ggtags and improvements to imenu.
;; However, seems old and unmaintained. Just leave it in case it can be used as a reference for some feature.
(use-package vhdl-tools
  :after vhdl-mode)



(provide 'init-vhdl)

;;; init-vhdl.el ends here
