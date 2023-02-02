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
  (setq vhdl-company-name "Ericsson")
  (setq vhdl-conditions-in-parenthesis t)
  (setq vhdl-default-library "xil_defaultlib")
  (setq vhdl-end-comment-column 120)
  (setq vhdl-platform-spec (capitalize (system-name)))
  (setq vhdl-reset-kind 'sync)
  (setq vhdl-speedbar-auto-open nil)
  (setq vhdl-standard '(08 nil))
  (vhdl-electric-mode -1)
  ;; GHDL custom linter setup
  (defvar larumbe/vhdl-custom-ghdl-list
    '("GHDL-custom" "ghdl" "-i --ieee=synopsys -fexplicit -fno-color-diagnostics" "make" "-f \\1"
      nil "mkdir \\1" "./" "work/" "Makefile" "ghdl"
      ("ghdl_p: \\*E,\\w+ (\\([^ \\t\\n]+\\),\\([0-9]+\\)|\\([0-9]+\\)):" 1 2 3) ("" 0)
      ("\\1/entity" "\\2/\\1" "\\1/configuration"
       "\\1/package" "\\1/body" downcase)))
  (add-to-list 'vhdl-compiler-alist larumbe/vhdl-custom-ghdl-list)
  (vhdl-set-compiler "GHDL-custom")
  ;; BUG: When used use-package :bind to `vhdl-speedbar-mode-map' this keybinding applied to non-spacebar modes
  (advice-add 'vhdl-speedbar-initialize :after #'(lambda () (define-key vhdl-speedbar-mode-map [? ] #'speedbar-toggle-line-expansion)))
  ;; Projects
  (require 'vhdl-projects)
  ;; Additional MELPA packages
  ;; Adds implementation to `completion-at-point-functions'
  (use-package vhdl-capf)
  ;; Provides minor-mode `vhdl-tools-mode', with some wrappers for code navigation using ggtags,  improvements to imenu,
  ;; However, seems old and unmaintained and relies on `helm-rg'
  (use-package vhdl-tools))


(use-package vhdl-ext
  :straight (:host github :repo "gmlarumbe/vhdl-ext")
  :after vhdl-mode
  :demand
  :mode (("\\.vhd\\'" . vhdl-ts-mode))
  :bind (:map vhdl-mode-map
         ("C-M-d"   . vhdl-ext-find-entity-instance-fwd)
         ("C-M-u"   . vhdl-ext-find-entity-instance-bwd)
         ("C-M-."   . vhdl-ext-jump-to-parent-entity)
         ("C-c C-t" . vhdl-ext-hydra/body))
  :bind (:map vhdl-ts-mode-map
         ("TAB"     . nil)
         ("C-M-d"   . vhdl-ext-find-entity-instance-fwd)
         ("C-M-u"   . vhdl-ext-find-entity-instance-bwd)
         ("C-M-."   . vhdl-ext-jump-to-parent-entity)
         ("C-c C-t" . vhdl-ext-hydra/body))
  :config
  (message "Initializating vhdl-ext")
  ;; Flycheck
  (setq flycheck-ghdl-ieee-library "synopsys") ; Xilinx primitives
  (setq flycheck-ghdl-workdir (concat (projectile-project-root) "library/" vhdl-default-library)))


(provide 'init-vhdl)

;;; init-vhdl.el ends here
