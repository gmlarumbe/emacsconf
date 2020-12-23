;;; init-vhdl.el --- VHDL  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defvar larumbe/vhdl-use-own-custom-fontify t)  ; To refresh font-lock call `larumbe/vhdl-font-lock-init'

;; INFO: Moved out of `vhdl-navigation' because it is loaded in vhdl-mode in
;; `larumbe/vhdl-font-lock-init' function.
(defvar larumbe/vhdl-entity-re "^\\s-*\\(entity\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)")
(defvar larumbe/vhdl-blank-opt-re "[[:blank:]\n]*")
(defvar larumbe/vhdl-blank-mand-re "[[:blank:]\n]+")
(defvar larumbe/vhdl-identifier-re "[a-zA-Z_][a-zA-Z0-9_-]*")
(defvar larumbe/vhdl-instance-re
  (concat "^\\s-*\\(?1:" larumbe/vhdl-identifier-re "\\)\\s-*:" larumbe/vhdl-blank-opt-re ; Instance TAG
          "\\(?2:\\(?3:component\\s-+\\|configuration\\s-+\\|\\(?4:entity\\s-+\\(?5:" larumbe/vhdl-identifier-re "\\)\.\\)\\)\\)?"
          "\\(?6:" larumbe/vhdl-identifier-re "\\)" larumbe/vhdl-blank-opt-re ; Module name
          "\\(--[^\n]*" larumbe/vhdl-blank-mand-re "\\)*\\(generic\\|port\\)\\s-+map\\>"))



(use-package vhdl-mode
  :commands (larumbe/vhdl-index-menu-init
             larumbe/vhdl-jump-to-module-at-point
             larumbe/vhdl-find-parent-module)
  :hook ((vhdl-mode . larumbe/vhdl-mode-hook)
         (vhdl-mode . larumbe/vhdl-flycheck-ghdl-hook))
  :bind (:map vhdl-mode-map
              ("C-M-a"           . vhdl-beginning-of-defun)
              ("C-M-e"           . vhdl-end-of-defun)
              ("C-M-d"           . larumbe/find-vhdl-module-instance-fwd)
              ("C-M-u"           . larumbe/find-vhdl-module-instance-bwd)
              ("C-M-p"           . vhdl-backward-same-indent)
              ("C-M-n"           . vhdl-forward-same-indent)
              ("<f5>"            . vhdl-compile)
              ("C-c C-t"         . hydra-vhdl-template/body)
              ("<f8>"            . sr-speedbar-open))
  :bind (:map vhdl-speedbar-mode-map
              ("SPC" . speedbar-toggle-line-expansion)) ; BUG: There was a bug that made this keybinding apply to non-spacebar modes
  :config
  ;; Bind chords
  (bind-chord "\\\\" #'larumbe/vhdl-jump-to-module-at-point vhdl-mode-map)
  (bind-chord "\|\|" #'larumbe/vhdl-find-parent-module vhdl-mode-map)
  ;; Mode config
  (setq vhdl-clock-edge-condition 'function)
  (setq vhdl-company-name "HP Inc")
  (setq vhdl-conditions-in-parenthesis t)
  (setq vhdl-default-library "xil_defaultlib")
  (setq vhdl-end-comment-column 120)
  (setq vhdl-platform-spec (capitalize (system-name)))
  (setq vhdl-reset-kind 'sync)
  (setq vhdl-speedbar-auto-open nil)
  (setq vhdl-standard '(08 nil))
  (vhdl-electric-mode -1)
  ;; Indentation
  (setq vhdl-basic-offset 4)
  (setq tab-width 4)          ; TAB Width for indentation (buffer local)
  (setq indent-tabs-mode nil) ; Replace TAB with Spaces when indenting
  ;; GHDL custom linter setup
  (setq vhdl-custom-ghdl-list
        '("GHDL-custom" "ghdl" "-i --ieee=synopsys -fexplicit -fno-color-diagnostics" "make" "-f \\1" nil "mkdir \\1" "./" "work/" "Makefile" "ghdl"
          ("ghdl_p: \\*E,\\w+ (\\([^ \\t\\n]+\\),\\([0-9]+\\)|\\([0-9]+\\)):" 1 2 3)
          ("" 0)
          ("\\1/entity" "\\2/\\1" "\\1/configuration" "\\1/package" "\\1/body" downcase)))
  (add-to-list 'vhdl-compiler-alist vhdl-custom-ghdl-list)
  (vhdl-set-compiler "GHDL-custom")

  ;; Own settings
  (require 'vhdl-utils)
  (require 'vhdl-projects) ; Speedbar design hierarchy and compilation via makefiles
  (require 'vhdl-templates)
  (require 'vhdl-navigation)
  (require 'vhdl-imenu)
  (require 'vhdl-flycheck)
  (require 'vhdl-font-lock)

  ;; Additional MELPA packages
  ;; INFO: Check how they work, still untested, probably there is some overlap with my functions
  (use-package vhdl-tools)
  (use-package vhdl-capf))




(provide 'init-vhdl)

;;; init-vhdl.el ends here
