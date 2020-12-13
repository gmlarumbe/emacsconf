;;; vhdl-settings.el --- VHDL  -*- lexical-binding: t -*-
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



;;; Basic settings
(use-package vhdl-mode
  :load-path "~/.elisp/larumbe/own-modes/override"
  :commands (larumbe/vhdl-index-menu-init)
  :hook ((vhdl-mode . my-vhdl-mode-hook))
  :bind (:map vhdl-mode-map
              ("C-M-a"           . vhdl-beginning-of-defun)
              ("C-M-e"           . vhdl-end-of-defun)
              ("C-M-d"           . larumbe/find-vhdl-module-instance-fwd)
              ("C-M-u"           . larumbe/find-vhdl-module-instance-bwd)
              ("C-M-p"           . vhdl-backward-same-indent)
              ("C-M-n"           . vhdl-forward-same-indent)
              ("<f5>"            . vhdl-compile)
              ("<C-iso-lefttab>" . insert-tab-vhdl)
              ("C-M-<tab>"       . remove-tab-vhdl)
              ("C-c C-t"         . hydra-vhdl-template/body)
              ("<f8>"            . sr-speedbar-open))
  :bind (:map vhdl-speedbar-mode-map
              ("SPC" . speedbar-toggle-line-expansion))

  :init   ; INFO: Requires to be set before loading package in order to variables like faces to take effect
  (fset 'insert-tab-vhdl (kbd "C-u 4 SPC")) ; Custom 4 spaces TAB key
  (fset 'remove-tab-vhdl (kbd "C-u 4 DEL")) ; Custom remove 4 spaces TAB key
  :config
  (setq vhdl-clock-edge-condition (quote function))
  (setq vhdl-company-name "")
  (setq vhdl-conditions-in-parenthesis t)
  (setq vhdl-default-library "xil_defaultlib")
  (setq vhdl-end-comment-column 120)
  (setq vhdl-platform-spec "Debian 9.1")
  (setq vhdl-reset-kind (quote sync))
  (setq vhdl-speedbar-auto-open nil)
  (setq vhdl-standard '(08 nil))
  ;; Indentation
  (setq vhdl-basic-offset 4)
  (setq tab-width 4)                    ; TAB Width for indentation
  (setq indent-tabs-mode nil)           ; Replace TAB with Spaces when indenting
  ;; GHDL custom linter setup
  (setq vhdl-custom-ghdl-list
        '("GHDL-custom" "ghdl" "-i --ieee=synopsys -fexplicit -fno-color-diagnostics" "make" "-f \\1" nil "mkdir \\1" "./" "work/" "Makefile" "ghdl"
          ("ghdl_p: \\*E,\\w+ (\\([^ \\t\\n]+\\),\\([0-9]+\\)|\\([0-9]+\\)):" 1 2 3)
          ("" 0)
          ("\\1/entity" "\\2/\\1" "\\1/configuration" "\\1/package" "\\1/body" downcase)
          )
        )
  (add-to-list 'vhdl-compiler-alist vhdl-custom-ghdl-list)
  (vhdl-set-compiler "GHDL-custom")
  (vhdl-electric-mode -1)
  ;; Bind chords
  (bind-chord "\\\\" #'larumbe/vhdl-jump-to-module-at-point vhdl-mode-map)
  (when (executable-find "ag")
    (bind-chord "\|\|" #'larumbe/vhdl-find-parent-module vhdl-mode-map))

  ;; Own settings
  (require 'vhdl-utils)
  (require 'vhdl-projects) ; Speedbar design hierarchy and compilation via makefiles
  (require 'vhdl-templates)
  (require 'vhdl-navigation)
  (require 'vhdl-imenu)
  (require 'vhdl-flycheck)

  ;; Additional MELPA packages
  ;; INFO: Check how they work, still untested, probably there is some overlap
  ;; with my functions
  (use-package vhdl-tools)
  (use-package vhdl-capf))


;; TODO: Merge and switch some day to latest official version
;; (use-package vhdl-mode
;;   :load-path "~/.elisp/modified/")


(provide 'vhdl-settings)

;;; vhdl-settings.el ends here
