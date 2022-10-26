;;; init-vhdl.el --- VHDL  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package vhdl-mode
  :straight (:host github :repo "emacs-mirror/emacs"
             :fork (:repo "gmlarumbe/emacs" :branch "vhdl-projects")
             :files ("lisp/progmodes/vhdl-mode.el"))
  :bind (:map vhdl-mode-map
         ("C-M-a"    . vhdl-beginning-of-defun)
         ("C-M-e"    . vhdl-end-of-defun)
         ("C-M-p"    . vhdl-backward-same-indent)
         ("C-M-n"    . vhdl-forward-same-indent)
         ("<f5>"     . vhdl-compile)
         ("<f8>"     . sr-speedbar-open))
  :hook ((vhdl-mode . larumbe/vhdl-flycheck-ghdl-hook))
  :config
  ;; INFO: Using `bind-chord' instead of use-package :chords as the latter does
  ;; a global mapping (not to `vhdl-mode')
  (bind-chord "\\\\" #'vhdl-ext-jump-to-module-at-point vhdl-mode-map)
  (bind-chord "\|\|" #'vhdl-ext-find-parent-module vhdl-mode-map)
  ;; BUG: When used use-package :bind to `vhdl-speedbar-mode-map' this keybinding applied to non-spacebar modes
  (advice-add 'vhdl-speedbar-initialize :after #'(lambda () (define-key vhdl-speedbar-mode-map [? ] #'speedbar-toggle-line-expansion)))
  ;; Indentation
  (setq vhdl-basic-offset 4)
  (setq tab-width 4)          ; TAB Width for indentation (buffer local)
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
  (key-chord-mode 1)
  ;; GHDL custom linter setup
  (defvar larumbe/vhdl-custom-ghdl-list
        '("GHDL-custom" "ghdl" "-i --ieee=synopsys -fexplicit -fno-color-diagnostics" "make" "-f \\1" nil "mkdir \\1" "./" "work/" "Makefile" "ghdl"
          ("ghdl_p: \\*E,\\w+ (\\([^ \\t\\n]+\\),\\([0-9]+\\)|\\([0-9]+\\)):" 1 2 3)
          ("" 0)
          ("\\1/entity" "\\2/\\1" "\\1/configuration" "\\1/package" "\\1/body" downcase)))
  (add-to-list 'vhdl-compiler-alist larumbe/vhdl-custom-ghdl-list)
  (vhdl-set-compiler "GHDL-custom")
  ;; Projects
  (require vhdl-projects)
  ;; Additional MELPA packages
  ;; INFO: Check how they work, still untested, probably there is some overlap with my functions
  (use-package vhdl-tools)
  (use-package vhdl-capf))


(use-package vhdl-ext
  :straight nil
  :after vhdl-mode
  :demand
  :bind (:map vhdl-mode-map
         ("C-M-d"   . vhdl-ext-find-module-instance-fwd)
         ("C-M-u"   . vhdl-ext-find-module-instance-bwd)
         ("C-c C-t" . vhdl-ext-hydra/body)
         )
  :config
  (message "Initializating vhdl-ext"))



(provide 'init-vhdl)

;;; init-vhdl.el ends here
