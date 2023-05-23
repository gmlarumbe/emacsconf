;;; init-vhdl.el --- VHDL  -*- lexical-binding: t -*-
;;
;; INFO: Fetched from `vhdl-mode' docstring:
;;
;; DESIGN HIERARCHY BROWSER:
;;   The speedbar can also be used for browsing the hierarchy of design units
;;   contained in the source files of the current directory or the specified
;;   projects (see option `vhdl-project-alist').
;;
;;     The speedbar can be switched between file, buffer, directory hierarchy and
;;   project hierarchy browsing mode in the speedbar menu or by typing `f', 'b',
;;   `h' or `H' in speedbar.
;;
;;     In speedbar, open design units with `mouse-2' on the name and browse
;;   their hierarchy with `mouse-2' on the `+'.  Ports can directly be copied
;;   from entities and components (in packages).  Individual design units and
;;   complete designs can directly be compiled (\"Make\" menu entry).
;;
;;     The hierarchy is automatically updated upon saving a modified source
;;   file when option `vhdl-speedbar-update-on-saving' is non-nil.  The
;;   hierarchy is only updated for projects that have been opened once in the
;;   speedbar.  The hierarchy is cached between Emacs sessions in a file (see
;;   options in group `vhdl-speedbar').
;;
;;     Simple design consistency checks are done during scanning, such as
;;   multiple declarations of the same unit or missing primary units that are
;;   required by secondary units.
;;
;;
;; More INFO:
;;  Keybindings for vhdl-speedbar Design Hierarchy view:
;;    - f: files
;;    - h: directory hierarchy
;;    - H: project hierarchy
;;    - b: buffers
;;    - SPC: Added additionally @ `init-vhdl' to toggle expand/contract level
;;
;; More INFO: The hierarchy extraction stop working with lexical binding enabling.
;;
;; DANGER: If pressing 'R' while in hierarchy mode to refresh hierarchy, make
;; sure of doing it with cursor on a line with text. Otherwise the error:
;; "speedbar-files-line-directory: Wrong type argument: stringp, nil" will show up.
;;
;; DANGER: From `vhdl-project-alist' docstring:
;; NOTE: Reflect the new setting in the choice list of option `vhdl-project'
;;       by RESTARTING EMACS."
;;
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
  (vhdl-electric-mode -1)
  ;; BUG: With use-package :bind to `vhdl-speedbar-mode-map' this keybinding applied to non-spacebar modes
  (advice-add 'vhdl-speedbar-initialize :after #'(lambda () (define-key vhdl-speedbar-mode-map [? ] #'speedbar-toggle-line-expansion)))
  ;; Newline advice to kill def/refs buffers
  (advice-add 'vhdl-electric-return :before-until #'larumbe/newline-advice)) ; Kill def/refs buffers with C-RET


(use-package vhdl-ext
  :straight (:host github :repo "gmlarumbe/vhdl-ext"
             :files (:defaults "snippets" "ts-mode/*.el")) ; TODO: Don't miss out vhdl-ts-mode
  :after vhdl-mode
  :demand
  :mode (("\\.vhd\\'" . vhdl-ts-mode))
  :hook ((vhdl-mode    . vhdl-ext-mode)
         (vhdl-ts-mode . vhdl-ext-mode))
  :config
  (vhdl-ext-mode-setup)
  (when (executable-find "vhdl_ls")
    (add-hook 'vhdl-mode-hook (lambda () (when (file-exists-p (file-name-concat (vhdl-ext-project-root) "vhdl_ls.toml"))
                                      (lsp))))))


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
