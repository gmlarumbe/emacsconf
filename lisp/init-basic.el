;;; init-basic.el --- Basic Config  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;; Custom-file
(setq custom-file "~/.emacs.d/custom-file.el") ; Custom file does not need to be in version control.
(unless (file-exists-p custom-file)            ; It will only hold a list with safe variables, `package-selected-packages' for autoremove and custom set variables.
  (write-region "" nil custom-file))           ; All of these are actually local to a machine.
(load custom-file)

;; Startup
(setq inhibit-startup-screen t)
(setq initial-scratch-message nil)
(setq initial-major-mode 'fundamental-mode)

;; Global config
(desktop-save-mode 1)
(load-theme 'deeper-blue t)
(defalias 'yes-or-no-p 'y-or-n-p)
(setq confirm-kill-emacs #'y-or-n-p) ; Avoid closing Emacs unexpectedly (helm prefix C-x c)
(setq disabled-command-function nil)

;; Save screen real estate
(menu-bar-mode -1)
(when (featurep 'tool-bar)
  (tool-bar-mode -1))
(when (featurep 'scroll-bar)
  (scroll-bar-mode -1))

;; Conf tweaking variables
(defconst larumbe/gitignore-global-file (expand-file-name "~/.dotfiles/gitconfig/.gitignore_global")) ; Used by `helm-rg', `counsel-rg' and `init-projectile'.
(defconst larumbe/completion-framework 'ivy) ; 'ivy or 'helm are allowed values (helm will coexist with `ivy-switch-buffer')

(defconst larumbe/emacs-conf-repos-core '("~/.elisp" "~/.elisp_private"))
(defconst larumbe/emacs-conf-repos-packages '("~/.emacs.d/straight/repos/my-elisp-packages"
                                              "~/.emacs.d/straight/repos/my-elisp-packages-priv"
                                              "~/.emacs.d/straight/repos/verilog-ext"
                                              "~/.emacs.d/straight/repos/vhdl-ext"))
(defconst larumbe/emacs-conf-repos-devel (append larumbe/emacs-conf-repos-core
                                                 larumbe/emacs-conf-repos-packages
                                                 (when (file-exists-p "~/.dotfiles")
                                                   '("~/.dotfiles"))))
(defconst larumbe/emacs-conf-straight-forked
  '("~/.emacs.d/straight/repos/org-jira"           ; Keep forked: changes for non-Atlassian accounts
    "~/.emacs.d/straight/repos/yasnippet-snippets" ; Keep forked: get updates with --rebase
    "~/.emacs.d/straight/repos/jenkins.el"         ; Keep forked: deferred additions with some larumbe/
    "~/.emacs.d/straight/repos/magit-gerrit"       ; Keep forked: still untested
    "~/.emacs.d/straight/repos/wide-column"        ; Keep forked: too old, very unused
    "~/.emacs.d/straight/repos/arch-packer"        ; Maybe with some refactoring, updates after 5 years, no PR in this project. Wait until I get arch in new computer
    "~/.emacs.d/straight/repos/verilog-mode"       ; Development as a maintainer
    )
  "Evaluation of: `(larumbe/git-check-forked-repos-straight)'.")

;; Elpy PR pending: add support for python-ts-mode
;; Ggtags PR pending: sync ggtags xref function

;; TODO: Open PR for arch-packer, just in case? There is some people complaining that it doesn't work

;; TODO: Add PR to apheleia? verilog-ext formatter
;; TODO: Add PR to eglot? verilog-ext/vhdl LSPs
;; TODO: Add PR to lsp? verilog-ext/vhdl LSPs
;; TODO: Add PR to flycheck? verilog-ext/vhdl linters


(provide 'init-basic)

;;; init-basic.el ends here
