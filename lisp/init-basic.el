;;; init-basic.el --- Basic Config  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;; Server
(require 'server)
(unless (server-running-p)                     ; Server start for emacsclient support
  (server-start))

;; Custom-file
(setq custom-file "~/.emacs.d/custom-file.el") ; Custom file does not need to be in version control.
(unless (file-exists-p custom-file)            ; It will only hold a list with safe variables, `package-selected-packages' for autoremove and custom set variables.
  (write-region "" nil custom-file))           ; All of these are actually local to a machine.
(load custom-file)                             ; Create file if it doesn't exist in emacs directory, and load it

;; Global config
(load-theme 'deeper-blue t)                    ; Load theme
(desktop-save-mode 1)                          ; Autosave Desktop
(defalias 'yes-or-no-p 'y-or-n-p)              ; Globally set y-or-n-p
(setq confirm-kill-emacs #'y-or-n-p)           ; Avoid closing Emacs unexpectedly (helm prefix C-x c)
(setq inhibit-startup-screen t)                ; Inhibit startup screen
(setq disabled-command-function 'ignore)       ; Enable all commands
(setq initial-major-mode 'fundamental-mode)    ; Avoid start *scratch* in `lisp-interaction-mode' and enabling default `prog-mode-hook.

;; Save some screen real estate
(menu-bar-mode -1)
(when (featurep 'tool-bar)
  (tool-bar-mode -1))
(when (featurep 'scroll-bar)
  (scroll-bar-mode -1))

;; Conf tweaking variables
(defvar larumbe/gitignore-global-file (concat (getenv "HOME") "/.gitignore_global")) ; Variable used by `helm-rg', `counsel-rg' and `init-projectile'.
(defvar larumbe/completion-framework 'ivy) ; 'ivy or 'helm are allowed values (helm will coexist with `ivy-switch-buffer')

(defvar larumbe/emacs-conf-repos-all (append '("~/.elisp" "~/.elisp_private") (larumbe/straight-packages)))
(defvar larumbe/emacs-conf-repos-devel '("~/.elisp" "~/.elisp_private" "~/.emacs.d/straight/repos/my-elisp-packages" "~/.emacs.d/straight/repos/my-elisp-packages-priv"))
(defvar larumbe/emacs-conf-straight-forked
  '("~/.emacs.d/straight/repos/yasnippet-snippets"
    "~/.emacs.d/straight/repos/verilog-mode"
    "~/.emacs.d/straight/repos/ssh-tunnels"
    "~/.emacs.d/straight/repos/repo-el"
    "~/.emacs.d/straight/repos/org-jira"
    "~/.emacs.d/straight/repos/kmodi"
    "~/.emacs.d/straight/repos/jenkins.el"
    "~/.emacs.d/straight/repos/ivy-youtube"
    "~/.emacs.d/straight/repos/emacs-btc-ticker"
    "~/.emacs.d/straight/repos/emacs"
    "~/.emacs.d/straight/repos/arch-packer")
  "Obtained through evaluation of: `(larumbe/git-check-forked-repos (larumbe/straight-packages))'")



(provide 'init-basic)

;;; init-basic.el ends here
