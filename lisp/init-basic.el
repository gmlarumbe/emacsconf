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

;; Save some screen real estate
(menu-bar-mode -1)
(when (featurep 'tool-bar)
  (tool-bar-mode -1))
(when (featurep 'scroll-bar)
  (scroll-bar-mode -1))

;; Conf tweaking variables
(defvar larumbe/gitignore-global-file (concat (getenv "HOME") "/.gitignore_global")) ; Variable used by `helm-rg', `counsel-rg' and `init-projectile'.
(defvar larumbe/completion-framework 'ivy) ; 'ivy or 'helm are allowed values (helm will coexist with `ivy-switch-buffer')


(provide 'init-basic)

;;; init-basic.el ends here
