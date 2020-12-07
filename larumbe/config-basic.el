;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BASIC CONFIGURATION FOR EMACS INIT FILE ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic settings
;;;; Basics
(if (and (fboundp 'server-running-p)           ; Server start for emacsclient support
         (not (server-running-p)))
    (server-start))
(setq custom-file "~/.emacs.d/custom-file.el") ; Custom file does not need to be in version control.
(unless (file-exists-p custom-file)            ; It will only hold a list with safe variables, `package-selected-packages' for autoremove and custom set variables.
  (write-region "" nil custom-file))           ; All of these are actually local to a machine.
(load custom-file)                             ; Create file if it doesn't exist in emacs directory, and load it
(load-theme 'deeper-blue t)                    ; Load theme
(desktop-save-mode 1)                          ; Autosave Desktop
(setq confirm-kill-emacs #'y-or-n-p)           ; Avoid closing Emacs unexpectedly (helm prefix C-x c)
(setq inhibit-startup-screen t)                ; Inhibit startup screen
(setq disabled-command-function 'ignore)       ; Enable all commands
(defalias 'yes-or-no-p 'y-or-n-p)              ; Globally set y-or-n-p

;;;; Window/Frame Display
(menu-bar-mode -1)
(when (featurep 'tool-bar)
  (tool-bar-mode -1))
(when (featurep 'scroll-bar)
  (scroll-bar-mode -1))


;;; Mode-line
(use-package smart-mode-line
  :config
  (setq sml/theme 'dark) ; Other choices would be 'light or 'respectful. By default, sml will try to figure out the best sml theme to go with your Emacs theme.
  (sml/setup)            ; Enable smart-mode-line
  (which-function-mode)
  (set-face-attribute 'which-func nil :foreground "green")
  (setq line-number-mode nil) ; Hide current line number from mode-line
  (setq display-time-default-load-average nil) ; Display time on the status bar
  (display-time-mode t))
