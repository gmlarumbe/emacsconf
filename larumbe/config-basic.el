;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BASIC CONFIGURATION FOR EMACS INIT FILE ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic settings
;;;; Basics
(server-start)                           ; Server start for emacsclient support
(load-theme 'deeper-blue t)              ; Load theme
(desktop-save-mode 1)                    ; Autosave Desktop
(setq confirm-kill-emacs #'y-or-n-p)     ; Avoid closing Emacs unexpectedly (helm prefix C-x c)
(setq inhibit-startup-screen t)          ; Inhibit startup screen
(setq disabled-command-function 'ignore) ; Enable all commands
(defalias 'yes-or-no-p 'y-or-n-p)        ; Globally set y-or-n-p
(setq custom-file "~/.elisp/larumbe/custom-file.el")
(load custom-file)

;;;; Window/Frame Display
(menu-bar-mode -1)   ; Disable Menu bar
(tool-bar-mode -1)   ; Disable Tool bar
(scroll-bar-mode -1) ; Disable Scroll-bar (watch out percentage)

;;;; Load Path
(add-to-list 'load-path (expand-file-name "~/.elisp"))
(add-to-list 'load-path (expand-file-name "~/.elisp/download"))
(add-to-list 'load-path (expand-file-name "~/.elisp/larumbe/own-modes/majors/"))
(add-to-list 'load-path (expand-file-name "~/.elisp/larumbe/own-modes/minors/"))
(add-to-list 'load-path (expand-file-name "~/.elisp/larumbe/own-modes/override/"))

;;; Package management setup for use-package
(require 'package)
(setq package-enable-at-startup nil)
(add-to-list 'package-archives '("melpa"        . "http://melpa.org/packages/"))
(add-to-list 'package-archives '("melpa-stable" . "http://stable.melpa.org/packages/"))
(add-to-list 'package-archives '("gnu"          . "http://elpa.gnu.org/packages/"))
(package-initialize)

(unless (package-installed-p 'use-package)
  (package-refresh-contents)
  (package-install 'use-package))

;; use-package.el is no longer needed at runtime
;; This means you should put the following at the top of your Emacs, to further reduce load time:
(eval-when-compile
  (require 'use-package))
(setq use-package-always-ensure t) ; Force download if not available. INFO: Set to nil for built-in packages.
