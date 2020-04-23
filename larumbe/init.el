;;; init.el --- Larumbe's dotemacs file

;; Copyright (C) 2017-2020 Gonzalo M. Larumbe

;; Author: Gonzalo Martinez Larumbe <gonzalomlarumbe@gmail.com>
;; Homepage: https://github.com/gmlarumbe/emacsconf
;;           https://gmlarumbe.com

;;; Code
;; Emacs Basic config setup
(load "~/.elisp/larumbe/config-basic.el")

;; Emacs Packages setup
(load "~/.elisp/larumbe/packages-settings.el")

;; Emacs Packages setup
(load "~/.elisp/larumbe/ggtags-settings.el")

;; Custom functions
(load "~/.elisp/larumbe/custom-functions.el")

;; Custom Macros as functions
(load "~/.elisp/larumbe/macros.el")

;; Process/Compilation buffers config
(load "~/.elisp/larumbe/compilation-settings.el")

;; Programming languages config
(load "~/.elisp/larumbe/programming-settings.el")

;; Emacs X-Window Manager config
(load "~/.elisp/larumbe/exwm-settings.el")

;; Machine specific settings files:
;;   - This file will not be present in the repo
;;   - It will have specific content to the machine (e.g. EXWM enabling)
(load "~/.emacs.d/.elisp_private/machine/machine-config.el" t)
