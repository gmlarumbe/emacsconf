;;; init.el --- Larumbe's dotemacs file

;; Copyright (C) 2017-2020 Gonzalo M. Larumbe

;; Author: Gonzalo Martinez Larumbe <gonzalomlarumbe@gmail.com>
;; Homepage: https://github.com/gmlarumbe/emacsconf
;;           https://gmlarumbe.com

;;; Code
;; Emacs Basic config setup
(load "~/.elisp/larumbe/config-basic.el")

;; Custom functions
(load "~/.elisp/larumbe/custom-functions.el")

;; Custom macros as functions
(load "~/.elisp/larumbe/macros.el")

;; Helm/IDO setup
(load "~/.elisp/larumbe/helm-settings.el")

;; Dired setup
(load "~/.elisp/larumbe/dired-settings.el")

;; Org-mode setup
(load "~/.elisp/larumbe/org-settings.el")

;; Global/ggtags setup
(load "~/.elisp/larumbe/ggtags-settings.el")

;; Other packages setup
(load "~/.elisp/larumbe/packages-settings.el")

;; Git/SVN/repo
(load "~/.elisp/larumbe/version-control-settings.el")

;; Process/Compilation buffers config
(load "~/.elisp/larumbe/compilation-settings.el")

;; Programming languages config
(load "~/.elisp/larumbe/programming-settings.el")

;; Emacs X-Window Manager config
(load "~/.elisp/larumbe/exwm-settings.el")

;; Machine specific settings files:
;;   - This file will not be present in the repo
;;   - It will have specific content to the machine (e.g. EXWM enabling)
(if (file-exists-p "~/.elisp_private/machine/machine-config.el")
    (load "~/.elisp_private/machine/machine-config.el" t))
