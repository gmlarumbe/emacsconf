;;; init.el --- Larumbe's dotemacs file  -*- lexical-binding: t -*-

;; Copyright (C) 2017-2020 Gonzalo M. Larumbe

;; Author: Gonzalo Martinez Larumbe <gonzalomlarumbe@gmail.com>
;; Homepage: https://github.com/gmlarumbe/emacsconf
;;           https://gmlarumbe.com

;;; Code

;;; Load Path
(add-to-list 'load-path (expand-file-name "~/.elisp"))
(add-to-list 'load-path (expand-file-name "~/.elisp/larumbe"))
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
(use-package gnu-elpa-keyring-update) ; Update elpa keys to avoid signature issues


;;; Requires
;; Config basic
(load "~/.elisp/larumbe/config-basic.el")

;; Custom functions
(require 'custom-functions)

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
