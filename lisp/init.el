;;; init.el --- Larumbe's dotemacs file  -*- lexical-binding: t -*-
;;
;;; Commentary:
;;
;; Copyright (C) 2017-2020 Gonzalo M. Larumbe
;;
;; Author: Gonzalo Martinez Larumbe <gonzalomlarumbe@gmail.com>
;; Homepage: https://github.com/gmlarumbe/emacsconf
;;           https://gmlarumbe.com
;;
;;; Code:


;;;; Load path
;; Order of packages within `load-path' actually matters.
;; If there is one package present in more than one directory of `load-path',
;; only the first in the list will be used to load the package.

;; Since `normal-top-level-add-subdirs-to-load-path' will add subdirectories at
;; the end of `load-path', MELPA packages loaded with `use-package' will take
;; precedence. As I would like to have many MELPA packages coexisting with my
;; own overriden packages, I prefer to use a custom approach using shell commands.


(defvar larumbe/load-path-dirs-recursive '("~/.elisp/lisp"
                                           "~/.elisp/lisp-prog"
                                           "~/.elisp/download"
                                           "~/.elisp/own-modes"))
(dolist (dir larumbe/load-path-dirs-recursive)
  (dolist (subdir (split-string (shell-command-to-string (concat "find " dir " -type d"))))
    (add-to-list 'load-path (expand-file-name subdir))))


;;;; Packages
(require 'package-settings)
(require 'config-basic)
(require 'basic-functions)
(require 'melpa-settings)
(require 'custom-functions)
(require 'macros)
(require 'helm-settings)
(require 'projectile-settings)
(require 'ggtags-settings)
(require 'completion-settings)
(require 'ag-settings)
(require 'dired-settings)
(require 'org-settings)
(require 'version-control-settings)
(require 'compilation-settings)
(require 'fpga-projects-settings)
(require 'term-settings)
(require 'programming-settings)
(require 'exwm-settings)



;;;; Load path overriding
;; If a MELPA package has to be overriden, copy the new version (or symlink) to
;; the 'modified' directory.
;; When loading with `use-package', some mechanism is needed to defer it and
;; load it after `load-path' has been updated (such as :bind, :defer, :hook...)
(defvar larumbe/load-path-dirs-non-recursive '("~/.elisp/modified"))
(dolist (dir larumbe/load-path-dirs-non-recursive)
  (add-to-list 'load-path (expand-file-name dir)))



;;;; Machine-specific
;;   - This file will not be present in the repo
;;   - It will have specific machine content (e.g. EXWM enabling)
(when (file-exists-p "~/.elisp_private/")
  (defvar larumbe/load-path-dirs-private '("~/.elisp_private"))
  (dolist (dir larumbe/load-path-dirs-private)
    (add-to-list 'load-path (expand-file-name dir)))
  (require 'private-settings))



(provide 'init)
;;; init.el ends here

