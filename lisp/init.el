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

(load "~/.elisp/lisp/init-load-path-header.el")

;;;; Packages
(require 'package-settings)
(require 'config-basic)
(require 'basic-functions)
(require 'melpa-settings)
(require 'custom-functions)
(require 'macros-settings)
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
(require 'init-load-path-footer)


(provide 'init)
;;; init.el ends here
