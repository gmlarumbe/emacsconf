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
(require 'init-package)
(require 'init-basic)
(require 'init-custom-functions)
(require 'init-macros)
(require 'init-helm)
(require 'init-projectile)
(require 'init-ggtags)
(require 'init-completion)
(require 'init-ag)
(require 'init-dired)
(require 'init-org)
(require 'init-version-control)
(require 'init-compilation)
(require 'init-fpga-projects)
(require 'init-term)
(require 'init-prog)
(require 'init-exwm)
(require 'init-load-path-footer)


(provide 'init)
;;; init.el ends here
