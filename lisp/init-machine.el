;;; init-machine.el --- Load Machine specific config  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Machine-specific
;;   - This file will not be present in the repo
;;   - It will have specific machine content (e.g. EXWM enabling)
(when (file-exists-p "~/.elisp_private/")
  (defvar larumbe/load-path-dirs-machine '("~/.elisp_private/lisp")) ; Required to provide `init-private' package
  (larumbe/add-to-load-path larumbe/load-path-dirs-machine t)        ; Add recursively
  (require 'init-private))


(provide 'init-machine)

;;; init-machine.el ends here
