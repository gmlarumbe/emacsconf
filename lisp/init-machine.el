;;; init-machine.el --- Load Machine specific config  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Machine-specific
;;   - This file will not be present in the repo
;;   - It will have specific machine content (e.g. EXWM enabling)
(when (file-exists-p "~/.elisp_private/")
  (defvar larumbe/load-path-dirs-private '("~/.elisp_private/lisp"
                                           "~/.elisp_private/site-lisp"))
  (larumbe/add-to-load-path larumbe/load-path-dirs-private t) ; Add recursively
  (require 'init-private))


(provide 'init-machine)

;;; init-machine.el ends here
