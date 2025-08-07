;;; init-machine.el --- Load Machine specific config  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun larumbe/enable-deferred-global-modes ()
  "Enable deferred packages downloaded via `use-package'.
All these packages have to be global modes."
  (interactive)
  (projectile-mode 1)
  (show-paren-mode 1)
  (which-function-mode)
  (display-time-mode t)
  (larumbe/sml-enable 'dark)
  (winner-mode 1)
  (beacon-mode 1)
  (global-hardcore-mode 1)
  (untabify-trailing-ws-mode 1)
  (electric-pair-mode 1)
  (which-key-mode 1)
  (global-prettify-symbols-mode 1))

(larumbe/enable-deferred-global-modes)


;;;; Machine-specific
;;   - This file will not be present in the repo
;;   - It will have specific machine content (e.g. EXWM enabling)
(when (file-exists-p "~/.elisp_private/")
  (defvar larumbe/load-path-dirs-machine '("~/.elisp_private/lisp")) ; Required to provide `init-private' package
  (larumbe/add-to-load-path larumbe/load-path-dirs-machine t)        ; Add recursively
  (require 'init-private))


(provide 'init-machine)

;;; init-machine.el ends here
