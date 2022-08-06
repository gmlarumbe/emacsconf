;;; init-machine.el --- Load Machine specific config  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun larumbe/enable-deferred-packages ()
  "Enable deferred packages downloaded via `use-package'."
  (interactive)
  (which-function-mode)
  (display-time-mode t)
  (larumbe/sml-enable 'dark)
  (winner-mode 1)
  (beacon-mode 1)
  (global-hardcore-mode 1)
  (untabify-trailing-ws-mode 1)
  (electric-pair-mode 1)
  (smart-mark-mode 1) ;; TODO: Verify that it's working properly. Remove otherwise
  (which-key-mode 1))

(larumbe/enable-deferred-packages)


;;;; Machine-specific
;;   - This file will not be present in the repo
;;   - It will have specific machine content (e.g. EXWM enabling)
(when (file-exists-p "~/.elisp_private/")
  (defvar larumbe/load-path-dirs-machine '("~/.elisp_private/lisp")) ; Required to provide `init-private' package
  (larumbe/add-to-load-path larumbe/load-path-dirs-machine t)        ; Add recursively
  (require 'init-private))


(provide 'init-machine)

;;; init-machine.el ends here
