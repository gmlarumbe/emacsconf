;;; init-tcl.el --- Tcl  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package tcl
  :bind (:map tcl-mode-map
              ("C-c C-p" . larumbe/tcl-send-line-or-region-and-step)
              ("C-c C-k" . larumbe/tcl-send-line-or-region-and-step-vivado-shell))
  :hook ((tcl-mode . my-tcl-hook))
  :config
  ;; Reuse hdl font-lock faces
  ;; TODO: Move them to a more generic font locking scheme for more prog languages
  (require 'init-hdl-font-lock)
  (defvar larumbe/tcl-font-lock-additional-keywords
        (list
         (list larumbe/braces-regex         0 larumbe/font-lock-braces-face)
         (list larumbe/brackets-regex       0 larumbe/font-lock-brackets-face)
         ))
  (font-lock-add-keywords 'tcl-mode larumbe/tcl-font-lock-additional-keywords)

  (require 'tcl-utils))


(provide 'init-tcl)

;;; init-tcl.el ends here
