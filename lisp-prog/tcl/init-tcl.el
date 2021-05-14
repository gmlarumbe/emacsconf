;;; init-tcl.el --- Tcl  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package tcl
  :bind (:map tcl-mode-map
              ("C-c C-c" . inferior-tcl)
              ("C-c C-p" . larumbe/tcl-send-line-or-region-and-step)
              ;; INFO: Check `tcl-eval-region', `tcl-eval-defun', `tcl-load-file'
              ("C-c C-k" . larumbe/tcl-send-line-or-region-and-step-vivado-shell))
  :hook ((tcl-mode . larumbe/tcl-mode-hook))
  :init
  (setq tcl-application "tclsh")
  (setq tcl-command-switches nil)
  :config
  (defvar larumbe/tcl-braces-face    'larumbe/tcl-braces-face)
  (defvar larumbe/tcl-brackets-face  'larumbe/tcl-brackets-face)
  (defface larumbe/tcl-braces-face   '((t (:foreground "goldenrod")))      "Face for TCL Braces"   :group 'tcl-custom-faces)
  (defface larumbe/tcl-brackets-face '((t (:foreground "dark goldenrod"))) "Face for TCL Brackets" :group 'tcl-custom-faces)
  (defvar larumbe/tcl-font-lock-additional-keywords ; Initially inspired hdl font lock
    (list
     (list "\\(\\[\\|\\]\\)" 0 'larumbe/tcl-braces-face)
     (list "[()]"            0 'larumbe/tcl-brackets-face)
     ))
  (font-lock-add-keywords 'tcl-mode larumbe/tcl-font-lock-additional-keywords)

  (require 'tcl-utils))


(provide 'init-tcl)

;;; init-tcl.el ends here
