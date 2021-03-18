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
  (defvar larumbe/tcl-font-lock-additional-keywords ; Initially inspired hdl font lock
    (list
     (list "\\(\\[\\|\\]\\)" 0 '((t (:foreground "goldenrod"))))      ; Braces
     (list "[()]"            0 '((t (:foreground "dark goldenrod")))) ; Brackets
     ))
  (font-lock-add-keywords 'tcl-mode larumbe/tcl-font-lock-additional-keywords)

  (require 'tcl-utils))


(provide 'init-tcl)

;;; init-tcl.el ends here
