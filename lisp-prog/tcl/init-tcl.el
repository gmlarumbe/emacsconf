;;; init-tcl.el --- Tcl  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package tcl
  :bind (:map tcl-mode-map
         ;; INFO: Check `tcl-eval-region', `tcl-eval-defun', `tcl-load-file'
         ("C-c C-c" . inferior-tcl)
         ("C-c C-p" . larumbe/tcl-send-line-or-region-and-step))
  :hook ((tcl-mode . larumbe/tcl-mode-hook))
  :init
  (setq tcl-application "tclsh")
  (setq tcl-command-switches nil)
  :config
  (require 'tcl-utils)
  (larumbe/tcl-font-lock-setup))


(provide 'init-tcl)

;;; init-tcl.el ends here
("C-c C-k" . larumbe/tcl-send-line-or-region-and-step-vivado-shell)
