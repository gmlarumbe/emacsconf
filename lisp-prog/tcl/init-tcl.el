;;; init-tcl.el --- Tcl  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package tcl
  :bind (:map tcl-mode-map
              ("C-c C-p" . larumbe/tcl-send-line-or-region-and-step)
              ("C-c C-k" . larumbe/tcl-send-line-or-region-and-step-vivado-shell))
  :hook ((tcl-mode . my-tcl-hook))
  :config
  (require 'tcl-utils))


(provide 'init-tcl)

;;; init-tcl.el ends here
