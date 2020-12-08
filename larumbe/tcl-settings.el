;;; tcl-settings.el --- Tcl  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package tcl
  :bind (:map tcl-mode-map
              ("C-c C-p" . larumbe/tcl-send-line-or-region-and-step)
              ("C-c C-k" . larumbe/tcl-send-line-or-region-and-step-vivado-shell))
  :hook ((tcl-mode . my-tcl-hook))
  :config
  (defun my-tcl-hook ()
    (modify-syntax-entry ?$ ".")
    ;; Reuse hdl font-lock faces
    (setq larumbe/tcl-font-lock-additional-keywords
          (list
           (list larumbe/braces-regex         0 larumbe/font-lock-braces-face)
           (list larumbe/brackets-regex       0 larumbe/font-lock-brackets-face)
           ))
    (font-lock-add-keywords 'tcl-mode larumbe/tcl-font-lock-additional-keywords))

  (defun larumbe/tcl-send-line-or-region-and-step ()
    "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead.
Copied from `sh-send-line-or-regin-and-step' for SH Shell scripting "
    (interactive)
    (let (from to end (proc (inferior-tcl-proc)))
      (if (use-region-p)
          (setq from (region-beginning)
                to (region-end)
                end to)
        (setq from (line-beginning-position)
              to (line-end-position)
              end (1+ to)))
      (tcl-send-string proc (buffer-substring-no-properties from to))
      (tcl-send-string proc "\n")
      (goto-char end))))


(provide 'tcl-settings)

;;; tcl-settings.el ends here
