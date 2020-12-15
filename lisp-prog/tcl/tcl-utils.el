;;; tcl-utils.el --- Tcl Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun my-tcl-hook ()
  (modify-syntax-entry ?$ ".")
  ;; Reuse hdl font-lock faces
  ;; TODO: Defer until autoloading issues are fixed with verilog/hdl-font-lock
  ;; (setq larumbe/tcl-font-lock-additional-keywords
  ;;       (list
  ;;        (list larumbe/braces-regex         0 larumbe/font-lock-braces-face)
  ;;        (list larumbe/brackets-regex       0 larumbe/font-lock-brackets-face)
  ;;        ))
  ;; (font-lock-add-keywords 'tcl-mode larumbe/tcl-font-lock-additional-keywords)
  )


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
    (goto-char end)))


(provide 'tcl-utils)

;;; tcl-utils.el ends here
