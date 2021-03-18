;;; tcl-utils.el --- Tcl Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun larumbe/tcl-mode-hook ()
  "Tcl mode hook."
  (modify-syntax-entry ?$ "."))


(defun larumbe/tcl-send-line-or-region-and-step ()
  "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead.
Copied from `sh-send-line-or-regin-and-step' for SH Shell scripting."
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
