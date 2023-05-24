;;; tcl-utils.el --- Tcl Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'tcl)

(defvar larumbe/tcl-braces-face    'larumbe/tcl-braces-face)
(defvar larumbe/tcl-brackets-face  'larumbe/tcl-brackets-face)
(defface larumbe/tcl-braces-face   '((t (:foreground "goldenrod")))      "Face for TCL Braces"   :group 'tcl-custom-faces)
(defface larumbe/tcl-brackets-face '((t (:foreground "dark goldenrod"))) "Face for TCL Brackets" :group 'tcl-custom-faces)
(defvar larumbe/tcl-font-lock-additional-keywords
  (list
   (list "\\(\\[\\|\\]\\)" 0 'larumbe/tcl-braces-face)
   (list "[()]" 0 'larumbe/tcl-brackets-face)
   ))


(defun larumbe/tcl-font-lock-setup ()
  "Setup font-lock for tcl buffers."
  (font-lock-add-keywords 'tcl-mode larumbe/tcl-font-lock-additional-keywords))


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
