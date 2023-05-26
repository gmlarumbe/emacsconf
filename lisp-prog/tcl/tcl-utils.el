;;; tcl-utils.el --- Tcl Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'tcl)

(defvar larumbe/tcl-parenthesis-face 'larumbe/tcl-parenthesis-face)
(defface larumbe/tcl-parenthesis-face '((t (:foreground "goldenrod")))
  "Face for parenthesis ()."
  :group 'tcl-custom-faces)

(defvar larumbe/tcl-brackets-face 'larumbe/tcl-brackets-face)
(defface larumbe/tcl-brackets-face '((t (:foreground "dark goldenrod")))
  "Face for brackets []."
  :group 'tcl-custom-faces)

(defvar larumbe/tcl-curly-braces-face 'larumbe/tcl-curly-braces-face)
(defface larumbe/tcl-curly-braces-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly braces {}."
  :group 'tcl-custom-faces)

(defvar larumbe/tcl-punctuation-face 'larumbe/tcl-punctuation-face)
(defface larumbe/tcl-punctuation-face '((t (:foreground "burlywood")))
  "Face for punctuation symbols, e.g:
!,;:?'=<>*"
  :group 'tcl-custom-faces)

(defconst larumbe/tcl-font-lock-additional-keywords
  '(("\\(\\[\\|\\]\\)" 0 larumbe/tcl-brackets-face)
    ("[()]" 0 larumbe/tcl-parenthesis-face)
    ("[{}]" 0 larumbe/tcl-curly-braces-face)
    ("[$\\.><=\\*!;]" 0 larumbe/tcl-punctuation-face)
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
