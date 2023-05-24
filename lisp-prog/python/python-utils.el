;;; python-utils.el --- Python Utilities  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(require 'python)
(require 'hideshow)

;;;; Legacy: send to shell
(defun larumbe/python-send-line-or-region ()
  "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead.
Adapted from `sh-send-line-or-region-and-step' for SH Shell scripting."
  (interactive)
  (let (from to end)
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    (python-shell-send-string (buffer-substring-no-properties from to))
    (python-shell-send-string "\n")
    (goto-char end)))

(defun larumbe/python-send-line-or-region-vterm ()
  "Send the current line to a *vterm* that runs a Python Interpreter.
Step to next line afterwards and if the region is active, send the region instead.
Adapted from `sh-send-line-or-region-and-step' for SH Shell scripting.

INFO: If indentation of a region needs to be bypassed, use this command
along with `rectangle-mark-mode' with `C-x SPC'.

Differs from `larumbe/python-send-line-or-region' in that the former makes use of
`python-shell-send-string', which creates temps files and sends them to the inferior
process.

Sends data to *vterm* and when a region needs to be sent, instead of creating
a temp file that is later deleted through Python interpreter, is instead parsed in a temp-buffer
and newlines are erased.  That was the main issue when sending text, as a newline is interpreted as Enter."
  (interactive)
  (unless (get-buffer "*vterm*")
    (error "Buffer *vterm* does not exist"))
  (let (from to end string)
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    ;; Prepare output to send to console to avoid errors
    (setq string (buffer-substring-no-properties from to))
    (with-temp-buffer
      (insert string)
      (flush-lines "^\\s-*$" (point-min) (point-max)) ; Remove newlines before sending to console
      (delete-trailing-whitespace)
      (setq string (buffer-string)))
    ;; Send to console *vterm*
    (comint-send-string "*vterm*" (concat string "\n"))
    (goto-char end)
    (message "Sent to *vterm*...")))


(defun larumbe/python-send-line-or-region-ansi-term ()
  "Send the current line to an *ansi-term* that runs a Python Interpreter.
Step to next line afterwards and if the region is active, send the region instead.
Adapted from `sh-send-line-or-region-and-step' for SH Shell scripting.

INFO: If indentation of a region needs to be bypassed, use this command
along with `rectangle-mark-mode' with `C-x SPC'.

Differs from `larumbe/python-send-line-or-region' in that the former makes use of
`python-shell-send-string', which creates temps files and sends them to the inferior
process.

Sends data to *ansi-term* and when a region needs to be sent, instead of creating
a temp file that is later deleted through Python interpreter, is instead parsed in a temp-buffer
and newlines are erased.  That was the main issue when sending text, as a newline is interpreted as Enter."
  (interactive)
  (unless (get-buffer "*ansi-term*")
    (error "Buffer *ansi-term* does not exist"))
  (let (from to end string)
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    ;; Prepare output to send to console to avoid errors
    (setq string (buffer-substring-no-properties from to))
    (with-temp-buffer
      (insert string)
      (flush-lines "^\\s-*$" (point-min) (point-max)) ; Remove newlines before sending to console
      (delete-trailing-whitespace)
      (setq string (buffer-string)))
    ;; Send to console *ansi-term*
    (comint-send-string "*ansi-term*" (concat string "\n"))
    (goto-char end)
    (message "Sent to *ansi-term*...")))


(defun larumbe/python-send-line-ansi-term-no-indent-ignore-comment ()
  "Send the current line to an *ansi-term* that runs a Python Interpreter.
Step to next line afterwards and bypass indentation and comments."
  (interactive)
  (let (from to end string)
    (if (use-region-p)
        (error "Region not supported while bypassing indentation!")
      (setq from (progn (beginning-of-line-text) ; DANGER: Does not take comments into account!
                        (point))
            to (line-end-position)
            end (1+ to)))
    (setq string (buffer-substring-no-properties from to))
    (comint-send-string "*ansi-term*" string)
    (comint-send-string "*ansi-term*" "\n")
    (goto-char end)
    (message "Bypassing indentation and ignoring comments...")))


;;;; Hideshow
(defun larumbe/python-hs-hide-all (&optional hideall)
  "Hide all defs at file (not classes).
If called with prefix arg HIDEALL, execute `hs-hide-all' (including classes)"
  (interactive "P")
  (if hideall
      (hs-hide-all) ; TODO: Seems broken with my config and bundled Python in Emacs 30
    ;; Else
    (save-excursion
      (goto-char (point-min))
      (while (python-nav-forward-defun)
        (when (string= "def" (car (split-string (string-trim-left (match-string-no-properties 0)) " ")))
          (hs-hide-block))))))


(provide 'python-utils)

;;; python-utils.el ends here
