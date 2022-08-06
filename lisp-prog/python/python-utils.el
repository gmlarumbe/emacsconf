;;; python-utils.el --- Python Utilities  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Send to console
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


;;;; HideShow
;; TODO: Fork python-mode GitHub repo and try to fix it if it is not already done.
(defun larumbe/python-fix-hs-special-modes-alist ()
  "BUG: Issue with `hs-minor-mode' and MELPA `python-mode' (it didn't apply to bundled Emacs installation python-mode).

It seems there are two ways of using HideShow with python-mode:

1. The generic one that makes use of `hs-special-modes-alist':
This includes setting the `hs-block-start-regexp', comment delimiter and `hs-forward-sexp-func'.
- Done in `python-mode': /home/martigon/.emacs.d/elpa/python-mode-20200417.648/python-mode.el:23524

2. The custom functions used by MELPA python-mode (`py-hide-base' and `py-show-all' based functions).
These ones seem to work well for hiding but not for toggling, as there were some issues with overlay detecting in the buffer.

Since I decided to follow with the first method, there was a bug in line 23524 when adding python hideshow to
`hs-special-modes-alist'. The `hs-forward-sexp-func' was a lambda and took incorrect number of arguments.
Declaring it as a quoted symbol fixed the issue.

Furthermore, this was necessary because setting these variables manually (via use-package config/init or with a hook)
didn't work as expected either (only worked with a hook and not at Emacs startup).
  - /home/martigon/.emacs.d/elpa/python-mode-20200417.648/python-mode.el:22918
  ;; (setq hs-block-start-regexp py-extended-block-or-clause-re)
  ;; (setq hs-forward-sexp-func 'py-forward-block-or-clause)
"
  ;; Pushes list with HideShow config to `hs-special-modes-alist', taking precedence over variables
  (let ((python-entry (assoc 'python-mode hs-special-modes-alist)))
    (when python-entry
      (setq hs-special-modes-alist (remove python-entry hs-special-modes-alist)))
    (push (list
           'python-mode
           ;; start regex
           py-extended-block-or-clause-re
           ;; end regex
           nil
           ;; comment-start regex
           "#"
           ;; forward-sexp function
           'py-forward-block-or-clause
           nil) hs-special-modes-alist)))


(defun larumbe/python-hs-hide-all (&optional hideall)
  "Hide all defs at file (not classes).
If called witih prefix arg HIDEALL, execute `hs-hide-all' (including classes)"
  (interactive "P")
  (if (not hideall)
      (progn
        (save-excursion
          (goto-char (point-min))
          (while (re-search-forward py-def-re nil t)
            (hs-hide-block))))
    (hs-hide-all)))


;;;; Newline workaround for ag/xref/ripgrep buffers
;; INFO: Same as `py-newline-and-indent' but withouth the (interactive "*" form):
;;  - Check comments of `newline' overriden function
(defun py-newline-and-indent ()
  "Add a newline and indent to outmost reasonable indent.
When indent is set back manually, this is honoured in following lines."
  (interactive) ; DANGER: Only change from original
  (let* ((orig (point))
         ;; lp:1280982, deliberatly dedented by user
         (this-dedent
          (when (and (or (eq 10 (char-after))(eobp))(looking-back "^[ \t]*" (line-beginning-position)))
            (current-column)))
         erg)
    (newline 1)
    (py--delete-trailing-whitespace orig)
    (setq erg
          (cond (this-dedent
                 (indent-to-column this-dedent))
                ((and py-empty-line-closes-p (or (eq this-command last-command)(py--after-empty-line)))
                 (indent-to-column (save-excursion (py-backward-statement)(- (current-indentation) py-indent-offset))))
                (t
                 (fixup-whitespace)
                 (indent-to-column (py-compute-indentation)))))
    erg))

(provide 'python-utils)

;;; python-utils.el ends here
