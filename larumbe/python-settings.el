;;;;;;;;;;;;;;;;;;
;; Python setup ;;
;;;;;;;;;;;;;;;;;;
(use-package python-mode
  :mode (("\\SConstruct\\'"      . python-mode)
         ("\\SConstruct.repo\\'" . python-mode))

  :bind (:map python-mode-map
              ("C-c C-p"     . python-send-line-or-region-and-step) ; Overrides `run-python'
              ("C-c C-c"     . run-python)                          ; Overrides `python-shell-send-buffer'
              ("C-M-n"       . forward-same-indent)
              ("C-M-p"       . backward-same-indent)
              ("C-c RET"     . ac-complete-jedi-direct)
              ;; Send text to an *ansi-term* running a Python interpreter (that may run in a remote machine)
              ("C-c C-k"     . larumbe/python-send-line-or-region-and-step-remote-from-host)
              ;; Ignore indentation and send to an *ansi-term* running a Python interpretera Python term individual statements (that may run in a remote machine).
              ("C-c C-l"     . larumbe/python-send-line-and-step-ansi-no-indent) ; Overrides `python-shell-send-file'
              )
  :bind (:map jedi-mode-map ("<C-tab>" . nil)) ; Let C-tab to HideShow

  :config
  (setq python-check-command "pylint")
  (setq py-number-face           font-lock-doc-face)
  (setq py-object-reference-face larumbe/font-lock-grouping-keywords-face)
  (setq py-pseudo-keyword-face   font-lock-constant-face) ; True/False/None
  (setq py-try-if-face           font-lock-doc-face)
  (setq py-variable-name-face    font-lock-variable-name-face)
  (setq py-use-font-lock-doc-face-p t)
  (define-key python-mode-map "\C-c@\C-\M-h" 'larumbe/python-hs-hide-all) ; Overrides `hs-hide-all' (Error if declaring with use-package :bind - Key sequence C-c @  starts with non-prefix key C-c @
  (larumbe/python-fix-hs-special-modes-alist) ; BUG Fix (check function docstring for more info)

  (use-package jedi-core
    :config
    (add-hook 'python-mode-hook 'jedi:setup))
  )


;; Copied from sh-send-line-or-region-and-step for SH Shell scripting
(defun python-send-line-or-region-and-step ()
  "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead."
  (interactive)
  (let (from to end (proc (python-shell-get-process-or-error)))
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


;; INFO: These two latter functions were created for development in Python setup (for remote targets)
(defun larumbe/python-send-line-or-region-and-step-remote-from-host ()
  "Similar to previous one but sends data to *ansi-term* and when a region needs to be sent, instead of creating
a temp file that is later deleted through Python interpreter, is instead parsed in a temp-buffer
and newlines are erased. That was the main issue when sending text, as a newline is interpreted as Enter "
  (interactive)
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
      (insert-string string)
      (flush-lines "^\\s-*$" (point-min) (point-max)) ; Remove newlines before sending to console
      (delete-trailing-whitespace)
      (setq string (buffer-string)))
    ;; Send to console *ansi-term*
    (comint-send-string "*ansi-term*" (concat string "\n"))
    (goto-char end)))


(defun larumbe/python-send-line-and-step-ansi-no-indent ()
  "Similar to `larumbe/sh-send-line-or-region-and-step-ansi', but useful for python individual
statements to avoid indentation errors when testing"
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
    (message "Bypassing indentation...")))



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
  "If called normally hide only defs at file (not classes)
If called witih prefix argument, execute `hs-hide-all' (including classes)"
  (interactive "P")
  (if (not hideall)
      (progn
        (save-excursion
          (beginning-of-buffer)
          (while (re-search-forward py-def-re nil t)
            (hs-hide-block))))
    (hs-hide-all)))


;; Global Tags functions (copied from the ones of verilog)
(defun larumbe/gtags-python-files-pwd-recursive ()
  "Generate gtags.files for current directory. Purpose is to be used with dired mode for small projects, to save the regexp"
  (interactive)
  (larumbe/directory-files-recursively-to-file default-directory "gtags.files" ".py$"))


(defun larumbe/ggtags-create-python-tags-recursive ()
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-python-files-pwd-recursive)
  (ggtags-create-tags default-directory))

