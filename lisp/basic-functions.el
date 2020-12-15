;;; basic-functions.el --- Basic Functions  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; This file hosts some general purpose functions that have no dependencies
;; beyond those provided by Emacs installation libraries.
;;
;; These are meant to be used all along the configuration file.
;;
;;; Code:

;;;; Restart code
;; https://emacs.stackexchange.com/questions/5428/restart-emacs-from-within-emacs
(defun launch-separate-emacs-in-terminal ()
  (suspend-emacs "fg ; emacs -nw"))


(defun launch-separate-emacs-under-x ()
  (call-process "sh" nil nil nil "-c" "emacs &"))


(defun restart-emacs ()
  (interactive)
  ;; We need the new emacs to be spawned after all kill-emacs-hooks
  ;; have been processed and there is nothing interesting left
  (let ((kill-emacs-hook (append kill-emacs-hook (list (if (display-graphic-p)
                                                           #'launch-separate-emacs-under-x
                                                         #'launch-separate-emacs-in-terminal)))))
    (save-buffers-kill-emacs)))


;;;; Window resizing
(defvar larumbe/shrink-window-horizontally-delta   15)
(defvar larumbe/shrink-window-vertically-delta      5)

(defun larumbe/enlarge-window-horizontally ()
  "Use `shrink-window' as a wrapper."
  (interactive)
  (shrink-window larumbe/shrink-window-horizontally-delta t))


(defun larumbe/shrink-window-horizontally ()
  "Use `shrink-window' as a wrapper."
  (interactive)
  (shrink-window (- larumbe/shrink-window-horizontally-delta) t))


(defun larumbe/enlarge-window-vertically ()
  "Use `shrink-window' as a wrapper."
  (interactive)
  (shrink-window larumbe/shrink-window-vertically-delta))


(defun larumbe/shrink-window-vertically ()
  "Use `shrink-window' as a wrapper."
  (interactive)
  (shrink-window (- larumbe/shrink-window-vertically-delta)))



;;;; Buffer management
(defun close-all-buffers ()
  "Kill all buffers."
  (interactive)
  (mapc #'kill-buffer (buffer-list)))


(defun only-current-buffer ()
  "Kill all buffers except active one."
  (interactive)
  (mapc #'kill-buffer (cdr (buffer-list (current-buffer)))))


(defun buffer-mode (&optional buffer)
  "Return the major mode associated with BUFFER."
  (let (buf)
    (if buffer
        (setq buf buffer)
      (setq buf (current-buffer)))
    (with-current-buffer buf
      major-mode)))


(defun file-title ()
  "Return file title; e.g. for '/opt/asdf.txt' eval 'asdf'."
  (file-name-sans-extension (file-name-nondirectory (buffer-file-name))))


(defun larumbe/kill-current-buffer ()
  "Kill current buffer without confirmation."
  (interactive)
  (kill-buffer (buffer-name)))


(defun larumbe/load-file-current-buffer ()
  "Load current buffer .el file."
  (interactive)
  (if (string-equal "el" (file-name-extension buffer-file-name))
      (load-file buffer-file-name)
    (error "Cannot load non-Elisp files")))


(defun larumbe/revert-buffer-no-confirm ()
  "Revert current buffer without prompting for confirmation."
  (interactive)
  (revert-buffer nil t t))


(defun larumbe/current-buffer-to-file (out-file)
  "Export current buffer to OUT-FILE.
Seems useful to export long compilation logs."
  (interactive "FEnter output path: ")
  (append-to-file (point-min) (point-max) out-file))


(defun larumbe/pwd-to-kill-ring (&optional no-line)
  "Copy current file path to `kill-ring'.
If optional NO-LINE is given, then do not copy line to `kill-ring'"
  (interactive "P")
  (let (file-name)
    (if no-line
        (setq file-name (buffer-file-name))
      (setq file-name (concat (buffer-file-name) ":" (format "%s" (line-number-at-pos)))))
    (kill-new file-name)
    (message (buffer-file-name))))



;;;; Navigation
(defun larumbe/find-file-at-point ()
  "Wrapper for `ffap' without asking for the file."
  (interactive)
  (let ((file (thing-at-point 'filename)))
    (if (file-exists-p file)
        (progn
          (xref-push-marker-stack)
          (ffap file))
      (error "File \"%s\" does not exist (check point or current path)" file))))


(defun larumbe/pop-to-previous-mark ()
  "Pop to previous mark."
  (interactive)
  (set-mark-command 4))


(defun larumbe/xref-find-definitions-at-point-dwim ()
  "Find definition of symbol at point.
If pointing a file, visit that file instead.

INFO: Will use global/ggtags as a backend if configured."
  (interactive)
  (if (file-exists-p (thing-at-point 'filename))
      (larumbe/find-file-at-point)
    (xref-find-definitions (thing-at-point 'symbol))))


(defun larumbe/xref-find-reference-at-point ()
  "Find reference of symbol at point.

INFO: Will use global/ggtags as a backend if configured."
  (interactive)
  (xref-find-references (thing-at-point 'symbol)))



;;;; Editing
;; https://stackoverflow.com/questions/88399/how-do-i-duplicate-a-whole-line-in-emacs
(defun duplicate-line()
  "Duplicate current line."
  (interactive)
  (move-beginning-of-line 1)
  (kill-line)
  (yank)
  (open-line 1)
  (forward-line 1)
  (yank)
  (move-beginning-of-line 1))


(defun larumbe/copy-region-or-symbol-at-point ()
  "Copy symbol under cursor.  If region is active, copy it instead."
  (interactive)
  (let ((symbol (thing-at-point 'symbol t)))
    (if (use-region-p)
        (call-interactively #'kill-ring-save)
      (kill-new symbol)
      (message symbol))))



;;;; Lists/regexp/strings/files/directories
;; http://ergoemacs.org/emacs/elisp_read_file_content.html
(defun read-lines (filePath)
  "Return a list of lines of a file at FILEPATH."
  (with-temp-buffer
    (insert-file-contents filePath)
    (split-string (buffer-string) "\n" t)))


;; https://www.gnu.org/software/emacs/manual/html_node/eintr/print_002delements_002dof_002dlist.html
(defun print-elements-of-list (list)
  "Print each element of LIST on a line of its own."
  (while list
    (print (car list))
    (setq list (cdr list))))


(defun larumbe/print-elements-of-list-of-strings (list-of-strings)
  "Print each element of LIST-OF-STRINGS on a line of its own."
  (let (return-string)
    (while list-of-strings
      (setq return-string (concat return-string (message "%s\n" (car list-of-strings))))
      (setq list-of-strings (cdr list-of-strings)))
    (message "%s" return-string)))


;; http://ergoemacs.org/emacs/elisp_read_file_content.html
(defun get-string-from-file (filePath)
  "Return FILEPATH file content as a string."
  (with-temp-buffer
    (insert-file-contents filePath)
    (buffer-string)))


;; https://stackoverflow.com/questions/17325713/looking-for-a-replace-in-string-function-in-elisp
(defun replace-in-string (what with in)
  "Replace WHAT to WITH in string IN."
  (replace-regexp-in-string (regexp-quote what) with in nil 'literal))


(defun larumbe/replace-regexp (regexp to-string start end)
  "Wrapper function for programatic use of `replace-regexp'.
Replace REGEXP with TO-STRING from START to END."
  (save-excursion
    (goto-char start)
    (while (re-search-forward regexp end t)
      (replace-match to-string))))


(defun larumbe/replace-regexp-whole-buffer (regexp to-string)
  "Replace REGEXP with TO-STRING on whole current-buffer."
  (larumbe/replace-regexp regexp to-string (point-min) nil))


(defun larumbe/replace-string (string to-string start end &optional fixedcase)
  "Wrapper function for programatic use of `replace-string'.
Replace STRING with TO-STRING from START to END.

If optional arg FIXEDCASE is non-nil, do not alter the case of
the replacement text (see `replace-match' for more info)."
  (save-excursion
    (goto-char start)
    (while (search-forward string end t)
      (replace-match to-string fixedcase))))


(defun larumbe/replace-string-whole-buffer (string to-string &optional fixedcase)
  "Replace STRING with TO-STRING on whole current-buffer.

If optional arg FIXEDCASE is non-nil, do not alter the case of
the replacement text (see `replace-match' for more info)."
  (larumbe/replace-string string to-string (point-min) nil fixedcase))



(defun larumbe/path-join (arg1 arg2)
  "Join path of ARG1 and ARG2."
  (if (and arg1 arg2)
      (concat (file-name-as-directory arg1) arg2)
    (message "larumbe/path-join: Cannot join path with nil arguments.")
    nil))


(defun larumbe/directory-find-recursive-dirs (&optional dir)
  "Retrieve list of recursive directories from current directory.
If first argument is provided, find DIR subdirectories.

Elisp closest form was `directory-files-recursively' but extracts files as well.

This is identical to what is done to to handle the `load-path' at startup."
  (let (cwd)
    (if dir
        (setq cwd dir)
      (setq cwd default-directory))
    (split-string (shell-command-to-string (concat "find " dir " -type d")))))



;;;; Misc
(defun larumbe/toggle-keyboard-layout ()
  "Toggle keyboard language between US and ES."
  (interactive)
  (let (cur-layout)
    (setq cur-layout (shell-command-to-string "setxkbmap -query | grep layout | awk '{print $2}'"))
    (setq cur-layout (replace-regexp-in-string "\n$" "" cur-layout))
    (if (string-equal cur-layout "us")
        (progn
          (shell-command "setxkbmap es")
          (message "Switched to ES"))
      (shell-command "setxkbmap us")
      (message "Switched to US"))))



;;;; Keybindings
(global-set-key (kbd "C-x d")   #'duplicate-line)                         ; Replaces Dired (C-x C-j works better)
(global-set-key (kbd "M-w")     #'larumbe/copy-region-or-symbol-at-point) ; Overrides `kill-ring-save'
(global-set-key (kbd "C-z")     #'larumbe/pop-to-previous-mark)           ; Unmaps suspending frame
(global-set-key (kbd "C-x C-z") #'larumbe/pop-to-previous-mark)           ; Unmaps suspending frame
(global-set-key (kbd "C-x C-/") #'larumbe/pwd-to-kill-ring)
(global-set-key (kbd "C-x C-,") #'larumbe/revert-buffer-no-confirm)



(provide 'basic-functions)

;;; basic-functions.el ends here
