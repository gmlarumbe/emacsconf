;;; init-custom-functions.el --- Custom Functions  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; This file hosts some general purpose functions that might have some
;; package dependencies.
;;
;; These are meant to be used all along the configuration file.
;;
;;; Code:

(require 'f)
(require 'with-editor)


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




;;;; More complex/less frequently used
(defun forward-same-indent ()
  "Move forward to next line with same indent (copied from `vhdl-mode').
DANGER: Comment needs to be substituted from '--' to  mode-specific comment."
  (interactive)
  (let ((pos (point))
        (indent (current-indentation)))
    (beginning-of-line 2)
    (while (and (not (eobp))
                (or (looking-at "^\\s-*\\(--.*\\)?$")
                    (> (current-indentation) indent)))
      (beginning-of-line 2))
    (if (= (current-indentation) indent)
        (back-to-indentation)
      (message "No following line with same indent found in this block")
      (goto-char pos)
      nil)))


(defun backward-same-indent ()
  "Move backward to previous line with same indent (copied from `vhdl-mode').
DANGER: Comment needs to be substituted from '--' to  mode-specific comment."
  (interactive)
  (let ((pos (point))
        (indent (current-indentation)))
    (beginning-of-line -0)
    (while (and (not (bobp))
                (or (looking-at "^\\s-*\\(--.*\\)?$")
                    (> (current-indentation) indent)))
      (beginning-of-line -0))
    (if (= (current-indentation) indent)
        (back-to-indentation)
      (message "No preceding line with same indent found in this block")
      (goto-char pos)
      nil)))


;; https://emacs.stackexchange.com/questions/5441/function-to-delete-all-comments-from-a-buffer-without-moving-them-to-kill-ring
(defun larumbe/delete-comments-from-buffer ()
  "Delete comments from buffer without moving them to the kill ring."
  (interactive)
  (goto-char (point-min))
  (let (kill-ring)
    (comment-kill (count-lines (point-min) (point-max)))))


;; https://stackoverflow.com/questions/31767779/is-there-an-apply-command-to-each-line-in-region-in-emacs
;; INFO: Do not use functions that alter the length of the buffer
;; (e.g. #'kill-line) as the start/end parameters will change during execution.
(defun do-lines (fun &optional start end)
  "Invoke function FUN on the text of each line from START to END."
  (interactive
   (let ((fn (intern (completing-read "Function: " obarray 'functionp t))))
     (if (use-region-p)
         (list fn (region-beginning) (region-end))
       (list fn (point-min) (point-max)))))
  (save-excursion
    (goto-char start)
    (while (< (point) end)
      (funcall fun (buffer-substring (line-beginning-position) (line-end-position)))
      (forward-line 1))))


(defun larumbe/buffer-expand-filenames ()
  "Expands filenames paths present in `current-buffer' line by line."
  (interactive)
  (let (cur-line)
    (save-excursion
      (goto-char (point-min))
      (while (< (point) (point-max))
        (delete-horizontal-space)
        (setq cur-line (expand-file-name (thing-at-point 'line) default-directory))
        (kill-line 1)
        (insert cur-line)))))


(defun larumbe/sort-regexp-at-the-beginning-of-file (regexp)
  "Move lines containing REGEXP recursively at the beginning of the file.
Done line by line, this might be useful when managing a list of files,
one file at a line,and there is some need of sorting by regexp.
For example, in SystemVerilog,packages might need to be included before other files."
  (interactive)
  (let ((sorted-files-p nil))
    (goto-char (point-min))
    (unless sorted-files-p
      (save-excursion
        (unless (search-forward-regexp regexp nil 1)
          (setq sorted-files-p t))
        (beginning-of-line)
        (kill-line 1)) ; Kill trailing newline as well
      (yank))))


(defun larumbe/directory-files-recursively-to-file (base-dir file re &optional append exclude-re)
  "Retrieve all files matching regexp RE of a specified BASE-DIR to output FILE.
If optional APPEND is set to non-nil, append result to existing FILE.
Otherwise, overwrite old existing FILE with new results.
If optional EXCLUDE-RE is set, delete paths with that regexp from generated file."
  (let (buf)
    (save-window-excursion
      (with-temp-buffer
        (mapc
         (lambda (dir) (insert (mapconcat #'identity (directory-files-recursively dir re) "\n")))
         (list base-dir))
        ;; Append to existing file
        (when (and (file-exists-p (concat base-dir file))
                   append)
          (setq buf (current-buffer))
          (find-file file)
          (goto-char (point-max))
          (newline)
          (insert-buffer-substring buf))
        ;; Filter according to optional parameter
        (when exclude-re
          (flush-lines exclude-re (point-min) (point-max)))
        (write-file file)))))


;; https://stackoverflow.com/questions/3775377/how-do-you-diff-a-directory-for-only-files-of-a-specific-type
(defun larumbe/directory-diff-recursive (dir1 dir2 out-file)
  "Export diff between DIR1 and DIR2 to OUT-FILE.
It uses an exclude schema that leaves out of the diff
the files/expresions in exclude.list This is because there
is no include option for `diff' utils."
  (interactive "DSelect first directory: \nDSelect second directory: \nFSelect output file:")
  (let ((exclude-file)
        (exclude-patterns '("*.wdf"
                            "*.xml"
                            "*.bxml"
                            "*.wpc"
                            "*.target"
                            "*.rdl.ast"
                            "file_list.py"
                            "source_list.tcl"
                            "run_vivado.tcl")))
    (setq exclude-file (concat (file-name-directory out-file) "exclude.pats"))
    (f-write-text (larumbe/print-elements-of-list-of-strings exclude-patterns) 'utf-8 exclude-file)
    ;; If return value is `1' is because differences were found
    (start-process-shell-command
     "*diff-dirs*" nil
     (concat "diff -X " exclude-file " -r " dir1 " " dir2 " > " out-file))))


;; https://gist.github.com/ffevotte/9345586#file-gistfile1-el
(defun source (filename)
  "Update environment variables from FILENAME source file."
  (interactive "fSource file: ")
  (message "Sourcing environment from `%s'..." filename)
  (with-temp-buffer
    (shell-command (format "diff -u <(true; export) <(source %s; export)" filename) '(4))
    (let ((envvar-re "declare -x \\([^=]+\\)=\\(.*\\)$"))
      ;; Remove environment variables
      (while (search-forward-regexp (concat "^-" envvar-re) nil t)
        (let ((var (match-string 1)))
          (message "%s" (prin1-to-string `(setenv ,var nil)))
          (setenv var nil)))
      ;; Update environment variables
      (goto-char (point-min))
      (while (search-forward-regexp (concat "^+" envvar-re) nil t)
        (let ((var (match-string 1))
              (value (read (match-string 2))))
          (message "%s" (prin1-to-string `(setenv ,var ,value)))
          (setenv var value)))))
  (message "Sourcing environment from `%s'... done." filename))



;; https://emacs.stackexchange.com/questions/10077/how-to-edit-crontab-directly-within-emacs-when-i-already-have-emacs-open
(defun crontab-e ()
  "Run `crontab -e' in an Emacs buffer."
  (interactive)
  (with-editor-async-shell-command "crontab -e"))



;;;; Keybindings
(global-set-key (kbd "C-x d")   #'duplicate-line)                         ; Replaces Dired (C-x C-j works better)
(global-set-key (kbd "M-w")     #'larumbe/copy-region-or-symbol-at-point) ; Overrides `kill-ring-save'
(global-set-key (kbd "C-z")     #'larumbe/pop-to-previous-mark)           ; Unmaps suspending frame
(global-set-key (kbd "C-x C-z") #'larumbe/pop-to-previous-mark)           ; Unmaps suspending frame
(global-set-key (kbd "C-x C-/") #'larumbe/pwd-to-kill-ring)
(global-set-key (kbd "C-x C-,") #'larumbe/revert-buffer-no-confirm)



(provide 'init-custom-functions)

;;; init-custom-functions.el ends here
