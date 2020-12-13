;;; basic-functions.el --- Basic Functions  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; This file hosts basic functions that have no dependencies beyond Emacs
;; bundled basic functions and libraries.
;;
;; These are meant to be used everywhere in the configuration file.
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


;;;; Directories
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



(provide 'basic-functions)

;;; basic-functions.el ends here
