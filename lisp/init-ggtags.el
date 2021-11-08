;;; init-ggtags.el --- Ggtags/Global  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package ggtags
  :diminish
  :commands (ggtags-create-tags
             ggtags-current-project-root
             ggtags-find-reference
             modi/ggtags-tag-at-point
             larumbe/gtags-create-tags-async
             larumbe/ggtags-backend-switch)
  :bind (:map ggtags-navigation-map
         ("M-o"     . nil)
         ("C-c C-k" . nil) ; EXWM character mode
         ("M->"     . nil)
         ("M-<"     . nil))
  :bind (:map ggtags-mode-map
         ("M-."     . nil)
         ("M-?"     . nil))
  :bind (:map ggtags-global-mode-map
         ("r"       . ggtags-query-replace))
  :config
  (setq ggtags-sort-by-nearness t) ; Enabling nearness requires global 6.5+
  (setq ggtags-navigation-mode-lighter nil)
  (setq ggtags-mode-line-project-name nil)
  ;; INFO: Set to 1 to avoid the `global -u' automatic GTAGS update if tags file is smaller than the variable.
  (setq ggtags-oversize-limit 1)   ; If set to nil it seems that there is no limit...
  (setq ggtags-update-on-save nil) ; Try to avoid the `global -u in progress...'


;;;; Function overriding/wrapping
  ;; Don't consider ` (back quote) as part of `tag' when looking for a Verilog macro definition
  (defun modi/ggtags-tag-at-point ()
    (pcase (funcall ggtags-bounds-of-tag-function)
      (`(,beg . ,end)
       (if (eq ?` (string-to-char (buffer-substring beg end)))
           ;; If `(buffer-substring beg end)' returns "`uvm_info" (for example),
           ;; discard the ` and return just "uvm_info"
           (buffer-substring (1+ beg) end)
         ;; else return the whole `(buffer-substring beg end)'
         (buffer-substring beg end)))))

  ;; Advising
  ;; INFO: It is not a good idea to advice ggtags-mode as it also advices the
  ;; buffer-local variable `ggtags-mode', with some side-effects such as
  ;; recursive function calling when testing `ggtags-mode' variable...
  (advice-add 'ggtags-tag-at-point :override #'modi/ggtags-tag-at-point)


  ;; Similar to `ggtags-navigation-mode-done' but killing gtags buffer to avoid conflicts with
  ;; flycheck/compilation when moving to previous/next error.
  ;; Change at last call (ggtags-navigation-mode-cleanup nil t) setting 2nd argument to t to kill buffer
  (defun larumbe/ggtags-navigation-mode-done ()
    (interactive)
    (ggtags-navigation-mode -1)
    (setq tags-loop-scan t
          tags-loop-operate '(ggtags-find-tag-continue))
    (ggtags-navigation-mode-cleanup nil t))

  (advice-add 'ggtags-navigation-mode-done :override #'larumbe/ggtags-navigation-mode-done)


;;;; Global/ctags
  ;; INFO: Global does not allow to find external definitions outside project root directory (probably due to security reasons).
  ;; In order to do so, there are 2 methods:
  ;;   - Use symbolic links to external directories.
  ;;   - Make use of GTAGSLIBPATH environment variable.
  ;; Associated thread: https://emacs.stackexchange.com/questions/13254/find-external-definition-with-gtags-or-ggtags
  (defun larumbe/gtags-filelist-create (regex &optional exclude-re dir append)
    "Generate gtags.files for current directory, unless optional DIR is set.
Include files that match REGEX.
If EXCLUDE-RE is set, delete paths with that regexp from generated file.
If DIR is not specified, use current-directory.
If APPEND is set, append directory files to already existing tags file."
    (let (tags-dir)
      (if dir
          (setq tags-dir dir)
        (setq tags-dir default-directory))
      (message "Creating gtags.files ...")
      (larumbe/directory-files-recursively-to-file tags-dir "gtags.files" regex append exclude-re)))


  (defun larumbe/gtags-create-tags-async-sentinel (process signal)
    "Sentinel for asynchronous gtags creation."
    (let ((buf (process-buffer process)))
      (cond
       ((equal signal "finished\n")
        (pop-to-buffer buf)
        (message "GTAGS generated in %s" buf))
       ;; Error handling
       ('t
        (message "Unison process open message got signal %s" signal)
        (display-buffer (process-buffer process))))))


  (defun larumbe/gtags-create-tags-async-process (dir)
    "Spawn shell and execute gtags asynchronously at directory DIR."
    (let ((gtags-cmd "gtags -v")
          (output-buffer (concat "*gtags-" (file-name-nondirectory (directory-file-name dir)) "*")))
      (save-window-excursion
        (async-shell-command (concat "cd " dir " && " gtags-cmd) output-buffer))
      (message "Started gtags at buffer %s" output-buffer)
      (set-process-sentinel (get-buffer-process output-buffer) #'larumbe/gtags-create-tags-async-sentinel)))



  ;; List of available regexps for different languages gtags extraction
  ;; If cdr of an element is a string use it as the regexp of the file extension
  ;; If cdr of an element is a cons cell, use first element as the regexp and second as the exclude-re
  (defvar larumbe/gtags-create-tags-lang-regexps
    '(("(System)Verilog" . ("\\.[s]?v[h]?$" . "[^/]+_targets")) ; Exclude re
      ("Python"          . "\\.py$")
      ("Elisp"           . "\\.el$")
      ("c"               . "\\.[ch]\\\(pp\\)?$")
      ("VHDL"            . "\\.vhd[l]?$")
      ("other"           . nil)))

  (defun larumbe/gtags-create-tags-async (&optional dir lang)
    "Similar to `ggtags-create-tags' but asynchronously and adapted to Global+Ctags+Pygments workflow.

Create tags at DIR for language LANG.
If DIR is nil create tags at `default-directory'.
If LANG is nil default to first language in `larumbe/gtags-create-tags-lang-regexps'.

If called interactively, default to create tags for first language in `larumbe/gtags-create-tags-lang-regexps'
at `default-directory'. If called interactively with prefix, prompt for DIR and LANG."
    (interactive "P")
    (let ((lang-regexps larumbe/gtags-create-tags-lang-regexps)
          (regex)
          (regex-lang-cdr) ; cdr of element of `larumbe/gtags-create-tags-lang-regexps' (listp or stringp)
          (exclude-re))
      ;; Default dir and lang
      (unless dir
        (setq dir default-directory))
      (unless lang
        (setq lang (car (car lang-regexps))))
      ;; Prompt for dir and lang if called interactively with prefix
      (when (and current-prefix-arg
                 (called-interactively-p))
        (setq dir (read-directory-name "Directory: "))
        (setq lang (completing-read "Lang: " (mapcar #'car lang-regexps))))
      ;; Set variable values
      (setq dir (expand-file-name dir)) ; Expand in case tags are created at ~ or something similar
      (setq regex-lang-cdr (cdr (assoc lang lang-regexps)))
      ;; Set proper regexp
      (cond
       ;; If cdr is a string, use it as the regex for file creation
       ((stringp regex-lang-cdr)
        (setq regex regex-lang-cdr))
       ;; If cdr is a list (non-nil, e.g. "other"), use first elm as the regex and second as the exclude-re
       ((and (listp regex-lang-cdr)
             regex-lang-cdr)
        (setq regex      (car regex-lang-cdr))
        (setq exclude-re (cdr regex-lang-cdr)))
       ;; Other language: cdr should be nil, prompt for regex for file creation
       ((string= lang "other")
        (when regex-lang-cdr
          (error "If selecting other languaage, regexp must be nil!"))
        (setq regex (read-string "Lang file extension regexp: " "\\.{ext}$")))
       ;; Default (throw error)
       (t (error "Should have not arrived here!")))
      ;; Create filelist
      (larumbe/gtags-filelist-create regex exclude-re dir) ; Do not append created tags to existing file
      ;; Execute gtags
      (larumbe/gtags-create-tags-async-process dir)))


;;;; Auxiliar functions
  (defun larumbe/ggtags-backend-switch ()
    "Switch between diferent backends for Global and ggtags.
The function `ggtags-create-tags' used by all the wrappers relies on the
environment variable GTAGSLABEL, which will select between backends
available at GTAGSCONF globalrc file."
    (interactive)
    (let ((active-backend)
          (backends '("pygments" "ctags" "default")))
      (setq active-backend (completing-read "Select backend: " backends))
      (setenv "GTAGSLABEL" active-backend)
      (message "Set env GTAGSLABEL=%s" active-backend))))



(provide 'init-ggtags)

;;; init-ggtags.el ends here
