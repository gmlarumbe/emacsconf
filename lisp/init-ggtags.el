;;; init-ggtags.el --- Ggtags/Global  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Ggtags & Xref:
;;  - Xref uses the backends in the `xref-backend-functions' hook, similar to how
;;  CAPF works (check commentary section of `init-completion').
;;  - If ggtags is enabled the `ggtags--xref-backend' function will be added to the
;;  hook and therefore gtags will be used as a backend for Xref.
;;  - Besides, some major modes define their own backends for Xref (e.g. `elisp--xref-backend')
;;  - Semantic adds a backend for other specific modes such as Python/HTML/C
;;
;;; Code:


(use-package ggtags
  :diminish
  :commands (ggtags-create-tags
             modi/ggtags-tag-at-point
             larumbe/ggtags-global-handle-exit-advice
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
  (setq ggtags-sort-by-nearness nil) ; INFO: If set to non-nil it will not work if using symlinks to external directories
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

  ;; Advice
  (advice-add 'ggtags-navigation-mode-done :override #'larumbe/ggtags-navigation-mode-done)


  ;; INFO: Issue with `ggtags-global-handle-exit' on remote machines where
  ;; *global* buffer was killed before `compilation-auto-jump' could jump to
  ;; first match, when there was only one match.
  ;; The problem was that `ggtags' relies heavily on `compilation-auto-jump'
  ;; executing as a hook of `compilation-finish-functions', and it runs through
  ;; a timer, so on slow/remote machines sometimes the buffer was killed before
  ;; jumping to the first/only match, giving an error.
  ;;
  ;; The workaround implied runnin `ggtags-navigation-mode-cleanup' also with a
  ;; programmable timer through the variable `larumbe/ggtags-global-handle-exit-timer-time'
  ;;
  ;; NOTE: This fix works only the first time a tag is visited if `ggtags-auto-jump-to-match'
  ;; is 'history since somehow once it has been stored in `ggtags-global-search-history'
  ;; it does not execute the adviced snippet of code.

  (defvar larumbe/ggtags-global-handle-exit-timer-time 1
    "Time for the timer to wait until global buffer is killed when there is only 1 result.
Default to 1 sec only if function has been advised through `larumbe/ggtags-global-handle-exit-advice'")
  (defvar larumbe/ggtags-global-handle-exit-use-idle-timer nil
    "If set to non-nil run an idle timer.")

  (defun larumbe/ggtags-global-handle-exit (buf how)
    "A function for `compilation-finish-functions' (which see)."
    (cond
     (ggtags-global-continuation
      (let ((cont (prog1 ggtags-global-continuation
                    (setq ggtags-global-continuation nil))))
        (funcall cont buf how)))
     ((string-prefix-p "exited abnormally" how)
      ;; If exit abnormally display the buffer for inspection.
      (ggtags-global--display-buffer)
      (when (save-excursion
              (goto-char (point-max))
              (re-search-backward
               (eval-when-compile
                 (format "^global: %s not found.$"
                         (regexp-opt '("GTAGS" "GRTAGS" "GSYMS" "GPATH"))))
               nil t))
        (ggtags-echo "WARNING: Global tag files missing in `%s'"
                     ggtags-project-root)
        (remhash ggtags-project-root ggtags-projects)))
     (ggtags-auto-jump-to-match
      (if (pcase (compilation-next-single-property-change
                  (point-min) 'compilation-message)
            ((and pt (guard pt))
             (compilation-next-single-property-change
              (save-excursion (goto-char pt) (end-of-line) (point))
              'compilation-message)))
          ;; INFO: Case when there are multiple matches
          ;; There are multiple matches so pop up the buffer.
          (and ggtags-navigation-mode (ggtags-global--display-buffer))

        ;; INFO: Else clause when there is only one match and global buffer gets killed.
        ;; Similar to the one in `ggtags-global-handle-exit' but running
        ;; the cleanup also with a timer.

        ;; Manually run the `compilation-auto-jump' timer. Hackish but
        ;; everything else seems unreliable. See:
        ;;
        ;; - http://debbugs.gnu.org/13829
        ;; - http://debbugs.gnu.org/23987
        ;; - https://github.com/leoliu/ggtags/issues/89
        ;;
        (pcase (cl-find 'compilation-auto-jump timer-list :key #'timer--function)
          (`nil )
          (timer (timer-event-handler timer)))
        (ggtags-navigation-mode -1)
        (if larumbe/ggtags-global-handle-exit-use-idle-timer
            (run-with-idle-timer larumbe/ggtags-global-handle-exit-timer-time
                                 nil
                                 #'ggtags-navigation-mode-cleanup buf t)
          (run-with-timer larumbe/ggtags-global-handle-exit-timer-time
                          nil
                          #'ggtags-navigation-mode-cleanup buf t))))))

  ;; Advice function (not used on every machine, only in remote slow ones)
  (defun larumbe/ggtags-global-handle-exit-advice (enable)
    "Advice `ggtags-global-handle-exit' if ENABLE is set to non-nil and
remove advice is ENABLE is set to nil."
    (if enable
        (progn
          (advice-add 'ggtags-global-handle-exit :override #'larumbe/ggtags-global-handle-exit)
          (message "Adviced `ggtags-global-handle-exit' with a %s secs timer" larumbe/ggtags-global-handle-exit-timer-time))
      (advice-remove 'ggtags-global-handle-exit #'larumbe/ggtags-global-handle-exit)
      (message "Removed advice on `ggtags-global-handle-exit'. Killing global buffer without timer!")))


;;;; Global/ctags
  ;; INFO: Global does not allow to find external definitions outside project root directory (probably due to security reasons).
  ;; In order to do so, there are 2 methods:
  ;;   - Use symbolic links to external directories.
  ;;   - Make use of GTAGSLIBPATH environment variable.
  ;; Associated thread: https://emacs.stackexchange.com/questions/13254/find-external-definition-with-gtags-or-ggtags
  (defun larumbe/gtags-filelist-create (regex &optional exclude-re dir append)
    "Generate gtags.files on current directory for tags in directory DIR if it is set.
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
    (let* ((buf (process-buffer process))
           (filename default-directory))
      (cond
       ((equal signal "finished\n")
        (pop-to-buffer buf)
        (message "GTAGS generated in %s" buf))
       ;; Error handling
       ('t
        (message "#'larumbe/gtags-create-tags-async-sentinel %s failed with error code %s" filename signal)
        (display-buffer buf)))))


  (defun larumbe/gtags-create-tags-async-kill-buf-sentinel (process signal)
    "Sentinel for asynchronous gtags creation.
Kills gtags buffer after finishing the process if created sucessfully."
    (let* ((buf (process-buffer process))
           (filename default-directory))
      (cond
       ((equal signal "finished\n")
        (message "GTAGS successfully generated  %s" (buffer-file-name buf))
        (quit-window t (get-buffer-window buf)))
       ;; Error handling
       ('t
        (message "#'larumbe/gtags-create-tags-async-kill-buf-sentinel %s failed with error code %s" filename signal)
        (display-buffer buf)))))


  (defun larumbe/gtags-create-tags-async-process (dir &optional bufname kill-buf)
    "Spawn shell and execute gtags asynchronously at directory DIR.
Use buffer BUFNAME if optional arg is provided. Otherwise, default will be *gtags-<dirname>*.
If optional KILL-BUF is non-nil, create a sentinel that kills the process buffer after creating tags."
    (let ((gtags-cmd "gtags -v")
          (output-buffer (if bufname
                             bufname
                           (concat "*gtags-" (file-name-nondirectory (directory-file-name dir)) "*")))
          (sentinel (if kill-buf
                        #'larumbe/gtags-create-tags-async-kill-buf-sentinel
                      #'larumbe/gtags-create-tags-async-sentinel)))
      (save-window-excursion
        (async-shell-command (concat "cd " dir " && " gtags-cmd) output-buffer))
      (message "Started gtags at buffer %s" output-buffer)
      (set-process-sentinel (get-buffer-process output-buffer) sentinel)))



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

  (defun larumbe/gtags-create-tags-async (&optional dir lang bufname kill-buf)
    "Similar to `ggtags-create-tags' but asynchronously and adapted to Global+Ctags+Pygments workflow.

Create tags at DIR for language LANG.
If DIR is nil create tags at `default-directory'.
If LANG is nil default to first language in `larumbe/gtags-create-tags-lang-regexps'.
Use buffer BUFNAME if optional arg is provided. Otherwise, default will be *gtags-<dirname>*.
If KILL-BUF is non-nil kill the *gtags-<path>* buffer after finishing the process.

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
      (larumbe/gtags-create-tags-async-process dir bufname kill-buf)))


  (defun larumbe/gtags-create-tags-async-dirs (dirs)
    "Create gtags for list of strings directories DIRS.
Skip the ones where there is no write permissions."
    (dolist (dir dirs)
      (if (file-writable-p dir)
          (larumbe/gtags-create-tags-async dir
                                           "Elisp"
                                           (concat "*gtags-" (expand-file-name dir) "*")
                                           :kill-buf)
        (message "Skipping %s due to write permissions..." dir))))



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
