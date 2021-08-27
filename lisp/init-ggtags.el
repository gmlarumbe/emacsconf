;;; init-ggtags.el --- Ggtags/Global  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defvar larumbe/ggtags-enable t
  "Conditionally determine in a hook if mode is enabled.")


(use-package ggtags
  :diminish
  :commands (ggtags-create-tags
             ggtags-current-project-root
             ggtags-find-reference
             modi/ggtags-tag-at-point
             larumbe/ggtags-mode)
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


  (defun larumbe/ggtags-mode (&optional arg)
    "Enable ggtags-mode depending on value of `larumbe/ggtags-enable'.

Purpose is to use this function as a conditional hook.
ARG will be passed to `ggtags-mode' wrapped function."
    (interactive)
    (if larumbe/ggtags-enable
        (ggtags-mode arg)
      (ggtags-mode -1)))



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


  (defun larumbe/gtags-create-tags-async (dir)
    "Similar to `ggtags-create-tags' but asynchronously and adapted to Global+Ctags+Pygments workflow"
    (interactive "DRoot directory: ")
    (let ((gtags-cmd "gtags -v")
          (output-buffer (concat "*gtags-" (file-name-nondirectory (directory-file-name dir)) "*")))
      (save-window-excursion
        (async-shell-command (concat "cd " dir " && " gtags-cmd) output-buffer))
      (message "Started gtags at buffer %s" output-buffer)
      (set-process-sentinel (get-buffer-process output-buffer) #'larumbe/gtags-create-tags-async-sentinel)))



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
