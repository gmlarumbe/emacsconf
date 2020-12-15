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
  :config
  (setq ggtags-sort-by-nearness t) ; Enabling nearness requires global 6.5+
  (setq ggtags-navigation-mode-lighter nil)
  (setq ggtags-mode-line-project-name nil)
  ;; (setq ggtags-oversize-limit (* 30 1024 1024)) ; 30 MB

  ;; BUG: Set to 0 to avoid the `global -u' automatic GTAGS update if tags file is smaller than the variable.
  ;; Problem is that that automatic command called from (ggtags-update-tags) does not read the Larumbe's verilog source file
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
