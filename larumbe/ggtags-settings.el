;;; ggtags-settings.el --- Ggtags/Global  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'f)
(require 'ag)
(require 'custom-functions)

;;; Use-package config
(use-package ggtags
  :diminish
  :commands (ggtags-create-tags ggtags-current-project-root)
  :bind (:map ggtags-navigation-map
              ("M-o"     . nil)
              ("C-c C-k" . nil)         ; EXWM character mode
              ("M->"     . nil)
              ("M-<"     . nil))
  :bind (:map ggtags-mode-map
              ("M-."     . larumbe/ggtags-find-tag-dwim))
  :config
  (setq ggtags-sort-by-nearness t) ; Enabling nearness requires global 6.5+
  (setq ggtags-navigation-mode-lighter nil)
  (setq ggtags-mode-line-project-name nil)
  ;; (setq ggtags-oversize-limit (* 30 1024 1024)) ; 30 MB

  ;; BUG: Set to 0 to avoid the `global -u' automatic GTAGS update if tags file is smaller than the variable.
  ;; Problem is that that automatic command called from (ggtags-update-tags) does not read the Larumbe's verilog source file
  (setq ggtags-oversize-limit 1)      ; If set to nil it seems that there is no limit...
  (setq ggtags-update-on-save nil)   ;; Try to avoid the `global -u in progress...'


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

  (defun larumbe/ggtags-find-tag-dwim ()
    "Wrapper of `ggtags-find-tag-dwim' to visit a tags/files depending
on where the point is."
    (interactive)
    (if (file-exists-p (thing-at-point 'filename))
        (larumbe/find-file-at-point)
      (call-interactively #'ggtags-find-tag-dwim)))


  (defun larumbe/ggtags-mode (&optional arg)
    "Enable `ggtags-mode' depending on current programming `major-mode'.
Add as a hook to every derived `prog-mode' and avoiding being for elisp buffers.
Pass ARG to `ggtags-mode' function if not called interactively."
    (interactive)
    (unless (string-match "emacs-lisp-mode" (format "%s" major-mode)) ; Do not use ggtags @ `emacs-lisp-mode'
      (ggtags-mode arg)))


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
      (message "Set env GTAGSLABEL=%s" active-backend)))


  ;; Advising
  (advice-add 'ggtags-tag-at-point :override #'modi/ggtags-tag-at-point)
  (advice-add 'ggtags-mode         :override #'larumbe/ggtags-mode))


(provide 'ggtags-settings)

;;; ggtags-settings.el ends here
