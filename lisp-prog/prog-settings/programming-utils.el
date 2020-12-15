;;; programming-utils.el --- Prog-mode derived modes utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun larumbe/prog-mode-definitions ()
  "Find definition of symbol at point.
If pointing a file, visit that file instead.

Selects between ggtags/xref to find definitions based on major-mode.

INFO: For some major-modes, xref will use global/ggtags as a backend
if configured. However, for elisp seems it's not the default engine,
as well as for C/C++ or Python..."
  (interactive)
  (let ((def (thing-at-point 'symbol)))
    (if (file-exists-p (thing-at-point 'filename))
        (larumbe/find-file-at-point)
      ;; If not pointing to a file choose between different navigation functions
      (cond
       ((string= major-mode "emacs-lisp-mode")
        (xref-find-definitions def))
       (t
        (call-interactively #'ggtags-find-tag-dwim))))))


(defun larumbe/prog-mode-references ()
  "Find references of symbol at point.

Selects between ggtags/xref to find references based on major-mode.

INFO: For some major-modes, xref will use global/ggtags as a backend
if configured. However, for elisp seems it's not the default engine,
as well as for C/C++ or Python..."
  (interactive)
  (let ((ref (thing-at-point 'symbol)))
    (if (file-exists-p (thing-at-point 'filename))
        (larumbe/find-file-at-point)
      ;; If not pointing to a file choose between different navigation functions
      (cond
       ((string= major-mode "emacs-lisp-mode")
        (xref-find-references ref))
       (t
        (ggtags-find-reference ref))))))


(defun larumbe/prog-mode-keys ()
  "Hook to set keys that will override the ones set in the derived major mode."
  (local-set-key (kbd "C-<tab>") #'hs-toggle-hiding)
  (local-set-key (kbd "C-c C-n") #'align-regexp)
  (local-set-key (kbd "C-c C-s") #'larumbe/yas-insert-snippet-dwim)
  (local-set-key (kbd "M-.")     #'larumbe/prog-mode-definitions)
  (local-set-key (kbd "M-?")     #'larumbe/prog-mode-references)
  (unless (or (string= major-mode "verilog-mode")
              (string= major-mode "emacs-lisp-mode"))
    (local-set-key (kbd "C-c C-f") #'flycheck-mode)))


(defun my-prog-mode-hook ()
  "Basic Hook for derived programming modes."
  (larumbe/ggtags-mode        1)
  (larumbe/projectile-mode    1)
  (larumbe/auto-complete-mode 1)
  (show-paren-mode            1)
  (linum-mode                 1)
  (outshine-mode              1)
  (fic-mode                   1)
  (yas-minor-mode             1)
  (hs-minor-mode              1)
  (auto-fill-mode             1)
  (wide-column-mode           1)
  (setq truncate-lines        t)
  (setq fill-column          80))


(provide 'programming-utils)

;;; programming-utils.el ends here