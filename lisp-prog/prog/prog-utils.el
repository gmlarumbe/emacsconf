;;; prog-utils.el --- Prog-mode derived modes utils  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;  Semantic adds an Xref backend for specific modes such as Python/HTML/C.
;;  That's the reason why they are included in `larumbe/prog-mode-references'.
;;
;;; Code:

(require 'init-completion)

(defun larumbe/prog-mode-definitions ()
  "Find definition of symbol at point.
If pointing a URL/file, visit that URL/file instead.

Selects between ggtags/xref to find definitions based on `major-mode'.

INFO: For some major-modes, xref will use global/ggtags as a backend
if configured.  However, for elisp seems it's not the default engine,
as well as for C/C++ or Python..."
  (interactive)
  (let ((file (thing-at-point 'filename))
        (url  (thing-at-point 'url))
        (def  (thing-at-point 'symbol)))
    (cond (url  (browse-url url))
          ((and file (file-exists-p file))
           (larumbe/find-file-at-point))
          ;; If not pointing to a file choose between different navigation functions
          ((string= major-mode "emacs-lisp-mode")
           (if def
               (xref-find-definitions def)
             (call-interactively #'xref-find-definitions)))
          ;; Default will be using ggtags interface
          (t
           (call-interactively #'ggtags-find-tag-dwim)))))


(defun larumbe/prog-mode-references ()
  "Find references of symbol at point.

Selects between ggtags/xref to find references based on `major-mode'.

INFO: For some major-modes, xref will use global/ggtags as a backend
if configured.  However, for elisp seems it's not the default engine,
as well as for C/C++ or Python..."
  (interactive)
  (let ((ref (thing-at-point 'symbol)))
    (cond ((or (string= major-mode "c-mode")
               (string= major-mode "python-mode")
               (string= major-mode "emacs-lisp-mode"))
           (if ref
               (xref-find-references ref)
             (call-interactively #'xref-find-references)))
          ;; Default will be using ggtags interface
          (t
           (call-interactively #'ggtags-find-reference ref)))))



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


(defun larumbe/prog-mode-hook ()
  "Basic Hook for derived programming modes."
  (ggtags-mode         1)
  (projectile-mode     1)
  (company-mode        1)
  (show-paren-mode     1)
  (linum-mode          1)
  (outshine-mode       1)
  (fic-mode            1)
  (yas-minor-mode      1)
  (hs-minor-mode       1)
  (wide-column-mode    1)
  (setq truncate-lines t)
  (setq fill-column   80)
  (setq-local company-backends (larumbe/company-backend-compute)))


(provide 'prog-utils)

;;; prog-utils.el ends here
