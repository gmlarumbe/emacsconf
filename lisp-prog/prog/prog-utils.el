;;; prog-utils.el --- Prog-mode derived modes utils  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;  Semantic adds an Xref backend for specific modes such as Python/HTML/C.
;;  That's the reason why they are included in `larumbe/prog-mode-references'.
;;  DANGER: Tried to check this on 3 April 2022 and dunno if it was certain...?
;;
;;; Code:

(require 'init-completion)

(defun larumbe/prog-mode-definitions ()
  "Find definition of symbol at point.
If pointing a URL/file, visit that URL/file instead.

Selects between specific xref backends to find definitions.

Assumes that prog-modes will have `dumb-jump' as a fallback backend before etags.
In case definitions are not found and dumb-jump is detected ask for use it as a backend."
  (interactive)
  (let ((file (thing-at-point 'filename))
        (url  (thing-at-point 'url))
        (def  (thing-at-point 'symbol))
        (backend-xref)
        (skip))
    (cond (url
           ;; URL
           (browse-url url))
          ((and file (file-exists-p file))
           ;; File
           (if (and (string= major-mode "python-mode")
                    (string= (file-name-extension file) "py"))
               (larumbe/find-file-at-point #'jedi:goto-definition-push-marker)
             (larumbe/find-file-at-point)))
          ;; If not pointing to a file choose between different navigation functions
          ;; - Python: jedi
          ((string= major-mode "python-mode")
           (call-interactively #'jedi:goto-definition)
           (message "[jedi] Definitions of: %s" def))
          ;; Default to use xref
          (t
           (if def (progn
                     (setq backend-xref (xref-find-backend))
                     ;; `dumb-jump' only supports definitions and does some basic processing of them
                     ;; Since sometimes these could not be the desired ones, ask for confirmation
                     (when (and (equal backend-xref 'dumb-jump)
                                (not (y-or-n-p "No definitions found, try dumb-jump? ")))
                       (setq skip t))
                     (unless skip
                       (xref-find-definitions def)
                       (message "[%s] Definitions of: %s" backend-xref def)))
             ;; Ask for input if there is no def at point
             (call-interactively #'xref-find-definitions))))))


(defun larumbe/prog-mode-references ()
  "Find references of symbol at point using xref.

Assumes that prog-modes will have `dumb-jump' as a fallback backend before etags.
In case references are not found, and dumb-jump is detected as a backend, perform a ripgrep instead.

This ripgrep will be executed at `projectile-project-root' or `default-directory'
and will be applied to only files of current `major-mode' if existing in `larumbe/ripgrep-types'."
  (interactive)
  (let* ((ref (thing-at-point 'symbol))
         (backend-xref))
    (if ref (progn
              (setq backend-xref (xref-find-backend))
              ;; `dumb-jump' only supports definitions (doesn't provide implementation for xref-find-references)
              ;; Since references would be searched through grep and processed by default `semantic-symref'
              ;; a customized ripgrep command is preferred.
              (if (equal backend-xref 'dumb-jump)
                  (when (y-or-n-p "[Skipping dumb-jump] No refs found, try ripgrep? ")
                    (larumbe/ripgrep-xref ref))
                ;; Find references with corresponding backend
                (xref-find-references ref)
                (message "[%s] References of: %s" backend-xref ref)))
      ;; Ask for input if there is no ref at point
      (call-interactively #'xref-find-references))))



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
  (setq-local company-backends (larumbe/company-backend-compute))
  (larumbe/dumb-jump-local-enable)
  (gtags-update-async-minor-mode 1))



(provide 'prog-utils)

;;; prog-utils.el ends here
