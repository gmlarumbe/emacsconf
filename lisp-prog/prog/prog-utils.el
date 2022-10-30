;;; prog-utils.el --- Prog-mode derived modes utils  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;  Semantic adds an Xref backend for specific modes such as Python/HTML/C.
;;  That's the reason why they are included in `larumbe/prog-mode-references'.
;;  DANGER: Tried to check this on 3 April 2022 and dunno if it was certain...?
;;
;;; Code:

(require 'init-completion)


(defun larumbe/prog-mode-report-backend (tag &optional ref-p backend)
  "Show in the minibuffer what is current used backend."
  (let (formatted-backend formatted-tag)
    (unless backend
      (setq backend (xref-find-backend)))
    ;; Add some coloring
    (setq formatted-backend (propertize (symbol-name backend) 'face '(:foreground "goldenrod" :weight bold)))
    (setq formatted-tag (propertize tag 'face '(:foreground "green")))
    ;; Report backend and tag
    (if ref-p
        (message "[%s] Refs of: %s" formatted-backend formatted-tag)
      (message "[%s] Defs of: %s" formatted-backend formatted-tag))))


(defun larumbe/prog-mode-definitions-default (def)
  "Default action to take when looking for definitions in a particular mode."
  (let ((backend-xref (xref-find-backend))
        skip)
    ;; `dumb-jump' only supports definitions and does some basic processing of them
    ;; Since sometimes these could not be the desired ones, ask for confirmation
    (when (and (equal backend-xref 'dumb-jump)
               (not (y-or-n-p "No definitions found, try dumb-jump? ")))
      (setq skip t))
    (unless skip
      (xref-find-definitions def)
      (larumbe/prog-mode-report-backend def))))


(defun larumbe/prog-mode-references-default (ref)
  "Default action to take when looking for references in a particular mode."
  (let ((backend-xref (xref-find-backend)))
    ;; `dumb-jump' only supports definitions (doesn't provide implementation for xref-find-references)
    ;; Since references would be searched through grep and processed by default `semantic-symref'
    ;; a customized ripgrep command is preferred.
    (if (equal backend-xref 'dumb-jump)
        (when (y-or-n-p "[Skipping dumb-jump] No refs found, try ripgrep? ")
          (larumbe/ripgrep-xref ref))
      ;; Find references with corresponding backend
      (xref-find-references ref)
      (larumbe/prog-mode-report-backend ref :ref))))


(defun larumbe/prog-mode-definitions ()
  "Find definition of symbol at point.
If pointing a URL/file, visit that URL/file instead.

Selects between specific xref backends to find definitions.

Assumes that prog-modes will have `dumb-jump' as a fallback backend before etags.
In case definitions are not found and dumb-jump is detected ask for use it as a backend."
  (interactive)
  (let ((file (thing-at-point 'filename :noprop))
        (url  (thing-at-point 'url      :noprop))
        (def  (thing-at-point 'symbol   :noprop))
        (backend-xref)
        (skip))
    (cond (;; URL
           url
           (browse-url url))
          ;; File
          ((and file (file-exists-p (larumbe/strip-file-line-number (substitute-in-file-name file))))
           (larumbe/find-file-dwim))
          ;;   - Org: `org-open-at-point'
          ((string= major-mode "org-mode")
           (call-interactively #'org-open-at-point))
          ;; If not pointing to a file choose between different navigation functions
          ;;   - Verilog: try to jump to module at point if not over a tag
          ((string= major-mode "verilog-mode")
           (if def
               (larumbe/prog-mode-definitions-default def)
             ;; Context based jump if no thing-at-point:
             (cond (;; Inside a module instance
                    (and (verilog-ext-point-inside-block-p 'module)
                         (verilog-ext-instance-at-point))
                    (setq def (match-string-no-properties 1))
                    (xref-find-definitions def)
                    (larumbe/prog-mode-report-backend def))
                   ;; Default fallback
                   (t
                    (call-interactively #'xref-find-definitions)))))
          ((string= major-mode "vhdl-mode")
           (if def
               (larumbe/prog-mode-definitions-default def)
             ;; Context based jump if no thing-at-point:
             (cond (;; Inside an entity instance
                    (vhdl-ext-instance-at-point)
                    (setq def (match-string-no-properties 6))
                    (xref-find-definitions def)
                    (larumbe/prog-mode-report-backend def))
                   ;; Default fallback
                   (t
                    (call-interactively #'xref-find-definitions)))))
          ;;   - Python: elpy
          ((string= major-mode "python-mode")
           (if def
               (progn
                 (xref-find-definitions (elpy-xref--identifier-at-point))
                 (larumbe/prog-mode-report-backend def))
             (call-interactively #'xref-find-definitions)))
          ;; Default to use xref
          (t
           (if def
               (larumbe/prog-mode-definitions-default def)
             ;; Ask for input if there is no def at point
             (call-interactively #'xref-find-definitions))))))


(defun larumbe/prog-mode-references ()
  "Find references of symbol at point using xref.

Assumes that prog-modes will have `dumb-jump' as a fallback backend before etags.
In case references are not found, and dumb-jump is detected as a backend, perform a ripgrep instead.

This ripgrep will be executed at `projectile-project-root' or `default-directory'
and will be applied to only files of current `major-mode' if existing in `larumbe/ripgrep-types'."
  (interactive)
  (let ((ref (thing-at-point 'symbol)))
    (cond (;; Verilog
           (string= major-mode "verilog-mode")
           (if ref
               (larumbe/prog-mode-references-default ref)
             ;; Context based jump if no thing-at-point:
             (cond (;; Inside a module instance
                    (and (verilog-ext-point-inside-block-p 'module)
                         (verilog-ext-instance-at-point))
                    (setq ref (match-string-no-properties 1))
                    (xref-find-references ref)
                    (larumbe/prog-mode-report-backend ref :ref))
                   ;; Default fallback
                   (t
                    (call-interactively #'xref-find-references)))))
          ;; VHDL
          ((string= major-mode "vhdl-mode")
           (if ref
               (larumbe/prog-mode-references-default ref)
             ;; Context based jump if no thing-at-point:
             (cond (;; Inside an entity instance
                    (vhdl-ext-instance-at-point)
                    (setq ref (match-string-no-properties 6))
                    (xref-find-references ref)
                    (larumbe/prog-mode-report-backend ref :ref))
                   ;; Default fallback
                   (t
                    (call-interactively #'xref-find-references)))))
          (;; Python
           (string= major-mode "python-mode")
           (if ref
               (progn
                 (xref-find-references (elpy-xref--identifier-at-point))
                 (larumbe/prog-mode-report-backend ref :ref))
             (call-interactively #'xref-find-references)))
          ;; Default
          (t (if ref
                 (larumbe/prog-mode-references-default ref)
               ;; Ask for input if there is no ref at point
               (call-interactively #'xref-find-references))))))


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


(defun larumbe/prog-mode-indent-tabs-mode ()
  "Do not use TAB for indentation, except for Makefile modes."
  (interactive)
  (if (string-match "makefile-" (format "%s" major-mode))
      (setq indent-tabs-mode t)
    (setq indent-tabs-mode nil)))


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
  (setq-local company-backends larumbe/company-backends-common)
  (larumbe/dumb-jump-local-enable)
  (gtags-update-async-minor-mode 1)
  (larumbe/prog-mode-indent-tabs-mode))



(provide 'prog-utils)

;;; prog-utils.el ends here
