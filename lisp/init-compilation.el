;;; init-compilation.el --- Compilation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package compile
  :straight nil
  :bind (([f5]  . compile))
  :bind (:map compilation-mode-map
         ("r"   . rename-buffer)
         ("M-." . larumbe/xref-find-definitions)) ; Browse URLs and files
  :bind (:map compilation-shell-minor-mode-map
         ("M-RET" . nil)) ; Leave space for `company-complete'
  :hook ((compilation-mode . larumbe/compilation-hook))
  :commands (recompile)
  :init
  ;; Compilation motion commands skip less important messages. The value can be either
  ;; 2 -- skip anything less than error,
  ;; 1 -- skip anything less than warning or
  ;; 0 -- don't skip any messages.
  (setq compilation-skip-threshold 2) ; Compilation error jumping settings
  (setq compilation-message-face nil) ; Set to nil to remove underlines from compilation faces (defaults to 'underline)
  (setq compilation-scroll-output 'first-error)

  :config
  (require 'popwin)
  (assq-delete-all 'compilation-mode popwin:special-display-config) ; Remove previous entries for compilation-mode

  (defun larumbe/compilation-hook ()
    (setq truncate-lines t))

  ;; Recompile keeping current error regexps
  (defun larumbe/compilation-recompile-keep-re-alist (oldfun &rest r)
    (let ((buf (current-buffer))
          (re-alist       compilation-error-regexp-alist)
          (re-alist-alist compilation-error-regexp-alist-alist))
      (apply oldfun r)
      (pop-to-buffer buf)
      (setq-local compilation-error-regexp-alist       re-alist)
      (setq-local compilation-error-regexp-alist-alist re-alist-alist)))

  (advice-add 'recompile :around #'larumbe/compilation-recompile-keep-re-alist))


(use-package compilation-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/compilation-utils.el"))
  :after compile
  :demand
  :bind (:map compilation-mode-map
         ("j" . larumbe/recompile-with-regexp-alist)
         ("t" . larumbe/compilation-threshold))
  :init
  (setq compilation-buffer-name-function #'larumbe/compilation-buffer-name-function))


(use-package ansi-color
  :hook (compilation-filter . ansi-color-compilation-filter))


;;;; Package providing

(provide 'init-compilation)

;;; init-compilation.el ends here
