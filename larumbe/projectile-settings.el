;;; projectile-settings.el --- Projectile setup  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package projectile
  :bind (:map projectile-mode-map ; Projectile 2.0 removes automatic keybindings
              ("C-c p j" . projectile-find-tag)
              ("C-c p r" . projectile-regenerate-tags)
              ("C-c p c" . projectile-compile-project)
              ("C-c p f" . projectile-find-file)
              ("C-c p a" . helm-projectile-ag)
              ("C-c p g" . helm-projectile-grep))
  :config
  (add-to-list 'projectile-project-root-files-bottom-up ".repo") ; Detect `repo' Git sandboxes (Sandbox preference over IP)
  (setq projectile-completion-system 'helm)
  (setq projectile-mode-line-prefix " P") ; Modeline

  (defun larumbe/projectile-custom-mode-line ()
    "Report ONLY project name (without type) in the modeline.
Replaces `projectile-default-mode-line' that also showed ':generic' type of project"
    (let ((project-name (projectile-project-name)))
      (format "%s[%s]"
              projectile-mode-line-prefix
              (or project-name "-")
              )))
  (setq projectile-mode-line-function #'larumbe/projectile-custom-mode-line))



(provide 'projectile-settings)

;;; projectile-settings.el ends here
