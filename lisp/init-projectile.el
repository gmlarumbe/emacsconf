;;; init-projectile.el --- Projectile setup  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(defvar larumbe/projectile-enable t
  "Conditionally determine in a hook if mode is enabled.")


(use-package projectile
  :diminish projectile-mode       ; Also diminishes `larumbe/projectile-custom-mode-line', as it is already available at the left corner
  :bind (:map projectile-mode-map ; Projectile 2.0 removes automatic keybindings
              ("C-c p j" . projectile-find-tag)
              ("C-c p u" . projectile-regenerate-tags)
              ("C-c p c" . projectile-compile-project)
              ("C-c p f" . projectile-find-file)
              ("C-c p s" . projectile-switch-project)
              ("C-c p a" . helm-projectile-ag)
              ("C-c p g" . helm-projectile-grep)
              ("C-c p r" . helm-projectile-rg))

  :commands (projectile-project-name
             larumbe/projectile-custom-mode-line
             larumbe/projectile-mode)

  :config
  (setq projectile-enable-caching t) ; Enable caching, otherwise `projectile-find-file' is really slow for large projects.

  (add-to-list 'projectile-globally-ignored-directories "*.repo") ; https://github.com/bbatsov/projectile/issues/1250

  (let ((ignore-targets '("bundle_targets" "sim_targets" "syn_targets" "doc_targets" "version_targets")))
    (dolist (dir ignore-targets)
      (add-to-list 'projectile-globally-ignored-directories dir)))

  (setq projectile-indexing-method 'hybrid) ; `alien' is the fastest indexing method (default), but ignores .projectile ignores
  (setq projectile-completion-system 'helm)
  (setq projectile-mode-line-prefix " P") ; Modeline
  (setq projectile-mode-line-function #'larumbe/projectile-custom-mode-line)

  ;; Default search order is defined by functions of variable `projectile-project-root-functions':
  (defvar larumbe/projectile-project-root-files '("GTAGS" ".repo" ".git" ".svn")) ; In order of precedence. If none of this works, use variable `projectile-project-root'
  (setq projectile-project-root-files                    larumbe/projectile-project-root-files) ; Top-down
  (setq projectile-project-root-files-bottom-up          larumbe/projectile-project-root-files) ; Bottom-up
  (setq projectile-project-root-files-top-down-recurring larumbe/projectile-project-root-files) ; Top-down recurring


  (defun larumbe/projectile-custom-mode-line ()
    "Report ONLY project name (without type) in the modeline.
Replaces `projectile-default-mode-line' that also showed ':generic' type of project"
    (let ((project-name (projectile-project-name)))
      (format "%s[%s]"
              projectile-mode-line-prefix
              (or project-name "-"))))


  (defun larumbe/projectile-mode (&optional arg)
    "Enable projectile-mode depending on value of `larumbe/projectile-enable'.

Purpose is to use this function as a conditional hook.
ARG will be passed to `projectile-mode' wrapped function."
    (interactive)
    (if larumbe/projectile-enable
        (projectile-mode arg)
      (projectile-mode -1))))



(provide 'init-projectile)

;;; init-projectile.el ends here
