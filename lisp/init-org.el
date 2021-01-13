;;; init-org.el --- Org  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package org
  :ensure nil
  :bind (:map org-mode-map
              ("C-c c" . org-capture)
              ("C-c b" . org-iswitchb)
              ("M-."   . org-open-at-point)  ; Override xref-find-definitions, used now to follow internal/external links/tags
              ("M-,"   . org-mark-ring-goto) ; Override xref-pop-marker-stack, used now to pop back links
              ("C-,"   . nil)                ; Unamps org-cycle-agenda-files to free `larumbe/ansi-term'
              ("C-c l" . org-store-link)
              ("C-c a" . org-agenda))
  :bind (("C-x l" . larumbe/org-show-todos-agenda))
  :hook ((org-agenda-mode . larumbe/org-agenda-mode-hook))
  :config
  (setq org-log-done 'time)
  (setq org-agenda-files (list "~/TODO.org"))
  (setq org-todo-keywords
        '((sequence "TODO" "IN PROGRESS" "|" "DONE" "CANCELED" "POSTPONED")
          (sequence "|" "INFO")))
  (setq org-todo-keyword-faces
        '(("TODO"        . org-warning)
          ("IN PROGRESS" . "yellow")
          ("CANCELED"    . (:foreground "blue" :weight bold))
          ("POSTPONED"   . "cyan")
          ("INFO"        . "light blue")))


  (defun larumbe/org-show-todos-agenda ()
    "Show `org-mode' TODOs and agenda."
    (interactive)
    (let* ((buf  "TODO.org")
           (file (concat "~/" buf)))
      (when (not (get-buffer buf))
        (find-file file))
      (switch-to-buffer buf)
      (call-interactively #'org-agenda-list)))


  (defun larumbe/org-agenda-mode-hook ()
    "`org-agenda-mode' own hook."
    (interactive)
    (hardcore-mode -1)))



(provide 'init-org)

;;; init-org.el ends here
