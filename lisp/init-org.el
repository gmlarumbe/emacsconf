;;; init-org.el --- Org  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Org
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
  :hook ((org-agenda-mode . larumbe/org-mode-hook)
         (org-mode        . larumbe/org-mode-hook))
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

  (add-to-list 'org-export-backends 'md) ; Add markdown to export backends

  (defun larumbe/org-show-todos-agenda ()
    "Show `org-mode' TODOs and agenda."
    (interactive)
    (let* ((buf  "TODO.org")
           (file (concat "~/" buf)))
      (when (not (get-buffer buf))
        (find-file file))
      (switch-to-buffer buf)
      (call-interactively #'org-agenda-list)))


  (defun larumbe/org-mode-hook ()
    "`org-mode' own hook."
    (interactive)
    (hardcore-mode -1)))



;;;; Jira
(use-package org-jira
  ;; INFO: Auhentication through .authinfo file
  ;; Plus, the variable `org-jira-users' does not have the expected behaviour
  ;; if the accountId is not findable (that is the case for HP)
  :config)


(use-package ejira
  :ensure nil
  :commands (ejira-update-my-projects)
  :config
  ;; Dependencies (handled manually)
  (use-package ox-jira         :demand)
  (use-package dash-functional :demand)
  (use-package jiralib2        :demand)

  (setq ejira-org-directory "~/.ejira")
  (setq ejira-priorities-alist    '(("Highest" . ?A)
                                    ("High"    . ?B)
                                    ("Medium"  . ?C)
                                    ("Low"     . ?D)
                                    ("Lowest"  . ?E)))
  (setq ejira-todo-states-alist   '(("To Do"       . 1)
                                    ("In Progress" . 2)
                                    ("Done"        . 3)))
  ;; Sync only the tickets assigned to me
  (setq ejira-update-jql-unresolved-fn #'ejira-jql-my-unresolved-project-tickets)
  ;; Tries to auto-set custom fields by looking into /editmeta of an issue and an epic.
  (add-hook 'jiralib2-post-login-hook #'ejira-guess-epic-sprint-fields)

  ;; Agenda
  (require 'ejira-agenda)
  (add-to-list 'org-agenda-files ejira-org-directory) ; Make the issues visisble in the agenda
  ;; Add an agenda view to browse the issues assigned to me
  (org-add-agenda-custom-command
   '("j" "My JIRA issues"
     ((ejira-jql "resolution = unresolved and assignee = currentUser()"
                 ((org-agenda-overriding-header "Assigned to me")))))))


(provide 'init-org)

;;; init-org.el ends here
