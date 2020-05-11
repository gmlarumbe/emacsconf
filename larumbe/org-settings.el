;;;;;;;;;;;;;;;;;;;;
;; Org-mode setup ;;
;;;;;;;;;;;;;;;;;;;;

(use-package org
  :ensure nil
  :bind (:map org-mode-map
              ("C-c l" . org-store-link)
              ("C-c a" . org-agenda)
              ("C-c c" . org-capture)
              ("C-c b" . org-iswitchb)
              ("C-,"   . nil) ; Unamps org-cycle-agenda-files to free `larumbe/ansi-term'
              )
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
          ("INFO"        . "light blue")
          )))


(defun larumbe/org-show-todos-agenda ()
  "Show org-mode TODOs and agenda."
  (interactive)
  (let* ((buf  "TODO.org")
         (file (concat "~/" buf)))
    (when (not (get-buffer buf))
      (find-file file))
    (switch-to-buffer buf)
    (call-interactively #'org-agenda-list)))