;;; init-org.el --- Org  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;  INFO: NEEDS to be loaded right AFTER Straight bootstraping!
;;
;; If this doesn't happen and another package that has org as
;; a dependency (helm-org, outorg, etc...) gets loaded, it will in turn
;; load the built-in org package and there will be mismatches between
;; outdated built-in version and up to date straight version.
;;
;; There are some related threads due to some variables not being defined,
;; (Symbol’s value as variable is void: org-priority-highest):
;;  - https://github.com/raxod502/straight.el/commit/3190d95ee0556233624a4fb3bd2342e1fcb516b1
;;  - https://github.com/raxod502/straight.el/issues/211
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; If by any case the built-in Emacs bundled version is preferred, the order
;; when it is loaded should not matter and the following should be placed within
;; the use-package declaration:
;;   :straight (:type built-in)
;;
;; NOTE: However this built-in thing did not work possibly due to an already loaded package
;; from straight that had org as a dependency.
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; To use the org-contrib repo:
;;   (use-package org
;;     :straight org-plus-contrib
;;     :config
;;     ...)
;;
;;; Code:


;;;; Org
(use-package org
  :bind (:map org-mode-map
              ("C-c c" . org-capture)
              ("C-c b" . org-iswitchb)
              ("M-."   . org-open-at-point)  ; Override xref-find-definitions, used now to follow internal/external links/tags
              ("M-,"   . org-mark-ring-goto) ; Override xref-pop-marker-stack, used now to pop back links
              ("C-,"   . nil)                ; Unamps org-cycle-agenda-files to free `larumbe/ansi-term'
              ("C-c l" . org-store-link)
              ("C-c a" . org-agenda))
  :bind (("C-x l" . larumbe/org-show-todos-agenda))
  :hook ((org-agenda-mode    . larumbe/org-mode-hook)
         (org-mode           . larumbe/org-mode-hook)
         (org-insert-heading . larumbe/org-insert-current-header))
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
    (hardcore-mode -1))


  (defun larumbe/org-insert-current-header ()
    "Insert current header of highest hierarchy.
Meant to be used as a hook for `org-insert-heading-hook'"
    (interactive)
    (let (outline-path header text)
      (setq outline-path (org-get-outline-path))
      ;; Corner case when it's the first heading after a top-level
      (unless outline-path
        (save-excursion
          (org-previous-visible-heading 1)
          (setq outline-path (org--get-outline-path-1))))
      ;; Set text to be inserted
      (setq header (car outline-path))
      (setq text (concat header ": "))
      (insert text)))


  ;; By default, `org-insert-todo-heading' inserts the TODO after
  ;; the `org-insert-heading-hook'. This advice moves the pointer
  ;; to the end of the line, making it ready to write afterwards.
  (advice-add 'org-insert-todo-heading :after #'org-end-of-line))



(provide 'init-org)

;;; init-org.el ends here
