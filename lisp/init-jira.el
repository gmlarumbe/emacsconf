;;; init-jira.el --- JIRA Org-modes customization  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Org-jira
;; INFO: Using a customized version of `org-jira' for non-Atlassian domain

(use-package org-jira
  :straight (:repo "ahungry/org-jira"
             :fork (:repo "gmlarumbe/org-jira" :branch "hp"))
  :config
  ;; At some point there was a race condition with cURL.
  ;; Set the variable `request-backend' to 'url-retrieve if it happens again.
  ;; https://github.com/tkf/emacs-request/issues/92
  (setq request-backend 'url-retrieve)

  ;; Dependencies
  (require 'cl) ; Required by `jiralib-call' (first params) function

  ;; Overrides
  (defun larumbe/org-jira-get-assignable-users (project-key)
    "Get the list of assignable users for PROJECT-KEY, adding user set jira-users first."
    org-jira-users)

  (defun larumbe/org-jira-get-reporter-candidates (project-key)
    "Get the list of assignable users for PROJECT-KEY, adding user set jira-users first."
    org-jira-users)

  ;; The function `jiralib-get-resolutions' returns a forbidden 403 error.
  ;; Available values need to be determined mannually.
  (defun larumbe/org-jira-read-resolution ()
    "Read issue workflow progress resolution."
    (let* ((hp-resolutions '("Done" "Cannot Reproduce" "Declined" "Duplicate" "Feature Dropped" "Not a Bug" "Won't Do"))
           (resolution (completing-read "Resolution: " hp-resolutions)))
      (cons 'name resolution)))


  ;; Avoid retrieval of the whole list of users
  (advice-add 'org-jira-get-assignable-users    :override #'larumbe/org-jira-get-assignable-users)
  (advice-add 'org-jira-get-reporter-candidates :override #'larumbe/org-jira-get-reporter-candidates)

  ;; Fix the `org-jira-progress-issue' problem with the Resolution required field that doesn't get set.
  (advice-add 'org-jira-read-resolution         :override #'larumbe/org-jira-read-resolution)


  ;; The limitation of `org-jira-create-issue' is that for non-Atlassian domains, the fields
  ;; components, acceptance criteria and fix version/s are required, and it gets complicated
  ;; add them to the fields in the `org-jira-get-issue-struct' call.
  ;;
  ;; The `org-jira-get-issue-struct' is only called by `org-jira-create-issue' and `org-jira-create-subtask',
  ;; and it creates some cons cells with the required REST fields that are converted later into JSON.
  ;; The required fields (components, acceptance criteria and fix version/s) need to be an array and the
  ;; function `json-encode' does not support that out-of-the-box.
  ;;
  ;; Therefore, it is easier to use a function that creates a template and update fields individually later.
  (defun larumbe/org-jira-create-issue-hp-template ()
    "JIRA Issue creation template.
SUMMARY and DESCRIPTION."
    (interactive)
    (let* ((project larumbe/org-jira-project)
           (parent "null") ; For the time being don't create subtasks
           (type (if current-prefix-arg
                     (org-jira-read-issue-type project)
                   "Story"))
           (issuetype (car (rassoc type (jiralib-get-issue-types-by-project project))))
           (summary (read-string "Summary: " "To "))
           (description (read-string "Description: "))
           (jira-users (org-jira-get-assignable-users project))
           (user (completing-read "Assignee: " jira-users))
           (assignee (cdr (assoc user jira-users)))
           (components (jiralib-get-components project))
           (component-name (org-jira-read-component larumbe/org-jira-project))
           (component-id (car (rassoc component-name components)))
           (acceptance-criteria "||Num||Test Name||Status||
|1| | |")
           (fixversions (completing-read "Fix Versions" (mapcar
                                                         (lambda (version) (cdr (assoc 'name version)))
                                                         (jiralib-get-versions project))))
           (template-json (concat
       "{\"fields\": {

            \"project\": {
                \"key\":\"" project "\"
             },

            \"parent\": {
                \"key\": " parent "
             },

            \"issuetype\": {
                \"id\":\"" issuetype "\"
             },

            \"summary\":\"" summary "\",

            \"description\":\"" description "\",

            \"assignee\": {
                \"name\":\"" assignee "\"
            },

            \"components\": [
                {
                    \"id\":\"" component-id "\"
                }
            ],

            \"customfield_11108\":\"" acceptance-criteria "\",

            \"fixVersions\": [
                {
                    \"name\":\"" fixversions "\"
                }
            ]
       }  }"))
           (response))
      ;; Check input
      (if (or (equal summary "")
              (equal description "")
              (equal assignee "")
              (equal component-id "")
              (equal fixversions ""))
          (error "Must provide all information!"))
      ;; Perform issue creation request
      (setq response (jiralib--rest-call-it
                      "/rest/api/2/issue"
                      :type "POST"
                      :data template-json))
      (jiralib--rest-call-it (cdr (assoc 'self response)) :type "GET")
      (message "HP Template JIRA issue created successfully!")))


  (defun larumbe/org-jira-set-issue-components ()
    "If placed inside a JIRA issue this function will fill the components field
with some of the availables.

Issue needs to be updated manually later via `org-jira-update-issue'."
    (interactive)
    (ensure-on-issue
      (let* ((component-list (org-jira-read-components larumbe/org-jira-project))
             (component-string (mapconcat #'identity component-list ", ")))
        (org-set-property "components" component-string)))))



;;;; Ejira
;; Dependencies (handled manually)
(use-package ox-jira)
(use-package dash-functional)
(use-package jiralib2)


;; DANGER: Stopped working with error:
;; - ejira--set-heading-body-jira-markup: Wrong type argument: integer-or-marker-p, nil
(use-package ejira
  :straight (:host github :repo "nyyManni/ejira")
  :config
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


(provide 'init-jira)

;;; init-jira.el ends here
