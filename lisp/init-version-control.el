;;; init-version-control.el --- Init Version Control (Git/Repo/SVN) -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; vc-dir
(use-package vc-dir
  :straight nil
  :bind (:map vc-dir-mode-map
              ("e"       . vc-ediff)      ; Overrides vc-find-file, already mapped to `f'
              ("C-x v p" . svn-propedit)) ; dsvn function 'exported' to be used as well with vc-mode
  :config
  (add-hook 'vc-dir-mode-hook #'(lambda () (setq truncate-lines t))))



;;;; Git
;;;;; Magit
(use-package magit
  :bind (("C-x g"   . magit-status)
         ("C-x M-g" . magit-dispatch)
         :map magit-file-section-map ("RET" . magit-diff-visit-file-other-window)
         :map magit-hunk-section-map ("RET" . magit-diff-visit-file-other-window))
  :commands (magit-list-branch-names
             magit-get-current-branch)
  :config
  (defun larumbe/magit-customize-dispatch ()
    "Customize `magit-dispatch' according to available magit extensions.
These make the commands available to `magit-dispatch' and `magit-status'
before loading them, acting as autoloads.

Some of the code is copied directly from the packages themselves. In case
some day some change on a key is needed, make them be in sync."
    ;; `magit-lfs'
    (when (locate-library "magit-lfs")
      ;; Fetched from `magit-lfs' code to emulate an autoload
      (define-key magit-status-mode-map magit-lfs-suffix #'magit-lfs)
      (transient-append-suffix 'magit-dispatch '(0 -1 -1)
        `(magit-lfs
          :key ,magit-lfs-suffix
          :description "Magit-LFS")))
    ;; `magit-gerrit'
    (when (locate-library "magit-gerrit")
      (define-key magit-status-mode-map magit-gerrit-popup-prefix #'magit-gerrit-popup)
      (transient-append-suffix 'magit-dispatch "Q"
        `(magit-gerrit-popup
          :key ,magit-gerrit-popup-prefix
          :description "Magit-Gerrit")))
    ;; `gerrit'
    (when (locate-library "gerrit")
      (add-hook 'magit-status-sections-hook #'larumbe/gerrit-magit-insert-status t)
      (define-key magit-status-mode-map "," #'gerrit-dashboard)
      (transient-append-suffix 'magit-dispatch "H"
        `(gerrit-dashboard
          :key ","
          :description "Gerrit dashboard"))
      (define-key magit-status-mode-map "." #'gerrit-download)
      (transient-append-suffix 'magit-dispatch '(0 -1 -1)
        `(gerrit-download
          :key "."
          :description "Gerrit download"))
      (define-key magit-status-mode-map "/" #'gerrit-upload-transient)
      (transient-append-suffix 'magit-dispatch '(0 -1 -1)
        `(gerrit-upload-transient
          :key "/"
          :description "Gerrit upload")))
    ;; `forge'
    (when (locate-library "forge")
      (define-key magit-status-mode-map "'" #'forge-dispatch)
      (define-key magit-status-mode-map "N" #'forge-dispatch)
      (transient-insert-suffix 'magit-dispatch "o"
        '("N" "Forge" forge-dispatch))
      (transient-insert-suffix 'magit-dispatch '(0 -1 -1)
        '("'" "Forge" forge-dispatch))))

  ;; Magit config
  (setq magit-diff-refine-hunk t) ; Highlight differences of selected hunk
  (larumbe/magit-customize-dispatch))



(use-package magit-lfs
  :commands (magit-lfs)
  :init
  ;; INFO: Magit Remaps ':' key from `magit-git-command' to `magit-lfs'
  ;; Setting following variable maps it to ";" instead
  (setq magit-lfs-suffix ";"))



;;;;; Gerrit
;; https://github.com/emacsorphanage/magit-gerrit/issues/59
;; Original magit-gerrit was not maintained anymore and transfered to Emacsorphanage
;; after Tarsius looked at many different forks.
;;  - Decided to create my own fork to add R transient to `magit-dispatch'
(use-package magit-gerrit
  :straight (:repo "emacsorphanage/magit-gerrit"
             :fork (:repo "gmlarumbe/magit-gerrit"))
  :commands (magit-gerrit-popup)
  :init
  (setq magit-gerrit-popup-prefix "R"))



(use-package gerrit
  :commands (gerrit-upload-transient
             gerrit-download
             gerrit-magit-insert-status
             larumbe/gerrit-magit-insert-status)
  :config
  ;; INFO: Removed the -is:wip  and -is:ignored things from suggested config at https://github.com/thisch/gerrit.el
  (setq gerrit-dashboard-query-alist
        '(("Assigned to me"   . "assignee:self (owner:self OR assignee:self) is:open")
          ("Outgoing reviews" . "is:open owner:self")
          ("Incoming reviews" . "is:open -owner:self (reviewer:self OR assignee:self)")
          ("CCed On"          . "is:open  cc:self")
          ("Recently closed"  . "is:closed  (owner:self) (owner:self OR reviewer:self OR assignee:self OR cc:self) limit:15")))

  (defun larumbe/gerrit-magit-insert-status ()
    "Make sure that Gerrit bar is only added for Gerrit repos."
    (when (file-exists-p (larumbe/path-join (magit-toplevel) ".gitreview"))
      (gerrit-magit-insert-status))))


;;;;; Forge
;; INFO: Magithub is broken and unmaintained, using `forge' instead.
;;  It seems `forge' is heavily based on what what's been done in Magithub.
;;
;; Forge basic setup and configuration:
;;   - https://github.com/vermiculus/magithub/blob/master/magithub.org
;;
;; Authentication: Forge looks at variable `auth-sources', normally at ./authinfo
;; Within that file, the following structure is required:
;;  - machine api.github.com login user^forge password ***
;;
;; Plus, the [github] section in .gitconfig is not used by Git by defult,
;; but is instead a section of .gitconfig (global) used by Forge.
;; In this section, there are two fields that can be configured:
;;   - user = <github_user>
;;   - host (default is api.github.com, so not needed so far)
;;
;; If besides a regular user, other account with GHE needs to be added,
;; customize previous fields but with proper user/host in .gitconfig and .authinfo.
;;  Add to .authinfo:
;;  - machine ghe.example.domain login user^forge password ***
;;
;;  .gitconfig:
;;  [github]
;;    user = <regular_user>
;;
;;  [github "<ghe_host>"]
;;    user = <ghe_user>
;;
;; And add the GHE host to the variable `forge-alist'
;; (with-eval-after-load 'forge
;;   (push '("<host>" "<host_api>" "<id_for_local_database>" forge-github-repository) forge-alist))
;;
;; Finally, take into account that to get list of assignable issues, the github.user needs
;; to be set properly locally (otherwise it will take the global value)
;;   $ git config github.user <user_for_current_repo>
;;
;; NOTE: Issue creation/modification did not work properly with older versions of git (e.g. 2.11)
(use-package forge
  :config
  ;; Database storage in SQL
  (use-package emacsql))


;;;;; Other packages
;; This package provides several major modes for editing Git configuration files.
;;   - `gitattributes-mode'
;;   - `gitconfig-mode'
;;   - `gitignore-mode'
;; Adds to the `auto-mode-alist' these modes to their corresponding files.
(use-package git-modes
  :init
  (dolist (pattern '("\\.git_cfgs/gitconfig-*"
                     "/\\.gitreview\\'"))
    (add-to-list 'auto-mode-alist (cons pattern 'gitconfig-mode))))


;; Create URLs for files and commits in GitHub/Bitbucket/GitLab/... repositories.
;; Autoloads:
;;  - `git-link'
;;  - `git-link-commit'
;;  - `git-link-homepage'
(use-package git-link)


;; Fast browsing of Git historic versions of a file.
(use-package git-timemachine
  :hook ((git-timemachine-mode . linum-mode))
  :config
  (add-hook 'git-timemachine-mode-hook #'(lambda () (setq truncate-lines t))))


;;;; Repo
(use-package repo
  :straight (:repo "canatella/repo-el"
             :fork (:repo "gmlarumbe/repo-el" :branch "dev"))
  :bind (:map repo-mode-map
         ("U" . larumbe/update-repo))
  :config
  ;; Add additional debug messages
  (advice-add 'repo-status :after #'(lambda (workspace) (message "repo status @ %s" (file-name-nondirectory (directory-file-name workspace)))))

  ;; update_repo interface
  (defvar larumbe/repo-workspace nil "docstring")

  (defun larumbe/update-repo-sentinel (process signal)
    "Notify the user when current workspace has been updated."
    (cond
     ((equal signal "finished\n")
      (repo-status larumbe/repo-workspace)
      (message "%s updated!" larumbe/repo-workspace))
     ;; Error handling
     ('t
      (message "urepo process open message got signal %s" signal)
      (display-buffer (process-buffer process)))))

  (defun larumbe/update-repo ()
    "Update repo with 'urepo' command."
    (interactive)
    (unless (and (executable-find "repo")
                 (executable-find "urepo"))
      (error "repo and urepo not found!"))
    (let (proc buf cmd)
      (setq larumbe/repo-workspace repo-workspace)
      (setq cmd "urepo")
      (setq buf "*update_repo*")
      (setq proc (start-process-shell-command "update_repo" buf cmd))
      (pop-to-buffer buf)
      (message "Updating *%s*" (file-name-nondirectory (directory-file-name larumbe/repo-workspace)))
      (set-process-sentinel proc #'larumbe/update-repo-sentinel))))


;;;; SVN
(use-package dsvn
  :commands (svn-status larumbe/svn-status)
  :config
  (define-obsolete-function-alias 'string-to-int 'string-to-number "22.1")

  (defun larumbe/svn-status ()
    "Perform svn status via `dsvn' on `default-directory'."
    (interactive)
    (svn-status default-directory)
    (setq truncate-lines t)))



;;;; Own utils
(use-package larumbe-vc-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/larumbe-vc-utils.el"))
  :bind (("C-<f12>" . larumbe/emacs-check-dirty-repos)))

(use-package git-dirty
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/git-dirty.el")))



(provide 'init-version-control)

;;; init-version-control.el ends here
