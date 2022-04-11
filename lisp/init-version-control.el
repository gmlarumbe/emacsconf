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
  (add-hook 'vc-dir-mode-hook '(lambda () (setq truncate-lines t))))



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
  ;; Subpackages
  (use-package magit-lfs
    :init
    ;; INFO: Magit Remaps ':' key from `magit-git-command' to `magit-lfs'
    ;; Setting following variable maps it to ";" instead
    (setq magit-lfs-suffix ";"))

  (use-package forge
    :config
    ;; Database storage in SQL
    (use-package emacsql))
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

  ;;;;;;;;;;;;;;;;;;
  ;; Magit config ;;
  ;;;;;;;;;;;;;;;;;;
  ;; Highlight differences of selected hunk
  (setq magit-diff-refine-hunk t))


;;;;; Other packages
;; Create URLs for files and commits in GitHub/Bitbucket/GitLab/... repositories.
(use-package git-link
  :bind ("C-c g l" . git-link))

;; Fast browsing of Git historic versions of a file.
(use-package git-timemachine
  :hook ((git-timemachine-mode . linum-mode))
  :config
  (add-hook 'git-timemachine-mode-hook '(lambda () (setq truncate-lines t))))


;;;; Repo
(use-package repo
  :straight (:repo "canatella/repo-el"
             :fork (:repo "gmlarumbe/repo-el"))
  :bind (("C-x j" . repo-status))
  :bind (:map repo-mode-map
         ("U" . larumbe/update-repo))
  :config
  ;; Overwrite font-locking
  (setq repo-font-lock-defaults
        `((("^\\(?1:project\\) \\(?2:[^ ]+\\)/\\W+\\(?3:branch \\(?4:.*\\)\\)$" . ((1 font-lock-function-name-face) (2 font-lock-variable-name-face) (4 font-lock-variable-name-face)))
           ("^\\(?1:project\\) \\(?2:[^ ]+\\)/\\W+\\(?3:(\\*\\*\\* NO BRANCH \\*\\*\\*)\\)" . ((1 font-lock-function-name-face) (2 font-lock-variable-name-face) (3 font-lock-comment-face)))
           ("^Workspace: +\\(.*\\)$" . (1 font-lock-function-name-face))
           ("^Manifest.* branch: +\\(.*\\)$" . (1 font-lock-keyword-face))
           ("^ \\(?1:--\\)" . (1 font-lock-comment-face)) ; Untracked changes
           ("^ \\(?1:-\\)\\(?2:[amdrctu]\\)" . ((1 font-lock-comment-face)  (2 font-lock-builtin-face))) ; Only unstaged changes
           ("^ \\(?1:[AMDRCTU]\\)\\(?2:-\\)" . ((1 font-lock-variable-name-face) (2 font-lock-comment-face))) ; Only staged changes
           ("^ \\(?1:[AMDRCTU]\\)\\(?2:[amdrctu]\\)" . ((1 font-lock-variable-name-face) (2 font-lock-builtin-face))) ; Staged and unstaged changes in the same file
           )))

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
  :commands (svn-status)
  :bind (("C-x ;" . larumbe/svn-status)) ; Overrides `set-comment-column'
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
  :bind (("C-x t"   . larumbe/repohome-magit-status)
         ("C-x y"   . larumbe/repohome-magit-reset-args)))




(provide 'init-version-control)

;;; init-version-control.el ends here
