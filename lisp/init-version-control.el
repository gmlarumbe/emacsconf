;;; init-version-control.el --- Init Version Control (Git/Repo/SVN) -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


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
  ;; Magit config
  (setq magit-diff-refine-hunk t) ; Show word-granularity differences within diff hunks
  (setq magit-diff-highlight-hunk-body nil)) ; Disable background gray highlighting of current hunk


(use-package magit-lfs
  :commands (magit-lfs)
  :init
  ;; INFO: Magit Remaps ':' key from `magit-git-command' to `magit-lfs'
  ;; Setting following variable maps it to ";" instead
  (setq magit-lfs-suffix ";"))


;; INFO: Requires xterm-256color to work properly (*ansi-term* is not enough)
;; - https://dandavison.github.io/delta/delta-configs-used-in-screenshots.html
;; - https://scripter.co/using-git-delta-with-magit/
;; - Magit uses its own configuration for faces/highlighting (not the config from .gitconfig)
(use-package magit-delta
  :after magit
  :if (executable-find "delta")
  :demand
  :hook (magit-mode . magit-delta-mode)
  :config
  (setq magit-delta-default-dark-theme "none")
  (setq magit-delta-default-light-theme "none")
  (setq magit-delta-delta-args '("--max-line-distance" "0.6" "--true-color" "never" "--diff-so-fancy")))



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
  (dolist (pattern '("gitconfig-*"
                     ".gitconfig-*"
                     ".gitignore_global\\'"
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
  :straight (:host codeberg
             :repo "pidu/git-timemachine")
  :hook ((git-timemachine-mode . display-line-numbers-mode))
  :config
  (add-hook 'git-timemachine-mode-hook #'(lambda () (setq truncate-lines t))))


;;;; Misc
(use-package diff-hl
  :bind (("M-<f10>" . global-diff-hl-mode))
  :config
  (add-hook 'magit-pre-refresh-hook 'diff-hl-magit-pre-refresh)
  (add-hook 'magit-post-refresh-hook 'diff-hl-magit-post-refresh))


;;;; Own utils
(use-package larumbe-vc-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/larumbe-vc-utils.el"))
  :bind (("C-<f12>" . larumbe/emacs-check-dirty-repos)))

(use-package git-dirty
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/git-dirty.el")))



(provide 'init-version-control)

;;; init-version-control.el ends here
