;;; init-version-control.el --- Init Version Control (Git/Repo/SVN) -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(defvar larumbe/magit-difftastic-enable nil)
(defvar larumbe/magit-lfs-enable nil)


;;;; Magit
(use-package magit
  :bind (("C-x g"   . magit-status)
         ("C-x M-g" . magit-dispatch)
         :map magit-file-section-map ("RET" . magit-diff-visit-file-other-window)
         :map magit-hunk-section-map ("RET" . magit-diff-visit-file-other-window))
  :commands (magit-list-branch-names
             magit-get-current-branch)
  :init
  (setq magit-diff-refine-hunk t)               ; Show word-granularity differences within diff hunks
  (setq magit-diff-highlight-hunk-body nil)     ; Disable background gray highlighting of current hunk
  (setq magit-section-disable-line-numbers nil) ; Tried to use this to show lines but didn't work as expected
  (setq magit-ediff-dwim-show-on-hunks t)       ; Avoid showing three windows for HEAD/index/unstaged and show only two depending on where section the point is in a magit buffer
  :config
  ;; If running an Ediff on Magit, it will create some buffers with suffixes such as
  ;; ".~{index}~". The magit Ediff code calls `magit-find-file-noselect-1' to perform
  ;; Ediff, which in turn calls `magit-revert-rev-file-buffer'. The latter calls
  ;; (normal-mode t) to somehow set the buffer to its corresponding major-mode for
  ;; syntax highlighting. However, hooks are not run. The way to work this around is
  ;; to run them manually using Ediff hooks only on corresponding buffers.
  (defun larumbe/magit-ediff-hook ()
    "Magit fix to show line-numbers and truncate lines on Ediff sessions."
    (let ((buf-name (buffer-name)))
      (when (string-match "\.~.*~$" buf-name)
        (run-mode-hooks))))

  (add-hook 'ediff-prepare-buffer-hook #'larumbe/magit-ediff-hook)

  ;; Also run hooks (to show line numbers and truncate lines) after visiting a file from a diff
  (setq magit-diff-visit-file-hook '(larumbe/magit-ediff-hook)))


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
  ;; Adding the options "--line-numbers" "true" doesn't work as expected with magit...
  (setq magit-delta-delta-args '("--max-line-distance" "0.6" "--true-color" "never" "--diff-so-fancy")))


;; Forge basic setup and configuration:
;;   - https://github.com/vermiculus/magithub/blob/master/magithub.org
;;
;; Authentication: Forge looks at files from variable `auth-sources'.
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
(use-package forge)


;;;; Git misc
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


(use-package gitlab-ci-mode)


(use-package diff-hl
  :bind (("M-<f10>" . global-diff-hl-mode))
  :config
  (add-hook 'magit-pre-refresh-hook 'diff-hl-magit-pre-refresh)
  (add-hook 'magit-post-refresh-hook 'diff-hl-magit-post-refresh))


(when larumbe/magit-lfs-enable
  (use-package magit-lfs
    :commands (magit-lfs)
    :init
    ;; INFO: Magit Remaps ':' key from `magit-git-command' to `magit-lfs'
    ;; Setting following variable maps it to ";" instead
    (setq magit-lfs-suffix ";")))



;;;; Difftastic
;; `difftastic' package is equivalent to my own `magit-difft' utils
;; - https://github.com/pkryger/difftastic.el
(when larumbe/magit-difftastic-enable
  (use-package difftastic
    :after magit
    :demand)

  (use-package difftastic-bindings
    :straight (:host github :repo "pkryger/difftastic.el" :files ("difftastic-bindings.el"))
    :after difftastic
    :demand
    :config (difftastic-bindings-mode))

  ;; `difftastic' package is equivalent to my own `magit-difft' utils
  ;; - https://github.com/pkryger/difftastic.el
  ;; This one should be deprecated once the `difftastic' one is setup properly
  ;; (i.e. customized as god dictates)
  (use-package magit-difft
    :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/magit-difft.el"))
    :after magit
    :demand))


;;;; Own utils
(use-package larumbe-vc-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/larumbe-vc-utils.el")))

(use-package git-dirty
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/git-dirty.el"))
  :bind (("C-<f12>" . git-dirty-check-repos-emacs))
  :init
  (unless straight-base-dir
    (error "Variable `straight-base-dir' not set!"))
  :config
  (setq git-dirty-repo-list-emacs larumbe/emacs-conf-repos-devel)
  (setq git-dirty-repo-list-straight (larumbe/straight-packages)))


(provide 'init-version-control)

;;; init-version-control.el ends here
