;;; init-version-control.el ---   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Repohome
(defvar larumbe/gite-work-tree (expand-file-name "~"))
(defvar larumbe/gite-repo-path (expand-file-name "~/.repohome"))


;;;; vc-dir
(use-package vc-dir
  :ensure nil
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
         ("C-x t"   . larumbe/repohome-magit-status)
         ("C-x y"   . larumbe/repohome-magit-reset-args))
  :commands (magit-list-branch-names
             magit-get-current-branch)
  :config
  ;; Subpackages
  (use-package magit-lfs
    :demand ; Use :demand inside :config instead of :after magit due to load issues
    :init
    ;; INFO: Magit Remaps ':' key from `magit-git-command' to `magit-lfs'
    ;; Setting following variable maps it to ";" instead
    (setq magit-lfs-suffix ";"))

  (use-package magithub
    :config
    (magithub-feature-autoinject t)
    (setq magithub-clone-default-directory "~/github"))


  ;; Magit config
  (setq magit-diff-refine-hunk t) ; Highlight differences of selected hunk

  (defun larumbe/repohome-magit-status ()
    "Perform `magit-status' with `git-dir' and `work-tree' changed accordingly.
INFO: Is not possible to use `magit-git-global-arguments' as a local variable,
since it needs to be set for the whole magit session, not only for the command."
    (interactive)
    (let ((gite-args (concat "--git-dir=" larumbe/gite-repo-path " --work-tree=" larumbe/gite-work-tree)))
      (larumbe/repohome-magit-reset-args)
      (setq magit-git-global-arguments (append magit-git-global-arguments (split-string gite-args))) ; Append `gite' args
      (magit-status-setup-buffer larumbe/gite-work-tree)
      (message "Gite arguments set...")))

  ;; https://emacs.stackexchange.com/questions/3022/reset-custom-variable-to-default-value-programmatically
  (defun larumbe/repohome-magit-reset-args ()
    "Reset git global arguments to switch between `gite' workspace and the rest."
    (interactive)
    (setq magit-git-global-arguments (eval (car (get 'magit-git-global-arguments 'standard-value))))
    (message "Git arguments reset!")))



;;;;; Other packages
;; Create URLs for files and commits in GitHub/Bitbucket/GitLab/... repositories.
(use-package git-link
  :bind ("C-c g l" . git-link))

;; Fast browsing of Git historic versions of a file.
(use-package git-timemachine
  :hook ((git-timemachine-mode . linum-mode))
  :config
  (add-hook 'git-timemachine-mode-hook '(lambda () (setq truncate-lines t))))



;;;;; Aux functions
(defun larumbe/git-find-changed-files-between-branches (rev-a rev-b)
  "Return a list of strings with changed files between REV-A and REV-B."
  (let ((str)
        (buffer-name "*shell-git-diff-output*"))
    (save-window-excursion
      (shell-command
       (concat "git diff --name-status " rev-a ".." rev-b)
       buffer-name)
      (switch-to-buffer buffer-name)
      (goto-char (point-min))
      (while (re-search-forward "[MAD]\t" nil t)  ; Modified/Added/Deleted = MAD
        (replace-match ""))
      (setq str (split-string (buffer-string)))
      str)))


;; https://stackoverflow.com/questions/25009453/how-to-delete-a-list-of-elements-from-another-list-in-elisp
;; It is the same as solution 1 but using delete instead of delq, and printing the value of temp variable at the end
(defun larumbe/git-exclude-files-before-ediff (merge-files exclude-files)
  "Remove EXCLUDE-FILES from MERGE-FILES parameter list."
  (let (temp)
    (setq temp merge-files)
    (mapc
     (lambda (x)
       (setq temp (delete x temp)))
     exclude-files)
    (setq temp temp)))  ; Return only last value after all the iterations


(defun larumbe/git-merge-all-files-between-branches (reva revb changed-files)
  "Ediff/Merge every file from CHANGED-FILES.
Compares same file of revisions REVA and REVB using `magit-ediff-compare'"
  (mapcar
   (lambda (file)
     (magit-ediff-compare reva revb file file))
   changed-files))



;;;;; Interactive functions
(defvar larumbe/git-branch-files-to-exclude-from-merge
      '(".elisp/larumbe/hp-settings.el"
        ".elisp/larumbe/cee-settings.el"
        ".bashrc"
        ".ctags"
        ".gitconfig"
        ".xinitrc"
        ".globalrc"
        "TODO.org"))

(defun larumbe/git-checkout-file-from-another-branch ()
  "Used when an override needs to be performed."
  (interactive)
  (let (fetch-file-from-branch
        fetch-file-to-branch
        filename
        files-changed)
    (save-window-excursion
      ;; Prepare variables according to initial setup and prompts
      (setq fetch-file-from-branch (completing-read "Checkout file from branch: " (magit-list-branch-names)))
      (setq fetch-file-to-branch   (completing-read "Checkout file to branch: "   (magit-list-branch-names) nil nil (magit-get-current-branch)))
      (setq files-changed (larumbe/git-find-changed-files-between-branches fetch-file-from-branch fetch-file-to-branch))
      (setq files-changed (larumbe/git-exclude-files-before-ediff files-changed larumbe/git-branch-files-to-exclude-from-merge))
      (setq filename (completing-read "Choose file to checkout: " files-changed))
      ;; And finally choose between the possible files and execute the shell-command to checkout the file
      (shell-command
       (concat
        magit-git-executable " checkout " fetch-file-to-branch " && "
        magit-git-executable " checkout " fetch-file-from-branch " " filename)))))


(defun larumbe/git-manual-branch-ediff-merge ()
  "Ediff manual merging of every changed file between chosen revisions."
  (interactive)
  (let (changed-files rev-a rev-b)
    (setq rev-a (completing-read "RevA: " (magit-list-branch-names)))
    (setq rev-b (completing-read "RevB: " (magit-list-branch-names) nil nil (magit-get-current-branch)))
    ;; First part is to find which files have changed between both branches
    (setq changed-files (larumbe/git-find-changed-files-between-branches rev-a rev-b))
    ;; An (optional) step would be to determine which of previous files require manual merging
    (setq changed-files (larumbe/git-exclude-files-before-ediff changed-files larumbe/git-branch-files-to-exclude-from-merge))
    ;; Last step would be to merge manually these files
    (larumbe/git-merge-all-files-between-branches rev-a rev-b changed-files)))




;;;; Repo
(defun larumbe/repo-sync-sandboxes (repo-paths)
  "Update all .repo sandboxes passed REPO-PATHS parameters.
Meant to be used in local and remote."
  (while repo-paths
    (async-shell-command
     (concat "cd " (nth 0 (car repo-paths)) " && repo sync")
     (concat "*<" (nth 1 (car repo-paths)) ">*"))
    (setq repo-paths (cdr repo-paths))))




;;;; SVN
(use-package dsvn
  :bind (("C-x j" . larumbe/svn-status)) ; Setting a hook for `svn-status-mode' did not seem to work
  :commands (svn-status
             larumbe/update-svn-repos)
  :config
  (define-obsolete-function-alias 'string-to-int 'string-to-number "22.1")


  (defun larumbe/svn-status ()
    "Perform svn status via `dsvn' on `default-directory'."
    (interactive)
    (svn-status default-directory)
    (setq truncate-lines t))


  (defun larumbe/update-svn-repos (repo-paths)
    "Update all svn-repos passed as REPO-PATHS parameter.
Meant to be used in local and remote."
    (while repo-paths
      (async-shell-command
       (concat "svn update " (nth 0 (car repo-paths)))
       (concat "*svn-update" "<" (nth 1 (car repo-paths)) ">" "*"))
      (setq repo-paths (cdr repo-paths)))))






(provide 'init-version-control)

;;; init-version-control.el ends here
