;;; version-control-settings.el ---   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;; vc-dir
(use-package vc-dir
  :ensure nil
  :bind (:map vc-dir-mode-map
              ("e"       . vc-ediff)      ; Overrides vc-find-file, already mapped to `f'
              ("C-x v p" . svn-propedit)) ; dsvn function 'exported' to be used as well with vc-mode
  :config
  (add-hook 'vc-dir-mode-hook '(lambda () (setq truncate-lines t))))


;;; Git
(use-package magit
  :config
  (setq magit-diff-refine-hunk t)) ; Highlight differences of selected hunk


(use-package magit-lfs
  :init
  ;; INFO: Magit Remaps ':' key from `magit-git-command' to `magit-lfs'
  ;; Setting following variable maps it to ";" instead
  (setq magit-lfs-suffix ";"))



;;; SVN
(use-package dsvn
  :commands (svn-status
             svn-update)
  :config
  (define-obsolete-function-alias 'string-to-int 'string-to-number "22.1"))


;;; Custom functions
;;;; SVN customizations
(defun larumbe/update-svn-repos (repo-paths)
  "Update all svn-repos passed as REPO-PATHS parameter.
Meant to be used in local and remote."
  (while repo-paths
    (async-shell-command
     (concat "svn update " (nth 0 (car repo-paths)))
     (concat "*svn-update" "<" (nth 1 (car repo-paths)) ">" "*"))
    (setq repo-paths (cdr repo-paths))))



;;;; Git customizations
;;;;; Repo sync
(defun larumbe/repo-sync-sandboxes (repo-paths)
  "Update all .repo sandboxes passed REPO-PATHS parameters.
Meant to be used in local and remote."
  (while repo-paths
    (async-shell-command
     (concat "cd " (nth 0 (car repo-paths)) " && repo sync")
     (concat "*<" (nth 1 (car repo-paths)) ">*"))
    (setq repo-paths (cdr repo-paths))))


;;;;; Manual/Ediff Merging
;;;;;; Variables
;; INFO: Needs to be tested after erasing `repohome.el'
;; Ediff/Merge 2 branches manually by doing checkouts
;; This is based on old .repohome sync example. Fill with current development repo branches
;;;;;;; Default repohome values
(defvar larumbe/gite-repo-path "~/.repohome")
(defvar larumbe/gite-work-tree "~")
(defvar larumbe/gite-args (concat "--git-dir=" larumbe/gite-repo-path " --work-tree=" larumbe/gite-work-tree))
(defvar larumbe/gite-cmd (concat magit-git-executable " " larumbe/gite-args))

;;;;;;; Variables to check which repos must get synced
(defvar larumbe/git-available-branches '("hp" "cee" "master"))
(defvar larumbe/git-branch-a "origin/master")
(defvar larumbe/git-branch-b "origin/hp")

;;;;;;; Variables to set which files must be excluded from ediff/merging
(defvar larumbe/git-branch-files-to-exclude-from-merge
      '(".elisp/larumbe/hp-settings.el"
        ".elisp/larumbe/cee-settings.el"
        ".bashrc"
        ".ctags"
        ".gitconfig"
        ".xinitrc"
        ".globalrc"
        "TODO.org"))


;;;;;; Aux functions
(defun larumbe/git-find-changed-files-between-branches ()
  "Return a list of strings with changed files."
  (let ((str)
        (buffer-name "*shell-git-diff-output*"))
    (save-window-excursion
      (shell-command
       (concat "git diff --name-status " larumbe/git-branch-a ".." larumbe/git-branch-b)
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



;;;;;; Interactive functions
(defun larumbe/git-checkout-file-from-another-branch ()
  "Used when an override needs to be performed."
  (interactive)
  (let (fetch-file-from-branch
        fetch-file-to-branch
        filename
        files-changed)
    (save-window-excursion
      ;; Prepare variables according to initial setup and prompts
      (setq fetch-file-from-branch (completing-read "Checkout file from branch: " larumbe/git-available-branches))
      (setq fetch-file-to-branch   (completing-read "Checkout file to branch: "   larumbe/git-available-branches))
      (setq files-changed (larumbe/git-find-changed-files-between-branches))
      (setq files-changed (larumbe/git-exclude-files-before-ediff files-changed larumbe/git-branch-files-to-exclude-from-merge))
      (setq filename (completing-read "Choose file to checkout: " files-changed))
      ;; And finally choose between the possible files and execute the shell-command to checkout the file
      (shell-command
       (concat
        larumbe/gite-cmd " checkout " fetch-file-to-branch " && "
        larumbe/gite-cmd " "
        "checkout "
        "origin/" fetch-file-from-branch " -- "
        larumbe/gite-work-tree "/" filename)))))


(defun larumbe/git-manual-branch-ediff-merge ()
  "Ediff manual inspection/merging on every file that has changed between two branches."
  (interactive)
  (let (changed-files)
    ;; First part is to find which files have changed between both branches
    (setq changed-files (larumbe/git-find-changed-files-between-branches))
    ;; An (optional) step would be to determine which of previous files require manual merging
    (setq changed-files
          (larumbe/git-exclude-files-before-ediff
           changed-files
           larumbe/git-branch-files-to-exclude-from-merge))
    ;; Last step would be to merge manually these files
    (larumbe/git-merge-all-files-between-branches larumbe/git-branch-a
                                                  larumbe/git-branch-b
                                                  changed-files)))


;;;; Repohome
(defun larumbe/repohome-magit-status ()
  "Perform magit-status with `git-dir' and `work-tree' changed accordingly.
INFO: Is not possible to use `magit-git-global-arguments' as a local variable,
since it needs to be set for the whole magit session, not only for the command."
  (interactive)
  (larumbe/repohome-reset-git-args)
  (setq magit-git-global-arguments (append magit-git-global-arguments (split-string larumbe/gite-args))) ; Append `gite' args
  (magit-status-setup-buffer larumbe/gite-work-tree)
  (message "Gite arguments set..."))


;; https://emacs.stackexchange.com/questions/3022/reset-custom-variable-to-default-value-programmatically
(defun larumbe/repohome-reset-git-args ()
  "Reset git global arguments to switch between `gite' workspace and the rest."
  (interactive)
  (setq magit-git-global-arguments (eval (car (get 'magit-git-global-arguments 'standard-value))))
  (message "Git arguments reset!"))




(provide 'version-control-settings)

;;; version-control-settings.el ends here
