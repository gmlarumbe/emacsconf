;;;;;;;;;;;;;;;;;;;;;
;; VERSION CONTROL ;;
;;;;;;;;;;;;;;;;;;;;;

;;; vc-dir
(use-package vc-dir
  :ensure nil
  :bind (:map vc-dir-map
              ("e"       . vc-ediff)     ; Overrides vc-find-file, already mapped to `f'
              ("C-x v p" . svn-propedit) ; dsvn function 'exported' to be used as well with vc-mode
              )
  :config
  (add-hook 'vc-dir-mode-hook '(lambda () (setq truncate-lines t))))


;;; Git
(use-package magit
  :config
  (setq magit-diff-refine-hunk t) ; Highlight differences of selected hunk
  )



;;; SVN
(use-package dsvn
  :config
  (autoload 'svn-status "dsvn" "Run `svn status'." t)
  (autoload 'svn-update "dsvn" "Run `svn update'." t)

  (define-obsolete-function-alias 'string-to-int 'string-to-number "22.1")
  )


;;; Custom functions
;;;; SVN customizations
(defun larumbe/update-svn-repos (repo-paths)
  "Update all svn-repos passed as parameter (to be used in local and cee)"
  (while repo-paths
    (async-shell-command
     (concat "svn update " (nth 0 (car repo-paths)))
     (concat "*svn-update" "<" (nth 1 (car repo-paths)) ">" "*"))
    (setq repo-paths (cdr repo-paths))))



;;;; Git customizations
;;;;; Repo sync
(defun larumbe/repo-sync-sandboxes (repo-paths)
  "Update all .repo sandboxes passed as parameter (to be used in local and cee)"
  (while repo-paths
    (async-shell-command
     (concat "cd " (nth 0 (car repo-paths)) " && repo sync")
     (concat "*<" (nth 1 (car repo-paths)) ">*"))
    (setq repo-paths (cdr repo-paths))))


;;;;; Manual/Ediff Merging
;;;;;; Aux functions
(defun larumbe/git-find-changed-files-between-branches ()
  "Returns a list of strings with changed files"
  (let ((str)
        (buffer-name "*shell-git-diff-output*"))
    (save-window-excursion
      (shell-command
       (concat "git diff --name-status " larumbe/git-branch-a ".." larumbe/git-branch-b)
       buffer-name)
      (switch-to-buffer buffer-name)
      (replace-regexp "[MAD]\t" "" nil (point-min) (point-max)) ; Modified/Added/Deleted = MAD
      (setq str (split-string (buffer-string))))))


(defun larumbe/git-exclude-files-before-ediff (merge-files exclude-files)
  "Remove EXCLUDE-FILES from MERGE-FILES parameter list.
https://stackoverflow.com/questions/25009453/how-to-delete-a-list-of-elements-from-another-list-in-elisp
It is the same as solution 1 but using delete instead of delq, and printing the value of temp variable at the end"
  (let (temp)
    (setq temp merge-files)
    (mapcar
     (lambda (x)
       (setq temp (delete x temp)))
     exclude-files)
    (setq temp temp) ; Return only last value after all the iterations
    ))


(defun larumbe/git-merge-all-files-between-branches (changed-files)
  "Ediff/Merge every changed file (present in `files' argument)"
  (mapcar
   (lambda (file)
     (magit-ediff-compare
      larumbe/git-sync-repo-a
      larumbe/git-sync-repo-b
      file file))
   changed-files))



;;;;;; Interactive functions
;; INFO: Needs to be tested after erasing `repohome.el'
;; Ediff/Merge 2 branches manually by doing checkouts
;; This is based on old .repohome sync example. Fill with current development repo branches
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
  "Ediff manual inspection/merging on every file that has changed between two branches"
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
    (larumbe/git-merge-all-files-between-branches changed-files)))


;;;; Repohome
(defun larumbe/repohome-magit-status ()
  "Perform magit-status with `git-dir' and `work-tree' changed accordingly"
  (interactive)
  (larumbe/repohome-reset-git-args)
  (setq magit-git-global-arguments (append magit-git-global-arguments (split-string larumbe/gite-args))) ; Append `gite' args
  (message "gite arguments set...")
  (magit-status larumbe/gite-work-tree))


;; https://emacs.stackexchange.com/questions/3022/reset-custom-variable-to-default-value-programmatically
(defun larumbe/repohome-reset-git-args ()
  "Resets git global arguments to switch between `gite' workspace and the rest"
  (interactive)
  (message "Git arguments reset!")
  (setq magit-git-global-arguments (eval (car (get 'magit-git-global-arguments 'standard-value)))))
