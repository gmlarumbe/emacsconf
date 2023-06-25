;;; init-version-control.el --- Init Version Control (Git/Repo/SVN) -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Magit
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


;;;; Misc
(use-package diff-hl
  :bind (("M-<f10>" . global-diff-hl-mode))
  :config
  (add-hook 'magit-pre-refresh-hook 'diff-hl-magit-pre-refresh)
  (add-hook 'magit-post-refresh-hook 'diff-hl-magit-post-refresh))


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
  (setq git-dirty-repo-list-emacs (remove "~/.dotfiles" larumbe/emacs-conf-repos-devel))
  (setq git-dirty-repo-list-straight (larumbe/straight-packages)))


;; TODO: Difftastic with Magit
;; https://tsdh.org/posts/2022-08-01-difftastic-diffing-with-magit.html
;; https://shivjm.blog/better-magit-diffs/
;; https://www.reddit.com/r/emacs/comments/123khq4/better_magit_diffs_with_delta_and_difftastic/
;; https://www.reddit.com/r/emacs/comments/tr42hl/how_to_configure_magit_with_difftastic/
;; https://github.com/Bitnut/diffgit


;; https://tsdh.org/posts/2022-08-01-difftastic-diffing-with-magit.html
(defun th/magit--with-difftastic (buffer command)
  "Run COMMAND with GIT_EXTERNAL_DIFF=difft then show result in BUFFER."
  (let ((process-environment
         (cons (concat "GIT_EXTERNAL_DIFF=difft --width="
                       (number-to-string (frame-width)))
               process-environment)))
    ;; Clear the result buffer (we might regenerate a diff, e.g., for
    ;; the current changes in our working directory).
    (with-current-buffer buffer
      (setq buffer-read-only nil)
      (erase-buffer))
    ;; Now spawn a process calling the git COMMAND.
    (make-process
     :name (buffer-name buffer)
     :buffer buffer
     :command command
     ;; Don't query for running processes when emacs is quit.
     :noquery t
     ;; Show the result buffer once the process has finished.
     :sentinel (lambda (proc event)
                 (when (eq (process-status proc) 'exit)
                   (with-current-buffer (process-buffer proc)
                     (goto-char (point-min))
                     (ansi-color-apply-on-region (point-min) (point-max))
                     (setq buffer-read-only t)
                     (view-mode)
                     (end-of-line)
                     ;; difftastic diffs are usually 2-column side-by-side,
                     ;; so ensure our window is wide enough.
                     (let ((width (current-column)))
                       (while (zerop (forward-line 1))
                         (end-of-line)
                         (setq width (max (current-column) width)))
                       ;; Add column size of fringes
                       (setq width (+ width
                                      (fringe-columns 'left)
                                      (fringe-columns 'right)))
                       (goto-char (point-min))
                       (pop-to-buffer
                        (current-buffer)
                        `(;; If the buffer is that wide that splitting the frame in
                          ;; two side-by-side windows would result in less than
                          ;; 80 columns left, ensure it's shown at the bottom.
                          ,(when (> 80 (- (frame-width) width))
                             #'display-buffer-at-bottom)
                          (window-width
                           . ,(min width (frame-width))))))))))))

(defun th/magit-show-with-difftastic (rev)
  "Show the result of \"git show REV\" with GIT_EXTERNAL_DIFF=difft."
  (interactive
   (list (or
          ;; If REV is given, just use it.
          (when (boundp 'rev) rev)
          ;; If not invoked with prefix arg, try to guess the REV from
          ;; point's position.
          (and (not current-prefix-arg)
               (or (magit-thing-at-point 'git-revision t)
                   (magit-branch-or-commit-at-point)))
          ;; Otherwise, query the user.
          (magit-read-branch-or-commit "Revision"))))
  (if (not rev)
      (error "No revision specified")
    (th/magit--with-difftastic
     (get-buffer-create (concat "*git show difftastic " rev "*"))
     (list "git" "--no-pager" "show" "--ext-diff" rev))))

(defun th/magit-diff-with-difftastic (arg)
  "Show the result of \"git diff ARG\" with GIT_EXTERNAL_DIFF=difft."
  (interactive
   (list (or
          ;; If RANGE is given, just use it.
          (when (boundp 'range) range)
          ;; If prefix arg is given, query the user.
          (and current-prefix-arg
               (magit-diff-read-range-or-commit "Range"))
          ;; Otherwise, auto-guess based on position of point, e.g., based on
          ;; if we are in the Staged or Unstaged section.
          (pcase (magit-diff--dwim)
            ('unmerged (error "unmerged is not yet implemented"))
            ('unstaged nil)
            ('staged "--cached")
            (`(stash . ,value) (error "stash is not yet implemented"))
            (`(commit . ,value) (format "%s^..%s" value value))
            ((and range (pred stringp)) range)
            (_ (magit-diff-read-range-or-commit "Range/Commit"))))))
  (let ((name (concat "*git diff difftastic"
                      (if arg (concat " " arg) "")
                      "*")))
    (th/magit--with-difftastic
     (get-buffer-create name)
     `("git" "--no-pager" "diff" "--ext-diff" ,@(when arg (list arg))))))

(transient-define-prefix th/magit-aux-commands ()
  "My personal auxiliary magit commands."
  ["Auxiliary commands"
   ("d" "Difftastic Diff (dwim)" th/magit-diff-with-difftastic)
   ("s" "Difftastic Show" th/magit-show-with-difftastic)])

(with-eval-after-load 'magit
  (transient-append-suffix 'magit-dispatch "!"
    '("#" "My Magit Cmds" th/magit-aux-commands))

  (define-key magit-status-mode-map (kbd "#") #'th/magit-aux-commands)
)


;; TODO: Still check this one: https://shivjm.blog/better-magit-diffs/
(defun aankh/toggle-magit-delta ()
  (interactive)
  (magit-delta-mode
   (if magit-delta-mode
       -1
     1))
  (magit-refresh))

;; (transient-append-suffix 'magit-diff '(-1 -1 -1)
;;   '("l" "Toggle magit-delta" aankh/toggle-magit-delta))

(defun aankh/recolor-difftastic ()
  (let ((ovs (overlays-in (point-min) (point-max))))
    (dolist (ov ovs)
      (let ((face (overlay-get ov 'face)))
        (when (and (not (null face)) (listp face))
          (when (plist-get face :foreground)
            (plist-put face :foreground (aankh/get-remapped-difftastic-colour (plist-get face :foreground))))
          (when-let ((existing (cl-find :foreground face :key (lambda (x) (if (consp x) (car x) nil)))))
            (setf face
                  (cl-subst `(:foreground ,(aankh/get-remapped-difftastic-colour (plist-get existing :foreground)))
                            :foreground
                            face
                            :key (lambda (x) (if (consp x) (car x) nil)))))
          (overlay-put ov 'face face))))))

(defun aankh/get-remapped-difftastic-colour (original)
  (alist-get original +aankh/difftastic-colour-remapping+ nil nil 'string=))

(defconst +aankh/difftastic-colour-remapping+
  `(("red2" . "#a8353e") ;; https://oklch.com/#50,0.15,20,100
    ("green2" . "#107823")
    ("yellow2" . "#2f3b97")))

;; For some reason, this was being called twice without the guard.
(with-eval-after-load 'magit

(unless (boundp 'aankh/added-magit-diff-suffixes)
  (transient-append-suffix 'magit-diff '(-1 -1)
    [("l" "Toggle magit-delta" aankh/toggle-magit-delta)
     ("D" "Difftastic Diff (dwim)" th/magit-diff-with-difftastic)
     ("S" "Difftastic Show" th/magit-show-with-difftastic)]))
(setf aankh/added-magit-diff-suffixes t)
)

(provide 'init-version-control)

;;; init-version-control.el ends here
