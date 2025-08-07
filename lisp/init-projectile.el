;;; init-projectile.el --- Projectile setup  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Projectile 2.0 removes automatic keybindings.
;; The keybindings are mapped to `projectile-mode-map' because they need
;; `projectile-mode' to be enabled to work properly.
;;
;; Currently, projectile gets enabled by doing it manually via M-x, or
;; by opening a `prog-mode' derived mode file via `larumbe/prog-mode-hook'.
;;
;;; Code:

;;;; Core
(use-package projectile
  :diminish projectile-mode       ; Also diminishes `larumbe/projectile-custom-mode-line', as it is already available at the left corner
  :bind (:map projectile-mode-map ; Projectile 2.0 removes automatic keybindings
         ("C-c p u" . projectile-regenerate-tags)
         ("C-c p c" . projectile-compile-project))
  :commands (projectile-project-root ; used by many larumbe functions
             projectile-project-name
             larumbe/projectile-custom-mode-line
             larumbe/projectile-project-root-or-current-dir)
  :config
  (setq projectile-indexing-method 'alien) ; `alien' is the fastest indexing method (default), but ignores .projectile ignores
  ;; INFO: hybrid works fine for most of the cases allowing for ignoring of specific dirs.
  ;; Plus, to quickly fetch the file-list, ripgrep based functions are used in conjunction with .gitignore_global
  ;;
  ;; To change indexing method per-project, set the following in the .dir-locals.el:
  ;;  ((nil . ((projectile-indexing-method . alien))))
  ;;
  ;; Source: http://joelmccracken.github.io/entries/project-local-variables-in-projectile-with-dirlocals/

  ;; Enable caching for indexing methods different than 'alien.
  ;; Otherwise `projectile-find-file' is really slow for large projects.
  (setq projectile-enable-caching (not (eq projectile-indexing-method 'alien)))

  ;; By default, on Git repos when fd is available, the command used will be fd with `projectile-git-fd-args'
  (setq projectile-git-fd-args (mapconcat #'identity `(,projectile-git-fd-args "--ignore-file" ,larumbe/gitignore-global-file) " "))

  (add-to-list 'projectile-globally-ignored-directories "*.repo") ; https://github.com/bbatsov/projectile/issues/1250
  (add-to-list 'projectile-globally-ignored-directories "*@@$")   ; Ignore ClearCase versions

  (setq projectile-mode-line-prefix " P") ; Modeline
  (setq projectile-mode-line-function #'larumbe/projectile-custom-mode-line)

  ;; Default search order is defined by functions of variable `projectile-project-root-functions':
  (defvar larumbe/projectile-project-root-files '("Makefile" "GTAGS" ".repo" ".git" ".svn")) ; In order of precedence. If none of this works, use variable `projectile-project-root'
  (setq projectile-project-root-files                    larumbe/projectile-project-root-files) ; Top-down
  (setq projectile-project-root-files-bottom-up          larumbe/projectile-project-root-files) ; Bottom-up
  (setq projectile-project-root-files-top-down-recurring larumbe/projectile-project-root-files) ; Top-down recurring

  (defun larumbe/projectile-custom-mode-line ()
    "Report ONLY project name (without type) in the modeline.
Replaces `projectile-default-mode-line' that also showed ':generic' type of project"
    (let ((project-name (projectile-project-name)))
      (format "%s[%s]"
              projectile-mode-line-prefix
              (or project-name "-"))))

  ;; https://emacs.stackexchange.com/questions/16497/how-to-exclude-files-from-projectile
  ;; Inspired also by kmodi/setup-files/setup-projectile.el:71
  (defun larumbe/projectile-rg-command ()
    "Copied/adapted from `modi/advice-projectile-use-rg'.
Use `rg' for getting a list of all files in the project."
    (mapconcat #'shell-quote-argument
               (append '("rg")
                       larumbe/rg-arguments
                       '("--null" ; Output null separated results
                         ;; Get names of all the to-be-searched files,
                         ;; same as the "-g ''" argument in ag.
                         "--files"))
               " "))

  ;; Use ripgrep for repo sandboxes (considered generic project by projectile)
  (setq projectile-generic-command
        (cond
         ((executable-find "rg")
          (larumbe/projectile-rg-command))
         ;; we prefer fd over find
         ((executable-find "fd")
          "fd . -0 --type f --color=never")
         ;; fd's executable is named fdfind is some Linux distros (e.g. Ubuntu)
         ((executable-find "fdfind")
          "fdfind . -0 --type f --color=never")
         ;; with find we have to be careful to strip the ./ from the paths
         ;; see https://stackoverflow.com/questions/2596462/how-to-strip-leading-in-unix-find
         (t "find . -type f | cut -c3- | tr '\\n' '\\0'")))

  (defun larumbe/projectile-project-root-or-current-dir (&optional dir)
    "Return `projectile-project-root' if existing, current dir otherwise.
Used for some ripgrep/dumb-jump xref related functions."
    (or (projectile-project-root dir)
        default-directory)))



;;;; Ibuffer
(use-package ibuffer-projectile
  :hook ((ibuffer . modi/ibuffer-customization))
  :after ibuffer
  :config
  (defun modi/ibuffer-customization ()
    "My customization for `ibuffer'."
    ;; ibuffer-projectile setup
    (ibuffer-projectile-set-filter-groups)
    (unless (eq ibuffer-sorting-mode 'alphabetic)
      (ibuffer-do-sort-by-alphabetic) ; first do alphabetic sort
      (ibuffer-do-sort-by-major-mode))))


;;;; Ivy
(when (equal larumbe/completion-framework 'ivy)
  (use-package counsel-projectile
    :after projectile ; Otherwise projectile would disable these package keybindings
    :bind (:map projectile-mode-map
           ("C-c p s" . counsel-projectile-switch-project)
           ("C-c p f" . counsel-projectile-find-file)
           ("C-c p b" . counsel-projectile-switch-to-buffer)
           ("C-c p a" . larumbe/counsel-projectile-ag)
           ("C-c p r" . larumbe/counsel-projectile-rg)
           ("C-c p g" . counsel-projectile-grep))
    :config
    (defun larumbe/counsel-projectile--search (cmd)
      "Auxiliary shared function between `counsel-projectile-ag' and `counsel-projectile-rg'.
Similar to `larumbe/counsel--search'.

Intended to do ag/rg with current symbol at point if cursor is over a symbol
and prompt for input otherwise.

If prefix ARG is provided, do case-sensitive search and with whole word.
Otherwise, smart-case is performed (similar to case-fold-search)."
      (let* ((ivy-case-fold-search-default ivy-case-fold-search-default)
             (extra-args nil))
        (when current-prefix-arg
          (setq current-prefix-arg nil)           ; Disable universal-arg value to avoid prompt for extra options
          (setq ivy-case-fold-search-default nil) ; Implicitly sets case-sensitive "-s" flag, which overrides "--smart-case"
          (setq extra-args "-w"))                 ; Whole word search
        (funcall cmd extra-args)))

    (defun larumbe/counsel-projectile-ag ()
      "Execute `counsel-projectile-ag' wrapper."
      (interactive)
      (let ((counsel-projectile-ag-initial-input (if (eq major-mode 'dired-mode)
                                                     nil
                                                   (thing-at-point 'symbol))))
        (larumbe/counsel-projectile--search #'counsel-projectile-ag)))

    (defun larumbe/counsel-projectile-rg ()
      "Execute `counsel-projectile-rg' wrapper."
      (interactive)
      (let ((counsel-projectile-rg-initial-input (if (eq major-mode 'dired-mode)
                                                     nil
                                                   (thing-at-point 'symbol))))
        (larumbe/counsel-projectile--search #'counsel-projectile-rg)))))


;;;; Vertico
(when (equal larumbe/completion-framework 'vertico)
  (use-package consult-projectile
    :diminish
    :after projectile
    :bind (:map projectile-mode-map
           ("C-c p s" . consult-projectile-switch-project)
           ("C-c p f" . consult-projectile-find-file)
           ("C-c p b" . consult-projectile-switch-to-buffer)
           ("C-c p g" . consult-projectile-grep))))
;; For commands `consult-projectile-ag'/`consult-projectile-rg'
;; - https://www.reddit.com/r/emacs/comments/m9zgwi/ann_consultprojectile_consult_integration_for/
;;
;; "This feature is unnecessary. If you set consult-project-root-function to
;; projectile-root as shown in the Consult README, the consult-grep/ripgrep
;; commands will use the project root by default."
;;
;; Seems that consult-grep via ag/rg relies on builtin `project' support instead
;; of on projectile.


;;;; Helm
(when (equal larumbe/completion-framework 'helm)
  (use-package helm-projectile
    :diminish
    :after projectile ; Otherwise projectile would disable these package keybindings
    :bind (:map projectile-mode-map
           ("C-c p s" . helm-projectile-switch-project)
           ("C-c p f" . helm-projectile-find-file)
           ("C-c p a" . helm-projectile-ag)
           ("C-c p g" . helm-projectile-grep)
           ("C-c p r" . helm-projectile-rg))))



(provide 'init-projectile)

;;; init-projectile.el ends here
