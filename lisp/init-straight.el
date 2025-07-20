;;; init-straight.el --- Straight Package Manager Init settings  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Package configuration is based upon straight.el and use-package
;;  - https://github.com/radian-software/straight.el
;;  - https://github.com/jwiegley/use-package
;;
;; Straight completely replaces Emacs default `package' system.
;; Instead of fetching tarballs from MELPA, straight clones Git repos into
;; `straight-base-dir'/repo directory and creates symlinks/autoloads in the build directory.
;; It easily integrates with `use-package' macro to make it less verbose and more readable.
;;
;; For built-in packages, straight documentation says that :straight (type: built-in) will
;; avoid trying to download the package.  However, :straight nil seems to have the same effect.
;;
;; Normally, for packages that are present in MELPA the :host keyword is not required.
;; If it is not present at MELPA it will normally be set to :host github.
;;
;; If the default name of the repo needs to be different (e.g. an .emacs.d named repo), the
;; keywords :local-repo can be used to set the local copy name.
;;
;; There might be cases (e.g. emacswiki.org) where we only want one file for the build.
;; Using the :files section avoids autoloading all the .el of the the Git root directory.
;;
;; If package name is different than mode name (e.g. Matlab):
;; (use-package matlab
;;   :straight matlab-mode)
;;
;; - With respect to key mapping and overriding:
;;     - If declaring with :bind, the keybindings will be overriden by major-mode keybindings
;;     - To override minor-mode keybindings, use :bind*
;;     - To override major-mode derived keybindings, use a hook (e.g. prog-mode-hook)
;;
;;; Code:

;;;; Straight bootstrap
(defvar bootstrap-version)
(let ((bootstrap-file
       (expand-file-name
        "straight/repos/straight.el/bootstrap.el"
        (or (bound-and-true-p straight-base-dir)
            user-emacs-directory)))
      (bootstrap-version 7))
  (unless (file-exists-p bootstrap-file)
    (with-current-buffer
        (url-retrieve-synchronously
         "https://raw.githubusercontent.com/radian-software/straight.el/develop/install.el"
         'silent 'inhibit-cookies)
      (goto-char (point-max))
      (eval-print-last-sexp)))
  (load bootstrap-file nil 'nomessage))


;;;; Use-package integration
(straight-use-package 'use-package)

(use-package use-package
  :config
  (setq use-package-always-defer t)
  ;; Enables one to run M-x `use-package-report' to check Initialized/Declared/Configured packages
  ;; -  https://github.com/jwiegley/use-package#gathering-statistics
  (setq use-package-compute-statistics t))


(use-package straight
  :config
  (setq straight-use-package-by-default t)
  (setq straight-host-usernames
        '((github . "gmlarumbe"))))


(use-package straight-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/straight-utils.el")))


;; INFO: Place here temporarily to make sure that it shadows Emacs 30.1 bundled transient
(use-package transient
  :straight (:host github :repo "magit/transient"))



(provide 'init-straight)

;;; init-straight.el ends here
