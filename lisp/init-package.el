;;; init-package.el --- Package Init settings  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:



;;; Code:

;;;; Straight bootstrap
(defvar bootstrap-version)
(let ((bootstrap-file
       (expand-file-name "straight/repos/straight.el/bootstrap.el" user-emacs-directory))
      (bootstrap-version 5))
  (unless (file-exists-p bootstrap-file)
    (with-current-buffer
        (url-retrieve-synchronously
         "https://raw.githubusercontent.com/raxod502/straight.el/develop/install.el"
         'silent 'inhibit-cookies)
      (goto-char (point-max))
      (eval-print-last-sexp)))
  (load bootstrap-file nil 'nomessage))

;;;; Use-package integration
(straight-use-package 'use-package)
(use-package straight
  :config
  (setq straight-use-package-by-default t)
  (setq straight-host-usernames
        '((github . "gmlarumbe"))))

(use-package use-package-chords :demand) ; Allow for :chords keyword with `use-package' (only to global keymap)


(provide 'init-package)

;;; init-package.el ends here
