;;; early-init.el --- Early Init  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Find directories recursively
;; Since `normal-top-level-add-subdirs-to-load-path' will add subdirectories at
;; the end of `load-path', packages loaded with `use-package' will take precedence.
;; That was an issue when I had many MELPA packages coexisting with some overriden packages.
;; By using straight, I only have one version of each package in the load-path, avoiding conflicts.
(defun larumbe/find-subdirectories-recursive (&optional dir)
  "Find subdirectories of DIR recursively, including DIR'.
If no argument is specified, find subdirectories of `default-directory'.

This function purpose is portability for Windows systems.
For Linux, the use of ' $ find DIR -type d ' was sufficient."
  (let (subdirs-and-files
        subdirs)
    (unless dir
      (setq dir default-directory))
    (setq subdirs-and-files (directory-files-recursively (expand-file-name dir) "" t))
    ;; Filter files to return only directories...
    (require 'seq)
    (setq subdirs (seq-remove
                   (lambda (x) (not (file-directory-p x)))
                   subdirs-and-files))
    ;; ...and include top directory.
    (push (expand-file-name dir) subdirs)))


;;;; Load-path
;; Order of packages within `load-path' actually matters.
;; If there is one package present in more than one directory of `load-path',
;; only the first in the list will be used to load the package.
(defun larumbe/add-to-load-path (dir-list &optional recursive)
  "Add directories in DIR-LIST to the front of `load-path'.
Add subdirectories if RECURSIVE is non-nil."
  (dolist (dir dir-list)
    (if recursive
        (dolist (subdir (larumbe/find-subdirectories-recursive dir))
          (add-to-list 'load-path (expand-file-name subdir)))
      (dolist (dir dir-list)
        (add-to-list 'load-path (expand-file-name dir))))))


(defvar larumbe/load-path-dirs '("~/.elisp/lisp"
                                 "~/.elisp/lisp-prog"
                                 "~/.elisp/site-lisp"
                                 "~/.elisp/own-modes"))
(larumbe/add-to-load-path larumbe/load-path-dirs t) ; Add recursively



;;;; Straight
(setq package-enable-at-startup nil) ;; Disable package.el in favor of straight.el


;;; early-init.el ends here
