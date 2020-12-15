;;; init-load-path-header.el --- Load-path Header  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Load path
;; Order of packages within `load-path' actually matters.
;; If there is one package present in more than one directory of `load-path',
;; only the first in the list will be used to load the package.

;; Since `normal-top-level-add-subdirs-to-load-path' will add subdirectories at
;; the end of `load-path', MELPA packages loaded with `use-package' will take
;; precedence. As I would like to have many MELPA packages coexisting with my
;; own overriden packages, I prefer to use a custom approach using shell commands.

(defun larumbe/add-to-load-path (dir-list &optional recursive)
  "Add directories in DIR-LIST to the front of `load-path'.
Add subdirectories if RECURSIVE is non-nil."
  (dolist (dir dir-list)
    (if recursive
        (dolist (subdir (split-string (shell-command-to-string (concat "find " dir " -type d"))))
          (add-to-list 'load-path (expand-file-name subdir)))
      (dolist (dir dir-list)
        (add-to-list 'load-path (expand-file-name dir))))))


(defvar larumbe/load-path-dirs-recursive '("~/.elisp/lisp"
                                           "~/.elisp/lisp-prog"
                                           "~/.elisp/own-modes"))


(larumbe/add-to-load-path larumbe/load-path-dirs-recursive t)


(provide 'init-load-path-header)

;;; init-load-path-header.el ends here
