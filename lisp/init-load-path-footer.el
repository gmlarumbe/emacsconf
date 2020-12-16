;;; init-load-path-footer.el --- Load-path footer  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'init-load-path-header)


;;;; Load path overriding
;; If a MELPA package has to be overriden, copy the new version (or symlink) to
;; the 'modified' or 'site-lisp' directories.
;; When loading with `use-package', some mechanism is needed to defer it and
;; load it after `load-path' has been updated (such as :bind, :defer, :hook...)
(defvar larumbe/load-path-dirs-non-recursive '("~/.elisp/snippets"
                                               "~/.elisp/site-lisp"
                                               "~/.elisp/modified"))
(larumbe/add-to-load-path larumbe/load-path-dirs-non-recursive)



;;;; Machine-specific
;;   - This file will not be present in the repo
;;   - It will have specific machine content (e.g. EXWM enabling)
(when (file-exists-p "~/.elisp_private/")
  (defvar larumbe/load-path-dirs-private-recursive '("~/.elisp_private/lisp"
                                                     "~/.elisp_private/site-lisp"))
  (larumbe/add-to-load-path larumbe/load-path-dirs-private-recursive t)
  (require 'init-private))


(provide 'init-load-path-footer)

;;; init-load-path-footer.el ends here
