;;; init-eaf.el --- Emacs Application Framework  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;
;;; Code:

(use-package eaf)

(use-package eaf
 :straight (:host github :repo "emacs-eaf/emacs-application-framework"
            :files ("*" (:exclude ".git" ".github" ".gitignore" "LICENSE" "img" "*.md" "*png")))
 :config
 (eaf-install-and-update)
 (eaf-add-subdirs-to-load-path eaf-build-dir)
 (require 'eaf-git)
 )


(provide 'init-eaf)

;;; init-eaf.el ends here
