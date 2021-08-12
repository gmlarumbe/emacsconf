;;; c-utils.el --- C/C++ Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Hook
(defun larumbe/c-or-c++-mode-hook ()
  "Custom C/C++ hook."
  (hide-ifdef-mode 1))


;;;; Gtags
(defun larumbe/gtags-c-files-pwd-recursive ()
  "Generate gtags.files for C files on current directory (.c .h and .cpp extensions)."
  (interactive)
  (larumbe/directory-files-recursively-to-file default-directory "gtags.files" "\\.[ch]\\\(pp\\)?$"))


(defun larumbe/ggtags-create-c-tags-recursive ()
  "Create global GTAGS of every C file in the directory."
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-c-files-pwd-recursive)
  (ggtags-create-tags default-directory))


(provide 'c-utils)

;;; c-utils.el ends here
