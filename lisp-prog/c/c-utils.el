;;; c-utils.el --- C/C++ Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Hook
(defun larumbe/c-and-c++-mode-hook ()
  "Custom C/C++ hook."
  (hide-ifdef-mode 1)
  (c-toggle-comment-style -1)) ; Default to line-style comment instead of block-style


;;;; Gtags
(defun larumbe/ggtags-create-c-tags-recursive ()
  "Create global GTAGS of every C file in the directory."
  (interactive)
  (let ((c-file-re "\\.[ch]\\\(pp\\)?$"))
    (larumbe/gtags-filelist-create c-file-re)
    (larumbe/gtags-create-tags-async default-directory)))



(provide 'c-utils)

;;; c-utils.el ends here
