;;; c-utils.el --- C/C++ Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Hook
(defun larumbe/c-and-c++-mode-hook ()
  "Custom C/C++ hook."
  (hide-ifdef-mode 1)
  (c-toggle-comment-style -1)) ; Default to line-style comment instead of block-style


(provide 'c-utils)

;;; c-utils.el ends here
