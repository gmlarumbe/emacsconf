;;; c-utils.el --- C/C++ Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(defun my-cc-mode-hook ()
  "C/C++ hook."
  (set 'ac-sources '(ac-source-semantic-raw ac-source-gtags)))



(provide 'c-utils)

;;; c-utils.el ends here
