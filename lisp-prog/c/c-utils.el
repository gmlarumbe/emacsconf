;;; c-utils.el --- C/C++ Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(defvar larumbe/semantic-enable t
  "Conditionally determine in a hook if mode is enabled.")

(defun my-cc-mode-hook ()
  "C/C++ hook."
  (set 'ac-sources '(ac-source-semantic-raw ac-source-gtags)))


(defun larumbe/semantic-mode (&optional arg)
  "Enable semantic depending on value of `larumbe/semantic-enable'.

Purpose is to use this function as a conditional hook.
ARG will be passed to wrapped function `semantic-mode'."
  (interactive)
  (if larumbe/semantic-enable
      (semantic-mode arg)
    (semantic-mode -1)))


(provide 'c-utils)

;;; c-utils.el ends here
