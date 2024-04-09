;;; init-js.el --- JavaScript init  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; JavaScript
(use-package js
  :straight nil
  :mode (("\\.js\\'" . js-ts-mode))
  :config
  (require 'js-ts-font-lock)
  (defun larumbe/js-hook ()
    "Prevent cursor in `js-mode' (not `js-ts-mode'!!) from moving to the beginning of indentation with C-p/C-n."
    (interactive)
    (setq-local goal-column nil)))


(provide 'init-js)

;;; init-js.el ends here
