;;; untabify-trailing-ws.el --- Untabify/Trailing WS  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;; Description
;; Basic Larumbe's minor mode to untabify and delete trailing whitespaces in buffers (except for Makefiles).
;; This seems to be an obsolete method and there are very good alternatives out there, but it still works, so that's why I keep it.
;; For more info on alternatives, check the followings:
;;; Related modes
;; ethan-wspace: cleans only if file is not full of whitespaces to avoid `diff' issues in large projects
;;   https://github.com/glasserc/ethan-wspace
;; ws-trimm
;; ws-butler
;; etc...

;;; Variables
(defvar untabify-delete-trailing-whitespace t) ; Default initial value


;;; Functions
(define-minor-mode untabify-trailing-ws
  "Basic minor mode to untabify and delete trailing whitespaces by using write-file-functions hooks."
  :global t
  (if untabify-trailing-ws
      (progn   ;; Enable
        (setq untabify-delete-trailing-whitespace t)
        (add-hook 'write-file-functions #'larumbe/untabify-trailing-whitespace)
        (message "Untabify set to: %s" untabify-delete-trailing-whitespace))
    ;; Disable
    (setq untabify-delete-trailing-whitespace nil)
    (remove-hook 'write-file-functions #'larumbe/untabify-trailing-whitespace)
    (message "Untabify set to: %s" untabify-delete-trailing-whitespace)))


(defun larumbe/untabify-trailing-whitespace ()
  "Untabify and delete trailing whitespace depending on MAJOR-MODE of current buffer.
Meant to be used as a wrapper for write-file-functions hook."
  (interactive)
  (unless (string-match "makefile-" (format "%s" major-mode)) ; Do not untabify `makefile-mode'
    (untabify (point-min) (point-max))
    (delete-trailing-whitespace (point-min) (point-max))))


(defun larumbe/untabify-trailing-whitespace-toggle ()
  "GLOBALLY Toggle untabify and delete trailing whitespace for some customized programming modes."
  (interactive)
  (if untabify-delete-trailing-whitespace
      (progn ;; Disable
        (setq untabify-delete-trailing-whitespace nil)
        (remove-hook 'write-file-functions #'larumbe/untabify-trailing-whitespace)
        (message "Untabify set to: %s" untabify-delete-trailing-whitespace))
    ;; Enable
    (setq untabify-delete-trailing-whitespace t)
    (add-hook 'write-file-functions #'larumbe/untabify-trailing-whitespace)
    (message "Untabify set to: %s" untabify-delete-trailing-whitespace)))


;;; Provide
(provide 'untabify-trailing-ws)

;;; untabify-trailing-ws.el ends here
