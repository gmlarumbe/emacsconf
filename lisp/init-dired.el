;;; init-dired.el --- Dired  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package dired
  :ensure nil
  :bind (:map dired-mode-map
              ("J" . dired-goto-file)                                ; Switch from 'j' to 'J'
              ("j" . larumbe/dired-do-async-shell-command-or-okular) ; Open file-at-point directly with Okular if is a PDF and delete async process window. Otherwise it will ask for default program
              ("," . larumbe/dired-toggle-deletion-confirmer)        ; https://superuser.com/questions/332590/how-to-prevent-delete-confirmation-in-emacs-dired
              ("b" . dired-up-directory))
  :bind (("C-x C-j" . dired-jump))
  :hook ((dired-mode . my-dired-hook))
  :commands (dired-do-async-shell-command dired-hide-details-mode)
  :config
  (defun larumbe/dired-toggle-deletion-confirmer ()
    "Toggles deletion confirmer for dired from (y-or-n) to nil and viceversa."
    (interactive)
    (if (equal dired-deletion-confirmer 'yes-or-no-p)
        (progn
          (setq dired-deletion-confirmer '(lambda (x) t))
          (message "Dired deletion confirmation: FALSE"))
      (progn
        (setq dired-deletion-confirmer 'yes-or-no-p)
        (message "Dired deletion confirmation: TRUE"))))


  (defun larumbe/dired-do-async-shell-command-or-okular ()
    "Same as `dired-do-async-shell-command' but if on a PDF will open Okular directly."
    (interactive)
    (when (not (string-equal major-mode "dired-mode"))
      (error "Needs to be executed in dired...! "))
    (let ((program "okular")
          (filename (thing-at-point 'filename t)))
      (if (string-equal (file-name-extension filename) "pdf")
          (progn
            (dired-do-async-shell-command program filename (list filename))
            (delete-window (get-buffer-window "*Async Shell Command*")))
        (call-interactively #'dired-do-async-shell-command))))


  (defun my-dired-hook ()
    (dired-hide-details-mode 1)))


(use-package dired-x
  :ensure nil
  :bind (:map dired-mode-map
              ("I" . dired-kill-subdir)) ; Replaces `dired-info' when dired-x is enabled
  :config
  (setq dired-guess-shell-alist-user ; Program mappings to dired-do-shell-command (precedence over `dired-guess-shell-alist-default')
        '(("\\.pdf\\'"  "okular")
          ("\\.lxt2\\'" "gtkwave")))
  (setq dired-bind-info nil))


(use-package dired-quick-sort
  :config
  (dired-quick-sort-setup)) ; This will bind the key S in `dired-mode' to run `hydra-dired-quick-sort/body', and automatically run the sorting criteria after entering `dired-mode'.


(use-package dired-narrow
  :bind (:map dired-mode-map
              ("/" . dired-narrow-regexp)))





(provide 'init-dired)

;;; init-dired.el ends here
