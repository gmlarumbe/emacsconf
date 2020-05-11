;;;;;;;;;;;
;; Dired ;;
;;;;;;;;;;;

(use-package dired
  :ensure nil
  :bind (:map dired-mode-map
              ("b" . dired-up-directory)
              ("J" . dired-goto-file)                             ; Switch from 'j' to 'J'
              ("j" . larumbe/dired-do-async-shell-command-okular) ; Open file-at-point directly with Okular if is a PDF and delete async process window. Otherwise it will ask for default program
              ("," . larumbe/dired-toggle-deletion-confirmer)     ; https://superuser.com/questions/332590/how-to-prevent-delete-confirmation-in-emacs-dired
              )
  :hook ((dired-mode . my-dired-hook))
  :config
  (defun my-dired-hook ()
    (dired-hide-details-mode 1)))


(use-package dired-x
  :ensure nil
  :bind (:map dired-mode-map
              ("I" . dired-kill-subdir)) ; Replaces `dired-info' when dired-x is enabled
  :config
  (setq dired-guess-shell-alist-user ; Program mappings to dired-do-shell-command (overrides `dired-guess-shell-alist-default')
        '(
          ("\\.pdf\\'" "okular")
          ))
  (setq dired-bind-info nil))


(use-package dired-quick-sort
  :config
  (dired-quick-sort-setup)) ; This will bind the key S in `dired-mode' to run `hydra-dired-quick-sort/body', and automatically run the sorting criteria after entering `dired-mode'.


(use-package dired-narrow
  :bind (:map dired-mode-map
              ("/" . dired-narrow-regexp)))



(defun larumbe/dired-toggle-deletion-confirmer ()
  "Toggles deletion confirmer for dired from (y-or-n) to nil and viceversa"
  (interactive)
  (if (equal dired-deletion-confirmer 'yes-or-no-p)
      (progn
        (setq dired-deletion-confirmer '(lambda (x) t))
        (message "Dired deletion confirmation: FALSE"))
    (progn
      (setq dired-deletion-confirmer 'yes-or-no-p)
      (message "Dired deletion confirmation: TRUE"))))


(defun larumbe/dired-do-async-shell-command-okular ()
  "Same as `dired-do-async-shell-command' but if on a PDF will open Okular directly"
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



