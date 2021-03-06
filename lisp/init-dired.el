;;; init-dired.el --- Dired  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;; Code:



(use-package dired
  :ensure nil
  :bind (:map dired-mode-map
         ("C-x C-j" . larumbe/dired-jump)
         ("b"       . dired-up-directory)
         ("l"       . recenter-top-bottom)
         ("J"       . dired-goto-file)                                ; Switch from 'j' to 'J'
         ("j"       . larumbe/dired-do-async-shell-command-or-okular) ; Open file-at-point directly with Okular if is a PDF and delete async process window. Otherwise it will ask for default program
         (","       . larumbe/dired-toggle-deletion-confirmer)        ; https://superuser.com/questions/332590/how-to-prevent-delete-confirmation-in-emacs-dired
         ("I"       . dired-kill-subdir))                             ; Replaces `dired-info', requires `dired-aux', mapping in dired-aux use-package didn't work
  :bind (("C-x C-j" . larumbe/dired-jump))
  :hook ((dired-mode . larumbe/dired-hook))
  :commands (dired-do-async-shell-command dired-hide-details-mode)
  :config
  ;; +--------------------+
  ;; | Bundled with Emacs |
  ;; +--------------------+
  ;;
  ;; less commonly used parts of dired (autoloads for native dired functions)
  (use-package dired-aux
    :ensure nil)

  ;; extra Dired functionality
  (use-package dired-x
    :ensure nil
    :demand
    :diminish dired-omit-mode
    :hook ((dired-mode . dired-omit-mode)) ; hide backup, autosave, *.*~ files
    :init
    (setq dired-bind-jump nil) ; Prevents overriding of `larumbe/dired-jump' for C-x C-j keybinding
    :config
    (setq dired-omit-verbose nil)
    (delete ".bin" dired-omit-extensions)
    (setq dired-guess-shell-alist-user ; Program mappings to dired-do-shell-command (precedence over `dired-guess-shell-alist-default')
          '(("\\.pdf\\'"  "okular")
            ("\\.lxt2\\'" "gtkwave")))
    (setq dired-bind-info nil))


  ;; EmacsWiki: `dired+'
  ;; INFO: Not enabled since it maps important keys to this non-required functionality
  ;; Package `dired+' added lots of extra functionality in a very large package.
  ;; Not available in MELPA due to security reasons for some years.


  ;; +-------+
  ;; | MELPA |
  ;; +-------+
  ;;
  ;; Fontifying
  ;; Also tried `dired-rainbow' package, but it was targeted to fontifying files based on extensions.
  ;; There were too many colors (and it also highlighted the extensions), and approach of <kbd '/'>
  ;; for `dired-narrow-regexp' or <kbd 'S'> for `hydra-dired-quick-sort/body' seemed easier.
  (use-package diredfl
    :demand
    :hook (dired-mode . diredfl-mode)
    :config
    (defface larumbe/diredfl-file-name              '((t (:inherit default)))                      "Face" :group 'diredfl)
    (defface larumbe/diredfl-symlink                '((t (:inherit dired-symlink)))                "Face" :group 'diredfl)
    (defface larumbe/diredfl-dir-name               '((t (:inherit dired-directory)))              "Face" :group 'diredfl)
    (defface larumbe/diredfl-file-suffix            '((t (:foreground "navajo white")))            "Face" :group 'diredfl)
    (defface larumbe/diredfl-compressed-file-suffix '((t (:foreground "steel blue")))              "Face" :group 'diredfl)
    (defface larumbe/diredfl-flag-mark-line         '((t (:background "dark blue")))               "Face" :group 'diredfl)
    (defface larumbe/diredfl-exec-priv              '((t (:background "medium blue")))             "Face" :group 'diredfl)
    (defface larumbe/diredfl-dir-priv               '((t (:inherit dired-directory :weight bold))) "Face" :group 'diredfl)

    (setq diredfl-file-name              'larumbe/diredfl-file-name)
    (setq diredfl-symlink                'larumbe/diredfl-symlink)
    (setq diredfl-dir-name               'larumbe/diredfl-dir-name)
    (setq diredfl-file-suffix            'larumbe/diredfl-file-suffix)
    (setq diredfl-compressed-file-suffix 'larumbe/diredfl-compressed-file-suffix)
    (setq diredfl-flag-mark-line         'larumbe/diredfl-flag-mark-line)
    (setq diredfl-exec-priv              'larumbe/diredfl-exec-priv)
    (setq diredfl-dir-priv               'larumbe/diredfl-dir-priv))



  (use-package dired-quick-sort
    :demand
    :config
    (dired-quick-sort-setup)) ; This will bind the key S in `dired-mode' to run `hydra-dired-quick-sort/body', and automatically run the sorting criteria after entering `dired-mode'.


  ;; Fuco1 `dired-hacks' extensions
  ;; https://github.com/Fuco1/dired-hacks
  (use-package dired-narrow
    :bind (:map dired-mode-map
           ("/" . dired-narrow-regexp)))


  (use-package dired-collapse
    :demand
    :bind (:map dired-mode-map
           (";" . dired-collapse-mode)))


  ;; Run asynchronously dired commands for copying, renaming and symlinking (through async library)
  ;; To cancel a copy call `dired-async-kill-process'
  (dired-async-mode 1)


  ;; Functionality
  (defun larumbe/dired-jump (arg)
    "Execute `dired-jump'.
With universal ARG, delete every dired-mode buffer to have only 1 dired buffer.
Provides a more convenient solution to cluttering dired buffers than `dired-single'."
    (interactive "P")
    (when arg
      (dolist ($buf (buffer-list (current-buffer)))
        (with-current-buffer $buf
          (when (string= major-mode "dired-mode")
            (kill-buffer $buf)))))
    (dired-jump))


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


  (defun larumbe/dired-hook ()
    (dired-hide-details-mode 1)))



(provide 'init-dired)

;;; init-dired.el ends here
