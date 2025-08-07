;;; init-dired.el --- Dired  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package dired
  :straight nil
  :bind (:map dired-mode-map
         ("C-j"     . dired-find-file)
         ("b"       . dired-up-directory)
         ("l"       . recenter-top-bottom)
         ("y"       . dired-do-symlink)                               ; Replaces `dired-show-file-type'
         ("J"       . dired-goto-file)                                ; Switch from 'j' to 'J'
         ("C-x C-q" . wdired-change-to-wdired-mode))                  ; Previously overriden by EXWM global keybinding
  :hook ((dired-mode . larumbe/dired-hook))
  :commands (dired-hide-details-mode)
  :init
  (setq dired-listing-switches "-alh") ; Show size in human readable format
  :config
  (defun larumbe/dired-hook ()
    (dired-hide-details-mode 1)
    (setq truncate-lines t)))


(use-package dired-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/dired-utils.el"))
  :after dired
  :demand
  :bind (:map dired-mode-map
         ("C-x C-l" . previous-buffer)                                ; Complementary to `larumbe/dired-jump'
         ("C-x C-j" . larumbe/dired-jump)                             ; Bind keybinding locally
         ("j"       . larumbe/dired-do-async-shell-command-or-okular) ; Open file-at-point directly with Okular if is a PDF and delete async process window. Otherwise it will ask for default program
         (","       . larumbe/dired-toggle-deletion-confirmer)        ; https://superuser.com/questions/332590/how-to-prevent-delete-confirmation-in-emacs-dired
         ("a"       . larumbe/dired-async-toggle))                    ; Replaces `dired-find-alternate-file', never used it though...
  :bind (("C-x C-j" . larumbe/dired-jump)))                           ; Bind keybinding globally


;; +--------------------+
;; | Bundled with Emacs |
;; +--------------------+
;;
;; less commonly used parts of dired (autoloads for native dired functions)
(use-package dired-aux
  :straight nil
  :after dired
  :demand
  :bind (:map dired-mode-map
         ("I" . dired-kill-subdir))) ; Replaces `dired-info', requires `dired-aux', mapping in dired-aux use-package didn't work


;; X-tra Dired functionality
(use-package dired-x
  :straight nil
  :demand
  :after dired
  :diminish dired-omit-mode
  :hook ((dired-mode . dired-omit-mode)) ; hide backup, autosave, *.*~ files
  :init
  (setq dired-bind-jump nil) ; Prevent overriding of `larumbe/dired-jump' for C-x C-j keybinding
  (setq dired-bind-info nil) ; Prevent overriding of `dired-kill-subdir'
  (setq dired-omit-verbose nil)
  (setq dired-guess-shell-alist-user ; Program mappings to dired-do-shell-command (precedence over `dired-guess-shell-alist-default')
        '(("\\.pdf\\'"  "okular")
          ("\\.lxt2\\'" "gtkwave")))
  :config
  (delete ".bin" dired-omit-extensions)
  (delete ".so"  dired-omit-extensions)
  (delete ".mem"  dired-omit-extensions))


;; EmacsWiki: `dired+'
;; INFO: Not enabled since it maps important keys to this non-required functionality
;; Package `dired+' added lots of extra functionality in a very large package.
;; Available in EmacsWiki.org but not in MELPA due to security reasons for some years.


;; +-------+
;; | MELPA |
;; +-------+
;;
;; Fontifying
;; Also tried `dired-rainbow' package, but it was targeted to fontifying files based on extensions.
;; There were too many colors (and it also highlighted the extensions), and approach of <kbd '/'>
;; for `dired-narrow-regexp' or <kbd 'S'> for `hydra-dired-quick-sort/body' seemed easier.
(use-package diredfl
  :after dired
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
  :after dired
  :demand
  :config
  (dired-quick-sort-setup)) ; This will bind the key S in `dired-mode' to run `hydra-dired-quick-sort/body', and automatically run the sorting criteria after entering `dired-mode'.


;; Fuco1 `dired-hacks' extensions
;; https://github.com/Fuco1/dired-hacks
(use-package dired-narrow
  :after dired
  :bind (:map dired-mode-map
         ("." . dired-narrow-regexp))) ; Unmaps `dired-clean-directory'

(use-package dired-collapse
  :after dired
  :bind (:map dired-mode-map
         (";" . dired-collapse-mode)))

;; INFO: `dired-filter-mode' is autoloaded, and sets "/" as a prefix key
;; Setting "/" to `dired-filter-mode' allows enabling of this minor-mode with "/" and overriding
;; with its common functions. To deactivate it but saving status, press "/" twice.
(use-package dired-filter
  :after dired
  :bind (:map dired-mode-map
         ("/" . dired-filter-mode)))



(provide 'init-dired)

;;; init-dired.el ends here
