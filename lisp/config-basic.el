;;; config-basic.el --- Basic configuration  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Basics
(if (and (fboundp 'server-running-p)           ; Server start for emacsclient support
         (not (server-running-p)))
    (server-start))
(setq custom-file "~/.emacs.d/custom-file.el") ; Custom file does not need to be in version control.
(unless (file-exists-p custom-file)            ; It will only hold a list with safe variables, `package-selected-packages' for autoremove and custom set variables.
  (write-region "" nil custom-file))           ; All of these are actually local to a machine.
(load custom-file)                             ; Create file if it doesn't exist in emacs directory, and load it
(load-theme 'deeper-blue t)                    ; Load theme
(desktop-save-mode 1)                          ; Autosave Desktop
(setq confirm-kill-emacs #'y-or-n-p)           ; Avoid closing Emacs unexpectedly (helm prefix C-x c)
(setq inhibit-startup-screen t)                ; Inhibit startup screen
(setq disabled-command-function 'ignore)       ; Enable all commands
(defalias 'yes-or-no-p 'y-or-n-p)              ; Globally set y-or-n-p


;;;; Window/Frame Display
(menu-bar-mode -1)
(when (featurep 'tool-bar)
  (tool-bar-mode -1))
(when (featurep 'scroll-bar)
  (scroll-bar-mode -1))


(use-package window
  :ensure nil
  :bind (("M-o" . other-window))) ; Replaces enriched faces


(use-package frame
  :ensure nil
  :bind (("M-O" . other-frame))) ; Replaces 'negative argument


(use-package minibuffer
  :ensure nil
  :bind ("<C-return>" . completion-at-point))


(use-package smart-mode-line
  :demand
  :config
  (setq sml/theme 'dark) ; Other choices would be 'light or 'respectful. By default, sml will try to figure out the best sml theme to go with your Emacs theme.
  (sml/setup)            ; Enable smart-mode-line
  (which-function-mode)
  (set-face-attribute 'which-func nil :foreground "green")
  (setq line-number-mode nil) ; Hide current line number from mode-line
  (setq display-time-default-load-average nil) ; Display time on the status bar
  (display-time-mode t))


(use-package popwin
  :config
  (popwin-mode 1))


(use-package buffer-move
  :bind (("<C-S-up>"    . buf-move-up)
         ("<C-S-down>"  . buf-move-down)
         ("<C-S-left>"  . buf-move-left)
         ("<C-S-right>" . buf-move-right)))



;;;; Navigation
(use-package isearch
  :ensure nil
  :bind (:map isearch-mode-map
              ("C-w" . my-isearch-yank-word-or-char-from-beginning)) ; Override `isearch-yank-word-or-char'
  :config
  ;; https://www.emacswiki.org/emacs/SearchAtPoint
  (defun my-isearch-yank-word-or-char-from-beginning ()
    "Move to beginning of word before yanking word in `isearch-mode'.
Make \\keymapC-s C-w and C-r C-w act like Vim's g* and g#, keeping Emacs'
C-s C-w [C-w] [C-w]... behaviour. "
    (interactive)
    ;; Making this work after a search string is entered by user
    ;; is too hard to do, so work only when search string is empty.
    (if (= 0 (length isearch-string))
        (beginning-of-thing 'word))
    (isearch-yank-word-or-char)))


(use-package view
  :ensure nil
  :diminish
  :bind (:map view-mode-map
              ("n"   . next-line)
              ("p"   . previous-line)
              ("f"   . forward-char)
              ("b"   . backward-char)
              ("C-j" . scroll-up-command)
              ("C-k" . scroll-down-command)
              ("j"   . View-scroll-line-forward)
              ("k"   . View-scroll-line-backward)
              ("l"   . recenter-top-bottom))
  :bind (("C-x C-q" . view-mode))
  :config
  (setq view-read-only t))


(use-package outshine
  :config
  ;; Do not include outshine tags at imenu
  (setq outshine-imenu-show-headlines-p nil))


(use-package ido
  :config
  (setq ido-everywhere nil)
  (setq ido-default-buffer-method "selected-window"))


(use-package winner
  :ensure nil
  :config
  (winner-mode 1))


(use-package beacon
  :demand
  :config
  (beacon-mode 1))


(use-package sr-speedbar
  :bind (:map speedbar-mode-map
              ("q"   . larumbe/kill-current-buffer)
              ("j"   . speedbar-edit-line))
  :config
  (setq speedbar-show-unknown-files t)
  (setq speedbar-use-images nil)
  (setq sr-speedbar-right-side t))


(use-package google-this
  :diminish
  :commands (google-this-line           ; TODO: They are marked as autoloads
             google-this-error          ; Might it be necessary to recompile the package?
             google-this-symbol
             google-this-word)
  :config
  (google-this-mode 1))


;; TODO: GitHub CI error regarding helm installation
;; Window too small for splitting
;; (use-package pdf-tools
;;   :bind (:map pdf-view-mode-map
;;               ("j"   . pdf-view-next-line-or-next-page)
;;               ("k"   . pdf-view-previous-line-or-previous-page)
;;               ("M-w" . pdf-view-kill-ring-save))
;;   :config
;;   (pdf-loader-install t))
;; End of TODO


;;;; Editing
(use-package move-lines
  :bind (("<C-M-up>"   . move-lines-up)
         ("<C-M-down>" . move-lines-down))
  :ensure nil)


(use-package untabify-trailing-ws
  :ensure nil
  :demand ; INFO: Assumes it's being enabled at startup!
  :config
  (untabify-trailing-ws 1))


(use-package align
  :ensure nil
  :config
  (setq align-default-spacing 1)
  (setq align-to-tab-stop nil))


(use-package elec-pair
  :ensure nil
  :config
  (electric-pair-mode 1))


(use-package whole-line-or-region
  :bind (("C-w" . whole-line-or-region-kill-region)))



;;;; Misc
(use-package simple
  :ensure nil
  :bind (("M-n"     . next-error)     ; M-n and M-p are already overwritten at mode-line.el.
         ("M-p"     . previous-error) ; This mapping allows to step through errors in a non-compilation buffer
         ("C-<f12>" . auto-fill-mode)
         ("<f12>"   . toggle-truncate-lines)))


(use-package tramp
  :config
  (setq tramp-own-remote-path nil) ; `tramp-remote-path': List of directories to search for executables on remote host.
  (add-to-list 'tramp-remote-path 'tramp-own-remote-path))


(use-package hi-lock
  :ensure nil
  :bind (("C-\\" . highlight-symbol-at-point)
         ("C-'"  . unhighlight-regexp)))


(use-package re-builder
  :config
  (setq reb-re-syntax 'read))  ;; Emacs double escaping (for single escaping use 'string)


(use-package man
  :ensure nil
  :config
  (setq Man-notify-method 'pushy))


(use-package which-key
  :config
  (which-key-mode 1))


(use-package browse-url
  :ensure nil
  :config
  (setq browse-url-browser-function 'browse-url-firefox))


(use-package jpeg-mode
  :ensure nil)


;; (use-package so-long
;;   :diminish
;;   :quelpa (so-long :url "https://raw.githubusercontent.com/emacs-mirror/emacs/master/lisp/so-long.el" :fetcher url)
;;   :config
;;   (require 'quelpa-use-package)
;;   (global-so-long-mode 1))


(use-package jenkins
  :bind (:map jenkins-job-view-mode-map
              ("n" . next-line)
              ("p" . previous-line)))


(use-package unison-mode
  ;; There are 2 packages, unison and unison-mode.
  ;; The first one for process invocation
  ;; The second one for syntax highlighting and process invocation -> Using this
  :bind (:map unison-mode-map
              ("C-c C-c" . unison-my-run))
  :mode (("\\.prf\\'" . unison-mode))
  :hook ((unison-mode . unison-sync-minor-mode))
  :config
  (use-package unison-sync-minor-mode
    :ensure nil))


(use-package btc-ticker)




(provide 'config-basic)

;;; config-basic.el ends here