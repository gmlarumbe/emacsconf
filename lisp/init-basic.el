;;; init-basic.el --- Basic configuration  -*- lexical-binding: t -*-
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


(use-package minibuffer
  :straight nil
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


(use-package diminish)


(use-package ibuffer
  :bind (("C-x C-b" . ibuffer))
  :config
  (setq ibuffer-default-sorting-mode 'major-mode)
  (setq ibuffer-expert t))


(use-package ibuffer-projectile
  :hook ((ibuffer . modi/ibuffer-customization))
  :config
  (defun modi/ibuffer-customization ()
    "My customization for `ibuffer'."
    ;; ibuffer-projectile setup
    (ibuffer-projectile-set-filter-groups)
    (unless (eq ibuffer-sorting-mode 'alphabetic)
      (ibuffer-do-sort-by-alphabetic) ; first do alphabetic sort
      (ibuffer-do-sort-by-major-mode))))


(use-package ibuf-ext
  :straight nil
  :config
  (setq ibuffer-show-empty-filter-groups nil))


(use-package indent-guide
  :bind (("C-<f10>" . indent-guide-global-mode)))


;;;; Navigation
(use-package isearch
  :straight nil
  :bind (:map isearch-mode-map
         ("C-w" . my-isearch-yank-word-or-char-from-beginning) ; Override `isearch-yank-word-or-char'
         ("C-j" . isearch-exit)) ; Overrides `isearch-printing-char' to search for newlines
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
    ;; DANGER: At some point in Emacs it required a '1' argument to fix a "Wrong type argument: number-or-marker-p, nil" error
    (isearch-yank-word-or-char 1)))


(use-package view
  :straight nil
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


(use-package navi-mode)


(use-package ido
  :config
  (setq ido-everywhere nil)
  (setq ido-default-buffer-method "selected-window"))


(use-package winner
  :straight nil
  :demand
  :config
  (winner-mode 1))


(use-package beacon
  :demand
  :diminish
  :config
  (setq beacon-size 20)
  (add-to-list 'beacon-dont-blink-major-modes 'term-mode)
  (beacon-mode 1))


(use-package sr-speedbar
  ;; Default would be fetched from emacsorphanage
  :straight (:host github :repo "emacsmirror/emacswiki.org" :branch "master" :files ("sr-speedbar.el"))
  :bind (:map speedbar-mode-map
              ("q"   . larumbe/kill-current-buffer)
              ("j"   . speedbar-edit-line))
  :config
  (setq speedbar-show-unknown-files t)
  (setq speedbar-use-images nil)
  (setq sr-speedbar-right-side t))


(use-package google-this
  :diminish
  :demand
  :config
  (google-this-mode 1))


(use-package howdoi
  :straight (:host github :repo "arthurnn/howdoi-emacs"))


(use-package bind-chord)


(use-package hardcore-mode
  :demand
  :diminish hardcore-mode
  :init
  (setq too-hardcore-backspace t)
  (setq too-hardcore-return    t)
  :config
  (global-hardcore-mode 1))



;;;; Editing

(use-package drag-stuff
  :bind (("<C-M-up>"   . drag-stuff-up)
         ("<C-M-down>" . drag-stuff-down))
  :hook ((drag-stuff-before-drag . modi/drag-stuff--adj-pt-pre-drag)
         (drag-stuff-after-drag  . modi/drag-stuff--rst-pt-post-drag))
  :config
  ;; kmodi hack to avoid dragging line of where currently point is
  ;; https://emacs.stackexchange.com/questions/13941/move-selected-lines-up-and-down
  (defvar modi/drag-stuff--point-adjusted nil)
  (defvar modi/drag-stuff--point-mark-exchanged nil)

  (defun modi/drag-stuff--adj-pt-pre-drag ()
    "If a region is selected AND the `point' is in the first column, move
back the point by one char so that it ends up on the previous line. If the
point is above the mark, exchange the point and mark temporarily."
    (when (region-active-p)
      (when (< (point) (mark)) ; selection is done starting from bottom to up
        (exchange-point-and-mark)
        (setq modi/drag-stuff--point-mark-exchanged t))
      (if (zerop (current-column))
          (progn
            (backward-char 1)
            (setq modi/drag-stuff--point-adjusted t))
        ;; If point did not end up being on the first column after the
        ;; point/mark exchange, revert that exchange.
        (when modi/drag-stuff--point-mark-exchanged
          (exchange-point-and-mark) ; restore the original point and mark loc
          (setq modi/drag-stuff--point-mark-exchanged nil)))))

  (defun modi/drag-stuff--rst-pt-post-drag ()
    "Restore the `point' to where it was by forwarding it by one char after
the vertical drag is done."
    (when modi/drag-stuff--point-adjusted
      (forward-char 1)
      (setq modi/drag-stuff--point-adjusted nil))
    (when modi/drag-stuff--point-mark-exchanged
      (exchange-point-and-mark) ; restore the original point and mark loc
      (setq modi/drag-stuff--point-mark-exchanged nil))))


(use-package untabify-trailing-ws
  :straight nil
  :demand
  :config
  (untabify-trailing-ws 1))


(use-package align
  :straight nil
  :config
  (setq align-default-spacing 1)
  (setq align-to-tab-stop nil))


(use-package elec-pair
  :straight nil
  :demand
  :config
  (electric-pair-mode 1))


(use-package whole-line-or-region
  :bind (("C-w" . whole-line-or-region-kill-region)))


;; INFO: `delete-selection-mode' prevented operating on regions,
;; such as adding parenthesis after selecting a sexp.
;; Disabled by default at load-up.
(use-package delsel
  :straight nil)


(use-package smart-mark
  :demand
  :config
  (smart-mark-mode 1))


;; INFO: Decided not to use `region-bindings-mode-map' to avoid conflicts with `elec-pair'
(use-package multiple-cursors
  :bind (("C-S-c C-S-c"   . mc/edit-lines)
         ("C->"           . mc/mark-next-like-this)
         ("C-<"           . mc/mark-previous-like-this)
         ("C-c C-<"       . mc/mark-all-like-this)
         ("C-C C-#"       . mc/insert-numbers)
         ("C-S-<mouse-1>" . mc/add-cursor-on-click)))


(use-package expand-region
  :bind (("C-=" . er/expand-region))
  :config
  (setq expand-region-contract-fast-key "|")
  (setq expand-region-reset-fast-key "<ESC><ESC>"))



;;;; Sysadmin
(use-package sudo-ext)


(use-package tramp
  :straight nil
  :config
  (setq tramp-own-remote-path nil) ; `tramp-remote-path': List of directories to search for executables on remote host.
  (add-to-list 'tramp-remote-path 'tramp-own-remote-path))


(use-package deferred)


(use-package pcap-mode)


(use-package jenkins
  :straight (:repo "rmuslimov/jenkins.el"
             :fork (:repo "gmlarumbe/jenkins.el" :branch "deferred"))
  :bind (:map jenkins-job-view-mode-map
         ("n" . next-line)
         ("p" . previous-line))

  :config
  (defun larumbe/jenkins-switch-regex-parsing ()
    "Switch Jenkins regexp parsing for large files to save loading time.
This is because regexp parsing blocks Emacs execution and might not be useful for large files."
    (interactive)
    (if larumbe/jenkins-compilation-parse-console-output
        (progn
          (setq larumbe/jenkins-compilation-parse-console-output nil)
          (message "Disabling parsing of Jenkins console output"))
      (setq larumbe/jenkins-compilation-parse-console-output t)
      (message "Enabling parsing of Jenkins console output"))))


(use-package unison-mode
  ;; There are 2 packages, unison and unison-mode.
  ;; The first one for process invocation
  ;; The second one for syntax highlighting and process invocation -> Using this
  :mode (("\\.prf\\'" . unison-mode))
  :config
  (use-package unison-sync-minor-mode
    :straight nil
    :bind (:map unison-mode-map
           ("C-c C-c" . unison-my-run))
    :hook ((unison-mode . unison-sync-minor-mode))))


(use-package ssh-tunnels
  :straight (:repo "death/ssh-tunnels"
             :fork (:repo "gmlarumbe/ssh-tunnels" :branch "larumbe")))


(use-package erc
  :straight nil
  :commands (erc-login
             larumbe/erc-login)
  :config
  (use-package erc-sasl
    :straight (:host github :repo "psachin/erc-sasl")
    :demand)
  (setq erc-sasl-use-sasl t)
  ;; Provides a way of authenticating before actually connecting to the server.
  ;; Requires providing the nick and password in the `erc-tls' function.
  (add-to-list 'erc-sasl-server-regexp-list "irc\\.freenode\\.net")
  (add-to-list 'erc-sasl-server-regexp-list "chat\\.freenode\\.net")

  (defun larumbe/erc-login ()
    "Perform user authentication at the IRC server."
    (erc-log (format "login: nick: %s, user: %s %s %s :%s"
                     (erc-current-nick)
                     (user-login-name)
                     (or erc-system-name (system-name))
                     erc-session-server
                     erc-session-user-full-name))
    (if erc-session-password
        (erc-server-send (format "PASS %s" erc-session-password))
      (message "Logging in without password"))
    (when (and (featurep 'erc-sasl)
               (erc-sasl-use-sasl-p))
      (erc-server-send "CAP REQ :sasl"))
    (erc-server-send (format "NICK %s" (erc-current-nick)))
    (erc-server-send
     (format "USER %s %s %s :%s"
             ;; hacked - S.B.
             (if erc-anonymous-login erc-email-userid (user-login-name))
             "0" "*"
             erc-session-user-full-name))
    (erc-update-mode-line))

  (advice-add 'erc-login :override #'larumbe/erc-login))



;;;; Misc
;; GUI and Clipboard
(use-package select
  :straight nil
  :config
  (setq select-enable-clipboard t) ; Clipboard enabling: default = t
  (setq select-enable-primary t))  ; Primary clipboard:  default = nil


(use-package simple
  :diminish auto-fill-function
  :straight nil
  :bind (("M-n"     . next-error)     ; M-n and M-p are already overwritten at mode-line.el.
         ("M-p"     . previous-error) ; This mapping allows to step through errors in a non-compilation buffer
         ("C-<f12>" . auto-fill-mode)
         ("<f12>"   . toggle-truncate-lines))
  :config
  (setq save-interprogram-paste-before-kill t))


(use-package hi-lock
  :straight nil
  :bind (("C-\\" . highlight-symbol-at-point)
         ("C-'" . unhighlight-regexp)))


(use-package auto-highlight-symbol
  :bind (("<f11>" . auto-highlight-symbol-mode))
  :bind (:map auto-highlight-symbol-mode-map
         ("M-<"     . ahs-backward)
         ("M->"     . ahs-forward)
         ("M--"     . ahs-back-to-start)
         ("C-x C-'" . ahs-change-range)
         ("C-x C-a" . ahs-edit-mode))
  :config
  (setq ahs-default-range 'ahs-range-whole-buffer))


(use-package re-builder
  :config
  (setq reb-re-syntax 'read))  ;; Emacs double escaping (for single escaping use 'string)


(use-package man
  :straight nil
  :config
  (setq Man-notify-method 'pushy))


(use-package which-key
  :diminish
  :demand
  :config
  (which-key-mode 1))


(use-package browse-url
  :straight nil
  :config
  (setq browse-url-browser-function 'browse-url-firefox))


(use-package pdf-tools
  :bind (:map pdf-view-mode-map
              ("j"   . pdf-view-next-line-or-next-page)
              ("k"   . pdf-view-previous-line-or-previous-page)
              ("M-w" . pdf-view-kill-ring-save))
  :config
  (pdf-loader-install t))


(use-package autorevert
  :straight nil
  :diminish auto-revert-mode)


(use-package so-long
  :diminish
  :config
  (global-so-long-mode 1))


;; API of `coin-ticker' was outdated. Also tried `crypto-ticker-mode' but was a bit more complex than this one
(use-package btc-ticker
  :straight (:repo "niedbalski/emacs-btc-ticker"
             :fork (:repo "gmlarumbe/emacs-btc-ticker" :branch "larumbe")))


(use-package keyfreq
  :demand
  :config
  (setq keyfreq-file      (locate-user-emacs-file "keyfreq"))
  (setq keyfreq-file-lock (locate-user-emacs-file "keyfreq.lock"))
  (setq keyfreq-excluded-commands
        '(self-insert-command
          outshine-self-insert-command
          forward-char
          backward-char
          previous-line
          next-line
          exwm-input-send-simulation-key))
  (keyfreq-mode 1)
  (keyfreq-autosave-mode 1)

  (defun my/keyfreq-save-html ()
    "Save the table of frequently used commands (and their associated bindings
to an html file in `user-emacs-directory'."
    (interactive)
    (keyfreq-html (locate-user-emacs-file "keyfreq.html"))))


(use-package xah-lee-functions
  :straight nil)


(use-package modi-functions
  :bind (("C-]" . modi/pull-up-line))
  :straight nil)



;;;; Libraries
(use-package f)
(use-package pcre2el)
(use-package with-editor)
(use-package request)
(use-package bind-key)



(provide 'init-basic)

;;; init-basic.el ends here
