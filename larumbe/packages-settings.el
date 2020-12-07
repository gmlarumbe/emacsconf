;;;;;;;;;;;;;;;;;;;;
;; PACKAGES SETUP ;;
;;;;;;;;;;;;;;;;;;;;

;;; Basic Packages
(use-package diminish
  :ensure
  :hook ((hs-minor-mode . my-diminish-hook))
  :config
  (diminish 'eldoc-mode)
  (defun my-diminish-hook ()
    (diminish 'hs-minor-mode)))

(use-package quelpa-use-package)

(use-package so-long
  :quelpa (so-long :url "https://raw.githubusercontent.com/emacs-mirror/emacs/master/lisp/so-long.el" :fetcher url)
  :config (global-so-long-mode 1)
  :diminish)

(use-package man
  :ensure nil
  :config
  (setq Man-notify-method 'pushy))

(use-package sudo-ext)

(use-package tramp
  :config
  (setq tramp-own-remote-path nil) ; `tramp-remote-path': List of directories to search for executables on remote host.
  (add-to-list 'tramp-remote-path 'tramp-own-remote-path))


(use-package re-builder
  :config
  (setq reb-re-syntax 'read))  ;; Emacs double escaping (for single escaping use 'string)

(use-package bind-key)

(use-package bind-chord)


(use-package which-key
  :config
  (which-key-mode 1))


;;; Navigation
(use-package ido
  :config
  ;; INFO: ido should not be enabled since compatibility with helm is managed by `helm-completing-read-handlers-alist'
  ;; However, if ido is not enabled, `ido-buffer-completion-map' does not get loaded
  ;; and therefore its not possible to make use of buffer killing while switching.
  (setq ido-everywhere nil)
  (ido-mode 1) ; Enable, so that commands like `ido-kill-buffer-at-head' can be performed
  (setq ido-default-buffer-method "selected-window"))


(use-package isearch
  :ensure nil
  :hook ((isearch-mode . my-isearch-mode-hook))
  :config
  (defun my-isearch-mode-hook ()
    (substitute-key-definition #'isearch-yank-word-or-char
                               #'my-isearch-yank-word-or-char-from-beginning
                               isearch-mode-map)))


(use-package view
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
  :config
  (setq view-read-only t))


(use-package popwin
  :config
  (setq popwin:special-display-config
        '(
          ("*Miniedit Help*" :noselect t)
          (help-mode)
          (completion-list-mode :noselect t)
          (compilation-mode :noselect t)
          (grep-mode :noselect t)
          (occur-mode :noselect t)
          ("*Pp Macroexpand Output*" :noselect t)
          ("*Shell Command Output*")
          ("*vc-diff*")
          ("*vc-change-log*")
          (" *undo-tree*" :width 60 :position right)
          ("^\\*anything.*\\*$" :regexp t)
          ("*slime-apropos*")
          ("*slime-macroexpansion*")
          ("*slime-description*")
          ("*slime-compilation*" :noselect t)
          ("*slime-xref*")
          (sldb-mode :stick t)
          (slime-repl-mode)
          (slime-connection-list-mode)
          ("*unison*")
          ))
  (popwin-mode 1))


(use-package winner
  :ensure nil
  :config
  (winner-mode 1))


(use-package ag
  :config
  (setq ag-arguments           ; Fetched from modi verilog config
        '("--nogroup"          ; mandatory argument for ag.el as per https://github.com/Wilfred/ag.el/issues/41
          "--skip-vcs-ignores" ; Ignore files/dirs ONLY from `.ignore'
          "--numbers"          ; Line numbers
          "--smart-case"
          ;; "--one-device"       ; Do not cross mounts when searching
          "--follow"           ; Follow symlinks
          "--ignore" "#*#"     ; Adding "*#*#" or "#*#" to .ignore does not work for ag (works for rg)
          ;; Added by Larumbe
          "--ignore" "*~"
          "--stats"))
  (setq ag-reuse-buffers t)
  (setq ag-reuse-window t))


(use-package pdf-tools
  :bind (:map pdf-view-mode-map
              ("j"   . pdf-view-next-line-or-next-page)
              ("k"   . pdf-view-previous-line-or-previous-page)
              ("M-w" . pdf-view-kill-ring-save)
              )
  :config
  (pdf-tools-install))


(use-package browse-url
  :config
  (setq browse-url-browser-function 'browse-url-firefox))


(use-package beacon
  :config
  (beacon-mode 1))

(use-package buffer-move)

;;; Editing
(use-package untabify-trailing-ws
  :load-path "~/.elisp/larumbe/own-modes/minors/"
  :config
  (untabify-trailing-ws 1)) ; Enabled


(use-package align
  :ensure nil
  :config
  (setq align-default-spacing 1) ; Align to 1 space
  (setq align-to-tab-stop nil))


(use-package elec-pair ; Automatically write closing matching parenthesis/brackets
  :ensure nil
  :config
  (electric-pair-mode 1))


(use-package move-lines
  :load-path "~/.elisp/download/")


(use-package whole-line-or-region)



;;; Misc
;; (use-package btc-ticker)


(use-package google-this
  :diminish
  :config
  (google-this-mode 1))


(use-package request)


;; There are 2 packages, unison and unison-mode.
;; The first one for process invocation
;; The second one for syntax highlighting and process invocation -> Using this
(use-package unison-mode
  :bind (:map unison-mode-map
              ("C-c C-c" . unison-my-run))
  :hook ((unison-mode . unison-sync-minor-mode))
  :config
  (autoload 'unison-mode "unison-mode" "my unison mode" t)
  (setq auto-mode-alist (append '(("\\.prf$" . unison-mode)) auto-mode-alist))

  (use-package unison-sync-minor-mode
    :load-path "~/.elisp/larumbe/own-modes/minors/"))


(use-package jenkins
  :bind (:map jenkins-job-view-mode-map
              ("n" . next-line)
              ("p" . previous-line))
  :config
  ;; Redefining MELPA function
  ;; DANGER: Workaround:
  ;;   1st - Require package to load funcions and make them available
  ;;   2nd - Redefine jenkins--get-auth-headers
  ;;       BUG: Send bug report of `jenkins--get-auth-headers'
  (defun jenkins--get-auth-headers ()
    "Helper function to setup auth header for jenkins url call."
    `(("Content-Type" . "application/x-www-form-urlencoded")
      ("Authorization" .
       ,(concat
         "Basic "
         (base64-encode-string
          (concat jenkins-username ":" jenkins-api-token) t)))))

  ;; Redefine to take scons regexps into account for console buffer
  (defun jenkins-get-console-output (jobname build)
    "Show the console output for the current job"
    (let ((url-request-extra-headers (jenkins--get-auth-headers))
          (console-buffer (get-buffer-create (format "*jenkins-console-%s-%s*" jobname build)))
          (url (format "%sjob/%s/%s/consoleText" (get-jenkins-url) jobname build)))
      (with-current-buffer console-buffer
        (erase-buffer)
        (compilation-mode)
        (larumbe/scons-error-regexp-set-emacs)
        (read-only-mode -1)
        (with-current-buffer (url-retrieve-synchronously url)
          (append-to-buffer console-buffer (point-min) (point-max))))
      (pop-to-buffer console-buffer)
      (read-only-mode 1)
      (setq truncate-lines t))))


(use-package jpeg-mode
  :load-path "~/.elisp/download/")

(use-package pcap-mode)

(use-package deferred)
