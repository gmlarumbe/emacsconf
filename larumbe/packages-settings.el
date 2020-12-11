;;; packages-settings.el --- Packages  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;; Explicit dependencies
(use-package gnu-elpa-keyring-update) ; Update elpa keys to avoid signature issues

(use-package f)
(use-package with-editor)
(use-package elmacro
  :diminish)
(use-package outshine
  :config
  ;; Do not include outshine tags at imenu
  (setq outshine-imenu-show-headlines-p nil))
(use-package navi-mode)

(use-package ido
  :config
  (setq ido-everywhere nil)
  (setq ido-default-buffer-method "selected-window"))


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
  ;; INFO: Is relatively straightforward to implement via deferring just the last
  ;; step (console output retrieval). However, since previous steps such as
  ;; `jenkins--retrieve-page-as-json' make use of `url-retrieve-synchronously'
  ;; and use the result all along the code, everything would need to be deferred
  ;; and rewritten, and that is simply non-viable.
  ;; Even with `async', a sentinel-based approach would be used and all the
  ;; pending code on the call stack would be executed before the callback
  ;; function, and this code actually depends on the result of the first
  ;; `url-retrieve', so there is no easy option...


  ;; Conditionally set compilation regexp parsing of Jenkins console output buffers
  (defvar larumbe/jenkins-compilation-parse-console-output t)

  (defun larumbe/jenkins-get-console-output (jobname build)
    "Show the console output for the current job."
    (let ((url-request-extra-headers (jenkins--get-auth-headers))
          (console-buffer (get-buffer-create (format "*jenkins-console-%s-%s*" jobname build)))
          (url (format "%sjob/%s/%s/consoleText" (get-jenkins-url) jobname build)))
      (switch-to-buffer console-buffer)
      ;; Retrieve output only if it wasn't fetched before
      (when (equal (buffer-size console-buffer) 0)
        (with-current-buffer console-buffer
          (setq buffer-read-only nil)
          (erase-buffer)
          (insert "Loading console output asynchronously...\n")
          (when larumbe/jenkins-compilation-parse-console-output
            (compilation-mode)
            (larumbe/scons-error-regexp-set-emacs)))
        (deferred:$
          (deferred:url-retrieve url)
          (deferred:nextc it
            (lambda (buf)
              (with-current-buffer console-buffer
                (setq buffer-read-only nil)
                (erase-buffer))
              (with-current-buffer buf
                (append-to-buffer console-buffer (point-min) (point-max))
                (message "Jenkins job retrieved successfully. Waiting for regexp parsing...")
                (pop-to-buffer console-buffer)
                (setq truncate-lines t)
                (setq buffer-read-only t))))))))

  (advice-add 'jenkins-get-console-output :override #'larumbe/jenkins-get-console-output))


(use-package jpeg-mode
  :load-path "~/.elisp/download/")

(use-package pcap-mode)

(use-package deferred)


(use-package sr-speedbar
  :load-path "~/.elisp/download/"
  :commands (sr-speedbar-open)
  :bind (:map speedbar-mode-map
              ("q"   . larumbe/kill-current-buffer)
              ("j"   . speedbar-edit-line))
  :config
  (setq speedbar-show-unknown-files t)
  (setq speedbar-use-images nil)
  (setq sr-speedbar-right-side t))


(use-package pcre2el) ; Used in VHDL and Verilog to convert Perl Regexps to Elisp and find parent modules



(provide 'packages-settings)

;;; packages-settings.el ends here
