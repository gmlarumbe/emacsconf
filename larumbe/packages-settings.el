;;;;;;;;;;;;;;;;;;;;
;; PACKAGES SETUP ;;
;;;;;;;;;;;;;;;;;;;;

;;; Package management setup for use-package
(require 'package)
(setq package-enable-at-startup nil)
(add-to-list 'package-archives '("melpa"        . "http://melpa.org/packages/"))
(add-to-list 'package-archives '("melpa-stable" . "http://stable.melpa.org/packages/"))
(add-to-list 'package-archives '("gnu"          . "http://elpa.gnu.org/packages/"))
(package-initialize)

(unless (package-installed-p 'use-package)
  (package-refresh-contents)
  (package-install 'use-package))

;; use-package.el is no longer needed at runtime
;; This means you should put the following at the top of your Emacs, to further reduce load time:
(eval-when-compile
  (require 'use-package))

(setq use-package-always-ensure t) ; Force download if not available


(use-package diminish
  :ensure
  :config
  ;; Emacs built-in modes
  (add-hook 'hs-minor-mode-hook '(lambda () (diminish 'hs-minor-mode)))
  (diminish 'eldoc-mode)
  )

(use-package bind-key)



;;; Basic Packages
(use-package quelpa-use-package)

(use-package so-long
  :quelpa (so-long :url "https://raw.githubusercontent.com/emacs-mirror/emacs/master/lisp/so-long.el" :fetcher url)
  :config (global-so-long-mode 1)
  :diminish
  )

(use-package move-lines
  :load-path "~/.elisp/download/")


(use-package whole-line-or-region)


(use-package sudo-ext)


(use-package f)


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
  )


(use-package imenu-list
  :config
  (setq imenu-list-size 0.15)
  )


(use-package hydra)


(use-package coin-ticker)


(use-package google-this
  :diminish
  :config
  (google-this-mode 1)
  )

(use-package tramp
  :config
  (setq larumbe/tramp-own-remote-path nil)                  ;; Overrides some local paths needed for Magit
  (when larumbe/tramp-own-remote-path
    (add-to-list 'tramp-remote-path 'tramp-own-remote-path) ;; Used to preserve remote $PATH variable after Nemo scripts are sourced
    )
  )

(use-package magit
  :config
  (setq magit-diff-refine-hunk t) ; Highlight differences of selected hunk
  )

(use-package bind-chord)


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
  (popwin-mode 1)
  )


(use-package dired-narrow)


(use-package dired-quick-sort
  :config
  (dired-quick-sort-setup)
  )



(use-package request)


(use-package elmacro
  :diminish
  :config
  (elmacro-mode 1) ; Enable 'elmacro' to translate Macros to Proper Elisp
  )



(use-package ido
  :config
  ;; Do not enable (ido-mode) since compatibility with helm is managed by `helm-completing-read-handlers-alist'
  (setq ido-default-buffer-method "selected-window")
  )



(use-package yasnippet
  :diminish yasnippet yas-minor-mode
  :config
  (use-package yasnippet-snippets)                      ; Install MELPA snippets database
  (add-to-list 'yas-snippet-dirs "~/.elisp/snippets" t) ; Add snippets fetched from GitHub and customized
  (yas-reload-all)
  )



(use-package diff-mode
  :bind (:map diff-mode-map
              ("M-o" . other-window)) ; Remove `M-o' binding (Overrides 'diff-goto-source, which is defined by `o' as well)
  :hook ((diff-mode . (lambda () (setq truncate-lines t)))
         (diff-mode . linum-mode))
  :config
  (setq ediff-split-window-function 'split-window-horizontally)
  (setq ediff-window-setup-function 'ediff-setup-windows-plain)
  )


(use-package dsvn
  :config
  (autoload 'svn-status "dsvn" "Run `svn status'." t)
  (autoload 'svn-update "dsvn" "Run `svn update'." t)

  (define-obsolete-function-alias 'string-to-int 'string-to-number "22.1")
  )


(use-package smart-mode-line
  :config
  (setq sml/theme 'dark) ; Other choices would be 'light or 'respectful. By default, sml will try to figure out the best sml theme to go with your Emacs theme.
  (sml/setup)            ; Enable smart-mode-line
  (which-function-mode)
  )



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
  (setq view-read-only t)
  )



(use-package term
  :bind (:map term-raw-map
              ("M-o" . other-window)
              ("M-x" . helm-M-x)
              ("M->" . end-of-buffer)
              ("M-<" . beginning-of-buffer))
  :config
  (setq comint-process-echoes t)
  )



(use-package fic-mode
  :config
  (setq fic-activated-faces '(font-lock-doc-face  font-lock-comment-face))
  (setq fic-highlighted-words '("FIXME" "TODO" "BUG" "DANGER" "INFO"))
  )


(use-package auto-complete
  :diminish
  :bind (:map ac-completing-map
              ("C-n" . ac-next)
              ("C-p" . ac-previous)
              ("C-j" . ac-complete)
              ("RET" . ac-complete))

  :config
  (setq ac-delay 1.3)
  (setq ac-etags-requires 1)
  ;; INFO: Auto-complete has 3 mode-maps
  ;; https://emacs.stackexchange.com/questions/3958/remove-tab-trigger-from-auto-complete
  (define-key ac-mode-map       (kbd "TAB") nil)
  (define-key ac-completing-map (kbd "TAB") nil)
  (define-key ac-completing-map [tab] nil)

  ;; Provides `ac-source-gtags'
  (use-package auto-complete-gtags
    :load-path "~/.elisp/download"
    :config
    (setq ac-gtags-modes '(c-mode cc-mode c++-mode verilog-mode emacs-lisp-mode vhdl-mode sh-mode python-mode tcl-mode))
    )

  ;; Provides `ac-source-verilog'
  (use-package auto-complete-verilog
    :load-path "~/.elisp/download/")

  ;; Default sources will be `ac-source-words-in-same-mode-buffers'
  )


(use-package re-builder
  :config
  (setq reb-re-syntax 'read)  ;; Emacs double escaping (for single escaping use 'string)
  )


;; There are 2 packages, unison and unison-mode.
;; The first one for process invocation
;; The second one for syntax highlighting and process invocation -> Using this
(use-package unison-mode
  :bind (:map unison-mode-map
              ("C-c C-c" . unison-my-run))
  :config
  (autoload 'unison-mode "unison-mode" "my unison mode" t)
  (setq auto-mode-alist (append '(("\\.prf$" . unison-mode)) auto-mode-alist))
  (setq unison-command-name "unison")   ;; Override unison command
  (add-hook 'unison-mode-hook 'unison-sync-minor-mode)
  )


(use-package unison-sync-minor-mode
  :load-path "~/.elisp/larumbe/own-modes/minors/")


;; BUG: Send bug report
(use-package jenkins
  :config
  ;; (setq jenkins-api-token "")
  ;; (setq jenkins-url "")
  ;; (setq jenkins-username "")
  ;; (setq jenkins-viewname "<viewname>")

  ;; Redefining MELPA function
  ;; DANGER: Workaround:
  ;;   1st - Require package to load funcions and make them available
  ;;   2nd - Redefine jenkins--get-auth-headers
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
      (setq truncate-lines t)))

  ;; Redefine Keys for Jenkins-job-view
  (define-key jenkins-job-view-mode-map (kbd "n") 'next-line)
  (define-key jenkins-job-view-mode-map (kbd "p") 'previous-line)
  )



;;; HELM
;;;; Helm Support
(use-package helm-org)

(use-package helm
  :diminish
  :bind (("C-x c /" . helm-find) ; Enable C-x c prefix commands
         ("C-x c p" . helm-list-emacs-process)
         ("C-x c t" . helm-top))

  :config
  (setq helm-completing-read-handlers-alist
        '((describe-function         . helm-completing-read-symbols)
          (describe-variable         . helm-completing-read-symbols)
          (describe-symbol           . helm-completing-read-symbols)
          (debug-on-entry            . helm-completing-read-symbols)
          (find-function             . helm-completing-read-symbols)
          (disassemble               . helm-completing-read-symbols)
          (trace-function            . helm-completing-read-symbols)
          (trace-function-foreground . helm-completing-read-symbols)
          (trace-function-background . helm-completing-read-symbols)
          (find-tag                  . helm-completing-read-default-find-tag)
          (org-capture               . helm-org-completing-read-tags)
          (org-set-tags              . helm-org-completing-read-tags)
          (ffap-alternate-file)
          (tmm-menubar)
          (find-file)
          (find-file-at-point        . helm-completing-read-sync-default-handler)
          (ffap                      . helm-completing-read-sync-default-handler)
          (execute-extended-command)
          ;; IDO support without enabling ido-mode
          (switch-to-buffer . ido)
          (kill-buffer      . ido)
          ))
  (helm-mode 1)
  (helm-autoresize-mode 1)
  )


;;;; Projectile + Helm-Projectile + Helm AG
(use-package helm-ag)
(use-package helm-projectile :diminish)
(use-package projectile
  :bind (:map projectile-mode-map ; Projectile 2.0 removes automatic keybindings
              ("C-c p j" . projectile-find-tag)
              ("C-c p r" . projectile-regenerate-tags)
              ("C-c p a" . helm-projectile-ag)
              ("C-c p g" . helm-projectile-grep)
              ("C-c p c" . projectile-compile-project)
              ("C-c p f" . projectile-find-file)
              )
  :config
  (add-to-list 'projectile-project-root-files-bottom-up ".repo") ; Detect `repo' Git sandboxes (Sandbox preference over IP)
  (setq projectile-completion-system 'helm)
  (setq projectile-mode-line-prefix " P") ; Modeline
  (defun larumbe/projectile-custom-mode-line ()
    "Report ONLY project name (without type) in the modeline."
    (let ((project-name (projectile-project-name)))
      (format "%s[%s]"
              projectile-mode-line-prefix
              (or project-name "-")
              )))
  (setq projectile-mode-line-function 'larumbe/projectile-custom-mode-line) ; Replaces `projectile-default-mode-line' that also showed ":generic" type of project
  )





;;;; Helm-Navi + Outshine
;; `helm-navi' loads `navi-mode', and this last one loads `outshine'
(use-package helm-navi
  :diminish outshine-mode outline-minor-mode
  :config
  ;; BUG: Issue with helm-navi in last MELPA package
  ;; https://github.com/emacs-helm/helm-navi/pull/3
  ;; These functions needs to be redefined and:
  ;;  Search and replace of: outline-promotion-headings -> outshine-promotion-headings
  (defun helm-navi--get-candidates-in-buffer (buffer &optional regexp)
    "Return Outshine heading candidates in BUFFER.
Optional argument REGEXP is a regular expression to match, a
function to return a regular expression, or
`outshine-promotion-headings' by default."
    ;; Much of this code is copied from helm-org.el
    (with-current-buffer buffer
      ;; Make sure outshine is loaded
      (unless outshine-promotion-headings
        (error "Outshine is not activated in buffer \"%s\".  Activate `outline-minor-mode', or consult Outshine's documentation for further instructions if necessary." (buffer-name buffer)))
      (let* ((heading-regexp (pcase regexp
                               ((pred functionp) (funcall regexp))
                               ((pred stringp) regexp)
                               ((pred null) (concat "^\\("
                                                    (mapconcat (lambda (s)
                                                                 (s-trim (car s)))
                                                               outshine-promotion-headings
                                                               "\\|")
                                                    "\\)"
                                                    "\s+\\(.*\\)$"))))
             (match-fn (if helm-navi-fontify
                           #'match-string
                         #'match-string-no-properties))
             (search-fn (lambda ()
                          (re-search-forward heading-regexp nil t))))
        (save-excursion
          (save-restriction
            (goto-char (point-min))
            (cl-loop while (funcall search-fn)
                     for beg = (point-at-bol)
                     for end = (point-at-eol)
                     when (and helm-navi-fontify
                               (null (text-property-any
                                      beg end 'fontified t)))
                     do (jit-lock-fontify-now beg end)
                     for level = (length (match-string-no-properties 1))
                     for heading = (if regexp
                                       (funcall match-fn 0)
                                     (concat (match-string 1) " " (funcall match-fn 2)))
                     if (or regexp
                            (and (>= level helm-org-headings-min-depth)
                                 (<= level helm-org-headings-max-depth)))
                     collect `(,heading . ,(point-marker))))))))


  (defun helm-navi--get-regexp ()
    "Return regexp for all headings and keywords in current buffer."
    (concat (navi-make-regexp-alternatives
             (navi-get-regexp (car
                               (split-string
                                (symbol-name major-mode)
                                "-mode" 'OMIT-NULLS))
                              :ALL)
             (mapconcat (lambda (s)
                          (s-trim (car s)))
                        outshine-promotion-headings
                        "\\|"))
            ".*$"))
  )


(use-package outshine
  :config
  (setq outshine-imenu-show-headlines-p nil)) ; Do not include outshine tags at imenu


;;; Own modes
;;;; Major Modes
;; Some day...

;;;; Minor modes
;;;;; unison-sync
(use-package unison-sync-minor-mode
  :load-path "~/.elisp/larumbe/own-modes/minors/")
;; DANGER:
;; This was declared when initializing unison-mode and might not work if no .prf file is open
;; (setq unison-command-name "unison")

;;;;; vhier-outline
(use-package vhier-outline-mode
  :load-path "~/.elisp/larumbe/own-modes/minors/")


;;; Rarely used packages
(use-package hide-comnt
  :load-path "~/.elisp/download/")


(use-package jpeg-mode
  :load-path "~/.elisp/download/")
