;;;;;;;;;;;;;;;;;;;;
;; PACKAGES SETUP ;;
;;;;;;;;;;;;;;;;;;;;

(use-package diminish
  :ensure
  :config
  ;; Emacs built-in modes
  (add-hook 'hs-minor-mode-hook '(lambda () (diminish 'hs-minor-mode)))
  (diminish 'eldoc-mode)
  )

;; TODO: Where to place it?
(use-package bind-key)


(use-package isearch
  :ensure nil
  :config
  (add-hook 'isearch-mode-hook
            (lambda ()
              "Activate my customized Isearch word yank command."
              (substitute-key-definition 'isearch-yank-word-or-char
                                         'my-isearch-yank-word-or-char-from-beginning
                                         isearch-mode-map))))

(use-package untabify-trailing-ws
  :load-path "~/.elisp/larumbe/own-modes/minors/"
  :config
  (untabify-trailing-ws 1)) ; Enabled


;;; Built-in modes config
;;;; Variables
(use-package man
  :ensure nil
  :config
  (setq Man-notify-method 'pushy))


(use-package align
  :ensure nil
  :config
  (setq align-default-spacing 1) ; Align to 1 space
  (setq align-to-tab-stop nil))


;;;; Generic
(use-package elec-pair ; Automatically write closing matching parenthesis/brackets
  :ensure nil
  :config
  (electric-pair-mode 1))


(use-package winner
  :ensure nil
  :config
  (winner-mode 1))


;;;; Org-Mode
(use-package org
  :ensure nil
  :bind (:map org-mode-map
              ("C-c l" . org-store-link)
              ("C-c a" . org-agenda)
              ("C-c c" . org-capture)
              ("C-c b" . org-iswitchb)
              ("C-,"   . nil) ; Unamps org-cycle-agenda-files to free `larumbe/ansi-term'
              )
  :config
  (setq org-log-done 'time)
  (setq org-agenda-files (list "~/TODO.org"))
  (setq org-todo-keywords
        '((sequence "TODO" "IN PROGRESS" "|" "DONE" "CANCELED" "POSTPONED")
          (sequence "|" "INFO")))
  (setq org-todo-keyword-faces
        '(("TODO"        . org-warning)
          ("IN PROGRESS" . "yellow")
          ("CANCELED"    . (:foreground "blue" :weight bold))
          ("POSTPONED"   . "cyan")
          ("INFO"        . "light blue")
          )))


(defun larumbe/org-show-todos-agenda ()
  "Show org-mode TODOs and agenda."
  (interactive)
  (let* ((buf  "TODO.org")
         (file (concat "~/" buf)))
    (when (not (get-buffer buf))
      (find-file file))
    (switch-to-buffer buf)
    (call-interactively 'org-agenda-list)))



;;;; dired
(use-package dired
  :ensure nil
  :bind (:map dired-mode-map
              ("b" . dired-up-directory)
              ("J" . dired-goto-file)                             ; Switch from 'j' to 'J'
              ("j" . larumbe/dired-do-async-shell-command-okular) ; Open file-at-point directly with Okular if is a PDF and delete async process window. Otherwise it will ask for default program
              ("," . larumbe/toggle-dired-deletion-confirmer)     ; https://superuser.com/questions/332590/how-to-prevent-delete-confirmation-in-emacs-dired
              )
  :config
  (add-hook 'dired-mode-hook '(lambda ()
                                (interactive)
                                (dired-hide-details-mode 1))))


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



(defun larumbe/toggle-dired-deletion-confirmer ()
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
      (call-interactively 'dired-do-async-shell-command))))




;;; Mode-line
(use-package smart-mode-line
  :config
  (setq sml/theme 'dark) ; Other choices would be 'light or 'respectful. By default, sml will try to figure out the best sml theme to go with your Emacs theme.
  (sml/setup)            ; Enable smart-mode-line
  (which-function-mode)
  (set-face-attribute 'which-func nil :foreground "green")
  (setq line-number-mode nil) ; Hide current line number from mode-line
  (setq display-time-default-load-average nil) ; Display time on the status bar
  (display-time-mode t)
  )



;;; Basic Packages
(use-package flycheck
  :diminish)


(use-package flyspell
  :ensure nil
  :config
  (defun flyspell-toggle ()
    "Toggle flyspell mode on current buffer."
    (interactive)
    (if (bound-and-true-p flyspell-mode)
        (call-interactively 'flyspell-mode nil)
      (progn
        (call-interactively 'flyspell-mode 1)
        (call-interactively 'flyspell-prog-mode 1)
        (call-interactively 'flyspell-buffer))))
  )


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
  (setq ag-reuse-buffers t)
  (setq ag-reuse-window t)
  )


(use-package imenu-list
  :config
  (setq imenu-list-size 0.15)
  (setq imenu-auto-rescan t)
  )


(use-package hydra
  :config
  (defun larumbe/hydra-yasnippet (snippet)
    "Function/Macro to integrate YASnippet within Hydra"
    (interactive)
    (progn
      (insert snippet)
      (yas-expand))))



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
  (add-to-list 'yas-snippet-dirs "~/.elisp/snippets")   ; Add snippets fetched from GitHub and customized ones. DO NOT Append to give them more precendence in case of collision
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

  (defun larumbe/ansi-term ()
    "Checks if there is an existing *ansi-term* buffer and pops to it (if not visible open on the same window).
Otherwise create it"
    (interactive)
    (let ((buf "*ansi-term*"))
      (if (get-buffer buf)
          (if (get-buffer-window buf)
              (pop-to-buffer buf)
            (switch-to-buffer buf))
        (ansi-term "/bin/bash"))))
  )



(use-package fic-mode
  :config
  (setq fic-activated-faces '(font-lock-doc-face  font-lock-comment-face))
  (setq fic-highlighted-words '("FIXME" "TODO" "BUG" "DANGER" "INFO"))
  )

;; Fetched from /home/martigon/.elisp/larumbe/lang/verilog-settings.el -> larumbe/lfp-clean-project-fic-keywords-ag-files
;; Generalizes to a directory and certain files
(defun larumbe/clean-fic-keywords-dir ()
  "Perform a `ag-regexp' of `fic-mode' highlighted keywords in order to check pending project actions. "
  (interactive)
  (let ((kwd)
        (path)
        (ag-arguments ag-arguments) ; Save the global value of `ag-arguments' (copied from modi)
        (regex)
        (files)
        )
    (setq kwd (completing-read "Select keyword: " 'fic-highlighted-words))
    (setq path (read-directory-name "Directory: "))
    ;; (setq regex (completing-read "Select file regex: " 'regex))
    (setq files (completing-read "Select file regex: " '("(System)Verilog" "Python" "elisp")))
    (pcase files
      ("(System)Verilog" (setq regex ".[s]?v[h]?$")) ; +Headers
      ("Python"          (setq regex ".py$"))
      ("elisp"           (setq regex ".el$"))
      )
    ;; Copied from AG for `modi/verilog-find-parent-module'
    (add-to-list 'ag-arguments "-G" :append)
    (add-to-list 'ag-arguments regex :append)
    (ag-regexp kwd path)))



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



;;; HELM + Ido
;;;; Helm Support
(use-package helm-org)

(use-package helm
  :diminish
  :bind (("C-x c /" . helm-find) ; Enable C-x c prefix commands
         ("C-x c p" . helm-list-emacs-process)
         ("C-x c t" . helm-top)
         ("M-s o"   . larumbe/helm-occur)
         )

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
  (ido-mode 1) ; Enable, so that commands like `ido-kill-buffer-at-head' can be performed
  )

(defun larumbe/helm-occur (&optional prefix)
  "Copied from `helm-occur' and slightly modified to allow searching symbols.
If called without prefix argument search for symbol and case-sensitive.
If called with prefix, search for string and no case sensitive."
  (interactive "P")
  ;; DANGER: Added to do a case-sensitive search
  (let ((case-fold-search prefix))
    ;; End of DANGER
    (setq helm-source-occur
          (car (helm-occur-build-sources (list (current-buffer)) "Helm occur")))
    (helm-set-local-variable 'helm-occur--buffer-list (list (current-buffer))
                             'helm-occur--buffer-tick
                             (list (buffer-chars-modified-tick (current-buffer))))
    (save-restriction
      (let (def pos)
        (when (use-region-p)
          ;; When user mark defun with `mark-defun' with intention of
          ;; using helm-occur on this region, it is relevant to use the
          ;; thing-at-point located at previous position which have been
          ;; pushed to `mark-ring'.
          (setq def (save-excursion
                      (goto-char (setq pos (car mark-ring)))
                      (helm-aif (thing-at-point 'symbol) (regexp-quote it))))
          (narrow-to-region (region-beginning) (region-end)))
        (unwind-protect
            (helm :sources 'helm-source-occur
                  :buffer "*helm occur*"
                  :default (or def (helm-aif (thing-at-point 'symbol)
                                       ;; DANGER: Modified at this point
                                       (if (not prefix)
                                           (concat "\\_<" (regexp-quote it) "\\_>")
                                         (regexp-quote it))
                                     ;; End of DANGER
                                     ))
                  :preselect (and (memq 'helm-source-occur
                                        helm-sources-using-default-as-input)
                                  (format "^%d:" (line-number-at-pos
                                                  (or pos (point)))))
                  :truncate-lines helm-occur-truncate-lines)
          (deactivate-mark t))))))


(defun larumbe/helm-help-major-mode ()
  "Get helm M-x commands list and shortcuts for the last time it was used (before a C-g)
It is assumed to be used after a `M-x' then e.g. `org-', then `C-g' and finally this function for window arrangement."
  (interactive)
  (delete-other-windows)
  (split-window-right)
  (other-window 1)
  (shrink-window 40 t)
  (switch-to-buffer "*helm M-x*")
  (other-window 1))



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
                                                    (mapconcat (lambda (s)                                     ;; DANGER: Modified to fix issue with // * headings,
                                                               (replace-in-string "*" "\\*" (s-trim (car s)))) ;; asterisk is wrongly inserted into the regexp
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
  (setq outshine-imenu-show-headlines-p nil) ; Do not include outshine tags at imenu
  )


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
