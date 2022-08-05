;;; init-packages.el --- Basic Packages configuration  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Window/Frame Display
(use-package popwin
  :config
  (popwin-mode 1))


(use-package which-func
  :straight nil
  :config
  (set-face-attribute 'which-func nil :foreground "green"))


(use-package time
  :straight nil
  :config
  (setq display-time-default-load-average nil)) ; Display time on the status bar


(use-package smart-mode-line
  :init
  (let* ((straight-repos-dir (expand-file-name (concat (file-name-as-directory straight-base-dir) "straight/repos")))
         (theme (concat (file-name-as-directory straight-repos-dir) "smart-mode-line/smart-mode-line-dark-theme.el"))
         (theme-buf (get-file-buffer theme))
         (hash (secure-hash 'sha256 theme-buf)))
    (unless (member hash custom-safe-themes)
      (push hash custom-safe-themes)))
  (setq sml/theme 'dark)) ; Other choices would be 'light or 'respectful. By default, sml will try to figure out the best sml theme to go with your Emacs theme.


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


  ;; Projectile-sorted buffers
(use-package ibuffer-projectile
    :hook ((ibuffer . modi/ibuffer-customization))
    :after ibuffer
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
  ;; Default was 'not-yanks, so text yanked into the search string in Isearch mode was always downcased.
  ;; Setting to t, upper case chars disable case fold searching (e.g. search symbol at point)
  (setq search-upper-case t)

  ;; https://www.emacswiki.org/emacs/SearchAtPoint
  (defun my-isearch-yank-word-or-char-from-beginning ()
    "Move to beginning of word before yanking word in `isearch-mode'.
Make \\keymapC-s C-w and C-r C-w act like Vim's g* and g#, keeping Emacs'
C-s C-w [C-w] [C-w]... behaviour. "
    (interactive)
    ;; Making this work after a search string is entered by user
    ;; is too hard to do, so work only when search string is empty.
    (let ((search-upper-case 'not-yanks)) ; INFO: Ignore case when searching. To take case into account better use symbol search
      (if (= 0 (length isearch-string))
          (beginning-of-thing 'word))
      ;; At some point in Emacs it required a '1' argument to fix a "Wrong type argument: number-or-marker-p, nil" error
      (isearch-yank-word-or-char 1))))


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
              ("l"   . recenter-top-bottom)
              ("RET" . nil)
              ("C-m" . nil))
  :config
  (setq view-read-only t))


(use-package outshine
  :bind (:map outshine-mode-map
         ("M-RET" . nil)) ; Leave space for `company-complete'
  :config
  ;; Do not include outshine tags at imenu
  (setq outshine-imenu-show-headlines-p nil))


(use-package navi-mode)


(use-package winner
  :straight nil
  :config)


(use-package beacon
  :diminish
  :config
  (setq beacon-size 20)
  (add-to-list 'beacon-dont-blink-major-modes 'term-mode))


(use-package speedbar
  :straight nil
  :commands (speedbar-toggle-line-expansion)) ; Used by `vhdl-speedbar' own customization


(use-package sr-speedbar
  ;; Default would be fetched from emacsorphanage
  :straight (:host github :repo "emacsmirror/emacswiki.org" :branch "master" :files ("sr-speedbar.el"))
  :bind (:map speedbar-mode-map
         ("q" . larumbe/kill-current-buffer)
         ("j" . speedbar-edit-line))
  :config
  (setq speedbar-show-unknown-files t)
  (setq speedbar-use-images nil)
  (setq sr-speedbar-right-side t))


(use-package bind-chord)


(use-package hardcore-mode
  :diminish hardcore-mode
  :init
  (setq too-hardcore-backspace t)
  (setq too-hardcore-return    t))


(use-package avy
  :bind (("C-;" . avy-goto-char-2)
         ("C-:" . avy-goto-word-1)))


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
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("minor-modes/untabify-trailing-ws.el"))
  :config
  (push (concat user-emacs-directory "straight/repos/verilog-mode/verilog-mode.el") untabify-trailing-disable-on-files)
  (push (concat user-emacs-directory "straight/repos/verilog-mode/verilog-test.el") untabify-trailing-disable-on-files))


(use-package align
  :straight nil
  :config
  (setq align-default-spacing 1)
  (setq align-to-tab-stop nil))


(use-package elec-pair
  :straight nil)


(use-package whole-line-or-region
  :bind (("C-w" . whole-line-or-region-kill-region)))


(use-package smart-mark)

(use-package multiple-cursors
  :bind (("C->"     . mc/mark-next-like-this)
         ("C-<"     . mc/mark-previous-like-this)
         ("C-c C->" . mc/edit-lines)
         ("C-c C-<" . mc/mark-all-like-this)
         ("C-c C-#" . mc/insert-numbers))
  :config
  (when (equal larumbe/completion-framework 'ivy)
    (add-to-list 'mc/cmds-to-run-once 'swiper-mc)))


(use-package expand-region
  :bind (("C-=" . er/expand-region))
  :config
  (setq expand-region-contract-fast-key "|")
  (setq expand-region-reset-fast-key "<ESC><ESC>"))



;;;; Sysadmin
(use-package arch-packer
  :straight (:repo "brotzeit/arch-packer"
             :fork (:repo "gmlarumbe/arch-packer"))
  :commands (arch-packer-toggle-command)
  :config
  (defun arch-packer-toggle-command ()
    "Toggle between 'pacman' and 'pacaur'."
    (interactive)
    (if (string= arch-packer-default-command "pacman")
        (progn
          (setq arch-packer-default-command "pacaur")
          (message "Set arch-packer command to: %s" arch-packer-default-command))
      (setq arch-packer-default-command "pacman")
      (message "Set arch-packer command to: %s" arch-packer-default-command))))


;; Similar to `arch-packer', but just for AUR.
;; Seems better to get info/voting.
;; Supports AUR package downloading but not installation.
(use-package aurel)

(use-package google-this
  :diminish
  :bind (("C-c / t" . google-this)
         ("C-c / l" . google-this-line)
         ("C-c / c" . google-this-translate-query-or-region))
  :config
  ;; Once a command present in :bind is executed the rest of `google-this-mode' commands will be available
  (google-this-mode 1))


(use-package google-translate
  :config
  ;; BUG: https://github.com/atykhonov/google-translate/issues/52
  ;; https://github.com/twlz0ne/multi-translate.el/issues/3
  (defun google-translate--search-tkk@fix-137 ()
    "Search TKK.
Fix ttk search error https://github.com/atykhonov/google-translate/issues/137"
    (list 430675 2721866130))

  (advice-add 'google-translate--search-tkk :override 'google-translate--search-tkk@fix-137)
  (setq google-translate-backend-method 'curl))


(use-package howdoi
  :straight (:host github :repo "arthurnn/howdoi-emacs"))


(use-package tramp
  :straight nil
  :config
  (setq tramp-own-remote-path nil) ; `tramp-remote-path': List of directories to search for executables on remote host.
  (add-to-list 'tramp-remote-path 'tramp-own-remote-path))


(use-package deferred)


(use-package async)


(use-package pcap-mode)


(use-package jenkins
  :straight (:repo "rmuslimov/jenkins.el"
             :fork (:repo "gmlarumbe/jenkins.el" :branch "deferred"))
  :bind (:map jenkins-job-view-mode-map
         ("n" . next-line)
         ("p" . previous-line))
  :config
  (setq jenkins-colwidth-name 50)
  (setq larumbe/jenkins-compilation-parser "xrun")

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
    :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("minor-modes/unison-sync-minor-mode.el"))
    :bind (:map unison-mode-map
           ("C-c C-c" . unison-my-run))
    :hook ((unison-mode . unison-sync-minor-mode))))


(use-package ssh-tunnels
  :config
  (setq ssh-tunnels-name-width 25)
  (setq ssh-tunnels-host-width 20))


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


(use-package env-switch
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/env-switch.el")))

;; Updates `exec-path' from $PATH.
;; More info: https://emacs.stackexchange.com/questions/550/exec-path-and-path
(use-package exec-path-from-shell)


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
  (setq line-number-mode nil)   ; Hide current line number from mode-line
  (setq save-interprogram-paste-before-kill t)
  (setq next-error-verbose nil) ; Hide "next-locus on <file> minibuffer messages that interfered with flycheck/eldoc"

  ;; INFO: Same as `newline' but withouth the (interactive "*" form):
  ;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Using-Interactive.html
  ;;  - If ‘*’ appears at the beginning of the string, then an error is signaled if the buffer is read-only.
  ;;  - This prevents signaling an error when pressing C-m (RET) if buffer is read-only
  ;;  i.e. var `buffer-read-only' was non-nil.
  ;;  - If this was the case, the function `larumbe/newline-advice' could not be used properly
  ;;  on read-only buffers to kill xref/help/ag popups since the read-only error had
  ;;  precedence over the call to `larumbe/newline-advice'. This seems to be implemented
  ;;  in C instead of Elisp and therefore is not possible to easily override it.
  ;;  - Plus, this function calls `barf-if-buffer-read-only' so the (interactive "*") check
  ;;  in C seems redundant.
  ;;
  ;; - Copied from <emacs-dir>/share/emacs/28.1/lisp/simple.el.gz
  ;; - Tried creating a `larumbe/newline' function and adding both
  ;; :override and :before-until advices to newline but did not seem to work,
  ;; (might be due to order of advice dependency).
  ;;
  (defun newline (&optional arg interactive)
    "Insert a newline, and move to left margin of the new line.
With prefix argument ARG, insert that many newlines.

If `electric-indent-mode' is enabled, this indents the final new line
that it adds, and reindents the preceding line.  To just insert
a newline, use \\[electric-indent-just-newline].

If `auto-fill-mode' is enabled, this may cause automatic line
breaking of the preceding line.  A non-nil ARG inhibits this.

If `use-hard-newlines' is enabled, the newline is marked with the
text-property `hard'.

A non-nil INTERACTIVE argument means to run the `post-self-insert-hook'."
    (interactive "P\np") ; DANGER: Only change with respect to original one
    (barf-if-buffer-read-only)
    (when (and arg
               (< (prefix-numeric-value arg) 0))
      (error "Repetition argument has to be non-negative"))
    ;; Call self-insert so that auto-fill, abbrev expansion etc. happen.
    ;; Set last-command-event to tell self-insert what to insert.
    (let* ((was-page-start (and (bolp) (looking-at page-delimiter)))
           (beforepos (point))
           (last-command-event ?\n)
           ;; Don't auto-fill if we have a prefix argument.
           (auto-fill-function (if arg nil auto-fill-function))
           (arg (prefix-numeric-value arg))
           (procsym (make-symbol "newline-postproc")) ;(bug#46326)
           (postproc
            ;; Do the rest in post-self-insert-hook, because we want to do it
            ;; *before* other functions on that hook.
            (lambda ()
              (remove-hook 'post-self-insert-hook procsym t)
              ;; Mark the newline(s) `hard'.
              (if use-hard-newlines
                  (set-hard-newline-properties
                   (- (point) arg) (point)))
              ;; If the newline leaves the previous line blank, and we
              ;; have a left margin, delete that from the blank line.
              (save-excursion
                (goto-char beforepos)
                (beginning-of-line)
                (and (looking-at "[ \t]+$")
                     (> (current-left-margin) 0)
                     (delete-region (point)
                                    (line-end-position))))
              ;; Indent the line after the newline, except in one case:
              ;; when we added the newline at the beginning of a line that
              ;; starts a page.
              (or was-page-start
                  (move-to-left-margin nil t)))))
      (fset procsym postproc)
      (if (not interactive)
          ;; FIXME: For non-interactive uses, many calls actually
          ;; just want (insert "\n"), so maybe we should do just
          ;; that, so as to avoid the risk of filling or running
          ;; abbrevs unexpectedly.
          (let ((post-self-insert-hook (list postproc)))
            (self-insert-command arg))
        (unwind-protect
            (progn
              (add-hook 'post-self-insert-hook procsym nil t)
              (self-insert-command arg))
          ;; We first used let-binding to protect the hook, but that
          ;; was naive since add-hook affects the symbol-default
          ;; value of the variable, whereas the let-binding might
          ;; protect only the buffer-local value.
          (remove-hook 'post-self-insert-hook procsym t))))
    nil)

  ;; Kill *ag*/*xref* and other active buffers with RET/C-m
  (advice-add 'newline :before-until #'larumbe/newline-advice))


(use-package menu-bar
  :straight nil
  :bind (("<f11>" . toggle-debug-on-error)))


(use-package hi-lock
  :straight nil
  :bind (("C-\\" . highlight-symbol-at-point)
         ("C-'" . unhighlight-regexp)))


(use-package elmacro
  :diminish elmacro-mode)


(use-package auto-highlight-symbol
  :bind (:map auto-highlight-symbol-mode-map
         ("M-<"     . ahs-backward)
         ("M->"     . ahs-forward)
         ("M--"     . ahs-back-to-start)
         ("C-x C-'" . ahs-change-range) ; This might be only function that I still do not know how to achieve with Isearch
         ("C-x C-a" . ahs-edit-mode))
  :config
  (setq ahs-default-range 'ahs-range-whole-buffer))


(use-package re-builder
  :config
  (setq reb-re-syntax 'read))  ;; Emacs double escaping (for single escaping use 'string)


(use-package man
  :straight nil
  :commands (Man-getpage-in-background) ; Used by `sh-script'
  :config
  (setq Man-notify-method 'pushy))


(use-package which-key
  :diminish)


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


;; API of `coin-ticker' was outdated. Also tried `crypto-ticker-mode' but was a bit more complex than this one
(use-package btc-ticker)


;; https://emacs.stackexchange.com/questions/14403/how-can-i-copy-syntax-highlighted-code-as-rtf-or-html
;; Steps:
;;  1 - Open *scratch* buffer and set proper major-mode
;;  2 - Copy code snippet to *scratch* buffer
;;  3 - Run `htmlize-buffer'
;;  4 - Copy text to file.html
;;  5 - In apps like Outlook (Insert as text)
;;
;; Considerations
;;  - If using `htmlize-region' directly on a non-scratch buffer the black background shows up (and not as a square)
;;  - Check if `modi/htmlize-region-to-file' is defined for my-elisp-packages
;;    + This one uses a CSS based on leuven css (light theme maybe more suitable for blank background emails)
;;  - Package `highlight2clipboard' did not support gnu/linux
(use-package htmlize)


;; Requires ImageMagick and makes use of binary "import"
;;
;; Prerequisites:
;; - /etc/ImageMagick-6/policy.xml
;; Change to:
;; <policy domain="coder" rights="read | write" pattern="PS" />
;;
;; Procedure:
;;  a) - `screenshot'
;;     - Set filename: file.png, file.jpg, etc...
;;     - Scheme: local (save in ~/images/ requires previous mkdir)
;;  b) After executing a:
;;     - `screenshot-take' (reuses previous filename and scheme)
(use-package screenshot)


;;;; Libraries
(use-package dash)
(use-package s)
(use-package f)
(use-package ht)
(use-package pcre2el)
(use-package with-editor)
(use-package request)
(use-package bind-key)
(use-package yaml
  :commands (yaml-parse-string
             yaml-encode-object)) ; Full Elisp, worse performance but portable
(use-package emacs-libyaml
  :straight (:host github :repo "syohex/emacs-libyaml")) ; Dinamic binding for libyaml.so


;;;; Functions & Utils
(use-package xah-lee-functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/xah-lee-functions.el")))

(use-package modi-functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/modi-functions.el"))
  :bind (("C-]" . modi/pull-up-line)))

(use-package others-functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/others-functions.el"))
  :bind (("C-x C-r" . er-sudo-edit)                       ; Unmap `find-file-read-only'
         ("C-x d"   . duplicate-current-line-or-region))) ; Replaces Dired (C-x C-j works better)

(use-package larumbe-functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/larumbe-functions.el"))
  :bind (("M-w"             . larumbe/copy-region-or-symbol-at-point) ; Overrides `kill-ring-save'
         ("C-z"             . larumbe/pop-to-previous-mark)           ; Unmaps suspending frame
         ("C-x C-z"         . larumbe/pop-to-previous-mark)           ; Unmaps suspending frame
         ("C-x C-/"         . larumbe/pwd-to-kill-ring)
         ("C-x C-,"         . larumbe/revert-buffer-maybe-no-confirm)
         ("C-M-<backspace>" . larumbe/kill-sexp-backwards)
         ("C-x C-h"         . larumbe/scratch-toggle)))

(use-package larumbe-macros
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("macros/larumbe-macros.el")))

(use-package fpga-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/fpga-utils.el")))


;;;; Provide package
(provide 'init-packages)

;;; init-packages.el ends here
