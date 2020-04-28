;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BASIC CONFIGURATION FOR EMACS INIT FILE ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic settings
;;;; Basics
(server-start)                           ; Server start for emacsclient support
(load-theme 'deeper-blue t)              ; Load theme
(desktop-save-mode 1)                    ; Autosave Desktop
(setq confirm-kill-emacs 'y-or-n-p)      ; Avoid closing Emacs unexpectedly (helm prefix C-x c)
(setq inhibit-startup-screen t)          ; Inhibit startup screen
(setq disabled-command-function 'ignore) ; Enable all commands
(defalias 'yes-or-no-p 'y-or-n-p)        ; Globally set y-or-n-p

(setq line-number-mode nil)              ; Hide current line number from mode-line
(setq Man-notify-method 'pushy)          ; `man' utility config
(setq apropos-sort-by-scores t)          ; Apropos can sort results by relevancy. To enable this, add:
(setq align-default-spacing 1)           ; Align to 1 space
(setq align-to-tab-stop nil)             ;

(setq safe-local-variable-values
      '((eval larumbe/scons-error-regexp-set-emacs)  ; Compilation logs that highlight Vivado regexps by using eval at the header
        (eval larumbe/vivado-error-regexp-set-emacs) ; Compilation logs that highlight SCons regexp by using eavl at the header
        (aggressive-indent-mode)                     ; Verilog Modi-setup
        ))

;; Emacs customizations
(setq custom-file "~/.elisp/larumbe/custom-file.el")
(load custom-file)

;;;; Window/Frame Display
(menu-bar-mode -1)   ; Disable Menu bar
(tool-bar-mode -1)   ; Disable Tool bar
(scroll-bar-mode -1) ; Disable Scroll-bar (watch out percentage)

(setq display-time-default-load-average nil) ; Display time on the status bar
(display-time-mode t)


;;;; Load Path
(add-to-list 'load-path (expand-file-name "~/.elisp"))
(add-to-list 'load-path (expand-file-name "~/.elisp/download"))
(add-to-list 'load-path (expand-file-name "~/.elisp/larumbe/own-modes/majors/"))
(add-to-list 'load-path (expand-file-name "~/.elisp/larumbe/own-modes/minors/"))
(add-to-list 'load-path (expand-file-name "~/.elisp/larumbe/own-modes/override/"))


;;;; Untabify/delete trailing (conditionally and globally added to hooks)
(setq untabify-delete-trailing-whitespace t) ; Default initial value
;; Untabify on save-file (conditionally)
(when untabify-delete-trailing-whitespace
  (add-hook 'write-file-functions 'larumbe/untabify-trailing-whitespace))


;;; Built-in modes config
;;;; Generic
(electric-pair-mode t) ; Automatically write closing matching parenthesis/brackets

(when (fboundp 'winner-mode) ;The ‘fboundp’ test is for those XEmacs installations that don’t have winner-mode available.
  (winner-mode 1))
(winner-mode) ; Enable winner-mode by default


;;;; Org-Mode
;;;;; Variables
(setq org-log-done 'time)
(setq org-agenda-files (list "~/TODO.org"))
;;  Org Keywords
(setq org-todo-keywords
      '((sequence "TODO" "IN PROGRESS" "|" "DONE" "CANCELED" "POSTPONED")
        (sequence "|" "INFO")))
;;  Org Faces for Keywords
(setq org-todo-keyword-faces
      '(("TODO"        . org-warning)
        ("IN PROGRESS" . "yellow")
        ("CANCELED"    . (:foreground "blue" :weight bold))
        ("POSTPONED"   . "cyan")
        ("INFO"        . "light blue")
        ))

;;;;; Keymap
(defun my-org-mode-hook ()
  (local-set-key "\C-cl" 'org-store-link)
  (local-set-key "\C-ca" 'org-agenda)
  (local-set-key "\C-cc" 'org-capture)
  (local-set-key "\C-cb" 'org-iswitchb)
  (local-set-key (kbd "C-,") 'larumbe/ansi-term) ; Overrides org-cycle-agenda-files
  )
(add-hook 'org-mode-hook 'my-org-mode-hook)


;;;; vc-dir-mode
;;;;; Variables
(require 'vc-dir)
;;;;; Keymap
(define-key vc-dir-mode-map (kbd "e") 'vc-ediff) ; Overrides vc-find-file, already mapped to `f'
(define-key vc-dir-mode-map (kbd "C-x v p") 'svn-propedit) ; dsvn function 'exported' to be used as well with vc-mode
(add-hook 'vc-dir-mode-hook '(lambda () (setq truncate-lines t)))



;;;; dired
;;;;; Variables
(require 'dired)
(setq dired-bind-info nil)
;; Program mappings to dired-do-shell-command (overrides `dired-guess-shell-alist-default')
(setq dired-guess-shell-alist-user
      '(
        ("\\.pdf\\'" "okular")
        ))

;;;;; Keymap
;; INFO: Dired-x bounds I to Info when `dired-jump' C-x C-j is called
(define-key dired-mode-map (kbd "I") 'dired-kill-subdir) ;; Replaces `dired-info' when dired-x is enabled
(define-key dired-mode-map (kbd "b") 'dired-up-directory)
(define-key dired-mode-map (kbd "J") 'dired-goto-file) ; Switch from 'j' to 'J'
(define-key dired-mode-map (kbd "j") 'larumbe/dired-do-async-shell-command-okular) ;; Open file-at-point directly with Okular if is a PDF and delete async process window. Otherwise it will ask for default program
(define-key dired-mode-map (kbd "/") 'dired-narrow-regexp)
;; Dired deletion confirmer
;; https://superuser.com/questions/332590/how-to-prevent-delete-confirmation-in-emacs-dired
(define-key dired-mode-map (kbd ",") 'larumbe/toggle-dired-deletion-confirmer)

;;;;; Hooks
(add-hook 'dired-mode-hook '(lambda ()
                              (interactive)
                              (dired-hide-details-mode 1)))


