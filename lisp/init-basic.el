;;; init-basic.el --- Basic Config  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;; Server
(require 'server)
(unless (server-running-p)                     ; Server start for emacsclient support
  (server-start))

;; Custom-file
(setq custom-file "~/.emacs.d/custom-file.el") ; Custom file does not need to be in version control.
(unless (file-exists-p custom-file)            ; It will only hold a list with safe variables, `package-selected-packages' for autoremove and custom set variables.
  (write-region "" nil custom-file))           ; All of these are actually local to a machine.
(load custom-file)                             ; Create file if it doesn't exist in emacs directory, and load it

;; Global config
(load-theme 'deeper-blue t)                    ; Load theme
(desktop-save-mode 1)                          ; Autosave Desktop
(defalias 'yes-or-no-p 'y-or-n-p)              ; Globally set y-or-n-p
(setq confirm-kill-emacs #'y-or-n-p)           ; Avoid closing Emacs unexpectedly (helm prefix C-x c)
(setq inhibit-startup-screen t)                ; Inhibit startup screen
(setq initial-scratch-message nil)             ; Clear initial *scratch* message
(setq disabled-command-function 'ignore)       ; Enable all commands
(setq initial-major-mode 'fundamental-mode)    ; Avoid start *scratch* in `lisp-interaction-mode' and enabling default `prog-mode-hook.
(setq completions-detailed t)                  ; New in Emacs 28
(setq tab-width 4)                             ; TAB width (buffer local)

;; Save some screen real estate
(menu-bar-mode -1)
(when (featurep 'tool-bar)
  (tool-bar-mode -1))
(when (featurep 'scroll-bar)
  (scroll-bar-mode -1))

;; Conf tweaking variables
(defvar larumbe/gitignore-global-file (concat (getenv "HOME") "/.gitignore_global")) ; Variable used by `helm-rg', `counsel-rg' and `init-projectile'.
(defvar larumbe/completion-framework 'ivy) ; 'ivy or 'helm are allowed values (helm will coexist with `ivy-switch-buffer')

(defvar larumbe/emacs-conf-repos-core '("~/.elisp" "~/.elisp_private"))
(defvar larumbe/emacs-conf-repos-packages '("~/.emacs.d/straight/repos/my-elisp-packages"
                                            "~/.emacs.d/straight/repos/my-elisp-packages-priv"
                                            "~/.emacs.d/straight/repos/verilog-ext"
                                            "~/.emacs.d/straight/repos/vhdl-ext"
                                            "~/.emacs.d/straight/repos/tree-sitter-langs"
                                            ))
(defvar larumbe/emacs-conf-repos-devel (append larumbe/emacs-conf-repos-core larumbe/emacs-conf-repos-packages))
(defvar larumbe/emacs-conf-straight-forked
  '("~/.emacs.d/straight/repos/org-jira"           ; Keep forked: changes for non-Atlassian accounts
    "~/.emacs.d/straight/repos/yasnippet-snippets" ; Keep forked: get updates with --rebase
    "~/.emacs.d/straight/repos/jenkins.el"         ; Keep forked: deferred additions with some larumbe/
    "~/.emacs.d/straight/repos/magit-gerrit"       ; Keep forked: still untested
    "~/.emacs.d/straight/repos/arch-packer"        ; Maybe with some refactoring, updates after 5 years, no PR in this project. Wait until I get arch in new computer
    "~/.emacs.d/straight/repos/helm-navi"          ; PR pending review
    "~/.emacs.d/straight/repos/emacs"              ; TODO: Ticket to python-mode (larumbe/python-fix-hs-special-modes-alist) / vhdl-mode hierarchy error fixed in Emacs 29
    "~/.emacs.d/straight/repos/verilog-mode"       ; Development as a maintainer
    ;; TODO: Add PR to apheleia?
    ;; TODO: Add PR to tree-sitter-langs?
    ;; TODO: Add PR to aweshell?
    ;; TODO: Add PR to eglot
    )
  "Obtained through evaluation of: `(larumbe/git-check-forked-repos (larumbe/straight-packages))'")


;; Native compilation
;;   How to enable it:
;;   - Install libgccjit
;;   - Install libjansson (JSON native for lsp/eglot)
;;   - Build emacs: $ ./configure --with-native-compilation && make && make install
;;   - Check if it's enabled:
;;      - (native-comp-available-p) -> t
;;      - (functionp 'json-serialize) -> t
;;
;; (when (native-comp-available-p)
;;   (setq native-comp-deferred-compilation t)) ; Defer compilation of .elc loaded modules until they are used


(setq treesit--indent-verbose t)
(setq-default treesit-font-lock-level 4)



(provide 'init-basic)

;;; init-basic.el ends here
