;;; init-python.el --- Python  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Elpy based configuration:
;;   - Provides tons of features but also overrid almost every keybinding.
;;   - Provides a company backend:
;;      - CAPF functions for `python-mode' are more related to shell, and only add gtags-completion-at-point (unnecessary)
;;      - This backend seems quite useful and uses jedi under the hood as well
;;   - Uses Jedi as a backend if available:
;;      - Could be installed through use-package jedi-core
;;      - Or through $ pip install jedi
;;   - Provides many functions for shell code evaluation
;;
;; Alternatives:
;;  - Python Language Server: https://github.com/palantir/python-language-server
;;    - Very good option, but also uses Jedi under the hood for most of its features.
;;    - References seem to be found by grepping, so no real improvement for my flow.
;;    - Also became quite slow on remote Emacs instances.
;;
;;; Code:

(use-package python-mode
  :mode (("\\SConstruct\\'"      . python-mode)
         ("\\SConstruct.repo\\'" . python-mode))
  :bind (:map python-mode-map
              ("C-c C-t" . larumbe/hydra-python-placeholder)   ; Unmaps `py-toggle-shell' which was not declared at the time of implementing...
              ("C-c C-f" . larumbe/flycheck-eldoc-mode))
  :init
  (setq py-pdbtrack-do-tracking-p nil) ; `python-mode' pdbtrack feature caused a BUG in window switching in gud/realgud when moving to next command in source window
  :config
  (setq python-check-command        "pylint")
  (setq py-number-face              font-lock-doc-face)
  (setq py-pseudo-keyword-face      font-lock-constant-face) ; True/False/None
  (setq py-try-if-face              font-lock-doc-face)
  (setq py-variable-name-face       font-lock-variable-name-face)
  (setq py-use-font-lock-doc-face-p t)
  ;; Utils
  (require 'python-utils)
  (require 'python-templates)
  ;; Customization
  (larumbe/python-fix-hs-special-modes-alist) ; BUG Fix (check function docstring for more info)
  ;; Overrides `hs-hide-all' (Error if declaring with use-package :bind - Key sequence C-c @  starts with non-prefix key C-c @
  (define-key python-mode-map "\C-c@\C-\M-h" #'larumbe/python-hs-hide-all)
  (advice-add 'py-newline-and-indent :before-until #'larumbe/newline-advice) ; Kill def/refs buffers with C-RET
  (defface larumbe/py-object-reference-face '((t (:foreground "dark olive green"))) "Face" :group 'python-faces) ; self. green face
  (setq py-object-reference-face 'larumbe/py-object-reference-face)
  ;; `python-mode' adds a defadvice to `pdb' that makes use of this variable
  (setq py-pdb-path (intern (executable-find "pdb"))))


(use-package jedi-core
  :after python-mode
  :demand
  :hook ((python-mode . jedi:setup))
  :bind (:map jedi-mode-map
         ("<C-tab>" . nil) ; Let C-tab to HideShow
         ;; Rely on `elpy' keybindings that use jedi as a backend
         ("M-."     . nil)
         ("M-,"     . nil)
         ("C-c ?"   . nil)
         ("C-c ."   . nil)
         ("C-c ,"   . nil))
  :config
  (defun larumbe/jedi-restart-server ()
    "Restart Jedi server.
Useful after changing the $PYTHONPATH (e.g. env switching)."
    (interactive)
    (message "Restarting all servers...")
    (jedi:stop-all-servers)
    (when (string= major-mode "python-mode")
      (message "Enabling jedi for current buffer..."))))


(use-package elpy
  :after python-mode
  :demand
  :hook ((elpy-mode . larumbe/elpy-hook))
  :bind (:map elpy-mode-map
         ("C-c RET" . nil) ; Unbind `elpy-importmagic-add-import', obsolete command
         ("C-c C-e" . nil) ; Unbind `elpy-multiedit-python-symbol-at-point', seems a useful command but better to rely on multiple cursors/ivy occurr and wgrep
         ("C-c C-f" . nil) ; Unbind `elpy-find-file', save space for `larumbe/python-flycheck-mode
         ("C-c C-n" . nil) ; Unbind `elpy-flymake-next-error', save space for `align-regexp'
         ("C-c C-p" . nil) ; Unbind `elpy-flymake-previous-error', save space for `larumbe/python-send-line-or-region', do research on
         ("C-c C-o" . nil) ; Unbind `elpy-occur-definitions', `imenu-list' already shows defs and classes
         ("C-c C-s" . nil) ; Unbind `elpy-rgrep-symbol', save space for `larumbe/yas-insert-snippet-dwim'
         ("C-c C-t" . nil) ; Unbind `elpy-test': runs "python3 -m unittest discover", but I have nothing implemented
         ("C-c C-v" . nil) ; Unbind `elpy-check': runs flake8 on current file, better through flycheck
         ("C-c C-r" . nil) ; Unbind `elpy-refactor-map'
         ("C-c C-x" . nil) ; Unbind `elpy-django-mode-map'

         ("<S-return>"   . nil) ; Unbind `elpy-open-and-indent-line-below'
         ("<C-S-return>" . nil) ; Unbind `elpy-open-and-indent-line-above'
         ("<C-return>"   . nil) ; Unbind `elpy-shell-send-statement-and-step'

         ("<C-down>"  . nil) ; Unbind `elpy-nav-forward-block'
         ("<C-up>"    . nil) ; Unbind `elpy-nav-backward-block'
         ("<C-left>"  . nil) ; Unbind `elpy-nav-backward-indent'
         ("<C-right>" . nil) ; Unbind `elpy-nav-forward-indent'
         ("<M-down>"  . nil) ; Unbind `elpy-nav-move-line-or-region-down': using `drag-stuff'
         ("<M-up>"    . nil) ; Unbind `elpy-nav-move-line-or-region-up': using `drag-stuff'
         ("<M-left>"  . nil) ; Unbind `elpy-nav-indent-shift-left'
         ("<M-right>" . nil) ; Unbind `elpy-nav-indent-shift-right'
         ("C-x 4 M-." . nil) ; Unbind `xref-find-definitions-other-window'
         ("M-*"       . nil) ; Unbind `xref-pop-marker-stack'
         ("M-TAB"     . nil) ; Unbind `elpy-company-backend'

         ("C-c C-l" . elpy-shell-send-statement-and-step)
         ("C-c C-b" . elpy-format-code)
         ("C-c ."   . elpy-goto-assignment)

         ("C-M-p"   . elpy-nav-backward-block)
         ("C-M-n"   . elpy-nav-forward-block)
         ("C-M-d"   . elpy-nav-forward-indent) ; Overrides `py-up' (not implemented at the time of overriding)
         ("C-M-u"   . elpy-nav-backward-indent) ; Overrides `py-down'
         ("C-c h"   . elpy-nav-indent-shift-left)   ; Vim-like
         ("C-c l"   . elpy-nav-indent-shift-right)) ; Vim-like
  :config
  (setq elpy-modules '(elpy-module-sane-defaults
                       elpy-module-pyvenv
                       elpy-module-company
                       elpy-module-eldoc
                       elpy-module-yasnippet))
  ;; Elpy automatically adds with highest precedence the `elpy-company-backend'.
  (setq elpy-eldoc-show-current-function nil) ; Already have `which-func'
  (elpy-enable)

  (defun larumbe/elpy-hook ()
    "Elpy hook."
    ;; Add higher precedence for `company-files' backend
    (setq-local company-backends (delete-dups (cons 'company-files (remove 'company-files company-backends))))))




(provide 'init-python)

;;; init-python.el ends here
