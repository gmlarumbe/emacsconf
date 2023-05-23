;;; init-python.el --- Python  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Replaced MELPA `python-mode' with Bundled modles in `python' package:
;;  - More specifically with `python-ts-mode'
;;
;; Elpy based configuration:
;;   - Provides `xref' backend based on RPCs to jedi, to find definitions and references
;;   - Provides a company backend:
;;      - CAPF functions for `python-mode' are more related to shell
;;      - This backend seems quite useful and uses jedi under the hood as well
;;   - Provides tons of features but also override almost every keybinding.
;;      - Solved by remaping many of these
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

;; TODO: Remove after testing:
;; This was inside the :config section:
;;    Avoid conflicts with `python-ts-mode'
;;    INFO: From time to time, even with this uncommented, opening some .py buffers
;;    would open them in `python-mode'
;;    (delete '("\\.py[iw]?\\'" . python-mode) auto-mode-alist)

(use-package python
  :straight nil
  :mode (("\\.py[iw]?\\'" . python-ts-mode))
  :bind (:map python-ts-mode-map
         ("C-c C-v" . nil) ; Unmap `python-check', better use flycheck
         ("C-c C-t" . larumbe/python-hydra/body))
  :init
  (setq python-indent-offset 4)
  (setq python-indent-guess-indent-offset nil)
  (setq python-pdbtrack-activate nil) ; pdbtrack feature causes a BUG in window switching in gud/realgud when moving to next command in source window
  :config
  (require 'python-ts-font-lock)
  (require 'python-utils)
  (require 'python-templates)
  (define-key python-ts-mode-map [remap hs-hide-all] #'larumbe/python-hs-hide-all))


(use-package jedi-core
  :after python
  :demand
  :commands (larumbe/jedi-restart-server)
  :hook ((python-mode . jedi:setup))
  :bind (:map jedi-mode-map
         ("<C-tab>" . nil) ; Let C-tab to HideShow
         ;; Rely on `xref-utils' to navigate defs/refs
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
  :straight (:repo "jorgenschaefer/elpy"
             :fork (:repo "gmlarumbe/elpy" :branch "ts-mode"))
  :diminish
  :after python
  :demand
  :hook ((python-base-mode     . elpy-mode)
         (elpy-mode            . larumbe/elpy-hook)
         (inferior-python-mode . larumbe/inferior-python-elpy-hook))
  :bind (:map elpy-mode-map
         ("C-c RET" . nil) ; Unbind `elpy-importmagic-add-import', obsolete command
         ("C-c C-e" . nil) ; Unbind `elpy-multiedit-python-symbol-at-point', seems a useful command but better to rely on multiple cursors/ivy occurr and wgrep
         ("C-c C-f" . nil) ; Unbind `elpy-find-file', save space for `flycheck-mode'
         ("C-c C-n" . nil) ; Unbind `elpy-flymake-next-error', save space for `align-regexp'
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

         ("C-c C-p" . larumbe/elpy-shell-send-dwim) ; Unbind `elpy-flymake-previous-error', save space for `larumbe/python-send-line-or-region', do research on
         ("C-c C-l" . elpy-shell-send-statement-and-step)
         ("C-c C-b" . elpy-format-code)
         ("C-c ."   . elpy-goto-assignment)

         ("C-M-p"   . elpy-nav-backward-block)
         ("C-M-n"   . elpy-nav-forward-block)
         ("C-M-d"   . elpy-nav-forward-indent) ; Overrides `py-up' (not implemented at the time of overriding)
         ("C-M-u"   . elpy-nav-backward-indent) ; Overrides `py-down'
         ("C-c h"   . elpy-nav-indent-shift-left)   ; Vim-like
         ("C-c l"   . elpy-nav-indent-shift-right)) ; Vim-like
  :init
  (setq elpy-get-info-from-shell t) ; No need for `company-capf'
  :config
  (setq elpy-modules '(elpy-module-sane-defaults
                       elpy-module-company
                       elpy-module-eldoc
                       elpy-module-yasnippet))
  (setq elpy-eldoc-show-current-function nil) ; Already have `which-func'
  (elpy-enable)

  (defun larumbe/elpy-shell-send-dwim ()
    "Send region if active, otherwise send statement and step."
    (interactive)
    (if (region-active-p)
        (elpy-shell-send-region-or-buffer)
      (elpy-shell-send-statement-and-step)))

  (defun larumbe/elpy-hook ()
    "Elpy hook."
    ;; Overrides `larumbe/prog-mode-hook' that sets the `company-backends' value to `larumbe/company-backends-common'.
    ;; Plus, Elpy automatically adds with highest precedence the `elpy-company-backend'.
    (setq-local company-backends '(company-files elpy-company-backend))
    ;; `elpy' automatically re-enables auto-completion
    (setq company-idle-delay nil))

  (defun larumbe/inferior-python-elpy-hook ()
    "Inferior Python shell hook."
    ;; Allow `python' and `elpy' powered `company-capf' to be used in the shell
    (company-mode)
    (setq-local company-backends larumbe/company-backends-common)))



(provide 'init-python)

;;; init-python.el ends here
