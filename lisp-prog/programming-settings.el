;;; programming-settings.el --- Programming settings  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(require 'ag-settings)
(require 'ggtags-settings)
(require 'ediff-wind)

;;; Common configuration
(use-package fic-mode
  :config
  (setq fic-activated-faces '(font-lock-doc-face  font-lock-comment-face))
  (setq fic-highlighted-words '("FIXME" "TODO" "BUG" "DANGER" "INFO" "NOTE"))

  (defun larumbe/clean-fic-keywords-dir ()
    "Perform an `ag-regexp' of `fic-mode' highlighted keywords in selected DIR
in order to check pending project actions. "
    (interactive)
    (let ((kwd (completing-read "Select keyword: " fic-highlighted-words))
          (path (read-directory-name "Directory: "))
          (files (completing-read "Select file regex: " '("(System)Verilog" "Python" "elisp")))
          (ag-arguments ag-arguments) ; Save the global value of `ag-arguments'
          (regex))
      (pcase files
        ("(System)Verilog" (setq regex ".[s]?v[h]?$")) ; +Headers
        ("Python"          (setq regex ".py$"))
        ("elisp"           (setq regex ".el$")))
      ;; ag glob search
      (setq ag-arguments (append ag-arguments '("-G")))
      (setq ag-arguments (append ag-arguments (list regex)))
      (ag-regexp kwd path))))


(use-package flycheck
  :commands (flycheck-display-error-messages-unless-error-list)
  :diminish
  :config
  (setq flycheck-display-errors-function ; Seems it shows full error if multiline
        #'flycheck-display-error-messages-unless-error-list))


(use-package flyspell
  :ensure nil
  :config
  (defun flyspell-toggle ()
    "Toggle flyspell mode on current buffer."
    (interactive)
    (if flyspell-mode
        (progn
          (flyspell-mode -1)
          (message "Flyspell disabled..."))
      (flyspell-mode 1)
      (message "Flyspell enabled..."))))


(use-package yasnippet
    :commands (yas-expand yas-reload-all)
    :diminish yasnippet yas-minor-mode
    :config
    ;; MELPA Snippets database
    (use-package yasnippet-snippets
      :config
      (defvar larumbe/major-modes-yasnippet-snippet-enabled
        '("prog-mode"
          "vhdl-mode"
          "c++-mode"
          "c-mode"
          "cc-mode"
          "perl-mode"
          "nxml-mode"
          "markdown-mode"
          "git-commit-mode")
        "Yasnippet-Snippets enabled snippets."))

    ;; `yasnippet-snippets' will add the directory of `yasnippet-snippets-dir' to
    ;; the list of available snippets. While it seems a good idea, it is better
    ;; to take it as a reference for building my own snippets to avoid conflicts
    ;; with some keybindings.
    (setq yas-snippet-dirs '("~/.elisp/snippets")) ; Limit snippets to those of my own to avoid name collisions
    ;; Load specific-mode snippets from `yasnippet-snippets'
    (dolist (mode larumbe/major-modes-yasnippet-snippet-enabled)
      (add-to-list 'yas-snippet-dirs (larumbe/path-join yasnippet-snippets-dir mode)))
    ;; DANGER: If more than one directory for a specific-mode is detected, only
    ;; the last one is taken into account.

    (define-key yas-minor-mode-map (kbd "TAB") nil) ; Use tab for indenting
    (define-key yas-minor-mode-map [tab] nil)

    ;; Load snippets
    (yas-reload-all)

    (defun larumbe/yas-insert-snippet-dwim (&optional arg)
      "Insert yasnippet snippet.
If universal ARG is provided, visit a snippet file."
      (interactive "P")
      (if arg
          (call-interactively #'yas-visit-snippet-file)
        (call-interactively #'yas-insert-snippet))))


(use-package hydra
  :config
  (defun larumbe/hydra-yasnippet (snippet)
    "Function/Macro to integrate YASnippet within Hydra."
    (interactive)
    (insert snippet)
    (yas-expand)))



(use-package diff-mode
  :bind (:map diff-mode-map
              ("M-o" . other-window)) ; Remove `M-o' binding (Overrides 'diff-goto-source, which is defined by `o' as well)
  :hook ((diff-mode . (lambda () (setq truncate-lines t)))
         (diff-mode . linum-mode))
  :config
  (setq ediff-split-window-function #'split-window-horizontally)
  (setq ediff-window-setup-function #'ediff-setup-windows-plain))


(use-package auto-complete
  :diminish
  :bind (:map ac-completing-map
              ("C-n" . ac-next)
              ("C-p" . ac-previous)
              ("C-j" . ac-complete)
              ("C-g" . ac-stop) ; Prevents aborting YAsnippet if occurs at the same time as autocompleting
              ("RET" . ac-complete))
  :config
  (setq ac-delay 1.3)
  ;; INFO: Auto-complete has 3 mode-maps: https://emacs.stackexchange.com/questions/3958/remove-tab-trigger-from-auto-complete
  (define-key ac-mode-map       (kbd "TAB") nil)
  (define-key ac-completing-map (kbd "TAB") nil)
  (define-key ac-completing-map [tab] nil)

  ;; AC-Sources
  ;; Default sources will be `ac-source-words-in-same-mode-buffers'

  ;; Provides `ac-source-gtags'
  (use-package auto-complete-gtags
    ;; :load-path "~/.elisp/download"
    :ensure nil
    :config
    (setq ac-gtags-modes '(c-mode cc-mode c++-mode verilog-mode emacs-lisp-mode vhdl-mode sh-mode python-mode tcl-mode)))

  ;; Provides `ac-source-verilog'
  (use-package auto-complete-verilog
    :ensure nil
    ;; :load-path "~/.elisp/download/"
    )
  )


(use-package imenu-list
  :config
  (setq imenu-list-size 0.15)
  (setq imenu-auto-rescan t))


(use-package hide-comnt
  :ensure nil
  ;; :load-path "~/.elisp/download/"
  )


(use-package rainbow-delimiters)


(use-package wide-column
  :commands (wide-column-mode))


(use-package prog-mode
  :ensure nil
  ;; INFO: If declaring with :bind, the keybindings will be overriden by major-mode keybindings
  ;;       To override minor-mode keybindings, use :bind*
  ;;       To override major-mode derived keybindings, use prog-mode-hook
  :hook ((prog-mode . my-prog-mode-hook)
         (prog-mode . larumbe/prog-mode-keys))
  :config
  (defun larumbe/prog-mode-definitions ()
    "Find definition of symbol at point.
If pointing a file, visit that file instead.

Selects between ggtags/xref to find definitions based on major-mode.

INFO: For some major-modes, xref will use global/ggtags as a backend
if configured. However, for elisp seems it's not the default engine,
as well as for C/C++ or Python..."
    (interactive)
    (let ((def (thing-at-point 'symbol)))
      (if (file-exists-p (thing-at-point 'filename))
          (larumbe/find-file-at-point)
        ;; If not pointing to a file choose between different navigation functions
        (cond
         ((string= major-mode "emacs-lisp-mode")
          (xref-find-definitions def))
         (t
          (call-interactively #'ggtags-find-tag-dwim))))))


  (defun larumbe/prog-mode-references ()
    "Find references of symbol at point.

Selects between ggtags/xref to find references based on major-mode.

INFO: For some major-modes, xref will use global/ggtags as a backend
if configured. However, for elisp seems it's not the default engine,
as well as for C/C++ or Python..."
    (interactive)
    (let ((ref (thing-at-point 'symbol)))
      (if (file-exists-p (thing-at-point 'filename))
          (larumbe/find-file-at-point)
        ;; If not pointing to a file choose between different navigation functions
        (cond
         ((string= major-mode "emacs-lisp-mode")
          (xref-find-references ref))
         (t
          (ggtags-find-reference ref))))))


  (defun larumbe/prog-mode-keys ()
    "Hook to set keys that will override the ones set in the derived major mode."
    (local-set-key (kbd "C-<tab>") #'hs-toggle-hiding)
    (local-set-key (kbd "C-c C-n") #'align-regexp)
    (local-set-key (kbd "C-c C-s") #'larumbe/yas-insert-snippet-dwim)
    (local-set-key (kbd "M-.")     #'larumbe/prog-mode-definitions)
    (local-set-key (kbd "M-?")     #'larumbe/prog-mode-references)
    (unless (or (string= major-mode "verilog-mode")
                (string= major-mode "emacs-lisp-mode"))
      (local-set-key (kbd "C-c C-f") #'flycheck-mode)))


  (defun my-prog-mode-hook ()
    "Basic Hook for derived programming modes."
    (ggtags-mode         1)
    (projectile-mode     1)
    (auto-complete-mode  1)
    (show-paren-mode     1)
    (linum-mode          1)
    (outshine-mode       1)
    (fic-mode            1)
    (yas-minor-mode      1)
    (hs-minor-mode       1)
    (auto-fill-mode      1)
    (wide-column-mode    1)
    (setq truncate-lines t)
    (setq fill-column    80)))


;;; Programming Languages Setups
(require 'verilog-settings)
(require 'vhdl-settings)
;; TODO: Temporary fix
;; (use-package hdl-font-lock
;;   :ensure nil
;;   :defer t
;;   :after verilog-settings
;;   )
(require 'hdl-font-lock)
;; End of TODO
(require 'elisp-settings)
(require 'python-settings)
(require 'sh-script-settings)
(require 'tcl-settings)
(require 'c-settings)
(require 'programming-others-settings)



(provide 'programming-settings)

;;; programming-settings.el ends here
