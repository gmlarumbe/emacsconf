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
  (setq fic-highlighted-words '("FIXME" "TODO" "BUG" "DANGER" "INFO"))

  (defun larumbe/clean-fic-keywords-dir ()
    "Perform an `ag-regexp' of `fic-mode' highlighted keywords in selected DIR
in order to check pending project actions. "
    (interactive)
    (let ((kwd (completing-read "Select keyword: " 'fic-highlighted-words))
          (path (read-directory-name "Directory: "))
          (files (completing-read "Select file regex: " '("(System)Verilog" "Python" "elisp")))
          (ag-arguments ag-arguments) ; Save the global value of `ag-arguments'
          (regex))
      (pcase files
        ("(System)Verilog" (setq regex ".[s]?v[h]?$")) ; +Headers
        ("Python"          (setq regex ".py$"))
        ("elisp"           (setq regex ".el$")))
      ;; ag glob search
      (add-to-list 'ag-arguments "-G"  :append)
      (add-to-list 'ag-arguments regex :append)
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


(use-package hydra
  :config
  (use-package yasnippet
    :commands (yas-expand yas-reload-all)
    :diminish yasnippet yas-minor-mode
    :config
    (defun larumbe/hydra-yasnippet (snippet)
      "Function/Macro to integrate YASnippet within Hydra."
      (interactive)
      (insert snippet)
      (yas-expand))

    ;; MELPA Snippets database
    (use-package yasnippet-snippets
      :config
      (defvar larumbe/major-modes-yasnippet-enabled '("perl-mode"
                                                      "cc-mode"
                                                      "c-mode"
                                                      "c++-mode"
                                                      "git-commit-mode"
                                                      "markdown-mode"
                                                      "vhdl-mode")
        "Yasnippet-Snippets enabled snippets."))

    ;; `yasnippet-snippets' will add the directory of `yasnippet-snippets-dir' to
    ;; the list of available snippets. While it seems a good idea, it is better
    ;; to take it as a reference for building my own snippets to avoid conflicts
    ;; with some keybindings.
    (setq yas-snippet-dirs '("~/.elisp/snippets")) ; Limit snippets to those of my own to avoid name collisions
    ;; Load specific-mode snippets from `yasnippet-snippets'
    (dolist (mode larumbe/major-modes-yasnippet-enabled)
      (add-to-list 'yas-snippet-dirs (larumbe/path-join yasnippet-snippets-dir mode)))
    (yas-reload-all)))


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
    :load-path "~/.elisp/download"
    :config
    (setq ac-gtags-modes '(c-mode cc-mode c++-mode verilog-mode emacs-lisp-mode vhdl-mode sh-mode python-mode tcl-mode)))

  ;; Provides `ac-source-verilog'
  (use-package auto-complete-verilog
    :load-path "~/.elisp/download/"))


(use-package imenu-list
  :config
  (setq imenu-list-size 0.15)
  (setq imenu-auto-rescan t))


(use-package hide-comnt
  :load-path "~/.elisp/download/")


(use-package rainbow-delimiters)


(use-package wide-column
  :commands (wide-column-mode))


(use-package prog-mode
  :ensure nil
  :commands (larumbe/ggtags-mode)
  :bind (:map prog-mode-map
              ("C-<tab>" . hs-toggle-hiding)
              ("C-c C-n" . align-regexp))
  :hook ((prog-mode . my-prog-mode-hook)
         (prog-mode . larumbe/prog-mode-keys))
  :config
  (defun larumbe/prog-mode-keys ()
    "Wrapper for flycheck-mode keybindings based on current major-mode"
    ;; Verilog has its own flycheck-mode wrapper function
    (unless (or (string-equal major-mode "verilog-mode")
                (string-equal major-mode "emacs-lisp-mode"))
      (local-set-key (kbd "C-c C-f") #'flycheck-mode)))

  (defun my-prog-mode-hook ()
    "Basic Hook for derived programming modes."
    (larumbe/ggtags-mode 1)
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
(require 'hdl-font-lock)
(require 'python-settings)
(require 'elisp-settings)
(require 'sh-script-settings)
(require 'c-settings)
(require 'tcl-settings)
(require 'programming-others-settings)



(provide 'programming-settings)

;;; programming-settings.el ends here
