;;; init-prog-others.el --- Other prog languages  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; XML
(use-package nxml-mode
  :straight nil
  :hook ((nxml-mode . larumbe/prog-mode-keys)
         (nxml-mode . larumbe/prog-mode-hook)) ; Since it is not a child of prog-mode, requires common configuration settings
  :init
  (setq nxml-child-indent 4)
  :config
  ;;  Relax NG validation through the following variables/modes:
  ;; `rng-nxml-auto-validate-flag' and `rng-validate-mode'
  (defun larumbe/rng-nxml-mode-init ()
    "Initialize `nxml-mode' to take advantage of `rng-validate-mode'.
This is typically called from `nxml-mode-hook'.
Validation will be enabled if `rng-nxml-auto-validate-flag' is non-nil."
    (interactive)
    (define-key nxml-mode-map "\C-c\C-v" 'rng-validate-mode)
    ;; INFO: Removed all the keys that began with C-c C-s that conflicted with `larumbe/yas-insert-snippet-dwim':
    `rng-what-schema', `rng-auto-set-schema-and-validate', `rng-set-schema-file-and-validate', `rng-save-schema-location',
    `rng-set-document-type-and-validate'
    ;; INFO: Removed the C-c C-n keybinding to allow the align regexp one
    (easy-menu-define rng-nxml-menu nxml-mode-map
      "Menu for nxml-mode used with rng-validate-mode."
      rng-nxml-easy-menu)
    (add-to-list 'mode-line-process
                 '(rng-validate-mode (:eval (rng-compute-mode-line-string)))
                 'append)
    (cond (rng-nxml-auto-validate-flag
           (rng-validate-mode 1)
           (add-hook 'completion-at-point-functions #'rng-completion-at-point nil t)
           (add-hook 'nxml-in-mixed-content-hook #'rng-in-mixed-content-p nil t))
          (t
           (rng-validate-mode 0)
           (remove-hook 'completion-at-point-functions #'rng-completion-at-point t)
           (remove-hook 'nxml-in-mixed-content-hook #'rng-in-mixed-content-p t))))

  ;; Override function
  (advice-add 'rng-nxml-mode-init :override #'larumbe/rng-nxml-mode-init))



;;;; Docbook
;; Own package with some utils and hydra templates for DocBook
(use-package docbook-mode
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/docbook-mode.el"))
  :mode (("\\.docbook\\.xml" . docbook-mode)))

;; Written by Francis Litterio. Located at Sourceforge and characteristically inactive.
;; Haven't tested it, but left here if some of their functions can be taken as a reference.
(use-package docbook-xml-mode
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/docbook-xml-mode.el")))

;; Info-like viewer for DocBook
;; Gave it a try but got some errors with function `docbook-find-file'
(use-package docbook)


;;;; SGML
(use-package sgml-mode
  :straight nil
  :commands (sgml-skip-tag-backward
             sgml-skip-tag-forward)
  :init
  (setq sgml-basic-offset 4))


;;;; HTML
(use-package mhtml-mode
  :bind (:map mhtml-mode-map
         ("C-M-u" . sgml-skip-tag-backward)
         ("C-M-d" . sgml-skip-tag-forward))
  :bind (:map html-mode-map
         ("M-o" . nil))) ; For some reason it bound M-o to `facemenu-keymap'


(use-package web-beautify ; Requires 'js-beautify' binary installed from npm (nodejs)
  :after mhtml-mode
  :bind (:map mhtml-mode-map
         ("C-c b h" . web-beautify-html)
         ("C-c b j" . web-beautify-js)
         ("C-c b c" . web-beautify-css)))


(use-package web-mode)


;;;; Markdown
(use-package markdown-mode
  :hook ((markdown-mode . larumbe/markdown-mode-hook))
  :mode (("\\.md\\'" . gfm-mode)) ; GitHub formatting mode
  :bind (:map markdown-mode-map
         ("M-." . markdown-follow-thing-at-point)
         ("C-M-{" . nil) ; Unmap `markdown-backward-block', leave space for `larumbe/shrink-window-vertically'
         ("C-M-}" . nil)) ; Unmap `markdown-forward-block', leave space for `larumbe/enlarge-window-vertically'
  :init
  (setq markdown-command "/usr/bin/pandoc -s")
  :config
  (defun larumbe/markdown-mode-hook ()
    "Markdown hook."
    (setq truncate-lines t)))


;;;; Conf
(use-package conf-mode
  :mode (("\\.service\\'" . conf-mode)
         ("\\.sby\\'"     . conf-mode)
         ("\\.f\\'"       . conf-mode)
         ("\\.ini\\'"     . conf-mode))
  :hook ((conf-mode . larumbe/prog-mode-hook))) ; Since it is not a childe of prog-mode, requires common configuration settings


;;;; Makefile
(use-package make-mode
  :mode (("\\.mf\\'" . makefile-mode)
         ("Makefile\\." . makefile-mode))
  :straight nil)


;;;; Rust
(use-package rust-mode)


;;;; JSON
;; `json-mode' seemed quite old, using Emacs 29.1 builtin js-json-mode
(use-package json-navigator)


;;;; Go!
(use-package go-mode)


;;;; Matlab
(use-package matlab
  :straight matlab-mode
  :mode (("\\.m\\'" . matlab-mode))
  :bind (:map matlab-mode-map
         ("M-s" . nil))) ; Unmap `matlab-show-matlab-shell-buffer' to allow for isearch/swiper


;;;; Nasl
(use-package nasl-mode
  :straight (:host github :repo "tenable/emacs-nasl"))


;;;; Yocto
(use-package mmm-mode) ; Multi-major-mode
(use-package bitbake)  ; Recipes
(use-package dts-mode) ; Device tree


;;;; PHP
(use-package php-mode
  :config
  ;; - Send to interactive shell (check 'phpsh' program).
  ;;   Configure in :config and not in :bind to avoid creating autoloads outside of its package
  ;; - Overrides `c-backward-conditional' but this is only used for interactive testing of PHP functions
  ;;   For further sending to process, check `php-send-region' and `php-executable'.
  ;;   These functions execute the whole code at once, they do not run in an interactive inferior process
  (define-key php-mode-map (kbd "C-c C-p") #'larumbe/sh-send-line-or-region-and-step-vterm))


;;;; AHK
(use-package ahk-mode
  ;; DANGER: Even though it is defined as prog-mode derived, hooks are not automatically loaded
  :hook ((ahk-mode . larumbe/prog-mode-hook))
  :init
  (setq ahk-indentation 2))


;;;; Cron
(use-package crontab-mode
  :hook ((crontab-mode . larumbe/crontab-hook))
  :config
  (defun larumbe/crontab-hook ()
    "Crontab hook"
    (setq truncate-lines t)))


;;;; Yaml
(use-package yaml-mode
  :hook ((yaml-mode . larumbe/prog-mode-hook)
         (yaml-mode . larumbe/prog-mode-keys)
         (yaml-mode . indent-guide-mode))
  :bind (:map yaml-mode-map
         ("C-M-n" . forward-same-indent)
         ("C-M-p" . backward-same-indent)
         ("C-M-u" . backward-to-indentation)
         ("C-M-d" . forward-to-indentation))
  :config
  ;; Do not add to :bind section to avoid creating autoload
  (define-key yaml-mode-map (kbd "C-c C-o") #'larumbe/yaml-shell-toggle))


;;;; Sed
(use-package sed-mode)

;;;; CSV
(use-package csv-mode)

;;;; INI
;; Tried with LindyDancer's `ini-mode', but it gave some errors in my config:
;; - It inherited from `prog-mode' but did not support hideshow
;; - Very simple, didn't provide any advatage over regular `conf-mode'

;;;; Hexl
(use-package hexl
  ;; INFO: `hexl-mode' uses Emacs 'hexl' by default. Check `(executable-find "hexl")'
  ;; At some point I tried to add some options to `hexl-options' but only -de or -iso seemed possible.
  :straight nil
  :config
  ;; Modify attributes of existing faces associated to font-lock, instead of declaring new ones
  (set-face-attribute 'hexl-address-region nil
                      :foreground "light green"
                      :inherit nil)
  (set-face-attribute 'hexl-ascii-region nil
                      :foreground "light yellow"
                      :inherit nil))


;;;; Specman/e
(use-package specman-mode
  :straight (:host github :repo "ooglyhLL/specman-mode")
  :commands (specman-mode)
  :mode (("\\.e\\'"    . specman-mode)
         ("\\.ecom\\'" . specman-mode)
         ("\\.erld\\'" . specman-mode)))


;;;; Jinja
(use-package jinja2-mode
  :hook ((jinja2-mode . larumbe/prog-mode-keys)
         (jinja2-mode . larumbe/prog-mode-hook))) ; Since it is not a child of prog-mode, requires common configuration settings


;;;; JavaScript
(use-package js
  :straight nil
  :hook ((js-mode . larumbe/js-hook))
  :config
  (defun larumbe/js-hook ()
    "Prevent cursor from moving to the beginning of indentation with C-p/C-n."
    (interactive)
    (setq-local goal-column nil)))


(provide 'init-prog-others)

;;; init-prog-others.el ends here
