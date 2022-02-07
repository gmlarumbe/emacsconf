;;; init-prog-others.el --- Other prog languages  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; XML
(use-package nxml-mode
  :straight nil
  :hook ((nxml-mode . larumbe/prog-mode-keys)
         (nxml-mode . larumbe/prog-mode-hook)) ; Since it is not a child of prog-mode, requires common configuration settings
  :config
  (setq nxml-child-indent 4)

  ;; INFO: Relax NG validation through the following variables/modes:
  ;; `rng-nxml-auto-validate-flag' and `rng-validate-mode'

  (defun larumbe/rng-nxml-mode-init ()
    "Initialize `nxml-mode' to take advantage of `rng-validate-mode'.
This is typically called from `nxml-mode-hook'.
Validation will be enabled if `rng-nxml-auto-validate-flag' is non-nil."
    (interactive)
    (define-key nxml-mode-map "\C-c\C-v" 'rng-validate-mode)
    (define-key nxml-mode-map "\C-c\C-n" 'rng-next-error)
    ;; INFO: Removed all the keys that began with C-c C-s that conflicted with `larumbe/yas-insert-snippet-dwim':
    `rng-what-schema', `rng-auto-set-schema-and-validate', `rng-set-schema-file-and-validate', `rng-save-schema-location',
    `rng-set-document-type-and-validate'
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



;;;; DOCBOOK
;; Own package with some utils and hydra templates for DocBook
(use-package docbook-mode
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/docbook-mode.el"))
  :mode (("\\.docbook\\.xml" . docbook-mode)))

;; Written by Francis Litterio. Located at Sourceforge and characteristically inactive.
;; INFO: Haven't tested it, but left here if some of their functions can be taken as a reference.
(use-package docbook-xml-mode
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/docbook-xml-mode.el")))

;; Info-like viewer for DocBook
;; INFO: Gave it a try but got some errors with function `docbook-find-file'
(use-package docbook)



;;;; VIVADO
(use-package vivado-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/vivado-utils.el"))
  :mode (("\\.xdc\\'" . larumbe/vivado-xdc-mode)))


;;;; LATTICE DIAMOND
(use-package diamond-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/diamond-utils.el")))


;;;; HTML
(use-package mhtml-mode
  :bind (:map mhtml-mode-map
              ("C-M-u" . sgml-skip-tag-backward)
              ("C-M-d" . sgml-skip-tag-forward))
  :config
  (setq sgml-basic-offset 4) ; Indentation of parent mode

  (use-package web-beautify
    ;; Requires 'js-beautify' binary installed from npm (nodejs)
    :bind (:map mhtml-mode-map
                ("C-c b h" . web-beautify-html)
                ("C-c b j" . web-beautify-js)
                ("C-c b c" . web-beautify-css))))



;;;; MARKDOWN
(use-package markdown-mode
  :config
  (setq markdown-command "/usr/bin/pandoc -s"))


;;;; CONF
(use-package conf-mode
  :mode (("\\.service\\'"        . conf-mode)
         ("\\.sby\\'"            . conf-mode)
         ("\\reg\\.sim\\.files\\'" . conf-mode)
         )
  :hook ((conf-mode . larumbe/prog-mode-hook))) ; Since it is not a childe of prog-mode, requires common configuration settings


;;;; MAKEFILE
(use-package make-mode
  :mode (("\\.mf\\'" . makefile-mode))
  :straight nil)


;;;; PERL
(defalias 'perl-mode 'cperl-mode)
;; Basic initial config
;;   - http://www.khngai.com/emacs/perl.php
;; Interactive console
;;   -https://stackoverflow.com/questions/73667/how-can-i-start-an-interactive-console-for-perl
(use-package cperl-mode
  ;; Since it is not a child of prog-mode, requires common configuration settings
  :hook ((cperl-mode . larumbe/prog-mode-keys)
         (cperl-mode . larumbe/prog-mode-hook)))


;;;; JSON
(use-package json-mode)


;;;; GO!
(use-package go-mode)


;;;; MATLAB
(use-package matlab
  :straight matlab-mode
  :defines (matlab-indent-function
            matlab-shell-command)
  :mode (("\\.m\\'" . matlab-mode))
  :config
  (setq matlab-indent-function t)
  (setq matlab-shell-command "matlab"))


;;;; NASL
(use-package nasl-mode
  :straight (:host github :repo "tenable/emacs-nasl"))


;;;; Yocto
(use-package mmm-mode) ; Multi-major-mode
(use-package bitbake)  ; Recipes
(use-package dts-mode) ; Device tree


;;;; PHP
(use-package php-mode
  :bind
  (:map php-mode-map
        ;; Overrides `c-backward-conditional' but this is only used for interactive testing of PHP functions
        ;; Requires an interactive shell running in *ansi-term* buffer. Check 'phpsh' program.
        ("C-c C-p" . larumbe/sh-send-line-or-region-and-step-ansi)
        ;; INFO: For further sending to process, check `php-send-region' and `php-executable'
        ;; These functions execute the whole code at once, they do not run in an interactive inferior process
        )
  :config
  ;; Send to interactive shell in *ansi-term*
  (require 'sh-script-utils))


;;;; AHK
(use-package ahk-mode
  ;; DANGER: Even though it is defined as prog-mode derived, hooks are not automatically loaded
  :hook ((ahk-mode . larumbe/prog-mode-hook))
  :config
  (setq ahk-indentation 2))


;;;; CRON
(use-package crontab-mode)


;;;; YAML
(use-package yaml-mode)


;;;; SED
(use-package sed-mode)


;;;; CSV
(use-package csv-mode)


;;;; HEXL
(use-package hexl
  :straight nil
  :config
  ;; INFO: `hexl-mode' uses Emacs 'hexl' by default. Check `(executable-find "hexl")'
  ;; At some point I tried to add some options to `hexl-options' but only -de or -iso seemed possible.

  ;; Modify attributes of existing faces associated to font-lock, instead of declaring new ones
  (set-face-attribute 'hexl-address-region nil
                      :foreground "light green"
                      :inherit nil)
  (set-face-attribute 'hexl-ascii-region nil
                      :foreground "light yellow"
                      :inherit nil))


;;;; POLYMODE
;; https://polymode.github.io/defining-polymodes
(use-package polymode
  :mode (("\\.xml\\.ep\\'"           . poly-nxml-mode)
         ("reg\\.sim\\.files\\.ep\\'" . poly-conf-perl-mode)
         ("\\.ini\\'"               . poly-conf-c-mode))
  :hook (poly-nxml-mode . larumbe/poly-nxml-mode-hook)
  :config
;;;;; nXML + Perl
  (define-hostmode poly-nxml-hostmode
    :mode 'nxml-mode)

  (define-innermode poly-nxml-perl-innermode
    :mode 'perl-mode
    :head-matcher "%"
    :tail-matcher "\n"
    :head-mode 'host
    :tail-mode 'host)

  (define-polymode poly-nxml-mode
    :hostmode 'poly-nxml-hostmode
    :innermodes '(poly-nxml-perl-innermode))

  (defun larumbe/poly-nxml-mode-hook ()
    "nXML + Perl Hook."
    (interactive)
    (rng-validate-mode -1)) ; Do not parse Perl preprocessor headers in XML files


;;;;; Conf + Perl
  (define-hostmode poly-conf-hostmode
    :mode 'conf-mode)

  (define-innermode poly-conf-perl-innermode
    :mode 'perl-mode
    :head-matcher "%"
    :tail-matcher "\n"
    :head-mode 'host
    :tail-mode 'host)

  (define-polymode poly-conf-perl-mode
    :hostmode 'poly-conf-hostmode
    :innermodes '(poly-conf-perl-innermode)))


;;;;; Conf + C
  (define-hostmode poly-conf-c-hostmode
    :mode 'conf-mode)

  (define-innermode poly-conf-c-innermode
    :mode 'c-mode
    :head-matcher (cons "\\(?1:\\)#\\(if\\|else\\|endif\\|elsif\\|include\\|ITERATE\\)" 1) ; Capture group 1 is a hack to also include the #(word) inside the C mode
    :tail-matcher "\n"
    :head-mode 'host
    :tail-mode 'host)

  (define-polymode poly-conf-c-mode
    :hostmode 'poly-conf-c-hostmode
    :innermodes '(poly-conf-c-innermode))


(provide 'init-prog-others)

;;; init-prog-others.el ends here
