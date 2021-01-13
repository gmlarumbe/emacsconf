;;; init-prog-others.el --- Other prog languages  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; XML
(use-package nxml-mode
  :ensure nil
  :after (auto-complete)
  :hook ((nxml-mode . larumbe/xml-mode-hook)
         (nxml-mode . larumbe/prog-mode-hook)) ; Since it is not a child of prog-mode, requires common configuration settings
  :config
  (setq nxml-child-indent 4)

  (defun larumbe/xml-mode-hook ()
    (set 'ac-sources '(ac-source-gtags
                       ac-source-symbols))))


;;;; DOCBOOK
(use-package docbook-mode
  :ensure nil
  :mode (("\\.docbook\\.xml" . docbook-mode)))


;;;; VIVADO
(use-package vivado-utils
  :ensure nil
  :commands (vivado-xdc-mode
             larumbe/vivado-shell
             larumbe/vivado-shell-tcl-send-line-or-region-and-step
             larumbe/vivado-shell-auto-complete-mode)
  :mode (("\\.xdc\\'" . vivado-xdc-mode))
  :hook ((vivado-mode . my-vivado-mode-hook))
  :config
  (defun my-vivado-mode-hook ()
    (set 'ac-sources '(ac-source-gtags
                       ac-source-symbols))))


;;;; HTML
(use-package mhtml-mode
  :bind (:map mhtml-mode-map
              ("C-M-u" . sgml-skip-tag-backward)
              ("C-M-d" . sgml-skip-tag-forward))
  :hook ((mthml-mode . my-mhtml-mode-hook))
  :config
  (setq sgml-basic-offset 4) ; Indentation of parent mode
  (defun my-mhtml-mode-hook ()
    (set 'ac-sources
         '(ac-source-gtags
           ac-source-symbols)))

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
  :mode (("\\.service\\'"      . conf-mode)
         ("\\.sby\\'"          . conf-mode)
         ("\\reg.sim.files\\'" . conf-mode)
         )
  :hook ((conf-mode . larumbe/prog-mode-hook))) ; Since it is not a childe of prog-mode, requires common configuration settings


;;;; MAKEFILE
(use-package make-mode
  :mode (("\\.mf\\'" . makefile-mode))
  :ensure nil)


;;;; PERL
(defalias 'perl-mode 'cperl-mode)
;; Basic initial config
;;   - http://www.khngai.com/emacs/perl.php
;; Interactive console
;;   -https://stackoverflow.com/questions/73667/how-can-i-start-an-interactive-console-for-perl
(use-package cperl-mode)


;;;; JSON
(use-package json-mode)


;;;; GO!
(use-package go-mode)


;;;; MATLAB
(use-package matlab
  :ensure matlab-mode
  :defines (matlab-indent-function
            matlab-shell-command)
  :mode (("\\.m\\'" . matlab-mode))
  :config
  (setq matlab-indent-function t)
  (setq matlab-shell-command "matlab"))


;;;; NASL
(use-package nasl-mode
  :ensure nil)


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



(provide 'init-prog-others)

;;; init-prog-others.el ends here
