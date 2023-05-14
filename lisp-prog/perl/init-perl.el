;;; init-perl.el --- Init Perl  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Basic initial config
;;   - http://www.khngai.com/emacs/perl.php
;;
;; Interactive console
;;   - https://stackoverflow.com/questions/73667/how-can-i-start-an-interactive-console-for-perl
;;   - Try with `realgud:perldb' and `perldb'.
;;
;;; Code:

(defalias 'perl-mode 'cperl-mode)

(use-package cperl-mode
  :straight nil
  ;; Since it is not a child of prog-mode, requires common configuration settings
  :hook ((cperl-mode . larumbe/prog-mode-keys)
         (cperl-mode . larumbe/prog-mode-hook)
         (cperl-mode . eglot-ensure))
  :bind (:map cperl-mode-map
         ("TAB" . larumbe/cperl-indent-command))
  :init
  (setq cperl-font-lock t)
  :config
  (setq cperl-nonoverridable-face font-lock-builtin-face)
  ;; Approach of defvar+defface and (setq cperl-array-face larumbe/cperl-array-face) did not work, it seems cperl-mode has some font-lock specifics
  (set-face-foreground 'cperl-array-face "yellow green")
  (set-face-foreground 'cperl-hash-face "green")

  (defun larumbe/cperl-indent-command ()
    "Wrapper for `cperl-indent-command' to also indent regions with TAB."
    (interactive)
    (if (region-active-p)
        (call-interactively #'cperl-indent-region)
      (call-interactively #'cperl-indent-command))))


(provide 'init-perl)

;;; init-perl.el ends here
