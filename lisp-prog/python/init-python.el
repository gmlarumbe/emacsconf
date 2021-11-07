;;; init-python.el --- Python  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package python-mode
  :mode (("\\SConstruct\\'"      . python-mode)
         ("\\SConstruct.repo\\'" . python-mode))
  :bind (:map python-mode-map
              ;; NOTE: Some commands need to be redefined since python overrides prog-mode-map somehow...
              ("C-c C-p"     . larumbe/python-send-line-or-region) ; Overrides `run-python'
              ("C-c C-c"     . run-python)                         ; Overrides `python-shell-send-buffer'
              ("C-c C-t"     . larumbe/hydra-python-placeholder)   ; Unmaps `py-toggle-shell' which was not declared at the time of implementing...
              ("C-c RET"     . ac-complete-jedi-direct)
              ("C-M-n"       . forward-same-indent)
              ("C-M-p"       . backward-same-indent)
              ;; Send text to an *ansi-term* running a Python interpreter (that may run in a remote machine)
              ("C-c C-k"     . larumbe/python-send-line-or-region-ansi-term)
              ;; Send text to an *ansi-term* running a Python interpreter and ignore indentation (that may run in a remote machine)
              ("C-c C-l"     . larumbe/python-send-line-ansi-term-no-indent-ignore-comment)) ; Overrides `python-shell-send-file'
  :bind (:map jedi-mode-map
         ("<C-tab>" . nil) ; Let C-tab to HideShow
         ("C-c RET" . company-jedi))
  :config
  (setq python-check-command     "pylint")
  (setq py-number-face           font-lock-doc-face)
  (setq py-pseudo-keyword-face   font-lock-constant-face) ; True/False/None
  (setq py-try-if-face           font-lock-doc-face)
  (setq py-variable-name-face    font-lock-variable-name-face)
  (setq py-use-font-lock-doc-face-p t)
  (define-key python-mode-map "\C-c@\C-\M-h" #'larumbe/python-hs-hide-all) ; Overrides `hs-hide-all' (Error if declaring with use-package :bind - Key sequence C-c @  starts with non-prefix key C-c @

  (defface larumbe/py-object-reference-face '((t (:foreground "dark olive green"))) "Face" :group 'python-faces)
  (setq py-object-reference-face 'larumbe/py-object-reference-face)

  (require 'python-utils)
  (larumbe/python-fix-hs-special-modes-alist) ; BUG Fix (check function docstring for more info)
  (require 'python-templates)

  (use-package jedi-core
    :demand
    :config
    (use-package company-jedi)
    ;; Add 'company-jedi to `company-backends' list to autocomplete with <S-RET> instead of <C-c RET>
    (add-hook 'python-mode-hook #'jedi:setup))

  (use-package elpy)) ; INFO: Deserves some attention if some day Python becomes a priority


(provide 'init-python)

;;; init-python.el ends here
