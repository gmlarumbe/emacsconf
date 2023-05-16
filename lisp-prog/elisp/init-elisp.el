;;; init-elisp.el --- Elisp  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package elisp-mode
  :straight nil
  :diminish eldoc-mode
  :commands (larumbe/elisp-xref-set-dirs)
  :bind (:map emacs-lisp-mode-map
         ("C-c C-l" . larumbe/load-file-current-buffer)
         ("C-c C-t" . hydra-elisp/body)
         ("C-c C-e" . larumbe/edebug-defun)
         ("C-c c b" . larumbe/byte-compile-current-buffer-or-dir)
         ("C-c c n" . larumbe/native-compile-current-buffer-or-dir)
         ("C-c h"   . sanityinc/headerise-elisp)
         ("C-c t"   . larumbe/insert-time-stamp-elisp)
         ("C-M-z"   . eval-region)
         ("C-M-i"   . larumbe/elisp-indent-defun))
  :hook ((emacs-lisp-mode . larumbe/elisp-hook)
         (emacs-lisp-mode . easy-escape-minor-mode)
         (emacs-lisp-mode . larumbe/set-emacs-lisp-indentation))
  :config
  (require 'flycheck)
  (setq flycheck-emacs-lisp-load-path 'inherit)
  (setq flycheck-emacs-lisp-initialize-packages t)
  (require 'elisp-utils)
  (require 'elisp-templates))


(use-package edebug
  :straight nil
  :bind (:map edebug-mode-map
         ("?" . hydra-edebug/body)))


(use-package lively
  :after elisp-mode
  :bind (:map emacs-lisp-mode-map
         ("C-c l" . larumbe/lively-dwim))
  :config
  (setq lively-interval 1)

  (defun larumbe/lively-dwim (arg)
    "docstring"
    (interactive "P")
    (if arg
        (lively-stop)
      (if (region-active-p)
          (lively-region (region-beginning) (region-end))
        (lively)))))


(use-package easy-escape ; https://github.com/cpitclaudel/easy-escape
  :after elisp-mode
  :demand
  :diminish easy-escape-minor-mode)


(use-package eros
  :after elisp-mode
  :demand
  :config
  (eros-mode 1))


(use-package package-lint) ; Needed to submit packages to MELPA. Helpful to write other modes.


(use-package flycheck-package
  ;; Only enabled if package has comments with: "Version" "Package-Version" "Package-Requires"
  ;; i.e: `package-lint-looks-like-a-package-p' is t for `current-buffer'
  :after package-lint
  :demand
  :config
  (flycheck-package-setup))


(use-package command-log-mode
  :bind (:map emacs-lisp-mode-map
         ("C-c C-o" . hydra-command-log/body))
  :after elisp-mode
  :init
  ;; Do not bind `clm/open-command-log-buffer' by default to "C-c o"
  (setq command-log-mode-key-binding-open-log nil)
  :config
  (setq command-log-mode-window-size 60)

  (defhydra hydra-command-log (:color teal
                               :columns 6)
    "Command Log"
    ("c" command-log-mode "toggle mode")
    ("o" clm/open-command-log-buffer "open log buffer")
    ("l" clm/open-command-log-buffer "open log buffer")
    ("C" clm/command-log-clear "clear log buffer")
    ("t" clm/toggle-command-log-buffer "toggle log buffer")
    ("s" clm/save-command-log "save log")
    ("x" clm/close-command-log-buffer "close log buffer")
    ("q" nil "cancel" :color blue)))



(use-package el2markdown)



(provide 'init-elisp)

;;; init-elisp.el ends here
