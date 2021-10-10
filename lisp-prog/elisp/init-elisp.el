;;; init-elisp.el --- Elisp  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package elisp-mode
  :straight nil
  :diminish eldoc-mode
  :commands (larumbe/lively-dwim
             hydra-command-log/body)
  :bind (:map emacs-lisp-mode-map
         ("<return>" . larumbe/newline)
         ("C-c C-l"  . larumbe/load-file-current-buffer)
         ("C-c C-b"  . larumbe/byte-compile-current-buffer)
         ("C-c C-f"  . larumbe/elisp-flycheck-mode)
         ("C-c C-t"  . hydra-elisp/body)
         ("C-c C-e"  . larumbe/edebug-defun)
         ("C-c C-o"  . hydra-command-log/body)
         ("C-c h"    . sanityinc/headerise-elisp)
         ("C-c t"    . larumbe/insert-time-stamp-elisp)
         ("C-c l"    . larumbe/lively-dwim)
         ("C-M-z"    . eval-region))
  :hook ((emacs-lisp-mode . larumbe/elisp-hook)
         (emacs-lisp-mode . easy-escape-minor-mode)
         (emacs-lisp-mode . modi/set-emacs-lisp-indentation))
  :config
  (use-package edebug
    :straight nil
    :bind (:map edebug-mode-map
           ("?" . hydra-edebug/body)))

  (require 'flycheck)
  (setq flycheck-emacs-lisp-load-path 'inherit)
  (setq flycheck-emacs-lisp-initialize-packages t)

  (require 'elisp-utils)
  (require 'elisp-templates))


(provide 'init-elisp)

;;; init-elisp.el ends here
