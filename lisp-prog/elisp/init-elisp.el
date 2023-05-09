;;; init-elisp.el --- Elisp  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package elisp-mode
  :straight nil
  :diminish eldoc-mode
  :commands (larumbe/elisp-xref-set-dirs)
  :bind (:map emacs-lisp-mode-map
         ("C-c C-l"  . larumbe/load-file-current-buffer)
         ("C-c C-f"  . flycheck-mode)
         ("C-c C-t"  . hydra-elisp/body)
         ("C-c C-e"  . larumbe/edebug-defun)
         ("C-c C-o"  . hydra-command-log/body)
         ("C-c c b"  . larumbe/byte-compile-current-buffer-or-dir)
         ("C-c c n"  . larumbe/native-compile-current-buffer-or-dir)
         ("C-c h"    . sanityinc/headerise-elisp)
         ("C-c t"    . larumbe/insert-time-stamp-elisp)
         ("C-c l"    . larumbe/lively-dwim)
         ("C-M-z"    . eval-region)
         ("C-M-i"    . larumbe/elisp-indent-defun))
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
