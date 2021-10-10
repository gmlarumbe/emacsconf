;;; init-prog.el --- Programming settings  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Common
(require 'prog-packages)

(use-package prog-mode
  :straight nil
  ;; INFO: If declaring with :bind, the keybindings will be overriden by major-mode keybindings
  ;;       To override minor-mode keybindings, use :bind*
  ;;       To override major-mode derived keybindings, use prog-mode-hook
  :hook ((prog-mode        . larumbe/prog-mode-hook)
         (prog-mode        . larumbe/prog-mode-keys)
         (before-save-hook . time-stamp))
  :config
  (require 'prog-utils))


;;;; Language-specific
(require 'init-verilog)
(require 'init-vhdl)
(require 'init-elisp)
(require 'init-python)
(require 'init-sh-script)
(require 'init-tcl)
(require 'init-c)
(require 'init-prog-others)



(provide 'init-prog)

;;; init-prog.el ends here
