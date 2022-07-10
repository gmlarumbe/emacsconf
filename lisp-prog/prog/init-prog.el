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
  :bind (("M-." . larumbe/prog-mode-definitions) ; Allow using it in non-prog modes (e.g. open files/URLs with fundamental/conf modes)
         ("M-?" . larumbe/prog-mode-references)) ; Let them being overriden by major-mode specific keybindings (e.g. `org-open-at-point')
  :hook ((prog-mode . larumbe/prog-mode-hook)
         (prog-mode . larumbe/prog-mode-keys)
         (prog-mode . remove-dos-eol))
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
(require 'init-polymode)


(provide 'init-prog)

;;; init-prog.el ends here
