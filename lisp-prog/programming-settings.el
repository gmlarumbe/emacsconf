;;; programming-settings.el --- Programming settings  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Common
(require 'programming-packages)

(use-package prog-mode
  :ensure nil
  ;; INFO: If declaring with :bind, the keybindings will be overriden by major-mode keybindings
  ;;       To override minor-mode keybindings, use :bind*
  ;;       To override major-mode derived keybindings, use prog-mode-hook
  :hook ((prog-mode . my-prog-mode-hook)
         (prog-mode . larumbe/prog-mode-keys))
  :config
  (require 'programming-utils))


;;;; Language-specific
(require 'verilog-settings)
(require 'vhdl-settings)
(require 'hdl-font-lock)
(require 'elisp-settings)
(require 'python-settings)
(require 'sh-script-settings)
(require 'tcl-settings)
(require 'c-settings)
(require 'programming-others-settings)



(provide 'programming-settings)

;;; programming-settings.el ends here
