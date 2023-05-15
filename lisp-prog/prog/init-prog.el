;;; init-prog.el --- Programming settings  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Common
(require 'prog-packages)

(use-package prog-mode
  :straight nil
  :hook ((prog-mode . larumbe/prog-mode-hook)
         (prog-mode . larumbe/prog-mode-keys)
         (prog-mode . remove-dos-eol))
  :config
  (require 'prog-utils))


;;;; Language-specific
(require 'init-verilog)
(require 'init-vhdl)

(use-package fpga-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/fpga-utils.el")))


(require 'init-elisp)
(require 'init-python)
(require 'init-sh-script)
(require 'init-tcl)
(require 'init-perl)
(require 'init-c)
(require 'init-prog-others)
(require 'init-polymode)


(provide 'init-prog)

;;; init-prog.el ends here
