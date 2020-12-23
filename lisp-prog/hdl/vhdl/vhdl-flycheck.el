;;; vhdl-flycheck.el --- VHDL Flycheck  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'vhdl-mode)
(require 'flycheck)
(require 'projectile)
(require 'vhdl-utils)


;; Fetched and adapted from Flycheck Verilator
;; INFO: Configured @ `my-vhdl-hook'
(flycheck-def-option-var flycheck-ghdl-include-path nil vhdl-ghdl
  "A list of include directories for GHDL

The value of this variable is a list of strings, where each
string is a directory to add to the include path of GHDL. "
  :type '(repeat (directory :tag "Include directory"))
  :safe #'flycheck-string-list-p
  :package-version '(flycheck . "32"))


;; Created to adapt GHDL to Xilinx libraries
(flycheck-def-option-var flycheck-ghdl-work-lib nil vhdl-ghdl
  "Work library name to be used for GHDL."
  :type '(choice (const :tag "Work library" nil)
                 (string :tag "Work library to be used (work, xil_defaultlib, etc...)"))
  :safe #'stringp
  :package-version '(flycheck . "32"))


;; Overrides the default @ flycheck.el
(flycheck-define-checker vhdl-ghdl
  "A VHDL syntax checker using GHDL.
See URL `https://github.com/ghdl/ghdl'."
  :command ("ghdl"
            "-s" ; only do the syntax checking
            (option "--std=" flycheck-ghdl-language-standard concat)
            (option "--workdir=" flycheck-ghdl-workdir concat)
            (option "--ieee=" flycheck-ghdl-ieee-library concat)
            (option "--work=" flycheck-ghdl-work-lib concat)
            (option-list "-P" flycheck-ghdl-include-path concat)
            source)
  :error-patterns
  ((error line-start (file-name) ":" line ":" column ": " (message) line-end))
  :modes vhdl-mode)



(defun larumbe/vhdl-flycheck-ghdl-hook ()
  "Set GHDL flycheck options."
  (setq flycheck-ghdl-include-path (larumbe/vhdl-list-directories-of-open-buffers))
  (setq flycheck-ghdl-language-standard "08")
  (setq flycheck-ghdl-work-lib vhdl-default-library) ; "xil_defaultlib"
  (setq flycheck-ghdl-workdir (concat (projectile-project-root) "library/" vhdl-default-library)) ; Used @ axi_if_converter
  (setq flycheck-ghdl-ieee-library "synopsys"))



(provide 'vhdl-flycheck)

;;; vhdl-flycheck.el ends here
