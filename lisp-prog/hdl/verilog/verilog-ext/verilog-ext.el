;;; verilog-ext.el --- Verilog Extensions  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;; TODO:
;;   - Clean verilog-utils
;;     - find-module-instance and get-header seem deprecable, based on other functions
;;     - Seems I prefer to use tokens instead of blocks/headers
;;   - The block-end-comments-to-block-names review, convert it to a minor-mode maybe?
;;   - What to do with the connect/disconnect/clean blanks ? Where to move? Editing is a nice place?
;;   - Move the regexps of compilation-utils to verilog-compile?
;;   - Overrides, maybe send Bug?
;;   - Navigation: review all of these and check if they work fine with/without shadowing
;;   - Indentation: Clean, remove the mode things
;;   - Imenu, check what can be reused and moved from/to other places (like navigation)
;;   - Vhier: clean, refactor
;;   - Remove larumbe/ functions and use generic ones (move to utils, use a variable that holds potential functions to do things)
;;   - Flycheck: good shape, but clean
;;   - Font-lock: reuse functions from the rest of the blocks
;;   - Clean up templates/hydra (use columns) and test if the rest work
;;   - Clean up code
;;   - Clean up/review functions doc
;;   - Check timestamp

;; (require 'verilog-rx)
;; ;; (require 'verilog-shadow)
;; (require 'verilog-completion)
;; (require 'verilog-navigation)
;; (require 'verilog-which-func)
;; (require 'verilog-hideshow)
;; (require 'verilog-utils)
;; (require 'verilog-beautify)
;; (require 'verilog-editing)
;; (require 'verilog-compile)
;; (require 'verilog-templates)
;; ;; TODO: This can be reduced to just remove blank spaces when detecting a outshine specific regexp in a particular line
;; ;; TODO: Set the variable for ignore custom regexp to "\\s-*//\\*"and the other to ignore multiline defines
;; ;; (require 'verilog-indentation)
;; (require 'verilog-imenu)
;; (require 'verilog-vhier)
;; (require 'verilog-flycheck)
;; (require 'verilog-font-lock)
;; (require 'verilog-timestamp) ; TODO: Change the 'work' section to a different name
;; (require 'verilog-compile) ; TODO: Add compilation regexp support for verilog here (as a derived compilation mode maybe?)
;; (require 'verilog-lsp)


(require 'verilog-utils)
(require 'verilog-completion)
(require 'verilog-navigation)
(require 'verilog-which-func)
(require 'verilog-hideshow)
(require 'verilog-beautify)
(require 'verilog-imenu)
;; (require 'verilog-templates) ; TODO: Revise thoroughly
;; (require 'verilog-compile) ; TODO: Rename to makefile? Add compilation regexps?




(provide 'verilog-ext)

;;; verilog-ext.el ends here
