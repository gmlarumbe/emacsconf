;;; verilog-rx.el --- Verilog Regexps  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; This file includes functions fetched from modi's modified `setup-verilog'
;; that are adviced to provide some extra/complementary functionality.
;;
;; It also includes hooks adding and modi's variable tweaking for personal customization.
;;
;;; Code:


;;;; Dependencies
(require 'verilog-mode)
(require 'rx)


;;;; Larumbe
(defmacro rx-verilog (&rest body-forms)
  `(rx-let ((newline-or-space+ (+ (or blank "\n")))
            (newline-or-space* (* (or blank "\n")))
            (keyword* (* (+ (char "a-z")) (+ blank)))
            (verilog-comments* (* (* blank) "//" (* nonl))) ; TODO: Review if this one is necessary
            (verilog-param-port-list (group "(" (opt (+ (not ";"))) ")"))
            (verilog-almost-anything-inside-port (group (opt (1+ (not (any ";./"))))))
            (verilog-array-content (group (* "[" (+ nonl) "]")))
            (verilog-identifier (group symbol-start
                                       (or (group (any letter "_") (* (any letter digit "_$"))) ; Simple identifier
                                           (group "\\" (+ letter)))                              ; Escaped identifier
                                       symbol-end)))
     ,@body-forms))


(defvar verilog-ext-module-instance-re
  (rx-verilog
   (rx bol (* blank)                                     ; Initial optional blanks
       (group-n 1 verilog-identifier) newline-or-space*  ; Identifier
       (* "#" newline-or-space* verilog-param-port-list) ; Optional parameters
       verilog-comments*                                 ; TODO: Review if this one is necessary
       verilog-almost-anything-inside-port               ; Parameter contents
       (group-n 2 verilog-identifier)                    ; Instance name
       (* blank) verilog-array-content newline-or-space* ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
       "("                                               ; Parenthesis before ports and connections
       )))


(defvar verilog-ext-keywords-re (regexp-opt verilog-keywords 'symbols))

(defvar verilog-ext-token-re
  (regexp-opt
   '("module"
     "program"
     "package"
     "class"
     "function"
     "task"
     "initial"
     "always"
     "always_ff"
     "always_comb"
     "generate"
     "property"
     "sequence")
   'symbols))



(defvar verilog-ext-header-words-re
  (regexp-opt
   '("case"
     "class"
     "clocking"
     "`define"
     "function"
     "group"
     "interface"
     "module"
     "program"
     "primitive"
     "package"
     "property"
     "sequence"
     "specify"
     "table"
     "task")
   'symbols))


(defvar verilog-ext-header-re
  (rx-verilog
   (rx bol (* blank) keyword* ; Optional virtual, local, protected
       (group-n 1 (regex verilog-ext-header-words-re))
       (+ blank) keyword* ;Optional void, static, automatic, ..
       ;; Allow parsing extern methods like class::task
       (group-n 2 (* verilog-identifier "::") verilog-identifier)
       word-boundary)))



(provide 'verilog-rx)

;;; verilog-rx.el ends here
