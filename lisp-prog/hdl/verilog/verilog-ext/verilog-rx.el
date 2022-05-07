;;; verilog-rx.el --- Verilog Regexps  -*- lexical-binding: t -*-
;;; Commentary:
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


(setq verilog-ext-module-instance-re
  (rx-verilog
   (rx bol (* blank)                                     ; Initial optional blanks
       (group-n 1 verilog-identifier) newline-or-space*  ; Identifier
       (* "#" newline-or-space* verilog-param-port-list verilog-almost-anything-inside-port) ; Optional parameters
       ;; verilog-comments*                                 ; TODO: Review if this one is necessary
                      ; Parameter contents
       (group-n 2 verilog-identifier)                    ; Instance name
       (* blank) verilog-array-content newline-or-space* ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
       "("                                               ; Parenthesis before ports and connections
       )))


(defvar verilog-ext-keywords-re (regexp-opt verilog-keywords 'symbols))

(setq verilog-ext-token-re
  (regexp-opt
   '("module"
     "interface"
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
     "sequence"
     "`define")
   'symbols))



;; Modi, to find header (probably can be removed later)
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


;;;; Used by Imenu
;; Search by regexp: Used as regexps in `verilog-ext-imenu-generic-expression'
(defvar verilog-ext-imenu-top-re        "^\\s-*\\(?1:connectmodule\\|m\\(?:odule\\|acromodule\\)\\|p\\(?:rimitive\\|rogram\\|ackage\\)\\)\\(\\s-+automatic\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defvar verilog-ext-imenu-localparam-re "^\\s-*localparam\\(?1:\\s-+\\(logic\\|bit\\|int\\|integer\\)\\s-*\\(\\[.*\\]\\)?\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defvar verilog-ext-imenu-define-re     "^\\s-*`define\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defvar verilog-ext-imenu-assign-re     "^\\s-*assign\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defvar verilog-ext-imenu-generate-re   "^\\s-*generate[ \t\n]*\\(?1:.*\\)")
(defvar verilog-ext-imenu-always-re     "^\\s-*always\\(_ff\\|_comb\\|_latch\\)?\\s-*\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")
(defvar verilog-ext-imenu-initial-re    "^\\s-*initial\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")
;; Search by function: Used for functions that will be passed as an argument of `verilog-ext-imenu-generic-expression'
(defvar verilog-ext-task-re     "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*task\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?2:[A-Za-z_][A-Za-z0-9_:]+\\)")
(defvar verilog-ext-function-re "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*function\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?:\\w+\\s-+\\)?\\(?:\\(?:un\\)signed\\s-+\\)?\\(?2:[A-Za-z_][A-Za-z0-9_:]+\\)")
(setq verilog-ext-class-re    "\\(?1:\\(?:\\(?:virtual\\)\\s-+\\)?class\\)\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)")
(setq verilog-ext-top-re      "\\(?1:package\\|program\\|module\\|interface\\)\\(\\s-+automatic\\)?\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)")


;;;; Used by font-lock
;; Some regexps come from evaluated `(concat verilog-ext-identifier-re "\\s-+" verilog-ext-identifier-re)' with capture groups and additions depending on what they might detect.
(defvar verilog-ext-system-task-re "\\$[a-zA-Z][a-zA-Z0-9_\\$]*")
(defvar verilog-ext-port-connection-re "^[[:blank:]]*\\.\\([0-9a-zA-Z*_-]*\\)")
(defvar verilog-ext-dot-itf-struct-re "\\([a-zA-Z*_-][0-9a-zA-Z*_-]+\\)\\.\\([0-9a-zA-Z*_-]+\\)")
(defvar verilog-ext-braces-content-re "\\[\\(?1:[ +\*/()$0-9a-zA-Z:_-]*\\)\\]")
(defvar verilog-ext-width-signal-re "\\(?1:[0-9]*\\)'\\(?2:[hdxbo]\\)\\(?3:[0-9a-fA-F_xzXZ]+\\)")
(defvar verilog-ext-time-event-re "\\([@#]\\)")
(defvar verilog-ext-time-unit-re "[0-9]+\\(\\.[0-9]+\\)?\\(?2:[umnpf]s\\)")



(defvar verilog-ext-variable-re-1
  "\\_<\\(?1:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-+\\(?2:\\[.*\\]\\s-*\\)?\\_<\\(?3:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-*\\(\\[.*\\]\\)?\\s-*\\(?4:=.*\\)?;"
  "type_t asdf;
   type_t [10:0] asdf;
   type_t [10:0] asdf = 'h0;
")
(defvar verilog-ext-variable-re-2
  "\\_<\\(?1:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\_>\\s-+\\(?3:\\([a-zA-Z_][a-zA-Z0-9$_]*\\s-*,\\s-*\\)+\\([a-zA-Z_][a-zA-Z0-9$_]*\\s-*\\)\\);"
  "type_t asdf1, asdf2 , asdf4, asdf6[], asdf7 [25], asdf8 ;")
(defvar verilog-ext-variable-re-3
  "\\_<\\(input\\|output\\|inout\\|ref\\|parameter\\|localparam\\)\\_>\\s-+\\_<\\(?1:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-+\\(\\[.*\\]\\)?\\s-*\\_<\\(?3:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-*\\(\\[.*\\]\\)?\\s-*"
  " ...
  parameter type_t a = 1,
  localparam type_t b = 2
  ) .. (
  ...
  task foo(
      input type_t foo1,
      input bit [ 4:0] foo2,
      output type_t address,
      inout type_t data []
  );
 ")



(provide 'verilog-rx)

;;; verilog-rx.el ends here
