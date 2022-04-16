;;; verilog-vars.el --- Verilog extra vars  -*- lexical-binding: t -*-
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

;;;; Modi
(defconst modi/verilog-identifier-re
  (concat "\\_<\\(?:"
          "\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)" ;simple identifier
          "\\|\\(?:\\\\[!-~]+\\)"               ;escaped identifier
          "\\)\\_>")
  "Regexp to match a valid Verilog/SystemVerilog identifier.

an identifier is used to give an object a unique name so it can be
referenced.  An identifier is either a simple identifier or an escaped
identifier.

A simple identifier shall be any sequence of letters, digits, dollar signs ( $ ),
and underscore characters ( _ ).

The first character of a simple identifier shall not be a digit or $ ; it can be
a letter or an underscore.  Identifiers shall be case sensitive.

For example:

  shiftreg_a
  busa_index
  error_condition
  merge_ab
  _bus3
  n$657

Escaped identifiers shall start with the backslash character ( \\ ) and end with
white space (space, tab, newline). They provide a means of including any of the
printable ASCII characters in an identifier (the decimal values 33 through 126,
or 21 through 7E in hexadecimal).

Neither the leading backslash character nor the terminating white space is
considered to be part of the identifier. Therefore, an escaped identifier \cpu3
is treated the same as a nonescaped identifier cpu3 .

For example:

  \\busa+index
  \\-clock
  \\***error-condition***
  \\net1/\\net2
  \\{a,b}
  \\a*(b+c)

IEEE 1800-2012 SystemVerilog Section 5.6 Identifiers, keywords,and system names.")

(defconst modi/verilog-identifier-pcre
  (concat "\\b"
          "([a-zA-Z_][a-zA-Z0-9$_]*)" ;simple identifier
          "|(\\\\[!-~]+\\s+)"            ;escaped identifier
          "\\b")
  "Perl regex to match a valid Verilog/SystemVerilog identifier.
This is a Perl regex equivalent of the Elips regexp in
`modi/verilog-identifier-re'.")

(defconst modi/verilog-module-instance-re
  (let* ((newline-or-space-optional "\\(?:[[:blank:]\n\r]\\)*")
         (newline-or-space-mandatory "\\(?:[[:blank:]\n\r]\\)+")
         (param-port-list "([^;]+?)"))
    (concat "^[[:blank:]]*"
            "\\(?1:" modi/verilog-identifier-re "\\)" ;module name (subgroup 1)
            newline-or-space-mandatory
            ;; optional port parameters
            "\\("
            "#" newline-or-space-optional param-port-list
            "\\([[:blank:]]*//.*?\\)*"  ;followed by optional comments
            "[^;\\./]+?"  ;followed by 'almost anything' before instance name
            "\\)*"
            "\\(?2:" modi/verilog-identifier-re "\\)" ;instance name (subgroup 2)
            newline-or-space-optional
            "(" ;And finally .. the opening parenthesis `(' before port list
            ))
  "Regexp to match valid Verilog/SystemVerilog module instance declaration.")


(defvar modi/verilog-block-end-keywords '("end"
                                          "join" "join_any" "join_none"
                                          "endchecker"
                                          "endclass"
                                          "endclocking"
                                          "endconfig"
                                          "endfunction"
                                          "endgroup"
                                          "endinterface"
                                          "endmodule"
                                          "endpackage"
                                          "endprimitive"
                                          "endprogram"
                                          "endproperty"
                                          "endsequence"
                                          "endtask")
  "Verilog/SystemVerilog block end keywords.
IEEE 1800-2012 SystemVerilog Section 9.3.4 Block names.")

(defvar modi/verilog-block-end-keywords-re
  (regexp-opt modi/verilog-block-end-keywords 'symbols)
  "Regexp to match the Verilog/SystemVerilog block end keywords.
See `modi/verilog-block-end-keywords' for more.")

(defvar modi/verilog-block-start-keywords '("begin"
                                            "fork"
                                            "checker"
                                            "class"
                                            "clocking"
                                            "config"
                                            "function"
                                            "covergroup"
                                            "interface"
                                            "module"
                                            "package"
                                            "primitive"
                                            "program"
                                            "property"
                                            "sequence"
                                            "task"
                                            )
  "Verilog/SystemVerilog block start keywords.

These keywords mirror the block end keywords (See `modi/verilog-block-end-keywords').")

(defvar modi/verilog-block-start-keywords-re
  (regexp-opt modi/verilog-block-start-keywords 'symbols)
  "Regexp to match the Verilog/SystemVerilog block start keywords.
See `modi/verilog-block-start-keywords' for more.")

(defconst modi/verilog-header-re
  (concat "^[[:blank:]]*"
          "\\([a-z]+[[:blank:]]+\\)*"   ;Optional virtual, local, protected
          "\\(?1:"                    ;Force group number to 1
          (regexp-opt '("case"
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
                      'symbols)
          "\\)"
          "[[:blank:]]+"
          "\\([a-z]+[[:blank:]]+\\)*"   ;Optional void, static, automatic, ..
          "\\(?2:"
          "\\(?:" modi/verilog-identifier-re "::\\)*" ;Allow parsing extern methods like class::task
          modi/verilog-identifier-re ;Block name, force group number to 2
          "\\)"
          "\\b"
          )
  "Regexp to match valid Verilog/SystemVerilog block header statement.")




;;;; Larumbe
(setq hdl-rx-verilog-simple-identifier (rx (or letter "_")
                                           (* (or letter digit "_" "$"))))

(setq hdl-rx-verilog-escaped-identifier (rx "\\" (+ (or "!" "-" "~"))))

(setq hdl-rx-verilog-identifier-re (rx symbol-start
                                       (or (regexp hdl-rx-verilog-simple-identifier)
                                           (regexp hdl-rx-verilog-escaped-identifier))
                                       symbol-end))

(setq hdl-rx-newline-or-space-optional  (rx (* (or blank
                                                   "\n"))))

(setq hdl-rx-newline-or-space-mandatory (rx (+ (or blank
                                                   "\n"))))

(setq hdl-rx-param-port-list (rx "("
                                 (opt (+ (not ";")))
                                 ")"))

(setq hdl-rx-verilog-module-instance-re
      (rx bol (* blank)
          (group-n 1 (regexp hdl-rx-verilog-identifier-re))
          (regexp hdl-rx-newline-or-space-optional)
          (* "#" (regexp hdl-rx-newline-or-space-optional) ; Change to optional?
             (regexp hdl-rx-param-port-list))
          ;; INFO: Excluded: "[^;\\./]+?"  ;followed by 'almost anything' before instance name exc
          ;; INFO: THe followed by almost anything
          (opt (1+ (not (or ";" "." "/"))))
          (group-n 2 (regexp hdl-rx-verilog-identifier-re))
          (* blank) (* "[" (+ not-newline) "]")
          (regexp hdl-rx-newline-or-space-optional)
          "("
          ))


(defvar hdl-rx-verilog-keywords-re (regexp-opt verilog-keywords 'symbols))

(defvar hdl-rx-verilog-token-re (regexp-opt '("module"
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defvar larumbe/verilog-module-instance-re
      (concat "^[[:blank:]]*"
              "\\(?1:" modi/verilog-identifier-re "\\)" ;module name (subgroup 1)
              larumbe/newline-or-space-optional ; For modi its mandatory, but thats a problem since it could be: btd#(
              ;; optional port parameters
              "\\("
              "#" larumbe/newline-or-space-optional larumbe/param-port-list
              "\\([[:blank:]]*//.*?\\)*"  ;followed by optional comments
              "[^;\\./]+?"  ;followed by 'almost anything' before instance name
              "\\)*"
              "\\(?2:" modi/verilog-identifier-re "\\)" ;instance name (subgroup 2)
              ;; Added by Larumbe
              "\\s-*\\(\\[.*\\]\\)*"         ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
              larumbe/newline-or-space-optional
              "(" ; And finally .. the opening parenthesis `(' before port list
              ))


(provide 'verilog-vars)

;;; verilog-vars.el ends here
