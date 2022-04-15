;;; verilog-vars.el --- Verilog extra vars  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; This file includes functions fetched from modi's modified `setup-verilog'
;; that are adviced to provide some extra/complementary functionality.
;;
;; It also includes hooks adding and modi's variable tweaking for personal customization.
;;
;;; Code:


;;;; Modi copied/Misc
(defconst modi/verilog-identifier-re
  (concat "\\_<\\(?:"
          "\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)" ;simple identifier
          "\\|\\(?:\\\\[!-~]+\\)"               ;escaped identifier
          "\\)\\_>")
  "Regexp to match a valid Verilog/SystemVerilog identifier.

An identifier is used to give an object a unique name so it can be
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


(defvar modi/verilog-keywords-re (regexp-opt verilog-keywords 'symbols)
  "Regexp to match reserved Verilog/SystemVerilog keywords.")



(provide 'verilog-vars)

;;; verilog-vars.el ends here
