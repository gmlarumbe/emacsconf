;;; verilog-templates.el --- Verilog Templates  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Many of these should be deprecated by Hydra+YASnippet
;;
;; Some customized functions extracted from `verilog-mode.el' and
;; tweaked to fulfill some specific functionality
;;
;; Had some issues trying to implement it with skeletons.
;; Finally decided on interactive functions.
;;
;;; Code:

(require 'verilog-mode)


;;;; Begin/end block
(defun verilog-ext-templ-begin-end ()
  "Insert begin/end block."
  (interactive)
  (electric-verilog-tab) ; Initial indent
  (insert "begin")
  (electric-verilog-terminate-line)
  (save-excursion
    (electric-verilog-terminate-line)
    (insert "end")
    (electric-verilog-tab))
  (electric-verilog-tab))


;;;; Comments
(defun verilog-ext-templ-block-comment ()
  "Create a Verilog comment block.

  ///////////////////
  // Block comment //
  ///////////////////
"
  (interactive)
  (let* ((block-comment-char 47) ; 47 = slash
         (block-comment (read-string "Name: "))
         (block-comment-width (string-width block-comment)))
    (electric-verilog-tab) ; Initial indent
    ;; Top line
    (insert-char block-comment-char (+ block-comment-width 6))
    (electric-verilog-terminate-line)
    ;; Comment line
    (insert-char block-comment-char 2)
    (insert " ")
    (insert block-comment)
    (insert " ")
    (insert-char block-comment-char 2)
    (electric-verilog-terminate-line)
    ;; Bottom line
    (insert-char block-comment-char (+ block-comment-width 6) nil)
    (electric-verilog-terminate-line)))


;;;; Case
(defun verilog-ext-templ-case ()
  "Fetched and modified from `verilog-state-machine-add-case-fold' for sync FSMs."
  (interactive)
  (let (param-read)
    (insert "case (" (read-string "Expression: ") ")") (electric-verilog-terminate-line)
    (while (not (string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (insert (concat param-read ": begin"))           (electric-verilog-terminate-line)
      (insert (concat "// Output statements... "))     (electric-verilog-terminate-line)
      (insert (concat "end"))                          (electric-verilog-terminate-line)
      (electric-verilog-terminate-line))
    (insert "endcase")
    (electric-verilog-terminate-line)))


;;;; Enum, Typedef, Struct
(defun verilog-ext-templ--compute-vector-width ()
  "Return [width-1:0] as a string for enum/struct templates.
If a number is set, then calculus will be automatically performed.
If set to 0 or 1, then do not set a vector.
If a constant is set, then it will be set to [CONSTANT-1:0].

DANGER: If width introduced is 0, it will be assumed as a human mistake and width 1 will be computed."
  (let (width-str width-num)
    (setq width-str (read-string "Width: "))
    (setq width-num (string-to-number width-str))
    ;; Corner case if width 0 or no width is introduced (assume 1)
    (when (or (string-equal width-str "0") (string-equal width-str ""))
      (setq width-num 1))
    ;; End of corner case
    (if (not (eq width-num 0)) ; width was a number different from 0, not a constant
        (if (> width-num 1)    ; Greater than 1 (i.e. a vector with brackets)
            (progn
              (setq width-num (1- width-num))
              (setq width-str (number-to-string width-num))
              (setq width-str (concat "[" width-str ":0]")))
          (setq width-str "")) ; Width was 1, just a signal without brackets
      (setq width-str (concat "[" width-str "-1:0]"))))) ;; If width was not a number but a constant, format properly [width-1:0]


(defun verilog-ext-templ-enum-typedef (&optional typedef)
  "Insert enum contents for TYPEDEF enum template."
  (let ((width "")
        (enum-types '("logic" "bit" "int" "integer" "other"))
        enum-item type)
    ;; Set typedef if specified
    (when typedef
      (insert "typedef "))
    ;; Select type for enum
    (setq type (completing-read "Type: " enum-types))
    (if (string-equal type "other")
        (setq type (read-string "Type: ")))
    ;; Select width
    (if (or (string-equal type "logic")
            (string-equal type "bit"))
        (setq width (verilog-ext-templ--compute-vector-width))
      (setq width "")) ; If not a vector disable width field
    (insert "enum " type width " {")
    (while (not (string-equal (setq enum-item (read-string "Item: ")) "")) ; Empty string ends with item addition
      (insert enum-item ", "))
    ;; Last item
    (delete-char -2)
    (insert "} ")
    ;; Name
    (if typedef
        (insert (read-string "Type Name: ") ";") ; Typedef
      (insert (read-string "Enum Name: ") ";"))  ; Enum
    (electric-verilog-terminate-line)))


(defun verilog-ext-templ-struct-typedef (&optional typedef union)
  "Insert struct contents for TYPEDEF struct template.
If UNION is non-nil, instantiate a union."
  (let (struct-item type (width ""))
    ;; Set typedef if specified
    (when typedef
      (insert "typedef "))
    ;; Struct Header
    (if union
        (insert "union ")
      (insert "struct "))
    (when (yes-or-no-p "Packed?")
      (insert "packed "))
    (insert "{")
    (electric-verilog-terminate-line)
    ;; Struct fields
    (while (not (string-equal (setq struct-item (read-string "Item: ")) "")) ; Empty string ends with item addition
      (setq type (read-string "Type: " "logic"))
      ;; Select width
      (if (or (string-equal type "logic") (string-equal type "bit"))
          (setq width (verilog-ext-templ--compute-vector-width))
        (setq width "")) ; If not a vector disable width field
      (insert type " " width " " struct-item ";")
      (electric-verilog-terminate-line))
    (insert "} ")
    ;; Struct Name
    (if typedef
        (insert (read-string "Type Name: ") ";")   ; Typedef
      (insert (read-string "Struct Name: ") ";"))  ; Enum
    (electric-verilog-terminate-line)))


;;;; Task
(defun verilog-ext-templ-task--add-port (direction read)
  "Add inputs to task template.
DIRECTION should be either 'input' or 'output'.
READ is assumed to be the signal name."
  (let (type width)
    ;; Select type
    (setq type (read-string "Type: " "logic"))
    ;; Select width
    (if (or (string-equal type "logic") (string-equal type "bit"))
        (setq width (verilog-ext-templ--compute-vector-width))
      (setq width "")) ; If not a vector disable width field
    ;; Insert port
    (insert direction " " type " " width " " read ",")
    (electric-verilog-terminate-line)))


(defun verilog-ext-templ-task ()
  "Insert a task definition."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (in-read)
        (out-read))
    (insert "task ")
    (insert (read-string "Task name: ") " (")
    (electric-verilog-terminate-line)
    (while (not(string-equal (setq in-read (read-string "Input signal: ")) ""))
      (verilog-ext-templ-task--add-port "input" in-read))
    (while (not(string-equal (setq out-read (read-string "Output signal: ")) ""))
      (verilog-ext-templ-task--add-port "output" out-read))
    ;; INFO: "inout" or "ref" could be added in the future via universal-arg
    (insert ");") (electric-verilog-terminate-line)
    (save-excursion
      (electric-verilog-terminate-line)
      (insert (concat "endtask"))
      (electric-verilog-terminate-line)
      (electric-verilog-tab))
    ;; Align port declarations
    (re-search-backward "(")
    (beginning-of-line)
    (forward-line)
    (verilog-pretty-declarations)
    (re-search-forward ");")
    (forward-line)
    (electric-verilog-tab)))


;;;; Signal definition
(defun verilog-ext-templ-def-logic--insert (sig)
  "Replace `verilog-sk-def-reg' for use within `verilog-ext-templ-def-logic'.
Define a 'logic' signal named SIG."
  (let (width str)
    (split-line) ;; Keep indentation
    (setq width (verilog-ext-templ--compute-vector-width))
    (setq str (concat "logic " width " " sig ";"))
    (insert str)
    (message (concat "[Line " (format "%s" (line-number-at-pos)) "]: " str))))


(defun verilog-ext-templ-def-logic ()
  "Insert a definition of signal under point at top of module.
INFO: Inspired from `verilog-sk-define-signal'."
  (interactive "*")
  (let* ((sig-re "[a-zA-Z0-9_]*")
         (sig (buffer-substring
               (save-excursion
                 (skip-chars-backward sig-re)
                 (point))
               (save-excursion
                 (skip-chars-forward sig-re)
                 (point)))))
    (if (not (member sig verilog-keywords))
        (save-excursion
          (verilog-beg-of-defun)
          (verilog-end-of-statement)
          (verilog-forward-syntactic-ws)
          (verilog-ext-templ-def-logic--insert sig))
      (message "object at point (%s) is a keyword" sig))))


;;;; FSM
(defvar verilog-ext-templ-fsm-reset "Rst_n")
(defvar verilog-ext-templ-fsm-clock "Clk")
(defvar verilog-ext-templ-fsm-param-pos nil)


(defun verilog-ext-templ-fsm--prompt-reset ()
  "Prompt for the name of an FSM reset."
  (setq verilog-ext-templ-fsm-reset (read-string "Active Low Reset Name: " "Rst_n")))

(defun verilog-ext-templ-fsm--prompt-clock ()
  "Prompt for the name of an FSM clock."
  (setq verilog-ext-templ-fsm-clock (read-string "Posedge clock name: " "Clk")))


(defun verilog-ext-templ-fsm--add-case (param-read)
  "Fill cases within the next state and output logic.
Declare them as parameters according to PARAM-READ at the beginning of the FSM.

INFO: One parameter keyword per declaration."
  (save-excursion
    (goto-char verilog-ext-templ-fsm-param-pos)
    (electric-verilog-terminate-line)
    (insert (concat "parameter " param-read " = " (read-string "Param value: ") ";"))
    (setq verilog-ext-templ-fsm-param-pos (point))))


(defun verilog-ext-templ-fsm-async ()
  "Insert a state machine custom definition with two always blocks.
One for next state and output logic and one for the state registers."
  (interactive)
  (let ((param-read)
        (state (read-string "Name of state variable: " "state")))
    (electric-verilog-tab) ; Initial indent
    (insert (concat "// State registers for " state))                                                                                         (electric-verilog-terminate-line)
    (insert (concat "reg [" (read-string "msb: " "31") ":" (read-string "lsb: " "0") "] " state ", next_" state ";"))
    (setq verilog-ext-templ-fsm-param-pos (point))                                                                                            (electric-verilog-terminate-line)
                                                                                                                                              (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " state))                                                                                                (electric-verilog-terminate-line)
    (insert (concat "always @ (posedge " (verilog-ext-templ-fsm--prompt-clock) " or negedge " (verilog-ext-templ-fsm--prompt-reset) ") begin")) (electric-verilog-terminate-line)
    (insert (concat "if (!" verilog-ext-templ-fsm-reset ")"))                                                                                 (electric-verilog-terminate-line)
    (insert (concat state " <= IDLE;"))                                                                                                       (electric-verilog-terminate-line)
    (insert (concat "else"))                                                                                                                  (electric-verilog-terminate-line)
    (insert (concat  state " <= next_" state ";"))                                                                                            (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                   (electric-verilog-terminate-line)
                                                                                                                                              (electric-verilog-terminate-line)
    ;; Next state and output logic
    (insert (concat "// Output and next State Logic for " state))                                                                             (electric-verilog-terminate-line)
    (insert (concat "always @ (posedge " verilog-ext-templ-fsm-clock  " or negedge " verilog-ext-templ-fsm-reset  ") begin"))                 (electric-verilog-terminate-line)
    (insert (concat "if (!" verilog-ext-templ-fsm-reset ") begin"))                                                                           (electric-verilog-terminate-line)
    (insert (concat "next_" state " <= IDLE;"))                                                                                               (electric-verilog-terminate-line)
    (insert (concat "// Output resets..."))                                                                                                   (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                   (electric-verilog-terminate-line)
    (insert (concat "else begin"))                                                                                                            (electric-verilog-terminate-line)
    (insert (concat "case (" state ") "))
    ;; Case reading
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (verilog-ext-templ-fsm--add-case  param-read)                                                                                            (electric-verilog-terminate-line)
      (insert (concat param-read ": begin"))                                                                                                  (electric-verilog-terminate-line)
      (insert (concat "// Output statements... "))                                                                                            (electric-verilog-terminate-line)
      (insert (concat "next_" state " <= <state>;"))                                                                                          (electric-verilog-terminate-line)
      (insert (concat "end"))                                                                                                                 (electric-verilog-terminate-line))
    (insert (concat "endcase"))                                                                                                               (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                   (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                   (electric-verilog-terminate-line)))


(defun verilog-ext-templ-fsm-sync--add-case-fold (param-read pfx idx)
  "Fill cases within the next state and output logic.
Declare them as parameters according to PARAM-READ at the beginning of the FSM.
Insert prefix PFX (4'hx or 1'bz) along with IDX.

Parameter keyword is used only once, improving readability."
  (save-excursion
    (goto-char verilog-ext-templ-fsm-param-pos)
    (delete-char -1)
    (insert ",")
    (electric-verilog-terminate-line)
    (insert (concat param-read " = " (read-string "Param value: " (concat pfx (number-to-string idx) ";"))))
    (setq verilog-ext-templ-fsm-param-pos (point))))



(defun verilog-ext-templ-fsm-sync--get-prefix (msb-str lsb-str)
  "Get prefix depending on the FSM state width.
This prefix will include MSB-STR and LSB-STR.

For the time being, since not very complex FSMs are being immplemented,
just binary and hexadecimal prefix are returned.
Return only \"4'h.\" or \"1'b.\" depending on msb and lsb."
  (let (width msb lsb)
    (setq msb (string-to-number msb-str))
    (setq lsb (string-to-number lsb-str))
    (setq width (-  msb  lsb))
    (if (/= (% (1+ width) 4) 0)
        (message "1'b")
      (message "4'h"))))


(defun verilog-ext-templ-fsm-sync ()
  "Insert a state machine custom definition with two always blocks.
One for next state and output logic and one for the state registers.

Improves `verilog-ext-templ-fsm-async' with automatic
reset state insertion and automatic parameter width insertion."
  (interactive)
  (let ((param-read)
        (rst-state-name)
        (msb)
        (lsb)
        (pfx)
        (idx 0)
        (state (read-string "Name of state variable: " "state")))
    (electric-verilog-tab) ; Initial indentation
    (insert (concat "// State registers for " state))                                                                                        (electric-verilog-terminate-line)
    (insert (concat "logic [" (setq msb (read-string "msb: " "3")) ":" (setq lsb (read-string "lsb: " "0")) "] " state ", next_" state ";")) (electric-verilog-terminate-line)
    (setq pfx (verilog-ext-templ-fsm-sync--get-prefix msb  lsb))
    (insert (concat "localparam " (setq rst-state-name (read-string "Reset State Name: " "IDLE"))  " = " (read-string "Reset Value: " (concat pfx "0;"))))
    (setq verilog-ext-templ-fsm-param-pos (point))                                                                                           (electric-verilog-terminate-line)
                                                                                                                                             (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " state))                                                                                               (electric-verilog-terminate-line)
    (insert (concat "always_ff @ (posedge " (verilog-ext-templ-fsm--prompt-clock) ") begin"))                                                (electric-verilog-terminate-line)
    (insert (concat "if (!" verilog-ext-templ-fsm-reset ")"))                                                                                (electric-verilog-terminate-line)
    (insert (concat state " <= " rst-state-name ";"))                                                                                        (electric-verilog-terminate-line)
    (insert (concat "else"))                                                                                                                 (electric-verilog-terminate-line)
    (insert (concat  state " <= next_" state ";"))                                                                                           (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                  (electric-verilog-terminate-line)
                                                                                                                                             (electric-verilog-terminate-line)
    ;; Next state and output logic
    (insert (concat "// Output and next State Logic for " state))                                                                            (electric-verilog-terminate-line)
    (insert (concat "always_ff @ (posedge " verilog-ext-templ-fsm-clock  ") begin"))                                                         (electric-verilog-terminate-line)
    (insert (concat "if (!" verilog-ext-templ-fsm-reset ") begin"))                                                                          (electric-verilog-terminate-line)
    (insert (concat "next_" state " <= "rst-state-name ";"))                                                                                 (electric-verilog-terminate-line)
    (insert (concat "// Output resets..."))                                                                                                  (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                  (electric-verilog-terminate-line)
    (insert (concat "else begin"))                                                                                                           (electric-verilog-terminate-line)
    (insert (concat "case (" state ") "))                                                                                                    (electric-verilog-terminate-line)
    ;; Reset State text insertion
    (insert (concat rst-state-name ": begin"))                                                                                               (electric-verilog-terminate-line)
    (insert (concat "// Output statements... "))                                                                                             (electric-verilog-terminate-line)
    (insert (concat "next_" state " <= <state>;"))                                                                                           (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                  (electric-verilog-terminate-line)
    ;; Case reading
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (setq idx (1+ idx))
      (verilog-ext-templ-fsm-sync--add-case-fold param-read pfx idx)                                                                         (electric-verilog-terminate-line)
      (insert (concat param-read ": begin"))                                                                                                 (electric-verilog-terminate-line)
      (insert (concat "// Output statements... "))                                                                                           (electric-verilog-terminate-line)
      (insert (concat "next_" state " <= <state>;"))                                                                                         (electric-verilog-terminate-line)
      (insert (concat "end"))                                                                                                                (electric-verilog-terminate-line))
    (insert (concat "endcase"))                                                                                                              (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                  (electric-verilog-terminate-line)
    (insert (concat "end"))                                                                                                                  (electric-verilog-terminate-line)))


;;;; Headers
(defun verilog-ext-templ-header ()
  "Insert a standard Verilog file header.
See also `verilog-sk-header' for an alternative format."
  (interactive)
  (let ((start (point)))
    (insert "\
//-----------------------------------------------------------------------------
// Title         : <title>
// Project       : <project>
//-----------------------------------------------------------------------------
// File          : <filename>
// Author        : <author>
// Created       : <credate>
// Last modified : <moddate>
//-----------------------------------------------------------------------------
// Description :
// <description>
//-----------------------------------------------------------------------------
// Copyright (c) <author>
//
//------------------------------------------------------------------------------
// Modification history :
// <modhist>
//-----------------------------------------------------------------------------

")
    (goto-char start)
    (search-forward "<filename>")
    (replace-match (buffer-name) t t)
    (search-forward "<author>") (replace-match "" t t)
    (insert (user-full-name))
    (search-forward "<credate>") (replace-match "" t t)
    (verilog-insert-date)
    (search-forward "<moddate>") (replace-match "" t t)
    (verilog-insert-date)
    (search-forward "<author>") (replace-match "" t t)
    (insert (user-full-name))
    (insert "  <" user-mail-address "> ")
    (search-forward "<modhist>") (replace-match "" t t)
    (verilog-insert-date)
    (insert " : created")
    (goto-char start)
    (let (string)
      (setq string (read-string "title: "))
      (search-forward "<title>")
      (replace-match string t t)
      (setq string (read-string "project: " verilog-project))
      (setq verilog-project string)
      (search-forward "<project>")
      (replace-match string t t)
      (replace-match string t t)
      (search-forward "<description>")
      (replace-match "" t t))))



;;;; Instances
(defvar verilog-ext-templ-inst-auto-header "// Beginning of Verilog AUTO_TEMPLATE")
(defvar verilog-ext-templ-inst-auto-footer "// End of Verilog AUTO_TEMPLATE")

(defmacro verilog-ext-templ-inst-auto (template)
  "Insert header and footer to TEMPLATE strings for instantiation."
  (concat "\n" verilog-ext-templ-inst-auto-header " " template " " verilog-ext-templ-inst-auto-footer "\n"))


(defvar verilog-ext-templ-inst-auto-conn-ports
  (verilog-ext-templ-inst-auto "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (\\1),
 ); */")
  "Template with connected ports (same signal name as the port).")

(defvar verilog-ext-templ-inst-auto-disc-ports
  (verilog-ext-templ-inst-auto "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (),
 ); */")
  "Template with disconnected ports.")

(defvar verilog-ext-templ-inst-auto-conn-ports-ss
  (verilog-ext-templ-inst-auto "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (\\1[]),
 ); */")
  "Template with connected ports and subscripts.")


(defvar verilog-ext-templ-inst-auto--simple "\
<module> <instance_name> (/*AUTOINST*/);
")

(defvar verilog-ext-templ-inst-auto-autoparam "\
<module> # (/*AUTOINSTPARAM*/) <instance_name> (/*AUTOINST*/);
")



(defun verilog-ext-templ-inst-auto--choose-template ()
  "Choose current // AUTO_TEMPLATE for instantiation."
  (let (templates-list)
    (setq templates-list (completing-read "AUTO_TEMPLATE: " '("Connected Ports" "Disconnected Ports" "Connected Ports with subscripts")))
    (pcase templates-list
      ("Connected Ports"                 (eval verilog-ext-templ-inst-auto-conn-ports))
      ("Disconnected Ports"              (eval verilog-ext-templ-inst-auto-disc-ports))
      ("Connected Ports with subscripts" (eval verilog-ext-templ-inst-auto-conn-ports-ss))
      (_                                 (error "Error @ verilog-ext-templ-choose-template: Unexpected string")))))

(defun verilog-ext-templ-inst-auto--choose-autoinst ()
  "Choose current /*AUTOINST*/ (and /*AUTOPARAMINST*/) for instantiation."
  (let (autoinst-list)
    (setq autoinst-list (completing-read "AUTOINST:" '("Simple" "With Parameters")))
    (pcase autoinst-list
      ("Simple"          (eval verilog-ext-templ-inst-auto--simple))
      ("With Parameters" (eval verilog-ext-templ-inst-auto-autoparam))
      (_                 (error "Error @ verilog-ext-templ-choose-autoinst: Unexpected string")))))


(defun verilog-ext-templ-inst-auto--autoinst-processing ()
  "Syntactic sugar.
Called from `verilog-ext-templ-inst-auto-from-file'."
  (let ((case-fold-search verilog-case-fold)
        (beg)
        (end))
    (save-excursion ;; Remove comments
      (setq beg (point))
      (setq end (re-search-forward ")[[:blank:]]*;[[:blank:]]*// Templated"))
      (replace-regexp "[[:blank:]]*// Templated" "" nil beg end))
    (save-excursion ;; Open final parenthesis
      (re-search-forward "));")
      (backward-char 2)
      (electric-verilog-terminate-line))
    (save-excursion ;; Remove /*AUTOINST*/
      (setq beg (point))
      (setq end (re-search-forward ");")) ; Last /*AUTOINST*/ comment by AUTO_TEMPLATE
      (replace-string "/*AUTOINST*/" "" nil beg end))))


(defun verilog-ext-templ-inst-auto--autoparam-processing ()
  "Syntactic sugar.
Called from `verilog-ext-templ-inst-auto-from-file'."
  (let ((case-fold-search verilog-case-fold)
        (beg)
        (end))
    (save-excursion
      (setq beg (point))
      (setq end (re-search-forward "))"))
      (backward-char 1)
      (electric-verilog-terminate-line))
    (save-excursion ; Remove /*AUTOINSTPARAM*/
      (setq beg (point))
      (setq end (re-search-forward ");"))
      (replace-string "/*AUTOINSTPARAM*/" "" nil beg end))
    (save-excursion ; Remove ' // Parameters ' string
      (next-line 1)
      (beginning-of-line)
      (kill-line 1))))


(defun verilog-ext-templ-inst-auto-from-file (file)
  "Instantiate top module present in FILE.
INFO: Assumes filename and module name are the same.
INFO: In the future, a list that returns modules in a file could be retrieved
and used as an input.

If universal argument is provided, then instantiate with parameters."
  (interactive "FSelect module from file:")
  (let* ((module-name (file-name-sans-extension (file-name-nondirectory file)))
         (instance-name (read-string "Instance-name: " (concat "I_" (upcase module-name))))
         (start-template (point))
         start-instance template inst-template autoparam)
    ;; Prepare instantiation template
    (add-to-list 'verilog-library-files file)
    (if current-prefix-arg
        (setq template (verilog-ext-templ-inst-auto--choose-template)) ; If universal-arg given ask for AUTO_TEMPLATE and parameterized module to choose
      (setq template verilog-ext-templ-inst-auto-conn-ports)) ; Default template
    (insert template)
    (save-excursion
      (goto-char start-template)
      (replace-string "<module>" module-name))
    (if current-prefix-arg
        (when (equal verilog-ext-templ-inst-auto-autoparam (setq inst-template (verilog-ext-templ-inst-auto--choose-autoinst))) ; If Universal Argument given, then ask for AUTOINST template
          (setq autoparam t))
      (setq inst-template verilog-ext-templ-inst-auto--simple)) ; Default AUTOINST with no parameters
    (setq start-instance (point))
    ;; Instantiate module/instance
    (save-excursion
      (insert inst-template)
      (goto-char start-instance)
      (replace-string "<module>" module-name)
      (goto-char start-instance)
      (replace-string "<instance_name>" instance-name)
      (verilog-auto))
    ;; PostProcess instantiation
    (verilog-ext-templ-inst-auto--autoinst-processing)
    (when autoparam
      (verilog-ext-templ-inst-auto--autoparam-processing))
    ;; Remove AUTO_TEMPLATE comment code
    (setq start-template (search-backward verilog-ext-templ-inst-auto-header))
    (setq start-instance (search-forward verilog-ext-templ-inst-auto-footer))
    (delete-region start-template (1+ start-instance))
    ;; Beautify instantiation
    (save-excursion
      (search-forward instance-name)
      (verilog-ext-indent-current-module module-name))
    (save-excursion
      (search-forward instance-name)
      (next-line 1)
      (verilog-ext-align-ports-current-module))
    (when autoparam
      (save-excursion
        (search-forward instance-name)
        (next-line 1)
        (verilog-ext-align-parameters-current-module module-name)))))


(defun verilog-ext-templ-inst-auto-from-file-with-params (file)
  "Instantiate from FILE with parameter list."
  (interactive "FSelect module from file:")
  (setq current-prefix-arg 4)
  (verilog-ext-templ-inst-auto-from-file file))


;;;; Testbenches
(defun verilog-ext-templ-testbench-simple-from-file (file)
  "Instantiate basic testbench from FILE's top module."
  (interactive "FSelect DUT from file:")
  (let ((start (point))
        (module-name (file-name-sans-extension (file-name-nondirectory file)))
        (current-prefix-arg)
        beg end)
    (insert "\
// TODO: unit space imported packages
// import AxiLiteBfm_pkg::*;

module tb_<module_name> () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;
    localparam CLKT = 10ns;  // 100 MHz

    // TODO: Don't forget to INIT after (verilog-auto)!!
    // DUT instance parameters
    /*AUTOINOUTPARAM(\"<module_name>\")*/
    // End of /*AUTOINOUTPARAM*/

    // Non-auto signals
    logic Clk   = 1'b0;
    logic Rst_n = 1'b1;

    // TODO: Init during declaration (before simulation time 0) to avoid unexpected triggering events
    /* DUT Inputs */
    /*AUTOREGINPUT*/

    /* DUT Outputs */
    /*AUTOLOGIC*/


    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // TODO: Declare/Connect interfaces
    // axi4_lite_if axil_if_<module_name> (.AClk(Clk), .AReset_n(Rst_n));
    // ...

    // TODO: Ensure SV interfaces connections
    // DUT Instantiation

    // TODO: Tasks
    // ...

    // TODO: TB Object declarations
    // AxiLiteBfm axil;

    // TODO: Stimuli
    initial begin
        // axil = new(axil_if_<module_name>);
        // axil.wait_out_of_reset();
        // ...
        // #10 Rst_n = 0;
        // ...
        // $display(\"@%0d: TEST PASSED\", $time);
        // $finish;
        // ...
    end


endmodule // tb_<module_name>
")
    (goto-char start)
    (replace-string "<module_name>" module-name)
    (goto-char start)
    (search-forward "// DUT Instantiation")
    (setq current-prefix-arg 4) ; Add DUT instance with parameters and choosing template
    (verilog-ext-templ-inst-auto-from-file file) ; Includes `verilog-auto' expansion
    (goto-char start)
    (search-forward "/*AUTOINOUTPARAM") ;; Postprocess /*AUTOINOUTPARAM*/
    (save-excursion
      (replace-regexp "logic[[:blank:]]+" "localparam " nil (point) (search-forward "// End of /*AUTOINOUTPARAM*/")))
    (save-excursion
      (replace-regexp "\\(localparam [a-zA-Z0-9_-]+\\);" "\\1 = 0;" nil (point) (search-forward "// End of /*AUTOINOUTPARAM*/")))
    (call-interactively #'verilog-ext-templ-header-hp)
    (goto-char start)
    ;; Beautify declarations and initialize values
    (save-excursion
      (search-forward "/*AUTOREGINPUT*/")
      (beginning-of-line)
      (verilog-pretty-declarations)
      (save-excursion ; Init to '0 every input signal
        (setq beg (point))
        (forward-paragraph 1)
        (setq end (point))
        (replace-regexp "\\(logic [a-zA-Z0-9_-]+\\);" "\\1 = '0;" nil beg end))
      (save-excursion ; Align // To or // From auto comments
        (setq beg (point))
        (forward-paragraph 2)
        (setq end (point))
        (align-regexp beg end "\\(\\s-*\\)//" 1 1 nil)))
    ;; Delete /*AUTO[.*]*/ and generated code
    (save-excursion
      (while (re-search-forward "/\\*AUTO.*\*\/" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (save-excursion
      (while (search-forward "// Beginning of automatic" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (save-excursion
      (while (search-forward "// End of automatics" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (search-forward "// TODO")))



(defun verilog-ext-templ-testbench-env--clocks (file)
  "Create environment `tb_clocks' and save to FILE."
  (with-temp-file file
    (insert "\
import tb_defs_pkg::CLKT;
// import other clock periods

module tb_clocks (
    output logic Clk
    // Other clocks
    );

    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // Other clocks
    // ...

    // Initial clock values
    initial begin
        Clk = 1;
    end


endmodule: tb_clocks
"))
  (find-file file)
  (verilog-ext-templ-header-hp)
  (save-buffer))


(defun verilog-ext-templ-testbench-env--program (file)
  "Create environment `tb_program' and save to FILE."
  (with-temp-file file
    (insert "\
import tb_defs_pkg::*;
import tb_classes::*;
// import Bfms

program automatic tb_program (
    // Interfaces from/to DUT
    // ...
    input logic Clk,
    output logic Rst_n
    );


    // Testbench tb;

    initial begin
        // tb = new();
        $display(\"Starting simulation...\");



        // tb.finish_simulation();
    end


endprogram: tb_program
"))
  (find-file file)
  (verilog-ext-templ-header-hp)
  (save-buffer))


(defun verilog-ext-templ-testbench-env--defs-pkg (file)
  "Create environment `tb_defs_pkg' and save to FILE."
  (with-temp-file file
    (insert "\
package tb_defs_pkg;
    // Simulation parameters
    timeprecision   = 1ps;
    timeunit        = 1ns;
    localparam CLKT = 10ns;  // 100 MHz

    // DUT instance parameters
    // ...

    // Other parameters
    // ...
endpackage : tb_defs_pkg
"))
  (find-file file)
  (verilog-ext-templ-header-hp)
  (save-buffer))



(defun verilog-ext-templ-testbench-env--classes-pkg (file)
  "Create environment `tb_classes_pkg' and save to FILE."
  (with-temp-file file
    (insert "\
package tb_classes_pkg;

// Drivers
// ...

// Monitor
// ...

// Test
// ...

endpackage : tb_defs_pkg
"))
  (find-file file)
  (verilog-ext-templ-header-hp)
  (save-buffer))


(defun verilog-ext-templ-testbench-env--top (file dut-file clocks-file)
  "Create environment top file and save to FILE.
Instantiate dut from DUT-FILE and clocks from CLOCKS-FILE."
  (find-file file)
  (insert "\
// TODO: unit space imported packages

module tb_top () ;

    logic Clk;
    logic Rst_n;

    // TODO: Declare/Connect interfaces
    // axi4_lite_if axil_if (.AClk(Clk), .AReset_n(Rst_n));
    // ...

    // Clocks

    // Testbench
    tb_program I_TB_PROGRAM (
        .Clk   (Clk),
        .Rst_n (Rst_n)
        );


    // DUT Instantiation

endmodule // tb_<module_name>
")
  (goto-char (point-min))
  (search-forward "// DUT Instantiation")
  (setq current-prefix-arg 4) ; Add DUT instance with parameters and choosing template
  (verilog-ext-templ-inst-auto-from-file dut-file) ; Includes `verilog-auto' expansion
  ;; Clocks
  (goto-char (point-min))
  (search-forward "// Clocks")
  (verilog-ext-templ-inst-auto-from-file clocks-file)
  ;; Header and postprocessing
  (verilog-ext-templ-header-hp)
  (save-buffer))




(defun verilog-ext-templ-testbench-env-from-file (dut-file dir)
  "Create SystemVerilog testbench environment.

DUT-FILE corresponds to the filepath of the DUT (assumes a module per file).
DIR selects the directory where the environment will be created.

If called interactively, prompt for these two previous values.
Environment files will be created at specified DIR (clocks, program, defs_pkg, classes_pkg...)"
  (interactive "FSelect module from file: \nDSelect environment directory: ")
  (let ((module-name      (file-name-sans-extension (file-name-nondirectory dut-file)))
        (clocks-file      (concat (file-name-as-directory dir) "tb_clocks.sv"))
        (program-file     (concat (file-name-as-directory dir) "tb_program.sv"))
        (defs-pkg-file    (concat (file-name-as-directory dir) "tb_defs_pkg.sv"))
        (classes-pkg-file (concat (file-name-as-directory dir) "tb_classes_pkg.sv"))
        (top-file         (concat (file-name-as-directory dir) "tb_top.sv")))
    ;; Create Environment files
    (verilog-ext-templ-testbench-env--clocks      clocks-file)
    (verilog-ext-templ-testbench-env--program     program-file)
    (verilog-ext-templ-testbench-env--defs-pkg    defs-pkg-file)
    (verilog-ext-templ-testbench-env--classes-pkg classes-pkg-file)
    (verilog-ext-templ-testbench-env--top         top-file dut-file clocks-file)))



(provide 'verilog-templates)

;;; verilog-templates.el ends here
