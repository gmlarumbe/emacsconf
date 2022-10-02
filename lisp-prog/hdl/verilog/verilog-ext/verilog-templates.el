;;; verilog-templates.el --- Verilog Templates  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;; Code:

(require 'verilog-mode)

(defvar verilog-ext-templ-resetn "Rst_n")
(defvar verilog-ext-templ-clock "Clk")


(defmacro with-verilog-template (&rest body)
  "Execute BODY, indent region and place point at proper place."
  (declare (indent 0) (debug t))
  `(let ((pos-end (make-marker))
         ind-beg ind-end)
     (setq ind-beg (line-beginning-position))
     ,@body
     (setq ind-end (line-end-position))
     (indent-region ind-beg ind-end)
     (when (marker-position pos-end)
       (goto-char (marker-position pos-end)))
     (electric-verilog-tab)))


;;;; Begin/end block
(defun verilog-ext-templ-begin-end ()
  "Insert begin/end block."
  (interactive)
  (with-verilog-template
    (insert "begin")
    (newline)
    (set-marker pos-end (point))
    (newline)
    (insert "end")))


;;;; Comments
(defun verilog-ext-templ-block-comment (&optional comment)
  "Create a comment block.

  ///////////////////
  // Block comment //
  ///////////////////
"
  (interactive)
  (let* ((block-comment-char ?\/)
         (block-comment (or comment (read-string "Name: ")))
         (block-comment-width (string-width block-comment)))
    (with-verilog-template
      (insert-char block-comment-char (+ block-comment-width 6))
      (newline)
      (insert-char block-comment-char 2)
      (insert " ")
      (insert block-comment)
      (insert " ")
      (insert-char block-comment-char 2)
      (newline)
      (insert-char block-comment-char (+ block-comment-width 6) nil)
      (newline))))


;;;; Case
(defun verilog-ext-templ-case (&optional expr cases)
  "Case template.

Read/add expressions until an empty string is entered.

If EXPR is non-nil, use it as case expression.
If CASES is non-nil it must be a list of all the possible
cases to iterate over."
  (interactive)
  (let (param-read)
    (with-verilog-template
      (insert "case (" (or expr (read-string "Expression: ")) ")\n\n")
      (if cases
          (dolist (case cases)
            (insert (concat case ": begin\n"))
            (insert (concat "// Output statements... \n"))
            (insert (concat "end\n\n")))
        (while (not (string-equal (setq param-read (read-string "Case: ")) ""))
          (insert (concat param-read ": begin\n"))
          (insert (concat "// Output statements... \n"))
          (insert (concat "end\n\n"))))
      (insert "endcase\n"))))



;; ;;;; Enum, Typedef, Struct
(defun verilog-ext-templ--compute-vector-width ()
  "Prompt for vector width and return expression:
- If a constant identifier is provided return [CONSTANT-1:0].
- If a number greater than 1 is provided, calculate width.
- If set to 0 or 1 (or negative) return a nil string."
  (let* ((width-str (read-string "Width: "))
         (width-num (string-to-number width-str)))
    ;; Cover width eq 0 and 1 cases
    (when (or (string-equal width-str "0")
              (string-equal width-str ""))
      (setq width-num 1))
    (if (not (eq width-num 0)) ; Number different from 0, not a constant
        (if (> width-num 1)    ; Vector with brackets
            (progn
              (setq width-num (1- width-num))
              (setq width-str (number-to-string width-num))
              (concat "[" width-str ":0]"))
          "") ; Width equals 1
      (concat "[" width-str "-1:0]")))) ; Width constant


(defun verilog-ext-templ-enum-typedef (&optional typedef logic name)
  "Insert enum template.
If TYPEDEF is non-nil, declare a typedef enum type.
If LOGIC is non-nil, declare it as logic type.
If NAME is non-nil, set it as the user type.

Read/add labels until an empty string is entered.

Return a list of the enum labels."
  (let ((width "")
        (enum-types '("logic" "bit" "int" "integer" "other"))
        enum-item type enum-labels)
    (with-verilog-template
      (when typedef
        (insert "typedef "))
      (if logic
          (setq type "logic")
        (setq type (completing-read "Type: " enum-types)))
      (when (string-equal type "other")
        (setq type (read-string "Type: ")))
      (if (or (string-equal type "logic")
              (string-equal type "bit"))
          (setq width (verilog-ext-templ--compute-vector-width))
        (setq width "")) ; Disable width field If not a vector
      (insert "enum " type " " width " {")
      (while (not (string-equal (setq enum-item (read-string "Item: ")) ""))
        (push (upcase enum-item) enum-labels)
        ;; (add-to-list 'enum-labels (upcase enum-item) :append)
        (insert (upcase enum-item) ", "))
      (delete-char -2)
      (insert "} ")
      (if name
          (insert name ";")
        ;; Else
        (if typedef
            (insert (read-string "Type Name: ") ";")
          (insert (read-string "Enum Name: ") ";"))))
    (reverse enum-labels)))


(defun verilog-ext-templ-struct-typedef (&optional typedef union)
  "Insert struct template.
If TYPEDEF is non-nil, declare a typedef struct type.
If UNION is non-nil, declare a union instead of a struct.
Read/add elements of struct until an empty string is entered."
  (let ((width "")
        struct-item type)
    (with-verilog-template
      (when typedef
        (insert "typedef "))
      (if union
          (insert "union ")
        (insert "struct "))
      (when (yes-or-no-p "Packed?")
        (insert "packed "))
      (insert "{\n")
      (while (not (string-equal (setq struct-item (read-string "Item: ")) ""))
        (setq type (read-string "Type: " "logic"))
        (if (or (string-equal type "logic") (string-equal type "bit"))
            (setq width (verilog-ext-templ--compute-vector-width))
          (setq width "")) ; Disable width field if not a vector
        (insert type " " width " " struct-item ";\n"))
      (insert "} ")
      (if typedef
          (insert (read-string "Type Name: ") ";")
        (insert (read-string "Struct Name: ") ";")))
    ;; Align declarations
    (save-excursion
      (verilog-re-search-backward "(" nil t)
      (forward-char)
      (verilog-forward-syntactic-ws)
      (verilog-pretty-declarations))))


;;;; Task
(defun verilog-ext-templ--task-add-port (direction signal)
  "Add SIGNAL to task template.
DIRECTION should be either 'input or 'output."
  (let ((type (read-string "Type: " "logic"))
        width)
    (if (or (string-equal type "logic")
            (string-equal type "bit"))
        (setq width (concat (verilog-ext-templ--compute-vector-width) " "))
      (setq width "")) ; Disable width field if not a vector
    (insert (symbol-name direction) " " type " " width signal ",\n")))


(defun verilog-ext-templ-task ()
  "Insert a task definition."
  (interactive)
  (let (inputs outputs)
    (with-verilog-template
      (insert "task ")
      (insert (read-string "Task name: ") " (\n")
      (while (not (string-equal (setq inputs (read-string "Input signal: ")) ""))
        (verilog-ext-templ--task-add-port 'input inputs))
      (while (not (string-equal (setq outputs (read-string "Output signal: ")) ""))
        (verilog-ext-templ--task-add-port 'output outputs))
      (delete-char -2)
      (insert "\n);\n")
      (set-marker pos-end (point))
      (insert "\nendtask"))
    ;; Align declarations
    (save-excursion
      (verilog-re-search-backward "(" nil t)
      (forward-char)
      (verilog-forward-syntactic-ws)
      (verilog-pretty-declarations))))



;;;; Signal definition
(defun verilog-ext-templ-def-logic ()
  "Insert a definition of signal under point at the beginning of current module."
  (interactive "*")
  (let ((sig (thing-at-point 'symbol :no-prop))
        str)
    (cond ((not sig)
           (user-error "No signal at point"))
          ((not (string-match verilog-identifier-re sig))
           (user-error "Not a valid verilog identifier"))
          ((member sig verilog-keywords)
           (message "object at point (%s) is a keyword" sig))
          (t
           (save-excursion
             (verilog-re-search-backward verilog-ext-top-re nil nil)
             (verilog-end-of-statement)
             (verilog-forward-syntactic-ws)
             (split-line)
             (setq str (concat "logic " (verilog-ext-templ--compute-vector-width) " " sig ";"))
             (insert str)
             (message (concat "[Line " (format "%s" (line-number-at-pos)) "]: " str)))))))


;;;; FSM
(defun verilog-ext-templ-fsm (&optional async)
  "Insert a state machine custom definition with two always blocks.
One for next state and output logic and one for the state registers.
If ASYNC is non-nil create an asynchronous reset."
  (interactive)
  (let* ((state-type (read-string "Name of state typedef: " "state_t"))
         (state-var  (read-string "Name of state variable: " "state"))
         (next-state-var (concat "next_" state-var))
         (enum-labels))
    ;; Define state enum typedef
    (with-verilog-template
      (setq enum-labels (verilog-ext-templ-enum-typedef :typedef :logic state-type))
      (newline)
      (insert state-type " " state-var ", " next-state-var ";\n\n"))
    ;; Synchronous logic
    (with-verilog-template
      (insert "// State FF for " state-var "\n")
      (insert "always_ff @ (posedge " verilog-ext-templ-clock)
      (when async
        (insert " or negedge " verilog-ext-templ-resetn))
      (insert ") begin\n")
      (insert "if (!" verilog-ext-templ-resetn ")\n")
      (insert state-var " <= " (car enum-labels) ";\n")
      (insert "else\n")
      (insert  state-var " <= " next-state-var ";\n")
      (insert "end\n\n"))
    ;; Combinational block
    (with-verilog-template
      (insert "// Output and next State Logic for " state-var "\n")
      (insert "always_comb begin\n")
      (verilog-ext-templ-case state-var enum-labels)
      (insert "end\n"))))


;;;; Headers
(defun verilog-ext-templ-header ()
  "Insert a standard Verilog file header."
  (interactive)
  (let (string)
    (save-excursion
      (goto-char (point-min))
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
// Modification history:
// <modhist>
//-----------------------------------------------------------------------------

")
      (goto-char (point-min))
      (search-forward "<filename>")
      (replace-match (buffer-name) t t)
      (search-forward "<author>")
      (replace-match (user-full-name) t t)
      (search-forward "<credate>")
      (replace-match "" t t)
      (verilog-insert-date)
      (search-forward "<moddate>")
      (replace-match "" t t)
      (verilog-insert-date)
      (search-forward "<author>")
      (replace-match (concat (user-full-name) " <" user-mail-address ">") t t)
      (search-forward "<modhist>")
      (replace-match "" t t)
      (verilog-insert-date)
      (insert " : created")
      (goto-char (point-min))
      (setq string (read-string "Title: "))
      (search-forward "<title>")
      (replace-match string t t)
      (setq string (read-string "Project: " verilog-project))
      (setq verilog-project string)
      (search-forward "<project>")
      (replace-match string t t)
      (search-forward "<description>")
      (replace-match "" t t)
      (insert (read-string "Description: ")))))



;;;; Instances
(defvar verilog-ext-templ-inst-auto-header "// Beginning of Verilog AUTO_TEMPLATE")
(defvar verilog-ext-templ-inst-auto-footer "// End of Verilog AUTO_TEMPLATE")

(defun verilog-ext-templ-inst-auto (template)
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

(defvar verilog-ext-templ-inst-auto-simple "\
<module> <instance_name> (/*AUTOINST*/);
")

(defvar verilog-ext-templ-inst-auto-params "\
<module> # (/*AUTOINSTPARAM*/) <instance_name> (/*AUTOINST*/);
")


(defun verilog-ext-templ-inst-auto--choose-template ()
  "Choose current // AUTO_TEMPLATE for instantiation."
  (let (templates-list)
    (setq templates-list (completing-read "AUTO_TEMPLATE: " '("Connected Ports" "Disconnected Ports" "Connected Ports with subscripts")))
    (pcase templates-list
      ("Connected Ports"                 verilog-ext-templ-inst-auto-conn-ports)
      ("Disconnected Ports"              verilog-ext-templ-inst-auto-disc-ports)
      ("Connected Ports with subscripts" verilog-ext-templ-inst-auto-conn-ports-ss)
      (_                                 (error "Error @ verilog-ext-templ-choose-template: Unexpected string")))))

(defun verilog-ext-templ-inst-auto--choose-autoinst ()
  "Choose current /*AUTOINST*/ (and /*AUTOPARAMINST*/) for instantiation."
  (let (autoinst-list)
    (setq autoinst-list (completing-read "AUTOINST:" '("Simple" "With Parameters")))
    (pcase autoinst-list
      ("Simple"          verilog-ext-templ-inst-auto-simple)
      ("With Parameters" verilog-ext-templ-inst-auto-params)
      (_                 (error "Error @ verilog-ext-templ-choose-autoinst: Unexpected string")))))


(defun verilog-ext-templ-inst-auto--autoinst-processing ()
  "Syntactic sugar.
Called from `verilog-ext-templ-inst-auto-from-file'."
  (let (beg end)
    (save-excursion ;; Remove comments
      (setq beg (point))
      (if (re-search-forward ")[[:blank:]]*;[[:blank:]]*// Templated" nil t)
          (setq end (point))
        (error "Couldn't process AUTOINST.  Does module have ports?"))
      (verilog-ext-replace-regexp "[[:blank:]]*// Templated" "" beg end))
    (save-excursion ;; Open final parenthesis
      (re-search-forward "));")
      (backward-char 2)
      (electric-verilog-terminate-line))
    ;; Remove /*AUTOINST*/
    (save-excursion
      (setq beg (point))
      (setq end (re-search-forward ");")) ; Last /*AUTOINST*/ comment by AUTO_TEMPLATE
      (verilog-ext-replace-string "/*AUTOINST*/" "" beg end))))


(defun verilog-ext-templ-inst-auto--autoparam-processing ()
  "Syntactic sugar.
Called from `verilog-ext-templ-inst-auto-from-file'."
  (let (beg end)
    (save-excursion
      (setq beg (point))
      (if (re-search-forward "))" nil t)
          (setq end (point))
        (error "Couldn't process AUTOPARAM Does module have parameters?"))
      (backward-char 1)
      (electric-verilog-terminate-line))
    ;; Remove /*AUTOINSTPARAM*/
    (save-excursion
      (setq beg (point))
      (setq end (re-search-forward ");" nil t))
      (verilog-ext-replace-string "/*AUTOINSTPARAM*/" "" beg end)
      ;; Remove ' // Parameters ' string
      (forward-line 1)
      (beginning-of-line)
      (kill-line 1))))


(defun verilog-ext-templ-inst-auto--read-file-modules (file)
  "Find modules in FILE.
Return found one, or prompt for list of found ones if there is more than one."
  (let (modules
        (debug nil))
    (with-temp-buffer
      (when debug
        (clone-indirect-buffer-other-window "*debug*" t))
      (insert-file-contents file)
      (verilog-mode) ; Needed to set the syntax table to avoid searching in comments
      (while (verilog-re-search-forward verilog-ext-top-instantiable-re nil t)
        (push (match-string-no-properties 2) modules)))
    (delete-dups modules)
    (if (cdr modules)
        (completing-read "Module to instantiate: " modules)
      (car modules))))


(defun verilog-ext-templ-inst-auto-from-file (file &optional template inst-template)
  "Instantiate top module present in FILE.
If there is more than one module, prompt for a list of detected modules.

Use auto TEMPLATE or prompt to choose one if is nil.
Use inst INST-TEMPLATE or prompt to choose one if is nil."
  (interactive "FSelect module from file:\nP")
  (let* ((module-name (verilog-ext-templ-inst-auto--read-file-modules file))
         (start-template (point))
         end-template end-instance instance-name start-instance autoparam)
    ;; Checks and env setup
    (unless buffer-file-name
      (error "Current buffer needs to visit a file to instantiate module"))
    (unless module-name
      (error "No module found in %s" file))
    (unless (verilog-ext-point-inside-block-p 'module)
      (error "Point is not inside a module block.  Cannot instantiate block"))
    (setq instance-name (read-string "Instance-name: " (concat "I_" (upcase module-name))))
    (add-to-list 'verilog-library-files file)
    ;; Prepare instantiation template
    (unless template
      (setq template (verilog-ext-templ-inst-auto--choose-template)))
    (unless inst-template
      (setq inst-template (verilog-ext-templ-inst-auto--choose-autoinst)))
    (when (equal inst-template verilog-ext-templ-inst-auto-params)
      (setq autoparam t))
    ;; Instantiate module/instance
    (insert template)
    (setq end-template (point))
    (verilog-ext-replace-string "<module>" module-name start-template end-template)
    (setq start-instance (point))
    (insert inst-template)
    (setq end-instance (point))
    (verilog-ext-replace-string "<module>" module-name start-instance end-instance)
    (verilog-ext-replace-string "<instance_name>" instance-name start-instance end-instance)
    (verilog-auto) ; Might change positions of some variables!
    ;; Postprocess instantiation
    (goto-char (point-min))
    (search-forward verilog-ext-templ-inst-auto-footer)
    (forward-line)
    (verilog-ext-templ-inst-auto--autoinst-processing)
    (when autoparam
      (verilog-ext-templ-inst-auto--autoparam-processing))
    ;; Remove AUTO_TEMPLATE comment code
    (setq start-template (search-backward verilog-ext-templ-inst-auto-header))
    (setq start-instance (search-forward verilog-ext-templ-inst-auto-footer))
    (delete-region start-template (1+ start-instance))
    ;; Beautify (indent and align) instantiation
    (search-forward instance-name)
    (verilog-ext-module-at-point-beautify)))


(defun verilog-ext-templ-inst-auto-from-file-simple (file)
  "Instantiate from FILE with simple template: connected ports and no parameters."
  (interactive "FSelect module from file:")
  (verilog-ext-templ-inst-auto-from-file file
                                         verilog-ext-templ-inst-auto-conn-ports
                                         verilog-ext-templ-inst-auto-simple))


(defun verilog-ext-templ-inst-auto-from-file-params (file)
  "Instantiate from FILE with params template: connected ports with parameters."
  (interactive "FSelect module from file:")
  (verilog-ext-templ-inst-auto-from-file file
                                         verilog-ext-templ-inst-auto-conn-ports
                                         verilog-ext-templ-inst-auto-params))


(defun verilog-ext-templ-inst-auto-from-file-tb-dut (file)
  "Instantiate from FILE with params template: connected ports with subscripts with parameters.
Required by tb instantiation to auto detect width of signals."
  (interactive "FSelect module from file:")
  (verilog-ext-templ-inst-auto-from-file file
                                         verilog-ext-templ-inst-auto-conn-ports-ss
                                         verilog-ext-templ-inst-auto-params))


(defun verilog-ext-templ-inst-auto-from-file-prompt (file)
  "Instantiate from FILE and prompt for template and parameters."
  (interactive "FSelect module from file:")
  (verilog-ext-templ-inst-auto-from-file file))



;;;; Testbenches
(defun verilog-ext-templ-testbench-simple-from-file (file outfile)
  "Instantiate basic testbench from FILE's top module into OUTFILE."
  (interactive "FSelect DUT from file:\nFOutput file: ")
  (when (file-exists-p outfile)
    (error "File %s exists" outfile))
  (let ((module-name (verilog-ext-templ-inst-auto--read-file-modules file))
        beg end)
    (find-file outfile)
    (insert "\
module tb_<module_name> () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;

    localparam CLKT = 10ns;  // 100 MHz

    // TODO: INIT after (verilog-auto)!!
    // DUT instance parameters
    /*AUTOINOUTPARAM(\"<module_name>\")*/
    // End of /*AUTOINOUTPARAM*/

    // Non-auto signals
    logic <clock> = 1'b0;
    logic <resetn> = 1'b1;

    // TODO: Init during declaration (before simulation time 0) to avoid race conditions
    /* DUT Inputs */
    /*AUTOREGINPUT*/

    /* DUT Outputs */
    /*AUTOLOGIC*/


    // System Clock
    always begin
        #(CLKT/2) <clock> = ~<clock>;
    end

    // TODO: Declare/Connect interfaces
    // axi4_lite_if axil_if_<module_name> (.Clk(<clock>), .Rst_n(<resetn>));
    // ...

    // TODO: Ensure SV interfaces connections
    // DUT Instantiation

    // TODO: Tasks/functions
    // ...

    // TODO: TB Objects
    // axi4_lite_bfm bfm;

    // TODO: Stimuli
    initial begin
        // bfm = new(axil_if_<module_name>);
        //
        // #10 Rst_n = 0;
        //
        // bfm.read();
        // bfm.write();
        // ...
        // ...
        $display(\"@%0d: TEST PASSED\", $time);
        $finish;
    end

endmodule // tb_<module_name>
")
    ;; Replace template parameteres, instantiate DUT and create header
    (verilog-ext-replace-string "<module_name>" module-name (point-min) (point-max))
    (verilog-ext-replace-string "<clock>" verilog-ext-templ-clock (point-min) (point-max))
    (verilog-ext-replace-string "<resetn>" verilog-ext-templ-resetn (point-min) (point-max))
    (goto-char (point-min))
    (search-forward "// DUT Instantiation")
    (verilog-ext-templ-inst-auto-from-file-tb-dut file)
    (verilog-ext-templ-header)
    ;; Postprocess /*AUTOINOUTPARAM*/
    (save-excursion
      (goto-char (point-min))
      (setq beg (search-forward (concat "/*AUTOINOUTPARAM(\"" module-name "\")*/")))
      (setq end (search-forward "// End of /*AUTOINOUTPARAM*/"))
      (verilog-ext-replace-regexp (concat "logic\\s-+\\(" verilog-identifier-re "\\)") "localparam \\1 = 0" beg end))
    ;; Beautify declarations and initialize values
    (save-excursion
      (goto-char (point-min))
      (search-forward "/*AUTOREGINPUT*/")
      (save-excursion ; Init to '0 every input signal
        (setq beg (point))
        (forward-paragraph 1)
        (setq end (point))
        (verilog-ext-replace-regexp (concat "\\(logic\\s-+\\(\\[[^]]*\\]\\s-*\\)*" verilog-identifier-re "\\);") "\\1 = '0;" beg end)
        (goto-char beg)
        (forward-line 2)
        (verilog-pretty-declarations)
        (verilog-pretty-expr))
      (save-excursion ; Align // To or // From auto comments if `verilog-auto-wire-comment' is non-nil
        (setq beg (point))
        (forward-paragraph 2)
        (setq end (point))
        (align-regexp beg end "\\(\\s-*\\)//" 1 1 nil)))
    ;; Delete /*AUTO[.*]*/ , generated code and instantiation subscripts (needed to autodetect width of signals)
    (goto-char (point-min))
    (save-excursion
      (search-forward "// DUT Instantiation")
      (verilog-ext-replace-regexp (concat "\\(\\." verilog-identifier-re "\\s-*(" verilog-identifier-re "\\)\\(\\[.*\\]\\)") "\\1"
                                  (point) (verilog-pos-at-end-of-statement)))
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
    (search-forward "// TODO")
    (write-file outfile)))




(provide 'verilog-templates)

;;; verilog-templates.el ends here
