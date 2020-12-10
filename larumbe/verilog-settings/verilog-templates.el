;;; verilog-templates.el --- Verilog Templates  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;; Own Verilog templates
;; Should be deprecated by Hydra+YASnippet
;; Customized functions extracted from verilog-mode.el at .elisp/ dir
;;;; Common
(defvar verilog-reset-custom "Rst_n")
(defun larumbe/verilog-prompt-reset-custom ()
  "Prompt for the name of a state machine reset."
  (setq verilog-reset-custom (read-string "Active Low Reset Name: " "Rst_n")))

(defun larumbe/verilog-prompt-clock-custom ()
  "Prompt for the name of a clock."
  (setq verilog-clock-custom (read-string "Posedge clock name: " "Clk")))


;;;; Begin/end block
;; Replace old begin-end from verilog-mode skeleton
(defun larumbe/verilog-begin-custom ()
  "Insert begin end block.  Use the minibuffer to prompt for name.
Written as `verilog-mode' original defun had issues with indentation."
  (interactive)
  (electric-verilog-tab)                ; Initial indent (we wont know where we are...)
  (insert "begin")
  (progn (electric-verilog-terminate-line) nil)
  (save-excursion
    (progn (electric-verilog-terminate-line) nil)
    (insert "end")
    (electric-verilog-tab)
    )
  (electric-verilog-tab)
  )


;;;; Comments
;; Had some issues trying to implement it with skeletons. Finally decided on interactive defun
(defun larumbe/verilog-add-block-comment ()
  "Create a Verilog comment block.
Useful to separate sections within code.
Char code 47 corresponds to '/' character in Verilog"
  (interactive)
  (setq verilog-block-comment-custom (read-string "Name: "))
  (setq verilog-block-comment-width (string-width verilog-block-comment-custom))
  ;; Top line
  (electric-verilog-tab)              ; Start indentation for comment block
  (insert (concat (insert-char 47 (+ verilog-block-comment-width 6) nil)))
  (electric-verilog-terminate-line)
  ;; Comment line
  (insert (concat
           (insert-char 47 2 nil)
           (insert " ")
           (insert verilog-block-comment-custom)
           (insert " ")
           (insert-char 47 2 nil)))
  (electric-verilog-terminate-line)
  ;; Bottom line
  (insert (concat (insert-char 47 (+ verilog-block-comment-width 6) nil)))
  (electric-verilog-terminate-line))


;;;; State Machines
;; Variables used to add parameters on-the-fly
(defvar larumbe/verilog-fsm-parameter-position nil)

;; 1 parameter keyword per parameter declaration
(defun larumbe/verilog-state-machine-add-case (param-read)
  "Fill cases within the next state and output logic.
Declare them as parameters at the beginning of the FSM."
  (save-excursion
    (goto-char larumbe/verilog-fsm-parameter-position)
    (electric-verilog-terminate-line)
    (insert (concat "parameter " param-read " = " (read-string "Param value: ") ";"))
    (setq larumbe/verilog-fsm-parameter-position (point))))


;; Adds a state machine with two always blocks.
(defun larumbe/verilog-state-machine-async-custom-simple ()
  "Insert a state machine custom definition     .
Two always blocks, one for next state and output logic and one for the state registers"
  (interactive)
  (let (param-read)
    (setq verilog-custom-state (read-string "Name of state variable: " "state"))
    (electric-verilog-tab)              ; Start indentation for comment block
    (insert (concat "// State registers for " verilog-custom-state))                                                                            (progn (electric-verilog-terminate-line) nil)
    (insert (concat "reg [" (read-string "msb: " "31") ":" (read-string "lsb: " "0") "] " verilog-custom-state ", next_" verilog-custom-state ";"))
    (setq larumbe/verilog-fsm-parameter-position (point))                                                                                       (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " verilog-custom-state))                                                                                   (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " (larumbe/verilog-prompt-clock-custom) " or negedge " (larumbe/verilog-prompt-reset-custom) ") begin")) (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ")"))                                                                                          (progn (electric-verilog-terminate-line) nil)
    (insert (concat verilog-custom-state " <= IDLE;"))                                                                                          (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else"))                                                                                                                    (progn (electric-verilog-terminate-line) nil)
    (insert (concat  verilog-custom-state " <= next_" verilog-custom-state ";"))                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; Next state and output logic
    (insert (concat "// Output and next State Logic for " verilog-custom-state))                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " verilog-clock-custom  " or negedge " verilog-reset-custom  ") begin"))                                 (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ") begin"))                                                                                    (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= IDLE;"))                                                                                  (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output resets..."))                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else begin"))                                                                                                              (progn (electric-verilog-terminate-line) nil)
    (insert (concat "case (" verilog-custom-state ") "))
    ;; Case reading
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (larumbe/verilog-state-machine-add-case  param-read)                                                                                      (progn (electric-verilog-terminate-line) nil)
      (insert (concat param-read ": begin"))                                                                                                    (progn (electric-verilog-terminate-line) nil)
      (insert (concat "// Output statements... "))                                                                                              (progn (electric-verilog-terminate-line) nil)
      (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                             (progn (electric-verilog-terminate-line) nil)
      (insert (concat "end"))                                                                                                                   (progn (electric-verilog-terminate-line) nil))
    (insert (concat "endcase"))                                                                                                                 (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                     (progn (electric-verilog-terminate-line) nil)))


;; Only 1 parameter keyword for all parameter declarations (improves readability)
(defun larumbe/verilog-state-machine-add-case-fold (param-read pfx idx )
  "Fills cases within the Next state and output logic and declares them as parameters at the beginning of the FSM.
Parameter keyword is used only once, improving readability."
  (save-excursion
    (goto-char larumbe/verilog-fsm-parameter-position)
    (delete-char -1)
    (insert ",")
    (electric-verilog-terminate-line)
    (insert (concat param-read " = " (read-string "Param value: " (concat pfx (number-to-string idx) ";"))))
    (setq larumbe/verilog-fsm-parameter-position (point))))





;; Returns "4'h." or "1'b." depending on msb and lsb.
(defun larumbe/verilog-state-machine-get-prefix (msb-str lsb-str)
  "Very neat function that gets the prefix depending on the FSM state width.
For the time being, since not very complex FSMs are being immplemented,
just binary and hexadecimal prefix are returned"
  (let (width msb lsb)
    (setq msb (string-to-number msb-str))
    (setq lsb (string-to-number lsb-str))
    (setq width (-  msb  lsb))
    (if (/= (% (1+ width) 4) 0)
        (message "1'b")
      (message "4'h"))))


;; Adds a state machine with two always blocks.
;; Improves previous function with automatic reset state insertion and automatic parameter width insertion
(defun larumbe/verilog-state-machine-sync-custom ()
  "Insert a state machine custom definition     .
Two always blocks, one for next state and output logic and one for the state registers"
  (interactive)
  (let (param-read rst-state-name msb lsb pfx (idx 0))
    (setq verilog-custom-state (read-string "Name of state variable: " "state"))
    (electric-verilog-tab)              ; Start indentation for comment block
    (insert (concat "// State registers for " verilog-custom-state))                                                                                                       (progn (electric-verilog-terminate-line) nil)
    (insert (concat "logic [" (setq msb (read-string "msb: " "3")) ":" (setq lsb (read-string "lsb: " "0")) "] " verilog-custom-state ", next_" verilog-custom-state ";")) (progn (electric-verilog-terminate-line) nil)
    (setq pfx (larumbe/verilog-state-machine-get-prefix msb  lsb))
    (insert (concat "localparam " (setq rst-state-name (read-string "Reset State Name: " "IDLE"))  " = " (read-string "Reset Value: " (concat pfx "0;"))))
    (setq larumbe/verilog-fsm-parameter-position (point))                                                                                                                          (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " verilog-custom-state))                                                                                                              (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always_ff @ (posedge " (larumbe/verilog-prompt-clock-custom) ") begin"))                                                                                      (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ")"))                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat verilog-custom-state " <= " rst-state-name ";"))                                                                                                       (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else"))                                                                                                                                               (progn (electric-verilog-terminate-line) nil)
    (insert (concat  verilog-custom-state " <= next_" verilog-custom-state ";"))                                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; Next state and output logic
    (insert (concat "// Output and next State Logic for " verilog-custom-state))                                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always_ff @ (posedge " verilog-clock-custom  ") begin"))                                                                                              (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ") begin"))                                                                                                               (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= "rst-state-name ";"))                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output resets..."))                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else begin"))                                                                                                                                         (progn (electric-verilog-terminate-line) nil)
    (insert (concat "case (" verilog-custom-state ") "))                                                                                                                   (progn (electric-verilog-terminate-line) nil)
    ;; Reset State text insertion
    (insert (concat rst-state-name ": begin"))                                                                                                                             (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output statements... "))                                                                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                                                          (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    ;; Case reading
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (setq idx (1+ idx))
      (larumbe/verilog-state-machine-add-case-fold param-read pfx idx)                                                                                                             (progn (electric-verilog-terminate-line) nil)
      (insert (concat param-read ": begin"))                                                                                                                               (progn (electric-verilog-terminate-line) nil)
      (insert (concat "// Output statements... "))                                                                                                                         (progn (electric-verilog-terminate-line) nil)
      (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                                                        (progn (electric-verilog-terminate-line) nil)
      (insert (concat "end"))                                                                                                                                              (progn (electric-verilog-terminate-line) nil)
      )
    (insert (concat "endcase"))                                                                                                                                            (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    )
  )

;;;; Headers
(defun larumbe/verilog-header ()
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
    (insert "  <gonzalomlarumbe@gmail.com> ")
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



(defun larumbe/verilog-header-hp ()
  "Insert an HP Verilog file header.
See also `verilog-header' for an alternative format."
  (interactive)
  (save-excursion
    (let ((start (point-min)))
      (goto-char start)
      (insert "\
/********1*********2*********3*********4*********5*********6*********7*********8
 *
 * FILE      : <filename>
 * HIERARCHY :
 * FUNCTION  : <function>
 * AUTHOR    : <author>
 *
 *_______________________________________________________________________________
 *
 * REVISION HISTORY
 *
 * Name         Date          Comments
 * ------------------------------------------------------------------------------
 * <user>    <credate>     Created
 * ------------------------------------------------------------------------------
 *_______________________________________________________________________________
 *
 * FUNCTIONAL DESCRIPTION
 * <description>
 *_______________________________________________________________________________
 *
 * (c) Copyright Hewlett-Packard Company, year
 * All rights reserved. Copying or other reproduction of this
 * program except for archival purposes is prohibited without
 * written consent of Hewlett-Packard Company.
 * HEWLETT-PACKARD COMPANY
 * INKJET COMERCIAL DIVISION
 *
 *********1*********2*********3*********4*********5*********6*********7*********/

")
      (goto-char start)
      (search-forward "<filename>")
      (replace-match (buffer-name) t t)
      (search-forward "<author>") (replace-match "" t t)
      (insert (user-full-name))
      (insert "  <gonzalo.martinez.larumbe@hp.com>")
      (search-forward "<user>")
      (replace-match (user-login-name) t t)
      (search-forward "<credate>") (replace-match "" t t)
      (verilog-insert-date)
      (if (called-interactively-p 'any)
          (progn
            (let (string)
              (goto-char start)
              (setq string (read-string "Function: "))
              (search-forward "<function>")
              (replace-match string t t)
              (setq string (read-string "Description: "))
              (search-forward "<description>")
              (replace-match string t t)))
        (progn
          (goto-char start)
          (search-forward "<function>")
          (replace-match "" t t)
          (search-forward "<description>")
          (replace-match "" t t))))))

;;;; Instances
(setq larumbe/verilog-auto-template-header "// Beginning of Larumbe's Verilog AUTO_TEMPLATE")
(setq larumbe/verilog-auto-template-footer "// End of Larumbe's Verilog AUTO_TEMPLATE")

(defmacro larumbe/verilog-auto-template (template)
  (concat "\n" larumbe/verilog-auto-template-header " " template " " larumbe/verilog-auto-template-footer "\n"))


(setq larumbe/verilog-auto-template-connected-ports
      (larumbe/verilog-auto-template "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (\\1),
 ); */"
                                     ))

(setq larumbe/verilog-auto-template-disconnected-ports
      (larumbe/verilog-auto-template "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (),
 ); */"
                                     ))

(setq larumbe/verilog-auto-template-connected-ports-subscripts
      (larumbe/verilog-auto-template "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (\\1[]),
 ); */"
                                     ))


(setq larumbe/verilog-autoinst-template-simple "\
<module> <instance_name> (/*AUTOINST*/);
")

(setq larumbe/verilog-autoinst-autoparam-template "\
<module> # (/*AUTOINSTPARAM*/) <instance_name> (/*AUTOINST*/);
")



(defun larumbe/verilog-choose-template ()
  "Choose current // AUTO_TEMPLATE for instantiation"
  (let (templates-list)
    (setq templates-list (completing-read "AUTO_TEMPLATE: " '("Connected Ports" "Disconnected Ports" "Connected Ports with subscripts")))
    (pcase templates-list
      ("Connected Ports"                 (eval larumbe/verilog-auto-template-connected-ports))
      ("Disconnected Ports"              (eval larumbe/verilog-auto-template-disconnected-ports))
      ("Connected Ports with subscripts" (eval larumbe/verilog-auto-template-connected-ports-subscripts))
      (_                                 (error "Error @ larumbe/verilog-choose-template: Unexpected string")))))

(defun larumbe/verilog-choose-autoinst ()
  "Choose current /*AUTOINST*/ (and /*AUTOPARAMINST*/) for instantiation"
  (let (autoinst-list)
    (setq autoinst-list (completing-read "AUTOINST:" '("Simple" "With Parameters")))
    (pcase autoinst-list
      ("Simple"          (eval larumbe/verilog-autoinst-template-simple))
      ("With Parameters" (eval larumbe/verilog-autoinst-autoparam-template))
      (_                 (error "Error @ larumbe/verilog-choose-autoinst: Unexpected string")))))


(defun larumbe/verilog-autoinst-processing ()
  "Called from `larumbe/verilog-insert-instance-from-file' (refactoring purposes)"
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


(defun larumbe/verilog-autoparam-processing ()
  "Called from `larumbe/verilog-insert-instance-from-file' (refactoring purposes)"
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


(defun larumbe/verilog-insert-instance-from-file (file)
  "DANGER: Assumes filename and module name are the same.
INFO: In the future, a list that returns modules in a file could be retrieved and used as an input"
  (interactive "FSelect module from file:")
  (let* ((module-name (file-name-sans-extension (file-name-nondirectory file)))
         (instance-name (read-string "Instance-name: " (concat "I_" (upcase module-name))))
         (start-template (point))
         start-instance template inst-template autoparam)
    ;; Prepare instantiation template
    (add-to-list 'verilog-library-files file)
    (if current-prefix-arg
        (setq template (larumbe/verilog-choose-template)) ; If universal-arg given ask for AUTO_TEMPLATE and parameterized module to choose
      (setq template larumbe/verilog-auto-template-connected-ports)) ; Default template
    (insert template)
    (save-excursion
      (goto-char start-template)
      (replace-string "<module>" module-name))
    (if current-prefix-arg
        (when (equal larumbe/verilog-autoinst-autoparam-template (setq inst-template (larumbe/verilog-choose-autoinst))) ; If Universal Argument given, then ask for AUTOINST template
          (setq autoparam t))
      (setq inst-template larumbe/verilog-autoinst-template-simple)) ; Default AUTOINST with no parameters
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
    (larumbe/verilog-autoinst-processing)
    (when autoparam
      (larumbe/verilog-autoparam-processing))
    ;; Remove AUTO_TEMPLATE comment code
    (setq start-template (search-backward larumbe/verilog-auto-template-header))
    (setq start-instance (search-forward larumbe/verilog-auto-template-footer))
    (delete-region start-template (1+ start-instance))
    ;; Beautify instantiation
    (save-excursion
      (search-forward instance-name)
      (larumbe/verilog-indent-current-module module-name))
    (save-excursion
      (search-forward instance-name)
      (next-line 1)
      (larumbe/verilog-align-ports-current-module))
    (when autoparam
      (save-excursion
        (search-forward instance-name)
        (next-line 1)
        (larumbe/verilog-align-parameters-current-module module-name)))))


(defun larumbe/verilog-insert-instance-from-file-with-params (file)
  "Necessary to be passed as a parameter for Hydra templates"
  (interactive "FSelect module from file:")
  (setq current-prefix-arg 4)
  (larumbe/verilog-insert-instance-from-file file))


;;;; Testbenches
(defun larumbe/verilog-testbench-insert-template-simple (file)
  "WIP: Just a first sketch to check which AUTOS are needed"
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
    (larumbe/verilog-insert-instance-from-file file) ; Includes `verilog-auto' expansion
    (goto-char start)
    (search-forward "/*AUTOINOUTPARAM") ;; Postprocess /*AUTOINOUTPARAM*/
    (save-excursion
      (replace-regexp "logic[[:blank:]]+" "localparam " nil (point) (search-forward "// End of /*AUTOINOUTPARAM*/")))
    (save-excursion
      (replace-regexp "\\(localparam [a-zA-Z0-9_-]+\\);" "\\1 = 0;" nil (point) (search-forward "// End of /*AUTOINOUTPARAM*/")))
    (call-interactively #'larumbe/verilog-header-hp)
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



(defun larumbe/verilog-testbench-environment-clocks (file)
  "Create `tb_clocks' file and module from template"
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
  (larumbe/verilog-header-hp)
  (save-buffer))


(defun larumbe/verilog-testbench-environment-program (file)
  "Create `tb_program' module from template"
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
  (larumbe/verilog-header-hp)
  (save-buffer))


(defun larumbe/verilog-testbench-environment-defs-pkg (file)
  "Create `tb_defs_pkg' module from template"
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
  (larumbe/verilog-header-hp)
  (save-buffer))



(defun larumbe/verilog-testbench-environment-classes-pkg (file)
  "Create `tb_classes_pkg' module from template"
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
  (larumbe/verilog-header-hp)
  (save-buffer))


(defun larumbe/verilog-testbench-environment-top (file dut-file clocks-file)
  "Create `tb_classes_pkg' module from template"
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
  (larumbe/verilog-insert-instance-from-file dut-file) ; Includes `verilog-auto' expansion
  ;; Clocks
  (goto-char (point-min))
  (search-forward "// Clocks")
  (larumbe/verilog-insert-instance-from-file clocks-file)
  ;; Header and postprocessing
  (larumbe/verilog-header-hp)
  (save-buffer))





(defun larumbe/verilog-testbench-environment (dut-file dir)
  "DUT-FILE corresponds to the path of the DUT, assumming there is a module per file
Environment files will be created at specified DIR (clocks, program, defs_pkg, classes_pkg...)"
  (interactive "FSelect module from file: \nDSelect environment directory: ")
  (let ((module-name      (file-name-sans-extension (file-name-nondirectory dut-file)))
        (clocks-file      (concat (file-name-as-directory dir) "tb_clocks.sv"))
        (program-file     (concat (file-name-as-directory dir) "tb_program.sv"))
        (defs-pkg-file    (concat (file-name-as-directory dir) "tb_defs_pkg.sv"))
        (classes-pkg-file (concat (file-name-as-directory dir) "tb_classes_pkg.sv"))
        (top-file         (concat (file-name-as-directory dir) "tb_top.sv")))
    ;; Create Environment files
    (larumbe/verilog-testbench-environment-clocks      clocks-file)
    (larumbe/verilog-testbench-environment-program     program-file)
    (larumbe/verilog-testbench-environment-defs-pkg    defs-pkg-file)
    (larumbe/verilog-testbench-environment-classes-pkg classes-pkg-file)
    (larumbe/verilog-testbench-environment-top         top-file dut-file clocks-file)))


;;;; Case
(defun larumbe/verilog-case-template ()
  "Fetched and modified from `verilog-state-machine-add-case-fold' for sync FSMs"
  (interactive)
  (let (param-read)
    (insert "case (" (read-string "Expression: ") ")") (progn (electric-verilog-terminate-line) nil)
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (insert (concat param-read ": begin"))       (progn (electric-verilog-terminate-line) nil)
      (insert (concat "// Output statements... ")) (progn (electric-verilog-terminate-line) nil)
      (insert (concat "end"))                      (progn (electric-verilog-terminate-line) nil)
      (electric-verilog-terminate-line))
    (insert "endcase") (electric-verilog-terminate-line)))


;;;; Enum, Typedef, Struct
(defvar larumbe-verilog-enum-types '("logic" "bit" "int" "integer" "other"))

(defun larumbe/verilog-compute-vector-width ()
  "Will return [width-1:0] as a string for enum/struct templates.
If a number is set, then calculus will be automatically performed. If set to 0 or 1, then do not set a vector.
If a constant is set, then it will be set to [CONSTANT-1:0].
DANGER: If width introduced is 0, it will be assumed as a human mistake and width 1 will be computed"
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


(defun larumbe/verilog-enum-typedef-template (&optional typedef)
  "Insert enum contents for [typedef] enum template"
  (let (enum-item type (width ""))
    ;; Set typedef if specified
    (when typedef
      (insert "typedef "))
    ;; Select type for enum
    (setq type (completing-read "Type: " larumbe-verilog-enum-types))
    (if (string-equal type "other")
        (setq type (read-string "Type: ")))
    ;; Select width
    (if (or (string-equal type "logic") (string-equal type "bit"))
        (setq width (larumbe/verilog-compute-vector-width))
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


(defun larumbe/verilog-struct-typedef-template (&optional typedef union)
  "Insert enum contents for [typedef] struct template"
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
          (setq width (larumbe/verilog-compute-vector-width))
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
(defun larumbe/verilog-task-add-port (direction read)
  "Add inputs to task template"
  (let (type width)
    ;; Select type
    (setq type (read-string "Type: " "logic"))
    ;; Select width
    (if (or (string-equal type "logic") (string-equal type "bit"))
        (setq width (larumbe/verilog-compute-vector-width))
      (setq width "")) ; If not a vector disable width field
    ;; Insert port
    (insert direction " " type " " width " " read ",")
    (electric-verilog-terminate-line)))


(defun larumbe/verilog-task-custom ()
  "Insert a task definition."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (in-read out-read))
    (insert "task ")
    (insert (read-string "Task name: ") " (")
    (electric-verilog-terminate-line)
    (while (not(string-equal (setq in-read (read-string "Input signal: ")) ""))
      (larumbe/verilog-task-add-port "input" in-read))
    (while (not(string-equal (setq out-read (read-string "Output signal: ")) ""))
      (larumbe/verilog-task-add-port "output" out-read))
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
    (next-line)
    (verilog-pretty-declarations)
    (re-search-forward ");")
    (next-line)
    (electric-verilog-tab)))



;;;; Hydra
(defhydra hydra-verilog-template (:color blue
                                         :hint nil)
  "
RTL                          TESTBENCH                       COMMON
^^
_af_: always ff                _@_:  (posedge Clk)               _for_: for             _td_: typedef
_ac_: always comb              _in_: initial                     _ff_: function         _en_: enum
_aa_: always                   _ta_: task (1 line)               _ll_: logic signal     _te_: typedef enum
_ms_: module simple            _tk_: task template               _lv_: logic vector     _st_: struct
_md_: module w/params          _cl_: class                       _lp_: localparam       _ts_: typedef struct
_gn_: generate                 _fv_: forever                     _pm_: parameter        _un_: union
_it_: interface                _rp_: repeat                      _pc_: package          _tu_: typedef union
_mp_: modport                  _fj_: fork-join                   _bg_: begin/end        ^^
_cc_: case                     _fa_: fork-join any               _fe_: foreach          _/_: Star comment
_as_: assign                   _fn_: fork-join none              _if_: if               _B_: Block comment
_FS_: FSM sync                 _rn_: rand/constraint             _ei_: else if          _D_: Define signal
_IS_: Inst simple              _cb_: clocking block              _el_: else             _hd_: HP Header
_IP_: Inst w/params            _d_:  display                     _wh_: while            ^^
^^                             _ai_: assert immediate            _wd_: do-while         ^^
^^                             _ap_: assert property             ^^
^^                             _pr_: property                    ^^
^^                             _sq_: sequence                    ^^
^^                             _fl_: final                       ^^
^^                             _pg_: program                     ^^
^^                             _cg_: covergroup                  ^^
^^                             _TS_: Testbench Simple            ^^
^^                             _TE_: Testbench Environment       ^^
"
  ;;;;;;;;;
  ;; RTL ;;
  ;;;;;;;;;
  ("af"  (larumbe/hydra-yasnippet "af"))  ; always_ff
  ("ac"  (larumbe/hydra-yasnippet "ac"))  ; always_comb
  ("aa"  (larumbe/hydra-yasnippet "aa"))  ; always
  ("ms"  (larumbe/hydra-yasnippet "ms"))  ; module simple
  ("md"  (larumbe/hydra-yasnippet "md"))  ; module with parameter
  ("gn"  (larumbe/hydra-yasnippet "gn"))  ; generate
  ("it"  (larumbe/hydra-yasnippet "it"))  ; interface
  ("mp"  (larumbe/hydra-yasnippet "mp"))  ; Modport
  ("cc"  (larumbe/verilog-case-template)) ; case
  ("as"  (larumbe/hydra-yasnippet "as"))  ; assign
  ;; FSM
  ("FS"  (larumbe/verilog-state-machine-sync-custom)) ; Sync FSM
  ;; Instances from file
  ("IS"  (call-interactively #'larumbe/verilog-insert-instance-from-file))             ; Simple (no params)
  ("IP"  (call-interactively #'larumbe/verilog-insert-instance-from-file-with-params)) ; With params

  ;;;;;;;;;;;;;;;
  ;; TestBench ;;
  ;;;;;;;;;;;;;;;
  ("@"   (larumbe/hydra-yasnippet "@"))  ; Clk posedge
  ("in"  (larumbe/hydra-yasnippet "in")) ; Initial
  ("ta"  (larumbe/hydra-yasnippet "ta")) ; Task 1 line
  ("tk"  (larumbe/verilog-task-custom))  ; Task multiple ports
  ("cl"  (larumbe/hydra-yasnippet "cl")) ; Class
  ("fv"  (larumbe/hydra-yasnippet "fv")) ; Forever
  ("rp"  (larumbe/hydra-yasnippet "rp")) ; Repeat
  ("fj"  (larumbe/hydra-yasnippet "fj")) ; Fork-join
  ("fa"  (larumbe/hydra-yasnippet "fa")) ; Fork-join_any
  ("fn"  (larumbe/hydra-yasnippet "fn")) ; Fork-join_none
  ("rn"  (larumbe/hydra-yasnippet "rn")) ; Rand/Constraint
  ("cb"  (larumbe/hydra-yasnippet "cb")) ; Clocking block
  ("d"   (larumbe/hydra-yasnippet "d"))  ; Display for debug
  ("ai"  (larumbe/hydra-yasnippet "ai")) ; assert immediate
  ("ap"  (larumbe/hydra-yasnippet "ap")) ; assert property
  ("pr"  (larumbe/hydra-yasnippet "pr")) ; property
  ("sq"  (larumbe/hydra-yasnippet "sq")) ; sequence
  ("fl"  (larumbe/hydra-yasnippet "fl")) ; Final
  ("pg"  (larumbe/hydra-yasnippet "pg")) ; Program
  ("cg"  (larumbe/hydra-yasnippet "cg")) ; Covergroup
  ;; Testbench from DUT file
  ("TS"   (call-interactively #'larumbe/verilog-testbench-insert-template-simple))
  ("TE"   (call-interactively #'larumbe/verilog-testbench-environment))
  ;;  TODO: Coverage at some point?
  ;;      : More constraints, rand and randc
  ;;         - Distribution templates?

  ;;;;;;;;;;;;
  ;; Common ;;
  ;;;;;;;;;;;;
  ("for" (larumbe/hydra-yasnippet "for"))  ; For
  ("ff"  (larumbe/hydra-yasnippet "ff")) ; function
  ("ll"  (larumbe/hydra-yasnippet "ll")) ; logic signal
  ("lv"  (larumbe/hydra-yasnippet "lv")) ; logic vector
  ("lp"  (larumbe/hydra-yasnippet "lp")) ; Localparam
  ("pm"  (larumbe/hydra-yasnippet "pm")) ; Parameter
  ("pc"  (larumbe/hydra-yasnippet "pc")) ; Package
  ("bg"  (larumbe/hydra-yasnippet "bg")) ; begin/end
  ("fe"  (larumbe/hydra-yasnippet "fe")) ; Foreach
  ("if"  (larumbe/hydra-yasnippet "if"))
  ("ei"  (larumbe/hydra-yasnippet "ei")) ; Else if
  ("el"  (larumbe/hydra-yasnippet "el")) ; else
  ("wh"  (larumbe/hydra-yasnippet "wh")) ; While
  ("wd"  (larumbe/hydra-yasnippet "wd")) ; Do-while
  ("td"  (larumbe/hydra-yasnippet "td")) ; Generic typedef
  ("en"  (larumbe/verilog-enum-typedef-template nil))     ; Enum
  ("te"  (larumbe/verilog-enum-typedef-template t))       ; Typedef Enum
  ("st"  (larumbe/verilog-struct-typedef-template nil))   ; Struct
  ("ts"  (larumbe/verilog-struct-typedef-template t))     ; Typedef struct
  ("un"  (larumbe/verilog-struct-typedef-template nil t)) ; Union
  ("tu"  (larumbe/verilog-struct-typedef-template t t))   ; Typedef Union
  ("/"   (larumbe/hydra-yasnippet "/"))  ; Star comment
  ("B"   (larumbe/verilog-add-block-comment))
  ("D"   (larumbe/verilog-define-signal))
  ("hd"  (call-interactively #'larumbe/verilog-header-hp)) ; header for HP

  ;;;;;;;;;
  ;; UVM ;;
  ;;;;;;;;;
  ;; TODO: Check already existing templates
  ;; ("uc"  (larumbe/hydra-yasnippet "uvm-component"))
  ;; ("uo"  (larumbe/hydra-yasnippet "uvm-object"))

  ;;;;;;;;;;;;
  ;; Others ;;
  ;;;;;;;;;;;;
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))


(provide 'verilog-templates)

;;; verilog-templates.el ends here
