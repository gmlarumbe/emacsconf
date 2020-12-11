;;; vhdl-templates.el --- VHDL Templates  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun larumbe/vhdl-insert-instance-from-file (file)
  "Insert module instance at point from FILE.
Copied and adapted from `larumbe/verilog-insert-instance-from-file'"
  (interactive "FSelect entity from file:")
  (let* ((entity-name (with-temp-buffer
                        (insert-file-contents file)
                        (if (re-search-forward larumbe/vhdl-entity-re nil t)
                            (progn
                              (save-match-data
                                (vhdl-port-copy))
                              (match-string-no-properties 2))
                          (error "No VHDL entity found in that file!"))))
         (instance-name (read-string "Instance-name: " (concat "I_" (upcase entity-name)))))
    (vhdl-port-paste-instance instance-name)))


(defun larumbe/vhdl-insert-testbench-from-file (file)
  "Create testbench from entity of selected FILE in current buffer directory."
  (interactive "FSelect entity from file:")
  (let* ((entity-name (with-temp-buffer
                        (insert-file-contents file)
                        (if (re-search-forward larumbe/vhdl-entity-re nil t)
                            (progn
                              (save-match-data
                                (vhdl-port-copy))
                              (match-string-no-properties 2))
                          (error "No VHDL entity found in that file!")))))
    (if (buffer-file-name)
        (vhdl-port-paste-testbench)
      (error "Not visiting a file.  TB is created in current file directory!!"))))


;;;; Hydra
(defhydra hydra-vhdl-template (:color blue
                                      :hint nil)
  "
RTL                   TESTBENCH             COMMON            PACKAGES
^^
_ps_: process seq       _@_:  clocked wait      _for_: for          _pb_: package body
_pc_: process comb      _pr_: procedure         _fn_: function      _pd_: package declaration
_en_: entity            _rp_: report            _sg_: signal        _pkg_: library package
_ac_: architecture      _as_: assert            _va_: variable
_gn_: generate          _fl_: file              _ct_: constant
_cp_: component         _TS_: TestBench         _ge_: generic
_at_: attribute         ^^                      _ty_: type
_IS_: Instance          ^^                      _al_: alias
^^                      ^^                      _if_: if-then
^^                      ^^                      _cc_: case
^^                      ^^                      _wh_: while
^^                      ^^                      _hd_: header
"
  ;;;;;;;;;
  ;; RTL ;;
  ;;;;;;;;;
  ("ps"  (vhdl-template-process-seq))
  ("pc"  (vhdl-template-process-comb))
  ("en"  (vhdl-template-entity))
  ("ac"  (vhdl-template-architecture))
  ("gn"  (vhdl-template-generate))
  ("cp"  (vhdl-template-component))
  ("at"  (vhdl-template-attribute))
  ("IS"  (call-interactively #'larumbe/vhdl-insert-instance-from-file))

  ;;;;;;;;;;;;;;;
  ;; TestBench ;;
  ;;;;;;;;;;;;;;;
  ("@"  (vhdl-template-clocked-wait))
  ("pr" (vhdl-template-procedure))
  ("rp" (vhdl-template-report))
  ("as" (vhdl-template-assert))
  ("fl" (vhdl-template-file))
  ("TS"  (call-interactively #'larumbe/vhdl-insert-testbench-from-file))

  ;;;;;;;;;;;;
  ;; Common ;;
  ;;;;;;;;;;;;
  ("for" (vhdl-template-for))
  ("fn"  (vhdl-template-function))
  ("sg"  (vhdl-template-signal))
  ("va"  (vhdl-template-variable))
  ("ct"  (vhdl-template-constant))
  ("ge"  (vhdl-template-generic))
  ("ty"  (vhdl-template-type))
  ("al"  (vhdl-template-alias))
  ("if"  (vhdl-template-if-then))
  ("cc"  (vhdl-template-case))
  ("wh"  (vhdl-template-while-loop))
  ("hd"  (vhdl-template-header))

  ("pb"  (vhdl-template-package-body))
  ("pd"  (vhdl-template-package-decl))
  ("pkg" (call-interactively #'vhdl-template-insert-package))

  ;;;;;;;;;;;;
  ;; Others ;;
  ;;;;;;;;;;;;
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))


(provide 'vhdl-templates)

;;; vhdl-templates.el ends here
