;;; vhdl-projects.el --- VHDL Projects settings  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;;; Design hierarchy
;;
;; INFO: Fetched from `vhdl-mode' docstring:
;;
;; DESIGN HIERARCHY BROWSER:
;;   The speedbar can also be used for browsing the hierarchy of design units
;;   contained in the source files of the current directory or the specified
;;   projects (see option `vhdl-project-alist').
;;
;;     The speedbar can be switched between file, buffer, directory hierarchy and
;;   project hierarchy browsing mode in the speedbar menu or by typing `f', 'b',
;;   `h' or `H' in speedbar.
;;
;;     In speedbar, open design units with `mouse-2' on the name and browse
;;   their hierarchy with `mouse-2' on the `+'.  Ports can directly be copied
;;   from entities and components (in packages).  Individual design units and
;;   complete designs can directly be compiled (\"Make\" menu entry).
;;
;;     The hierarchy is automatically updated upon saving a modified source
;;   file when option `vhdl-speedbar-update-on-saving' is non-nil.  The
;;   hierarchy is only updated for projects that have been opened once in the
;;   speedbar.  The hierarchy is cached between Emacs sessions in a file (see
;;   options in group `vhdl-speedbar').
;;
;;     Simple design consistency checks are done during scanning, such as
;;   multiple declarations of the same unit or missing primary units that are
;;   required by secondary units.
;;
;;
;; More INFO:
;;  Keybindings for vhdl-speedbar Design Hierarchy view:
;;    - f: files
;;    - h: directory hierarchy
;;    - H: project hierarchy
;;    - b: buffers
;;    - SPC: Added additionally @ `init-vhdl' to toggle expand/contract level
;;
;; More INFO: The hierarchy extraction stop working with lexical binding enabling.
;;
;; DANGER: If pressing 'R' while in hierarchy mode to refresh hierarchy, make
;; sure of doing it with cursor on a line with text. Otherwise the error:
;; "speedbar-files-line-directory: Wrong type argument: stringp, nil" will show up.
;;
;; DANGER: From `vhdl-project-alist' docstring:
;; NOTE: Reflect the new setting in the choice list of option `vhdl-project'
;;       by RESTARTING EMACS."
;;
;;
;;;; Makefile generation
;;
;; MAKEFILE GENERATION:
;;   Makefiles can be generated automatically by an internal generation
;;   routine (`C-c M-k').  The library unit dependency information is
;;   obtained from the hierarchy browser.  Makefile generation can be
;;   customized for each compiler in option `vhdl-compiler-alist'.
;;
;;     Makefile generation can also be run non-interactively using the
;;   command:
;;
;;       $emacs -batch -l ~/.emacs -l vhdl-mode
;;             [-compiler compilername] [-project projectname]
;;             -f vhdl-generate-makefile
;;
;;     The Makefile's default target \"all\" compiles the entire design, the
;;   target \"clean\" removes it and the target \"library\" creates the
;;   library directory if not existent.  These target names can be customized
;;   by option `vhdl-makefile-default-targets'.  The Makefile also includes a
;;   target for each primary library unit which allows selective compilation
;;   of this unit, its secondary units and its subhierarchy (example:
;;   compilation of a design specified by a configuration).  User specific
;;   parts can be inserted into a Makefile with option
;;   `vhdl-makefile-generation-hook'.
;;
;;; Code:


(require 'vhdl-mode)


;;;; Config
(setq vhdl-project "axi_if_converter")
(setq vhdl-project-alist

;;;; MAIN Project
      '(
        (;; Name
         "axi_if_converter"
         ;; Title
         "AXI Interface Converter"
         ;; Default directory
         "/home/gonz/Programming/FPGA/axi_if_converter/"
         ;; Sources (only RTL included) as directories (could be included
         ;; recursively or individually)
         ("src/axi_lite_master/rtl/"
          "src/axi_lite_regs/rtl/"
          "src/core_conv/rtl/"
          "src/core_fsm/rtl/"
          "src/input_buffer/rtl/"
          "src/misc/"
          "src/pattern_counter/rtl/"
          "src/top/rtl/"
          )
         ;; Exclude regexp
         ""
         ;; Compile options
         nil
         ;; Compile directory
         "./"
         ;; Library name
         "xil_defaultlib"
         ;; Library directory
         "library/xil_defaultlib/"
         ;; Makefile name
         ""
         ;; Description
         "")

;;;; SUBCOMPONENT project
        (;; Name
         "pattern_counter"
         ;; Title
         ""
         ;; Default directory
         "/home/gonz/Programming/FPGA/axi_if_converter/src/pattern_counter/"
         ;; Sources
         ("rtl/" "tb/")
         ;; Exclude regexp
         ""
         ;; Compile options
         nil
         ;; Compile directory
         "compile/"
         ;; Library name
         "xil_defaultlib"
         ;; Library directory
         "xil_defaultlib/"
         ;; Makefile name
         ""
         ;; Description
         "")

;;;; TinyALU project
        (;; Name
         "tinyalu"
         ;; Title
         ""
         ;; Default directory
         "/home/gonz/Programming/doc/SystemVerilog/UVM/uvmprimer/code/02_Conventional_Testbench/"
         ;; Sources
         ("tinyalu_dut/")
         ;; Exclude regexp
         ""
         ;; Compile options
         nil
         ;; Compile directory
         "./"
         ;; Library name
         "work"
         ;; Library directory
         "work/"
         ;; Makefile name
         ""
         ;; Description
         "")

        ))


(provide 'vhdl-projects)

;;; vhdl-projects.el ends here
