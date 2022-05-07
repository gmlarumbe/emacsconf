;;; verilog-font-lock.el --- Verilog Custom Font Lock  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'init-hdl-font-lock)
(require 'verilog-mode)
(require 'verilog-navigation)
(require 'verilog-rx)

(defvar verilog-ext-uvm-classes-face 'verilog-ext-uvm-classes-face)
(defface verilog-ext-uvm-classes-face
  '((t (:foreground "light blue")))
  "Face for UVM classes."
  :group 'hdl-font-lock-highlighting-faces)


;; TODO: Maybe move them somewhere else?
;; Variable declaration type/name font-lock
(defvar verilog-ext-highlight-variable-declaration-names nil)
(defvar verilog-ext-keywords-no-types '("`__FILE__" "`__LINE" "`begin_keywords" "`celldefine" "`default_nettype" "`define" "`else" "`elsif" "`end_keywords" "`endcelldefine" "`endif" "`ifdef" "`ifndef" "`include"
                                            "`line" "`nounconnected_drive" "`pragma" "`resetall" "`timescale" "`unconnected_drive" "`undef" "`undefineall" "`case" "`default" "`endfor" "`endprotect" "`endswitch"
                                            "`endwhile" "`for" "`format" "`if" "`let" "`protect" "`switch" "`timescale" "`time_scale" "`while" "after" "alias" "always" "always_comb" "always_ff" "always_latch"
                                            "assert" "assign" "assume" "automatic" "before" "begin" "bind" "bins" "binsof" "bit" "break" "byte" "case" "casex" "casez" "cell" "chandle" "class" "clocking" "config"
                                            "const" "constraint" "context" "continue" "cover" "covergroup" "coverpoint" "cross" "deassign" "default" "design" "disable" "dist" "do" "edge" "else" "end" "endcase"
                                            "endclass" "endclocking" "endconfig" "endfunction" "endgenerate" "endgroup" "endinterface" "endmodule" "endpackage" "endprimitive" "endprogram" "endproperty" "endspecify"
                                            "endsequence" "endtable" "endtask" "enum" "event" "expect" "export" "extends" "extern" "final" "first_match" "for" "force" "foreach" "forever" "fork" "forkjoin" "function"
                                            "generate" "genvar" "highz0" "highz1" "if" "iff" "ifnone" "ignore_bins" "illegal_bins" "import" "incdir" "include" "initial" "inside" "instance" "int" "interface" "intersect"
                                            "join" "join_any" "join_none" "large" "liblist" "library" "local" "longint" "macromodule" "matches" "medium" "modport" "module" "negedge" "new" "noshowcancelled" "null"
                                            "package" "packed" "posedge" "primitive" "priority" "program" "property" "protected" "pulsestyle_onevent" "pulsestyle_ondetect" "pure" "rand" "randc" "randcase"
                                            "randsequence" "ref" "release" "repeat" "return" "scalared" "sequence" "shortint" "shortreal" "showcancelled" "signed" "small" "solve" "specify"
                                            "specparam" "static" "string" "strong0" "strong1" "struct" "super" "supply0" "supply1" "table" "tagged" "task" "this" "throughout"
                                            "timeprecision" "timeunit" "type" "typedef" "union" "unique" "unsigned" "use" "uwire" "var" "vectored" "virtual" "void" "wait"
                                            "wait_order" "weak0" "weak1" "while" "wildcard" "with" "within" "accept_on" "checker" "endchecker" "eventually" "global" "implies" "let"
                                            "nexttime" "reject_on" "restrict" "s_always" "s_eventually" "s_nexttime" "s_until" "s_until_with" "strong" "sync_accept_on" "sync_reject_on" "unique0" "until" "until_with"
                                            "untyped" "weak" "implements"
                                            "interconnect" "nettype" "soft"))
;; Obtained with: (dolist (word (cl-set-difference verilog-keywords verilog-type-keywords :test #'equal)) (insert "\"" word "\" "))
(defvar verilog-ext-keywords-no-types-re (regexp-opt verilog-ext-keywords-no-types 'symbols))

;;;; Functions
;; INFO: Search based fontification:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Search_002dbased-Fontification.html
;;     Look for 'function' section.
;; - Based on `verilog-match-translate-off'

(defun verilog-ext-find-verilog-module-instance-fontify (limit)
  "Search based fontification function of Verilog modules/instances.
Arg LIMIT is used internally for fontification."
  (let (start-line end-line)
    (when (verilog-ext-find-module-instance-fwd limit)
      (setq start-line (save-excursion
                         (goto-char (match-beginning 0))
                         (point-at-bol)))
      (setq end-line (save-excursion
                       (goto-char (match-end 0))
                       (point-at-eol)))
      (unless (get-text-property (point) 'font-lock-multiline)
        (put-text-property start-line end-line 'font-lock-multiline t))
      (point))))


(defun verilog-ext-match-translate-off-fontify (limit)
  "Match a translate-off block, setting `match-data' and returning t, else nil.
Bound search by LIMIT.

Copied from `verilog-match-translate-off' but
including `font-lock-multiline' property."
  (when (< (point) limit)
    (let ((start (or (verilog-within-translate-off)
                     (verilog-start-translate-off limit)))
          (case-fold-search t))
      (when start
        (let ((end (or (verilog-end-translate-off limit) limit)))
          (put-text-property start end 'font-lock-multiline t)
          (set-match-data (list start end))
          (goto-char end))))))


(defun verilog-ext-find-verilog-variable-type-fwd (regex limit)
  "Generic search based fontification function of Verilog variable types.
INFO: It is not necessary to check that variable is not within string/comment
since these both have precedence over custom fontify.

Search for REGEX bound to LIMIT."
  (let ((found nil)
        (pos)
        (case-fold-search verilog-case-fold)
        (type)
        (name))
    (save-excursion
      (while (and (not found)
                  (re-search-forward regex limit t))
        (setq type (match-string-no-properties 1))
        (setq name (match-string-no-properties 3))
        (unless (or (string-match verilog-ext-keywords-no-types-re type)
                    (string-match verilog-ext-keywords-no-types-re name))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-verilog-variable-fwd-1 (limit)
  (verilog-ext-find-verilog-variable-type-fwd verilog-ext-variable-re-1 limit))

(defun verilog-ext-find-verilog-variable-fwd-2 (limit)
  (verilog-ext-find-verilog-variable-type-fwd verilog-ext-variable-re-2 limit))

(defun verilog-ext-find-verilog-variable-fwd-3 (limit)
  (verilog-ext-find-verilog-variable-type-fwd verilog-ext-variable-re-3 limit))


(defun verilog-ext-find-verilog-variable-type-fontify-1 (limit)
  "Search based fontification function of Verilog type 1 variable types.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-1 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-name-fontify-1 (limit)
  "Search based fontification function of Verilog type 1 variable names.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-1 limit)
      (setq start (match-beginning 3))
      (setq end (match-end 3))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-type-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable types.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-2 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-name-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable names.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-2 limit)
      (setq start (match-beginning 2))
      (setq end (match-end 2))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-type-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable types.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-3 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-name-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable names.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-3 limit)
      (setq start (match-beginning 3))
      (setq end (match-end 3))
      (set-match-data (list start end))
      (point))))



;;;; Font-lock keywords
(defvar verilog-ext-type-font-keywords
  (regexp-opt
   '("and" "buf" "bufif0" "bufif1" "cmos" "defparam" "event"
     "genvar" "highz0" "highz1" "inout" "input" "integer"
     "localparam" "mailbox" "nand" "nmos" "nor" "not" "notif0"
     "notif1" "or" "output" "parameter" "pmos" "pull0" "pull1"
     "pulldown" "pullup" "rcmos" "real" "realtime" "reg" "rnmos"
     "specparam" "strong0" "strong1" "supply" "supply0" "supply1"
     "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1" "triand"
     "trior" "trireg" "unsigned" "uwire" "vectored" "wand" "weak0"
     "weak1" "wire" "wor" "xnor" "xor" "signed"
     ;; 1800-2005
     "bit" "byte" "chandle" "const" "enum" "int" "logic" "longint"
     "packed" "ref" "shortint" "shortreal" "static" "string"
     "struct" "type" "typedef" "union" "var"
     ;; 1800-2009
     ;; 1800-2012
     "interconnect" "nettype" ) nil))

(defvar verilog-ext-pragma-keywords
  (regexp-opt
   '("surefire" "0in" "auto" "leda" "rtl_synthesis" "verilint"
     ;; Recognized by Vivado (check Xilinx attribute 'translate_off/translate_on'):
     "synthesis" "synopsys" "pragma") nil))


;; https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_3/ug901-vivado-synthesis.pdf
;; Chapter 2 (Some of them are also supported at XDC)
(defvar verilog-ext-xilinx-attributes
  (regexp-opt
   '("async_reg" "black_box" "cascade_height" "clock_buffer_type"
     "direct_enable" "direct_reset" "dont_touch" "extract_enable"
     "extract_reset" "fsm_encoding" "fsm_safe_state" "full_case"
     "gated_clock" "iob" "io_buffer_type" "keep" "keep_hierarchy"
     "mark_debug" "max_fanout" "parallel_case" "ram_decomp" "ram_style"
     "retiming_backward" "retiming_forward" "rom_style" "shreg_extract"
     "srl_style" "translate_off" "translate_on" "use_dsp"
     ;; uppercase
     "async_reg" "BLACK_BOX" "CASCADE_HEIGHT" "CLOCK_BUFFER_TYPE"
     "DIRECT_ENABLE" "DIRECT_RESET" "DONT_TOUCH" "EXTRACT_ENABLE"
     "EXTRACT_RESET" "FSM_ENCODING" "FSM_SAFE_STATE" "FULL_CASE"
     "GATED_CLOCK" "IOB" "IO_BUFFER_TYPE" "KEEP" "KEEP_HIERARCHY"
     "MARK_DEBUG" "MAX_FANOUT" "PARALLEL_CASE" "RAM_DECOMP" "RAM_STYLE"
     "RETIMING_BACKWARD" "RETIMING_FORWARD" "ROM_STYLE" "SHREG_EXTRACT"
     "SRL_STYLE" "TRANSLATE_OFF" "TRANSLATE_ON" "USE_DSP"
     ) nil))


(defvar verilog-ext-font-general-keywords
  (regexp-opt
   ;; INFO: Same as the one in `verilog-mode' but excluding "include"
   ;; as it must be highlighted as a macro instead.
   ;; INFO: Have changed macro priority over keywords.
   ;; INFO: Also excluding 'this' to highlight it in green, same as python
   '("always" "assign" "automatic" "case" "casex" "casez" "cell"
     "config" "deassign" "default" "design" "disable" "edge" "else"
     "endcase" "endconfig" "endfunction" "endgenerate" "endmodule"
     "endprimitive" "endspecify" "endtable" "endtask" "for" "force"
     "forever" "fork" "function" "generate" "if" "ifnone" "incdir"
     "initial" "instance" "join" "large" "liblist"
     "library" "macromodule" "medium" "module" "negedge"
     "noshowcancelled" "posedge" "primitive" "pulsestyle_ondetect"
     "pulsestyle_onevent" "release" "repeat" "scalared"
     "showcancelled" "small" "specify" "strength" "table" "task"
     "use" "wait" "while"
     ;; 1800-2005
     "alias" "always_comb" "always_ff" "always_latch" "assert"
     "assume" "before" "bind" "bins" "binsof" "break" "class"
     "clocking" "constraint" "context" "continue" "cover"
     "covergroup" "coverpoint" "cross" "dist" "do" "endclass"
     "endclocking" "endgroup" "endinterface" "endpackage"
     "endprogram" "endproperty" "endsequence" "expect" "export"
     "extends" "extern" "final" "first_match" "foreach" "forkjoin"
     "iff" "ignore_bins" "illegal_bins" "import" "inside"
     "interface" "intersect" "join_any" "join_none" "local"
     "matches" "modport" "new" "null" "package" "priority"
     "program" "property" "protected" "pure" "rand" "randc"
     "randcase" "randsequence" "return" "sequence" "solve" "super"
     "tagged" "throughout" "timeprecision" "timeunit"
     "unique" "virtual" "void" "wait_order" "wildcard" "with"
     "within"
     ;; 1800-2009
     "accept_on" "checker" "endchecker" "eventually" "global"
     "implies" "let" "nexttime" "reject_on" "restrict" "s_always"
     "s_eventually" "s_nexttime" "s_until" "s_until_with" "strong"
     "sync_accept_on" "sync_reject_on" "unique0" "until"
     "until_with" "untyped" "weak"
     ;; 1800-2012
     "implements" "soft" ) nil))

(defvar verilog-ext-font-grouping-keywords
  (regexp-opt
   '( "begin" "end" "this") nil))  ; "this" is not grouping but looks better in green

(defvar verilog-ext-special-macros
  (regexp-opt
   '( ;; DMA Macros
     "DMA_MASTER_V2K_PORTS_READ" "DMA_MASTER_V2K_PORTS_WRITE" "DMA_MASTER_V2K_PORTS" "DMA_MASTER_V2K_PORTS_QOS"
     "DMA_MASTER_V2K_PORTS_ACE" "DMA_MASTER_V2K_PORTS_ACE_QOS" "DMA_MASTER_V2K_PORTS_MON" "DMA_MASTER_IO_DECS_READ"
     "DMA_MASTER_IO_DECS_WRITE" "DMA_MASTER_IO_DECS" "DMA_MASTER_IO_DECS_QOS" "DMA_SLAVE_V2K_PORTS_READ"
     "DMA_SLAVE_V2K_PORTS_WRITE" "DMA_SLAVE_V2K_PORTS" "DMA_SLAVE_V2K_PORTS_QOS" "DMA_SLAVE_V2K_PORTS_ACE"
     "DMA_SLAVE_V2K_PORTS_ACE_QOS" "DMA_SLAVE_V2K_PORTS_ACELITE_QOS" "DMA_SLAVE_IO_DECS_READ" "DMA_SLAVE_IO_DECS_WRITE"
     "DMA_SLAVE_IO_DECS" "DMA_PORTS_READ" "DMA_PORTS_WRITE" "DMA_PORTS" "DMA_PORTS_QOS" "DMA_HP_TRACE_V2K_PORTS" "DMA_INST_CONNS_READ"
     "DMA_INST_CONNS_WRITE" "DMA_INST_CONNS" "DMA_INST_CONNS_QOS" "DMA_INST_CONNS_ACE" "DMA_INST_CONNS_ACE_QOS"
     "DMA_INST_CONNS_ACELITE_QOS" "DMA_INST_CONNS_NO_LC_READ" "DMA_INST_CONNS_NO_LC_WRITE" "DMA_INST_CONNS_NO_LC" "DMA_INST_CONNS_NO_LCPI_READ"
     "DMA_INST_CONNS_NO_LCPI_WRITE" "DMA_INST_CONNS_NO_LCPI" "DMA_INST_CONNS_READ_UC" "DMA_INST_CONNS_WRITE_UC" "DMA_INST_CONNS_UC"
     "DMA_INST_CONNS_READ_LC" "DMA_INST_CONNS_WRITE_LC" "DMA_INST_CONNS_LC" "DMA_INST_CONNS_LC_QOS" "DMA_INST_CONNS_ADDR_PAD_READ"
     "DMA_INST_CONNS_ADDR_PAD_WRITE" "DMA_INST_CONNS_ADDR_PAD" "DMA_INST_CONNS_ADDR_PAD_QOS" "DMA_INST_CONNS_ADDR_PAD_ACE"
     "DMA_INST_CONNS_ADDR_PAD_ACE_QOS" "DMA_INST_CONNS_ADDR_PAD_ACELITE_QOS" "DMA_INST_CONNS_ADDR_TRUNC_READ"
     "DMA_INST_CONNS_ADDR_TRUNC_WRITE" "DMA_INST_CONNS_ADDR_TRUNC" "DMA_INST_CONNS_ADDR_TRUNC_QOS" "DMA_INST_CONNS_ADDR_TRUNC_ACE"
     "DMA_INST_CONNS_ADDR_TRUNC_ACE_QOS" "DMA_INST_CONNS_ADDR_TRUNC_ACELITE_QOS" "DMA_INST_CONNS_ADDR_TRUNC_READ_UC" "DMA_INST_CONNS_ADDR_TRUNC_WRITE_UC"
     "DMA_INST_CONNS_ADDR_TRUNC_UC" "DMA_INST_HP_TRACE_CONNS" "DMA_WIRES_READ" "DMA_WIRES_WRITE"
     "DMA_WIRES" "DMA_WIRES_QOS" "DMA_WIRES_ACE" "DMA_WIRES_ACE_QOS"
     "DMA_WIRES_ACELITE_QOS" "DMA_WIRES_NO_LC_READ" "DMA_WIRES_NO_LC_WRITE" "DMA_WIRES_NO_LC"
     "DMA_WIRES_NO_LCP_READ" "DMA_WIRES_NO_LCP_WRITE" "DMA_WIRES_NO_LCP" "DMA_HP_TRACE_WIRES"
     "DMA_MASTER_EXCLUDE_ASSIGNS_READ" "DMA_MASTER_EXCLUDE_ASSIGNS_WRITE" "DMA_MASTER_EXCLUDE_ASSIGNS" "DMA_MASTER_EXCLUDE_ASSIGNS_QOS"
     "DMA_MASTER_EXCLUDE_ASSIGNS_ACE" "DMA_MASTER_EXCLUDE_ASSIGNS_ACE_QOS" "DMA_MASTER_EXCLUDE_ASSIGNS_ACELITE_QOS" "DMA_SLAVE_EXCLUDE_ASSIGNS_READ"
     "DMA_SLAVE_EXCLUDE_ASSIGNS_WRITE" "DMA_SLAVE_EXCLUDE_ASSIGNS" "DMA_SLAVE_EXCLUDE_ASSIGNS_ACE_QOS" "DMA_SLAVE_EXCLUDE_ASSIGNS_ACELITE_QOS"
     "DMA_MON_EXCLUDE_ASSIGNS" "DMA_PASS_THRU_NO_LC_READ" "DMA_PASS_THRU_NO_LC_WRITE" "DMA_PASS_THRU_NO_LC"
     "DMA_PASS_THRU_READ" "DMA_PASS_THRU_WRITE" "DMA_PASS_THRU" "DMA_PASS_THRU_QOS"
     "DMA_PASS_THRU_MON" "DMA_PASS_THRU_MON_NO_LC" "DMA_S_TO_M0_AND_M1_READ" "DMA_S_TO_M0_AND_M1_WRITE"
     "DMA_S_TO_M0_AND_M1" "DMA_S_TO_M0_AND_M1_QOS" "DMA_NO_LC_ASSIGNS" "DMA_NO_LCP_ASSIGNS"
     "DMA_NO_LCQ_ASSIGNS" "DMA_READ_ONLY_ASSIGNS" "DMA_WRITE_ONLY_ASSIGNS" "HP_TRACE_ASSIGNS"
     "AXI_TRACE_CODE" "AXI_MASTER_VALID_CHECKS" "AXI_SLAVE_VALID_CHECKS" "AXI_PACER_CONNECT"
     "AXI_PACING_CHECK" "AXI_PACING_CHECK_AHB_TO_AXI" "AXI_PACING_CHECK_ANSIBLE_TO_AXI" "AXI_PACING_CHECK_EBD2AXI"
     "AXI_PACING_CHECK_A_SERIES" "AXI_PACING_CHECK_MDMA"

     ;; Regbus macros
     "REGBUS_SINGLE_V2K_PORTS" "REGBUS_SUPER_V2K_PORTS" "REGBUS_RD_SIGS_V2K_PORTS" "REGBUS_RD_SIGS_V2K_PORTS_IN"
     "REGBUS_RD_SIGS_NO_RESP_V2K_PORTS" "REGBUS_RD_SIGS_NO_RESP_V2K_PORTS_IN" "REGBUS_RD_SIGS_EXCLUDE_ASSIGNS" "REGBUS_RD_SIGS_NO_RESP_EXCLUDE_ASSIGNS"
     "REGBUS_SINGLE_INST_CONNS" "REGBUS_SINGLE_NO_RESP_INST_CONNS" "REGBUS_SUPER_INST_CONNS" "REGBUS_RD_SIGS_INST_CONNS"
     "REGBUS_RD_SIGS_NO_RESP_INST_CONNS" "REGBUS_RD_SIGS_WIRES" "REGBUS_RD_SIGS_NO_RESP_WIRES" "REGBUS_SUPER_SINGLE_V2K_PORTS"
     "REGBUS_SUPER_SINGLE_INST_CONNS"

     ;; SRAM Macros
     "SRAM_SP_V2K_PORTS" "SRAM_TP_V2K_PORTS" "SRAM_DP_V2K_PORTS" "SRAM_DP_RW_R_V2K_PORTS"
     "SRAM_DP_R_RW_V2K_PORTS" "SRAM_DP_RW_W_V2K_PORTS" "SRAM_DP_W_RW_V2K_PORTS" "SRAM_RW_V2K_PORTS"
     "SRAM_WO_V2K_PORTS" "SRAM_RO_V2K_PORTS" "SRAM_SP_V95_PORTS" "SRAM_TP_V95_PORTS"
     "SRAM_DP_V95_PORTS" "SRAM_DP_RW_R_V95_PORTS" "SRAM_DP_R_RW_V95_PORTS" "SRAM_DP_RW_W_V95_PORTS"
     "SRAM_DP_W_RW_V95_PORTS" "SRAM_RW_V95_PORTS" "SRAM_WO_V95_PORTS" "SRAM_RO_V95_PORTS"
     "SRAM_SP_V95_IO_DECS" "SRAM_TP_V95_IO_DECS" "SRAM_DP_V95_IO_DECS" "SRAM_DP_RW_R_V95_IO_DECS"
     "SRAM_DP_R_RW_V95_IO_DECS" "SRAM_DP_RW_W_V95_IO_DECS" "SRAM_DP_W_RW_V95_IO_DECS" "SRAM_RW_V95_IO_DECS"
     "SRAM_WO_V95_IO_DECS" "SRAM_RO_V95_IO_DECS" "SRAM_SP_INST_CONNS" "SRAM_TP_INST_CONNS"
     "SRAM_DP_INST_CONNS" "SRAM_DP_RW_R_INST_CONNS" "SRAM_DP_R_RW_INST_CONNS" "SRAM_DP_RW_W_INST_CONNS"
     "SRAM_DP_W_RW_INST_CONNS" "SRAM_SP_INST_CONNS2" "SRAM_TP_INST_CONNS2" "SRAM_DP_INST_CONNS2"
     "SRAM_DP_RW_R_INST_CONNS2" "SRAM_DP_R_RW_INST_CONNS2" "SRAM_DP_RW_W_INST_CONNS2" "SRAM_DP_W_RW_INST_CONNS2"
     "SRAM_RW_INST_CONNS" "SRAM_WO_INST_CONNS" "SRAM_RO_INST_CONNS" "SRAM_SP_WIRES"
     "SRAM_TP_WIRES" "SRAM_DP_WIRES" "SRAM_DP_RW_R_WIRES" "SRAM_DP_R_RW_WIRES"
     "SRAM_DP_RW_W_WIRES" "SRAM_DP_W_RW_WIRES" "SRAM_RW_WIRES" "SRAM_WO_WIRES"
     "SRAM_RO_WIRES" "SRAM_SP_EXCLUDE_ASSIGNS" "SRAM_TP_EXCLUDE_ASSIGNS" "SRAM_DP_EXCLUDE_ASSIGNS"
     "SRAM_DP_RW_R_EXCLUDE_ASSIGNS" "SRAM_DP_R_RW_EXCLUDE_ASSIGNS" "SRAM_DP_RW_W_EXCLUDE_ASSIGNS" "SRAM_DP_W_RW_EXCLUDE_ASSIGNS"
     "SRAM_RW_EXCLUDE_ASSIGNS" "SRAM_WO_EXCLUDE_ASSIGNS" "SRAM_RO_EXCLUDE_ASSIGNS" "SRAM_SP_LJRBIST_ASSIGNS"
     "SRAM_TP_LJRBIST_ASSIGNS" "SRAM_DP_LJRBIST_ASSIGNS"
     )
   nil)) ; Used for non-verilog constructs (i.e. custom preprocessing)

(defvar verilog-ext-special-constructs
  (regexp-opt
   '(;; These constructs contain some special character that prevent them to be detected as symbols
     "@include" "@replace_ifdef" "@replace_end" "@insert_ifdef"
     "@macro_begin" "@macro_end"
     "@if" "@else" "@endif"
     "@comment"
     "@define" "@define_begin" "@define_end"

     "%include" "%register"
     )
   nil)) ; Used for non-verilog constructs (i.e. custom preprocessing)


(defvar verilog-ext-uvm-classes
  (regexp-opt
   '(; Fetched through grep -R of classes starting with uvm_* and subsequent processing
     ; Does not include internal classes (such as m_uvm_*), nor enums, nor non-class typedefs such as vector derived
     "uvm_agent" "uvm_algorithmic_comparator" "uvm_analysis_export" "uvm_analysis_imp" "uvm_analysis_port" "uvm_barrier"
     "uvm_bit_rsrc" "uvm_blocking_get_export" "uvm_blocking_get_imp" "uvm_blocking_get_peek_export" "uvm_blocking_get_peek_imp" "uvm_blocking_get_peek_port"
     "uvm_blocking_get_port" "uvm_blocking_master_export" "uvm_blocking_master_imp" "uvm_blocking_master_port" "uvm_blocking_peek_export" "uvm_blocking_peek_imp"
     "uvm_blocking_peek_port" "uvm_blocking_put_export" "uvm_blocking_put_imp" "uvm_blocking_put_port" "uvm_blocking_slave_export" "uvm_blocking_slave_imp"
     "uvm_blocking_slave_port" "uvm_blocking_transport_export" "uvm_blocking_transport_imp" "uvm_blocking_transport_port" "uvm_bogus_class" "uvm_bottomup_phase"
     "uvm_build_phase" "uvm_built_in_clone" "uvm_built_in_comp" "uvm_built_in_converter" "uvm_built_in_pair" "uvm_byte_rsrc"
     "uvm_callback" "uvm_callback_iter" "uvm_callbacks" "uvm_callbacks_base" "uvm_callbacks_objection" "uvm_check_phase"
     "uvm_class_clone" "uvm_class_comp" "uvm_class_converter" "uvm_class_pair" "uvm_cmd_line_verb" "uvm_cmdline_processor"
     "uvm_comparer" "uvm_component" "uvm_component_registry" "uvm_config_db" "uvm_config_db_options" "uvm_config_object_wrapper"
     "uvm_configure_phase" "uvm_connect_phase" "uvm_copy_map" "uvm_derived_callbacks" "uvm_domain" "uvm_driver"
     "uvm_end_of_elaboration_phase" "uvm_env" "uvm_event" "uvm_event_callback" "uvm_event_pool" "uvm_exhaustive_sequence"
     "uvm_external_connector" "uvm_extract_phase" "uvm_factory" "uvm_factory_override" "uvm_factory_queue_class" "uvm_final_phase"
     "uvm_get_export" "uvm_get_imp" "uvm_get_peek_export" "uvm_get_peek_imp" "uvm_get_peek_port" "uvm_get_port"
     "uvm_hdl_path_concat" "uvm_heartbeat" "uvm_heartbeat_callback" "uvm_if_base_abstract" "uvm_in_order_built_in_comparator" "uvm_in_order_class_comparator"
     "uvm_in_order_comparator" "uvm_int_rsrc" "uvm_line_printer" "uvm_main_phase" "uvm_master_export" "uvm_master_imp"
     "uvm_master_port" "uvm_mem" "uvm_mem_access_seq" "uvm_mem_mam" "uvm_mem_mam_cfg" "uvm_mem_mam_policy"
     "uvm_mem_region" "uvm_mem_shared_access_seq" "uvm_mem_single_access_seq" "uvm_mem_single_walk_seq" "uvm_mem_walk_seq" "uvm_monitor"
     "uvm_nonblocking_get_export" "uvm_nonblocking_get_imp" "uvm_nonblocking_get_peek_export" "uvm_nonblocking_get_peek_imp" "uvm_nonblocking_get_peek_port" "uvm_nonblocking_get_port"
     "uvm_nonblocking_master_export" "uvm_nonblocking_master_imp" "uvm_nonblocking_master_port" "uvm_nonblocking_peek_export" "uvm_nonblocking_peek_imp" "uvm_nonblocking_peek_port"
     "uvm_nonblocking_put_export" "uvm_nonblocking_put_imp" "uvm_nonblocking_put_port" "uvm_nonblocking_slave_export" "uvm_nonblocking_slave_imp" "uvm_nonblocking_slave_port"
     "uvm_nonblocking_transport_export" "uvm_nonblocking_transport_imp" "uvm_nonblocking_transport_port" "uvm_obj_rsrc" "uvm_object" "uvm_object_registry"
     "uvm_object_string_pool" "uvm_object_wrapper" "uvm_objection" "uvm_objection_callback" "uvm_objection_context_object" "uvm_objection_events"
     "uvm_packer" "uvm_peek_export" "uvm_peek_imp" "uvm_peek_port" "uvm_phase" "uvm_pool"
     "uvm_port_base" "uvm_port_component" "uvm_port_component_base" "uvm_post_configure_phase" "uvm_post_main_phase" "uvm_post_reset_phase"
     "uvm_post_shutdown_phase" "uvm_pre_configure_phase" "uvm_pre_main_phase" "uvm_pre_reset_phase" "uvm_pre_shutdown_phase" "uvm_predict_s"
     "uvm_printer" "uvm_printer_knobs" "uvm_push_driver" "uvm_push_sequencer" "uvm_put_export" "uvm_put_imp"
     "uvm_put_port" "uvm_queue" "uvm_random_sequence" "uvm_random_stimulus" "uvm_recorder" "uvm_reg"
     "uvm_reg_access_seq" "uvm_reg_adapter" "uvm_reg_backdoor" "uvm_reg_bit_bash_seq" "uvm_reg_block" "uvm_reg_cbs"
     "uvm_reg_field" "uvm_reg_fifo" "uvm_reg_file" "uvm_reg_frontdoor" "uvm_reg_hw_reset_seq" "uvm_reg_indirect_data"
     "uvm_reg_indirect_ftdr_seq" "uvm_reg_item" "uvm_reg_map" "uvm_reg_map_info" "uvm_reg_mem_access_seq" "uvm_reg_mem_built_in_seq"
     "uvm_reg_mem_hdl_paths_seq" "uvm_reg_mem_shared_access_seq" "uvm_reg_predictor" "uvm_reg_read_only_cbs" "uvm_reg_sequence" "uvm_reg_shared_access_seq"
     "uvm_reg_single_access_seq" "uvm_reg_single_bit_bash_seq" "uvm_reg_tlm_adapter" "uvm_reg_write_only_cbs" "uvm_report_catcher" "uvm_report_global_server"
     "uvm_report_handler" "uvm_report_object" "uvm_report_phase" "uvm_report_server" "uvm_reset_phase" "uvm_resource"
     "uvm_resource_base" "uvm_resource_db" "uvm_resource_db_options" "uvm_resource_options" "uvm_resource_pool" "uvm_resource_types"
     "uvm_root" "uvm_root_report_handler" "uvm_run_phase" "uvm_scope_stack" "uvm_scoreboard" "uvm_seed_map"
     "uvm_seq_item_pull_export" "uvm_seq_item_pull_imp" "uvm_seq_item_pull_port" "uvm_sequence" "uvm_sequence_base" "uvm_sequence_item"
     "uvm_sequence_library" "uvm_sequence_library_cfg" "uvm_sequence_request" "uvm_sequencer" "uvm_sequencer_analysis_fifo" "uvm_sequencer_base"
     "uvm_sequencer_param_base" "uvm_shutdown_phase" "uvm_simple_sequence" "uvm_slave_export" "uvm_slave_imp" "uvm_slave_port"
     "uvm_spell_chkr" "uvm_sqr_if_base" "uvm_start_of_simulation_phase" "uvm_status_container" "uvm_string_rsrc" "uvm_subscriber"
     "uvm_table_printer" "uvm_task_phase" "uvm_test" "uvm_test_done_objection" "uvm_tlm_analysis_fifo" "uvm_tlm_b_initiator_socket"
     "uvm_tlm_b_initiator_socket_base" "uvm_tlm_b_passthrough_initiator_socket" "uvm_tlm_b_passthrough_initiator_socket_base" "uvm_tlm_b_passthrough_target_socket"
     "uvm_tlm_b_passthrough_target_socket_base" "uvm_tlm_b_target_socket" "uvm_tlm_b_target_socket_base" "uvm_tlm_b_transport_export" "uvm_tlm_b_transport_imp"
     "uvm_tlm_b_transport_port" "uvm_tlm_event" "uvm_tlm_extension" "uvm_tlm_extension_base" "uvm_tlm_fifo" "uvm_tlm_fifo_base" "uvm_tlm_generic_payload"
     "uvm_tlm_if" "uvm_tlm_if_base" "uvm_tlm_nb_initiator_socket" "uvm_tlm_nb_initiator_socket_base" "uvm_tlm_nb_passthrough_initiator_socket" "uvm_tlm_nb_passthrough_initiator_socket_base"
     "uvm_tlm_nb_passthrough_target_socket" "uvm_tlm_nb_passthrough_target_socket_base" "uvm_tlm_nb_target_socket" "uvm_tlm_nb_target_socket_base" "uvm_tlm_nb_transport_bw_export"
     "uvm_tlm_nb_transport_bw_imp" "uvm_tlm_nb_transport_bw_port" "uvm_tlm_nb_transport_fw_export"
     "uvm_tlm_nb_transport_fw_imp" "uvm_tlm_nb_transport_fw_port" "uvm_tlm_req_rsp_channel" "uvm_tlm_time" "uvm_tlm_transport_channel" "uvm_topdown_phase"
     "uvm_transaction" "uvm_transport_export" "uvm_transport_imp" "uvm_transport_port" "uvm_tree_printer" "uvm_typed_callbacks"
     "uvm_typeid" "uvm_typeid_base" "uvm_utils" "uvm_void" "uvm_vreg" "uvm_vreg_cbs"
     "uvm_vreg_field" "uvm_vreg_field_cbs"
     )
   'symbols)) ; Used to emphasize UVM specific constructs


(defvar verilog-ext-font-lock-keywords
  (list
   ;; Preprocessor macros and compiler directives
   '("`\\s-*[A-Za-z][A-Za-z0-9_]*" 0 hdl-ext-font-lock-preprocessor-face) ; Place at the top to have precendence in `else or `include 'macros over keywords
   ;; Special macros
   (cons (concat "\\<\\(" verilog-ext-special-macros "\\)\\>") 'hdl-ext-xilinx-attributes-face)
   ;; Special constructs
   (cons (concat "\\(" verilog-ext-special-constructs "\\)") 'hdl-ext-xilinx-attributes-face)
   ;; UVM relevant constructs
   (cons (concat "\\(" verilog-ext-uvm-classes "\\)") 'verilog-ext-uvm-classes-face)
   ;; Builtin keywords
   (concat "\\<\\(" verilog-ext-font-general-keywords "\\)\\>") ; Default 'font-lock-keyword-face
   ;; User/System tasks and functions
   (cons (concat "\\<\\(" verilog-ext-system-task-re "\\)\\>") 'font-lock-builtin-face)
   ;; Grouping keywords
   (cons (concat "\\<\\(" verilog-ext-font-grouping-keywords "\\)\\>") 'hdl-ext-font-lock-grouping-keywords-face)
   ;; Types
   (cons (concat "\\<\\(" verilog-ext-type-font-keywords "\\)\\>") 'font-lock-type-face)
   ))

(defvar verilog-ext-font-lock-keywords-1
  (append verilog-ext-font-lock-keywords
          (list
           ;; Module definitions
           (list "\\<\\(?1:\\(macro\\|connect\\)?module\\|primitive\\|class\\|program\\|interface\\|package\\|task\\)\\>\\s-*\\(automatic\\s-+\\)?\\(?3:\\sw+\\)\\s-*\\(?4:#?\\)"
                 '(1 font-lock-keyword-face)
                 '(3 font-lock-function-name-face))
           ;; Function definitions
           (list "\\<function\\>\\s-+\\(?1:\\automatic\\s-+\\)?\\(?2:\\(?3:\\sw+\\)\\s-+\\)?\\(?4:\\sw+\\)"
                 '(4 font-lock-function-name-face)) ; Match 3 is return type (might be void)
           )))

(defvar verilog-ext-font-lock-keywords-2
  (append verilog-ext-font-lock-keywords-1
          (list
           ;; Pragmas
           (list (concat "\\(//\\s-*\\(" verilog-ext-pragma-keywords " \\).*\\)")
                 '(0 'verilog-ext-font-lock-translate-off-face prepend)
                 '(2 'verilog-ext-font-lock-preprocessor-face prepend))
           ;; Escaped names
           '("\\(\\\\\\S-*\\s-\\)"  0 font-lock-function-name-face)
           ;; Delays/numbers
           '("\\s-*#\\s-*\\(?1:\\([0-9_.]+\\([munpf]s\\)?\\('s?[hdxbo][0-9a-fA-F_xz]*\\)?\\)\\|\\(([^(),.=]+)\\|\\sw+\\)\\)" 1 font-lock-type-face append)
           ;; Fontify property/sequence cycle delays - these start with '##'
           '("##\\(?1:\\sw+\\|\\[[^]]+\\]\\)" 1 font-lock-type-face append)
           )))

(defvar verilog-ext-font-lock-keywords-3
  (append verilog-ext-font-lock-keywords-2
          (list
           (list verilog-ext-time-unit-re          2 hdl-ext-font-lock-time-unit-face)
           (list verilog-ext-time-event-re         0 hdl-ext-font-lock-time-event-face)
           (list verilog-ext-port-connection-re    1 hdl-ext-font-lock-port-connection-face)
           (list verilog-ext-dot-itf-struct-re     1 hdl-ext-font-lock-dot-expression-face)
           (list verilog-ext-braces-content-re     1 hdl-ext-font-lock-braces-content-face)
           (list hdl-ext-punctuation-re                0 hdl-ext-font-lock-punctuation-face)
           (list hdl-ext-punctuation-bold-re           0 hdl-ext-font-lock-punctuation-bold-face)
           (list hdl-ext-braces-re                     0 hdl-ext-font-lock-braces-face)
           (list hdl-ext-brackets-re                   0 hdl-ext-font-lock-brackets-face)
           (list hdl-ext-curly-brackets-re             0 hdl-ext-font-lock-curly-brackets-face)
           (list verilog-ext-width-signal-re
                 '(1 hdl-ext-font-lock-width-num-face)
                 '(2 hdl-ext-font-lock-width-type-face))

           ;; Xilinx attributes
           (list (concat "(\\*\\s-+" "\\<\\(?1:" verilog-ext-xilinx-attributes "\\)\\>" "\\s-+\\*)") 1 hdl-ext-xilinx-attributes-face)

           ;; FUNCTION-Based search fontify
           ;; Modules/instances
           '(verilog-ext-find-verilog-module-instance-fontify
             (1 'hdl-ext-font-lock-module-face))
           '(verilog-ext-find-verilog-module-instance-fontify
             (2 'hdl-ext-font-lock-instance-face))

           ;; Variable types
           '(verilog-ext-find-verilog-variable-type-fontify-1
             (0 'verilog-ext-font-lock-variable-type-face))
           '(verilog-ext-find-verilog-variable-type-fontify-2
             (0 'verilog-ext-font-lock-variable-type-face))
           '(verilog-ext-find-verilog-variable-type-fontify-3
             (0 'verilog-ext-font-lock-variable-type-face))

           ;; *_translate off regions
           '(verilog-ext-match-translate-off-fontify
             (0 'verilog-ext-font-lock-translate-off-face prepend)) ; 3rd parameter (prepend or t) overrides previous fontlocking
           )

          ;; DANGER: Still experimental. Regexps are not solid enough.
          (when verilog-ext-highlight-variable-declaration-names
            (list
             ;; A good approach would be fixing the function search based fontification to detect better variable declarations.
             '(verilog-ext-find-verilog-variable-name-fontify-1
               (0 'verilog-ext-font-lock-variable-name-face))
             '(verilog-ext-find-verilog-variable-name-fontify-2
               (0 'verilog-ext-font-lock-variable-name-face))
             '(verilog-ext-find-verilog-variable-name-fontify-3
               (0 'verilog-ext-font-lock-variable-name-face))
             ))))



;;;; Config
(setq verilog-highlight-grouping-keywords     t)
(setq verilog-highlight-translate-off       nil)  ; Conflict with `verilog-ext-match-translate-off-fontify' if enabled
(setq verilog-highlight-modules             nil)  ; Analogous to `verilog-highlight-includes', would highlight module while hovering mouse. However it's experimental/incomplete as the regexp is not consistent.

(font-lock-add-keywords 'verilog-mode
                        (append verilog-ext-font-lock-keywords
                                verilog-ext-font-lock-keywords-1
                                verilog-ext-font-lock-keywords-2
                                verilog-ext-font-lock-keywords-3) 'set)




(provide 'verilog-font-lock)

;;; verilog-font-lock.el ends here
