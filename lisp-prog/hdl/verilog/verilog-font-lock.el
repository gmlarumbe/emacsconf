;;; verilog-font-lock.el --- Verilog Custom Font Lock  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'init-hdl-font-lock)
(require 'verilog-mode)
(require 'verilog-navigation)

;;;; Variables
;; Some regexps come from evaluated `(concat larumbe/verilog-identifier-re "\\s-+" larumbe/verilog-identifier-re)' with capture groups and additions depending on what they might detect.
(defvar larumbe/verilog-system-task-regex "\\$[a-zA-Z][a-zA-Z0-9_\\$]*")
(defvar larumbe/verilog-port-connection-regex "^[[:blank:]]*\\.\\([0-9a-zA-Z*_-]*\\)")
(defvar larumbe/verilog-dot-itf-struct-regex "\\([a-zA-Z*_-][0-9a-zA-Z*_-]+\\)\\.\\([0-9a-zA-Z*_-]+\\)")
(defvar larumbe/verilog-braces-content-regex "\\[\\(?1:[ +\*/()$0-9a-zA-Z:_-]*\\)\\]")
(defvar larumbe/verilog-width-signal-regex "\\(?1:[0-9]*\\)'\\(?2:[hdxbo]\\)\\(?3:[0-9a-fA-F_xz]+\\)")
(defvar larumbe/verilog-time-event-regex "\\([@#]\\)")
(defvar larumbe/verilog-time-unit-regex "[0-9]+\\(\\.[0-9]+\\)?\\(?2:[umnpf]s\\)")

;; Variable declaration type/name font-lock
(defvar larumbe/verilog-highlight-variable-declaration-names nil)
(defvar larumbe/verilog-keywords-no-types '("`__FILE__" "`__LINE" "`begin_keywords" "`celldefine" "`default_nettype" "`define" "`else" "`elsif" "`end_keywords" "`endcelldefine" "`endif" "`ifdef" "`ifndef" "`include"
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
(defvar larumbe/verilog-keywords-no-types-re (regexp-opt larumbe/verilog-keywords-no-types 'symbols))
(defvar larumbe/verilog-variable-re-1
  "\\_<\\(?1:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-+\\(?2:\\[.*\\]\\s-*\\)?\\_<\\(?3:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-*\\(\\[.*\\]\\)?\\s-*\\(?4:=.*\\)?;"
  "type_t asdf;
   type_t [10:0] asdf;
   type_t [10:0] asdf = 'h0;
")
(defvar larumbe/verilog-variable-re-2
  "\\_<\\(?1:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\_>\\s-+\\(?3:\\([a-zA-Z_][a-zA-Z0-9$_]*\\s-*,\\s-*\\)+\\([a-zA-Z_][a-zA-Z0-9$_]*\\s-*\\)\\);"
  "type_t asdf1, asdf2 , asdf4, asdf6[], asdf7 [25], asdf8 ;")
(defvar larumbe/verilog-variable-re-3
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


;;;; Functions
;; INFO: Search based fontification:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Search_002dbased-Fontification.html
;;     Look for 'function' section.
;; - Based on `verilog-match-translate-off'

(defun larumbe/find-verilog-module-instance-fontify (limit)
  "Search based fontification function of Verilog modules/instances.
Arg LIMIT is used internally for fontification."
  (let (start-line end-line)
    (when (larumbe/find-verilog-module-instance-fwd limit)
      (setq start-line (save-excursion
                         (goto-char (match-beginning 0))
                         (point-at-bol)))
      (setq end-line (save-excursion
                       (goto-char (match-end 0))
                       (point-at-eol)))
      (unless (get-text-property (point) 'font-lock-multiline)
        (put-text-property start-line end-line 'font-lock-multiline t))
      (point))))


(defun larumbe/verilog-match-translate-off-fontify (limit)
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


(defun larumbe/find-verilog-variable-type-fwd (regex limit)
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
        (unless (or (string-match larumbe/verilog-keywords-no-types-re type)
                    (string-match larumbe/verilog-keywords-no-types-re name))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))


(defun larumbe/find-verilog-variable-fwd-1 (limit)
  (larumbe/find-verilog-variable-type-fwd larumbe/verilog-variable-re-1 limit))

(defun larumbe/find-verilog-variable-fwd-2 (limit)
  (larumbe/find-verilog-variable-type-fwd larumbe/verilog-variable-re-2 limit))

(defun larumbe/find-verilog-variable-fwd-3 (limit)
  (larumbe/find-verilog-variable-type-fwd larumbe/verilog-variable-re-3 limit))


(defun larumbe/find-verilog-variable-type-fontify-1 (limit)
  "Search based fontification function of Verilog type 1 variable types.
These are determined by variable `larumbe/verilog-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-1 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-name-fontify-1 (limit)
  "Search based fontification function of Verilog type 1 variable names.
These are determined by variable `larumbe/verilog-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-1 limit)
      (setq start (match-beginning 3))
      (setq end (match-end 3))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-type-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable types.
These are determined by variable `larumbe/verilog-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-2 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-name-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable names.
These are determined by variable `larumbe/verilog-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-2 limit)
      (setq start (match-beginning 2))
      (setq end (match-end 2))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-type-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable types.
These are determined by variable `larumbe/verilog-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-3 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-name-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable names.
These are determined by variable `larumbe/verilog-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-3 limit)
      (setq start (match-beginning 3))
      (setq end (match-end 3))
      (set-match-data (list start end))
      (point))))



;;;; Font-lock keywords
(defvar larumbe/verilog-type-font-keywords
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

(defvar larumbe/verilog-pragma-keywords
  (regexp-opt
   '("surefire" "0in" "auto" "leda" "rtl_synthesis" "verilint"
     ;; Recognized by Vivado (check Xilinx attribute 'translate_off/translate_on'):
     "synthesis" "synopsys" "pragma") nil))


;; https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_3/ug901-vivado-synthesis.pdf
;; Chapter 2 (Some of them are also supported at XDC)
(defvar larumbe/verilog-xilinx-attributes
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


(defvar larumbe/verilog-font-general-keywords
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

(defvar larumbe/verilog-font-grouping-keywords
  (regexp-opt
   '( "begin" "end" "this") nil))  ; "this" is not grouping but looks better in green

(defvar larumbe/verilog-special-macros
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

(defvar larumbe/verilog-special-constructs
  (regexp-opt
   '(
     ;; These constructs contain some special character that prevent them to be detected as symbols
     "@include" "@replace_ifdef" "@replace_end" "@insert_ifdef"
     "@macro_begin" "@macro_end"
     "@if" "@else" "@endif"
     "@comment"
     "@define" "@define_begin" "@define_end"

     "%include" "%register"
     )
   nil)) ; Used for non-verilog constructs (i.e. custom preprocessing)


(defvar larumbe/verilog-font-lock-keywords
  (list
   ;; Preprocessor macros and compiler directives
   '("`\\s-*[A-Za-z][A-Za-z0-9_]*" 0 larumbe/font-lock-preprocessor-face) ; Place at the top to have precendence in `else or `include 'macros over keywords
   ;; Special macros
   (cons (concat "\\<\\(" larumbe/verilog-special-macros "\\)\\>") 'larumbe/xilinx-attributes-face)
   ;; Special constructs
   (cons (concat "\\(" larumbe/verilog-special-constructs "\\)") 'larumbe/xilinx-attributes-face)
   ;; Builtin keywords
   (concat "\\<\\(" larumbe/verilog-font-general-keywords "\\)\\>") ; Default 'font-lock-keyword-face
   ;; User/System tasks and functions
   (cons (concat "\\<\\(" larumbe/verilog-system-task-regex "\\)\\>") 'font-lock-builtin-face)
   ;; Grouping keywords
   (cons (concat "\\<\\(" larumbe/verilog-font-grouping-keywords "\\)\\>") 'larumbe/font-lock-grouping-keywords-face)
   ;; Types
   (cons (concat "\\<\\(" larumbe/verilog-type-font-keywords "\\)\\>") 'font-lock-type-face)
   ))

(defvar larumbe/verilog-font-lock-keywords-1
  (append larumbe/verilog-font-lock-keywords
          (list
           ;; Module definitions
           (list "\\<\\(?1:\\(macro\\|connect\\)?module\\|primitive\\|class\\|program\\|interface\\|package\\|task\\)\\>\\s-*\\(automatic\\s-+\\)?\\(?3:\\sw+\\)\\s-*\\(?4:#?\\)"
                 '(1 font-lock-keyword-face)
                 '(3 font-lock-function-name-face))
           ;; Function definitions
           (list "\\<function\\>\\s-+\\(?1:\\automatic\\s-+\\)?\\(?2:\\(?3:\\sw+\\)\\s-+\\)?\\(?4:\\sw+\\)"
                 '(4 font-lock-function-name-face)) ; Match 3 is return type (might be void)
           )))

(defvar larumbe/verilog-font-lock-keywords-2
  (append larumbe/verilog-font-lock-keywords-1
          (list
           ;; Pragmas
           (list (concat "\\(//\\s-*\\(" larumbe/verilog-pragma-keywords "\\).*\\)")
                 '(0 'larumbe/font-lock-translate-off-face prepend)
                 '(2 'larumbe/font-lock-preprocessor-face prepend))
           ;; Escaped names
           '("\\(\\\\\\S-*\\s-\\)"  0 font-lock-function-name-face)
           ;; Delays/numbers
           '("\\s-*#\\s-*\\(?1:\\([0-9_.]+\\([munpf]s\\)?\\('s?[hdxbo][0-9a-fA-F_xz]*\\)?\\)\\|\\(([^(),.=]+)\\|\\sw+\\)\\)" 1 font-lock-type-face append)
           ;; Fontify property/sequence cycle delays - these start with '##'
           '("##\\(?1:\\sw+\\|\\[[^]]+\\]\\)" 1 font-lock-type-face append)
           )))

(defvar larumbe/verilog-font-lock-keywords-3
  (append larumbe/verilog-font-lock-keywords-2
          (list
           (list larumbe/verilog-time-unit-regex          2 larumbe/font-lock-time-unit-face)
           (list larumbe/verilog-time-event-regex         0 larumbe/font-lock-time-event-face)
           (list larumbe/verilog-port-connection-regex    1 larumbe/font-lock-port-connection-face)
           (list larumbe/verilog-dot-itf-struct-regex     1 larumbe/font-lock-dot-expression-face)
           (list larumbe/verilog-braces-content-regex     1 larumbe/font-lock-braces-content-face)
           (list larumbe/punctuation-regex                0 larumbe/font-lock-punctuation-face)
           (list larumbe/punctuation-bold-regex           0 larumbe/font-lock-punctuation-bold-face)
           (list larumbe/braces-regex                     0 larumbe/font-lock-braces-face)
           (list larumbe/brackets-regex                   0 larumbe/font-lock-brackets-face)
           (list larumbe/curly-brackets-regex             0 larumbe/font-lock-curly-brackets-face)
           (list larumbe/verilog-width-signal-regex
                 '(1 larumbe/font-lock-width-num-face)
                 '(2 larumbe/font-lock-width-type-face))

           ;; Xilinx attributes
           (list (concat "(\\*\\s-+" "\\<\\(?1:" larumbe/verilog-xilinx-attributes "\\)\\>" "\\s-+\\*)") 1 larumbe/xilinx-attributes-face)

           ;; FUNCTION-Based search fontify
           ;; Modules/instances
           '(larumbe/find-verilog-module-instance-fontify
             (1 'larumbe/font-lock-module-face))
           '(larumbe/find-verilog-module-instance-fontify
             (2 'larumbe/font-lock-instance-face))

           ;; Variable types
           '(larumbe/find-verilog-variable-type-fontify-1
             (0 'larumbe/font-lock-variable-type-face))
           '(larumbe/find-verilog-variable-type-fontify-2
             (0 'larumbe/font-lock-variable-type-face))
           '(larumbe/find-verilog-variable-type-fontify-3
             (0 'larumbe/font-lock-variable-type-face))

           ;; *_translate off regions
           '(larumbe/verilog-match-translate-off-fontify
             (0 'larumbe/font-lock-translate-off-face prepend)) ; 3rd parameter (prepend or t) overrides previous fontlocking
           )

          ;; DANGER: Still experimental. Regexps are not solid enough.
          (when larumbe/verilog-highlight-variable-declaration-names
            (list
             ;; A good approach would be fixing the function search based fontification to detect better variable declarations.
             '(larumbe/find-verilog-variable-name-fontify-1
               (0 'larumbe/font-lock-variable-name-face))
             '(larumbe/find-verilog-variable-name-fontify-2
               (0 'larumbe/font-lock-variable-name-face))
             '(larumbe/find-verilog-variable-name-fontify-3
               (0 'larumbe/font-lock-variable-name-face))
             ))))



;;;; Config
(setq verilog-highlight-grouping-keywords     t)
(setq verilog-highlight-translate-off       nil)  ; Conflict with `larumbe/verilog-match-translate-off-fontify' if enabled
(setq verilog-highlight-modules             nil)  ; Analogous to `verilog-highlight-includes', would highlight module while hovering mouse. However it's experimental/incomplete as the regexp is not consistent.

(font-lock-add-keywords 'verilog-mode
                        (append larumbe/verilog-font-lock-keywords
                                larumbe/verilog-font-lock-keywords-1
                                larumbe/verilog-font-lock-keywords-2
                                larumbe/verilog-font-lock-keywords-3) 'set)




(provide 'verilog-font-lock)

;;; verilog-font-lock.el ends here
