;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HDL Font-Locking (VHDL/SystemVerilog ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; INFO: Multiline Font Locking is not reliable in Emacs.
;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Font-Lock-Multiline.html
;;  - Some thread said that using the `font-lock-multiline' might apply to a few lines (such is the case).
;;    For longer sections it is necessary to create font lock custom functions and gets more complicated.

;; INFO: Search based fontification:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Search_002dbased-Fontification.html
;;     Look for 'function' section.
;; - Based on `verilog-match-translate-off'

;;; Faces
(defvar larumbe/font-lock-punctuation-face 'larumbe/font-lock-punctuation-face)
(defface larumbe/font-lock-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols: !,;:?'=<>* "
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-punctuation-bold-face 'larumbe/font-lock-punctuation-bold-face)
(defface larumbe/font-lock-punctuation-bold-face
  '((t (:inherit larumbe/font-lock-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|. "
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-port-connection-face 'larumbe/font-lock-port-connection-face)
(defface larumbe/font-lock-port-connection-face
  '((t (:foreground "bisque2")))
  "Face for instances port connections
...
.portA (signalA),
.portB (signalB)
);
 "
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-dot-expression-face 'larumbe/font-lock-dot-expression-face)
(defface larumbe/font-lock-dot-expression-face
  '((t (:foreground "gray70")))
  "Face for interfaces prefix (also applies to objects methods calling)
...
axi_if.Ready <= 1'b1;
obj.method();
"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-braces-content-face 'larumbe/font-lock-braces-content-face)
(defface larumbe/font-lock-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces: bit vector width and indexing "
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-braces-face 'larumbe/font-lock-braces-face)
(defface larumbe/font-lock-braces-face
  '((t (:foreground "goldenrod")))
  "Face for braces []"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-brackets-face 'larumbe/font-lock-brackets-face)
(defface larumbe/font-lock-brackets-face
  '((t (:foreground "dark goldenrod")))
  "Face for brackets ()"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-curly-brackets-face 'larumbe/font-lock-curly-brackets-face)
(defface larumbe/font-lock-curly-brackets-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly brackets {}"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-width-num-face 'larumbe/font-lock-width-num-face)
(defface larumbe/font-lock-width-num-face
  '((t (:foreground "chartreuse2")))
  "Face for the bit width number expressions:
{1}'b1,
{4}'hF,
{3}'o7,
"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-width-type-face 'larumbe/font-lock-width-type-face)
(defface larumbe/font-lock-width-type-face
  '((t (:foreground "sea green" :weight bold)))
  "Face for the bit width type expressions:
1'{b}1,
4'{h}F,
3'{o}7,
"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-module-face 'larumbe/font-lock-module-face)
(defface larumbe/font-lock-module-face
  '((t (:foreground "green1")))
  "Face for module names."
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-instance-face 'larumbe/font-lock-instance-face)
(defface larumbe/font-lock-instance-face
  '((t (:foreground "medium spring green")))
  "Face for instance names."
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-time-event-face 'larumbe/font-lock-time-event-face)
(defface larumbe/font-lock-time-event-face
  '((t (:foreground "deep sky blue" :weight bold)))
  "Face for time-events: @ and #"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-time-unit-face 'larumbe/font-lock-time-unit-face)
(defface larumbe/font-lock-time-unit-face
  '((t (:foreground "light steel blue")))
  "Face for time-units: ms, us, ns, ps, fs (used by delays and timescale/timeprecision)"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-preprocessor-face 'larumbe/font-lock-preprocessor-face)
(defface larumbe/font-lock-preprocessor-face
  '((t (:foreground "pale goldenrod")))
  "Face for preprocessor compiler directives (`include, `define...)"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-variable-type-face 'larumbe/font-lock-variable-type-face)
(defface larumbe/font-lock-variable-type-face
  '((t (:foreground "powder blue")))
  "Face for variables types (i.e. Verilog typedef types, defined `larumbe/verilog-variable-re-1', `larumbe/verilog-variable-re-2' and `larumbe/verilog-variable-re-3'"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-variable-name-face 'larumbe/font-lock-variable-name-face)
(defface larumbe/font-lock-variable-name-face
  '((t (:foreground "DarkSeaGreen1")))
  "Face for variables names (i.e. Verilog typedef names, defined `larumbe/verilog-variable-re-1', `larumbe/verilog-variable-re-2' and `larumbe/verilog-variable-re-3'"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/xilinx-attributes-face 'larumbe/xilinx-attributes-face)
(defface larumbe/xilinx-attributes-face
  '((t (:foreground "orange1")))
  "Face for Xilinx Vivado RTL synthesis attributes."
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-grouping-keywords-face 'larumbe/font-lock-grouping-keywords-face)
(defface larumbe/font-lock-grouping-keywords-face
  '((t (:foreground "dark olive green")))
  "Face for overriding grouping keywords (begin/end)"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/font-lock-translate-off-face 'larumbe/font-lock-translate-off-face)
(defface larumbe/font-lock-translate-off-face
  '((t (:background "gray20" :slant italic)))
  "Face for pragmas between comments: * translate_off / * translate_on"
  :group 'font-lock-highlighting-faces)


;;; Common
(defvar larumbe/brackets-regex "[()]")
(defvar larumbe/curly-brackets-regex "[{}]")
(defvar larumbe/braces-regex "\\(\\[\\|\\]\\)")
(defvar larumbe/punctuation-regex "\\([!,;:?'=<>]\\|\\*\\)")
(defvar larumbe/punctuation-bold-regex "\\([&^~+-/]\\||\\|\\.\\)")


;;; SystemVerilog
;;;; Variables
;; Some regexps come from evaluated `(concat larumbe/verilog-identifier-re "\\s-+" larumbe/verilog-identifier-re)' with capture groups and additions depending on what they might detect.
(defvar larumbe/verilog-system-task-regex "\\$[a-zA-Z][a-zA-Z0-9_\\$]*")
(defvar larumbe/verilog-port-connection-regex "[( ]\\.\\([0-9a-zA-Z*_-]*\\)")
(defvar larumbe/verilog-dot-itf-struct-regex "\\([a-zA-Z*_-][0-9a-zA-Z*_-]+\\)\\.\\([0-9a-zA-Z*_-]+\\)")
(defvar larumbe/verilog-braces-content-regex "\\[\\(?1:[ +\*/()$0-9a-zA-Z:_-]*\\)\\]")
(defvar larumbe/verilog-width-signal-regex "\\(?1:[0-9]*\\)'\\(?2:[hdxbo]\\)\\(?3:[0-9a-fA-F_xz]+\\)")
(defvar larumbe/verilog-time-event-regex "\\([@#]\\)")
(defvar larumbe/verilog-time-unit-regex "[0-9]+\\(\\.[0-9]+\\)?\\(?2:[umnpf]s\\)")

;; Variable declaration type/name font-lock
(defvar larumbe/verilog-highlight-variable-declaration-names nil)
(defvar larumbe/verilog-keywords-no-types (cl-set-difference verilog-keywords verilog-type-keywords :test #'equal))
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
(defun larumbe/find-verilog-module-fontify (limit)
  "Search based fontification function of Verilog modules."
  (let (start end)
    (when (larumbe/find-verilog-module-instance-fwd limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))


(defun larumbe/find-verilog-instance-fontify (limit)
  "Search based fontification function of Verilog instances."
  (let (start end)
    (when (larumbe/find-verilog-module-instance-fwd limit)
      (setq start (match-beginning 2))
      (setq end (match-end 2))
      (set-match-data (list start end))
      (point))))


(defun larumbe/find-verilog-variable-type-fwd (regex limit)
  "Generic search based fontification function of Verilog variable types.
INFO: It is not necessary to check that variable is not within string/comment since
these both have precedence over custom fontify."
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
  "Search based fontification function of Verilog type 1 variable types (`larumbe/verilog-variable-re-1')"
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-1 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-name-fontify-1 (limit)
  "Search based fontification function of Verilog type 1 variable names (`larumbe/verilog-variable-re-1')"
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-1 limit)
      (setq start (match-beginning 3))
      (setq end (match-end 3))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-type-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable types (`larumbe/verilog-variable-re-2')."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-2 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-name-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable names (`larumbe/verilog-variable-re-2')."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-2 limit)
      (setq start (match-beginning 2))
      (setq end (match-end 2))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-type-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable types (`larumbe/verilog-variable-re-3')."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-3 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-name-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable names (`larumbe/verilog-variable-re-3')."
  (let (start end)
    (when (larumbe/find-verilog-variable-fwd-3 limit)
      (setq start (match-beginning 3))
      (setq end (match-end 3))
      (set-match-data (list start end))
      (point))))



;;;; Font-lock keywords
(let* ((larumbe/verilog-type-font-keywords
        (eval-when-compile
          (regexp-opt
           '("and" "buf" "bufif0" "bufif1" "cmos" "defparam" "event"
             "genvar" "highz0" "highz1" "inout" "input" "integer"
             "localparam" "mailbox" "nand" "nmos" "nor" "not" "notif0"
             "notif1" "or" "output" "parameter" "pmos" "pull0" "pull1"
             "pulldown" "pullup" "rcmos" "real" "realtime" "reg" "rnmos"
             "specparam" "strong0" "strong1" "supply" "supply0" "supply1"
             "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1" "triand"
             "trior" "trireg" "unsigned" "uwire" "vectored" "wand" "weak0"
             "weak1" "wire" "wor" "xnor" "xor"
             ;; 1800-2005
             "bit" "byte" "chandle" "const" "enum" "int" "logic" "longint"
             "packed" "ref" "shortint" "shortreal" "static" "string"
             "struct" "type" "typedef" "union" "var"
             ;; 1800-2009
             ;; 1800-2012
             "interconnect" "nettype" ) nil)))

       (larumbe/verilog-pragma-keywords
        (eval-when-compile
          (regexp-opt
           '("surefire" "0in" "auto" "leda" "rtl_synthesis" "verilint"
             ;; Recognized by Vivado (check Xilinx attribute 'translate_off/translate_on'):
             "synthesis" "synopsys" "pragma") nil)))


       ;; https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_3/ug901-vivado-synthesis.pdf
       ;; Chapter 2 (Some of them are also supported at XDC)
       (larumbe/verilog-xilinx-attributes
        (eval-when-compile
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
             ) nil)))


       (larumbe/verilog-font-general-keywords
        (eval-when-compile
          (regexp-opt
           ;; INFO: Same as the one in `verilog-mode' but excluding include
           ;; as it must be highlighted as a macro instead
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
             "tagged" "this" "throughout" "timeprecision" "timeunit"
             "unique" "virtual" "void" "wait_order" "wildcard" "with"
             "within"
             ;; 1800-2009
             "accept_on" "checker" "endchecker" "eventually" "global"
             "implies" "let" "nexttime" "reject_on" "restrict" "s_always"
             "s_eventually" "s_nexttime" "s_until" "s_until_with" "strong"
             "sync_accept_on" "sync_reject_on" "unique0" "until"
             "until_with" "untyped" "weak"
             ;; 1800-2012
             "implements" "soft" ) nil)))

       (larumbe/verilog-font-grouping-keywords
        (eval-when-compile
          (regexp-opt
           '( "begin" "end" ) nil))))



  (setq larumbe/verilog-font-lock-keywords
        (list
         ;; Builtin keywords
         (concat "\\<\\(" larumbe/verilog-font-general-keywords "\\)\\>") ; Default 'font-lock-keyword-face
         ;; User/System tasks and functions
         (cons (concat "\\<\\(" larumbe/verilog-system-task-regex "\\)\\>") 'font-lock-builtin-face)
         ;; Grouping keywords
         (cons (concat "\\<\\(" larumbe/verilog-font-grouping-keywords "\\)\\>") 'larumbe/font-lock-grouping-keywords-face)
         ;; Types
         (cons (concat "\\<\\(" larumbe/verilog-type-font-keywords "\\)\\>") 'font-lock-type-face)
         ))

  (setq larumbe/verilog-font-lock-keywords-1
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

  (setq larumbe/verilog-font-lock-keywords-2
        (append larumbe/verilog-font-lock-keywords-1
                (list
                 ;; Pragmas
                 (list (concat "\\(//\\s-*\\(" larumbe/verilog-pragma-keywords "\\).*\\)")
                       '(0 'larumbe/font-lock-translate-off-face prepend)
                       '(2 'larumbe/font-lock-preprocessor-face prepend))
                 ;; Escaped names
                 '("\\(\\\\\\S-*\\s-\\)"  0 font-lock-function-name-face)
                 ;; Preprocessor macros and compiler directives
                 '("`\\s-*[A-Za-z][A-Za-z0-9_]*" 0 larumbe/font-lock-preprocessor-face)
                 ;; Delays/numbers
                 '("\\s-*#\\s-*\\(?1:\\([0-9_.]+\\([munpf]s\\)?\\('s?[hdxbo][0-9a-fA-F_xz]*\\)?\\)\\|\\(([^(),.=]+)\\|\\sw+\\)\\)" 1 font-lock-type-face append)
                 ;; Fontify property/sequence cycle delays - these start with '##'
                 '("##\\(?1:\\sw+\\|\\[[^]]+\\]\\)" 1 font-lock-type-face append)
                 )))

  (setq larumbe/verilog-font-lock-keywords-3
        (append larumbe/verilog-font-lock-keywords-2
                (list
                 (list larumbe/verilog-time-unit-regex       2 larumbe/font-lock-time-unit-face)
                 (list larumbe/verilog-time-event-regex      0 larumbe/font-lock-time-event-face)
                 (list larumbe/verilog-port-connection-regex 1 larumbe/font-lock-port-connection-face)
                 (list larumbe/verilog-dot-itf-struct-regex  1 larumbe/font-lock-dot-expression-face)
                 (list larumbe/verilog-braces-content-regex  1 larumbe/font-lock-braces-content-face)   ; Bit-range
                 (list larumbe/punctuation-regex             0 larumbe/font-lock-punctuation-face)      ; Overrides bracket range
                 (list larumbe/punctuation-bold-regex        0 larumbe/font-lock-punctuation-bold-face) ; Overrides bracket range
                 (list larumbe/braces-regex                  0 larumbe/font-lock-braces-face)
                 (list larumbe/brackets-regex                0 larumbe/font-lock-brackets-face)
                 (list larumbe/curly-brackets-regex          0 larumbe/font-lock-curly-brackets-face)
                 (list larumbe/verilog-width-signal-regex
                       '(1 larumbe/font-lock-width-num-face)
                       '(2 larumbe/font-lock-width-type-face))

                 ;; Xilinx attributes
                 (list (concat "(\\*\\s-+" "\\<\\(?1:" larumbe/verilog-xilinx-attributes "\\)\\>" "\\s-+\\*)") 1 larumbe/xilinx-attributes-face)

                 ;; FUNCTION-Based search fontify
                 ;; *_translate off regions
                 '(verilog-match-translate-off
                   (0 'larumbe/font-lock-translate-off-face prepend)) ; 3rd parameter (prepend or t) overrides previous fontlocking

                 ;; Modules/instances
                 '(larumbe/find-verilog-module-fontify
                   (0 'larumbe/font-lock-module-face prepend))
                 '(larumbe/find-verilog-instance-fontify
                   (0 'larumbe/font-lock-instance-face prepend))

                 ;; Variable types
                 '(larumbe/find-verilog-variable-type-fontify-1
                   (0 'larumbe/font-lock-variable-type-face))
                 '(larumbe/find-verilog-variable-type-fontify-2
                   (0 'larumbe/font-lock-variable-type-face))
                 '(larumbe/find-verilog-variable-type-fontify-3
                   (0 'larumbe/font-lock-variable-type-face))
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
                   )))))


;;; VHDL
;; INFO: Strong customization is done on vhdl-keywords-2, as the rest depend on parameters and Emacs groups customizing
;;;; Variables
(defvar larumbe/vhdl-brackets-content-range-regex "\\(?1:(\\)\\(?2:[ )+*/$0-9a-zA-Z:_-]*\\)\\s-+\\(?3:\\(down\\)?to\\)\\s-+\\(?4:[ (+*/$0-9a-zA-Z:_-]*\\)\\(?5:)\\)")
(defvar larumbe/vhdl-brackets-content-index-regex "\\(?1:(\\)\\s-*\\(?2:[0-9]+\\)\\s-*\\(?3:)\\)")

(defvar larumbe/vhdl-directive-keywords-regex (regexp-opt '("psl" "pragma" "synopsys" "synthesis") 'symbols))

;;;; Functions
(defun larumbe/vhdl-font-lock-init ()
  "Initialize fontification.
INFO: Executed once while loading `vhdl-mode'."
  ;; Enable muli-line font-locking
  (setq font-lock-multiline t)

  ;; highlight template prompts and directives
  (setq vhdl-font-lock-keywords-0
        (list
         (list (concat "\\(^\\|[ \t(.']\\)\\(<" vhdl-template-prompt-syntax ">\\)")
               2 'vhdl-font-lock-prompt-face t)
         (list (concat "--\\s-*" larumbe/vhdl-directive-keywords-regex "\\s-+\\(.*\\)$")
               '(0 'larumbe/font-lock-translate-off-face prepend)
               '(1 'larumbe/font-lock-preprocessor-face prepend))
         ;; highlight c-preprocessor directives
         (list "^#[ \t]*\\(\\w+\\)\\([ \t]+\\(\\w+\\)\\)?"
               '(1 font-lock-builtin-face)
               '(3 font-lock-variable-name-face nil t))))

  ;; highlight keywords and standardized types, attributes, enumeration, values, and subprograms
  (setq vhdl-font-lock-keywords-1
        (list
         (list (concat "'" vhdl-attributes-regexp)
               1 'vhdl-font-lock-attribute-face)
         (list vhdl-types-regexp       1 'font-lock-type-face)
         (list vhdl-functions-regexp   1 'font-lock-builtin-face)
         (list vhdl-packages-regexp    1 'font-lock-builtin-face)
         (list vhdl-enum-values-regexp 1 'vhdl-font-lock-enumvalue-face)
         (list vhdl-constants-regexp   1 'font-lock-constant-face)
         (list vhdl-keywords-regexp    1 'font-lock-keyword-face)))

  ;; Strong customization
  (setq larumbe/vhdl-font-lock-keywords-2
        (append
         (list
          ;; highlight names of units, subprograms, and components when declared
          (list
           (concat
            "^\\s-*\\("
            "architecture\\|configuration\\|context\\|entity\\|package"
            "\\(\\s-+body\\)?\\|"
            "\\(\\(impure\\|pure\\)\\s-+\\)?function\\|procedure\\|component"
            "\\)\\s-+\\(\\w+\\)")
           5 'font-lock-function-name-face)

          ;; highlight entity names of architectures and configurations
          (list
           "^\\s-*\\(architecture\\|configuration\\)\\s-+\\w+\\s-+of\\s-+\\(\\w+\\)"
           2 'font-lock-function-name-face)

          ;; highlight labels of common constructs
          (list
           (concat
            "^\\s-*\\(\\w+\\)\\s-*:[ \t\n\r\f]*\\(\\("
            "assert\\|block\\|case\\|exit\\|for\\|if\\|loop\\|next\\|null\\|"
            "postponed\\|process\\|"
            "with\\|while"
            "\\)\\>\\|\\w+\\s-*\\(([^\n]*)\\|\\.\\w+\\)*\\s-*<=\\)")
           1 'font-lock-function-name-face)

          ;; highlight label and component name of every instantiation (configuration, component and entity)
          (list
           larumbe/vhdl-instance-re
           '(1 larumbe/font-lock-instance-face prepend)
           '(5 larumbe/font-lock-dot-expression-face nil t) ; 3rd argument nil avoids font-locking in case there is no match (no entity instantiation)
           '(6 larumbe/font-lock-module-face prepend))

          ;; highlight names and labels at end of constructs
          (list
           (concat
            "^\\s-*end\\s-+\\(\\("
            "architecture\\|block\\|case\\|component\\|configuration\\|context\\|"
            "entity\\|for\\|function\\|generate\\|if\\|loop\\|package"
            "\\(\\s-+body\\)?\\|procedure\\|\\(postponed\\s-+\\)?process\\|"
            "units"
            "\\)\\s-+\\)?\\(\\w*\\)")
           5 'font-lock-function-name-face)

          ;; highlight labels in exit and next statements
          (list
           (concat
            "^\\s-*\\(\\w+\\s-*:\\s-*\\)?\\(exit\\|next\\)\\s-+\\(\\w*\\)")
           3 'font-lock-function-name-face)

          ;; highlight entity name in attribute specifications
          (list
           (concat
            "^\\s-*attribute\\s-+\\w+\\s-+of\\s-+\\(\\w+\\(,\\s-*\\w+\\)*\\)\\s-*:")
           1 'font-lock-function-name-face)

          ;; highlight labels in block and component specifications
          (list
           (concat
            "^\\s-*for\\s-+\\(\\w+\\(,\\s-*\\w+\\)*\\)\\>\\s-*"
            "\\(:[ \t\n\r\f]*\\(\\w+\\)\\|[^i \t]\\)")
           '(1 font-lock-function-name-face) '(4 font-lock-function-name-face nil t))

          ;; highlight names in library clauses
          (list "^\\s-*library\\>"
                '(vhdl-font-lock-match-item nil nil (1 font-lock-function-name-face)))

          ;; highlight names in use clauses
          (list
           (concat
            "\\<\\(context\\|use\\)\\s-+\\(\\(entity\\|configuration\\)\\s-+\\)?"
            "\\(\\w+\\)\\(\\.\\(\\w+\\)\\)?\\((\\(\\w+\\))\\)?")
           '(4 font-lock-function-name-face) '(6 font-lock-function-name-face nil t)
           '(8 font-lock-function-name-face nil t))

          ;; highlight attribute name in attribute declarations/specifications
          (list
           (concat
            "^\\s-*attribute\\s-+\\(\\w+\\)")
           1 'vhdl-font-lock-attribute-face)

          ;; highlight type/nature name in (sub)type/(sub)nature declarations
          (list
           (concat
            "^\\s-*\\(\\(sub\\)?\\(nature\\|type\\)\\|end\\s-+\\(record\\|protected\\)\\)\\s-+\\(\\w+\\)")
           5 'font-lock-type-face)

          ;; highlight formal parameters in component instantiations and subprogram
          ;; calls
          (list "\\(=>\\)"
                '(vhdl-font-lock-match-item
                  (progn (goto-char (match-beginning 1))
                         (skip-syntax-backward " ")
                         (while (= (preceding-char) ?\)) (backward-sexp))
                         (skip-syntax-backward "w_")
                         (skip-syntax-backward " ")
                         (when (memq (preceding-char) '(?n ?N ?|))
                           (goto-char (point-max))))
                  (goto-char (match-end 1)) (1 larumbe/font-lock-port-connection-face)))

          ;; highlight alias/group/quantity declaration names and for-loop/-generate
          ;; variables
          (list "\\<\\(alias\\|for\\|group\\|quantity\\)\\s-+\\w+\\s-+\\(across\\|in\\|is\\)\\>"
                '(vhdl-font-lock-match-item
                  (progn (goto-char (match-end 1)) (match-beginning 2))
                  nil (1 font-lock-variable-name-face)))

          ;; highlight tool directives
          (list
           (concat
            "^\\s-*\\(`\\w+\\)")
           1 'font-lock-preprocessor-face)


          ;; Own Verilog-based customization
          (list larumbe/punctuation-regex             0 larumbe/font-lock-punctuation-face)
          (list larumbe/punctuation-bold-regex        0 larumbe/font-lock-punctuation-bold-face)
          (list larumbe/vhdl-brackets-content-range-regex ; Bit range
                '(1 larumbe/font-lock-curly-brackets-face prepend)
                '(5 larumbe/font-lock-curly-brackets-face prepend)
                '(2 larumbe/font-lock-braces-content-face prepend)
                '(4 larumbe/font-lock-braces-content-face prepend)
                '(3 larumbe/font-lock-dot-expression-face prepend))
          (list larumbe/vhdl-brackets-content-index-regex ; Bit index
                '(1 larumbe/font-lock-curly-brackets-face prepend)
                '(3 larumbe/font-lock-curly-brackets-face prepend)
                '(2 larumbe/font-lock-braces-content-face prepend))
          (list larumbe/braces-regex                  0 larumbe/font-lock-braces-face)
          (list larumbe/brackets-regex                0 larumbe/font-lock-brackets-face)
          (list larumbe/curly-brackets-regex          0 larumbe/font-lock-curly-brackets-face)
          )

         ;; highlight signal/variable/constant declaration names
         (when larumbe/vhdl-highlight-variable-declaration-names
           (list "\\(:[^=]\\)"
                 '(vhdl-font-lock-match-item
                   (progn (goto-char (match-beginning 1))
                          (skip-syntax-backward " ")
                          (skip-syntax-backward "w_")
                          (skip-syntax-backward " ")
                          (while (= (preceding-char) ?,)
                            (backward-char 1)
                            (skip-syntax-backward " ")
                            (skip-syntax-backward "w_")
                            (skip-syntax-backward " ")))
                   (goto-char (match-end 1)) (1 larumbe/font-lock-variable-name-face))))
         )
        ;;   "For consideration as a value of `vhdl-font-lock-keywords'.
        ;; This does context sensitive highlighting of names and labels."
        )


  ;; highlight words with special syntax.
  (setq vhdl-font-lock-keywords-3
        (let ((syntax-alist vhdl-special-syntax-alist) ; "generic/constant" "type" "variable"
              keywords)
          (while syntax-alist
            (setq keywords
                  (cons
                   (list (concat "\\(" (nth 1 (car syntax-alist)) "\\)") 1
                         (vhdl-function-name
                          "vhdl-font-lock" (nth 0 (car syntax-alist)) "face")
                         (nth 4 (car syntax-alist)))
                   keywords))
            (setq syntax-alist (cdr syntax-alist)))
          keywords))

  ;; highlight additional reserved words
  (setq vhdl-font-lock-keywords-4
        (list (list vhdl-reserved-words-regexp 1
                    'vhdl-font-lock-reserved-words-face)))

  ;; highlight translate_off regions
  (setq larumbe/vhdl-font-lock-keywords-5
        '((larumbe/vhdl-match-translate-off
           (0 larumbe/font-lock-translate-off-face prepend))))

  ;; highlight everything together
  (setq vhdl-font-lock-keywords
        (append
         vhdl-font-lock-keywords-0
         vhdl-font-lock-keywords-1
         vhdl-font-lock-keywords-4 ; Empty by default
         vhdl-font-lock-keywords-3
         larumbe/vhdl-font-lock-keywords-2
         larumbe/vhdl-font-lock-keywords-5
         )))


(defun larumbe/vhdl-within-translate-off ()
  "Same as analogous `vhdl-mode' function but taking `larumbe/vhdl-directive-keywords-regex' words
into account instead of only 'pragma'"
  (and (save-excursion
         (re-search-backward
          (concat
           "^\\s-*--\\s-*" larumbe/vhdl-directive-keywords-regex "\\s-*translate_\\(on\\|off\\)\\s-*\n") nil t))
       (equal "off" (match-string 1))
       (point)))

(defun larumbe/vhdl-start-translate-off (limit)
  "Same as analogous `vhdl-mode' function but taking `larumbe/vhdl-directive-keywords-regex' words
into account instead of only 'pragma'"
  (when (re-search-forward
         (concat
          "^\\s-*--\\s-*" larumbe/vhdl-directive-keywords-regex "\\s-*translate_off\\s-*\n") limit t)
    (match-beginning 0)))

(defun larumbe/vhdl-end-translate-off (limit)
  "Same as analogous `vhdl-mode' function but taking `larumbe/vhdl-directive-keywords-regex' words
into account instead of only 'pragma'"
  (re-search-forward
   (concat "^\\s-*--\\s-*" larumbe/vhdl-directive-keywords-regex "\\s-*translate_on\\s-*\n") limit t))

(defun larumbe/vhdl-match-translate-off (limit)
  "Same as analogous `vhdl-mode' function but taking `larumbe/vhdl-directive-keywords-regex' words
into account instead of only 'pragma'"
  (when (< (point) limit)
    (let ((start (or (larumbe/vhdl-within-translate-off)
                     (larumbe/vhdl-start-translate-off limit)))
          (case-fold-search t))
      (when start
        (let ((end (or (larumbe/vhdl-end-translate-off limit) limit)))
          (set-match-data (list start end))
          (goto-char end))))))

