;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Verilog/SystemVerilog setup ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Fontify
;; INFO: Needs to be set before loading verilog-mode with use-package, since these variables
;; are used by verilog-mode font-lock functions.

;; INFO: Multiline Font Locking is not reliable in Emacs.
;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Font-Lock-Multiline.html
;;  - Some thread said that using the `font-lock-multiline' might apply to a few lines (such is the case).
;;    For longer sections it is necessary to create font lock custom functions and gets more complicated.

;; INFO: Search based fontification:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Search_002dbased-Fontification.html
;;     Look for 'function' section.
;; - Based on `verilog-match-translate-off'

;;;; Variables
(defvar larumbe/verilog-system-task-regex "\\$[a-zA-Z][a-zA-Z0-9_\\$]*")
(defvar larumbe/port-connection-regex "[( ]\\.\\([0-9a-zA-Z*_-]*\\)")
(defvar larumbe/dotted-interface-struct-regex "\\([a-zA-Z*_-][0-9a-zA-Z*_-]+\\)\\.\\([0-9a-zA-Z*_-]+\\)")
(defvar larumbe/brackets-regex "[()]")
(defvar larumbe/curly-brackets-regex "[{}]")
(defvar larumbe/braces-regex "\\(\\[\\|\\]\\)")
(defvar larumbe/braces-content-regex "\\[\\(?1:[ +\*/()$0-9a-zA-Z:_-]*\\)\\]")
(defvar larumbe/width-signal-regex "\\(?1:[0-9]*\\)'\\(?2:[hdxbo]\\)\\(?3:[0-9a-fA-F_xz]+\\)")
(defvar larumbe/punctuation-regex "\\([!,;:?'=<>]\\|\\*\\)")
(defvar larumbe/punctuation-bold-regex "\\([&^~+-/]\\||\\|\\.\\)")
(defvar larumbe/time-event-regex "\\([@#]\\)")
(defvar larumbe/time-unit-regex "[0-9]+\\(\\.[0-9]+\\)?\\(?2:[umnpf]s\\)")

;; Regexps come from evaluated `(concat larumbe/verilog-identifier-re "\\s-+" larumbe/verilog-identifier-re)' with capture groups and additions depending on what they might detect.
(defvar larumbe/verilog-variable-type-re-1
  "\\_<\\(?1:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-+\\_<\\(?2:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-*\\(\\[.*\\]\\)?\\s-*;"
  "type_t asdf;")

(defvar larumbe/verilog-variable-type-re-2
  "\\_<\\(?1:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-+\\_<\\(?2:\\(\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\_>\\)\\s-*\\(\\[.*\\]\\)?[, ]\\s-*\\)+;"
  "type_t asdf1, asdf2 , asdf4, asdf6[], asdf7 [25], asdf8 ;")

(defvar larumbe/verilog-variable-type-re-3
  "\\_<\\(input\\|output\\|inout\\|ref\\|parameter\\|localparam\\)\\_>\\s-+\\_<\\(?1:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-+\\(\\[.*\\]\\)?\\s-*\\_<\\(?2:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\s-*\\(\\[.*\\]\\)?\\s-*"
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


;;;; Faces
(defvar larumbe/verilog-font-lock-punctuation-face 'larumbe/verilog-font-lock-punctuation-face " ")
(defface larumbe/verilog-font-lock-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols: !,;:?'=<>* "
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-punctuation-bold-face 'larumbe/verilog-font-lock-punctuation-bold-face " ")
(defface larumbe/verilog-font-lock-punctuation-bold-face
  '((t (:inherit larumbe/verilog-font-lock-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|. "
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-port-connection-face 'larumbe/verilog-font-port-connection-face " ")
(defface larumbe/verilog-font-port-connection-face
  '((t (:foreground "bisque2")))
  "Face for instances port connections
...
.portA (signalA),
.portB (signalB)
);
 "
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-dotted-interface-struct-regex 'larumbe/verilog-font-dotted-interface-struct-regex " ")
(defface larumbe/verilog-font-dotted-interface-struct-regex
  '((t (:foreground "gray70")))
  "Face for interfaces prefix (also applies to objects methods calling)
...
axi_if.Ready <= 1'b1;
obj.method();
"
  :group 'font-lock-highlighting-faces)

(defvar larumbe/verilog-font-lock-braces-content-face 'larumbe/verilog-font-lock-braces-content-face " ")
(defface larumbe/verilog-font-lock-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces: bit vector width and indexing "
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-braces-face 'larumbe/verilog-font-lock-braces-face " ")
(defface larumbe/verilog-font-lock-braces-face
  '((t (:foreground "goldenrod")))
  "Face for braces []"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-brackets-face 'larumbe/verilog-font-lock-brackets-face " ")
(defface larumbe/verilog-font-lock-brackets-face
  '((t (:foreground "dark goldenrod")))
  "Face for brackets ()"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-curly-brackets-face 'larumbe/verilog-font-lock-curly-brackets-face " ")
(defface larumbe/verilog-font-lock-curly-brackets-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly brackets {}"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-width-num-face 'larumbe/verilog-font-lock-width-num-face " ")
(defface larumbe/verilog-font-lock-width-num-face
  '((t (:foreground "chartreuse2")))
  "Face for the bit width number expressions:
{1}'b1,
{4}'hF,
{3}'o7,
"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-width-type-face 'larumbe/verilog-font-lock-width-type-face " ")
(defface larumbe/verilog-font-lock-width-type-face
  '((t (:foreground "sea green" :weight bold)))
  "Face for the bit width type expressions:
1'{b}1,
4'{h}F,
3'{o}7,
"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-module-face 'larumbe/verilog-font-lock-module-face " ")
(defface larumbe/verilog-font-lock-module-face
  '((t (:foreground "green1")))
  "Face for module names."
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-instance-face 'larumbe/verilog-font-lock-instance-face " ")
(defface larumbe/verilog-font-lock-instance-face
  '((t (:foreground "medium spring green")))
  "Face for instance names."
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-time-event-regex-face 'larumbe/verilog-font-lock-time-event-regex-face " ")
(defface larumbe/verilog-font-lock-time-event-regex-face
  '((t (:foreground "deep sky blue" :weight bold)))
  "Face for time-events: @ and #"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-time-unit-regex-face 'larumbe/verilog-font-lock-time-unit-regex-face " ")
(defface larumbe/verilog-font-lock-time-unit-regex-face
  '((t (:foreground "light steel blue")))
  "Face for time-units: ms, us, ns, ps, fs (used by delays and timescale/timeprecision)"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-preprocessor-face 'larumbe/verilog-font-lock-preprocessor-face " ")
(defface larumbe/verilog-font-lock-preprocessor-face
  '((t (:foreground "pale goldenrod")))
  "Face for preprocessor compiler directives (`include, `define...)"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-variable-type-face 'larumbe/verilog-font-lock-variable-type-face " ")
(defface larumbe/verilog-font-lock-variable-type-face
  '((t (:foreground "powder blue")))
  "Face for variables defined by `larumbe/verilog-variable-type-re-1', `larumbe/verilog-variable-type-re-2' and `larumbe/verilog-variable-type-re-3'"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-xilinx-attributes-face 'larumbe/verilog-xilinx-attributes-face " ")
(defface larumbe/verilog-xilinx-attributes-face
  '((t (:foreground "orange1")))
  "Face for Xilinx Vivado RTL synthesis attributes."
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-grouping-keywords-face 'larumbe/verilog-font-lock-grouping-keywords-face " ")
(defface larumbe/verilog-font-lock-grouping-keywords-face
  '((t (:foreground "dark olive green")))
  "Face for overriding grouping keywords (begin/end)"
  :group 'font-lock-highlighting-faces)


(defvar larumbe/verilog-font-lock-translate-off-face 'larumbe/verilog-font-lock-translate-off-face " ")
(defface larumbe/verilog-font-lock-translate-off-face
  '((t (:background "gray20" :slant italic)))
  "Face for pragmas between comments: * translate_off / * translate_on"
  :group 'font-lock-highlighting-faces)



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
  "Generic search based fontification function of Verilog variable types."
  (let ((found nil)
        (pos))
    (save-excursion
      (while (and (not found)
                  (re-search-forward regex limit t))
        (unless (or (string-match modi/verilog-keywords-re (match-string-no-properties 1))
                    (string-match modi/verilog-keywords-re (match-string-no-properties 2)))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))


(defun larumbe/find-verilog-variable-type-fwd-1 (limit)
  (larumbe/find-verilog-variable-type-fwd larumbe/verilog-variable-type-re-1 limit))

(defun larumbe/find-verilog-variable-type-fwd-2 (limit)
  (larumbe/find-verilog-variable-type-fwd larumbe/verilog-variable-type-re-2 limit))

(defun larumbe/find-verilog-variable-type-fwd-3 (limit)
  (larumbe/find-verilog-variable-type-fwd larumbe/verilog-variable-type-re-3 limit))


(defun larumbe/find-verilog-variable-type-fontify-1 (limit)
  "Search based fontification function of Verilog type 1 variable types (`larumbe/verilog-variable-type-re-1')"
  (let (start end)
    (when (larumbe/find-verilog-variable-type-fwd-1 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-type-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable types (`larumbe/verilog-variable-type-re-2')."
  (let (start end)
    (when (larumbe/find-verilog-variable-type-fwd-2 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun larumbe/find-verilog-variable-type-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable types (`larumbe/verilog-variable-type-re-3')."
  (let (start end)
    (when (larumbe/find-verilog-variable-type-fwd-3 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
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
         (cons (concat "\\<\\(" larumbe/verilog-font-grouping-keywords "\\)\\>") 'larumbe/verilog-font-lock-grouping-keywords-face)
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
                       '(0 'larumbe/verilog-font-lock-translate-off-face prepend)
                       '(2 'larumbe/verilog-font-lock-preprocessor-face prepend))
                 ;; Escaped names
                 '("\\(\\\\\\S-*\\s-\\)"  0 font-lock-function-name-face)
                 ;; Preprocessor macros and compiler directives
                 '("`\\s-*[A-Za-z][A-Za-z0-9_]*" 0 larumbe/verilog-font-lock-preprocessor-face)
                 ;; Delays/numbers
                 '("\\s-*#\\s-*\\(?1:\\([0-9_.]+\\([munpf]s\\)?\\('s?[hdxbo][0-9a-fA-F_xz]*\\)?\\)\\|\\(([^(),.=]+)\\|\\sw+\\)\\)" 1 font-lock-type-face append)
                 ;; Fontify property/sequence cycle delays - these start with '##'
                 '("##\\(?1:\\sw+\\|\\[[^]]+\\]\\)" 1 font-lock-type-face append)
                 )))

  (setq larumbe/verilog-font-lock-keywords-3
        (append larumbe/verilog-font-lock-keywords-2
                (list
                 (list larumbe/time-unit-regex               2 larumbe/verilog-font-lock-time-unit-regex-face)
                 (list larumbe/time-event-regex              0 larumbe/verilog-font-lock-time-event-regex-face)
                 (list larumbe/port-connection-regex         1 larumbe/verilog-font-port-connection-face)
                 (list larumbe/dotted-interface-struct-regex 1 larumbe/verilog-font-dotted-interface-struct-regex)
                 (list larumbe/braces-content-regex          1 larumbe/verilog-font-lock-braces-content-face)   ; Bit-range
                 (list larumbe/punctuation-regex             0 larumbe/verilog-font-lock-punctuation-face)      ; Overrides bracket range
                 (list larumbe/punctuation-bold-regex        0 larumbe/verilog-font-lock-punctuation-bold-face) ; Overrides bracket range
                 (list larumbe/braces-regex                  0 larumbe/verilog-font-lock-braces-face)
                 (list larumbe/brackets-regex                0 larumbe/verilog-font-lock-brackets-face)
                 (list larumbe/curly-brackets-regex          0 larumbe/verilog-font-lock-curly-brackets-face)
                 (list larumbe/width-signal-regex
                       '(1 larumbe/verilog-font-lock-width-num-face)
                       '(2 larumbe/verilog-font-lock-width-type-face))

                 ;; Xilinx attributes
                 (list (concat "(\\*\\s-+" "\\<\\(?1:" larumbe/verilog-xilinx-attributes "\\)\\>" "\\s-+\\*)") 1 larumbe/verilog-xilinx-attributes-face)

                 ;; FUNCTION-Based search fontify
                 ;; *_translate off regions
                 '(verilog-match-translate-off
                   (0 'verilog-font-lock-translate-off-face prepend)) ; 3rd parameter (prepend or t) overrides previous fontlocking

                 ;; Modules/instances
                 '(larumbe/find-verilog-module-fontify
                   (0 'larumbe/verilog-font-lock-module-face))
                 '(larumbe/find-verilog-instance-fontify
                   (0 'larumbe/verilog-font-lock-instance-face))

                 ;; Variables
                 '(larumbe/find-verilog-variable-type-fontify-1
                   (0 'larumbe/verilog-font-lock-variable-type-face))
                 '(larumbe/find-verilog-variable-type-fontify-2
                   (0 'larumbe/verilog-font-lock-variable-type-face))
                 '(larumbe/find-verilog-variable-type-fontify-3
                   (0 'larumbe/verilog-font-lock-variable-type-face))
                 )
                )))
