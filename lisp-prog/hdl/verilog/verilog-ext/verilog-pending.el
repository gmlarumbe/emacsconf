;;; Priority


;;; Opened Buffers status
;;;; Hooks


(defun verilog-ext-save-buffer-hook ()
  "Verilog hook to run when saving a buffer."
  ;; (verilog-ext-typedef-var-decl-update)
  )

(add-hook 'after-save-hook #'verilog-ext-save-buffer-hook nil :local)




;;; Editing
(defvar verilog-ext-end-keywords-complete-re
  (rx-verilog
   (rx bol
       (group-n 1 (* blank) (regex verilog-ext-block-end-keywords-re))
       (* blank) "//" (* blank)
       (* (group (or "block:" (group verilog-identifier (* blank) "::")) (* blank)))
       (group-n 2 verilog-identifier)
       (* blank) eol)))

(defconst verilog-ext-block-end-keywords-complete-re
  (concat "^"
          "\\(?1:[[:blank:]]*"
          verilog-ext-block-end-keywords-re
          "\\)"
          "[[:blank:]]*//[[:blank:]]*"
          "\\(\\(block:\\|"
          modi/verilog-identifier-re "[[:blank:]]*::\\)[[:blank:]]*\\)*"
          "\\(?2:" modi/verilog-identifier-re "\\)"
          "[[:blank:]]*$"))


;;; Templates
;; TODO: `verilog-ext-templ-testbench-simple-from-file' fails if instantiates a DUT without parameters


;;;; UVM env
;; TODO: Convert this into a UVM env template
;; - Remove 'program' bullshit
;; - Add assertions file (bind to DUT)
;; - And so on...
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
  (let ((module-name (verilog-ext-templ-inst-auto--read-file-modules dut-file))
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




;;;; Misc
;; https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
(defvar verilog-ext-open-dirs nil
  "List with directories of current opened `verilog-mode' buffers.
Used for verilog AUTO libraries, flycheck and Verilog-Perl hierarchy.")
(defvar verilog-ext-open-pkgs nil
  "List of currently opened SystemVerilog packages.")
(defvar verilog-ext-open-pkgs-projectile nil
  "List of current open packages at projectile project.")


(defun verilog-ext-dirs-and-pkgs-of-open-buffers ()
  "Return a list of directories from current verilog opened files.
It also updates currently opened SystemVerilog packages.

Used for flycheck and vhier packages."
  (let ((verilog-opened-dirs)
        (verilog-opened-pkgs)
        (pkg-regexp "^\\s-*\\(?1:package\\)\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)"))
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "verilog-mode")
          (unless (member default-directory verilog-opened-dirs)
            (push default-directory verilog-opened-dirs))
          (save-excursion
            (goto-char (point-min))
            (when (re-search-forward pkg-regexp nil t)
              (unless (member (buffer-file-name) verilog-opened-pkgs)
                (push (buffer-file-name) verilog-opened-pkgs)))))))
    `(,verilog-opened-dirs ,verilog-opened-pkgs)))  ; Return list of dirs and packages


(defun verilog-ext-update-project-pkg-list ()
  "Update currently open packages on `verilog-ext-open-pkgs-projectile'.

Only packages within current projectile project are added.
To be used with vhier/flycheck.

INFO: Limitations:
 - Packages included as sources might not be in the proper order.
 - Some sorting method could be used in the future:
   - Extracting them from buffer file but in the order they have been
     opened and reverse sorting, for example..."
  (setq verilog-ext-open-pkgs-projectile nil) ; Reset list
  (mapc
   (lambda (pkg)
     (when (string-prefix-p (projectile-project-root) pkg)
       (unless (member pkg verilog-ext-open-pkgs-projectile)
         (push pkg verilog-ext-open-pkgs-projectile))))
   verilog-ext-open-pkgs)
  ;; Return pkg-list
  verilog-ext-open-pkgs-projectile)



;;;; Hooks
(defun verilog-ext-hook ()
  "Verilog hook."
  ;; TODO: Separate into various hooks:
  ;;  1) Open dirs/pkgs: (TODO: Could be rewritten as opened files with .sv and opened files with .svh?)
  (setq verilog-ext-open-dirs (nth 0 (verilog-ext-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-ext-open-pkgs (nth 1 (verilog-ext-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-library-directories verilog-ext-open-dirs) ; Verilog *AUTO* folders (could use `verilog-library-files' for files)
  ;;  2) Flycheck active linter
  (setq verilog-ext-flycheck-verilator-include-path verilog-ext-open-dirs)
  (flycheck-select-checker verilog-ext-flycheck-active-linter)
  ;;  4) Timestamp (TODO)
  (verilog-ext-time-stamp-update)
  ;;  5) Completion (TODO)
  (setq-local yas-indent-line 'fixed))






;;; Generic
;; TODO:
;;   - Clean verilog-utils
;;     - find-module-instance and get-header seem deprecable, based on other functions
;;     - Seems I prefer to use tokens instead of blocks/headers
;;   - The block-end-comments-to-block-names review, convert it to a minor-mode maybe?
;;   - What to do with the connect/disconnect/clean blanks ? Where to move? Editing is a nice place?
;;   - Move the regexps of compilation-utils to verilog-compile?

;; (require 'verilog-rx)
;; (require 'verilog-shadow) ; INFO: Might be useful in the future for some semantic parsing stuff
;; (require 'verilog-editing)
;; (require 'verilog-compile) ; TODO: Rename to makefile? Add compilation regexps?
;; (require 'verilog-timestamp) ; TODO: Change the 'work' section to a different name
;; (require 'verilog-compile) ; TODO: Add compilation regexp support for verilog here (as a derived compilation mode maybe?)
;; (require 'verilog-lsp)
;; TODO: Add these things for apheleia, tree-sitter, etc...


;;; rx
(require 'rx)

(defmacro rx-verilog (&rest body-forms)
  `(rx-let ((newline-or-space+ (+ (or blank "\n")))
            (newline-or-space* (* (or blank "\n")))
            (keyword* (* (+ (char "a-z")) (+ blank)))
            (verilog-comments* (* (* blank) "//" (* nonl))) ; TODO: Review if this one is necessary
            (verilog-param-port-list (group "(" (opt (+ (not ";"))) ")"))
            (verilog-almost-anything-inside-port (group (opt (1+ (not (any ";./"))))))
            (verilog-array-content (group (* "[" (+ nonl) "]")))
            (verilog-identifier (group symbol-start
                                       (or (group (any letter "_") (* (any letter digit "_$"))) ; Simple identifier
                                           (group "\\" (+ letter)))                              ; Escaped identifier
                                       symbol-end)))
     ,@body-forms))


(defvar verilog-ext-module-instance-re
  (rx-verilog
   (rx bol (* blank)                                     ; Initial optional blanks
       (group-n 1 verilog-identifier) newline-or-space*  ; Identifier
       (* "#" newline-or-space* verilog-param-port-list verilog-almost-anything-inside-port) ; Optional parameters
       ;; verilog-comments*                                 ; TODO: Review if this one is necessary
                                        ; Parameter contents
       (group-n 2 verilog-identifier)                    ; Instance name
       (* blank) verilog-array-content newline-or-space* ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
       "("                                               ; Parenthesis before ports and connections
       )))

;; TODO: Modi, to find header (probably can be removed later)
(defvar verilog-ext-header-words-re
  (regexp-opt
   '("case"
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
   'symbols))


;; TODO: Maybe use it along with tokens to get capture groups and make these re functions more generic?
(defvar verilog-ext-header-re
  (rx-verilog
   (rx bol (* blank) keyword* ; Optional virtual, local, protected
       (group-n 1 (regex verilog-ext-header-words-re))
       (+ blank) keyword* ;Optional void, static, automatic, ..
       ;; Allow parsing extern methods like class::task
       (group-n 2 (* verilog-identifier "::") verilog-identifier)
       word-boundary)))



;;; Navigation
;; In `verilog-ext-find-module-instance-fwd':
;;   TODO: Try to optimize it not to do the forward-line thing
;;   TODO: Right now the `verilog-identifier-sym-re' catches things such as (Rst_n) and .Rst_n
;;   It would be nice if it only recognized things that have an space before and after (a real symbol).
;;   TODO: Could this be done modifying temporarily the syntax table? But that might be an issue for font-locking?
;;
;; INFO: It seems it works fine, with the small optimization of the parenthesis search and byte/native compilation.
;; Probably the next step is jump into tree-sitter, instead of spend more time optimizing this shit.



;; TODO: Was quite complicated to make this work properly, or at least how I intended to
(defun verilog-ext-defun-same-level-next ()
  "Move forward to the same defun-level."
  (interactive)
  (let* ((data (verilog-ext-block-at-point))
         (block-type (alist-get 'type data))
         (start (point))
         temp-data end-pos)
    (cond (;; Functions/tasks
           (or (equal block-type "function")
               (equal block-type "task"))
           (when (setq temp-data (verilog-ext-point-inside-block-p 'class))
             (setq end-pos (alist-get 'end-point temp-data))) ; Methods inside classes
           (verilog-ext-find-function-task-fwd end-pos))
          (;; Classes inside package
           (equal block-type "class")
           (verilog-ext-find-class-fwd))
          (;; Package (top)
           (or (equal block-type "module")
               (equal block-type "interface")
               (equal block-type "program")
               (equal block-type "package"))
           (verilog-re-search-forward verilog-ext-top-re nil t))
          (t
           (verilog-re-search-forward verilog-defun-tf-re-beg nil t)))))

(defun verilog-ext-defun-same-level-prev ()
  ""
  (interactive)
  ;; TODO: Do it analogously to 'prev' function
  )


(defun verilog-ext-nav-down-dwim ()
  ""
  (interactive)
  (cond ((verilog-ext-scan-buffer-modules)
         (call-interactively #'verilog-ext-find-module-instance-fwd))
        ((or (verilog-ext-point-inside-block-p 'class)
             (verilog-ext-point-inside-block-p 'package))
         (call-interactively #'verilog-ext-defun-level-down))
        (t
         (verilog-ext-down-list))))

(defun verilog-ext-nav-up-dwim ()
  ""
  (interactive)
  (cond ((verilog-ext-scan-buffer-modules)
         (call-interactively #'verilog-ext-find-module-instance-bwd-2))
        ((or (verilog-ext-point-inside-block-p 'class)
             (verilog-ext-point-inside-block-p 'package))
         (call-interactively #'verilog-ext-defun-level-up))
        (t
         (verilog-ext-backward-up-list))))


;;;; Modi
;; TODO: Seems that instance is already handled
;; TODO: What modi calls header would be what I call token
;; TODO: Extend token-re to something more complex (like modi's) so that there are capture groups
;; TODO: And it can be easier
;; TODO: Take into account the rest of rx (like the ones used in imenu for task/func/class) etc

;; TODO: This is required by some modi functions
;; (require 'ag) ; Load `ag' package so `ag-arguments' get updated with --stats to jump to first match

;; TODO: This was added at some point to verilog-modi in the Citrix server
;; (add-to-list 'ag-arguments "--stats" :append) ; Just ensure

;; (if (and (executable-find "global")
;;          (projectile-project-root))
;;     ;; (projectile-project-root)


;; TODO: Modi headers are more complex than just looking for a word
(defun verilog-ext-get-header (&optional fwd)
  "Function to return the name of the block (module, class, package,
function, task, `define) under which the point is currently present.

If FWD is non-nil, do the block header search in forward direction;
otherwise in backward direction.

This function updates the local variable `verilog-ext-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"top\"
is returned and `verilog-ext-which-func-xtra' is updated to \"mod\" (short
for \"module\").

   module top ();
   ▯
   endmodule "
  (let (block-type block-name return-val) ;return-val will be nil by default
    (setq-local verilog-ext-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward verilog-ext-header-re nil :noerror)
              (re-search-backward verilog-ext-header-re nil :noerror))
        ;; Ensure that text in line or block comments is not incorrectly
        ;; parsed as a Verilog block header
        (when (not (equal (face-at-point) 'font-lock-comment-face))
          ;; (message "---- 1 ---- %s" (match-string 1))
          ;; (message "---- 2 ---- %s" (match-string 2))
          ;; (message "---- 3 ---- %s" (match-string 3))
          ;; (message "---- 4 ---- %s" (match-string 4))
          (setq block-type (match-string 1))
          (setq block-name (match-string 2))

          (when (and (stringp block-name)
                     (not (string-match verilog-ext-keywords-re
                                        block-name)))
            (setq-local verilog-ext-which-func-xtra
                        (cond
                         ((string= "class"     block-type) "class")
                         ((string= "clocking"  block-type) "clk")
                         ((string= "`define"   block-type) "macro")
                         ((string= "group"     block-type) "group")
                         ((string= "module"    block-type) "mod")
                         ((string= "interface" block-type) "if")
                         ((string= "package"   block-type) "pkg")
                         ((string= "sequence"  block-type) "seq")
                         (t (substring block-type 0 4)))) ;First 4 chars
            (setq return-val block-name)))))
    (when (featurep 'which-func)
      ;; (modi/verilog-update-which-func-format)
      )
    return-val))


;; TODO: Modi headers are more complex than just looking for a word
(defun verilog-ext-jump-to-header-dwim (fwd)
  "Jump to a module instantiation header above the current point. If
a module instantiation is not found, jump to a block header if available.

If FWD is non-nil, do that module instrantiation/header search in forward
direction; otherwise in backward direction.

Few examples of what is considered as a block: module, class, package, function,
task, `define."
  (interactive "P")
  (if (verilog-ext-find-module-instance fwd)
      (if fwd
          (re-search-forward verilog-ext-module-instance-re nil :noerror)
        (re-search-backward verilog-ext-module-instance-re nil :noerror))
    (if fwd
        (re-search-forward verilog-ext-header-re nil :noerror)
      (re-search-backward verilog-ext-header-re nil :noerror))))



;;; Utils
;; With respect to `verilog-ext-point-inside-block-p':
;;  - For generate thought to use `verilog-in-generate-region-p', however it didn't work as expected
;;    - (see LarumbeNotes.org)
;;
;; To detect always/initial/final that do not have begin/end (only one sentence) use
;; `verilog-end-of-statement'. This will detect either begin or ; but requires a bit
;; more of code writing.





;;; Beautify
;; TODO Add a function (C-c C-M-i) that aligns declarations of current paragraph
;; TODO Add a function (C-c C-M-o) that aligns expressions of current paragraph
;; TODO: Problem: paragraphs might not always be blocks of decl/expressions if there are no blank lines in between

;; INFO: These didn't work because only work if point is at a declaration or at a expression
;; Or in the case of a region, if the beginning or the point (don't remember)
;; So these are not useful at all!
(defun verilog-ext-pretty-declarations-block-at-point ()
  "Align declarations of current block at point."
  (interactive)
  (save-mark-and-excursion
    (let ((data (verilog-ext-block-at-point))
          block name)
      (unless data
        (user-error "Not inside a block"))
      (setq block (car data))
      (setq name (nth 1 data))
      (goto-char (nth 3 data))
      (end-of-line)
      (push-mark)
      (goto-char (nth 2 data))
      (beginning-of-line)
      (setq mark-active t)
      (verilog-pretty-declarations)
      (message "Aligned declarations of %s : %s" block name))))

(defun verilog-ext-pretty-expr-block-at-point ()
  "Align expressions of current block at point."
  (interactive)
  (save-mark-and-excursion
    (let ((data (verilog-ext-block-at-point))
          block name)
      (unless data
        (user-error "Not inside a block"))
      (setq block (car data))
      (setq name (nth 1 data))
      (goto-char (nth 3 data))
      (end-of-line)
      (push-mark)
      (goto-char (nth 2 data))
      (beginning-of-line)
      (setq mark-active t)
      (verilog-pretty-expr)
      (message "Aligned expressions of %s : %s" block name))))

;; TODO: Create function to gather typedefs of a directory and subdirectory?
;;  - Useful for typedef alignment




;;; Font-lock
;;;; Variables
(defconst verilog-ext-font-lock-range-optional-re "\\s-*\\(\\[[^]]*\\]\\s-*\\)*")
;; Think I don't need it anymore...?
;; There is `verilog-ext-range-optional-re' in `verilog-typedef'

;; Obtained with:
;; (dolist (word (cl-set-difference verilog-keywords verilog-type-keywords :test #'equal))
;;   (insert "\"" word "\" "))
;;   TODO: Can be removed?
(defconst verilog-ext-font-lock-keywords-no-types
  '("`__FILE__" "`__LINE" "`begin_keywords" "`celldefine" "`default_nettype"
    "`define" "`else" "`elsif" "`end_keywords" "`endcelldefine" "`endif"
    "`ifdef" "`ifndef" "`include" "`line" "`nounconnected_drive" "`pragma"
    "`resetall" "`timescale" "`unconnected_drive" "`undef" "`undefineall"
    "`case" "`default" "`endfor" "`endprotect" "`endswitch" "`endwhile" "`for"
    "`format" "`if" "`let" "`protect" "`switch" "`timescale" "`time_scale"
    "`while" "after" "alias" "always" "always_comb" "always_ff" "always_latch"
    "assert" "assign" "assume" "automatic" "before" "begin" "bind" "bins"
    "binsof" "bit" "break" "byte" "case" "casex" "casez" "cell" "chandle"
    "class" "clocking" "config" "const" "constraint" "context" "continue"
    "cover" "covergroup" "coverpoint" "cross" "deassign" "default" "design"
    "disable" "dist" "do" "edge" "else" "end" "endcase" "endclass" "endclocking"
    "endconfig" "endfunction" "endgenerate" "endgroup" "endinterface"
    "endmodule" "endpackage" "endprimitive" "endprogram" "endproperty"
    "endspecify" "endsequence" "endtable" "endtask" "enum" "event" "expect"
    "export" "extends" "extern" "final" "first_match" "for" "force" "foreach"
    "forever" "fork" "forkjoin" "function" "generate" "genvar" "highz0" "highz1"
    "if" "iff" "ifnone" "ignore_bins" "illegal_bins" "import" "incdir" "include"
    "initial" "inside" "instance" "int" "interface" "intersect" "join"
    "join_any" "join_none" "large" "liblist" "library" "local" "longint"
    "macromodule" "matches" "medium" "modport" "module" "negedge" "new"
    "noshowcancelled" "null" "package" "packed" "posedge" "primitive" "priority"
    "program" "property" "protected" "pulsestyle_onevent" "pulsestyle_ondetect"
    "pure" "rand" "randc" "randcase" "randsequence" "ref" "release" "repeat"
    "return" "scalared" "sequence" "shortint" "shortreal" "showcancelled"
    "signed" "small" "solve" "specify" "specparam" "static" "string" "strong0"
    "strong1" "struct" "super" "supply0" "supply1" "table" "tagged" "task"
    "this" "throughout" "timeprecision" "timeunit" "type" "typedef" "union"
    "unique" "unsigned" "use" "uwire" "var" "vectored" "virtual" "void" "wait"
    "wait_order" "weak0" "weak1" "while" "wildcard" "with" "within" "accept_on"
    "checker" "endchecker" "eventually" "global" "implies" "let" "nexttime"
    "reject_on" "restrict" "s_always" "s_eventually" "s_nexttime" "s_until"
    "s_until_with" "strong" "sync_accept_on" "sync_reject_on" "unique0" "until"
    "until_with" "untyped" "weak" "implements" "interconnect" "nettype" "soft"))
(defconst verilog-ext-font-lock-keywords-no-types-re
  (verilog-regexp-words verilog-ext-font-lock-keywords-no-types))



(defvar verilog-ext-font-lock-variable-type-face 'verilog-ext-font-lock-variable-type-face)
(defface verilog-ext-font-lock-variable-type-face
  '((t (:foreground "powder blue")))
  "Face for variable types."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-variable-name-face 'verilog-ext-font-lock-variable-name-face)
(defface verilog-ext-font-lock-variable-name-face
  '((t (:foreground "DarkSeaGreen1")))
  "Face for variable names."
  :group 'verilog-ext-font-lock-faces)


;; TODO: Do something with this or use default's verilog-mode?
(defvar verilog-ext-highlight-variable-declaration-names nil)


;; TODO: Check `verilog-declaration-varname-matcher' and `verilog-single-declaration-end'
;; TODO: There should be mandatory space between logic[3:0] ? For unpacked arrays is not mandatory, is it?
(defconst verilog-ext-variable-re-1
  (concat "\\<\\(?1:" verilog-identifier-re "\\)\\>" verilog-ext-range-optional-re ; Var type
          "\\<\\(?3:" verilog-identifier-re "\\)\\>" verilog-ext-range-optional-re ; Var name
          "\\s-*\\(?4:=.*\\)?;")                                                  ; Optional initialization value
  "type_t foo;
   type_t [10:0] foo;
   type_t [10:0] foo = 'h0;
")
;; TODO: Check `verilog-declaration-varname-matcher' and `verilog-single-declaration-end'
(defconst verilog-ext-variable-re-2
  (concat "\\<\\(?1:" verilog-identifier-re "\\)\\>"
          "\\s-+\\(?3:\\(" verilog-identifier-re "\\s-*,\\s-*\\)+\\(" verilog-identifier-re "\\s-*\\)\\);")
  "type_t foo1, foo2 , foo4, foo6[], foo7 [25], foo8 ;")

;; TODO: Check `verilog-declaration-varname-matcher' and `verilog-single-declaration-end'
(defconst verilog-ext-variable-re-3
  (concat "\\<\\(input\\|output\\|inout\\|ref\\|parameter\\|localparam\\)\\>\\s-+"
          "\\<\\(?1:" verilog-identifier-re "\\)\\>\\s-+" verilog-ext-range-optional-re
          "\\<\\(?3:" verilog-identifier-re "\\)\\>\\s-*" verilog-ext-range-optional-re)
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


;;;;; Another neat attempt

(defun verilog-ext-font-lock-typedef-var-decl-fontify (regex limit)
  "Fontify user types variables declarations.
Search for REGEX that matches declaration bound by LIMIT."
  (let (found pos type)
    (save-excursion
      (while (and (not found)
                  (verilog-re-search-forward regex limit t))
        (setq type (match-string-no-properties 1))
        (unless (member type verilog-keywords)
          (setq found t)
          (setq pos (point)))))
    (when found
      (add-to-list 'verilog-align-typedef-words type) ; Allow being able to be aligned
      (goto-char pos))))

(defun verilog-ext-font-lock-typedef-var-single-decl-fontify (limit)
  "Fontify user types single variables declarations."
  (verilog-ext-font-lock-typedef-var-decl-fontify verilog-ext-typedef-var-decl-single-re limit))

(defun verilog-ext-font-lock-typedef-var-multiple-decl-fontify (limit)
  "Fontify user types single variables declarations."
  (verilog-ext-font-lock-typedef-var-decl-fontify verilog-ext-typedef-var-decl-multiple-re limit))

    ;; User type variable declarations
    '(verilog-ext-font-lock-typedef-var-single-decl-fontify
      (1 'font-lock-type-face))
    '(verilog-ext-font-lock-typedef-var-multiple-decl-fontify
      (1 'font-lock-type-face))


;;;; Custom constructs
(defconst verilog-ext-special-macros
  (verilog-regexp-words
   '( ;; DMA Macros
     "MY_CUSTOM_MACRO"
     ))) ; Used for non-verilog constructs (i.e. custom preprocessing)

(defconst verilog-ext-special-constructs
  (verilog-regexp-words
   '(;; These constructs contain some special character that prevent them to be detected as symbols
     "@special_construct"
     "%special_construct"
     ))) ; Used for non-verilog constructs (i.e. custom preprocessing)


;; Put inside `verilog-ext-font-lock-keywords', after macros
   ;; Special macros
   (cons (concat "\\<\\(" verilog-ext-special-macros "\\)\\>") 'verilog-ext-font-lock-xilinx-attributes-face)
   ;; Special constructs
   (cons (concat "\\(" verilog-ext-special-constructs "\\)") 'verilog-ext-font-lock-xilinx-attributes-face)


;; Put inside `verilog-ext-font-lock-keywords-3'

    ;; Variable types
    '(verilog-ext-find-verilog-variable-type-fontify-1
      (0 'verilog-ext-font-lock-variable-type-face))
    '(verilog-ext-find-verilog-variable-type-fontify-2
      (0 'verilog-ext-font-lock-variable-type-face))
    '(verilog-ext-find-verilog-variable-type-fontify-3
      (0 'verilog-ext-font-lock-variable-type-face))

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
      ))


;; Put inside `verilog-ext-font-lock-keywords-3'
;; TODO: Copied from verilog-mode (to fontify variables controlled by knob)
   ;; Variables fontification
   (list
    verilog-declaration-re
    (list
     ;; Anchored matcher (lookup Search-Based Fontification)
     'verilog-declaration-varname-matcher
     ;; Pre-form for this anchored matcher:
     ;; First, avoid declaration keywords written in comments,
     ;; which can also trigger this anchor.
     '(if (and (not (verilog-in-comment-p))
               (not (member (thing-at-point 'symbol) verilog-keywords)))
          (verilog-single-declaration-end verilog-highlight-max-lookahead)
        (point)) ;; => current declaration statement is of 0 length
     nil ;; Post-form: nothing to be done
     '(0 verilog-ext-font-lock-variable-name-face)))



;;; Completion
;; TODO: Company improvements/ideas:
;;  - Add a company-backend that fetches attributes/methods of class after typing name. and then completing:
;;    - If thing before . is a class name:
;;       - Use global to find where it's defined, parse the file (maybe with verilog shadow), and find attributes/methods
;;       - Use them as completion candidates with some meta/annotation saying if they are attributes or methods (also seems useful for UVM classes)
;;       - Also add some class builtin methods such as randomize()
;;
;;    - If thing before . is an interface:
;;       - Do the same as for classes but parse its signals and return them as candidates
;;
;;    - If thing before . is not a class name:
;;       - It could be an array or queue: complete with their builtin methods and use meta/annotation
;;       -
;; INFO: All of this is probably SUPER EASY with tree-sitter. The problem is learning how to use tree-sitter
;;
;;
;; TODO: Add some CAPF improvements?
;; `verilog-completion-at-point' is added to CAPF. It calls `verilog-completion' which in turns
;; completes depending on the context. This context is determined based on indentation. Since
;; indentation is changed, this could be the reason why it fails. Or maybe it works fine but I didn't use it properly.
;; Study `verilog-completion'.
;;
;; `verilog-complete-word' and `verilog-show-completions' are fallbacks for Emacs versions lacking `completion-at-point'
;;
;; Get some idea for words in opened buffers? Like hippie? Is that a backend for company already?
;;
;; TODO: Add some CAPF that uses global to determine what current definition type is?
;;  - E.g.:
;;   - Use regular completion, except when after .
;;      - if current definition is a class, get its attributes and methods in a list and prompt them as completion candidates, plus randomize() method etc
;;      - if current definition is an array prompt for array methods
;;      - if is an enum for enum methods, if is a queue for queue methods, etc... Some semantic analysis
;;      - Could be done with tree-sitter?

;;;; Hydra
("TE"  (call-interactively #'verilog-ext-templ-testbench-env-from-file)        "TB from DUT file (full env)")



;;; Imenu
(defun verilog-ext-imenu-list-hide-all (&optional first)
  "Hide all the blocks at `imenu-list' buffer.
If optional arg FIRST is non-nil show first Imenu block
which by default corresponds to *instances*.
INFO: It is meant to be run after `verilog-ext-imenu-list', however
it could cause sluggish behaviour as it's not every efficient."
  (if (string-equal major-mode "imenu-list-major-mode")
      (progn
        (goto-char (point-min))
        (while (< (point) (point-max))
          (hs-hide-block)
          (line-move-visual 1))
        (goto-char (point-min))
        (when first
          (hs-show-block)))
    (message "Not in imenu-list mode !!")))


;; TODO: Do a minor-mode that adds/removes the hooks?
;;  - (add-hook 'verilog-mode-hook #'verilog-ext-imenu-hook)
;;

;; About nesting classes:
;; The original definition held a jump-label lexical variable, fetched from python-mode imenu build function
;; However, the add argument was not used.
;; INFO: Implement this recursive thing at some point?
(defun verilog-ext-imenu--class-put-parent (type name pos tree &optional add)
  "Create parent tag with TYPE and NAME.
If optional arg ADD is non-nil, add the parent with TYPE, NAME and POS to TREE."
  (let* ((label (funcall #'verilog-ext-imenu--format-class-item-label type name))
         (jump-label label))
    (if (not tree)
        (cons label pos)
      (if add
          (cons label (cons (cons jump-label pos) tree))
        (cons label tree)))))

(defun verilog-ext-imenu--build-class-tree (&optional tree)
  "Build the imenu alist TREE recursively.
Coded to work with verification files with CLASSES and METHODS.
Adapted from `python-mode' imenu build-tree function."
  (save-restriction
    (narrow-to-region (point-min) (point))
    (let* ((pos (progn
                  (verilog-re-search-backward verilog-ext-class-re nil t)
                  (verilog-forward-sexp)
                  (verilog-re-search-backward "\\<\\(function\\|task\\|class\\)\\>" nil t)))
           type
           (name (when (and pos
                            (or (looking-at verilog-ext-task-re)
                                (looking-at verilog-ext-function-re)
                                (looking-at verilog-ext-class-re)))
                   (setq type (match-string-no-properties 1))
                   (match-string-no-properties 2)))
           (label (when name
                    (funcall #'verilog-ext-imenu--format-class-item-label type name))))
      (cond ((not pos)
             nil)
            ((looking-at verilog-ext-class-re)
             ;; TODO: Do something here, instead of nil do some recursive magic
             (verilog-ext-imenu--class-put-parent type name pos tree nil)) ; Do not want class imenu redundancy (tags+entries)
            ;; End of TODO
            (t
             (verilog-ext-imenu--build-class-tree
              (if (or (looking-at verilog-ext-task-re)
                      (looking-at verilog-ext-function-re))
                  (cons (cons label pos) tree)
                (cons
                 (verilog-ext-imenu--build-class-tree
                  (list (cons label pos)))
                 tree))))))))

;; TODO: Use fonts for Imenu to differentiate between functions/tasks
;; INFO: Tested and worked!
(defun verilog-ext-imenu--format-class-item-label (type name)
  "Return Imenu label for single node using TYPE and NAME."
  (let ((props (pcase type
                 ("task"     'italic)
                 ("function" 'bold)
                 ("class"    nil)
                 (_          nil))))
    (format "%s" (propertize name 'face prop))))

;; INFO: Different imenu implementations override faces:
;;  - e.g. ivy-imenu somehow ignores faces? It worked once, but other times it didn't...
;;  - imenu-list will only be affected by bold/italic, but not by foreground (overrides faces)
;;  - So probably the best option is use a tag at the beginning as it was first
(defun verilog-ext-imenu--format-class-item-label (type name)
  "Return Imenu label for single node using TYPE and NAME."
  (let ((props (pcase type
                 ("task"     '(:foreground "red"))
                 ("function" '(:foreground "blue" :weight bold))
                 ("class"    nil)
                 (_          nil))))
    (format "%s" (propertize name 'font-lock-face props))))



;; About `verilog-ext-imenu-classes-index':
;; INFO: Tasks/functions outside classes are obtained with a custom function search
;; in the generic imenu-generic-function stage.
;; INFO: Detection of nested classes is unsupported and leads to bad detection of
;; class tasks/functions."



;;; Which-func
;; TODO: In `verilog-ext-block-at-point':
;;  - Do something more efficient:
;;  - Look for all the possible regexps ??

;; TODO: Seems it's not used!
(defun hdl-ext-which-func-current ()
  ""
  (gethash (get-buffer-window) which-func-table))
;; End of TODO

;; TODO: Don't seem to be necessary anymore

;; (defun verilog-ext-which-func-find-instance ()
;;   ""
;;   (let (instance-point instance-type instance-name)
;;     (save-excursion
;;       (when (verilog-ext-instance-at-point)
;;         (setq instance-point (point))
;;         (setq instance-type (match-string-no-properties 1))
;;         (setq instance-name (match-string-no-properties 2))))
;;     (list instance-point instance-type instance-name)))


;; (defun verilog-ext-which-func-find-token ()
;;   ""
;;   (let (token-point token-type token-name)
;;     (save-excursion
;;       (when (verilog-ext-find-token-bwd)
;;         (setq token-point (point))
;;         (setq token-type (match-string-no-properties 1))
;;         ;; Similar to `verilog-ext-find-task-function-class-bwd'. TODO: Could be refactored?
;;         (if (or (looking-at verilog-ext-function-re)
;;                 (looking-at verilog-ext-task-re)
;;                 (looking-at verilog-ext-class-re)
;;                 (looking-at verilog-ext-top-re))
;;             (setq token-name (match-string-no-properties 2))
;;           (setq token-name (buffer-substring-no-properties (point) (point-at-eol))))))
;;     (list token-point token-type token-name)))





;; (defun verilog-ext-which-func-set-instance (instance-type instance-name)
;;   ""
;;   (setq verilog-ext-which-func-xtra instance-name)
;;   instance-type)


;; (defun verilog-ext-which-func-set-token (token-type token-name)
;;   ""
;;   (setq verilog-ext-which-func-xtra (verilog-ext-which-func-maybe-shorten-token token-type))
;;   token-name)


;; (defun verilog-ext-which-func-decide (instance-data token-data)
;;   ""
;;   (let ((instance-point (nth 0 instance-data))
;;         (instance-type  (nth 1 instance-data))
;;         (instance-name  (nth 2 instance-data))
;;         (token-point (nth 0 token-data))
;;         (token-type  (nth 1 token-data))
;;         (token-name  (nth 2 token-data)))
;;     (cond (;; Instance found
;;            (and instance-point (not token-point))
;;            (verilog-ext-which-func-set-instance instance-type instance-name))
;;           ;; Token found
;;           ((and (not instance-point) token-point)
;;            (verilog-ext-which-func-set-token token-type token-name))
;;           ;; Both found: select closest one
;;           ((and instance-point token-point)
;;            (if (> instance-point token-point) ; which-func searches backwards, closest is the one with highest point value
;;                (verilog-ext-which-func-set-instance instance-type instance-name)
;;              (verilog-ext-which-func-set-token token-type token-name))))))


;; (defun verilog-ext-which-func-function ()
;;   ""
;;   (let ((instance-data (verilog-ext-which-func-find-instance))
;;         (token-data    (verilog-ext-which-func-find-token)))
;;     (verilog-ext-which-func-decide instance-data token-data)))


;;; Flycheck
;; TODO: Tried to use the javascript binding for the SV tree-sitter linter but got this error:
;; Error: /lib64/libstdc++.so.6: version `GLIBCXX_3.4.20' not found (required by /home/egonlar/node_modules/svlint/node_modules/tree-sitter/build/Release/tree_sitter_runtime_binding.node)
;; Check the Elisp binding and see how hward would it be to do the equivalent

;; TODO: Still doesn't recognize verible at startup

(defvar verilog-ext-flycheck-eldoc-toggle t)

(defun verilog-ext-flycheck-eldoc-toggle ()
  "Disable `eldoc-mode' when enabling `flycheck-mode'.
Avoid minibuffer conflicts between ggtags use of eldoc and flycheck."
  (interactive)
  (if eldoc-mode
      (progn
        (eldoc-mode -1)
        (flycheck-mode 1)
        (message "Flycheck enabled"))
    (eldoc-mode 1)
    (flycheck-mode -1)
    (message "Flycheck disabled")))


;; (define-minor-mode verilog-ext-flycheck-mode-toggle-toggle
n;;   "Flycheck wrapper that coexists with `eldoc'."
;;   :lighter ""
;;   (when verilog-ext-flycheck-mode-toggle-toggle
;;     (if eldoc-mode
;;         (progn
;;           (eldoc-mode -1)
;;           (flycheck-mode 1)
;;           (message "Flycheck enabled"))
;;       (eldoc-mode 1)
;;       (flycheck-mode -1)
;;       (message "Flycheck disabled"))))



;; (defun verilog-ext-flycheck-mode-toggle (&optional uarg)
;;   "`flycheck-mode' Verilog wrapper function.
;; If called with UARG, select among available linters.

;; Disable function `eldoc-mode' if flycheck is enabled
;; to avoid minibuffer collisions."
;;   (interactive "P")
;;   (let (enable)
;;     (when buffer-read-only
;;       (error "Flycheck does not work on read-only buffers!"))
;;     (if uarg
;;         (progn
;;           (verilog-ext-flycheck-set-linter)
;;           (setq enable t))
;;       ;; Toggle flycheck mode
;;       (unless flycheck-mode
;;         (setq enable t))
;;             (flycheck-mode -1)
;;             (message "Flycheck disabled"))
;;         (flycheck-mode 1)
;;         (message "[%s] Flycheck enabled" verilog-ext-flycheck-linter)))
;;     (when verilog-ext-flycheck-eldoc-toggle
;;       (if flycheck-mode
;;           (eldoc-mode -1)
;;         (eldoc-mode 1)))
;;     ;; (verilog-ext-update-project-pkg-list)
;;     ;; (verilog-ext-flycheck--extra-actions-post)
;;     )
;; (flycheck-mode 1)
;;           (message "[%s] Flycheck enabled" verilog-ext-flycheck-linter)



;; (defun verilog-ext-flycheck-eldoc-toggle ()
;;   "Disable `eldoc-mode' when enabling `flycheck-mode'.
;; Avoid minibuffer conflicts between ggtags use of eldoc and flycheck."
;;   (interactive)
;;   (if eldoc-mode
;;       (progn
;;         (eldoc-mode -1)
;;         (flycheck-mode 1)
;;         (message "Flycheck enabled"))
;;     (eldoc-mode 1)
;;     (flycheck-mode -1)
;;     (message "Flycheck disabled")))


(defun verilog-ext-flycheck--extra-actions-post ()
  "Extra actions to perform after enabling flycheck.
Actions for `verilog-ext-flycheck-linter'."
  (when (and (equal verilog-ext-flycheck-linter 'verilog-cadence-hal)
             (equal flycheck-mode t))
    (message "Cadence HAL linting...")))



;; TODO: Use the output of `verilog-expand-command' for different linter commands:
(verilog-expand-command "__FLAGS__")
;; INFO: This requires setting `verilog-library-files' and `verilog-library-directories' and `verilog-library-extensions'
;; accordingly. Probably this can be done after the pkg update and all of that

;; TODO: Add some options on the linters to use a -f or -F option (this will be really useful)

;; Add this option or equivalent to checkers command:
;; (option-list "" verilog-ext-verilog-project-pkg-list concat)
;; (option-list "" verilog-ext-verilog-project-pkg-list concat)

;; TODO: Verilator error checking:
;; INFO: Required to add a column for latests version of Verilator!
;; TODO: Send a bug report/pull request at some point



;; TODO: Add eventually to comments
;; Notes about linters:
;;
;; - Verilator:
;;    - Advantages:
;;      - Very complete linter for RTL code
;;      - Good SystemVerilog support for RTL constructs
;;    - Drawbacks:
;;      - Lacks support for SystemVerilog simulation constructs
;;      - Does not support ignoring missing modules (https://github.com/verilator/verilator/issues/2835)
;;      - Cannot lint unpreprocessed code (`defines/`includes/UVM macros)
;;
;; - Iverilog
;;    - Advantages:
;;      - Supports ignoring missing modules
;;    - Drawbacks:
;;      - Very small amount of support for SystemVerilog
;;
;; - Verible
;;    - Advantages:
;;      - Allows linting of single files
;;      - Allows linting of unpreprocessed code
;;      - Best option to find syntax errors on single complex testbench files
;;    - Drawbacks:
;;      - Lacks support for SystemVerilog simulation constructs
;;
;; - Svlint
;;    - Advantages:
;;      - It seems it uses slang under the hood (very good SV support)
;;    - Drawbacks:
;;      - Not many linting rules available, not very complete
;;      - Doesn't allow linting of unpreprocessed code (errors with defines/includes)
;;
;; - Cadence HAL
;;    - Advantages:
;;      - Complete support for RTL
;;      - Huge amount of linting rules for code quality
;;    - Drawbacks:
;;      - Not free
;;
;; - Slang
;;    - Advantages:
;;      - Full support of SV/UVM
;;    - Disadvantages:
;;      - Doesn't support linting of unpreprocessed code/single files
;;
;;



;; INFO: Notes about slang:
;; "--lint-only";; TODO: elaborates but does not expect a top-module
;; "--ignore-unknown-modules" ; TODO: Ignore not found modules but still do type checking
;; "--parse-only" ; TODO: Don't do type checking, just check syntax errors, but still checks macros (so it's a bit of a mess for large TB projects)

;; Add the -f or something for UVM library support:
(defvar verilog-ext-flycheck-slang-uvm-path "/home/egonlar/auxfiles/slang/UVM-1.1d-mod/src")

  ;; :command ("slang"
  ;;           "/home/egonlar/auxfiles/slang/UVM-1.1d-mod/src/uvm_pkg.sv"
  ;;           "+incdir+/home/egonlar/auxfiles/slang/UVM-1.1d-mod/src"
  ;;           "--lint-only"
  ;;           "--ignore-unknown-modules"

;; For error patterns:
   ;; (warning (file-name) ":" line ":" column ": warning: " (message))) ; TODO: Check if this is valid


;; For svlint error pattenrs:
;;    ;; (error   line-start "Error:" (message)) ; No file-name / line to parse

;; INFO: About svling
;; A bit rudimentary, with not many rules but enough to check for parsing errors.
;; Could be useful for small RTL self-contained blocks (i.e, almost never).

;; However, fails dramatically if defines are not found.
;;
;; INFO: Some of its failures didn't have a file line/number and that makes it impossible
;; for flycheck to test them properly



;;; Vhier
;; 3 options:
;;  - outline/outshine (currently used)
;;  - Treemacs as a framework: https://github.com/Alexander-Miller/treemacs/blob/master/Extensions.org
;;  - hierarchy.el (bundled with Emacs 28.1): https://github.com/DamienCassou/hierarchy

;; INFO: First preprocesses input files for `include' and `define' expansion.
;; Then extracts hierarchy from that preprocessed file.
(defvar verilog-ext-vhier-pp-outfile nil)
(defvar verilog-ext-vhier-pp-args    nil)

(defvar verilog-ext-vhier-vhier-filelist-name "vhier.files")
(defvar verilog-ext-vhier-vhier-filelist-path nil)

(defvar verilog-ext-vhier-vhier-outfile "hierarchy.v")

(defvar verilog-ext-vhier-projects nil
  "Projects list:
Name of the project (+plus)
1) Name of the top-module
2) Input files for hierarchy elaboration
3) Output hierarchy file path")
(defvar verilog-ext-vhier-top-module  nil)
(defvar verilog-ext-vhier-project-dir nil)
(defvar verilog-ext-vhier-input-files nil)


;;;;; Utility functions
(defun verilog-ext-buffer-expand-filenames (&optional absolute exp-dir)
  "Expands filenames paths present in `current-buffer' line by line.
If ABSOLUTE is nil expand relative to `default-directory'.
If ABSOLUTE is non-nil filenames will expand to their absolute paths.
If EXP-DIR is non-nil, expand relative to this argument instead
of `default-directory'."
  (let ((cur-line)
        (default-directory (if exp-dir
                               exp-dir
                             default-directory)))
    (save-excursion
      (goto-char (point-min))
      (while (< (point) (point-max))
        (delete-horizontal-space)
        (if absolute
            (setq cur-line (expand-file-name (thing-at-point 'line) default-directory))
          (setq cur-line (file-relative-name (thing-at-point 'line) default-directory)))
        (kill-line 1)
        (insert cur-line)))))


(defun verilog-ext-sort-regexp-at-the-beginning-of-file (regexp)
  "Move lines containing REGEXP recursively at the beginning of the file.
Done line by line, this might be useful when managing a list of files,
one file at a line, and there is some need of sorting by regexp.
For example, in SystemVerilog, packages might need to be included before other files."
  (interactive)
  (let ((sorted-files-p nil))
    (goto-char (point-min))
    (while (not sorted-files-p)
      (save-excursion
        (unless (search-forward-regexp regexp nil 1)
          (setq sorted-files-p t))
        (beginning-of-line)
        (kill-line 1)) ; Kill trailing newline as well
      (yank))))



;;;;; Actual logic
(defun verilog-ext-vhier-set-active-project ()
  "Retrieve Vhier project list and set variables accordingly."
  (let ((vhier-project)
        (files-list))
    ;; Get Project name
    (setq vhier-project (completing-read "Select project: " (mapcar 'car verilog-ext-vhier-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc vhier-project verilog-ext-vhier-projects)))
    ;; Set parameters accordingly
    (setq verilog-ext-vhier-top-module  (nth 0 files-list))
    (setq verilog-ext-vhier-input-files (nth 1 files-list))
    (setq verilog-ext-vhier-project-dir (nth 2 files-list))
    (setq verilog-ext-vhier-pp-outfile
          (concat (verilog-ext-path-join verilog-ext-vhier-project-dir verilog-ext-vhier-top-module)
                  "_pp.sv"))
    (setq verilog-ext-vhier-pp-args (concat "-o " verilog-ext-vhier-pp-outfile))
    (setq verilog-ext-vhier-vhier-filelist-path (verilog-ext-path-join verilog-ext-vhier-project-dir verilog-ext-vhier-vhier-filelist-name))))



(defun verilog-ext-vhier-create-filelist (&optional sort-defs-pkg)
  "Generate verilog-ext-vhier-vhier-filelist-name filelist.
Generate from `verilog-ext-vhier-input-files'file (normally gtags.files).

INFO: Assumes that files fetched from `verilog-ext-vhier-input-files' are
relative paths.

If optional arg SORT-DEFS-PKG is set then move every *_defs_pkg.sv file
to the beginning."
  (let ((exp-dir (file-name-directory verilog-ext-vhier-input-files))
        (debug nil)) ; INFO: Debug `with-temp-buffer', set to non-nil to debug temp buffer contents.
    (make-directory verilog-ext-vhier-project-dir t) ; Create vhier folder if it did not exist
    (with-temp-buffer
      (when debug
        (clone-indirect-buffer-other-window "*debug*" t))
      (insert-file-contents verilog-ext-vhier-input-files)
      (verilog-ext-buffer-expand-filenames t exp-dir)
      (verilog-ext-replace-regexp-whole-buffer "\\(.*/\\).*\.[s]?vh$" "-y \\1") ; Replace header `include' files with -y library flag
      (when sort-defs-pkg
        (verilog-ext-sort-regexp-at-the-beginning-of-file "_defs_pkg.sv"))
      (write-file verilog-ext-vhier-vhier-filelist-path))))







;;;###autoload
(defun verilog-ext-vhier-extract-hierarchy ()
  "Execute shell processes that preprocess hierarchy.
Preprocess from `verilog-ext-vhier-vhier-filelist-name'
and extract hierarchy from previous preprocessed file.

INFO: Defined as interactive for the case when the command
`verilog-ext-vhier-from-project'fails due to some reformatting needed on
previously created `verilog-ext-vhier-vhier-filelist-name' via
`verilog-ext-vhier-create-filelist'. e.g: some included file was not
added via -yDIR but as a source file and cannot be found."
  (interactive)
  (let* ((shell-command-dont-erase-buffer t) ; Append output to buffer
         (pp-cmd (concat "vppreproc "
                         "-f " verilog-ext-vhier-vhier-filelist-path " "
                         verilog-ext-vhier-pp-args))
         (vhier-cmd (concat "cd " verilog-ext-vhier-project-dir " && "
                            "vhier " (mapconcat #'identity verilog-ext-vhier-vhier-args " ") " --top-module " verilog-ext-vhier-top-module " "
                            verilog-ext-vhier-pp-outfile))
         (buf     verilog-ext-vhier-buffer-name)
         (buf-err verilog-ext-vhier-shell-cmds-buffer-name)
         (file-path (verilog-ext-path-join verilog-ext-vhier-project-dir verilog-ext-vhier-vhier-outfile))
         (err-msg (format "returned with errors\nCheck %s buffer\nModify %s\nAnd finally run `verilog-ext-vhier-extract-hierarchy' instead of `verilog-ext-vhier-from-project' !"
                          buf-err verilog-ext-vhier-vhier-filelist-path)))
    ;; Preprocess and extract hierarchy (vppreproc && vhier)
    (unless (= 0 (shell-command pp-cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error (concat "vppreproc " err-msg)))
    (unless (= 0 (shell-command vhier-cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error (concat "vhier " err-msg)))
    ;; Format buffer and write file
    (verilog-ext-vhier-format-hierarchy-write-file file-path)))


;;;###autoload
(defun verilog-ext-vhier-from-project ()
  "Extract hierarchy of top level module using Verilog-Perl backend."
  (interactive)
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (verilog-ext-vhier-set-active-project)
  (verilog-ext-vhier-create-filelist)
  (verilog-ext-vhier-extract-hierarchy))



;; VHIER Comments
;; TODO: In this order preferably:
;;  - First try to make it work the `verilog-ext-vhier-current-file'
;;  - Then try to make it work the more generic (don't do it by project, seems too complex)
;;  - Try to avoid the preprocessing stuff and try to use the __FLAGS__ of verilog-mode
;;  - Add a variable for additional arguments:
;;    - e.g. to use a -f __FILE__ or -F __FILE__ (to add extra command arguments, like missing packages in specific order, etc.)
;;
;;
;;
;; `vhier-outline-mode':
;; Navigate with `outline-minor-mode' through extracted Verilog-Perl hierarchy.
;;
;; `verilog-ext-vhier-current-file' and `verilog-ext-vhier-from-project':
;; Extract verilog hierarchy of current open files or from project list.
;;


;; Arguments
         ;; (pkg-files  (mapconcat #'identity (verilog-ext-update-project-pkg-list) " "))
         ;; (include-dirs (concat "-y " (mapconcat #'identity verilog-library-directories " -y "))) ; Did not have an effect

                      ;; include-dirs     " "
                      ;; pkg-files        " "


    ;; (verilog-read-defines) ; Not sure if needed...
    ;; (verilog-read-includes)



;; In `verilog-ext-vhier-format-hierarchy-write-file'
      ;; (if verilog-ext-vhier-input-files
      ;;     (insert (concat "// Hierarchy extracted from files included in: " verilog-ext-vhier-input-files "\n"))
      ;;   (insert (concat "// Hierarchy extracted from `verilog-ext-open-dirs' variable\n")))



;;; Init-verilog
;;          ("C-M-."    . verilog-ext-find-parent-module)
;;          ("C-M-n"    . verilog-ext-find-token-fwd)
;;          ("C-M-p"    . verilog-ext-find-token-bwd)
;;          ("C-c c"    . verilog-ext-toggle-connect-port)
;;          ("C-c C-c"  . verilog-ext-connect-ports-recursively)
;;          ("C-c t"    . verilog-ext-time-stamp-work-new-entry)
;;          ("C-c C-p"  . verilog-ext-preprocess)



;; (use-package verilog-ext
;;   :straight nil
;;   :after verilog-mode
;;   :demand
;;   :commands (verilog-ext-flycheck-select-linter)
;;   :hook ((verilog-mode . verilog-ext-hook))
;;   :bind (:map verilog-mode-map
;;   ;; :config
;;   ;; Dependencies
;;   ;; (require 'xah-lee-functions)
;;   ;; (require 'ag)
;;   ;; Bind chords
;;   ;; (bind-chord "\\\\" #'verilog-ext-jump-to-module-def-at-point verilog-mode-map)
;;   ;; (bind-chord "\|\|" #'verilog-ext-find-parent-module verilog-mode-map)
;;   ;; (key-chord-mode 1)
;;   )

;;; Compilation
;; For `verilog-ext-makefile-compile' use the custom compile regexp:
; TODO: What to do with this? Something like: if (featurep 'compilation-ext (compilation-ext whatever?))
(larumbe/compile cmd nil "verilog-make")
;; ))


;; INFO: Discarding the following `verilog-set-compile-command' variables:
;; - `verilog-linter:' replaced by FlyCheck with opened buffers as additional arguments, plus custom project parsing functions
;; - `verilog-simulator': replaced by XSim and ncsim sim project funcions
;; - `verilog-compiler': replaced by Vivado elaboration/synthesis project functions
;; - `verilog-preprocessor': `verilog-ext-preprocess' wrapper of verilog-mode internal function' does the trick
;; - `verilog-coverage' still not implemented as there are not many free alternatives...

;;; Tree-sitter
(defface tree-sitter-hl-face:error
  '((default :inherit tree-sitter-hl-face:string :underline "red"))
  ""
  :group 'tree-sitter-hl-faces)

(defface tree-sitter-hl-face:verilog-instance
  '((default :inherit verilog-ext-font-lock-instance-face))
  ""
  :group 'tree-sitter-hl-faces)

(defface tree-sitter-hl-face:verilog-module
  '((default :inherit verilog-ext-font-lock-module-face))
  ""
  :group 'tree-sitter-hl-faces)


;; (verilog-ext-profile-file "/vobs/fpga/cobra/src/paam_if_ext_ic/tb/src/paam_if_ext_ic_tb_top.sv")
;; (verilog-ext-profile-file "/vobs/fpga/cobra/src/paam_if_ext_ic/tb/lib/env/sv/paam_if_ext_ic_ptd_engine_ref_model.svh")
;; (verilog-ext-profile-imenu)


;;; Lsp
;; INFO: To make it work, just add the following at the end of the file so that verible gets added:
;; (verilog-ext-lsp-configure)
;; (verilog-ext-lsp-set-default-server)
;;
;; And execute M-x lsp RET on a verilog-mode buffer (or add it as a hook)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Language servers:
;; - Supported by `lsp-mode' without additional config:
;;   - hdl_checker: https://github.com/suoto/hdl_checker
;;   - svlangserver: https://github.com/imc-trading/svlangserver
;;
;; - With some additional config:
;;   - verible: https://github.com/chipsalliance/verible/tree/master/verilog/tools/ls
;;   - svls (svlint based): https://github.com/dalance/svls
;;   - veridian: https://github.com/vivekmalneedi/veridian
;;
;; Summary:
;;   - All of them somehow seem a bit simple at least with Emacs integration
;;   (might need a bit of research)
;;
;; Some of these might be using slang (SystemVerilog Language Features), which seems a C++ library:
;; - https://github.com/MikePopoloski/slang
;;
;;
;; INFO: Problems encountered:
;; 'verible-ls gave this error continuosly:
;; Error running timer `lsp--on-idle': (wrong-type-argument number-or-marker-p nil)
;;   - Some error probably relatd to `lsp-headerline--check-breadcrumb' due to 'verible-ls
;;     being still in progress


;; Tried to do it with `eglot-alternatives', but it seems better to set only one language server instead of all of them
(defun verilog-ext-eglot-set-server ()
  "Configure Verilog for `eglot'.
Override any previous configuration for `verilog-mode'."
  (interactive)
  (setq eglot-server-programs (assq-delete-all 'verilog-mode eglot-server-programs))
  (push (cons 'verilog-mode (eglot-alternatives verilog-ext-lsp-server-binaries))
        eglot-server-programs))

(alist-get 'verilog-mode eglot-server-programs)


;; Some info for the README
;;   - hdl_checker: doesn't seem to support definitions/references or completion. More 'compilation oriented for both VHDL/SystemVerilog
;;     - eglot & lsp: similar results on both, very limited
;;     -  requires .hdl_checker.config file
;;
;;   - svlangserver: Flycheck works, can extract hierarchy
;;     - lsp: good builtin support, built index with lsp command and then navigate only definitions (not references)
;;     - eglot: limited support. Requires somehow adding the command to index code to be able to navigate sources (couldn't make it work)
;;        - Check `eglot-execute-command'
;;        - eglot requires adding some stuff to make it work properly (navigation and completion)
;;
;;   - verible: linting, code formatting and imenu. Hovering gave errors... No navigation find def/ref implemented
;;
;;   - svls: only offers svlint based linting
;;     - requires .svls.toml
;;
;;   - veridian: makes use of verible tools for linting/formatting (similar to verible-ls). Requires veridian.yml file
;;     - hovering, imenu (very weird), (claims it find references but couldn't make it work), syntax/linter doesn't work well with verible-verilog syntax, and completion
;;
;;   - Summary: svlangserver/veridian are prety good because of navigation/linting capabilities,
;;



;;; Apheleia
; TODO: Do a PR to submit formatter: https://github.com/radian-software/apheleia section "Adding a formatter"



;;; Time-stamp (HP)
;; INFO: Implemented as a minor-mode that's working
;; The only thing that is really worth the effort taking a look in here, is the
;; function `verilog-ext-time-stamp-work-new-entry', but in reality is not that important though.
;; Could be useful if default header does not include a "Last Modified" field by default.
;; In reality since VCS track modifications of a file, the only thing that really makes sense is
;; to know when it was last modified, not the whole history of modifications.

(defvar verilog-ext-time-stamp-profiles '("work" "personal"))
(defvar verilog-ext-time-stamp-active-profile "work") ; Defaults to work

(defun verilog-ext-time-stamp-set-profile ()
  "Set active profile for verilog timestamp: work or personal."
  (interactive)
  (let ((profile (completing-read "Set timestamp profile: " verilog-ext-time-stamp-profiles)))
    (setq verilog-ext-time-stamp-active-profile profile)))


(defun verilog-ext-time-stamp-update ()
  "Update `time-stamp' variables depending on current active profile."
  (if (string= verilog-ext-time-stamp-active-profile "work")
      (verilog-ext-time-stamp-work-update) ; Work
    (verilog-ext-time-stamp-pers-update))) ; Personal


;;;;; Work
(defvar verilog-ext-time-stamp-work-boundary-re "\\(?1:[ ]?\\)\\* ------------------------------------------------------------------------------")
(defvar verilog-ext-time-stamp-work-created-re  "\\(?1:^* \\)\\(?2:[a-z]+\\)\\(?3:[ ]+\\)\\(?4:[^ ]+\\)\\(?5:[ ]+\\)\\(?6:Created\\)")
(defvar verilog-ext-time-stamp-work-modified-re "\\(?1:^* \\)\\(?2:[a-z]+\\)\\(?3:[ ]+\\)\\(?4:[^ ]+\\)\\(?5:[ ]+\\)\\(?6:Modified\\)")

(defvar verilog-ext-time-stamp-work-start  (concat "* " user-login-name "  "))
(defvar verilog-ext-time-stamp-work-format "%Y/%m/%d")
(defvar verilog-ext-time-stamp-work-end    "   Modified")


(defun verilog-ext-time-stamp-work-buffer-end-pos ()
  "Return position of point at the end of the buffer timestamp.
Return nil if no timestamp structure was found."
  (save-excursion
    (goto-char (point-min))
    (re-search-forward verilog-ext-time-stamp-work-boundary-re nil t)
    (re-search-forward verilog-ext-time-stamp-work-created-re nil t)
    (re-search-forward verilog-ext-time-stamp-work-boundary-re nil t)))


(defun verilog-ext-time-stamp-work-new-entry ()
  "Create new time-stamp entry at header."
  (interactive)
  (let (initial-blank
        pos)
    (save-excursion
      (setq pos (verilog-ext-time-stamp-work-buffer-end-pos))
      (if pos
          (progn
            (goto-char pos)
            (verilog-ext-time-stamp-work-buffer-end-pos)
            (setq initial-blank (match-string-no-properties 1))
            (beginning-of-line)
            (open-line 1)
            (insert (concat initial-blank verilog-ext-time-stamp-work-start))
            (insert (format-time-string verilog-ext-time-stamp-work-format))
            (insert verilog-ext-time-stamp-work-end))
        (message "Could not find proper time-stamp structure!")))))


(defun verilog-ext-time-stamp-work-update ()
  "Update the 'Modified' entry `time-stamp.'"
  (save-excursion
    (goto-char (point-min))
    (when (verilog-ext-time-stamp-work-buffer-end-pos) ; Activate time-stamp if structure is present
      (setq-local time-stamp-start  verilog-ext-time-stamp-work-start)
      (setq-local time-stamp-format verilog-ext-time-stamp-work-format)
      (setq-local time-stamp-end    verilog-ext-time-stamp-work-end))))





;;; README.md

## Why not inside `verilog-mode` ? ##

One of the reasons is that `verilog-ext` overrides some functionality of `verilog-mode` (e.g. syntax highlighting).
Since not every user of `verilog-mode` would accept some of these changes, `verilog-ext` offers modularity with respect to which functionality to use.

Another reason is that `verilog-ext` only supports GNU Emacs (tested in 28.1) in contrast to `verilog-mode` which also aims to be compatible with XEmacs.
Backwards compatibility with XEmacs would prevent development from using new neat features such as `lsp` or `tree-sitter`.

On the other hand, since the development of `verilog-ext` happens on GitHub, it is not restricted by the FSF contributor agreement and everyone can easily contribute to the project.
Eventually, maintainers of `verilog-mode` could agree on including some `verilog-ext` functionality inside `verilog-mode` for newer Emacs releases.


# WIP/TODO #

## Doc website ##

Use a .org file as an input for GitHub README and HTML doc website.

## Tree-sitter ##

There is some work done with `tree-sitter`. Since Emacs 29 includes it as part of the core, many of the functionalities
here could be replaced and optimized by using `tree-sitter` instead of regexp based search.

## Completion ##

A good `completion-at-point` function would include symbols indexing for a project (e.g. same as `ggtags`). This could
be used by a function of `completion-at-point-functions` to determine contextually what type of completion is needed.


## Hierarchy display ##

Right now hierarchy is shown via `outline-minor-mode` and `outshine`. Other alternatives such as builtin `hierarchy`
or `treemacs` could offer better results.



;;; Tree-sitter
;; TODO:
;;   1 - Check how to highlight ERROR
;;   2 - How to defines macro multiline:
;;     - /home/gonz/Programming/tree-sitter-verilog/grammar.js:170
;;     - optseq('(', $.list_of_actual_arguments, ')')
;;     - Add somehow the \ + \n until there is a newline without \
;;   Seems they are already defined, but it's hard to higlight the text on them

;; Indentation rules

;; Default?
;; (verilog-ts--default-indent parent-bol 4)

;; TODO: Couldn't make it work: /vobs/fpga/cobra/src/paam_if_ext_ic/tb/tc/paam_if_ext_ic_ssw_default_tc.svh
;; ((or (parent-is "(")
;;      (parent-is "{"))
;;  grand-parent 0)

;; TODO: `include compiler directives still don't work inside packages as items?
;; /home/gonz/Programming/FPGA/ucontroller/uvm_tb/uart_agent/uart_agent_pkg.sv


;; Major-mode

;; For treesiter-rules

;; :feature 'error
;; :language 'verilog
;; '(
;;   ;; TODO: Don't really work... Maybe is a thing of treesit Emacs core?
;;   ((ERROR) @font-lock-type-face)
;;   (ERROR
;;    (simple-identifier) @font-lock-type-face)

;;   ;; ;;
;;   )



;; Method qualifiers (virtual/local/protected/pure)
;; (class_method
;;  (method_qualifier) @function.builtin)


;; Some Neovim queries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; User typedefs


;; (package_scope
;;  (package_identifier
;;   (simple_identifier) @constant))

;; (parameter_port_list
;;  "#" @constructor)

;; (modport_identifier
;;  (modport_identifier
;;   (simple_identifier) @field))

;; (net_port_type1
;;  (simple_identifier) @type)


;; (text_macro_identifier
;;  (simple_identifier) @constant)

;; (module_declaration
;;  (module_header
;;   (simple_identifier) @constructor))


;; (parameter_identifier
;;  (simple_identifier) @parameter)


;; (interface_port_declaration
;;  (interface_identifier
;;   (simple_identifier) @type))



;; (function_subroutine_call
;;  (subroutine_call
;;   (tf_call
;;    (simple_identifier) @function)))

;; (function_subroutine_call
;;  (subroutine_call
;;   (system_tf_call
;;    (system_tf_identifier) @function.builtin)))


;; ;;TODO: fixme
;; ;(assignment_pattern_expression
;;  ;(assignment_pattern
;;   ;(parameter_identifier) @field))

;; (type_declaration
;;   (data_type ["packed"] @label))



;; (struct_union_member
;;  (list_of_variable_decl_assignments
;;   (variable_decl_assignment
;;    (simple_identifier) @field)))

;; (member_identifier
;;  (simple_identifier) @field)

;; (struct_union_member
;;  (data_type_or_void
;;   (data_type
;;    (simple_identifier) @type)))


;; TODO: Tests here
;; (simple_identifier
;;  (.match? @constant "after")) @constant


;; ;; Error
;; ;; TODO: Not sure if it's a good idea to highlight this
;; ;; , since not all code is supported:
;; ;;  - e.g.: macros inside ports show as an ERROR
;; ;;  - external function declarations also show as ERROR
;; ;; (ERROR) @error
