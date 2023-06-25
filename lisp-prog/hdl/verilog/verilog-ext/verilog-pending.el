;;; Generic

;;; Completion
;; TODO: Improve dot completion detecting if in a queue/array/enum to show its builtin methods
;; TODO: Improve completion if ` detected (directives candidates)
;; TODO: Add completions for system tasks: https://verificationacademy.com/forums/systemverilog/complete-list-system-functions-or-system-tasks-descriptions
;; TODO: How to do something rudimentary to calculate only tags/references in files that have changed? With hashes as metadata to these files?
;; TODO: Also add some class builtin methods such as randomize()

;;; Tags
;; TODO: Implement multiple definitions with one-line comma sepparation for tags
;; TODO: Possible unit space declarations and externally defined methods
;; TODO: There might be classes also inside modules and packages, frequently in packages!
;; - In those cases, autocompletion should not include attributes and functions inside those clases! Just the class name!
;;   Maybe filtering with (verilog-ext-in-block 'class)?

;;; Flycheck

;;; Compilation
;; For `verilog-ext-makefile-compile' use the custom compile regexp:
; TODO: What to do with this? Something like: if (featurep 'compilation-ext (compilation-ext whatever?))
;; (larumbe/compile cmd nil "verilog-make")

;;; Templates
;; TODO: `verilog-ext-templ-testbench-simple-from-file' fails if instantiates a DUT without parameters
;;;; Hydra
("TE"  (call-interactively #'verilog-ext-templ-testbench-env-from-file)        "TB from DUT file (full env)")


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


;;; Beautify
;; Canceled: Add a function (C-c C-M-i) that aligns declarations of current paragraph
;; Canceled: Add a function (C-c C-M-o) that aligns expressions of current paragraph
;; Problem: paragraphs might not always be blocks of decl/expressions if there are no blank lines in between

;; DANGER: These didn't work because only work if point is at a declaration or at a expression
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



;;; Flycheck
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

;; INFO: About svlint:
;;  - A bit rudimentary, with not many rules but enough to check for parsing errors.
;;  - Could be useful for small RTL self-contained blocks (i.e, almost never).
;;  - Some of its failures didn't have a file line/number and that makes it impossible for flycheck to test them properly


;;; Vhier
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

;;; LSP
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


;;; Inside procedural
(defun verilog-ext-inside-procedural ()
  "Return cons cell with start/end pos if point is inside a procedural block.
If point is inside a begin-end block inside a procedural, return begin-end
positions."
  (save-match-data
    (save-excursion
      (let* ((block-data (verilog-ext-block-at-point))
             (block-type (alist-get 'type block-data))
             (beg-end-data (verilog-ext-point-inside-block-p 'begin-end)))
        (cond (beg-end-data ; If on a begin-end block outside a generate, it will always be procedural
               (unless (string= block-type "generate") ; Relies on `verilog-ext-block-at-point' having higher precedence ...
                 (cons (alist-get 'beg-point beg-end-data) (alist-get 'end-point beg-end-data)))) ; ... for always than for generate
              ;; If outside a begin-end, look for
              ((or (string= block-type "function")
                   (string= block-type "task")
                   (string= block-type "class")
                   (string= block-type "package")
                   (string= block-type "initial")
                   (string= block-type "final")
                   (string= block-type "program"))
               (cons (alist-get 'beg-point block-data) (alist-get 'end-point block-data)))
              ;; Default, not in a procedural block
              (t
               nil))))))

(defun verilog-ext-find-module-instance--legal-p ()
  "Return non-nil if it point position would be legal for an instantiation.
DANGER: Still very inefficient, removed funcall in
`verilog-ext-find-module-instance-fwd'."
  (and (not (verilog-parenthesis-depth))
       (not (verilog-ext-inside-procedural))))


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




