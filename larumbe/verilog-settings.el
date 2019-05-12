;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Verilog/SystemVerilog setup ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Basic settings
(use-package verilog-mode
  :load-path "~/.elisp/larumbe/own-modes/override"
  :mode (("\\.[st]*v[hp]*\\'" . verilog-mode) ;.v, .sv, .svh, .tv, .vp
         ("\\.psl\\'"         . verilog-mode)
         ("\\.vams\\'"        . verilog-mode)
         ("\\.vinc\\'"        . verilog-mode)
         ("\\.vsrc\\'"        . verilog-mode)) ; Custom, for Gigatron vsrc files
  :bind (:map verilog-mode-map
              ("M-f"     . verilog-forward-word)
              ("M-b"     . verilog-backward-word)
              ([delete]  . delete-forward-char)
              ("C-M-n"   . forward-same-indent)
              ("C-M-p"   . backward-same-indent)
              ("C-%"     . hide/show-comments-toggle)
              ("C-M-u"   . larumbe/find-verilog-module-instance-bwd)
              ("C-M-d"   . larumbe/find-verilog-module-instance-fwd)
              ("C-M-h"   . xah-select-current-block)
              ("C-c C-t" . hydra-verilog-template/body)
              ("C-^"     . modi/verilog-jump-to-header-dwim)
              ("C-&"     . modi/verilog-jump-to-header-dwim-fwd))
  :demand ; INFO: Avoid deferring to properly load modi settings
  :init   ; INFO: Requires to be set before loading package in order to variables like faces to take effect
  (setq larumbe/verilog-indent-level 4)

  (setq verilog-indent-level             larumbe/verilog-indent-level)
  (setq verilog-indent-level-module      larumbe/verilog-indent-level)
  (setq verilog-indent-level-declaration larumbe/verilog-indent-level)
  (setq verilog-indent-level-behavioral  larumbe/verilog-indent-level)
  (setq verilog-case-indent              larumbe/verilog-indent-level)
  (setq verilog-indent-level-directive   larumbe/verilog-indent-level)
  (setq verilog-cexp-indent              larumbe/verilog-indent-level)

  (setq verilog-auto-delete-trailing-whitespace t) ; ‘delete-trailing-whitespace’ in ‘verilog-auto’.
  (setq verilog-highlight-grouping-keywords     t) ; begin/end
  (setq verilog-auto-indent-on-newline          t) ; Self-explaining
  (setq verilog-tab-always-indent               t) ; Indent even though we are not at the beginning of line
  (setq verilog-indent-begin-after-if           t)
  (setq verilog-auto-endcomments                t)
  (setq verilog-date-scientific-format          t)

  (setq verilog-indent-lists      nil) ; How to treat indenting items in a list. TODO: Change this to resemble old-style?
  (setq verilog-auto-lineup       nil) ; other options are 'declarations or 'all
  (setq verilog-auto-newline      nil)
  (setq verilog-align-ifelse      nil)
  (setq verilog-tab-to-comment    nil)
  (setq verilog-highlight-modules nil) ; Experimental for highlight-buffer. TODO: Test how this works

  (setq verilog-minimum-comment-distance 10)


  :config
  (bind-chord "\\\\" #'modi/verilog-jump-to-module-at-point verilog-mode-map) ;"\\"
  (when (executable-find "ag")
    (bind-chord "\|\|" #'modi/verilog-find-parent-module verilog-mode-map))
  )


;;; Common settings and hooks
(defun my-verilog-hook ()
  (set 'ac-sources ; Auto-complete verilog-sources
       '(
         ac-source-verilog
         ac-source-gtags
         )
       )

  (setq verilog-library-directories ;; Auto Folder Compute
        '(
          ;; LVDS Training & ICarus Verilog
          "."                       ; current directory
          "../src/"                 ; In case of a _tb within sim directory (Icarus custom sims)
          ))
  (setq verilog-library-files
        '(
          ;; SLLC Project (local path)
          "/home/martigon/Repos/svn/asterix/trunk/projects/metaljf/ip/sllc/rtl/sllc.sv"
          "/home/martigon/Repos/svn/smc/trunk/projects/dogmatix/x02_tsabar/top/tb/asterix_heartbeat/asxmodel/asterix_tsaabar_wrapper.sv"
          "/home/martigon/Repos/svn/metaljf/trunk/ip/btd/rtl/btd.sv"
          ;; IPI-less and bd_block stub
          "/home/martigon/Repos/svn/metaljf/trunk/syn_targets/projects/metaljf/heartbeat/top/engine_top_bd/engine_top_bd.srcs/sources_1/bd/bd_block/hdl/bd_block_wrapper.v"
          "/home/martigon/Repos/svn/metaljf/trunk/syn_targets/projects/metaljf/heartbeat/top/engine_top_bd/engine_top_bd.srcs/sources_1/bd/bd_block/hdl/bd_block_wrapper_stub.v"
          ))

  (modify-syntax-entry ?` ".")     ; TODO: Breaks syntax table anyhow?
  )

;; Verilog Hooks
(add-hook 'verilog-mode-hook 'my-verilog-hook)
(add-hook 'verilog-mode-hook '(lambda () (key-chord-mode 1))) ; Find where modules are instantiated in a project with ag
(add-hook 'verilog-mode-hook 'verilog-set-compile-command) ; Makes f5 be the verilator linter command
(add-hook 'verilog-mode-hook '(lambda () (setq compilation-error-regexp-alist (delete 'gnu compilation-error-regexp-alist))))


;;; Lint, Compilation and Simulation Tools
;;;; Common
(setq verilog-tool 'verilog-linter)
(setq verilog-linter "verilator --lint-only -sv") ; 'compile' default command
;; (setq verilog-coverage "coverage ...)
;; (setq verilog-simulator "verilator ... ")
;; (setq verilog-compiler "verilator ... ")


;;;; Verilator Linter
(defun compile-verilator ()
  (interactive)
  (verilog-set-compile-command) ; Set to verilator linter (current file)
  (compile compile-command)
  (larumbe/verilator-error-regexp-set-emacs))


;;;; Icarus Verilog + GtkWave
(setq iverilog-compile-version "-g2012") ; Other options: -g2005-sv
(setq iverilog-vpi-file "my_vpi.c")      ; VPI Icarus verilog C routines
(setq iverilog-vpi-flags (concat "-m" (file-name-sans-extension (file-name-nondirectory (concat "./" iverilog-vpi-file)))))

(defun file-title()
  "Return file title; eg returns asdf for /otp/asdf.txt ."
  (file-name-sans-extension(file-name-nondirectory (buffer-file-name))))

(defun iverilog-compile-command ()
  "Custom function to get current Icarus Verilog compile command depending on file-title"
  (concat "iverilog " iverilog-compile-version " -gassertions " iverilog-vpi-flags " -o iver/" (file-title) ".compiled -c " (file-title) "_files.txt" " -Wall "))

(defun iverilog-vvp-command ()
  "Custom function to get current Icarus Verilog simulation command depending on file-title"
  (concat "vvp -M. iver/" (file-title) ".compiled -lxt2")) ;add -lxt2 for LXT

(defun iverilog-compile-vpi ()
  "Custom function to compile VPI routines at 'iverilog-vpi-file' variable. It should be at 'sim' folder, as well as testbench source code."
  (interactive)
  (compile (concat "iverilog-vpi " iverilog-vpi-file)))

(defun iverilog-compile ()
  "Pass current verilog file (should be a testbench) to iverilog for compilation.
   NOTE: Files included in testbench must be included in a <tb_top_module>_files.txt
   NOTE2: Assumes this command is called at sim directory, with souces at ../src/<module>.v
   NOTE3: Temp and sim files for iverilog are created at sim/iver/ directory"
  (interactive)
  (if (string-equal (file-name-extension (buffer-file-name)) "v") ; File must be .v
      (if (string-match-p (regexp-quote "_tb") (file-title))
          (progn
            (shell-command "mkdir -p iver")
            (compile (iverilog-compile-command)))
        (message "File must be a TestBench! <file>_tb.v"))
    (message "File isn't .v!")))

(defun iverilog-run-vvp()
  "Run Icarus Verilog simulator engine. Generate dumpfile <top_tb_module>.lxt2 from .compiled extension iverilog previous step file."
  (interactive)
  (if (string-equal (file-name-extension (buffer-file-name)) "v")
      (if (string-match-p (regexp-quote "_tb") (file-title))
          (progn
            (compile (iverilog-vvp-command)))
        (message "File must be a TestBench! <file>_tb.v"))
    (message "File isn't .v!")))

(defun iverilog-update-simulation ()
  "Update simulation for GTKwave refreshing"
  (interactive)
  (if (string-equal (file-name-extension (buffer-file-name)) "v") ; File must be .v
      (if (string-match-p (regexp-quote "_tb") (file-title))
          (save-window-excursion
            (progn
              (shell-command "mkdir -p iver")
              (shell-command (iverilog-compile-command))
              (shell-command (iverilog-vvp-command))
              (shell-command (concat "mv " (file-title) ".lx2 iver/")) ; move to iver/ temp folder
              (message "Simulation updated.")))
        (message "File must be a TestBench! <file>_tb.v"))
    (message "File isn't .v!")))

(defun gtkwave-view-current()
  "Open GTKWAVE on the LXT2 file corresponding to current buffer, with matching save file (if available)."
  (interactive)
  (if (string-equal (file-name-extension (buffer-file-name)) "v")
      (if (string-match-p (regexp-quote "_tb") (file-title))
          (save-window-excursion
            (progn
              (shell-command "mkdir -p iver")
              (shell-command (iverilog-compile-command))
              (shell-command (iverilog-vvp-command))
              (shell-command (concat "mv " (file-title) ".lx2 iver/")) ; move to iver/ temp folder
              (start-process "GtkWave" "*GtkWave*" "gtkwave" (concat "iver/" (file-title) ".lx2") (concat "iver/" (file-title) ".sav"))))
        (message "File must be a TestBench! <file>_tb.v"))
    (message "File isn't .v!")))

(defun iverilog-clean-files()
  "Clean files under the iver/ directory with extensions .compiled and .lxt"
  (interactive)
  (if (string-equal (file-name-extension (buffer-file-name)) "v")
      (if (string-match-p (regexp-quote "_tb") (file-title))
          (shell-command "rm -v iver/*.compiled iver/*.lx2") ; Let .sav files live
        (message "File must be a TestBench! <file>_tb.v"))
    (message "File isn't .v! Open the .v file whose subfiles you wish to clean!")))




;;; Own Verilog templates
;; Should be deprecated by Hydra+YASnippet
;; Customized functions extracted from verilog-mode.el at .elisp/ dir
;;;; Common
(defun verilog-prompt-reset-custom ()
  "Prompt for the name of a state machine reset."
  (setq verilog-reset-custom (read-string "Active Low Reset Name: " "Rst_n")))

(defun verilog-prompt-clock-custom ()
  "Prompt for the name of a clock."
  (setq verilog-clock-custom (read-string "Posedge clock name: " "Clk")))

;;;; Always
(define-skeleton verilog-sk-always-async-custom
  "Insert always async reset block.
Rise Edge active clk and Low Active reset.
Default clk name = clk, Default reset name = reset_n"
  ()
  > "always @ (posedge " '(verilog-prompt-clock-custom) | verilog-clock-custom
  " or negedge " '(verilog-prompt-reset-custom) | verilog-reset-custom ") begin"  (progn (electric-verilog-tab) nil) \n
  > "if (!" verilog-reset-custom ") begin"                                           (progn (electric-verilog-tab) nil) \n
  > _ "// Insert reset statements here"                                                 (progn (electric-verilog-tab) nil) \n
  > "/*AUTORESET*/"                                                                     (progn (electric-verilog-tab) nil) \n
  > "end"                                                                               (progn (electric-verilog-tab) nil) \n
  > "else begin"                                                                        (progn (electric-verilog-tab) nil) \n
  > "// Insert block statements here"                                                   (progn (electric-verilog-tab) nil) \n
  > "end"                                                                               (progn (electric-verilog-tab) nil) \n
  > "end"                                                                               (progn (electric-verilog-tab) nil) \n
  )

;;;; Begin/end block
;; Replace old begin-end from verilog-mode skeleton
(defun verilog-begin-custom ()
  "Insert begin end block.  Uses the minibuffer to prompt for name.
Written as verilog-mode original defun had issues with indentation."
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


;;;; Tasks
(defun verilog-task-add-in (in-read)
  "Add inputs to task template"
  (let (msb lsb)
    (setq msb (read-string "msb: " "31"))
    (setq lsb (read-string "lsb: " "0"))
    (insert (concat "input [" msb ":" lsb "] " in-read ";"))
    (electric-verilog-terminate-line)))

(defun verilog-task-add-out (out-read)
  "Add Outputs to task template"
  (let (msb lsb)
    (setq msb (read-string "msb: " "31"))
    (setq lsb (read-string "lsb: " "0"))
    (insert (concat "output [" msb ":" lsb "] " out-read ";"))
    (electric-verilog-terminate-line)))


;; Custom Task template
(defun verilog-task-custom ()
  "Insert a task definition."
  (interactive)
  (let (in-read out-read)
    (insert (concat "task " (read-string "Task name: ") ";"))   (progn (electric-verilog-terminate-line) nil)
    (while (not(string-equal (setq in-read (read-string "Input: ")) ""))
      (verilog-task-add-in in-read)
      )
    (while (not(string-equal (setq out-read (read-string "Output: ")) ""))
      (verilog-task-add-out out-read)
      )
    (insert (concat "begin"))
    (electric-verilog-terminate-line)
    (save-excursion
      (electric-verilog-terminate-line)
      (insert (concat "end"))                                   (progn (electric-verilog-terminate-line) nil)
      (insert (concat "endtask"))                               (progn (electric-verilog-terminate-line) nil))
    (electric-verilog-tab)))



;;;; Comments
;; Had some issues trying to implement it with skeletons. Finally decided on interactive defun
(defun verilog-add-block-comment ()
  "Custom function. Creates a Verilog comment block. Useful to separate sections within code.
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
           (insert-char 47 2 nil)
           ))
  (electric-verilog-terminate-line)
  ;; Bottom line
  (insert (concat (insert-char 47 (+ verilog-block-comment-width 6) nil)))
  (electric-verilog-terminate-line)
  )


;;;; State Machines
;; Variables used to add parameters on-the-fly
(defvar verilog-fsm-parameter-position nil)

;; 1 parameter keyword per parameter declaration
(defun verilog-state-machine-add-case (param-read)
  "Fills cases within the Next state and output logic and declares them as parameters at the beginning of the FSM "
  (save-excursion
    (goto-char verilog-fsm-parameter-position)
    (electric-verilog-terminate-line)
    (insert (concat "parameter " param-read " = " (read-string "Param value: ") ";"))
    (setq verilog-fsm-parameter-position (point))))


;; Adds a state machine with two always blocks.
(defun verilog-state-machine-async-custom-simple ()
  "Insert a state machine custom definition     .
Two always blocks, one for next state and output logic and one for the state registers"
  (interactive)
  (let (param-read)
    (setq verilog-custom-state (read-string "Name of state variable: " "state"))
    (electric-verilog-tab)              ; Start indentation for comment block
    (insert (concat "// State registers for " verilog-custom-state))                                                                    (progn (electric-verilog-terminate-line) nil)
    (insert (concat "reg [" (read-string "msb: " "31") ":" (read-string "lsb: " "0") "] " verilog-custom-state ", next_" verilog-custom-state ";"))
    (setq verilog-fsm-parameter-position (point))                                                                                       (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " verilog-custom-state))                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " (verilog-prompt-clock-custom) " or negedge " (verilog-prompt-reset-custom) ") begin"))   (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ")"))                                                                               (progn (electric-verilog-terminate-line) nil)
    (insert (concat verilog-custom-state " <= IDLE;"))                                                                                  (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else"))                                                                                                            (progn (electric-verilog-terminate-line) nil)
    (insert (concat  verilog-custom-state " <= next_" verilog-custom-state ";"))                                                        (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; Next state and output logic
    (insert (concat "// Output and next State Logic for " verilog-custom-state))                                                        (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " verilog-clock-custom  " or negedge " verilog-reset-custom  ") begin"))                   (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ") begin"))                                                                         (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= IDLE;"))                                                                          (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output resets..."))                                                                                             (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else begin"))                                                                                                      (progn (electric-verilog-terminate-line) nil)
    (insert (concat "case (" verilog-custom-state ") "))
    ;; Case reading
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (verilog-state-machine-add-case  param-read)                                                                                   (progn (electric-verilog-terminate-line) nil)
      (insert (concat param-read ": begin"))                                                                                            (progn (electric-verilog-terminate-line) nil)
      (insert (concat "// Output statements... "))                                                                                      (progn (electric-verilog-terminate-line) nil)
      (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                     (progn (electric-verilog-terminate-line) nil)
      (insert (concat "end"))                                                                                                           (progn (electric-verilog-terminate-line) nil)
      )
    (insert (concat "endcase"))                                                                                                         (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
    )
  )


;; Only 1 parameter keyword for all parameter declarations (improves readability)
(defun verilog-state-machine-add-case-fold (param-read pfx idx)
  "Fills cases within the Next state and output logic and declares them as parameters at the beginning of the FSM.
Parameter keyword is used only once, improving readability."
  (save-excursion
    (goto-char verilog-fsm-parameter-position)
    (delete-char -1)
    (insert ",")
    (electric-verilog-terminate-line)
    (insert (concat param-read " = " (read-string "Param value: " (concat pfx (number-to-string idx) ";"))))
    (setq verilog-fsm-parameter-position (point))))


;; Returns "4'h." or "1'b." depending on msb and lsb.
(defun verilog-state-machine-get-prefix (msb-str lsb-str)
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
(defun verilog-state-machine-async-custom ()
  "Insert a state machine custom definition     .
Two always blocks, one for next state and output logic and one for the state registers"
  (interactive)
  (let (param-read rst-state-name msb lsb pfx (idx 0))
    (setq verilog-custom-state (read-string "Name of state variable: " "state"))
    (electric-verilog-tab)              ; Start indentation for comment block
    (insert (concat "// State registers for " verilog-custom-state))                                                                                                            (progn (electric-verilog-terminate-line) nil)
    (insert (concat "reg [" (setq msb (read-string "msb: " "3")) ":" (setq lsb (read-string "lsb: " "0")) "] " verilog-custom-state ", next_" verilog-custom-state ";"))        (progn (electric-verilog-terminate-line) nil)
    (setq pfx (verilog-state-machine-get-prefix msb  lsb))
    (insert (concat "parameter " (setq rst-state-name (read-string "Reset State Name: " "IDLE"))  " = " (read-string "Reset Value: " (concat pfx "0;"))))
    (setq verilog-fsm-parameter-position (point))                                                                                                                               (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " verilog-custom-state))                                                                                                                   (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " (verilog-prompt-clock-custom) " or negedge " (verilog-prompt-reset-custom) ") begin"))                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ")"))                                                                                                                       (progn (electric-verilog-terminate-line) nil)
    (insert (concat verilog-custom-state " <= " rst-state-name ";"))                                                                                                            (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else"))                                                                                                                                                    (progn (electric-verilog-terminate-line) nil)
    (insert (concat  verilog-custom-state " <= next_" verilog-custom-state ";"))                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; Next state and output logic
    (insert (concat "// Output and next State Logic for " verilog-custom-state))                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " verilog-clock-custom  " or negedge " verilog-reset-custom  ") begin"))                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ") begin"))                                                                                                                 (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= "rst-state-name ";"))                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output resets..."))                                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else begin"))                                                                                                                                              (progn (electric-verilog-terminate-line) nil)
    (insert (concat "case (" verilog-custom-state ") "))                                                                                                                        (progn (electric-verilog-terminate-line) nil)
    ;; Reset State text insertion
    (insert (concat rst-state-name ": begin"))                                                                                                                                  (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output statements... "))                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                                                               (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    ;; Case reading
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (setq idx (1+ idx))
      (verilog-state-machine-add-case-fold param-read pfx idx)                                                                                                               (progn (electric-verilog-terminate-line) nil)
      (insert (concat param-read ": begin"))                                                                                                                                    (progn (electric-verilog-terminate-line) nil)
      (insert (concat "// Output statements... "))                                                                                                                              (progn (electric-verilog-terminate-line) nil)
      (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
      (insert (concat "end"))                                                                                                                                                   (progn (electric-verilog-terminate-line) nil)
      )
    (insert (concat "endcase"))                                                                                                                                                 (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    )
  )

;;;; Headers
(defun verilog-header-hp ()
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
      (let (string)
        (goto-char start)
        (setq string (read-string "Function: "))
        (search-forward "<function>")
        (replace-match string t t)
        (setq string (read-string "Description: "))
        (search-forward "<description>")
        (replace-match string t t))
      ))
  )

;;;; Testbenches
(defun verilog-insert-testbench-template ()
  "WIP: Just a first sketch to check which AUTOS are needed"
  (interactive)
  (let ((start (point)) (module-name (read-string "Module name: ")))
    (insert "\
module <module_name>_tb (/*AUTOARG*/) ;

    /*AUTOWIRE*/
    /*AUTOREGINPUT*/

    <module_name> <module_name>_DUT(/*AUTOINST*/);

endmodule // <module_name>_tb
")
    (goto-char start)
    (replace-string "<module_name>" module-name)
    (verilog-auto)
    ))


;;; Regexps things (imenu+instance finding)
;; Same as modi's one
(setq larumbe/verilog-identifier-re
      (concat "\\_<\\(?:"
              "\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)" ; simple identifier
              "\\|\\(?:\\\\[!-~]+\\)"           ; escaped identifier
              "\\)\\_>"))

;; "Modi's Regexp modified to match valid Verilog/SystemVerilog module instance declaration."
(setq larumbe/newline-or-space-optional "\\(?:[[:blank:]\n]\\)*")
(setq larumbe/newline-or-space-mandatory "\\(?:[[:blank:]\n]\\)+")
(setq larumbe/param-port-list "([^;]+?)")
(setq larumbe/verilog-module-instance-re
      (concat "^[[:blank:]]*"
              "\\(?1:" larumbe/verilog-identifier-re "\\)" ;module name (subgroup 1)
              larumbe/newline-or-space-optional ; For modi its mandatory, but thats a problem since it could be: btd#(
              ;; optional port parameters
              "\\("
              "#" larumbe/newline-or-space-optional larumbe/param-port-list
              "\\([[:blank:]]*//.*?\\)*"  ;followed by optional comments
              "[^;\\./]+?"  ;followed by 'almost anything' before instance name
              "\\)*"
              "\\(?2:" larumbe/verilog-identifier-re "\\)" ;instance name (subgroup 2)
              ;; Added by Larumbe
              "\\(\\[.*\\]\\)*"         ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
              larumbe/newline-or-space-optional
              "(" ; And finally .. the opening parenthesis `(' before port list
              ;; Added by Larumbe (detect dot (port connection) after instance name parenthesis)
              larumbe/newline-or-space-optional
              ;; "[^;]+?"  ;followed by 'almost anything' before instance name -> This one requires content between brackets (instances only)
              "[^;]*?"  ;followed by 'almost anything' before instance name -> This one does not require contents necessarily between brackets (instances+interfaces)
              ")"
              larumbe/newline-or-space-optional
              ";"
              ))


;; Set imenu patterns (SystemVerilog): https://www.veripool.org/issues/1025-Verilog-mode-Integration-with-the-speedbar
;; This function overrides the value of the variable present in `verilog-mode.el'
;; FIXME: Still does note recognize instances when there are line-comments that end in ; (due to line 608 regexp)
(setq verilog-imenu-generic-expression
      '((nil "^\\s-*\\(?:m\\(?:odule\\|acromodule\\)\\|p\\(?:rimitive\\|rogram\\|ackage\\)\\)\\s-+\\([a-zA-Z0-9_.:]+\\)" 1)
        ("*Vars*" "^\\s-*\\(reg\\|wire\\|logic\\)\\s-+\\(\\|\\[[^]]+\\]\\s-+\\)\\([A-Za-z0-9_]+\\)" 3)
        ("*Classes*" "^\\s-*\\(?:virtual\\s-+\\)?class\\s-+\\([a-zA-Z_0-9]+\\)" 1)
        ("*Tasks*" "^\\s-*\\(?:virtual\\s-+\\)?task\\s-+\\([a-zA-Z_0-9:]+\\)\\s-*[(;]" 1)
        ("*Funct*" "^\\s-*\\(?:virtual\\s-+\\)?function\\s-+\\(?:\\w+\\s-+\\)?\\([a-zA-Z_0-9:]+\\)\\s-*[(;]" 1)
        ("*Interfaces*" "^\\s-*interface\\s-+\\([a-zA-Z_0-9]+\\)" 1)
        ("*Types*" "^\\s-*typedef\\s-+.*\\s-+\\([a-zA-Z_0-9]+\\)\\s-*;" 1)
        ;; Larumbe's shit
        ("*Localparams*" "^\\s-*localparam\\s-+\\([a-zA-Z0-9_.:]+\\)" 1)
        ("*Defines*" "^\\s-*`define\\s-+\\([a-zA-Z0-9_.:]+\\)" 1)
        ("*Assigns*" "^\\s-*assign\\s-+\\([a-zA-Z0-9_.:]+\\)" 1)
        ("*Always blocks*" "^\\s-*always\\(_ff\\|_comb\\|_latch\\)?\\s-*\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)" 4)
        ;; ("*Always blocks*" "^\\s-*always\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)" 3)
        ("*Initial blocks*" "^\\s-*initial\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)" 3)

        ;; Larumbe's instantiations for comment-erased buffer
        ("*Instances/Interfaces*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)*\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(\\(?:[[:blank:]\n]\\)*[^;]*?)\\(?:[[:blank:]\n]\\)*;" 1)
        ;; ("*Instances/Interfaces Names*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)*\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(\\(?:[[:blank:]\n]\\)*[^;]*?)\\(?:[[:blank:]\n]\\)*;" 2)

        ;; DANGER: Unused, just to show what the problems were when dealing with this regexp bullcrap
        ;; Same as next one but including point (problem if comments after connections, but avoids interfaces and keywords)
        ;; ("*Instances*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)*\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(\\(?:[[:blank:]\n]\\)*[\.]" 1)
        ;; Instance including no space between instance name and # when there are parameters
        ;; ("*Instances*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)*\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(" 1)
        ;; Instance without points (problem with keywords and when <name>#() with no space )
        ;; ("*Instances*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)+\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(" 1)
        ;; Instance with point (to avoid keywords, but problems with SV)
        ;; ("*Instances*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)+\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(\\(?:[[:blank:]\n]\\)*[.]" 1)

        ;; Same as next one but including point (problem if comments after connections, but avoids interfaces and keywords)
        ;; ("*Instances Names*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)*\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(\\(?:[[:blank:]\n]\\)*[\.]" 2)
        ;; ("*Instances Names*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)*\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(" 2)
        ;; ("*Instances Names*" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)+\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(" 2)
        ;; ("*Instances Names**" "^[[:blank:]]*\\(?1:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(?:[[:blank:]\n]\\)+\\(#\\(?:[[:blank:]\n]\\)*([^;]+?)\\([[:blank:]]*//.*?\\)*[^;\\./]+?\\)*\\(?2:\\_<\\(?:\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)\\|\\(?:\\\\[!-~]+\\)\\)\\_>\\)\\(\\[.*\\]\\)*\\(?:[[:blank:]\n]\\)*(\\(?:[[:blank:]\n]\\)*[.]" 2)
        ;; End of DANGER
        ))


(defun larumbe/find-verilog-module-instance-fwd ()
  "Test"
  (interactive)
  (setq ignore-comments-flag t)
  (with-comments-hidden
   (point-min)
   (point-max)
   (if (not (re-search-forward larumbe/verilog-module-instance-re nil t))
       (message "No more instances forward")
     t)))

(defun larumbe/find-verilog-module-instance-bwd ()
  "Test"
  (interactive)
  (setq ignore-comments-flag t)
  (with-comments-hidden
   (point-min)
   (point-max)
   (if (not (re-search-backward larumbe/verilog-module-instance-re nil t))
       (message "No more instances backwards")
     t)))


;; INFO: Perl Regexps
;; Convert Perl-Regexp to Elisp Regexp (https://stackoverflow.com/questions/15856154/perl-style-regular-expressions-in-emacs)
;; Use: Detect Verilog instantiations with Regexp from Verilog-Perl instead of modi's
;; Just M-x pcre-query-replace-regexp


;;; Custom Functions
;; Make word navigation commands stop at underscores (withouth destroying verilog-mode syntax highlighting)
;; Fetched from: https://www.veripool.org/issues/724-Verilog-mode-How-to-make-word-navigation-commands-stop-at-underscores-
(defun verilog-forward-word (&optional arg)
  (interactive "p")
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (forward-word arg))))

;; And analogously to previous function (created by Larumbe)
(defun verilog-backward-word (&optional arg)
  (interactive "p")
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-word arg))))

;; https://emacs.stackexchange.com/questions/8032/configure-indentation-logic-to-ignore-certain-lines/8033#8033
(defun my/verilog-selective-indent (&rest args)
  "Return t if the current line starts with '// *'."
  (interactive)
  (let ((match (looking-at "^[[:blank:]]*// \\*")))
    (when match (delete-horizontal-space))
    match))

;; TODO: Ignore outshine comments for indentation, but conflicts? with modi advice?
(advice-add 'verilog-indent-line-relative :before-until #'my/verilog-selective-indent)

;; Select default LFP Gtags/AG/Vhier default project
;; (larumbe/lfp-project-set-active-project)


;; TODO: elisp expresion to copy files from gtags.files to sllc_src scons folder
;; (copy-file (thing-at-point 'filename) "/home/martigon/Repos/svn/smc/trunk/projects/dogmatix/x02_tsabar/top/tb/asxmodel/sllc_src" t)


(defun larumbe/gtags-verilog-files-pwd-recursive ()
  "Generate gtags.files for current directory. Purpose is to be used with dired mode for small projects, to save the regexp"
  (interactive)
  (larumbe/directory-files-recursively-to-file (list default-directory) "gtags.files" ".[s]?v[h]?$")
  )


(defun larumbe/ggtags-create-verilog-tags-recursive ()
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-verilog-files-pwd-recursive)
  (ggtags-create-tags default-directory))


;;; Verilog-Perl hierarchy
;; INFO: First preprocesses input files in a file for `include' and `define' resolution. Then extracts hierarchy from that preprocessed file.
;; Init variables for VHIER Generation to nil
(setq larumbe-verilog-perl-project-path nil)
(setq larumbe-verilog-perl-top-module nil)
(setq larumbe-verilog-perl-project-vhier-path nil)
(setq larumbe-verilog-perl-hier-input-files nil)
(setq larumbe-verilog-perl-hier-file nil)

(setq larumbe-verilog-perl-preprocessed-file nil)
(setq larumbe-verilog-perl-outargs nil)
(setq larumbe-verilog-perl-prep-outargs nil)

;; Projects list
;; Name of the project (+plus)
;; 1) Root path of the project (Just INFO, not used by variables)
;; 2) Name of the top-module
;; 3) Input files for hierarchy elaboration
;; 4) vhier folder path (for generation and further reading)
;; 5) Output hierarchy file path


;; Retrieve VHIER project list and set variables accordingly
(defun larumbe/lfp-project-set-active-project-vhier ()
  (let ((vhier-project)
        (files-list))
    ;; Get Project name
    (setq vhier-project (completing-read "Select project: " (mapcar 'car larumbe-verilog-perl-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc vhier-project larumbe-verilog-perl-projects)))
    ;; Set parameters accordingly
    (setq larumbe-verilog-perl-project-path       (nth 0 files-list))
    (setq larumbe-verilog-perl-top-module         (nth 1 files-list))
    (setq larumbe-verilog-perl-hier-input-files   (nth 2 files-list))
    (setq larumbe-verilog-perl-project-vhier-path (nth 3 files-list))
    (setq larumbe-verilog-perl-hier-file          (nth 4 files-list))

    (setq larumbe-verilog-perl-preprocessed-file
          (concat
           larumbe-verilog-perl-project-vhier-path
           larumbe-verilog-perl-top-module "_pp.sv"))
    (setq larumbe-verilog-perl-outargs
          (concat
           "--cells" " "
           "--no-missing" " "
           "--missing-modules" " "
           "--top-module " larumbe-verilog-perl-top-module " "
           ))
    (setq larumbe-verilog-perl-prep-outargs
          (concat "-o " larumbe-verilog-perl-preprocessed-file))
    ))


;; Has to be done in the file with the relative include path so that it can be found (e.g. sllc_tb.sv)
(defun larumbe/verilog-preprocess-hierarchy-file ()
  "Preproecss hierarchy of top-level module for `includes and `defines'"
  (interactive)
  (let ((processed-files (concat larumbe-verilog-perl-project-vhier-path "tempvhierfiles")))
    (shell-command
     (concat "mkdir -p " larumbe-verilog-perl-project-vhier-path)) ; Create vhier folder if it did not exist
    ;; Replace header `include' files with -y library flag
    (find-file processed-files)
    (with-temp-buffer
      (insert-file-contents larumbe-verilog-perl-hier-input-files)
      (replace-regexp "\\(.*/\\).*\.[s]?vh" "-y \\1" nil (point-min) (point-max))
      (write-file processed-files))
    (shell-command
     (concat "vppreproc "
             "-f " processed-files " "
             larumbe-verilog-perl-prep-outargs
             ))))

(defun larumbe/verilog-process-hierarchy-file ()
  "Process Verilog-Perl file prior to write it to hierarchy.v"
  ;; Process Output to get an outline/outshine accessible view (for use with GTAGS)
  (switch-to-buffer (get-buffer "Verilog-Perl"))
  (save-excursion
    (replace-regexp "  " "*" nil (point-min) (point-max)) ; Replace blank spaces by * for outline
    (replace-regexp "*\\([a-zA-Z0-9_-]\\)" "* \\1" nil (point-min) (point-max)) ; Add blank after asterisks
    ;; Add comments on every line for outshine detection
    (beginning-of-buffer)
    (while (> (point-max) (point))
      (insert "// ")
      (beginning-of-line)
      (forward-line))
    ;; Parse not-used/not-found modules/files
    (beginning-of-buffer)
    (re-search-forward "// \\* ") ; Find top instance
    (when (re-search-forward "// \\* " nil t) ; Find second instance to add a blank line if non-found modules exist
      (beginning-of-line)
      (open-line 2)
      (forward-line)
      (insert "// * Not found files or not present in hierarchy") ; Create level for not found
      (replace-string "// * " "// ** " nil (point) (point-max)))
    ;; Insert header to get some info of the file
    (beginning-of-buffer)
    (open-line 1)
    (insert
     (concat "// This file was created by Larumbe at " (format-time-string "%d-%m-%Y, %H:%M:%S") "\n"
             "// Hierarchy extracted from files included in: " larumbe-verilog-perl-hier-input-files "\n"))))

(defun larumbe/verilog-extract-hierarchy-file ()
  "Extract hierarchy of top-level module using Verilog-Perl backend"
  (interactive)
  (larumbe/lfp-project-set-active-project-vhier)
  (larumbe/verilog-preprocess-hierarchy-file)
  (shell-command
   (concat "vhier "
           larumbe-verilog-perl-outargs
           larumbe-verilog-perl-preprocessed-file)
   "Verilog-Perl")
  (larumbe/verilog-process-hierarchy-file)
  ;; Save-file and enable verilog-mode for tag navigation
  (write-file larumbe-verilog-perl-hier-file)
  (setq buffer-read-only t)
  (vhier-outline-mode)
  (find-alternate-file larumbe-verilog-perl-hier-file)
  )


;;; Modi config
;; Many thanks to Kaushal Modi (https://scripter.co/)
(load "~/.elisp/larumbe/verilog-modi-setup.el")
