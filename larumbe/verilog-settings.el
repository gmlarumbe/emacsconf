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
              ("C-c l"   . larumbe/verilog-insert-instance-from-file)
              ("C-c i"   . larumbe/verilog-indent-current-module)
              ("C-c a"   . larumbe/verilog-align-ports-current-module)
              ("C-c C-l" . larumbe/verilog-align-parameters-current-module)
              ("C-c b"   . larumbe/verilog-beautify-current-module)
              ("C-c c"   . larumbe/verilog-toggle-connect-port)
              ("C-c C-c" . larumbe/verilog-connect-ports-recursively)
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
  (setq verilog-case-fold                       nil) ; Regexps should NOT ignore case

  (setq verilog-indent-lists      t)   ; If set to nil, indentation will not properly detect we are inside a parenthesized expression (instance or ports/parameters)
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
          ;; "/home/martigon/Repos/lfp_GitHub/git_metaljf/metaljf/top/rtl/metaljf_debug.sv"
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
(setq verilog-linter "verilator --lint-only +1800-2012ext+sv") ; 'compile' default command
;; (setq verilog-coverage "coverage ...)
;; (setq verilog-simulator "verilator ... ")
;; (setq verilog-compiler "verilator ... ")


;;;; Verilator Linter
(defun larumbe/compile-verilator ()
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
  (if (string-match "[s]?v[h]?$" (file-name-extension (buffer-file-name))) ; File must be Verilog/SystemVerilog
      (if (string-match-p (regexp-quote "tb") (file-title))
          (progn
            (shell-command "mkdir -p iver")
            (compile (iverilog-compile-command)))
        (message "File must be a TestBench! <file>_tb.v / tb_<file>.sv"))
    (message "File isn't .v/.sv!")))

(defun iverilog-run-vvp()
  "Run Icarus Verilog simulator engine. Generate dumpfile <top_tb_module>.lxt2 from .compiled extension iverilog previous step file."
  (interactive)
  (if (string-match "[s]?v[h]?$" (file-name-extension (buffer-file-name))) ; File must be Verilog/SystemVerilog
      (if (string-match-p (regexp-quote "_tb") (file-title))
          (progn
            (compile (iverilog-vvp-command)))
        (message "File must be a TestBench! <file>_tb.v"))
    (message "File isn't .v!")))

(defun iverilog-update-simulation ()
  "Update simulation for GTKwave refreshing"
  (interactive)
  (if (string-match "[s]?v[h]?$" (file-name-extension (buffer-file-name))) ; File must be Verilog/SystemVerilog
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


;;;; Comments
;; Had some issues trying to implement it with skeletons. Finally decided on interactive defun
(defun larumbe/verilog-add-block-comment ()
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
(defvar larumbe/verilog-fsm-parameter-position nil)

;; 1 parameter keyword per parameter declaration
(defun larumbe/verilog-state-machine-add-case (param-read)
  "Fills cases within the Next state and output logic and declares them as parameters at the beginning of the FSM "
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
    (insert (concat "// State registers for " verilog-custom-state))                                                                    (progn (electric-verilog-terminate-line) nil)
    (insert (concat "reg [" (read-string "msb: " "31") ":" (read-string "lsb: " "0") "] " verilog-custom-state ", next_" verilog-custom-state ";"))
    (setq larumbe/verilog-fsm-parameter-position (point))                                                                                       (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " verilog-custom-state))                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " (larumbe/verilog-prompt-clock-custom) " or negedge " (larumbe/verilog-prompt-reset-custom) ") begin"))   (progn (electric-verilog-terminate-line) nil)
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
      (larumbe/verilog-state-machine-add-case  param-read)                                                                                   (progn (electric-verilog-terminate-line) nil)
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
  (let (beg end)
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
  (let (beg end)
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
TODO: In the future, a list that returns modules in a file could be retrieved and used as an input"
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
    (call-interactively 'larumbe/verilog-header-hp)
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
  (let (in-read out-read)
    (insert "task ")
    (insert (read-string "Task name: ") " (")
    (electric-verilog-terminate-line)
    (while (not(string-equal (setq in-read (read-string "Input signal: ")) ""))
      (larumbe/verilog-task-add-port "input" in-read))
    (while (not(string-equal (setq out-read (read-string "Output signal: ")) ""))
      (larumbe/verilog-task-add-port "output" out-read))
    ;; TODO: "inout" or "ref" could be added in the future via universal-arg
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


(defun larumbe/verilog-indent-current-module (&optional module)
  "Indent current module, the one pointed to by `which-func' (not instant)

For use programatically, an argument needs to be specified as current-module is determined by `which-func' and that takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let (current-module)
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (re-search-backward (concat "\\_<" current-module "\\_>"))
      (beginning-of-line) ; INFO: Needed to detect current instantiation and avoid the "No more instances forward" error message
      (set-mark (point))
      (larumbe/find-verilog-module-instance-fwd)
      (electric-verilog-tab))))


(defun larumbe/verilog-align-parameters-current-module (&optional module)
  "Align parenthesis PARAMETERS of current module, the one pointed to by `which-func' (not instant).
It will align parameters contained between module name and instance name.

For use programatically, an argument needs to be specified as current-module is determined by `which-func' and that takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let (current-module current-instance beg end)
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (re-search-backward (concat "\\_<" current-module "\\_>"))
      (next-line 1) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward current-instance)))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Parameters aligned...")))


(defun larumbe/verilog-align-ports-current-module ()
  "Align parenthesis PORTS of current module, the one pointed to by `modi/verilog-find-module-instance'
It will only align ports, i.e., between instance name and end of instantiation."
  (interactive)
  (let (current-instance beg end)
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (save-excursion
      (re-search-backward (concat "\\_<" current-instance "\\_>"))
      (next-line 1) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward ");")))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Ports aligned...")))


(defun larumbe/verilog-beautify-current-module ()
  "Beautify current module (open parenthesis +indent + align)"
  (interactive)
  (save-excursion
    (larumbe/verilog-indent-current-module)
    (larumbe/verilog-align-ports-current-module)
    (larumbe/verilog-align-parameters-current-module)))


(defvar larumbe/connect-disconnect-port-re "\\.\\(?1:[a-zA-Z0-9_-]+\\)\\(?2:[[:blank:]]*\\)")
(defvar larumbe/connect-disconnect-conn-re "(\\(?3:.*\\))")
(defvar larumbe/connect-disconnect-not-found "No port detected at current line")

(defun larumbe/verilog-toggle-connect-port (force-connect)
  "Connect/disconnect port @ current line (regexp based).
If regexp detects that port is connected, then disconnect it. The other way round works the same.
If called with universal arg, `force-connect' parameter will force connection of current port, no matter it is connected/disconnected"
  (interactive "P")
  (let* ((port-regex larumbe/connect-disconnect-port-re)
         (conn-regex larumbe/connect-disconnect-conn-re)
         (line-regex (concat port-regex conn-regex))
         port conn sig
         (start (point)))
    ;; Find '.port (conn)' verilog regexp
    (beginning-of-line)
    (if (re-search-forward line-regex (point-at-eol) t)
        (progn
          (setq port (substring-no-properties (match-string 1)))
          (setq conn (substring-no-properties (match-string 3)))
          (if (or (string-equal conn "") force-connect) ; If it is disconnected or connection is forced via parameter...
              (progn ; Connect
                (setq sig (read-string (concat "Connect [" port "] to: ") conn))
                (replace-match (concat ".\\1\\2\(" sig "\)") t))
            (progn ; Else disconnect
              (replace-match (concat ".\\1\\2()") t)))
          (goto-char start)
          (next-line 1))
      (progn ; No port found
        (goto-char start)
        (message larumbe/connect-disconnect-not-found)))))


(defun larumbe/verilog-connect-ports-recursively ()
  "Ask recursively for ports to be connected until no port is found at current line"
  (interactive)
  (while (not (string-equal (larumbe/verilog-toggle-connect-port t) larumbe/connect-disconnect-not-found))))




(defun larumbe/verilog-def-logic (sig)
  "Replaces `verilog-sk-def-reg' for use within `larumbe/verilog-define-signal'"
  (let (width str)
    (split-line) ;; Keep indentation
    (setq width (larumbe/verilog-compute-vector-width))
    (setq str (concat "logic " width " " sig ";"))
    (insert str)
    (message (concat "[Line " (format "%s" (line-number-at-pos)) "]: " str))))


(defun larumbe/verilog-define-signal ()
  "INFO: Copied/modified from `verilog-mode.el' function: `verilog-sk-define-signal'.
There were some issues with this skeleton, an a function offers more flexibility.

Insert a definition of signal under point at top of module."
  (interactive "*")
  (let* ((sig-re "[a-zA-Z0-9_]*")
         (sig (buffer-substring
               (save-excursion
                 (skip-chars-backward sig-re)
                 (point))
               (save-excursion
                 (skip-chars-forward sig-re)
                 (point)))))
    (if (not (member sig verilog-keywords))
        (save-excursion
          (verilog-beg-of-defun)
          (verilog-end-of-statement)
          (verilog-forward-syntactic-ws)
          (larumbe/verilog-def-logic sig))
      (message "object at point (%s) is a keyword" sig))))



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


;; Recorded with elmacro, and used to remove spaces on verilog instances (still in test)
;; First, searches for (.*) and then removes blank spaces.
;; Still needs to be called inside an instantiation and later aligned with previous regexp
(defun larumbe/verilog-remove-spaces-parenthesis ()
  (interactive)
  (hide/show-comments-toggle (point-min) (point-max))
  (isearch-forward-regexp nil 1)
  (isearch-printing-char 40 1)
  (isearch-printing-char 46 1)
  (isearch-printing-char 42 1)
  (isearch-printing-char 41 1)
  (isearch-exit)
  (electric-verilog-backward-sexp)
  (forward-char 1)
  (delete-horizontal-space nil)
  (backward-char 1)
  (electric-verilog-forward-sexp)
  (backward-char 1)
  (delete-horizontal-space nil)
  (hide/show-comments-toggle (point-min) (point-max))
  )


;; TODO Create a function that fixes comments ending in ; at instantiations
;; This avoid proper detection of instatiations for imenu
;; To fix, use the following command regexp based
;; (query-replace-regexp "//\(.*\); -> /\1")



;;; Verilog-Perl hierarchy
;; INFO: First preprocesses input files in a file for `include' and `define' resolution. Then extracts hierarchy from that preprocessed file.
;; Init variables for VHIER Generation to nil
(setq larumbe-verilog-perl-top-module nil)
(setq larumbe-verilog-perl-project-vhier-path nil)
(setq larumbe-verilog-perl-hier-input-files nil)
(setq larumbe-verilog-perl-hier-file nil)

(setq larumbe-verilog-perl-preprocessed-file nil)
(setq larumbe-verilog-perl-outargs nil)
(setq larumbe-verilog-perl-prep-outargs nil)

;; Projects list
;; Name of the project (+plus)
;; 1) Name of the top-module
;; 2) Input files for hierarchy elaboration
;; 3) vhier folder path (for generation and further reading)
;; 4) Output hierarchy file path


;; Retrieve VHIER project list and set variables accordingly
(defun larumbe/lfp-project-set-active-project-vhier ()
  (let ((vhier-project)
        (files-list))
    ;; Get Project name
    (setq vhier-project (completing-read "Select project: " (mapcar 'car larumbe-verilog-perl-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc vhier-project larumbe-verilog-perl-projects)))
    ;; Set parameters accordingly
    (setq larumbe-verilog-perl-top-module         (nth 0 files-list))
    (setq larumbe-verilog-perl-hier-input-files   (nth 1 files-list))
    (setq larumbe-verilog-perl-project-vhier-path (nth 2 files-list))
    (setq larumbe-verilog-perl-hier-file          (nth 3 files-list))

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
  "Preprocess hierarchy of top-level module for `includes and `defines'"
  (interactive)
  (let ((processed-files (concat larumbe-verilog-perl-project-vhier-path "vhier.files"))
        (sorted-files-p nil) ; Used inside while loop to decide when every `defs_pkg' has been put at the beginning
        )
    (shell-command
     (concat "mkdir -p " larumbe-verilog-perl-project-vhier-path)) ; Create vhier folder if it did not exist
    (with-temp-buffer
      ;; (view-buffer-other-window (current-buffer))      ; INFO: Debug for `with-temp-buffer'
      ;; (clone-indirect-buffer-other-window "*debug*" t) ; INFO: Debug for `with-temp-buffer'
      (insert-file-contents larumbe-verilog-perl-hier-input-files)
      (replace-regexp "\\(.*/\\).*\.[s]?vh$" "-y \\1" nil (point-min) (point-max)) ; Replace header `include' files with -y library flag
      (larumbe/sort-regexp-at-the-beginning-of-file "_defs_pkg.sv") ;; Move every _defs_pkg.sv at the beginning
      (write-file processed-files))
    ;; Eecute preprocess command
    (shell-command
     (concat "vppreproc "
             "-f " processed-files " "
             larumbe-verilog-perl-prep-outargs))))


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
  (vhier-outline-mode)
  (setq buffer-read-only t))


;;; Modi config
;; Many thanks to Kaushal Modi (https://scripter.co/)
(load "~/.elisp/larumbe/verilog-modi-setup.el")
