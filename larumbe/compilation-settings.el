;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;      COMPILATION-MODE Settings            ;;
;;                                           ;;
;; - Allows for process output parsing     - ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Use-package setup
(use-package compile
  :ensure nil
  :bind (:map compilation-mode-map
              ("r"   . rename-buffer)
              ("j"   . larumbe/recompile-with-regexp-alist)
              ("C-(" . larumbe/show-only-vivado-warnings))
  :bind (:map comint-mode-map
              ("TAB" . completion-at-point)                  ; Similar to ansi-term (e.g. for vivado tcl-shell)
              ("C-j" . larumbe/shell-compilation-recompile)) ; sandbox oriented
  :hook ((compilation-mode . my-compilation-hook))
  :config
  ;; Compilation motion commands skip less important messages. The value can be either
  ;; 2 -- skip anything less than error,
  ;; 1 -- skip anything less than warning or
  ;; 0 -- don't skip any messages.
  (setq compilation-skip-threshold 2) ; Compilation error jumping settings

  (defun my-compilation-hook ()
    (setq truncate-lines t))) ; Do not enable linum-mode since it slows down large compilation buffers


(use-package term
  :bind (:map term-raw-map
              ("M-o" . other-window)
              ("M-x" . helm-M-x)
              ("M->" . end-of-buffer)
              ("M-<" . beginning-of-buffer))
  :config
  (setq comint-process-echoes t))

(defun larumbe/ansi-term ()
  "Checks if there is an existing *ansi-term* buffer and pops to it (if not visible open on the same window).
Otherwise create it"
  (interactive)
  (let ((buf "*ansi-term*"))
    (if (get-buffer buf)
        (if (get-buffer-window buf)
            (pop-to-buffer buf)
          (switch-to-buffer buf))
      (ansi-term "/bin/bash"))))


;;; Compilation-mode related functions
;;;; Filtering
(defun larumbe/show-only-vivado-warnings ()
  "Filter *compilation* buffer to parse only Vivado warnings and critical warnings"
  (interactive)
  (select-window (get-buffer-window "*compilation*"))
  (setq truncate-lines t)
  (beginning-of-buffer)
  (setq inhibit-read-only t)
  (keep-lines "WARNING")
  (setq inhibit-read-only nil)
  (end-of-buffer))

;;;; Resizing/regexp
(defun larumbe/show-custom-compilation-buffers (&optional regexp-alist-alist kill-wins)
  "Show custom compilation buffers.
If first argument is set then provide it wiith custom regexp to parse the compilation buffer.
If second argument is set then delete every other window."
  (interactive)
  (delete-other-windows)
  (unless kill-wins
    (split-window-below)
    (other-window 1))
  (switch-to-buffer "*compilation*")
  (when regexp-alist-alist
    (larumbe/custom-error-regexp-set-emacs regexp-alist-alist))
  (end-of-buffer))


;;; Compilation error regexp alist
;;;; Common
(defvar larumbe/custom-compilation-regexp-sets '("verilog-make" "vivado" "irun" "verilator" "iverilog" "scons" "python"))
(defvar larumbe/custom-compilation-regexp-active nil)


(defun larumbe/recompile-set-active-regexp-alist ()
  "Set current regexp-alist for *compilation* buffer"
  (interactive)
  (setq larumbe/custom-compilation-regexp-active (completing-read "Select compiler: " larumbe/custom-compilation-regexp-sets)))


(defun larumbe/recompile-with-regexp-alist ()
  "Recompile current *compilation* buffer and set proper regexp-alist for different programs"
  (interactive)
  (when (not (bound-and-true-p larumbe/custom-compilation-regexp-active))
    (larumbe/recompile-set-active-regexp-alist))
  (recompile)
  (pcase larumbe/custom-compilation-regexp-active
    ("verilog-make" (larumbe/custom-error-regexp-set-emacs (append iverilog-error-regexp-emacs-alist-alist
                                                                   verilator-error-regexp-emacs-alist-alist
                                                                   vivado-error-regexp-emacs-alist-alist)))
    ("vivado"       (larumbe/vivado-error-regexp-set-emacs))
    ("irun"         (larumbe/irun-error-regexp-set-emacs))
    ("verilator"    (larumbe/verilator-error-regexp-set-emacs))
    ("iverilog"     (larumbe/iverilog-error-regexp-set-emacs))
    ("dc-compiler"  (larumbe/synopsys-dc-error-regexp-set-emacs))
    ("scons"        (larumbe/scons-error-regexp-set-emacs))
    ("python"       (larumbe/python-error-regexp-set-emacs)))
  (end-of-buffer))

;; Master function
(defun larumbe/custom-error-regexp-set-emacs (ce-re-alist-alist)
  "Sets variables `compilation-error-regexp-alist' and `compilation-error-regexp-alist-alist' according to parameter"
  (interactive)
  (when (boundp 'compilation-error-regexp-alist-alist)
    (setq compilation-error-regexp-alist (mapcar 'car ce-re-alist-alist)) ; Fetch first element of list of lists
    (setq compilation-error-regexp-alist-alist ce-re-alist-alist)))


;;;; Vivado
;; Variable to parse regexps with vivado info/warning/errors
(defvar vivado-error-regexp-emacs-alist-alist
      '(
        (vivado-error     "^\\(?1:^ERROR: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"            3   4   nil 2 nil (1 compilation-error-face))
        (vivado-error2    "^\\(?1:^ERROR:\\) "                                                        nil nil nil 2 nil (1 compilation-error-face))
        (vivado-critical  "^\\(?1:^CRITICAL WARNING: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)" 3   4   nil 2 nil (1 compilation-error-face))
        (vivado-critical2 "^\\(?1:^CRITICAL WARNING:\\) "                                             nil nil nil 2 nil (1 compilation-error-face))
        (vivado-warning   "^\\(?1:^WARNING: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"          3   4   nil 1 nil (1 compilation-warning-face))
        (vivado-warning2  "^\\(?1:^WARNING:\\) "                                                      nil nil nil 1 nil (1 compilation-warning-face))
        (vivado-info      "^\\(?1:^INFO: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"             3   4   nil 0 nil (1 compilation-info-face))
        (vivado-info2     "^\\(?1:^INFO:\\) "                                                         nil nil nil 0 nil (1 compilation-info-face))
        ))

(defun larumbe/vivado-error-regexp-set-emacs ()
  "Only takes Vivado Errors regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs vivado-error-regexp-emacs-alist-alist))


;;;; IES
;; Fetched from verilog-mode (verilog-IES: Incisive Enterprise Simulator) and improved to fit Emacs
(defvar irun-error-regexp-emacs-alist-alist
      '(
        (verilog-IES-error   ".*\\(?1:\\*E\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 2 nil (1 compilation-error-face))
        (verilog-IES-warning ".*\\(?1:\\*W\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 1 nil (1 compilation-warning-face))
        (verilog-IES-note    ".*\\(?1:\\*N\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 0 nil (1 compilation-info-face))
        ))

(defun larumbe/irun-error-regexp-set-emacs ()
  "Only takes Cadence IES regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs irun-error-regexp-emacs-alist-alist))



;;;; Verilator
;; Fetched from verilog-mode variable: `verilog-error-regexp-emacs-alist'
(defvar verilator-error-regexp-emacs-alist-alist
      '((verilator-warning "%?\\(Error\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"    3 4 nil 2 nil (1 compilation-error-face) (2 compilation-line-face))
        (verilator-error   "%?\\(Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"  3 4 nil 1 nil (1 compilation-warning-face) (2 compilation-line-face))
        ))

(defun larumbe/verilator-error-regexp-set-emacs ()
  "Takes Verilator regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs verilator-error-regexp-emacs-alist-alist))



;;;; Iverilog
(defvar iverilog-error-regexp-emacs-alist-alist
      '((iverilog-unsupported  "\\(?1:.*\\):\\(?2:[0-9]+\\):.*sorry:"            1 2 nil 0 nil (1 compilation-info-face) (2 compilation-line-face))
        (iverilog-warning      "\\(?1:.*\\):\\(?2:[0-9]+\\):.*warning:"          1 2 nil 1 nil (1 compilation-warning-face) (2 compilation-line-face))
        (iverilog-warning2     "^\\(warning\\):"                                 nil nil nil 1 nil (1 compilation-warning-face))
        (iverilog-error        "\\(?1:.*\\):\\(?2:[0-9]+\\):.*error:"            1 2 nil 2 nil (1 compilation-error-face)   (2 compilation-line-face))
        (vvp-warning           "^\\(?1:WARNING\\): \\(?2:.*\\):\\(?3:[0-9]+\\):" 2 3 nil 1 nil (1 compilation-warning-face) (2 compilation-warning-face) (3 compilation-line-face))
        (vvp-error             "^\\(?1:ERROR\\): \\(?2:.*\\):\\(?3:[0-9]+\\):"   2 3 nil 2 nil (1 compilation-warning-face) (2 compilation-warning-face) (3 compilation-line-face))
        (vvp-info              "^\\(?1:LXT2 info\\):"                            nil nil nil 0 nil (1 compilation-info-face))
        ))

(defun larumbe/iverilog-error-regexp-set-emacs ()
  "Takes Iverilog regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs iverilog-error-regexp-emacs-alist-alist))



;;;; Design compiler
(defvar synopsys-dc-error-regexp-emacs-alist-alist
      '(
        (dc-error     "\\(?1:^Error\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): "       2 3 nil 2 nil (1 compilation-error-face))
        (dc-error-2   "\\(?1:^Error\\): .*"                                                 nil nil nil 2 nil (1 compilation-error-face))
        (dc-warning   "\\(?1:^Warning\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): "     2 3 nil 1 nil (1 compilation-warning-face))
        (dc-warning-2 "\\(?1:^Warning\\): .*"                                               nil nil nil 1 nil (1 compilation-warning-face))
        (dc-info      "\\(?1:^Information\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): " 2 3 nil 0 nil (1 compilation-info-face))
        (dc-info-2    "\\(?1:^Information\\): .*"                                           nil nil nil 0 nil (1 compilation-info-face))
        ))

(defun larumbe/synopsys-dc-error-regexp-set-emacs ()
  "Only takes Synopsys Design Compiler regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs synopsys-dc-error-regexp-emacs-alist-alist))



;;;; Python
(defvar python-error-regexp-emacs-alist-alist
      '(;; Adapted from compilation.el for Python tracebacks
        (python-tracebacks-and-caml "File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)?" 2 (3 . 4) (5 . 6) (7)) ; Some regexps where not detected on some SCons errors (original one did not have `?' at the end)
        (python-log-error   "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:ERROR\\) - "   nil nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
        (python-log-warning "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:WARNING\\) - " nil nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
        (python-log-info    "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:INFO\\) - "    nil nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
        ))


;;;; SCons
(defvar scons-error-regexp-emacs-alist-alist
      '((scons-target-cmd    "\\(?1:^[a-zA-Z_-]+\\)(\\[\"\\(?2:.*\\)\"\\],"   2 nil nil 0 nil (1 compilation-line-face))
        (scons-target-err    "\\(?1:NOK\\)$"                                  1 nil nil 2 nil (1 compilation-error-face))
        (scons-target-cw     "\\(?1:critical warning\\)$"                     1 nil nil 2 nil (1 compilation-warning-face))
        (scons-target-ok     "\\(?1:OK\\)$"                                   1 nil nil 0 nil (1 compilation-info-face))
        ))

(defun larumbe/scons-error-regexp-set-emacs ()
  "Takes Vivado, Irun, SCons and python regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs
   (append
    irun-error-regexp-emacs-alist-alist
    vivado-error-regexp-emacs-alist-alist
    scons-error-regexp-emacs-alist-alist
    python-error-regexp-emacs-alist-alist)))



;;;; Ableton MIDI Remote Scripts Regexps
;; INFO: To be used with: `C-u M-x compile RET tail -f Log.txt'
;; Or just make a wrapper function to set up this debug config
(defvar ableton-error-regexp-emacs-alist-alist
      '(;; Ableton own ones
        (ableton-error      "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptError:\\)"    nil nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
        (ableton-exception  "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:Exception:\\)"            nil nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
        (ableton-message    "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptMessage:\\)"  nil nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
        (ableton-others     "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\)"                                nil nil nil 0 2 (1 compilation-line-face))
        ))

(defun larumbe/ableton-error-regexp-set-emacs ()
  "Takes Ableton and python regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs
   (append
    python-error-regexp-emacs-alist-alist
    ableton-error-regexp-emacs-alist-alist)))



;;; FPGA compilation functions
;;;; Vivado Synthesis
(defvar vivado-batch-project-path nil)
(defvar vivado-batch-project-name nil)
(defvar vivado-batch-compilation-command nil)


(defun larumbe/lfp-compile-vivado-set-active-project ()
  (interactive)
  (let (vivado-project files-list)
    (setq vivado-project (completing-read "Select project: " (mapcar 'car vivado-batch-project-list)))
    (setq files-list (cdr (assoc vivado-project vivado-batch-project-list)))
    (setq vivado-batch-project-path (nth 0 files-list))
    (setq vivado-batch-project-name (nth 1 files-list))
    (setq vivado-batch-compilation-command
          (concat
           "cd " vivado-batch-project-path " && " ; Temp files will be stored in this path
           vivado-binary-path " -mode tcl "
           vivado-batch-project-name
           " -source "
           vivado-batch-script-path))))


(defun larumbe/lfp-compile-vivado-tcl ()
  "Use TCL console to elaborate/compile a design based on previous variables"
  (interactive)
  (larumbe/lfp-compile-vivado-set-active-project)
  (compile vivado-batch-compilation-command)
  (larumbe/show-custom-compilation-buffers vivado-error-regexp-emacs-alist-alist))


;;;; Vivado Simulation (XSim)
;; INFO: It is required to create the simulation first with Vivado GUI, and then run the script
(defvar vivado-sim-project-path nil)

(defun larumbe/lfp-sim-elab-vivado-set-active-project ()
  (interactive)
  (let (vivado-project)
    (setq vivado-project (completing-read "Select project: " (mapcar 'car vivado-sim-project-list)))
    (setq vivado-sim-project-path (cdr (assoc vivado-project vivado-sim-project-list)))
    (setq vivado-sim-compilation-command
          (concat
           "cd " vivado-sim-project-path " && " ; Temp files will be stored in this path
           "source compile.sh && "
           "source elaborate.sh"))))


(defun larumbe/lfp-sim-elab-vivado-tcl (&optional universal-arg)
  "Use TCL console to simulate/elaborate a design based on previous variables"
  (interactive "P")
  (larumbe/lfp-sim-elab-vivado-set-active-project)
  (let (cmd)
    (if universal-arg
        (setq cmd (concat vivado-sim-compilation-command " && source simulate.sh"))
      (setq cmd vivado-sim-compilation-command))
    (compile cmd)
    (larumbe/show-custom-compilation-buffers vivado-error-regexp-emacs-alist-alist)))


;;;; Irun
(defvar larumbe/irun-sources-file       nil)
(defvar larumbe/irun-top-module         nil)
(defvar larumbe/irun-compilation-dir    nil)
(defvar larumbe/irun-opts
      (concat
       "-64bit "
       "-v93 "
       "-relax "
       "-access +rwc "
       "-namemap_mixgen "
       "-clean "
       "-vlog_ext +.vh "
       ))

(defun larumbe/irun-set-active-project ()
  (interactive)
  (let (irun-project files-list)
    (setq irun-project (completing-read "Select project: " (mapcar 'car larumbe/irun-projects)))
    (setq files-list (cdr (assoc irun-project larumbe/irun-projects)))
    (setq larumbe/irun-sources-file    (nth 0 files-list))
    (setq larumbe/irun-top-module      (nth 1 files-list))
    (setq larumbe/irun-compilation-dir (nth 2 files-list))
    (setq larumbe/irun-command
          (concat
           "irun "
           larumbe/irun-opts
           larumbe/irun-vivado-simlib-args
           "-f " larumbe/irun-sources-file " "
           "-top xil_defaultlib." larumbe/irun-top-module " "
           "-top glbl " larumbe/irun-glbl-path))))



(defun larumbe/irun-sim-elab (&optional universal-arg)
  "Simulate a design with `irun' after selecting corresponding project with previous function.
If universal-arg is given, then elaborate the design instead."
  (interactive "P")
  (let (cmd)
    (larumbe/irun-set-active-project)
    (if universal-arg
        (setq cmd (concat larumbe/irun-command " -elaborate"))
      (setq cmd larumbe/irun-command))
    (set (make-local-variable 'compile-command) cmd)
    (compile (concat "cd " larumbe/irun-compilation-dir " && " compile-command))
    (larumbe/show-custom-compilation-buffers irun-error-regexp-emacs-alist-alist)))



;;;; Verilator
;; INFO: Verilator does not support SystemVerilog verification constructs.
;; Therefore, any source with constructs such as a clocking blocks or classes must be deleted from `verilator.files' (copied previously from gtags.file for example)
;; If that is not possible because it is used as a source (e.g. a SystemVerilog interface with a clocking block), then tweak/comment temporarily files by hand.
;;
;; INFO: This is useful while developing small IPs
(defvar verilator-compile-lint-files nil)
(defvar verilator-compile-lint-top   nil)
(defvar verilator-compile-lint-cmd   nil)

(defun larumbe/verilator-lint-set-active-project ()
  (interactive)
  (let (verilator-project)
    (setq verilator-project (completing-read "Select project: " (mapcar 'car verilator-project-list)))
    (setq verilator-compile-lint-files (nth 0 (cdr (assoc verilator-project verilator-project-list))))
    (setq verilator-compile-lint-top   (nth 1 (cdr (assoc verilator-project verilator-project-list))))
    (setq verilator-compile-lint-cmd
          (concat "verilator --lint-only +1800-2012ext+sv -f "
                  verilator-compile-lint-files " "
                  "--top-module " verilator-compile-lint-top))))

(defun larumbe/compile-verilator-lint ()
  "Files created with ggtags and renamed (useful for small projects).
It's faster than Vivado elaboration since it does not elaborate design"
  (interactive)
  (larumbe/verilator-lint-set-active-project)
  (setq compile-command verilator-compile-lint-cmd)
  (compile compile-command)
  (larumbe/show-custom-compilation-buffers verilator-error-regexp-emacs-alist-alist))


;;;; Reggen
;; Projects list
;; Name of the project (+plus)
;; 1) Name of project/IP
;; 2) Path to the RDL definition
;; 3) Name of address map
;; 4) Output directory

(defvar larumbe-reggen-template-types
      '("c_header"
        "docbook"
        "verilog_header"
        "verilog_defspkg"
        "verilog_regcomponent_simple"
        "verilog_regcomponent_regbusitf"
        "verilog_regcomponent_axilite"))

(defun larumbe/reggen-set-active-project ()
  (interactive)
  (let (reggen files-list)
    ;; Get Project name
    (if (bound-and-true-p larumbe-reggen-input-file)
        (setq reggen (completing-read "Select project: " (mapcar 'car larumbe-reggen-projects)))
      (progn
        (setq reggen (car (car larumbe-reggen-projects)))))  ; If no project is defined, use default (first one)
    (setq files-list (cdr (assoc reggen larumbe-reggen-projects)))
    ;; Set parameters accordingly
    (setq larumbe-reggen-input-file       (nth 0 files-list))
    (setq larumbe-reggen-address-map-name (nth 1 files-list))
    (setq larumbe-reggen-output-path      (nth 2 files-list))))


(defun larumbe/reggen ()
  "Generate Reggen Outputs according to global variables (depending on hp/cee)"
  (interactive)
  (let ((larumbe-reggen-command)
        (larumbe-reggen-output-file)
        (larumbe-reggen-output-filename)
        (larumbe-reggen-template))
    (larumbe/reggen-set-active-project)
    ;; Check which type of output has to be generated
    (setq larumbe-reggen-template (completing-read "Select template: " larumbe-reggen-template-types))
    ;; Set output filename extension
    (pcase larumbe-reggen-template
      ("c_header"
       (setq larumbe-reggen-output-filename (concat larumbe-reggen-address-map-name ".h")))
      ("docbook"
       (setq larumbe-reggen-output-filename (concat larumbe-reggen-address-map-name ".xml")))
      ("verilog_header"
       (setq larumbe-reggen-output-filename (concat larumbe-reggen-address-map-name ".vh")))
      ("verilog_regcomponent_simple"
       (setq larumbe-reggen-output-filename (concat larumbe-reggen-address-map-name ".sv")))
      ("verilog_regcomponent_regbusitf"
       (setq larumbe-reggen-output-filename (concat larumbe-reggen-address-map-name "_regbus.sv")))
      ("verilog_regcomponent_axilite"
       (setq larumbe-reggen-output-filename (concat larumbe-reggen-address-map-name "_axi.sv")))
      ("verilog_defspkg"
       (setq larumbe-reggen-output-filename (concat larumbe-reggen-address-map-name "_defs_pkg.sv"))))
    ;; Set output filename
    (setq larumbe-reggen-output-file
          (concat larumbe-reggen-output-path "/" larumbe-reggen-output-filename))
    ;; Set compilation command
    (setq larumbe-reggen-command
          (concat
           larumbe-reggen-tool-path " "
           "-i " larumbe-reggen-input-file " "
           "-o " larumbe-reggen-output-file " "
           "-t " larumbe-reggen-template " "
           "-a " larumbe-reggen-address-map-name " "
           "-m " "full "
           "-v" ; Verbose
           ))
    ;; Compile
    (compile larumbe-reggen-command)))



;;; Compilation interactive with regexp
(defun larumbe/shell-compilation-regexp-interactive (command bufname re-func)
  "Creates a `compilation-mode' comint shell that allows having an identical
shell as an *ansi-term*, regarding environment and aliases without the need of setting
`shell-command-switch' to '-ic'.
Useful to spawn a *tcl-shell* with Vivado regexps, or to init sandbox modules."
  (when (get-buffer bufname)
    (pop-to-buffer bufname)
    (error (concat "Buffer " bufname " already in use!")))
  (compile command t)
  (select-window (get-buffer-window "*compilation*"))
  (end-of-buffer)
  (setq truncate-lines t)
  (funcall re-func)
  (rename-buffer bufname))


;;;; Sandboxes
(defun larumbe/shell-compilation-sandbox (initcmd buildcmd bufname re-func)
  "Initialize a bash sandbox and execute build command.
Basically a wrapper for `larumbe/shell-compilation-regexp-interactive' with an additional build command."
  (let ((command initcmd)
        (proc))
    (larumbe/shell-compilation-regexp-interactive command bufname re-func)
    (setq-local larumbe/shell-compilation-sandbox-buildcmd buildcmd)
    (setq proc (get-buffer-process bufname))
    (comint-send-string proc buildcmd)
    (comint-send-string proc "\n")))


(defun larumbe/shell-compilation-recompile ()
  "Will only work in comint mode for previous functions.
Makes use of local variable `larumbe/shell-compilation-sandbox-buildcmd' to rebuild a target."
  (interactive)
  (when (string= major-mode "comint-mode")
    (setq proc (get-buffer-process (current-buffer)))
    (comint-send-string proc larumbe/shell-compilation-sandbox-buildcmd)
    (comint-send-string proc "\n")))
