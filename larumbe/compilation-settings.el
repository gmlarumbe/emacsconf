;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;      COMPILATION-MODE Settings            ;;
;;                                           ;;
;; - Allows for process output parsing     - ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Variable settings
(setq compilation-skip-threshold 2) ; Compilation error jumping settings
    ;; Compilation motion commands skip less important messages. The value can be either
    ;; 2 -- skip anything less than error,
    ;; 1 -- skip anything less than warning or
    ;; 0 -- don't skip any messages.


;;; Hooks
;; INFO: Do not enable linum-mode since it slows down large compilation buffers
(defun my-compilation-hook ()
  (setq truncate-lines t)
  )
(add-hook 'compilation-mode-hook 'my-compilation-hook)
(define-key compilation-mode-map (kbd "r") 'rename-buffer)
(define-key compilation-mode-map (kbd "j") 'larumbe/recompile-with-regexp-alist)
(define-key compilation-mode-map (kbd "C-(") 'larumbe/show-only-vivado-warnings)

;;; Compilation-mode related functions
;;;; Filtering
(defun larumbe/show-only-vivado-warnings ()
  "Filter *compilation* buffer to parse only Vivado warnings and critical warnings"
  (interactive)
  (select-window (get-buffer-window "*compilation*")) ; Select compilation buffer
  (setq truncate-lines t)
  (beginning-of-buffer)
  (setq inhibit-read-only t)
  (keep-lines "WARNING")
  (setq inhibit-read-only nil)
  (end-of-buffer))

;;;; Resizing/regexp
(defun show-custom-compilation-buffers()
  (interactive)
  (delete-other-windows)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*compilation*")
  (end-of-buffer)
  (shrink-window 18)
  )

(defun show-custom-compilation-buffers-vivado()
  (interactive)
  (delete-other-windows)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*compilation*")
  (larumbe/vivado-error-regexp-set-emacs) ; Sets compilation-error-regexp-alist-alist temporarily for the current compilation buffer
  (end-of-buffer)
  (shrink-window 10)
  )

(defun show-custom-compilation-buffers-verilator()
  (interactive)
  (delete-other-windows)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*compilation*")
  (larumbe/verilator-error-regexp-set-emacs) ; Sets compilation-error-regexp-alist-alist temporarily for the current compilation buffer
  (end-of-buffer)
  (shrink-window 10)
  )


;;; Compilation error regexp alist
;;;; Common
(setq larumbe/custom-compilation-regexp-sets '("vivado" "irun" "scons" "verilator")) ; Used for custom recompile (edited by hand)
(setq larumbe/custom-compilation-regexp-active nil)                                  ; Current active compilation regexp

;; Recompiling with regexp (active profile needs to be modified manually once set... this should be changed somehow in the future)
(defun larumbe/recompile-set-active-regexp-alist ()
  "Set current regexp-alist for *compilation* buffer"
  (interactive)
  (setq larumbe/custom-compilation-regexp-active (completing-read "Select compiler: " larumbe/custom-compilation-regexp-sets))
  )
(defun larumbe/recompile-with-regexp-alist ()
  "Recompile current *compilation* buffer and set proper regexp-alist for different programs"
  (interactive)
  (when (not (bound-and-true-p larumbe/custom-compilation-regexp-active))
    (larumbe/recompile-set-active-regexp-alist))
  (recompile)
  (pcase larumbe/custom-compilation-regexp-active
    ("vivado"
     (larumbe/vivado-error-regexp-set-emacs))
    ("irun"
     (larumbe/irun-error-regexp-set-emacs))
    ("scons"
     (larumbe/scons-error-regexp-set-emacs))
    ("verilator"
     (larumbe/verilator-error-regexp-set-emacs))
    )
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
(setq vivado-error-regexp-emacs-alist-alist
      '(
        (vivado-error    "^\\(ERROR\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"            3 4 nil 2 nil (1 compilation-error-face))
        (vivado-critical "^\\(CRITICAL WARNING\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*" 3 4 nil 2 nil (1 compilation-error-face))
        (vivado-warning  "^\\(WARNING\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"          3 4 nil 1 nil (1 compilation-warning-face))
        (vivado-info     "^\\(INFO\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"             3 4 nil 0 nil (1 compilation-info-face))
        )
      )

(defun larumbe/vivado-error-regexp-set-emacs ()
  "Only takes Vivado Errors regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs vivado-error-regexp-emacs-alist-alist))


;;;; Cadence Incisive (irun)
;; Fetched from verilog-mode (verilog-IES: Incisive Enterprise Simulator) and improved to fit Emacs
(setq irun-error-regexp-emacs-alist-alist
      '(
        (verilog-IES-error   ".*\\(?1:\\*E\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 2 nil (1 compilation-error-face))
        (verilog-IES-warning ".*\\(?1:\\*W\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 1 nil (1 compilation-warning-face))
        )
      )
(defun larumbe/irun-error-regexp-set-emacs ()
  "Only takes Cadence IES regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs irun-error-regexp-emacs-alist-alist))


;;;; SCons
;; Irun + Vivado + SCons targets + Python
(setq scons-error-regexp-emacs-alist-alist
      '(
        (verilog-IES-error   ".*\\(?1:\\*E\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 2 nil (1 compilation-error-face))
        (verilog-IES-warning ".*\\(?1:\\*W\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 1 nil (1 compilation-warning-face))
        (vivado-error        "^\\(ERROR\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"            3 4 nil 2 nil (1 compilation-error-face))
        (vivado-critical     "^\\(CRITICAL WARNING\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*" 3 4 nil 2 nil (1 compilation-error-face))
        (vivado-warning      "^\\(WARNING\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"          3 4 nil 1 nil (1 compilation-warning-face))
        (vivado-info         "^\\(INFO\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"             3 4 nil 0 nil (1 compilation-info-face))
        ;; (scons-target-cmd    "\\(?1:^[a-zA-Z_-]+\\)(\\[\"\\(?2:.*\\)\"\\],"   2 nil nil 0 nil (1 compilation-info-face))
        (scons-target-cmd    "\\(?1:^[a-zA-Z_-]+\\)(\\[\"\\(?2:.*\\)\"\\],"   2 nil nil 0 nil (1 compilation-line-face))
        (scons-target-err    "\\(?1:NOK\\)$"                                  1 nil nil 2 nil (1 compilation-error-face))
        (scons-target-cw     "\\(?1:critical warning\\)$"                     1 nil nil 2 nil (1 compilation-warning-face))
        (scons-target-ok     "\\(?1:OK\\)$"                                   1 nil nil 0 nil (1 compilation-info-face))
        ;; Adapted from compilation.el for Python tracebacks
        (python-tracebacks-and-caml "File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)?" 2 (3 . 4) (5 . 6) (7)) ; Some regexps where not detected on some SCons errors
        ;; (python-tracebacks-and-caml "^[ \t]*File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)" 2 (3 . 4) (5 . 6) (7)) ;; Original one, without the ? at the end
        ;; Python Logs (fetched from Ableton)
        (python-log-error   "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:ERROR\\) - "   nil nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
        (python-log-warning "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:WARNING\\) - " nil nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
        (python-log-info    "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:INFO\\) - "    nil nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
        )
      )

(defun larumbe/scons-error-regexp-set-emacs ()
  "Takes Vivado, Irun, SCons and python regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs scons-error-regexp-emacs-alist-alist))


;;;; Verilator
;; Fetched from: /home/martigon/.elisp/verilog-mode.el:902
(setq verilator-error-regexp-emacs-alist-alist
      '((verilator-warning "%?\\(Error\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"    3 4 nil 2 nil (1 compilation-error-face) (2 compilation-line-face))
        (verilator-error   "%?\\(Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"  3 4 nil 1 nil (1 compilation-warning-face) (2 compilation-line-face)))
      )

(defun larumbe/verilator-error-regexp-set-emacs ()
  "Takes Verilator regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs verilator-error-regexp-emacs-alist-alist))




;;;; Ableton MIDI Remote Scripts Regexps
;; INFO: To be used with: `C-u M-x compile RET tail -f Log.txt'
;; Or just make a wrapper function to set up this debug config
(setq ableton-error-regexp-emacs-alist-alist
      '(
        ;; Taken from scons functions present back in the file
        (python-tracebacks-and-caml "File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)?" 2 (3 . 4) (5 . 6) (7)) ; Some regexps where not detected on some SCons errors
        ;; Ableton own ones, extend as desired
        (ableton-error      "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptError:\\)"    nil nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
        (ableton-exception  "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:Exception:\\)"            nil nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
        (ableton-message    "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptMessage:\\)"  nil nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
        (ableton-others     "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\)"                                nil nil nil 0 2 (1 compilation-line-face))
        )
      )

(defun larumbe/ableton-error-regexp-set-emacs ()
  "Takes Ableton and python regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs ableton-error-regexp-emacs-alist-alist))



;;; FPGA compilation functions
;;;; Vivado Synthesis
(setq vivado-batch-project-path nil)
(setq vivado-batch-project-name nil)
(setq vivado-batch-compilation-command nil)


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
  (show-custom-compilation-buffers-vivado) ; Takes into account vivado regexps
  )


;;;; Vivado Simulation (XSim)
;; INFO: It is required to create the simulation first with Vivado GUI, and then run the script
(setq vivado-sim-project-path nil)

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
    (show-custom-compilation-buffers-vivado)))


;;;; Irun
(setq larumbe/irun-sources-file       nil)
(setq larumbe/irun-top-module         nil)
(setq larumbe/irun-compilation-dir    nil)
(setq larumbe/irun-opts
      (concat
       "-64bit "
       "-v93 "
       "-relax "
       "-access +rwc "
       "-namemap_mixgen "
       "-clean "
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
    (show-custom-compilation-buffers)
    (enlarge-window 18)
    (larumbe/irun-error-regexp-set-emacs)))



;;;; Verilator
;; INFO: Verilator does not support SystemVerilog verification constructs.
;; Therefore, any source with constructs such as a clocking blocks or classes must be deleted from `verilator.files' (copied previously from gtags.file for example)
;; If that is not possible because it is used as a source (e.g. a SystemVerilog interface with a clocking block), then tweak/comment temporarily files by hand.
;;
;; INFO: This is useful while developing small IPs
(setq verilator-compile-lint-files nil)
(setq verilator-compile-lint-top   nil)
(setq verilator-compile-lint-cmd   nil)

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
  (show-custom-compilation-buffers-verilator))


;;;; Reggen
;; Projects list
;; Name of the project (+plus)
;; 1) Name of project/IP
;; 2) Path to the RDL definition
;; 3) Name of address map
;; 4) Output directory

(setq larumbe-reggen-template-types
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



;;;; Vivado-TCL shell
(setq larumbe/vivado-tcl-shell-buffer "*vivado-tcl*")
;; Fake TCL Shell based on compilation/comint modes to allow for regexps
;; Advantages over `inferior-tcl': Can parse Regexps
;; Drawbacks over `inferior-tcl': Requires custom function to send lines/regions from a .tcl buffer
;;   - This would be previous function :)
(defun larumbe/shell-compilation-tcl-vivado ()
  "Invoke a TCL vivado shell with the proper regexps, suited for compilation"
  (interactive)
  (let ((command (concat tcl-application " " (mapconcat 'identity tcl-command-switches " ")))
        (bufname larumbe/vivado-tcl-shell-buffer)
        (re-func 'larumbe/vivado-error-regexp-set-emacs))
    (larumbe/shell-compilation-regexp-interactive command bufname re-func)))


;; Same as `larumbe/tcl-send-line-or-region-and-step'  but intended for sending text to a *compilation* Vivado Shell with regexps
(defun larumbe/tcl-send-line-or-region-and-step-vivado-shell ()
  "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead."
  (interactive)
  (let (from to end (proc (get-buffer-process larumbe/vivado-tcl-shell-buffer)))
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    (comint-send-string proc (buffer-substring-no-properties from to))
    (comint-send-string proc "\n")
    (goto-char end)))


;;;; Sandboxes
(defun larumbe/shell-compilation-sandbox (initcmd buildcmd bufname re-func)
  "Initialize a bash sandbox and execute build command.
Basically a wrapper for `larumbe/shell-compilation-regexp-interactive' with an additional build command."
  (let ((command initcmd)
        (proc))
    (larumbe/shell-compilation-regexp-interactive command bufname re-func)
    (setq proc (get-buffer-process bufname))
    (comint-send-string proc buildcmd)
    (comint-send-string proc "\n")))
