;;; fpga-projects-settings.el --- FPGA Projects  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(require 'comint)
(require 'compilation-settings)
(require 'compile)


;;;; Vivado Synthesis
(defvar vivado-binary-path nil)
(defvar vivado-batch-script-path nil)
(defvar vivado-batch-project-list nil)
(defvar vivado-batch-project-path nil)
(defvar vivado-batch-project-name nil)
(defvar vivado-batch-compilation-command nil)


(defun larumbe/lfp-compile-vivado-set-active-project ()
  "Set active project based on `vivado-batch-project-list'."
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
  "Use TCL console to elaborate/compile a design based on previous variables."
  (interactive)
  (larumbe/lfp-compile-vivado-set-active-project)
  (compile vivado-batch-compilation-command)
  (larumbe/show-custom-compilation-buffers vivado-error-regexp-emacs-alist-alist))


;;;; Vivado Simulation (XSim)
;; INFO: It is required to create the simulation first with Vivado GUI, and then run the script
(defvar vivado-sim-project-path nil)
(defvar vivado-sim-project-list nil)
(defvar vivado-sim-compilation-command nil)

(defun larumbe/lfp-sim-elab-vivado-set-active-project ()
  "Set active project based on `vivado-sim-project-list'."
  (let (vivado-project)
    (setq vivado-project (completing-read "Select project: " (mapcar 'car vivado-sim-project-list)))
    (setq vivado-sim-project-path (cdr (assoc vivado-project vivado-sim-project-list)))
    (setq vivado-sim-compilation-command
          (concat
           "cd " vivado-sim-project-path " && " ; Temp files will be stored in this path
           "source compile.sh && "
           "source elaborate.sh"))))


(defun larumbe/lfp-sim-elab-vivado-tcl (&optional universal-arg)
  "Use TCL console to elaborate a design with Isim based on previous variables.
If UNIVERSAL-ARG is provided, then simulate as well."
  (interactive "P")
  (larumbe/lfp-sim-elab-vivado-set-active-project)
  (let (cmd)
    (if universal-arg
        (setq cmd (concat vivado-sim-compilation-command " && source simulate.sh"))
      (setq cmd vivado-sim-compilation-command))
    (compile cmd)
    (larumbe/show-custom-compilation-buffers vivado-error-regexp-emacs-alist-alist)))


;;;; Irun
(defvar larumbe/irun-glbl-path          nil)
(defvar larumbe/irun-vivado-simlib-path nil)
(defvar larumbe/irun-vivado-simlib-args nil)

(defvar larumbe/irun-projects           nil)
(defvar larumbe/irun-command            nil)
(defvar larumbe/irun-sources-file       nil)
(defvar larumbe/irun-top-module         nil)
(defvar larumbe/irun-compilation-dir    nil)
(defvar larumbe/irun-opts (concat "-64bit "
                                  "-v93 "
                                  "-relax "
                                  "-access +rwc "
                                  "-namemap_mixgen "
                                  "-clean "
                                  "-vlog_ext +.vh "))

(defun larumbe/irun-set-active-project ()
  "Set active project based on `larumbe/irun-projects'."
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
  "Simulate a design with `irun' after selecting project.
If UNIVERSAL-ARG is given, elaborate the design instead."
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
;; Therefore, any source with constructs such as a clocking blocks or classes must be
;; deleted from `verilator.files' (copied previously from gtags.file for example)
;; If that is not possible because it is used as a source (e.g. a SystemVerilog interface
;; with a clocking block), then tweak/comment temporarily files by hand.
;;
;; INFO: This is useful while developing small IPs
(defvar verilator-project-list       nil)
(defvar verilator-compile-lint-files nil)
(defvar verilator-compile-lint-top   nil)
(defvar verilator-compile-lint-cmd   nil)

(defun larumbe/verilator-lint-set-active-project ()
  "Set active project based on `verilator-project-list'."
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
(defvar larumbe-reggen-tool-path        nil)
(defvar larumbe-reggen-projects         nil)
(defvar larumbe-reggen-input-file       nil)
(defvar larumbe-reggen-address-map-name nil)
(defvar larumbe-reggen-output-path      nil)
(defvar larumbe-reggen-template-types
  '("c_header"
    "docbook"
    "verilog_header"
    "verilog_defspkg"
    "verilog_regcomponent_simple"
    "verilog_regcomponent_regbusitf"
    "verilog_regcomponent_axilite"))


(defun larumbe/reggen-set-active-project ()
  "Set active project based on `larumbe-reggen-projects'."
  (interactive)
  (let (reggen files-list)
    ;; Get Project name
    (if (bound-and-true-p larumbe-reggen-input-file)
        (setq reggen (completing-read "Select project: " (mapcar 'car larumbe-reggen-projects)))
      (setq reggen (car (car larumbe-reggen-projects))))  ; If no project is defined, use default (first one)
    (setq files-list (cdr (assoc reggen larumbe-reggen-projects)))
    ;; Set parameters accordingly
    (setq larumbe-reggen-input-file       (nth 0 files-list))
    (setq larumbe-reggen-address-map-name (nth 1 files-list))
    (setq larumbe-reggen-output-path      (nth 2 files-list))))


(defun larumbe/reggen ()
  "Generate reggen outputs according to `larumbe-reggen-projects' and derived."
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
  "Create a `compilation-mode' comint shell almost identical to *ansi-term*.
It will have the same environment and aliases without the need of setting
`shell-command-switch' to '-ic'.

Execute COMMAND in the buffer.  Buffer will be renamed to BUFNAME.
Regexp parsing function RE-FUNC is applied.

Useful to spawn a *tcl-shell* with Vivado regexps, or to init sandbox modules."
  (when (get-buffer bufname)
    (pop-to-buffer bufname)
    (error (concat "Buffer " bufname " already in use!")))
  (compile command t)
  (select-window (get-buffer-window "*compilation*"))
  (goto-char (point-max))
  (setq truncate-lines t)
  (funcall re-func)
  (rename-buffer bufname))


;;;; Sandboxes
(defvar larumbe/shell-compilation-sandbox-buildcmd nil
  "Buffer-local variable used to determine the executed build command.
It's main use is to allow for recompiling easily.")

(defun larumbe/shell-compilation-sandbox (initcmd buildcmd bufname re-func)
  "Initialize a comint Bash sandbox with INITCMD and execute BUILDCMD next.
Buffer will be renamed to BUFNAME, and regexp parsing depending on RE-FUNC.

Acts as wrapper for `larumbe/shell-compilation-regexp-interactive'
with an additional build command.

INFO: With some minor tweaks could be extended to allow a list
of commands to be executed by sending them through `comint-send-string'"
  (let ((command initcmd)
        (proc))
    (larumbe/shell-compilation-regexp-interactive command bufname re-func)
    (setq-local larumbe/shell-compilation-sandbox-buildcmd buildcmd)
    (setq proc (get-buffer-process bufname))
    (comint-send-string proc buildcmd)
    (comint-send-string proc "\n")))


(defun larumbe/shell-compilation-recompile ()
  "Will only work in comint mode for previous functions.
Makes use of buffer-local variable `larumbe/shell-compilation-sandbox-buildcmd' to rebuild a target."
  (interactive)
  (let (proc)
    (when (string= major-mode "comint-mode")
      (setq proc (get-buffer-process (current-buffer)))
      (comint-send-string proc larumbe/shell-compilation-sandbox-buildcmd)
      (comint-send-string proc "\n"))))


(provide 'fpga-projects-settings)

;;; fpga-projects-settings.el ends here
