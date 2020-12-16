;;; init-fpga-projects.el --- FPGA Projects  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Vivado tags
;; Projects list for the `larumbe/vivado-projects':
;; Name of the project (+plus)
;; 1) Path of the .xpr file (without name)
;; 2) Name of the .xpr
;; 3) Path where GTAGS file will be created
;; 4) Name of the file that will be read by global to generate GTAGS (e.g. verilog files)

;; Init variables for GTAGS generation to nil (this should work as ASSOC list with project name only has 1 element)
(defvar larumbe/vivado-projects nil)
(defvar larumbe/project-xpr-dir              (nth 1 (car larumbe/vivado-projects)))
(defvar larumbe/project-xpr-file             (nth 2 (car larumbe/vivado-projects)))
(defvar larumbe/project-gtags-dirs-directory (nth 3 (car larumbe/vivado-projects)))
(defvar larumbe/project-gtags-dirs-file      (nth 4 (car larumbe/vivado-projects)))
(defvar larumbe/project-gtags-file           nil) ; (larumbe/path-join larumbe/project-gtags-dirs-directory larumbe/project-gtags-dirs-file)

(defvar larumbe/hdl-source-extension-regex "\\(.sv$\\|.v$\\|.svh$\\|.vh$\\|.vhd$\\)")


(defun larumbe/project-set-active-xpr ()
  "Retrieve project list and set variables accordingly."
  (let ((project)
        (files-list))
    ;; Get Project name
    (setq project (completing-read "Select project: " (mapcar 'car larumbe/vivado-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc project larumbe/vivado-projects)))
    ;; Set parameters accordingly
    (setq larumbe/project-xpr-dir              (nth 0 files-list))
    (setq larumbe/project-xpr-file             (nth 1 files-list))
    (setq larumbe/project-gtags-dirs-directory (nth 2 files-list))
    (setq larumbe/project-gtags-dirs-file      (nth 3 files-list))
    (setq larumbe/project-gtags-file           (larumbe/path-join larumbe/project-gtags-dirs-directory larumbe/project-gtags-dirs-file))))


(defun larumbe/project-convert-xci-to-v-and-downcase ()
  "Convert .xci file paths present in gtags.files to .v and downcase.
Vivado generates them in this way... Used by `vhier' and GTAGS
Assumes it is being used in current buffer (i.e. gtags.files).

INFO: This is a Workaround for Vivado Naming Conventions at IP Wizard generation."
  (save-excursion
    (goto-char (point-min))
    (if (re-search-forward "\\([a-zA-Z0-9_-]*\\).xci" nil t) ; Fail silently
        (progn
          (replace-match "\\1.v")
          (re-search-backward "/")
          (downcase-region (point) (point-at-eol))))))


;; Function to parse files for project from Vivado XPR
(defun larumbe/project-files-from-xpr ()
  "Create `gtags.files' file for a specific project.
Avoid creating GTAGS for every project included inside a repo folder"
  (with-temp-buffer
    ;; (view-buffer-other-window (current-buffer))      ; Option A: preferred (not valid if modifying the temp buffer)
    ;; (clone-indirect-buffer-other-window "*debug*" t) ; Option B: used here (however, cannot save temp buffer while debugging)
    (insert-file-contents (larumbe/path-join larumbe/project-xpr-dir larumbe/project-xpr-file))
    ;; Start Regexp replacement for file
    (keep-lines "<.*File Path=.*>" (point-min) (point-max))
    (larumbe/replace-regexp-whole-buffer "<.*File Path=\"" "")
    (larumbe/replace-regexp-whole-buffer "\">" "")
    (larumbe/replace-string-whole-buffer "$PPRDIR" larumbe/project-xpr-dir t)
    (delete-whitespace-rectangle (point-min) (point-max))
    (larumbe/project-convert-xci-to-v-and-downcase)                         ; Replace xci by corresponding .v files (if existing)
    (keep-lines larumbe/hdl-source-extension-regex (point-min) (point-max)) ; Remove any non verilog/vhdl file (such as waveconfig, verilog templates, etc...)
    (larumbe/buffer-expand-filenames)
    (write-file larumbe/project-gtags-file)))


;; Function to parse files for project from Vivado XPR
(defun larumbe/project-tags-xilinx ()
  "Create `gtags.files' file for a specific project.
Avoid creating GTAGS for every project included inside a repo folder"
  (interactive)
  (larumbe/project-set-active-xpr)
  (save-window-excursion
    (larumbe/project-files-from-xpr)
    (ggtags-create-tags larumbe/project-gtags-dirs-directory)))


;;;; Quartus tags
;; Projects list for the `larumbe/quartus-projects' variables:
;; Name of the project (+plus)
;; 1) Path of the altera dir (without name)
;; 2) Name of the tcl file used to get the file list (files_and_libraries.tcl)
;; 3) Path where GTAGS file will be created
;; 4) Name of the file that will be read by global to generate GTAGS (e.g. gtags.files)
(defvar larumbe/quartus-projects nil)
(defvar larumbe/project-altera-dir                  (nth 1 (car larumbe/quartus-projects)))
(defvar larumbe/project-altera-file                 (nth 2 (car larumbe/quartus-projects)))
(defvar larumbe/project-altera-gtags-dirs-directory (nth 3 (car larumbe/quartus-projects)))
(defvar larumbe/project-altera-gtags-dirs-file      (nth 4 (car larumbe/quartus-projects)))

(defvar altera-tcl-file-regexp "\\(.*_FILE\\|SEARCH_PATH\\) ")
(defvar altera-tcl-file-regexp-file "\\(.*_FILE\\) ")
(defvar altera-tcl-file-regexp-dir "\\(.*SEARCH_PATH\\) ")

;; Functions and variables for directory expansion (retrieve files from a dir on each line for gtags processing)
(defvar altera-tcl-env-archons-path "/home/martigon/Repos/svn/obelix/archons/3.0")
(defvar altera-tcl-env-archons-regex "$env(ARCHONS_PATH)")
;; Output of `echo $ARCHONS_PATH' at LFP CEE obelix environment

(defun larumbe/project-append-files-from-dir (dir)
  "Append list of files from DIR to FILE.
Used on `tempfile' from `files_and_libraries.tcl' to expand directories
Global needs the file name, hence this function"
  (save-excursion
    (mapcar
     (lambda (x)
       (goto-char (point-max))
       (insert (concat x "\n")))
     (directory-files dir t))))


(defun larumbe/project-find-repeated-included-files ()
  "Find repeated files in current buffer (meant for gtags.files).
There are duplicates in `larumbe/project-append-files-from-dir' if files and
dirs are included.  This function checks if there is a repeated file in
gtags.files for GTAGS not to have a duplicate tag.
Checks Works in current buffer."
  (let ((file-to-check))
    (goto-char (point-min))
    (while (< (point) (point-max))
      (save-excursion
        (setq file-to-check (concat (file-name-base (thing-at-point 'filename)) "." (file-name-extension (thing-at-point 'filename))))
        (move-end-of-line 1)
        (while (re-search-forward (concat file-to-check "$") nil t) ; If file is included more than once we keep only the first one
          (beginning-of-line)
          (kill-line 1)))
      (forward-line))))


(defun larumbe/project-set-active-project-altera ()
  "Retrieve project list and set variables accordingly.
Copied from `larumbe/project-set-active-xpr' for Vivado xpr."
  (interactive)
  (let ((project)
        (files-list))
    ;; Get Project name
    (setq project (completing-read "Select project: " (mapcar 'car larumbe/quartus-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc project larumbe/quartus-projects)))
    ;; Set parameters accordingly
    (setq larumbe/project-altera-dir                  (nth 0 files-list))
    (setq larumbe/project-altera-file                 (nth 1 files-list))
    (setq larumbe/project-altera-gtags-dirs-directory (nth 2 files-list))
    (setq larumbe/project-altera-gtags-dirs-file      (nth 3 files-list))))


(defun larumbe/project-tags-altera ()
  "Create `gtags.files' file for a specific Altera project.
Based on a search from `files_and_libraries.tcl' file.
Avoid creating GTAGS for every project included inside a sandbox."
  (interactive)
  ;; First thing is to set project and paths
  (larumbe/project-set-active-project-altera)
  (save-window-excursion
    (with-temp-buffer
      ;; INFO: Debugging with-temp-buffer:
      ;; (view-buffer-other-window (current-buffer))      ; Option A: preferred (not valid if modifying the temp buffer)
      ;; (clone-indirect-buffer-other-window "*debug*" t) ; Option B: used here (however, cannot save temp buffer while debugging)
      ;; End of INFO
      (insert-file-contents (larumbe/path-join larumbe/project-altera-dir larumbe/project-altera-file))
      ;; Start Regexp replacement for file
      (keep-lines altera-tcl-file-regexp (point-min) (point-max)) ; Get only files
      (goto-char (point-min))
      (while (re-search-forward "^#" nil t)   ; Remove comments
        (beginning-of-line)
        (kill-line 1))
      ;; Replace files
      (larumbe/replace-regexp-whole-buffer
       (concat "set_global_assignment -name " altera-tcl-file-regexp-file)
       (concat (file-name-as-directory larumbe/project-altera-dir)))
      ;; Replace SEARCH_PATH dirs
      (goto-char (point-min))
      (while (re-search-forward altera-tcl-file-regexp-dir nil t)
        (kill-line 0) ; Kill until the beginning of line
        (insert (file-name-as-directory larumbe/project-altera-dir))
        (larumbe/project-append-files-from-dir (thing-at-point 'filename)))
      ;; Replace $env(ARCHONS_PATH) dirs
      (goto-char (point-min))
      (while (re-search-forward altera-tcl-env-archons-regex nil t)
        (kill-line 0) ; Kill until the beginning of line
        (insert altera-tcl-env-archons-path))
      ;; Cleanup file
      (larumbe/replace-regexp-whole-buffer " +" "")  ; Delete whitespaces in PATHs
      (goto-char (point-min))
      (while (re-search-forward "\\.$" nil t) ; Remove search paths with previous or current dir
        (beginning-of-line)                   ; Equivalent to `flush-lines' but
        (kill-line 1))                        ; for non-interactive use
      (larumbe/project-find-repeated-included-files) ; Remove repeated files (due to previous directory expansion)
      (larumbe/buffer-expand-filenames)
      (write-file (larumbe/path-join larumbe/project-altera-gtags-dirs-directory larumbe/project-altera-gtags-dirs-file))))
  ;; Create Tags from gtags.files
  (f-touch (larumbe/path-join larumbe/project-altera-gtags-dirs-directory "GTAGS")) ; Sometimes there are errors with gtags if file didnt exist before
  (ggtags-create-tags larumbe/project-altera-gtags-dirs-directory))


;;;; Moduledef tags
(defun larumbe/project-files-from-moduledef ()
  "Manually create gtags.files from `source_files.tcl'.
Should only be used interactive and in the source_files.tcl buffer.
The output gtags.files will be created in the same directory.

INFO: Useful function for Verilog-Perl hierarchy extraction."
  (interactive)
  (let ((sources-file (buffer-file-name))
        (output-file (concat default-directory "gtags.files")))
    (when (not (string-equal
                (file-relative-name (buffer-file-name))
                "source_list.tcl"))
      (error "Not in 'source_list.tcl file!!"))
    (with-temp-buffer
      ;; (clone-indirect-buffer-other-window "*debug*" t) ; Option B: used here (however, cannot save temp buffer while debugging)
      (insert-file-contents sources-file)
      (keep-lines larumbe/hdl-source-extension-regex)
      (delete-duplicate-lines (point-min) (point-max)) ; for libraries setup of previous files
      (larumbe/buffer-expand-filenames)
      (write-file output-file))))


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


;;;; Vivado XSim
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



(provide 'init-fpga-projects)

;;; init-fpga-projects.el ends here
