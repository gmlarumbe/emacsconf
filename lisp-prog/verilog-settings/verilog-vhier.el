;;; verilog-vhier.el --- Verilog-Perl Hierarchy  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;; Verilog-Perl hierarchy
(use-package vhier-outline-mode
  :load-path "~/.elisp/larumbe/own-modes/minors/") ; Navigate hierarchy files easily

(defvar larumbe-verilog-perl-buffer-name "Verilog-Perl"
  "Initial buffer name to use for the hierarchy file.")

;; INFO: First preprocesses input files in a file for `include' and `define' expansion. Then extracts hierarchy from that preprocessed file.
;; Init variables for VHIER Generation to nil
(defvar larumbe-verilog-perl-top-module nil)
(defvar larumbe-verilog-perl-project-vhier-path nil)
(defvar larumbe-verilog-perl-hier-input-files nil)
(defvar larumbe-verilog-perl-hier-file nil)

(defvar larumbe-verilog-perl-preprocessed-file nil)
(defvar larumbe-verilog-perl-outargs nil)
(defvar larumbe-verilog-perl-prep-outargs nil)

(defvar larumbe-verilog-perl-projects nil
"Projects list:
Name of the project (+plus)
1) Name of the top-module
2) Input files for hierarchy elaboration
3) vhier folder path (for generation and further reading)
4) Output hierarchy file path")



(defun larumbe/verilog-vhier-set-active-project ()
  "Retrieve Vhier project list and set variables accordingly."
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
          (concat "-o " larumbe-verilog-perl-preprocessed-file))))


;; Has to be done in the file with the relative include path so that it can be found (e.g. sllc_tb.sv)
(defun larumbe/verilog-vhier-preprocess-hierarchy ()
  "Preprocess hierarchy of top level module for `includes and `defines.
Only used if hierarchy is extracted in project mode."
  (let ((processed-files (concat larumbe-verilog-perl-project-vhier-path "vhier.files")))
    (shell-command
     (concat "mkdir -p " larumbe-verilog-perl-project-vhier-path)) ; Create vhier folder if it did not exist
    (with-temp-buffer
      ;; (view-buffer-other-window (current-buffer))      ; INFO: Debug for `with-temp-buffer'
      ;; (clone-indirect-buffer-other-window "*debug*" t) ; INFO: Debug for `with-temp-buffer'
      (insert-file-contents larumbe-verilog-perl-hier-input-files)
      (larumbe/replace-regexp-whole-buffer "\\(.*/\\).*\.[s]?vh$" "-y \\1") ; Replace header `include' files with -y library flag
      (larumbe/sort-regexp-at-the-beginning-of-file "_defs_pkg.sv") ;; Move every _defs_pkg.sv at the beginning
      (write-file processed-files))
    ;; Eecute preprocess command
    (shell-command
     (concat "vppreproc "
             "-f " processed-files " "
             larumbe-verilog-perl-prep-outargs))))


(defun larumbe/verilog-vhier-format-hierarchy-file ()
  "Process Verilog-Perl file prior to write it to hierarchy file.
Make an outline/outshine accessible view for use with Gtags)"
  (pop-to-buffer (get-buffer larumbe-verilog-perl-buffer-name))
  (save-excursion
    (larumbe/replace-regexp-whole-buffer "  " "*") ; Replace blank spaces by * for outline
    (larumbe/replace-regexp-whole-buffer "*\\([a-zA-Z0-9_-]\\)" "* \\1") ; Add blank after asterisks
    ;; Add comments on every line for outshine detection
    (goto-char (point-min))
    (while (> (point-max) (point))
      (insert "// ")
      (beginning-of-line)
      (forward-line))
    ;; Parse not-used/not-found modules/files
    (goto-char (point-min))
    (re-search-forward "// \\* ") ; Find top instance
    (when (re-search-forward "// \\* " nil t) ; Find second instance to add a blank line if non-found modules exist
      (beginning-of-line)
      (open-line 2)
      (forward-line)
      (insert "// * Not found module references") ; Create level for not found
      (larumbe/replace-string-whole-buffer "// * " "// ** "))
    ;; Insert header to get some info of the file
    (goto-char (point-min))
    (open-line 1)
    (insert
     (concat "// Created by Larumbe at " (format-time-string "%d-%m-%Y, %H:%M:%S") "\n"))
    (if larumbe-verilog-perl-hier-input-files
        (insert (concat "// Hierarchy extracted from files included in: " larumbe-verilog-perl-hier-input-files "\n"))
      (insert (concat "// Hierarchy extracted from `larumbe/verilog-open-dirs' variable\n")))))


(defun larumbe/verilog-vhier-from-project ()
  "Extract hierarchy of top level module using Verilog-Perl backend."
  (interactive)
  (larumbe/verilog-vhier-set-active-project)
  (larumbe/verilog-vhier-preprocess-hierarchy)
  (shell-command
   (concat "vhier "
           larumbe-verilog-perl-outargs
           larumbe-verilog-perl-preprocessed-file)
   larumbe-verilog-perl-buffer-name)
  (larumbe/verilog-vhier-format-hierarchy-file)
  ;; Save-file and enable verilog-mode for tag navigation
  (write-file larumbe-verilog-perl-hier-file)
  (vhier-outline-mode)
  (setq buffer-read-only t))


(defun larumbe/verilog-vhier-current-file ()
  "Extract hierarchy of current file module using Verilog-Perl backend."
  (interactive)
  (let* ((library-args (verilog-expand-command "__FLAGS__"))
         (pkg-files (mapconcat #'identity (larumbe/verilog-update-project-pkg-list) " "))
         (top-module (file-title))
         (cmd (concat
               "vhier "
               pkg-files " "
               buffer-file-name " "
               library-args " "
               "--cells" " "
               "--no-missing" " "
               "--missing-modules" " "
               "--top-module " top-module))
         (file-path (concat (projectile-project-root) "vhier/" top-module ".v")))
    ;; Body
    (verilog-read-defines) ; Not sure if needed...
    (verilog-read-includes)
    (shell-command cmd larumbe-verilog-perl-buffer-name)
    (larumbe/verilog-vhier-format-hierarchy-file)
    (shell-command (concat "mkdir -p " (file-name-directory file-path))) ; Ensure vhier folder is created
    (write-file file-path) ; Ensure ggtags working by writing hier file into projectile root
    (vhier-outline-mode)
    (setq buffer-read-only t)))





(provide 'verilog-vhier)

;;; verilog-vhier.el ends here
