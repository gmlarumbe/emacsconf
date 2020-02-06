;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Global/ggtags and functions based on them ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Use-package config
(use-package ggtags
  :diminish

  :bind (:map ggtags-navigation-map
              ("M-o"     . nil)
              ("C-c C-k" . nil)         ; EXWM character mode
              ("M->"     . nil)
              ("M-<"     . nil))

  :config
  (setq ggtags-sort-by-nearness nil) ; Enabling nearness requires global 6.5+
  (setq ggtags-navigation-mode-lighter nil)
  (setq ggtags-mode-line-project-name nil)
  ;; (setq ggtags-oversize-limit (* 30 1024 1024)) ; 30 MB

  ;; BUG: Set to 0 to avoid the `global -u' automatic GTAGS update if tags file is smaller than the variable.
  ;; Problem is that that automatic command called from (ggtags-update-tags) does not read the Larumbe's verilog source file
  (setq ggtags-oversize-limit 1)      ; If set to nil it seems that there is no limit...
  (setq ggtags-update-on-save nil)   ;; Try to avoid the `global -u in progress...'

  ;; Don't consider ` (back quote) as part of `tag' when looking for a Verilog macro definition
  (defun ggtags-tag-at-point ()
    (pcase (funcall ggtags-bounds-of-tag-function)
      (`(,beg . ,end)
       (if (eq ?` (string-to-char (buffer-substring beg end)))
           ;; If `(buffer-substring beg end)' returns "`uvm_info" (for example),
           ;; discard the ` and return just "uvm_info"
           (buffer-substring (1+ beg) end)
         ;; else return the whole `(buffer-substring beg end)'
         (buffer-substring beg end)))))
  )


;;; Vivado
;; Projects list for the `larumbe/vivado-projects' and `larumbe/quartus-projects' variables:
;; Name of the project (+plus)
;; 1) Path of the .xpr file (without name)
;; 2) Name of the .xpr
;; 3) Path where GTAGS file will be created
;; 4) Name of the file that will be read by global to generate GTAGS (e.g. verilog files)

;; Init variables for GTAGS generation to nil (this should work as ASSOC list with project name only has 1 element)
(setq larumbe/vivado-projects nil)
(setq larumbe/project-xpr-dir              (nth 1 (car larumbe/vivado-projects)))
(setq larumbe/project-xpr-file             (nth 2 (car larumbe/vivado-projects)))
(setq larumbe/project-gtags-dirs-directory (nth 3 (car larumbe/vivado-projects)))
(setq larumbe/project-gtags-dirs-file      (nth 4 (car larumbe/vivado-projects)))
(setq larumbe/project-gtags-file           (concat larumbe/project-gtags-dirs-directory "/" larumbe/project-gtags-dirs-file))
;; AG Variable files
(setq larumbe/project-gtags-ag-files-filename "ag-files") ; Default, not a need to parameterize.

; INFO: Seems that will eventually deprecate, since is not scalable (assumes files are regexps, and freezes emacs for more than a few files)
; If set to true, will use files in `ag-files' as regexps to parse instantiations. It was a first attempt of making that work in a sandbox with many projects.
(setq larumbe/ag-use-input-regexps nil)
(setq larumbe/hdl-source-extension-regex "\\(.sv$\\|.v$\\|.svh$\\|.vh$\\|.vhd$\\)")

;; Retrieve project list and set variables accordingly
(defun larumbe/project-set-active-project ()
  (interactive)
  (let ((project)
        (files-list)
        (gtags-args))
    ;; Get Project name
    (setq project (completing-read "Select project: " (mapcar 'car larumbe/vivado-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc project larumbe/vivado-projects)))
    ;; Set parameters accordingly
    (setq larumbe/project-xpr-dir              (nth 0 files-list))
    (setq larumbe/project-xpr-file             (nth 1 files-list))
    (setq larumbe/project-gtags-dirs-directory (nth 2 files-list))
    (setq larumbe/project-gtags-dirs-file      (nth 3 files-list))
    (setq larumbe/project-gtags-file           (concat larumbe/project-gtags-dirs-directory "/" larumbe/project-gtags-dirs-file))
    ;; Gtags creation update (For ONLY verilog file parsing)
    ))

;; WORKAROUND FOR SHITTY VIVADO Naming Conventions at IP Wizard generation.
(defun larumbe/project-convert-xci-to-v-and-downcase ()
  "Converts .xci file paths present in gtags.files to .v at downcase
Vivado generates them in this way... Used by `vhier' and GTAGS
Assumes it is being used in current buffer (i.e. gtags.files)"
  (save-excursion
    (beginning-of-buffer)
    (if (re-search-forward "\\([a-zA-Z0-9_-]*\\).xci" nil t) ; Fail silently
        (progn
          (replace-match "\\1.v")
          (re-search-backward "/")
          (downcase-region (point) (point-at-eol)) ; Downcase the whole line
          ))))


;; Function to parse files for project from Vivado XPR
(defun larumbe/project-files-from-xpr ()
  "Create `gtags.files' file for a specific project.
Avoid creating GTAGS for every project included inside a repo folder"
  (with-temp-buffer
    ;; (view-buffer-other-window (current-buffer))      ; Option A: preferred (not valid if modifying the temp buffer)
    ;; (clone-indirect-buffer-other-window "*debug*" t) ; Option B: used here (however, cannot save temp buffer while debugging)
    (insert-file-contents (concat larumbe/project-xpr-dir "/" larumbe/project-xpr-file))
    ;; Start Regexp replacement for file
    (keep-lines "<.*File Path=.*>" (point-min) (point-max))
    (replace-regexp "<.*File Path=\"" "" nil (point-min) (point-max))
    (replace-regexp "\">" "" nil (point-min) (point-max))
    (replace-string "$PPRDIR" larumbe/project-xpr-dir nil (point-min) (point-max))
    (delete-whitespace-rectangle (point-min) (point-max))
    (larumbe/project-convert-xci-to-v-and-downcase)                     ; Replace xci by corresponding .v files (if existing)
    (keep-lines larumbe/hdl-source-extension-regex (point-min) (point-max)) ; Remove any non verilog/vhdl file (such as waveconfig, verilog templates, etc...)
    (larumbe/buffer-expand-filenames)
    (write-file larumbe/project-gtags-file)))


;; Function to parse files for project from Vivado XPR
(defun larumbe/project-tags-xilinx ()
  "Create `gtags.files' file for a specific project.
Avoid creating GTAGS for every project included inside a repo folder"
  (interactive)
  (larumbe/project-set-active-project)
  (save-window-excursion
    (larumbe/project-files-from-xpr)
    (ggtags-create-tags larumbe/project-gtags-dirs-directory)
    (larumbe/project-ag-files-create) ; Create regexps for AG top-module instance searching
    ))


;;; Quartus
(setq larumbe/quartus-projects nil)
(setq larumbe/project-altera-dir                  (nth 1 (car larumbe/quartus-projects)))
(setq larumbe/project-altera-file                 (nth 2 (car larumbe/quartus-projects)))
(setq larumbe/project-altera-gtags-dirs-directory (nth 3 (car larumbe/quartus-projects)))
(setq larumbe/project-altera-gtags-dirs-file      (nth 4 (car larumbe/quartus-projects)))

(setq altera-tcl-file-regexp "\\(.*_FILE\\|SEARCH_PATH\\) ")
(setq altera-tcl-file-regexp-file "\\(.*_FILE\\) ")
(setq altera-tcl-file-regexp-dir "\\(.*SEARCH_PATH\\) ")

;; Functions and variables for directory expansion (retrieve files from a dir on each line for gtags processing)
(setq altera-tcl-env-archons-path "/home/martigon/Repos/svn/obelix/archons/3.0")
(setq altera-tcl-env-archons-regex "$env(ARCHONS_PATH)")
;; Output of `echo $ARCHONS_PATH' at LFP CEE obelix environment
;; Copied from CEE (it was needed to switch to Gigatron environment, something strange with SCP)

(defun larumbe/project-append-files-from-dir (dir)
  "Append list of files from DIR to FILE.
Used on `tempfile' from `files_and_libraries.tcl' to expand directories
Global needs the file name, hence this function"
  (save-excursion
    (mapcar
     (lambda (x)
       (end-of-buffer)
       (insert (concat x "\n")))
     (directory-files dir t))))


(defun larumbe/project-find-repeated-included-files ()
  "Previous append function makes duplicates if files and dirs were included.
This function checks if there is a repeated file for GTAGS not to have a duplicate tag.
Checks Works in current buffer"
  (let ((file-to-check))
    (beginning-of-buffer)
    (while (< (point) (point-max))
      (save-excursion
        (setq file-to-check (concat (file-name-base (thing-at-point 'filename)) "." (file-name-extension (thing-at-point 'filename))))
        (move-end-of-line 1)
        (while (search-forward-regexp (concat file-to-check "$") nil t) ; If file is included more than once we keep only the first one
          (beginning-of-line)
          (kill-line 1)))
      (next-line))))


;; Retrieve project list and set variables accordingly (copied from `larumbe/project-set-active-project' for Vivado xpr)
(defun larumbe/project-set-active-project-altera ()
  (interactive)
  (let ((project)
        (files-list)
        (gtags-args))
    ;; Get Project name
    (setq project (completing-read "Select project: " (mapcar 'car larumbe/quartus-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc project larumbe/quartus-projects)))
    ;; Set parameters accordingly
    (setq larumbe/project-altera-dir                  (nth 0 files-list))
    (setq larumbe/project-altera-file                 (nth 1 files-list))
    (setq larumbe/project-altera-gtags-dirs-directory (nth 2 files-list))
    (setq larumbe/project-altera-gtags-dirs-file      (nth 3 files-list))
    ;; Gtags creation update (For ONLY verilog file parsing)
    ))


(defun larumbe/project-tags-altera ()
  "Create `gtags.files' file for a specific Altera project from `files_and_libraries.tcl' file.
Avoid creating GTAGS for every project included inside a repo folder"
  (interactive)
  ;; First thing is to set project and paths
  (larumbe/project-set-active-project-altera)
  (save-window-excursion
    (with-temp-buffer
      ;; INFO: Debugging with-temp-buffer:
      ;; (view-buffer-other-window (current-buffer))      ; Option A: preferred (not valid if modifying the temp buffer)
      ;; (clone-indirect-buffer-other-window "*debug*" t) ; Option B: used here (however, cannot save temp buffer while debugging)
      ;; End of INFO
      (insert-file-contents (concat larumbe/project-altera-dir "/" larumbe/project-altera-file))
      ;; Start Regexp replacement for file
      (keep-lines altera-tcl-file-regexp (point-min) (point-max)) ; Get only files
      (flush-lines "^#" (point-min) (point-max)) ; Remove comments
      ;; Replace files
      (replace-regexp
       (concat "set_global_assignment -name " altera-tcl-file-regexp-file)
       (concat larumbe/project-altera-dir "/")
       nil (point-min) (point-max))
      ;; Replace SEARCH_PATH dirs
      (beginning-of-buffer)
      (while (search-forward-regexp altera-tcl-file-regexp-dir nil t)
        (kill-line 0) ; Kill until the beginning of line
        (insert (concat larumbe/project-altera-dir "/"))
        (larumbe/project-append-files-from-dir (thing-at-point 'filename)))
      ;; Replace $env(ARCHONS_PATH) dirs
      (beginning-of-buffer)
      (while (search-forward-regexp altera-tcl-env-archons-regex nil t)
        (kill-line 0) ; Kill until the beginning of line
        (insert altera-tcl-env-archons-path))
      ;; Cleanup file
      (replace-regexp " +" "" nil (point-min) (point-max)) ; Delete whitespaces in PATHs
      (flush-lines "\\.$" (point-min) (point-max)) ; Remove search paths with previous or current dir
      (larumbe/project-find-repeated-included-files) ; Remove repeated files (due to previous directory expansion)
      (write-file (concat larumbe/project-altera-gtags-dirs-directory "/" larumbe/project-altera-gtags-dirs-file))))
  ;; Create Tags from gtags.files
  (f-touch (concat larumbe/project-altera-gtags-dirs-directory "/GTAGS")) ; Sometimes there are errors with gtags if file didnt exist before
  (ggtags-create-tags larumbe/project-altera-gtags-dirs-directory))



;;; AG based functions (using ag-files gtags based file)
(defun larumbe/project-ag-files-create (&optional universal-arg)
  "Creates `ag-files' file for further processing to get regexps.
When called interactively, just use LFP project directory `gtags.files' to create `ag-files'
If called with a prefix, then use `gtags.files' from current directory (use with dired)"
  (interactive "P")
  (let ((gtags-files-name (concat larumbe/project-gtags-dirs-directory "/" larumbe/project-gtags-dirs-file))
        (ag-files-name    (concat larumbe/project-gtags-dirs-directory "/" larumbe/project-gtags-ag-files-filename))
        (ag-files-dir     (concat larumbe/project-gtags-dirs-directory "/trunk/")))
    (when universal-arg
      (setq gtags-files-name (concat default-directory "gtags.files"))
      (setq ag-files-name    (concat default-directory "ag-files"))
      (setq ag-files-dir     (expand-file-name default-directory)))
    (with-temp-buffer
      (insert-file-contents gtags-files-name)
      (replace-regexp ag-files-dir "" nil (point-min) (point-max))
      (write-file ag-files-name nil))))


(defun larumbe/project-ag-regexps ()
  "Returns a list for the input of the -G argument of the ag searcher.
This allows for instance detection at a specified set of files (from project gtags.files)"
  (let ((ag-files-name (concat (ggtags-current-project-root) "/" larumbe/project-gtags-ag-files-filename)))
    (with-temp-buffer
      (insert-file-contents ag-files-name)
      (replace-regexp "\n" "|" nil (point-min) (point-max))
      (buffer-string))))


(defun larumbe/lfp-clean-project-fic-keywords-ag-files ()
  "Perform a `ag-regexp' of `fic-mode' highlighted keywords in order to check pending project actions (reads from ag_files for input file filtering)
An alternative manual method would be to use a (helm-projectile-grep)"
  (interactive)
  (let ((kwd)
        (path)
        (ag-arguments ag-arguments)) ; Save the global value of `ag-arguments' (copied from modi)
    (setq kwd (completing-read "Select keyword: " 'fic-highlighted-words))
    (setq path (ggtags-current-project-root))
    ;; Copied from AG for `modi/verilog-find-parent-module'
    (add-to-list 'ag-arguments "-G" :append)
    (add-to-list 'ag-arguments (concat "\"" (larumbe/project-ag-regexps) "\"") :append)
    (ag-regexp kwd path)))



;;; Useful for input to Verilog-Perl extract-hierarchy
;; `gtags.files' can be created manually by opening `source_files.tcl' and executing `larumbe/project-files-from-moduledef'
(defun larumbe/project-files-from-moduledef ()
  "Get into file all the sources present in `source_list.tcl' created by SCons from moduledef.py"
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
