;;; verilog-vhier.el --- Verilog-Perl Hierarchy  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; `vhier-outline-mode':
;; Navigate with `outline-minor-mode' through extracted Verilog-Perl hierarchy.
;;
;; `larumbe/verilog-perl-current-file' and `larumbe/verilog-vhier-from-project':
;; Extract verilog hierarchy of current open files or from project list.
;;
;;; Code:

(require 'verilog-mode)


;;;; Hierarchy navigation
(define-minor-mode vhier-outline-mode
  "Frontend for Verilog-Perl `vhier' processed output for outline-minor-mode with outshine visualization."
  :lighter " vH"
  :keymap
  '(;; Fetched from https://www.emacswiki.org/emacs/OutlineMinorMode
    ;; SHOW/HIDE
    ("a" . outline-show-all)          ; Show (expand) everything
    ("i" . outline-show-children)     ; Show this heading's immediate child sub-headings
    ("l" . vhier-hide-sublevels)      ; Hide current-level sublevels
    ("I" . outline-show-branches)     ; Show all sub-headings under this heading
    (";" . outline-hide-other)        ; Hide other branches
    ;; MOVE
    ("u" . vhier-up-heading)               ; Up
    ("n" . vhier-next-visible-heading)     ; Next
    ("j" . vhier-next-visible-heading)     ;
    ("p" . vhier-previous-visible-heading) ; Previous
    ("k" . vhier-previous-visible-heading)
    ("f" . vhier-forward-same-level)       ; Forward - same level
    ("b" . vhier-backward-same-level)      ; Backward - same level
    ;; JUMP
    ("o" . vhier-outline-jump-to-file)))   ; INFO: Added by Larumbe


;; Still needs to be polished...
;; For example: if added imenu-list, it would parse the vhier-outline buffer instead of the verilog one.
;; Moreover, since there is delay in finding the tag, if set a read-only it would affect the vhier-outline buffer as well...
(defun vhier-outline-jump-to-file ()
  "Jump to file at cursor on hierarchy.v file."
  (interactive)
  (when (not vhier-outline-mode)
    (error "Vhier mode not enabled on current buffer"))
  (when (not (executable-find "global"))
    (error "Vhier mode requires global to work"))
  (when (not (ggtags-find-project))
    (error "Associated GTAGS file not found.  Make sure hierarchy file is in the same folder as its matching GTAGS file"))
  (delete-other-windows)
  (split-window-right)
  (shrink-window-horizontally 60)
  (other-window 1)
  (end-of-line)
  (ggtags-find-tag-dwim (thing-at-point 'symbol t)))


(defun vhier-previous-visible-heading ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-previous-visible-heading)
  (skip-chars-forward "/ *"))


(defun vhier-next-visible-heading ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-next-visible-heading)
  (skip-chars-forward "/ *"))


(defun vhier-up-heading ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-up-heading)
  (skip-chars-forward "/ *"))


(defun vhier-forward-same-level ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-forward-same-level)
  (skip-chars-forward "/ *"))


(defun vhier-backward-same-level ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-backward-same-level)
  (skip-chars-forward "/ *"))


(defun vhier-hide-sublevels ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (beginning-of-line)
  (call-interactively #'outline-hide-sublevels)
  (skip-chars-forward "/ *"))




;;;; Hierarchy extraction
;; INFO: First preprocesses input files for `include' and `define' expansion.
;; Then extracts hierarchy from that preprocessed file.
(defvar larumbe/verilog-perl-buffer-name "*Verilog-Perl*"
  "Buffer name to use for the hierarchy file.")
(defvar larumbe/verilog-perl-shell-cmds-buffer-name "*Verilog-Perl-Shell*"
  "Buffer name to use for the output of the shell commands vppreproc and vhier.")


(defvar larumbe/verilog-perl-pp-outfile nil)
(defvar larumbe/verilog-perl-pp-args    nil)


(defvar larumbe/verilog-perl-vhier-outfile "hierarchy.v")
(defvar larumbe/verilog-perl-vhier-args '("--cells"
                                          "--no-missing"
                                          "--missing-modules"))
(defvar larumbe/verilog-perl-vhier-filelist-name "vhier.files")
(defvar larumbe/verilog-perl-vhier-filelist-path nil)


(defvar larumbe/verilog-perl-projects nil
  "Projects list:
Name of the project (+plus)
1) Name of the top-module
2) Input files for hierarchy elaboration
3) Output hierarchy file path")
(defvar larumbe/verilog-perl-top-module  nil)
(defvar larumbe/verilog-perl-project-dir nil)
(defvar larumbe/verilog-perl-input-files nil)



(defun larumbe/verilog-perl-set-active-project ()
  "Retrieve Vhier project list and set variables accordingly."
  (let ((vhier-project)
        (files-list))
    ;; Get Project name
    (setq vhier-project (completing-read "Select project: " (mapcar 'car larumbe/verilog-perl-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc vhier-project larumbe/verilog-perl-projects)))
    ;; Set parameters accordingly
    (setq larumbe/verilog-perl-top-module  (nth 0 files-list))
    (setq larumbe/verilog-perl-input-files (nth 1 files-list))
    (setq larumbe/verilog-perl-project-dir (nth 2 files-list))
    (setq larumbe/verilog-perl-pp-outfile
          (concat (larumbe/path-join larumbe/verilog-perl-project-dir larumbe/verilog-perl-top-module)
                  "_pp.sv"))
    (setq larumbe/verilog-perl-pp-args (concat "-o " larumbe/verilog-perl-pp-outfile))
    (setq larumbe/verilog-perl-vhier-filelist-path (larumbe/path-join larumbe/verilog-perl-project-dir larumbe/verilog-perl-vhier-filelist-name))))



(defun larumbe/verilog-perl-create-filelist (&optional sort-defs-pkg)
  "Generate larumbe/verilog-perl-vhier-filelist-name filelist from `larumbe/verilog-perl-input-files'
file (normally gtags.files).

INFO: Assumes that files fetched from `larumbe/verilog-perl-input-files' are
relative paths.

If optional arg SORT-DEFS-PKG is set then move every *_defs_pkg.sv file
to the beginning."
  (let ((exp-dir (file-name-directory larumbe/verilog-perl-input-files))
        (debug nil)) ; INFO: Debug `with-temp-buffer', set to non-nil to debug temp buffer contents.
    (make-directory larumbe/verilog-perl-project-dir t) ; Create vhier folder if it did not exist
    (with-temp-buffer
      (when debug
        (clone-indirect-buffer-other-window "*debug*" t))
      (insert-file-contents larumbe/verilog-perl-input-files)
      (larumbe/buffer-expand-filenames t exp-dir)
      (larumbe/replace-regexp-whole-buffer "\\(.*/\\).*\.[s]?vh$" "-y \\1") ; Replace header `include' files with -y library flag
      (when sort-defs-pkg
        (larumbe/sort-regexp-at-the-beginning-of-file "_defs_pkg.sv"))
      (write-file larumbe/verilog-perl-vhier-filelist-path))))



(defun larumbe/verilog-perl-format-hierarchy-write-file (output-file)
  "Process Verilog-Perl buffer prior to write it to hierarchy file.
Make an outline/outshine accessible view for use with Gtags.

INFO: Ensure ggtags works by writing OUTPUT-FILE into projectile root."
  (pop-to-buffer (get-buffer larumbe/verilog-perl-buffer-name))
  (goto-char (point-min))
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
      (larumbe/replace-string "// * " "// ** " (point) (point-max)))
    ;; Insert header to get some info of the file
    (goto-char (point-min))
    (open-line 1)
    (insert
     (concat "// Created by Larumbe at " (format-time-string "%d-%m-%Y, %H:%M:%S") "\n"))
    (if larumbe/verilog-perl-input-files
        (insert (concat "// Hierarchy extracted from files included in: " larumbe/verilog-perl-input-files "\n"))
      (insert (concat "// Hierarchy extracted from `larumbe/verilog-open-dirs' variable\n")))
    (write-file output-file)
    (vhier-outline-mode)
    (setq buffer-read-only t)
    (unless (string-prefix-p (projectile-project-root output-file) output-file)
      (warn "Vhier outside projectile sandbox. Cannot use ggtags!"))))



;;;###autoload
(defun larumbe/verilog-perl-extract-hierarchy ()
  "Execute shell processes that preprocess hierarchy from `larumbe/verilog-perl-vhier-filelist-name'
and extract hierarchy from previous preprocessed file.

INFO: Defined as interactive for the case when the command `larumbe/verilog-perl-from-project'
fails due to some reformatting needed on previously created `larumbe/verilog-perl-vhier-filelist-name' via `larumbe/verilog-perl-create-filelist'.
  e.g: some included file was not added via -yDIR but as a source file and cannot be found.
"
  (interactive)
  (let* ((shell-command-dont-erase-buffer t) ; Append output to buffer
         (pp-cmd (concat "vppreproc "
                         "-f " larumbe/verilog-perl-vhier-filelist-path " "
                         larumbe/verilog-perl-pp-args))
         (vhier-cmd (concat "cd " larumbe/verilog-perl-project-dir " && "
                            "vhier " (mapconcat #'identity larumbe/verilog-perl-vhier-args " ") " --top-module " larumbe/verilog-perl-top-module " "
                            larumbe/verilog-perl-pp-outfile))
         (buf     larumbe/verilog-perl-buffer-name)
         (buf-err larumbe/verilog-perl-shell-cmds-buffer-name)
         (file-path (larumbe/path-join larumbe/verilog-perl-project-dir larumbe/verilog-perl-vhier-outfile))
         (err-msg (format "returned with errors\nCheck %s buffer\nModify %s\nAnd finally run `larumbe/verilog-perl-extract-hierarchy' instead of `larumbe/verilog-perl-from-project' !"
                          buf-err larumbe/verilog-perl-vhier-filelist-path)))
    ;; Preprocess and extract hierarchy (vppreproc && vhier)
    (unless (= 0 (shell-command pp-cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error (concat "vppreproc " err-msg)))
    (unless (= 0 (shell-command vhier-cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error (concat "vhier " err-msg)))
    ;; Format buffer and write file
    (larumbe/verilog-perl-format-hierarchy-write-file file-path)))


;;;###autoload
(defun larumbe/verilog-perl-from-project ()
  "Extract hierarchy of top level module using Verilog-Perl backend."
  (interactive)
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (larumbe/verilog-perl-set-active-project)
  (larumbe/verilog-perl-create-filelist)
  (larumbe/verilog-perl-extract-hierarchy))


;; TODO: Beautify a little bit
;;;###autoload
(defun larumbe/verilog-perl-current-file ()
  "Extract hierarchy of current file module using Verilog-Perl backend."
  (interactive)
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (let* ((library-args (verilog-expand-command "__FLAGS__"))
         (pkg-files  (mapconcat #'identity (larumbe/verilog-update-project-pkg-list) " "))
         (vhier-args (mapconcat #'identity larumbe/verilog-perl-vhier-args " "))
         (top-module (file-title))
         (cmd (concat "vhier "
                      pkg-files        " "
                      buffer-file-name " "
                      library-args     " "
                      vhier-args       " "
                      "--top-module " top-module))
         (file-path (concat (larumbe/path-join (projectile-project-root) "vhier/") top-module ".v"))
         (buf larumbe/verilog-perl-buffer-name)
         (buf-err larumbe/verilog-perl-shell-cmds-buffer-name)
         (err-msg (format "vhier returned with errors\nCheck %s buffer" buf-err)))
    ;; Body
    (make-directory (file-name-directory file-path) t)
    (verilog-read-defines) ; Not sure if needed...
    (verilog-read-includes)
    (unless (= 0 (shell-command cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error err-msg))
    (larumbe/verilog-perl-format-hierarchy-write-file file-path)))




(provide 'verilog-vhier)

;;; verilog-vhier.el ends here
