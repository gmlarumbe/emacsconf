;;; verilog-vhier.el --- Verilog-Perl Hierarchy  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; `vhier-outline-mode':
;; Navigate with `outline-minor-mode' through extracted Verilog-Perl hierarchy.
;;
;; `verilog-ext-vhier-current-file' and `verilog-ext-vhier-from-project':
;; Extract verilog hierarchy of current open files or from project list.
;;
;;; Code:

;; (require 'ggtags) ; Gives strange error
(require 'outline)
(require 'verilog-mode)
(require 'verilog-utils)

;;;; Hierarchy navigation
(define-minor-mode vhier-outline-mode
  "Frontend for Verilog-Perl `vhier'.
Rocessed output for `outline-minor-mode' with outshine visualization."
  :lighter " vH"
  :keymap
  '(;; Fetched from https://www.emacswiki.org/emacs/OutlineMinorMode
    ;; SHOW/HIDE
    ("a" . outline-show-all)          ; Show (expand) everything
    ("i" . outline-show-children)     ; Show this heading's immediate child sub-headings
    ("h" . outline-show-children)     ; Alias for `i' due to similarity with vim keys
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
(defvar verilog-ext-vhier-buffer-name "*Verilog-Perl*"
  "Buffer name to use for the hierarchy file.")
(defvar verilog-ext-vhier-shell-cmds-buffer-name "*Verilog-Perl-Shell*"
  "Buffer name to use for the output of the shell commands vppreproc and vhier.")


(defvar verilog-ext-vhier-pp-outfile nil)
(defvar verilog-ext-vhier-pp-args    nil)


(defvar verilog-ext-vhier-vhier-outfile "hierarchy.v")
(defvar verilog-ext-vhier-vhier-args '("--cells"
                                      "--no-missing"
                                      "--missing-modules"))
(defvar verilog-ext-vhier-vhier-filelist-name "vhier.files")
(defvar verilog-ext-vhier-vhier-filelist-path nil)


(defvar verilog-ext-vhier-projects nil
  "Projects list:
Name of the project (+plus)
1) Name of the top-module
2) Input files for hierarchy elaboration
3) Output hierarchy file path")
(defvar verilog-ext-vhier-top-module  nil)
(defvar verilog-ext-vhier-project-dir nil)
(defvar verilog-ext-vhier-input-files nil)



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



(defun verilog-ext-vhier-format-hierarchy-write-file (output-file)
  "Process Verilog-Perl buffer prior to write it to hierarchy file.
Make an outline/outshine accessible view for use with Gtags.

INFO: Ensure ggtags works by writing OUTPUT-FILE into projectile root."
  (pop-to-buffer (get-buffer verilog-ext-vhier-buffer-name))
  (goto-char (point-min))
  (save-excursion
    (verilog-ext-replace-regexp-whole-buffer "  " "*") ; Replace blank spaces by * for outline
    (verilog-ext-replace-regexp-whole-buffer "*\\([a-zA-Z0-9_-]\\)" "* \\1") ; Add blank after asterisks
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
      (verilog-ext-replace-string "// * " "// ** " (point) nil))
    ;; Insert local variables at the end of the file
    (goto-char (point-max))
    (newline 1)
    (insert "
// Local Variables:
// eval: (vhier-outline-mode 1)
// eval: (read-only-mode 1)
// End:
")
    ;; Insert header to get some info of the file
    (goto-char (point-min))
    (open-line 1)
    (insert
     (concat "// Created by Larumbe at " (format-time-string "%d-%m-%Y, %H:%M:%S") "\n"))
    (if verilog-ext-vhier-input-files
        (insert (concat "// Hierarchy extracted from files included in: " verilog-ext-vhier-input-files "\n"))
      (insert (concat "// Hierarchy extracted from `verilog-ext-open-dirs' variable\n")))
    (write-file output-file)
    (vhier-outline-mode)
    (setq buffer-read-only t)
    (unless (string-prefix-p (projectile-project-root output-file) output-file)
      (warn "Vhier outside projectile sandbox. Cannot use ggtags!"))))



;;;###autoload
(defun verilog-ext-vhier-extract-hierarchy ()
  "Execute shell processes that preprocess hierarchy.
Preprocess from `verilog-ext-vhier-vhier-filelist-name'
and extract hierarchy from previous preprocessed file.

INFO: Defined as interactive for the case when the command
`verilog-ext-vhier-from-project'fails due to some reformatting needed on
previously created `verilog-ext-vhier-vhier-filelist-name' via
`verilog-ext-vhier-create-filelist'. e.g: some included file was not
added via -yDIR but as a source file and cannot be found."
  (interactive)
  (let* ((shell-command-dont-erase-buffer t) ; Append output to buffer
         (pp-cmd (concat "vppreproc "
                         "-f " verilog-ext-vhier-vhier-filelist-path " "
                         verilog-ext-vhier-pp-args))
         (vhier-cmd (concat "cd " verilog-ext-vhier-project-dir " && "
                            "vhier " (mapconcat #'identity verilog-ext-vhier-vhier-args " ") " --top-module " verilog-ext-vhier-top-module " "
                            verilog-ext-vhier-pp-outfile))
         (buf     verilog-ext-vhier-buffer-name)
         (buf-err verilog-ext-vhier-shell-cmds-buffer-name)
         (file-path (verilog-ext-path-join verilog-ext-vhier-project-dir verilog-ext-vhier-vhier-outfile))
         (err-msg (format "returned with errors\nCheck %s buffer\nModify %s\nAnd finally run `verilog-ext-vhier-extract-hierarchy' instead of `verilog-ext-vhier-from-project' !"
                          buf-err verilog-ext-vhier-vhier-filelist-path)))
    ;; Preprocess and extract hierarchy (vppreproc && vhier)
    (unless (= 0 (shell-command pp-cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error (concat "vppreproc " err-msg)))
    (unless (= 0 (shell-command vhier-cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error (concat "vhier " err-msg)))
    ;; Format buffer and write file
    (verilog-ext-vhier-format-hierarchy-write-file file-path)))


;;;###autoload
(defun verilog-ext-vhier-from-project ()
  "Extract hierarchy of top level module using Verilog-Perl backend."
  (interactive)
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (verilog-ext-vhier-set-active-project)
  (verilog-ext-vhier-create-filelist)
  (verilog-ext-vhier-extract-hierarchy))


;; TODO: Beautify a little bit
;;;###autoload
(defun verilog-ext-vhier-current-file ()
  "Extract hierarchy of current file module using Verilog-Perl backend."
  (interactive)
  (unless (executable-find "vhier")
    (error "Executable vhier not found"))
  (let* ((library-args (verilog-expand-command "__FLAGS__"))
         (pkg-files  (mapconcat #'identity (verilog-ext-update-project-pkg-list) " "))
         (vhier-args (mapconcat #'identity verilog-ext-vhier-vhier-args " "))
         (top-module (verilog-ext-file-title))
         (cmd (concat "vhier "
                      pkg-files        " "
                      buffer-file-name " "
                      library-args     " "
                      vhier-args       " "
                      "--top-module " top-module))
         (file-path (concat (verilog-ext-path-join (projectile-project-root) "vhier/") top-module ".v"))
         (buf verilog-ext-vhier-buffer-name)
         (buf-err verilog-ext-vhier-shell-cmds-buffer-name)
         (err-msg (format "vhier returned with errors\nCheck %s buffer" buf-err)))
    ;; Body
    (make-directory (file-name-directory file-path) t)
    (verilog-read-defines) ; Not sure if needed...
    (verilog-read-includes)
    (unless (= 0 (shell-command cmd buf buf-err))
      (pop-to-buffer buf-err)
      (error err-msg))
    (verilog-ext-vhier-format-hierarchy-write-file file-path)))




(provide 'verilog-vhier)

;;; verilog-vhier.el ends here
