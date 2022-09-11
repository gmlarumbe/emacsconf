;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(require 'flycheck)
(require 'projectile)
(require 'verilog-mode)
(require 'verilog-rx)
(require 'verilog-navigation)
;; (require 'verilog-flycheck) ; TODO: Recursive inclusion or something like that?

;;;; Misc
;; https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
(defvar verilog-ext-open-dirs nil
  "List with directories of current opened `verilog-mode' buffers.
Used for verilog AUTO libraries, flycheck and Verilog-Perl hierarchy.")
(defvar verilog-ext-open-pkgs nil
  "List of currently opened SystemVerilog packages.")
(defvar verilog-ext-open-pkgs-projectile nil
  "List of current open packages at projectile project.")


(defun verilog-ext-dirs-and-pkgs-of-open-buffers ()
  "Return a list of directories from current verilog opened files.
It also updates currently opened SystemVerilog packages.

Used for flycheck and vhier packages."
  (let ((verilog-opened-dirs)
        (verilog-opened-pkgs)
        (pkg-regexp "^\\s-*\\(?1:package\\)\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)"))
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "verilog-mode")
          (unless (member default-directory verilog-opened-dirs)
            (push default-directory verilog-opened-dirs))
          (save-excursion
            (goto-char (point-min))
            (when (re-search-forward pkg-regexp nil t)
              (unless (member (buffer-file-name) verilog-opened-pkgs)
                (push (buffer-file-name) verilog-opened-pkgs)))))))
    `(,verilog-opened-dirs ,verilog-opened-pkgs)))  ; Return list of dirs and packages


(defun verilog-ext-update-project-pkg-list ()
  "Update currently open packages on `verilog-ext-open-pkgs-projectile'.

Only packages within current projectile project are added.
To be used with vhier/flycheck.

INFO: Limitations:
 - Packages included as sources might not be in the proper order.
 - Some sorting method could be used in the future:
   - Extracting them from buffer file but in the order they have been
     opened and reverse sorting, for example..."
  (setq verilog-ext-open-pkgs-projectile nil) ; Reset list
  (mapc
   (lambda (pkg)
     (when (string-prefix-p (projectile-project-root) pkg)
       (unless (member pkg verilog-ext-open-pkgs-projectile)
         (push pkg verilog-ext-open-pkgs-projectile))))
   verilog-ext-open-pkgs)
  ;; Return pkg-list
  verilog-ext-open-pkgs-projectile)


(defun verilog-ext-path-join (arg1 arg2)
  "Join path of ARG1 and ARG2.
If more than 2 args are required, use `f-join'"
  (if (and arg1 arg2)
      (concat (file-name-as-directory arg1) arg2)
    (error "Cannot join path with nil arguments.")
    nil))


(defun verilog-ext-file-title ()
  "Return file title; e.g. for '/opt/asdf.txt' eval 'asdf'."
  (file-name-sans-extension (file-name-nondirectory (buffer-file-name))))


(defun verilog-ext-buffer-expand-filenames (&optional absolute exp-dir)
  "Expands filenames paths present in `current-buffer' line by line.
If ABSOLUTE is nil expand relative to `default-directory'.
If ABSOLUTE is non-nil filenames will expand to their absolute paths.
If EXP-DIR is non-nil, expand relative to this argument instead
of `default-directory'."
  (let ((cur-line)
        (default-directory (if exp-dir
                               exp-dir
                             default-directory)))
    (save-excursion
      (goto-char (point-min))
      (while (< (point) (point-max))
        (delete-horizontal-space)
        (if absolute
            (setq cur-line (expand-file-name (thing-at-point 'line) default-directory))
          (setq cur-line (file-relative-name (thing-at-point 'line) default-directory)))
        (kill-line 1)
        (insert cur-line)))))


(defun verilog-ext-replace-regexp (regexp to-string start end)
  "Wrapper function for programatic use of `replace-regexp'.
Replace REGEXP with TO-STRING from START to END."
  (save-excursion
    (goto-char start)
    (while (re-search-forward regexp end t)
      (replace-match to-string))))


(defun verilog-ext-replace-regexp-whole-buffer (regexp to-string)
  "Replace REGEXP with TO-STRING on whole current-buffer."
  (verilog-ext-replace-regexp regexp to-string (point-min) nil))

(defun verilog-ext-replace-string (string to-string start end &optional fixedcase)
  "Wrapper function for programatic use of `replace-string'.
Replace STRING with TO-STRING from START to END.

If optional arg FIXEDCASE is non-nil, do not alter the case of
the replacement text (see `replace-match' for more info)."
  (save-excursion
    (goto-char start)
    (while (search-forward string end t)
      (replace-match to-string fixedcase))))


(defun verilog-ext-sort-regexp-at-the-beginning-of-file (regexp)
  "Move lines containing REGEXP recursively at the beginning of the file.
Done line by line, this might be useful when managing a list of files,
one file at a line, and there is some need of sorting by regexp.
For example, in SystemVerilog, packages might need to be included before other files."
  (interactive)
  (let ((sorted-files-p nil))
    (goto-char (point-min))
    (while (not sorted-files-p)
      (save-excursion
        (unless (search-forward-regexp regexp nil 1)
          (setq sorted-files-p t))
        (beginning-of-line)
        (kill-line 1)) ; Kill trailing newline as well
      (yank))))

(defun verilog-ext-flycheck-eldoc-toggle ()
  "Disable `eldoc-mode' when enabling `flycheck-mode'.
Avoid minibuffer conflicts between ggtags use of eldoc and flycheck."
  (interactive)
  (if eldoc-mode
      (progn
        (eldoc-mode -1)
        (flycheck-mode 1)
        (message "Flycheck enabled"))
    (eldoc-mode 1)
    (flycheck-mode -1)
    (message "Flycheck disabled")))


;;;; Others
(defun verilog-ext-find-semicolon-in-instance-comments ()
  "Find semicolons in instance comments.

Main purpose is to avoid missing instantiation detections with `imenu' and
`verilog-ext-find-module-instance-fwd' functions.

Point to problematic regexp in case it is found."
  (let ((case-fold-search verilog-case-fold)
        (problem-re ")[, ]*\\(//\\|/\\*\\).*;") ; DANGER: Does not detect semicolon if newline within /* comment */
        (found))
    (save-excursion
      (goto-char (point-min))
      (when (re-search-forward problem-re nil t)
        (setq found t)))
    (when found
      (goto-char (point-min))
      (re-search-forward problem-re nil t)
      (message "Imenu DANGER!: semicolon in comment instance!!"))))




(defun verilog-ext-point-at-instance-p ()
  "Return if point is inside a Verilog instance.
Return list with TYPE and NAME."
  (let ((point-cur (point))
        point-instance-begin
        point-instance-end
        instance-type
        instance-name)
    (save-excursion
      (when (verilog-ext-find-module-instance-bwd)
        (setq instance-type (match-string-no-properties 1))
        (setq instance-name (match-string-no-properties 2))
        (setq point-instance-begin (point))
        (verilog-ext-find-module-instance-fwd)
        (re-search-forward ")\s*;") ; TODO: Do something in case finds a ); inside comment? Check if it is used somehwere else?
        (setq point-instance-end (point))
        (if (and (>= point-cur point-instance-begin)
                 (<= point-cur point-instance-end))
            (list instance-type instance-name)
          nil)))))


(defun verilog-ext-point-inside-class-p ()
  "Return non-nil if cursor is pointing a func/task inside a class."
  (interactive)
  (save-match-data
    (unless (or (looking-at verilog-ext-task-re)
                (looking-at verilog-ext-function-re))
      (error "Pointer is not in a function/task!"))
    (let ((task-point (point))
          (endclass-point))
      (save-excursion
        (if (verilog-ext-find-class-bwd)
            (progn
              (verilog-forward-sexp)
              (setq endclass-point (point))
              (if (< task-point endclass-point)
                  t
                nil))
          nil)))))



;;;; Hooks
(defun verilog-ext-hook ()
  "Verilog hook."
  (setq verilog-ext-open-dirs (nth 0 (verilog-ext-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-ext-open-pkgs (nth 1 (verilog-ext-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-library-directories verilog-ext-open-dirs) ; Verilog *AUTO* folders (could use `verilog-library-files' for files)
  (setq verilog-ext-flycheck-verilator-include-path verilog-ext-open-dirs)
  (flycheck-select-checker verilog-ext-flycheck-active-linter)
  (modify-syntax-entry ?` ".") ; Avoid including preprocessor tags while isearching. Requires `verilog-ext-electric-verilog-tab' to get back standard table to avoid indentation issues with compiler directives.
  (verilog-ext-time-stamp-update)
  (verilog-ext-find-semicolon-in-instance-comments)
  (setq-local yas-indent-line 'fixed))




(provide 'verilog-utils)

;;; verilog-utils.el ends here
