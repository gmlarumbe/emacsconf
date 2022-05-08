;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'verilog-mode)


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
