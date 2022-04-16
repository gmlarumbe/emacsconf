;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'make-mode)
(require 'which-func)
(require 'verilog-mode)
(require 'init-ggtags)
(require 'time-stamp)



;;;; Lint, Compilation and Simulation Tools
;; INFO: Discarding the following `verilog-set-compile-command' variables:
;; - `verilog-linter:' replaced by FlyCheck with opened buffers as additional arguments, plus custom project parsing functions
;; - `verilog-simulator': replaced by XSim and ncsim sim project funcions
;; - `verilog-compiler': replaced by Vivado elaboration/synthesis project functions
;; - `verilog-preprocessor': `larumbe/verilog-preprocess' wrapper of verilog-mode internal function' does the trick
;; - `verilog-coverage' still not implemented as there are not many free alternatives...


;;;;; Preprocessor
(defun larumbe/verilog-preprocess ()
  "Allow choosing between programs with a wrapper of `verilog-preprocess'.
All the libraries/incdirs are computed internally at `verilog-mode' via
`verilog-expand'.
INFO: `iverilog' command syntax requires writing to an output file (defaults to a.out)."
  (interactive)
  (let (iver-out-file)
    (pcase (completing-read "Select tool: " '("verilator" "vppreproc" "iverilog"))
      ("verilator" (setq verilog-preprocessor "verilator -E __FLAGS__ __FILE__"))
      ("vppreproc" (setq verilog-preprocessor "vppreproc __FLAGS__ __FILE__"))
      ("iverilog"  (progn (setq iver-out-file (read-string "Output filename: " (concat (file-title) "_pp.sv")))
                          (setq verilog-preprocessor (concat "iverilog -E -o" iver-out-file " __FILE__ __FLAGS__")))))
    (verilog-preprocess)))


;;;;; Iverilog/verilator Makefile development
(defun larumbe/verilog-makefile-create ()
  "Create Iverilog/verilator Yasnippet based Makefile.
Create it only if in a projectile project and the Makefile does not exist already."
  (interactive)
  (let (file)
    (if (projectile-project-p)
        (if (file-exists-p (setq file (concat (projectile-project-root) "Makefile")))
            (error "File %s already exists!" file)
          (progn
            (find-file file)
            (larumbe/hydra-yasnippet "verilog")))
      (error "Not in a projectile project!"))))


(defun larumbe/verilog-makefile-compile-project ()
  "Prompts to available previous Makefile targets and compiles them with various verilog regexps."
  (interactive)
  (let ((makefile (concat (projectile-project-root) "Makefile"))
        target
        cmd)
    (unless (file-exists-p makefile)
      (error "%s does not exist!" makefile))
    (with-temp-buffer
      (insert-file-contents makefile)
      (setq makefile-need-target-pickup t)
      (makefile-pickup-targets)
      (setq target (completing-read "Target: " makefile-target-table)))
    ;; INFO: Tried with `projectile-compile-project' but without sucess.
    ;; Plus, it was necessary to change `compilation-read-command' which is unsafe.
    (setq cmd (concat "make " target))
    (cd (projectile-project-root))
    (larumbe/compile cmd nil "verilog-make")))


;;;; Port connect/disconnect/blank cleaning
(defvar larumbe/connect-disconnect-port-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)")
(defvar larumbe/connect-disconnect-conn-re "\\(?4:(\\(?5:.*\\))\\)?")
(defvar larumbe/connect-disconnect-not-found "No port detected at current line")

(defun larumbe/verilog-toggle-connect-port (force-connect)
  "Toggle connect/disconnect port at current line.

If regexp detects that port is connected then disconnect it
and viceversa.

If called with universal arg, FORCE-CONNECT parameter will force connection
of current port, no matter if it is connected/disconnected"
  (interactive "P")
  (let* ((case-fold-search verilog-case-fold)
         (port-regex larumbe/connect-disconnect-port-re)
         (conn-regex larumbe/connect-disconnect-conn-re)
         (line-regex (concat port-regex conn-regex))
         port conn sig
         (start (point)))
    ;; Find '.port (conn)' verilog regexp
    (beginning-of-line)
    (if (re-search-forward line-regex (point-at-eol) t)
        (progn
          (setq port (match-string-no-properties 2))
          (setq conn (match-string-no-properties 5))
          (if (or (string-equal conn "") force-connect) ; If it is disconnected or connection is forced via parameter...
              (progn ; Connect
                (setq sig (read-string (concat "Connect [" port "] to: ") port))
                (replace-match (concat "\\1.\\2\\3\(" sig "\)") t))
            (progn ; Else disconnect
              (replace-match (concat "\\1.\\2\\3\(" nil "\)") t)))
          (goto-char start)
          (forward-line))
      (progn ; No port found
        (goto-char start)
        (message larumbe/connect-disconnect-not-found)))))


(defun larumbe/verilog-connect-ports-recursively ()
  "Connect ports of current instance recursively.

Ask for ports to be connected until no port is found at current line."
  (interactive)
  (while (not (equal (larumbe/verilog-toggle-connect-port t) larumbe/connect-disconnect-not-found))
    (larumbe/verilog-toggle-connect-port t)))



(defvar larumbe/verilog-clean-port-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)(\\(?4:[ ]*\\)\\(?5:[^ ]+\\)\\(?6:[ ]*\\))"
  "Information about different capture groups:
Group 1: Beginning of line blanks
Group 2: Port name (after dot connection)
Group 3: Blanks after identifier
Group 4: Blanks after beginning of port connection '('
Group 5: Name of connection
Group 6: Blanks after end of port connection ')'")

(defun larumbe/verilog-clean-port-blanks ()
  "Cleans blanks inside port connections of current buffer."
  (interactive)
  (let ((old-re larumbe/verilog-clean-port-re)
        (new-re "\\1.\\2\\3\(\\5\)"))
    (larumbe/replace-regexp-whole-buffer old-re new-re)
    (message "Removed blanks from current buffer port connections.")))



;;;; Misc
;; https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
(defvar larumbe/verilog-open-dirs nil
  "List with directories of current opened `verilog-mode' buffers.
Used for verilog AUTO libraries, flycheck and Verilog-Perl hierarchy.")
(defvar larumbe/verilog-open-pkgs nil
  "List of currently opened SystemVerilog packages.")
(defvar larumbe/verilog-project-pkg-list nil
  "List of current open packages at projectile project.")


(defun larumbe/verilog-dirs-and-pkgs-of-open-buffers ()
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


(defun larumbe/verilog-update-project-pkg-list ()
  "Update currently open packages on `larumbe/verilog-project-pkg-list'.

Only packages within current projectile project are added.
To be used with vhier/flycheck.

INFO: Limitations:
 - Packages included as sources might not be in the proper order.
 - Some sorting method could be used in the future:
   - Extracting them from buffer file but in the order they have been
     opened and reverse sorting, for example..."
  (setq larumbe/verilog-project-pkg-list nil) ; Reset list
  (mapc
   (lambda (pkg)
     (when (string-prefix-p (projectile-project-root) pkg)
       (unless (member pkg larumbe/verilog-project-pkg-list)
         (push pkg larumbe/verilog-project-pkg-list))))
   larumbe/verilog-open-pkgs)
  ;; Return pkg-list
  larumbe/verilog-project-pkg-list)



;;;; Hooks
(defun larumbe/verilog-hook ()
  "Verilog hook."
  (setq larumbe/verilog-open-dirs (nth 0 (larumbe/verilog-dirs-and-pkgs-of-open-buffers)))
  (setq larumbe/verilog-open-pkgs (nth 1 (larumbe/verilog-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-library-directories larumbe/verilog-open-dirs) ; Verilog *AUTO* folders (could use `verilog-library-files' for files)
  (setq larumbe/flycheck-verilator-include-path larumbe/verilog-open-dirs)
  (flycheck-select-checker larumbe/flycheck-active-linter)
  (modify-syntax-entry ?` ".") ; Avoid including preprocessor tags while isearching. Requires `larumbe/electric-verilog-tab' to get back standard table to avoid indentation issues with compiler directives.
  (larumbe/verilog-time-stamp-update)
  (larumbe/verilog-find-semicolon-in-instance-comments)
  (setq-local yas-indent-line 'fixed))


;;;; Modi
(defun modi/verilog-get-header (&optional fwd)
  "Function to return the name of the block (module, class, package,
function, task, `define) under which the point is currently present.

If FWD is non-nil, do the block header search in forward direction;
otherwise in backward direction.

This function updates the local variable `modi/verilog-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"top\"
is returned and `modi/verilog-which-func-xtra' is updated to \"mod\" (short
for \"module\").

   module top ();
   ▯
   endmodule "
  (let (block-type block-name return-val) ;return-val will be nil by default
    (setq-local modi/verilog-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward modi/verilog-header-re nil :noerror)
              (re-search-backward modi/verilog-header-re nil :noerror))
        ;; Ensure that text in line or block comments is not incorrectly
        ;; parsed as a Verilog block header
        (when (not (equal (face-at-point) 'font-lock-comment-face))
          ;; (message "---- 1 ---- %s" (match-string 1))
          ;; (message "---- 2 ---- %s" (match-string 2))
          ;; (message "---- 3 ---- %s" (match-string 3))
          ;; (message "---- 4 ---- %s" (match-string 4))
          (setq block-type (match-string 1))
          (setq block-name (match-string 2))

          (when (and (stringp block-name)
                     (not (string-match modi/verilog-keywords-re
                                        block-name)))
            (setq-local modi/verilog-which-func-xtra
                        (cond
                         ((string= "class"     block-type) "class")
                         ((string= "clocking"  block-type) "clk")
                         ((string= "`define"   block-type) "macro")
                         ((string= "group"     block-type) "group")
                         ((string= "module"    block-type) "mod")
                         ((string= "interface" block-type) "if")
                         ((string= "package"   block-type) "pkg")
                         ((string= "sequence"  block-type) "seq")
                         (t (substring block-type 0 4)))) ;First 4 chars
            (setq return-val block-name)))))
    (when (featurep 'which-func)
      (modi/verilog-update-which-func-format))
    return-val))






(defun modi/verilog-block-end-comments-to-block-names ()
  "Convert valid block-end comments to ': BLOCK_NAME'.

Examples: endmodule // module_name             → endmodule : module_name
          endfunction // some comment          → endfunction // some comment
          endfunction // class_name::func_name → endfunction : func_name
          end // block: block_name             → end : block_name "
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward (concat "^"
                                      "\\(?1:[[:blank:]]*"
                                      modi/verilog-block-end-keywords-re
                                      "\\)"
                                      "[[:blank:]]*//[[:blank:]]*"
                                      "\\(\\(block:\\|"
                                      modi/verilog-identifier-re "[[:blank:]]*::\\)[[:blank:]]*\\)*"
                                      "\\(?2:" modi/verilog-identifier-re "\\)"
                                      "[[:blank:]]*$")
                              nil :noerror)
      ;; Make sure that the matched string after "//" is not a verilog
      ;; keyword.
      (when (not (string-match-p modi/verilog-keywords-re (match-string 2)))
        (replace-match "\\1 : \\2")))))

(add-hook 'verilog-mode-hook (lambda () (add-hook 'before-save-hook #'modi/verilog-block-end-comments-to-block-names nil :local)))




(provide 'verilog-utils)

;;; verilog-utils.el ends here
