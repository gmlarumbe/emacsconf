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
;; - `verilog-preprocessor': `verilog-ext-preprocess' wrapper of verilog-mode internal function' does the trick
;; - `verilog-coverage' still not implemented as there are not many free alternatives...


;;;;; Preprocessor
(defun verilog-ext-preprocess ()
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
(defun verilog-ext-makefile-create ()
  "Create Iverilog/verilator Yasnippet based Makefile.
Create it only if in a projectile project and the Makefile does not exist already."
  (interactive)
  (let (file)
    (if (projectile-project-p)
        (if (file-exists-p (setq file (concat (projectile-project-root) "Makefile")))
            (error "File %s already exists!" file)
          (progn
            (find-file file)
            (verilog-ext-hydra-yasnippet "verilog")))
      (error "Not in a projectile project!"))))


(defun verilog-ext-makefile-compile-project ()
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
(defvar verilog-ext-connect-disconnect-port-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)")
(defvar verilog-ext-connect-disconnect-conn-re "\\(?4:(\\(?5:.*\\))\\)?")
(defvar verilog-ext-connect-disconnect-not-found "No port detected at current line")

(defun verilog-ext-toggle-connect-port (force-connect)
  "Toggle connect/disconnect port at current line.

If regexp detects that port is connected then disconnect it
and viceversa.

If called with universal arg, FORCE-CONNECT parameter will force connection
of current port, no matter if it is connected/disconnected"
  (interactive "P")
  (let* ((case-fold-search verilog-case-fold)
         (port-regex verilog-ext-connect-disconnect-port-re)
         (conn-regex verilog-ext-connect-disconnect-conn-re)
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
        (message verilog-ext-connect-disconnect-not-found)))))


(defun verilog-ext-connect-ports-recursively ()
  "Connect ports of current instance recursively.

Ask for ports to be connected until no port is found at current line."
  (interactive)
  (while (not (equal (verilog-ext-toggle-connect-port t) verilog-ext-connect-disconnect-not-found))
    (verilog-ext-toggle-connect-port t)))



(defvar verilog-ext-verilog-clean-port-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)(\\(?4:[ ]*\\)\\(?5:[^ ]+\\)\\(?6:[ ]*\\))"
  "Information about different capture groups:
Group 1: Beginning of line blanks
Group 2: Port name (after dot connection)
Group 3: Blanks after identifier
Group 4: Blanks after beginning of port connection '('
Group 5: Name of connection
Group 6: Blanks after end of port connection ')'")

(defun verilog-ext-verilog-clean-port-blanks ()
  "Cleans blanks inside port connections of current buffer."
  (interactive)
  (let ((old-re verilog-ext-verilog-clean-port-re)
        (new-re "\\1.\\2\\3\(\\5\)"))
    (larumbe/replace-regexp-whole-buffer old-re new-re)
    (message "Removed blanks from current buffer port connections.")))



;;;; Misc
;; https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
(defvar verilog-ext-verilog-open-dirs nil
  "List with directories of current opened `verilog-mode' buffers.
Used for verilog AUTO libraries, flycheck and Verilog-Perl hierarchy.")
(defvar verilog-ext-verilog-open-pkgs nil
  "List of currently opened SystemVerilog packages.")
(defvar verilog-ext-verilog-project-pkg-list nil
  "List of current open packages at projectile project.")


(defun verilog-ext-verilog-dirs-and-pkgs-of-open-buffers ()
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


(defun verilog-ext-verilog-update-project-pkg-list ()
  "Update currently open packages on `verilog-ext-verilog-project-pkg-list'.

Only packages within current projectile project are added.
To be used with vhier/flycheck.

INFO: Limitations:
 - Packages included as sources might not be in the proper order.
 - Some sorting method could be used in the future:
   - Extracting them from buffer file but in the order they have been
     opened and reverse sorting, for example..."
  (setq verilog-ext-verilog-project-pkg-list nil) ; Reset list
  (mapc
   (lambda (pkg)
     (when (string-prefix-p (projectile-project-root) pkg)
       (unless (member pkg verilog-ext-verilog-project-pkg-list)
         (push pkg verilog-ext-verilog-project-pkg-list))))
   verilog-ext-verilog-open-pkgs)
  ;; Return pkg-list
  verilog-ext-verilog-project-pkg-list)



;;;; Others
(defun verilog-ext-verilog-find-semicolon-in-instance-comments ()
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



(defun verilog-ext-find-module-instance (&optional fwd)
  "Return the module instance name within which the point is currently.

If FWD is non-nil, do the verilog module/instance search in forward direction;
otherwise in backward direction.

This function updates the local variable `verilog-ext-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"u_adder\"
is returned and `verilog-ext-which-func-xtra' is updated to \"adder\".

   adder u_adder
   (
    ▯
    );"
  (let (instance-name return-val)   ;return-val will be nil by default
    (setq-local verilog-ext-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward verilog-ext-header-re nil :noerror)
              (re-search-backward verilog-ext-header-re nil :noerror))
        ;; Ensure that text in line or block comments is not incorrectly
        ;; parsed as a module instance
        (when (not (equal (face-at-point) 'font-lock-comment-face))
          ;; (message "---- 1 ---- %s" (match-string 1))
          ;; (message "---- 2 ---- %s" (match-string 2))
          ;; (message "---- 3 ---- %s" (match-string 3))
          (setq-local verilog-ext-which-func-xtra (match-string 1)) ;module name
          (setq instance-name (match-string 2)) ;Instance name

          (when (and (stringp verilog-ext-which-func-xtra)
                     (string-match verilog-ext-keywords-re
                                   verilog-ext-which-func-xtra))
            (setq-local verilog-ext-which-func-xtra nil))

          (when (and (stringp instance-name)
                     (string-match verilog-ext-keywords-re
                                   instance-name))
            (setq instance-name nil))

          (when (and verilog-ext-which-func-xtra
                     instance-name)
            (setq return-val instance-name)))))
    (when (featurep 'which-func)
      (modi/verilog-update-which-func-format))
    return-val))


(defun verilog-ext-get-header (&optional fwd)
  "Function to return the name of the block (module, class, package,
function, task, `define) under which the point is currently present.

If FWD is non-nil, do the block header search in forward direction;
otherwise in backward direction.

This function updates the local variable `verilog-ext-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"top\"
is returned and `verilog-ext-which-func-xtra' is updated to \"mod\" (short
for \"module\").

   module top ();
   ▯
   endmodule "
  (let (block-type block-name return-val) ;return-val will be nil by default
    (setq-local verilog-ext-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward verilog-ext-header-re nil :noerror)
              (re-search-backward verilog-ext-header-re nil :noerror))
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
                     (not (string-match verilog-ext-keywords-re
                                        block-name)))
            (setq-local verilog-ext-which-func-xtra
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


;;;; Hooks
(defun verilog-ext-verilog-hook ()
  "Verilog hook."
  (setq verilog-ext-verilog-open-dirs (nth 0 (verilog-ext-verilog-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-ext-verilog-open-pkgs (nth 1 (verilog-ext-verilog-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-library-directories verilog-ext-verilog-open-dirs) ; Verilog *AUTO* folders (could use `verilog-library-files' for files)
  (setq verilog-ext-flycheck-verilator-include-path verilog-ext-verilog-open-dirs)
  (flycheck-select-checker verilog-ext-flycheck-active-linter)
  (modify-syntax-entry ?` ".") ; Avoid including preprocessor tags while isearching. Requires `verilog-ext-electric-verilog-tab' to get back standard table to avoid indentation issues with compiler directives.
  (verilog-ext-verilog-time-stamp-update)
  (verilog-ext-verilog-find-semicolon-in-instance-comments)
  (setq-local yas-indent-line 'fixed))


;;;; Modi
(defvar modi/verilog-block-end-keywords '("end"
                                          "join" "join_any" "join_none"
                                          "endchecker"
                                          "endclass"
                                          "endclocking"
                                          "endconfig"
                                          "endfunction"
                                          "endgroup"
                                          "endinterface"
                                          "endmodule"
                                          "endpackage"
                                          "endprimitive"
                                          "endprogram"
                                          "endproperty"
                                          "endsequence"
                                          "endtask")
  "Verilog/SystemVerilog block end keywords.
IEEE 1800-2012 SystemVerilog Section 9.3.4 Block names.")

(defvar modi/verilog-block-end-keywords-re
  (regexp-opt modi/verilog-block-end-keywords 'symbols)
  "Regexp to match the Verilog/SystemVerilog block end keywords.
See `modi/verilog-block-end-keywords' for more.")


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
      (when (not (string-match-p verilog-ext-keywords-re (match-string 2)))
        (replace-match "\\1 : \\2")))))

(add-hook 'verilog-mode-hook (lambda () (add-hook 'before-save-hook #'modi/verilog-block-end-comments-to-block-names nil :local)))




(provide 'verilog-utils)

;;; verilog-utils.el ends here
