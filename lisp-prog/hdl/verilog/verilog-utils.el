;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'make-mode)
(require 'init-custom-functions)
(require 'which-func)
(require 'verilog-mode)
(require 'setup-verilog) ; Modi's setup
(require 'init-ggtags)


;; Inspired by kmodi's variables (`modi/verilog-identifier-re')
(defvar larumbe/newline-or-space-optional "\\(?:[[:blank:]\n]\\)*")
(defvar larumbe/newline-or-space-mandatory "\\(?:[[:blank:]\n]\\)+")
(defvar larumbe/verilog-identifier-re ;; Same as modi's one
      (concat "\\_<\\(?:"
              "\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)" ; simple identifier
              "\\|\\(?:\\\\[!-~]+\\)"           ; escaped identifier
              "\\)\\_>"))
(defvar larumbe/param-port-list "([^;]+?)")
(defvar larumbe/verilog-module-instance-re
      (concat "^[[:blank:]]*"
              "\\(?1:" larumbe/verilog-identifier-re "\\)" ;module name (subgroup 1)
              larumbe/newline-or-space-optional ; For modi its mandatory, but thats a problem since it could be: btd#(
              ;; optional port parameters
              "\\("
              "#" larumbe/newline-or-space-optional larumbe/param-port-list
              "\\([[:blank:]]*//.*?\\)*"  ;followed by optional comments
              "[^;\\./]+?"  ;followed by 'almost anything' before instance name
              "\\)*"
              "\\(?2:" larumbe/verilog-identifier-re "\\)" ;instance name (subgroup 2)
              ;; Added by Larumbe
              "\\s-*\\(\\[.*\\]\\)*"         ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
              larumbe/newline-or-space-optional
              "(" ; And finally .. the opening parenthesis `(' before port list
              ))

(defvar larumbe/verilog-module-instance-full-re ; INFO: Not used for the time being even though it worked for a while... regex too complex
      (concat larumbe/verilog-module-instance-re
              ;; Includes content inside parenthesis of instance. Currently not being used
              larumbe/newline-or-space-optional
              ;; "[^;]+?"  ;followed by 'almost anything' before instance name -> This one requires content between brackets (instances only)
              "[^;]*?"  ;followed by 'almost anything' before instance name -> This one does not require contents necessarily between brackets (instances+interfaces)
              ")"
              larumbe/newline-or-space-optional
              ";"
              ))

(defvar larumbe/verilog-token-re
  (regexp-opt '("module"
                "program"
                "package"
                "class"
                "function"
                "task"
                "initial"
                "always"
                "always_ff"
                "always_comb"
                "generate"
                "property"
                "sequence"
                ) 'symbols))



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
    (compile cmd)
    (larumbe/compilation-error-re-set "verilog-make")
    (larumbe/compilation-show-buffer)))


;;;; Code beautifying
(defun larumbe/verilog-clean-parenthesis-blanks ()
  "Cleans blanks inside parenthesis blocks (Verilog port connections).
If region is not used, then a query replacement is performed instead.
DANGER: It may wrongly detect some `old-end' regexp matches, but seems too complex for the effort..."
  (interactive)
  (let ((old-start "([ ]+\\(.*\\))")
        (new-start "(\\1)")
        (old-end "(\\([^ ]+\\)[ ]+)")
        (new-end "(\\1)"))
    (if (use-region-p)
        (progn
          (message "Removing blanks at the beginning...")
          (larumbe/replace-regexp old-start new-start (region-beginning) (region-end))
          (larumbe/replace-regexp old-end   new-end   (region-beginning) (region-end)))
      (message "Removing blanks at the end...")
      (query-replace-regexp old-start new-start nil (point-min) (point-max))
      (query-replace-regexp old-end   new-end   nil (point-min) (point-max)))))


(defun larumbe/verilog-indent-current-module (&optional module)
  "Indent current module, the one pointed to by `which-func'.

If used programatically perform a backwards regexp-search of MODULE
and start indentation at that point.
This is because current-module is determined by `which-func' and it takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module))
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (re-search-backward (concat "\\_<" current-module "\\_>"))
      ;; Mark region for the whole module
      (beginning-of-line)
      (set-mark (point))
      (re-search-forward larumbe/verilog-module-instance-re nil t)
      (backward-char)                            ; Point at instance opening parenthesis
      (electric-verilog-forward-sexp)            ; Point at instance closing parenthesis
      (end-of-line)
      (electric-verilog-tab))))


(defun larumbe/verilog-align-parameters-current-module (&optional module)
  "Align parameters of current module, the one pointed to by `which-func'.

Alignment is performed between module name and instance name.

If used programatically perform a backwards regexp-search of MODULE
and start indentation at that point.
This is because current-module is determined by `which-func' and it takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module)
        (current-instance)
        (beg)
        (end))
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (re-search-backward (concat "\\_<" current-module "\\_>"))
      (forward-line) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward current-instance)))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Parameters aligned...")))


(defun larumbe/verilog-align-ports-current-module ()
  "Align parenthesis ports of current module.
Current module is the one pointed to by `modi/verilog-find-module-instance'.

Alignment is performed between instance name and end of instantiation."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-instance)
        (beg)
        (end))
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (save-excursion
      (re-search-backward (concat "\\_<" current-instance "\\_>"))
      (forward-line) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward ");")))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Ports aligned...")))


(defun larumbe/verilog-beautify-current-module ()
  "Beautify current module (open parenthesis, indent and align)."
  (interactive)
  (save-excursion
    (larumbe/verilog-indent-current-module)
    (larumbe/verilog-align-ports-current-module)
    (larumbe/verilog-align-parameters-current-module)))


;;;; Port connect/disconnect
(defvar larumbe/connect-disconnect-port-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)")
(defvar larumbe/connect-disconnect-conn-re "\\(?4:(\\(?5:.*\\))\\)?")
(defvar larumbe/connect-disconnect-not-found "No port detected at current line")

(defun larumbe/verilog-toggle-connect-port (force-connect)
  "Toggle connect/disconnect port at current line.

If regexp detects that port is connected, then disconnect it.
The other way round works the same.

If called with universal arg, FORCE-CONNECT parameter will force connection
of current port, no matter it is connected/disconnected"
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
              (replace-match (concat "\\1.\\2\\3\(" sig "\)") t)))
          (goto-char start)
          (forward-line))
      (progn ; No port found
        (goto-char start)
        (message larumbe/connect-disconnect-not-found)))))


(defun larumbe/verilog-connect-ports-recursively ()
  "Connect ports of current instance recursively.
Ask for ports to be connected until no port is found at current line."
  (interactive)
  (while (not (string-equal (larumbe/verilog-toggle-connect-port t) larumbe/connect-disconnect-not-found))))


;;;; Gtags
(defun larumbe/ggtags-create-verilog-tags-recursive ()
  "Create Verilog gtags.files for current directory.

INFO: Exclude custom '*_targets' folders."
  (interactive)
  (let ((verilog-file-re "\\.[s]?v[h]?$")
        (exclude-re      "[^/]+_targets"))
    (larumbe/gtags-filelist-create verilog-file-re exclude-re)
    (larumbe/gtags-create-tags-async default-directory)))


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
          (setq verilog-opened-dirs (push default-directory verilog-opened-dirs))
          (save-excursion
            (goto-char (point-min))
            (when (re-search-forward pkg-regexp nil t)
              (setq verilog-opened-pkgs (push (buffer-file-name) verilog-opened-pkgs)))))))
    `(,verilog-opened-dirs ,verilog-opened-pkgs)))  ; Return list of dirs and packages



;; Own projects verilog timestamp header
(defvar larumbe/verilog-time-stamp-regex   "^// Last modified : ")
(defvar larumbe/verilog-time-stamp-pattern (concat larumbe/verilog-time-stamp-regex "%%$"))
(defvar larumbe/verilog-time-stamp-format  "%:y/%02m/%02d")

(defun larumbe/verilog-time-stamp-setup ()
  "Setup Time-stamp format for Verilog files."
  (setq-local time-stamp-pattern larumbe/verilog-time-stamp-pattern)
  (setq-local time-stamp-format  larumbe/verilog-time-stamp-format))



(defun larumbe/verilog-hook ()
  "Verilog hook."
  (setq larumbe/verilog-open-dirs (nth 0 (larumbe/verilog-dirs-and-pkgs-of-open-buffers)))
  (setq larumbe/verilog-open-pkgs (nth 1 (larumbe/verilog-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-library-directories larumbe/verilog-open-dirs) ; Verilog *AUTO* folders (could use `verilog-library-files' for files)
  (modify-syntax-entry ?` ".") ; Avoid including preprocessor tags while isearching. Requires `larumbe/electric-verilog-tab' to get back standard table to avoid indentation issues with compiler directives.
  (larumbe/verilog-time-stamp-setup)
  (larumbe/verilog-find-semicolon-in-instance-comments)
  (setq-local yas-indent-line 'fixed))





(provide 'verilog-utils)

;;; verilog-utils.el ends here
