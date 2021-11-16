;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'make-mode)
(require 'which-func)
(require 'verilog-mode)
(require 'setup-verilog) ; Modi's setup
(require 'init-ggtags)
(require 'time-stamp)

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


;;;; Code beautifying
(defun larumbe/verilog-align-ports-current-module ()
  "Align parenthesis ports of current module.
Current module is the one pointed to by `modi/verilog-find-module-instance'.

Alignment is performed between instance name and end of instantiation."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module)
        (current-instance)
        (beg)
        (end)
        (re-beg-pos)
        (re-end-pos))
    (setq current-module modi/verilog-which-func-xtra)
    (setq current-instance (modi/verilog-find-module-instance))
    (save-excursion
      (setq re-beg-pos (re-search-backward (concat "\\_<" current-instance "\\_>") nil t))
      (forward-line) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq re-end-pos (re-search-forward ");" nil t))
      (setq end re-end-pos))
    (if (and re-beg-pos re-end-pos)
        (progn
          (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
          (message "Ports of %s aligned..." current-module))
      (message "Could not align ports!"))))


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
        (end)
        (re-beg-pos)
        (re-end-pos))
    (setq current-instance (modi/verilog-find-module-instance))
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (setq re-beg-pos (re-search-backward (concat "\\_<" current-module "\\_>") nil t))
      (forward-line) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (when current-instance
        (setq re-end-pos (re-search-forward current-instance nil t)))
      (setq end re-end-pos))
    (if (and re-beg-pos re-end-pos)
        (progn
          (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
          (message "Parameters of %s  aligned..." current-module))
      (message "Could not align parameters!"))))


(defun larumbe/verilog-indent-current-module (&optional module)
  "Indent current module, the one pointed to by `which-func'.

If used programatically perform a backwards regexp-search of MODULE
and start indentation at that point.
This is because current-module is determined by `which-func' and it takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module)
        (re-beg-pos)
        (re-end-pos)))
  (if module
      (setq current-module module)
    (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
  (save-excursion
    (setq re-beg-pos (re-search-backward (concat "\\_<" current-module "\\_>") nil t))
    (beginning-of-line)
    (setq re-end-pos (re-search-forward larumbe/verilog-module-instance-re nil t)))
  (if (and re-beg-pos re-end-pos)
      (save-excursion
        (goto-char re-beg-pos)
        (beginning-of-line)
        (set-mark (point))
        (goto-char re-end-pos)
        (backward-char)                 ; Point at instance opening parenthesis
        (electric-verilog-forward-sexp) ; Point at instance closing parenthesis
        (end-of-line)
        (electric-verilog-tab)
        (message "Indented %s" current-module))
    (message "Point is not inside a module instantiation")))


(defun larumbe/verilog-beautify-current-module ()
  "Beautify current module (open parenthesis, indent and align)."
  (interactive)
  (save-excursion
    ;; Leave indentation for the end to avoid conflicts with
    ;; point position due to update delay in which-func
    (larumbe/verilog-align-ports-current-module)
    (larumbe/verilog-align-parameters-current-module)
    (larumbe/verilog-indent-current-module)))


(defun larumbe/verilog-beautify-current-buffer ()
  "Beautify current buffer.

Indent whole buffer, beautify every instantiated module and
remove blanks in port connections."
  (interactive)
  (save-excursion
    (indent-region (point-min) (point-max))
    (larumbe/verilog-clean-port-blanks)
    (goto-char (point-min))
    (while (larumbe/find-verilog-module-instance-fwd)
      (larumbe/verilog-beautify-current-module))))


(defun larumbe/verilog-beautify-files (files)
  "Beautify Verilog FILES.

FILES is a list of strings containing the paths to the files to beautify."
  (dolist (file files)
    (unless (file-exists-p file)
      (error "File %s does not exist! Aborting..." file)))
  (dolist (file files)
    (with-temp-file file
      (verilog-mode)
      (insert-file-contents file)
      (larumbe/verilog-beautify-current-buffer)
      (untabify-trailing-whitespace)
      (write-file file))))


(defun larumbe/verilog-beautify-files-current-dir ()
  "Beautify Verilog files on current dired directory."
  (interactive)
  (unless (string= major-mode "dired-mode")
    (error "Must be used in dired!"))
  (let ((files (directory-files-recursively default-directory "\\.[s]?v[h]?$")))
    (larumbe/verilog-beautify-files files)))


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


;;;; Timestamp
(defvar larumbe/verilog-time-stamp-profiles '("work" "personal"))
(defvar larumbe/verilog-time-stamp-active-profile "work") ; Defaults to work

(defun larumbe/verilog-time-stamp-set-profile ()
  "Set active profile for verilog timestamp: work or personal."
  (interactive)
  (let ((profile (completing-read "Set timestamp profile: " larumbe/verilog-time-stamp-profiles)))
    (setq larumbe/verilog-time-stamp-active-profile profile)))


(defun larumbe/verilog-time-stamp-update ()
  "Update `time-stamp' variables depending on current active profile."
  (if (string= larumbe/verilog-time-stamp-active-profile "work")
      (larumbe/verilog-time-stamp-work-update) ; Work
    (larumbe/verilog-time-stamp-pers-update))) ; Personal


;;;;; Work
(defvar larumbe/verilog-time-stamp-work-boundary-re "\\(?1:[ ]?\\)\\* ------------------------------------------------------------------------------")
(defvar larumbe/verilog-time-stamp-work-created-re  "\\(?1:^* \\)\\(?2:[a-z]+\\)\\(?3:[ ]+\\)\\(?4:[^ ]+\\)\\(?5:[ ]+\\)\\(?6:Created\\)")
(defvar larumbe/verilog-time-stamp-work-modified-re "\\(?1:^* \\)\\(?2:[a-z]+\\)\\(?3:[ ]+\\)\\(?4:[^ ]+\\)\\(?5:[ ]+\\)\\(?6:Modified\\)")

(defvar larumbe/verilog-time-stamp-work-start  (concat "* " user-login-name "  "))
(defvar larumbe/verilog-time-stamp-work-format "%Y/%m/%d")
(defvar larumbe/verilog-time-stamp-work-end    "   Modified")


(defun larumbe/verilog-time-stamp-work-buffer-end-pos ()
  "Return position of point at the end of the buffer timestamp.
Return nil if no timestamp structure was found."
  (save-excursion
    (goto-char (point-min))
    (re-search-forward larumbe/verilog-time-stamp-work-boundary-re nil t)
    (re-search-forward larumbe/verilog-time-stamp-work-created-re nil t)
    (re-search-forward larumbe/verilog-time-stamp-work-boundary-re nil t)))


(defun larumbe/verilog-time-stamp-work-new-entry ()
  "Create new time-stamp entry at header."
  (interactive)
  (let (initial-blank
        pos)
    (save-excursion
      (setq pos (larumbe/verilog-time-stamp-work-buffer-end-pos))
      (if pos
          (progn
            (goto-char pos)
            (larumbe/verilog-time-stamp-work-buffer-end-pos)
            (setq initial-blank (match-string-no-properties 1))
            (beginning-of-line)
            (open-line 1)
            (insert (concat initial-blank larumbe/verilog-time-stamp-work-start))
            (insert (format-time-string larumbe/verilog-time-stamp-work-format))
            (insert larumbe/verilog-time-stamp-work-end))
        (message "Could not find proper time-stamp structure!")))))


(defun larumbe/verilog-time-stamp-work-update ()
  "Update the 'Modified' entry `time-stamp.'"
  (save-excursion
    (goto-char (point-min))
    (when (larumbe/verilog-time-stamp-work-buffer-end-pos) ; Activate time-stamp if structure is present
      (setq-local time-stamp-start  larumbe/verilog-time-stamp-work-start)
      (setq-local time-stamp-format larumbe/verilog-time-stamp-work-format)
      (setq-local time-stamp-end    larumbe/verilog-time-stamp-work-end))))


;;;;; Personal
(defvar larumbe/verilog-time-stamp-pers-regex   "^// Last modified : ")
(defvar larumbe/verilog-time-stamp-pers-pattern (concat larumbe/verilog-time-stamp-pers-regex "%%$"))
(defvar larumbe/verilog-time-stamp-pers-format  "%:y/%02m/%02d")


(defun larumbe/verilog-time-stamp-pers-update ()
  "Setup `time-stamp' format for Verilog files."
  (setq-local time-stamp-pattern larumbe/verilog-time-stamp-pers-pattern)
  (setq-local time-stamp-format  larumbe/verilog-time-stamp-pers-format))



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





(provide 'verilog-utils)

;;; verilog-utils.el ends here
