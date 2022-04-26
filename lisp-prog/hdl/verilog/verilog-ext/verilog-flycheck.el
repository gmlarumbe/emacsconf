;;; verilog-flycheck.el --- Verilog Flycheck  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'flycheck)
(require 'verilog-mode)
(require 'verilog-utils)


(defvar verilog-ext-flycheck-verilator-include-path nil)
(defvar verilog-ext-flycheck-active-linter nil) ; Flycheck will automatically set its default, avoiding potential errors when executables are not found



(defun verilog-ext-flycheck-extra-actions-pre (linter)
  "Extra actions to perform for speficic LINTER to work properly before enabling flycheck."
  (pcase linter
    ('verilog-verible
     (verilog-ext-verible-rules-fmt))
    ('verilog-hal
     (unless (and (executable-find "xrun")
                  (executable-find "hal"))
       (error "Could not find 'xrun' and 'hal' in $PATH"))
     (verilog-ext-xrun-hal-script-create))))


(defun verilog-ext-flycheck-extra-actions-post ()
  "Extra actions to perform for `verilog-ext-flycheck-active-linter' after enabling flycheck."
  (when (and (equal verilog-ext-flycheck-active-linter 'verilog-cadence-hal)
             (equal flycheck-mode t))
    (message "Cadence HAL linting...")))


(defun verilog-ext-flycheck-select-linter (&optional linter)
  "Select LINTER for verilog flycheck."
  (unless linter
    (setq linter (intern (completing-read "Select linter: " '(verilog-verible
                                                              verilog-verilator
                                                              verilog-iverilog
                                                              verilog-cadence-hal
                                                              verilog-svlint) nil t))))
  (verilog-ext-flycheck-extra-actions-pre linter)
  (setq verilog-ext-flycheck-active-linter linter)
  (when (string= major-mode "verilog-mode") ; Allow for setting up the linter in the elisp init
    (flycheck-select-checker linter))       ; This line needs to be executed only in a verilog buffer
  (message "Linter set to: %s " verilog-ext-flycheck-active-linter)
  ;; Return 'linter value
  linter)


(defun verilog-ext-flycheck-mode (&optional uarg)
  "`flycheck-mode' Verilog wrapper function.
If called with UARG, select among available linters.

Disable function `eldoc-mode' if flycheck is enabled
to avoid minibuffer collisions."
  (interactive "P")
  (when buffer-read-only
    (error "Flycheck does not work on read-only buffers!"))
  (if uarg
      (verilog-ext-flycheck-select-linter)
    ;; No uarg
    (verilog-ext-verilog-update-project-pkg-list)
    (verilog-ext-flycheck-eldoc-toggle)
    (verilog-ext-flycheck-extra-actions-post)))




;;;; Cadence HAL
(defvar verilog-ext-xrun-hal-directory   "/tmp")
(defvar verilog-ext-xrun-hal-log-name    "xrun.log")
(defvar verilog-ext-xrun-hal-script-name "hal.sh")

(defvar verilog-ext-xrun-hal-log-path    (larumbe/path-join verilog-ext-xrun-hal-directory verilog-ext-xrun-hal-log-name))
(defvar verilog-ext-xrun-hal-script-path (larumbe/path-join verilog-ext-xrun-hal-directory verilog-ext-xrun-hal-script-name))
(defvar verilog-ext-xrun-hal-script-code (concat "#!/bin/bash
args=\"${@}\"
xrun -hal $args
cat " verilog-ext-xrun-hal-log-path "
"))

(defun verilog-ext-hal-directory-fn (_checker)
  "Return directory where hal is executed.
xcelium.d (INCA_libs) and lint logs will be saved at this path."
  (let ((dir verilog-ext-xrun-hal-directory))
    dir))

(defun verilog-ext-hal-script-create ()
  "Create HAL wrapper script according to `verilog-ext-hal-script-code'.

This is needed because the output of HAL is written to a logfile and
flycheck parses stdout (didn't find the way to redirect xrun output to stdout).

Plus, the :command keyword of `flycheck-define-command-checker' assumes each
of the strings are arguments, so if something such as \"&&\" \"cat\" is used to
try to output the log, it would throw a xrun fatal error since
\"&&\" would not be recognized as a file."
  (let ((file verilog-ext-xrun-hal-script-path))
    (unless (file-exists-p verilog-ext-xrun-hal-script-path)
      (with-temp-buffer
        (insert verilog-ext-hal-script-code)
        (write-file file)
        (set-file-modes file #o755)))))

(defun verilog-ext-hal-open-log ()
  "Open xrun log file for debug."
  (interactive)
  (find-file verilog-ext-xrun-hal-log-path))


;; Similar to `flycheck-define-checker' but it's a defun instead of a macro.
;; This allows the use of evaluated variables (`verilog-ext-xrun-hal-script-path' and
;; `verilog-ext-xrun-hal-log-path') inside the first string of the keyword argument :command
;;
;; The only difference with `flycheck-define-checker' is that this one requires
;; keyword arguments to be quoted.
(flycheck-define-command-checker 'verilog-cadence-hal
  "A Verilog syntax checker using Cadence HAL."
  :command `(,verilog-ext-xrun-hal-script-path
             "-bb_unbound_comp"
             "-timescale" "1ns/1ps"
             "-l" ,verilog-ext-xrun-hal-log-path
             "+libext+.v+.vh+.sv+.svh"
             (option-list "-incdir" verilog-ext-flycheck-verilator-include-path)
             (option-list "-y" verilog-ext-flycheck-verilator-include-path)
             (option-list "" verilog-ext-verilog-project-pkg-list concat)
             source-original)
  :working-directory #'verilog-ext-hal-directory-fn
  :error-patterns
  ;; Check `verilog-ext-compilation-error-re-xrun'
  '((info    (zero-or-more not-newline) ": *N," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end)
    (warning (zero-or-more not-newline) ": *W," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end)
    (error   (zero-or-more not-newline) ": *E," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end))
  :modes 'verilog-mode)



;;;; Verilator override
(flycheck-define-checker verilog-verilator
  "A Verilog syntax checker using the Verilator Verilog HDL simulator.

See URL `https://www.veripool.org/wiki/verilator'.

INFO: Verilator does not support ignoring missing modules, as Iverilog does.
  - https://github.com/verilator/verilator/issues/2835
However, verilator supports SystemVerilog far better than Iverilog does.

For RTL seems a good solution. For simulation it has many issues
with 'Define or directive not defined' due to difficulties finding defines
and includes (e.g. for UVM macros).
"
  :command ("verilator" "--lint-only" "-Wall" "-Wno-fatal"
            "--bbox-unsup" ; Blackbox unsupported language features: avoids errors on verification sources
            "--bbox-sys"  ;  Blackbox unknown $system calls
            ;; https://verilator.org/guide/latest/exe_verilator.html
            ;;  - The three flags -y, +incdir+<dir> and -I<dir> have similar effect;
            ;;  +incdir+<dir> and -y are fairly standard across Verilog tools while -I<dir> is used by many C++ compilers.
            (option-list "-I" verilog-ext-flycheck-verilator-include-path concat) ; -I searchs for includes and modules
            (option-list "" verilog-ext-verilog-project-pkg-list concat)
            source)
  :error-patterns
  ;; INFO: Required to add a column for latests version of Verilator!
  ;; TODO: Send a bug report/pull request at some point
  ((warning line-start "%Warning-" (zero-or-more not-newline) ": " (file-name) ":" line ":" column ": " (message) line-end)
   (error   line-start "%Error: "                                  (file-name) ":" line ":" column ": " (message) line-end)
   (error   line-start "%Error-"   (zero-or-more not-newline) ": " (file-name) ":" line ":" column ": " (message) line-end))
  :modes verilog-mode)


;;;; Iverilog
(flycheck-define-checker verilog-iverilog
  "A Verilog syntax checker using Icarus Verilog.

See URL `http://iverilog.icarus.com/'"

  ;; INFO: Use `-i' flag to ignore missing modules for current buffer.
  ;;
  ;; If a 'project mode' was to be used by means of library includes with -y flag, then there are known limitations with iverilog:
  ;;   - The command line -y flag will not search for .sv extensions, even though the -g2012 flag is set.
  ;;   - The +libext+.sv will only work with command files (equivalent to -f in xrun), not with command line arguments.
  ;;      - That means that a file that specifies the libraries/plusargs should be used with the -c <COMMAND_FILE> command line argument.
  ;;   - Since this is a just a linter for current file, other files errors/warnings would appear at the beginning of the buffer.

  :command ("iverilog" "-g2012" "-Wall" "-gassertions" "-t" "null" "-i"
            (option-list "" verilog-ext-verilog-project-pkg-list concat)
            source)
  :error-patterns
  ((info    (file-name) ":" line ":" (zero-or-more not-newline) "sorry:" (message) line-end) ; Unsupported
   (warning (file-name) ":" line ":" (zero-or-more not-newline) "warning:" (message) line-end)
   (error   (file-name) ":" line ":" (zero-or-more not-newline) "error:"   (message) line-end)
   (error   (file-name) ":" line ":" (message) line-end) ; 'syntax error' message (missing package)
   )
  :modes verilog-mode)



;;;; Verible
(defvar verilog-ext-verible-rules nil
  "List of strings containing rules. Use - or + prefixes depending on enabling/disabling of rules.
https://chipsalliance.github.io/verible/lint.html")

(defvar verilog-ext-verible-rules-flycheck nil
  "Used as a flycheck argument depending on `verilog-ext-verible-rules'")

(defun verilog-ext-verible-rules-fmt ()
  "Format `verilog-ext-verible-rules' to pass correct arguments to --rules flycheck checker."
  (setq verilog-ext-verible-rules-flycheck (mapconcat #'identity verilog-ext-verible-rules ",")))


(flycheck-define-checker verilog-verible
  " The Verible project's main mission is to parse SystemVerilog (IEEE 1800-2017)
(as standardized in the SV-LRM) for a wide variety of applications, including developer tools.

See URL `https://github.com/chipsalliance/verible'.

So far seems the best option to find syntax errors quickly without compiling
on single testbench files."
  ;; INFO: From the documentation:
  ;; Syntax errors cannot be waived. A common source of syntax errors is if the file is not a standalone Verilog program
  ;; as defined by the LRM, e.g. a body snippet of a module, class, task, or function. In such cases, the parser can be
  ;; directed to treat the code as a snippet by selecting a parsing mode, which looks like a comment near the top-of-file
  ;; like // verilog_syntax: parse-as-module-body.
  ;;
  ;; NOTE: Since regexps are common for error/warning/infos, it is important to declare errors before warnings below!

  :command ("verible-verilog-lint"
            (option "--rules=" verilog-ext-verible-rules-flycheck concat)
            source)
  :error-patterns
  ((error    (file-name) ":" line ":" column (zero-or-more "-") (zero-or-more digit) ":" (zero-or-more blank) "syntax error at " (message) line-end)
   (warning  (file-name) ":" line ":" column (zero-or-more "-") (zero-or-more digit) ":" (zero-or-more blank)                    (message) line-end))
  :modes verilog-mode)


;;;; Others
(flycheck-define-checker verilog-svlint
  "A Verilog syntax checker using svlint.

A bit rudimentary, with not many rules but enough to check for parsing errors.
Could be useful for small RTL self-contained blocks (i.e, almost never).

However, fails dramatically if defines are not found.

See URL `https://github.com/dalance/svlint'"
  :command ("svlint"
            "-1" ; one-line output
            "--ignore-include"
            (option-list "-i" verilog-ext-flycheck-verilator-include-path)
            source)
  :error-patterns
  ((warning line-start "Fail"  (zero-or-more blank) (file-name) ":" line ":" column (zero-or-more blank) (zero-or-more not-newline) "hint: " (message) line-end)
   (error   line-start "Error" (zero-or-more blank) (file-name) ":" line ":" column (zero-or-more blank) (zero-or-more not-newline) "hint: " (message) line-end))
  :modes verilog-mode)



(provide 'verilog-flycheck)

;;; verilog-flycheck.el ends here
