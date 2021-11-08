;;; verilog-flycheck.el --- Verilog Flycheck  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'flycheck)
(require 'verilog-mode)
(require 'verilog-utils)


(defvar larumbe/flycheck-verilator-include-path nil)
(defvar larumbe/flycheck-active-linter nil) ; Flycheck will automatically set its default, avoiding potential errors when executables are not found


(defun larumbe/verilog-flycheck-hook ()
  "Set Verilog flycheck options."
  (flycheck-select-checker larumbe/flycheck-active-linter)
  (setq larumbe/flycheck-verilator-include-path larumbe/verilog-open-dirs))


(defun larumbe/verilog-flycheck-mode (&optional uarg)
  "`flycheck-mode' Verilog wrapper function.
If called with UARG, select among available linters.

Disable function `eldoc-mode' if flycheck is enabled
to avoid minibuffer collisions."
  (interactive "P")
  (let ((linters '("verilator" "iverilog" "hal"))
        (active-linter))
    (if uarg
        (progn
          (pcase (completing-read "Select linter: " linters)
            ("verilator"
             (setq active-linter 'verilog-verilator))
            ("iverilog"
             (setq active-linter 'verilog-iverilog))
            ("hal"
             (setq active-linter 'verilog-cadence-hal)
             (larumbe/xrun-hal-script-create)))
          (setq larumbe/flycheck-active-linter active-linter)
          (flycheck-select-checker active-linter)
          (message "Linter set to: %s " larumbe/flycheck-active-linter))
      ;; No uarg
      (larumbe/verilog-update-project-pkg-list)
      (larumbe/flycheck-eldoc-toggle)
      (when (and (equal larumbe/flycheck-active-linter 'verilog-cadence-hal)
                 (equal flycheck-mode t))
        (message "Cadence HAL linting...")))))




;;;; Cadence HAL
(defvar larumbe/xrun-hal-directory   "/tmp")
(defvar larumbe/xrun-hal-log-name    "xrun.log")
(defvar larumbe/xrun-hal-script-name "hal.sh")

(defvar larumbe/xrun-hal-log-path    (larumbe/path-join larumbe/xrun-hal-directory larumbe/xrun-hal-log-name))
(defvar larumbe/xrun-hal-script-path (larumbe/path-join larumbe/xrun-hal-directory larumbe/xrun-hal-script-name))
(defvar larumbe/xrun-hal-script-code (concat "#!/bin/bash
args=\"${@}\"
xrun -hal $args && cat " larumbe/xrun-hal-log-path "
"))

(defun larumbe/xrun-hal-directory-fn (_checker)
  "Return directory where hal is executed.
xcelium.d (INCA_libs) and lint logs will be saved at this path."
  (let ((dir larumbe/xrun-hal-directory))
    dir))

(defun larumbe/xrun-hal-script-create ()
  "Create HAL wrapper script according to `larumbe/xrun-hal-script-code'.

This is needed because the output of HAL is written to a logfile and
flycheck parses stdout (didn't find the way to redirect xrun output to stdout).

Plus, the :command keyword of `flycheck-define-command-checker' assumes each
of the strings are arguments, so if something such as \"&&\" \"cat\" is used to
try to output the log, it would throw a xrun fatal error since
\"&&\" would not be recognized as a file."
  (let ((file larumbe/xrun-hal-script-path))
    (unless (file-exists-p larumbe/xrun-hal-script-path)
      (with-temp-buffer
        (insert larumbe/xrun-hal-script-code)
        (write-file file)
        (set-file-modes file #o755)))))


;; Similar to `flycheck-define-checker' but it's a defun instead of a macro.
;; This allows the use of evaluated variables (`larumbe/xrun-hal-script-path' and
;; `larumbe/xrun-hal-log-path') inside the first string of the keyword argument :command
;;
;; The only difference with `flycheck-define-checker' is that this one requires
;; keyword arguments to be quoted.
(flycheck-define-command-checker 'verilog-cadence-hal
  "A Verilog syntax checker using Cadence HAL."
  :command `(,larumbe/xrun-hal-script-path
             "-timescale"
             "1ns/1ps"
             "-l"
             ,larumbe/xrun-hal-log-path
             (option-list "" larumbe/verilog-project-pkg-list concat)
             source-original)
  :working-directory #'larumbe/xrun-hal-directory-fn
  :error-patterns
  ;; Check `larumbe/compilation-error-re-xrun'
  '((info    (zero-or-more not-newline) ": *N," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end)
    (warning (zero-or-more not-newline) ": *W," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end)
    (error   (zero-or-more not-newline) ": *E," (zero-or-more not-newline) "(" (file-name) "," line "|" column "): " (message) line-end))
  :modes 'verilog-mode)



;;;; Verilator override
(flycheck-define-checker verilog-verilator
  "A Verilog syntax checker using the Verilator Verilog HDL simulator.

See URL `https://www.veripool.org/wiki/verilator'."
  :command ("verilator" "--lint-only" "-Wall" "-Wno-fatal"
            "--bbox-unsup" ; Blackbox unsupported language features: avoids errors on verification sources
            (option-list "-I" larumbe/flycheck-verilator-include-path concat) ; -I searchs for includes
            (option-list "-y" larumbe/flycheck-verilator-include-path)        ; -y searchs for modules
            (option-list "" larumbe/verilog-project-pkg-list concat)
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
            (option-list "" larumbe/verilog-project-pkg-list concat)
            source)
  :error-patterns
  ((info    (file-name) ":" line ":" (zero-or-more not-newline) "sorry:" (message) line-end) ; Unsupported
   (warning (file-name) ":" line ":" (zero-or-more not-newline) "warning:" (message) line-end)
   (error   (file-name) ":" line ":" (zero-or-more not-newline) "error:"   (message) line-end)
   (error   (file-name) ":" line ":" (message) line-end) ; 'syntax error' message (missing package)
   )
  :modes verilog-mode)


(provide 'verilog-flycheck)

;;; verilog-flycheck.el ends here
