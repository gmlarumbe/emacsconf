;;; verilog-flycheck.el --- Verilog Flycheck  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'flycheck)
(require 'verilog-mode)
(require 'verilog-utils)



(defvar larumbe/flycheck-verilator-include-path nil)
(defvar larumbe/flycheck-active-linter nil) ; Flycheck will automaticall set its default, avoiding potential errors when executables are not found


(defun larumbe/verilog-flycheck-hook ()
  "Set Verilog flycheck options."
  (flycheck-select-checker larumbe/flycheck-active-linter)
  (setq larumbe/flycheck-verilator-include-path larumbe/verilog-open-dirs))

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
       (add-to-list 'larumbe/verilog-project-pkg-list pkg)))
   larumbe/verilog-open-pkgs)
  larumbe/verilog-project-pkg-list)     ; Return pkg-list


(defun larumbe/verilog-flycheck-mode (&optional uarg)
  "`flycheck-mode' Verilog wrapper function.
If called with UARG, select among available linters."
  (interactive "P")
  (let ((linters '("verilator" "iverilog"))
        (active-linter))
    (if uarg
        (progn
          (pcase (completing-read "Select linter: " linters)
            ("verilator" (setq active-linter 'verilog-verilator))
            ("iverilog"  (setq active-linter 'verilog-iverilog)))
          (setq larumbe/flycheck-active-linter active-linter)
          (flycheck-select-checker active-linter))
      (larumbe/verilog-update-project-pkg-list)
      (call-interactively #'flycheck-mode))))


;;; Verilator override
(flycheck-define-checker verilog-verilator
  "A Verilog syntax checker using the Verilator Verilog HDL simulator.

See URL `https://www.veripool.org/wiki/verilator'."
  :command ("verilator" "--lint-only" "-Wall"
            (option-list "-I" larumbe/flycheck-verilator-include-path concat)
            (option-list "" larumbe/verilog-project-pkg-list concat)
            source)
  :error-patterns
  ((warning line-start "%Warning-" (zero-or-more not-newline) ": "
            (file-name) ":" line ": " (message) line-end)
   (error line-start "%Error: " (file-name) ":"
          line ": " (message) line-end))
  :modes verilog-mode)


;;; Iverilog
(flycheck-define-checker verilog-iverilog
  "A Verilog syntax checker using Icarus Verilog.

See URL `http://iverilog.icarus.com/'"

  ;; INFO: Use `-i' flag to ignore missing modules for current buffer.
  ;; If a 'project mode' was to be used by means of library includes with -y flag, then there are kown limitations with iverilog:
  ;;   - The command line -y flag will not search for .sv extensions, even though the -g2012 flag is set.
  ;;   - The +libext+.sv will only work with COMMAND FILES, not with command line arguments.
  ;;      - That means that a file that specifies the libraries/plusargs should be used with the -c COMMAND_FILE command line argument.
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
