;;; verilog-tools.el --- Verilog Tools  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;; Lint, Compilation and Simulation Tools
;; INFO: Discarding the following `verilog-set-compile-command' variables:
;; - `verilog-linter:' replaced by FlyCheck with opened buffers as additional arguments, plus custom project parsing functions
;; - `verilog-simulator': replaced by XSim and ncsim sim project funcions
;; - `verilog-compiler': replaced by Vivado elaboration/synthesis project functions
;; - `verilog-preprocessor': `larumbe/verilog-preprocess' wrapper of verilog-mode internal function' does the trick
;; - `verilog-coverage' still not implemented as there are not many free alternatives...


;;;; Preprocessor
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


;;;; Iverilog/verilator Makefile development
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
  "Prompts to available previous Makefile targets and compiles then with various verilog regexps."
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
    (larumbe/custom-error-regexp-set-emacs
     (append iverilog-error-regexp-emacs-alist-alist
             verilator-error-regexp-emacs-alist-alist
             vivado-error-regexp-emacs-alist-alist))
    (larumbe/show-custom-compilation-buffers)))


(provide 'verilog-tools)

;;; verilog-tools.el ends here
