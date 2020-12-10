;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
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


;;; Code beautifying
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
          (replace-regexp old-start new-start nil (region-beginning) (region-end))
          (replace-regexp old-end   new-end   nil (region-beginning) (region-end)))
      (progn
        (message "Removing blanks at the end...")
        (query-replace-regexp old-start new-start nil (point-min) (point-max))
        (query-replace-regexp old-end   new-end   nil (point-min) (point-max))))))


(defun larumbe/verilog-indent-current-module (&optional module)
  "Indent current module, the one pointed to by `which-func' (not instant)

For use programatically, an argument needs to be specified as current-module is determined by `which-func' and that takes time,
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
  "Align parenthesis PARAMETERS of current module, the one pointed to by `which-func' (not instant).
It will align parameters contained between module name and instance name.

For use programatically, an argument needs to be specified as current-module is determined by `which-func' and that takes time,
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
      (next-line 1) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward current-instance)))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Parameters aligned...")))


(defun larumbe/verilog-align-ports-current-module ()
  "Align parenthesis PORTS of current module, the one pointed to by `modi/verilog-find-module-instance'
It will only align ports, i.e., between instance name and end of instantiation."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-instance)
        (beg)
        (end))
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (save-excursion
      (re-search-backward (concat "\\_<" current-instance "\\_>"))
      (next-line 1) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward ");")))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Ports aligned...")))


(defun larumbe/verilog-beautify-current-module ()
  "Beautify current module (open parenthesis +indent + align)"
  (interactive)
  (save-excursion
    (larumbe/verilog-indent-current-module)
    (larumbe/verilog-align-ports-current-module)
    (larumbe/verilog-align-parameters-current-module)))


;;; Port connect/disconnect
(defvar larumbe/connect-disconnect-port-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)")
(defvar larumbe/connect-disconnect-conn-re "\\(?4:(\\(?5:.*\\))\\)?")
(defvar larumbe/connect-disconnect-not-found "No port detected at current line")

(defun larumbe/verilog-toggle-connect-port (force-connect)
  "Connect/disconnect port @ current line (regexp based).
If regexp detects that port is connected, then disconnect it. The other way round works the same.
If called with universal arg, `force-connect' parameter will force connection of current port, no matter it is connected/disconnected"
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
          (next-line 1))
      (progn ; No port found
        (goto-char start)
        (message larumbe/connect-disconnect-not-found)))))


(defun larumbe/verilog-connect-ports-recursively ()
  "Ask recursively for ports to be connected until no port is found at current line"
  (interactive)
  (while (not (string-equal (larumbe/verilog-toggle-connect-port t) larumbe/connect-disconnect-not-found))))


;;; Gtags
;; INFO: Global does not allow to find external definitions outside project root directory (probably due to security reasons).
;; In order to do so, there are 2 methods:
;;   - Use symbolic links to external directories.
;;   - Make use of GTAGSLIBPATH environment variable.
;; Associated thread: https://emacs.stackexchange.com/questions/13254/find-external-definition-with-gtags-or-ggtags
(defun larumbe/gtags-verilog-files-pwd-recursive (&optional exclude-re dir append)
  "Generate gtags.files for current directory, unless optional DIR is set.
If optional EXCLUDE-RE is set, delete paths with that regexp from generated file.
If DIR is not specified, use current-directory.
If APPEND is set, append directory files to already existing tags file. "
  (let (tags-dir)
    (if dir
        (setq tags-dir dir)
      (setq tags-dir default-directory))
    (larumbe/directory-files-recursively-to-file tags-dir "gtags.files" ".[s]?v[h]?$" append exclude-re)))


(defun larumbe/ggtags-create-verilog-tags-recursive ()
  "Create Verilog gtags.files for current directory.
Do not include SCons generated '*_targets' folders. "
  (interactive)
  (let ((exclude-re (concat (projectile-project-root) "[^/]+_targets")))
    (shell-command "touch GTAGS")
    (larumbe/gtags-verilog-files-pwd-recursive exclude-re)
    (ggtags-create-tags default-directory)))


;;; Misc
(defun larumbe/verilog-dirs-and-pkgs-of-open-buffers ()
  "Base content fetched from: https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
Returns a list of directories from current verilog opened files.
It also updates currently opened SystemVerilog packages."
  (let ((verilog-opened-dirs)
        (verilog-opened-pkgs)
        (pkg-regexp "^\\s-*\\(?1:package\\)\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)"))
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "verilog-mode")
          (add-to-list 'verilog-opened-dirs default-directory)
          (save-excursion
            (beginning-of-buffer)
            (when (re-search-forward pkg-regexp nil t)
              (add-to-list 'verilog-opened-pkgs (buffer-file-name)))))))
    `(,verilog-opened-dirs ,verilog-opened-pkgs)))  ; Return list of dirs and packages



(provide 'verilog-utils)

;;; verilog-utils.el ends here
