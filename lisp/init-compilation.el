;;; init-compilation.el --- Compilation  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; The variable `larumbe/compilation-custom-regexp-sets' holds parser names
;; and their corresponding regexp-alist-alists.
;;
;; In order to extend it, just create the proper `larumbe/compilation-error-re-<program>'
;; and add its parser at `larumbe/compilation-custom-regexp-sets'.
;;
;; The function `larumbe/compilation-error-re-set' does all the logic.
;;
;; Plus, there are some functions to do interactive compilation with regexp
;; parsing.
;;
;;; Code:


(require 'popwin)
(require 'ansi-color) ; Buffer colorizing


(defvar larumbe/compilation-error-re-vivado
  '((vivado-error     "^\\(?1:^ERROR: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"            3   4   nil 2 nil (1 compilation-error-face))
    (vivado-error2    "^\\(?1:^ERROR:\\) "                                                        1   nil nil 2 nil)
    (vivado-critical  "^\\(?1:^CRITICAL WARNING: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)" 3   4   nil 1 nil (1 compilation-error-face))
    (vivado-critical2 "^\\(?1:^CRITICAL WARNING:\\) "                                             1   nil nil 1 nil)
    (vivado-warning   "^\\(?1:^WARNING: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"          3   4   nil 1 nil (1 compilation-warning-face))
    (vivado-warning2  "^\\(?1:^WARNING:\\) "                                                      1   nil nil 1 nil)
    (vivado-info      "^\\(?1:^INFO: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"             3   4   nil 0 nil (1 compilation-info-face))
    (vivado-info2     "^\\(?1:^INFO:\\) "                                                         1   nil nil 0 nil)))

;; Leveraged from verilog-mode (verilog-IES: Incisive Enterprise Simulator) and extended for UVM
(defvar larumbe/compilation-error-re-irun
  '((verilog-IES-fatal    "^[a-z]+: \\(?1:\\*F\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)" 2 3 nil 2 nil (1 compilation-error-face))
    (verilog-IES-fatal2   "^[a-z]+: \\(?1:\\*F\\),[0-9A-Z]+: " 1 nil nil 2 nil)
    (verilog-IES-error    "^[a-z]+: \\(?1:\\*E\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)" 2 3 nil 2 nil (1 compilation-error-face))
    (verilog-IES-error2   "^[a-z]+: \\(?1:\\*E\\),[0-9A-Z]+: " 1 nil nil 2 nil)
    (verilog-IES-warning  "^[a-z]+: \\(?1:\\*W\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)" 2 3 nil 1 nil (1 compilation-warning-face))
    (verilog-IES-warning2 "^[a-z]+: \\(?1:\\*W\\),[0-9A-Z]+: " 1 nil nil 1 nil)
    (verilog-IES-note     "^[a-z]+: \\(?1:\\*N\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)" 2 3 nil 0 nil (1 compilation-info-face))
    (verilog-IES-note2    "^[a-z]+: \\(?1:\\*N\\),[0-9A-Z]+: " 1 nil nil 0 nil)
    ;; UVM
    (uvm-fatal    "^\\(?1:UVM_FATAL\\) \\(?2:[a-zA-Z0-9\./_-]+\\)(\\(?3:[0-9]+\\))"   2 3 nil 2 nil (1 compilation-error-face))
    (uvm-fatal2   "^\\(?1:UVM_FATAL\\) @"   nil nil nil 2 nil (1 compilation-error-face))
    (uvm-error    "^\\(?1:UVM_ERROR\\) \\(?2:[a-zA-Z0-9\./_-]+\\)(\\(?3:[0-9]+\\))"   2 3 nil 2 nil (1 compilation-error-face))
    (uvm-error2   "^\\(?1:UVM_ERROR\\) @"   nil nil nil 2 nil (1 compilation-error-face))
    (uvm-warning  "^\\(?1:UVM_WARNING\\) \\(?2:[a-zA-Z0-9\./_-]+\\)(\\(?3:[0-9]+\\))" 2 3 nil 1 nil (1 compilation-warning-face))
    (uvm-warning2 "^\\(?1:UVM_WARNING\\) @" nil nil nil 1 nil (1 compilation-warning-face))
    (uvm-info     "^\\(?1:UVM_INFO\\) \\(?2:[a-zA-Z0-9\./_-]+\\)(\\(?3:[0-9]+\\))"    2 3 nil 0 nil (1 compilation-info-face))
    (uvm-info2    "^\\(?1:UVM_INFO\\) @"    nil nil nil 0 nil (1 compilation-info-face))))

;; Fetched from verilog-mode variable: `verilog-error-regexp-emacs-alist'.
(defvar larumbe/compilation-error-re-verilator
  '((verilator-error   "%?\\(Error\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"    3 4 nil 2 nil (1 compilation-error-face)   (2 compilation-line-face))
    (verilator-warning "%?\\(Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"  3 4 nil 1 nil (1 compilation-warning-face) (2 compilation-line-face))))

(defvar larumbe/compilation-error-re-iverilog
  '((iverilog-unsupported  "\\(?1:.*\\):\\(?2:[0-9]+\\):.*sorry:"            1 2 nil   0 nil (1 compilation-info-face) (2 compilation-line-face))
    (iverilog-warning      "\\(?1:.*\\):\\(?2:[0-9]+\\):.*warning:"          1 2 nil   1 nil (1 compilation-warning-face) (2 compilation-line-face))
    (iverilog-warning2     "^\\(?1:warning\\):"                              1 nil nil 1 nil)
    (iverilog-error        "\\(?1:.*\\):\\(?2:[0-9]+\\):.*error:"            1 2 nil   2 nil (1 compilation-error-face)   (2 compilation-line-face))
    (vvp-warning           "^\\(?1:WARNING\\): \\(?2:.*\\):\\(?3:[0-9]+\\):" 2 3 nil   1 nil (1 compilation-warning-face) (2 compilation-warning-face) (3 compilation-line-face))
    (vvp-error             "^\\(?1:ERROR\\): \\(?2:.*\\):\\(?3:[0-9]+\\):"   2 3 nil   2 nil (1 compilation-warning-face) (2 compilation-warning-face) (3 compilation-line-face))
    (vvp-info              "^\\(?1:LXT2 info\\):"                            1 nil nil 0 nil)))

(defvar larumbe/compilation-error-re-synopsys-dc
  '((dc-error     "\\(?1:^Error\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): "       2 3   nil 2 nil (1 compilation-error-face))
    (dc-error-2   "\\(?1:^Error\\): .*"                                                 1 nil nil 2 nil)
    (dc-warning   "\\(?1:^Warning\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): "     2 3   nil 1 nil (1 compilation-warning-face))
    (dc-warning-2 "\\(?1:^Warning\\): .*"                                               1 nil nil 1 nil)
    (dc-info      "\\(?1:^Information\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): " 2 3   nil 0 nil (1 compilation-info-face))
    (dc-info-2    "\\(?1:^Information\\): .*"                                           1 nil nil 0 nil)))

;; Adapted from compilation.el for Python tracebacks
(defvar larumbe/compilation-error-re-python
  '((python-tracebacks-and-caml "File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)?" 2 (3 . 4) (5 . 6) (7)) ; Some regexps where not detected on some SCons errors (original one did not have `?' at the end)
    (python-log-error   "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:ERROR\\) - "   3 nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
    (python-log-warning "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:WARNING\\) - " 3 nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
    (python-log-info    "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:INFO\\) - "    3 nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))))

(defvar larumbe/compilation-error-re-scons
  '((scons-target-cmd    "\\(?1:^[a-zA-Z_-]+\\)(\\(?2:.*\\))$" nil nil nil 0 nil (1 compilation-line-face) (2 compilation-info-face))
    (scons-target-err    "\\(?1:NOK\\)$"                         1 nil nil 2 nil (1 compilation-error-face))
    (scons-target-cw     "\\(?1:critical warning\\)$"            1 nil nil 1 nil (1 compilation-warning-face))
    (scons-target-ok     "\\(?1:OK\\)$"                          1 nil nil 0 nil (1 compilation-info-face))))

(defvar larumbe/compilation-error-re-pax
  '((pax-assert-err  "** \\(?1:assertion failure\\) at time \\(?2:[0-9.]+\\)"   1 nil nil 2 nil (2 compilation-line-face))
    (pax-tb-note     "\\(?1:^TB_NOTE\\) @ [0-9\.]+:"                            1 nil nil 0 nil)
    (pax-tb-debug    "\\(?1:^TB_DEBUG\\) @ [0-9\.]+:"                           1 nil nil 0 nil (1 compilation-line-face))
    (pax-tb-warning  "\\(?1:^TB_WARNING\\) @ [0-9\.]+:"                         1 nil nil 1 nil)
    (pax-tb-err      "\\(?1:^TB_ERROR\\) @ [0-9\.]+:"                           1 nil nil 2 nil)
    (pax-tb-fatal    "\\(?1:^TB_FATAL\\) @ [0-9\.]+:"                           1 nil nil 2 nil)
    (pax-perl-err    "\\(?1:^ERROR\\):"                                         1 nil nil 2 nil)
    (pax-perl-err2   "\\(?1:^ERROR\\)!"                                         1 nil nil 2 nil)
    (pax-gasearch    "^\\(?1:[0-9]+\\) \\(?2:[a-zA-Z0-9\\_\\-\\.\\/]+\\)+ \"\\(?3:[a-zA-Z0-9\\_\\-\\.]+\\)+\" \\(?4:[0-9]+\\)" 2 nil nil 2 nil (1 compilation-info-face) (3 compilation-warning-face) (4 compilation-info-face))))

(defvar larumbe/compilation-error-re-gcc
  '((gcc-warning "^\\(?1:[0-9a-zA-Z\/\._-]+\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\): \\(?4:warning\\):" 1 2 3 1 nil)
    (gcc-error   "^\\(?1:[0-9a-zA-Z\/\._-]+\\):\\(?2:[0-9]+\\):\\(?3:[0-9]+\\): \\(?4:error\\):"   1 2 3 2 nil)))


;; INFO: To be used with: `C-u M-x compile RET tail -f Log.txt'
;; Or just make a wrapper function to set up this debug config
(defvar larumbe/compilation-error-re-ableton
  '((ableton-error      "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptError:\\)"    nil nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
    (ableton-exception  "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:Exception:\\)"            nil nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
    (ableton-message    "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptMessage:\\)"  nil nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
    (ableton-others     "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\)"                                nil nil nil 0 2 (1 compilation-line-face))))



(defvar larumbe/compilation-custom-regexp-sets
  '(("verilog-make" . (larumbe/compilation-error-re-iverilog larumbe/compilation-error-re-verilator larumbe/compilation-error-re-vivado))
    ("vivado"       . (larumbe/compilation-error-re-vivado))
    ("irun"         . (larumbe/compilation-error-re-irun))
    ("verilator"    . (larumbe/compilation-error-re-verilator))
    ("iverilog"     . (larumbe/compilation-error-re-iverilog))
    ("synopsys-dc"  . (larumbe/compilation-error-re-synopsys-dc))
    ("scons"        . (larumbe/compilation-error-re-irun larumbe/compilation-error-re-vivado larumbe/compilation-error-re-scons larumbe/compilation-error-re-python))
    ("pax"          . (larumbe/compilation-error-re-irun larumbe/compilation-error-re-pax larumbe/compilation-error-re-gcc))
    ("ableton"      . (larumbe/compilation-error-re-python larumbe/compilation-error-re-ableton))))

(defvar larumbe/compilation-custom-regexp-active nil)



;;; Use-package setup
(use-package compile
  :ensure nil
  :bind (([f5]  . compile)
         ("C-*" . larumbe/compilation-show-buffer))
  :bind (:map compilation-mode-map
              ("r"   . rename-buffer)
              ("j"   . larumbe/recompile-with-regexp-alist)
              ("t"   . larumbe/compilation-threshold))
  :bind (:map comint-mode-map
              ("TAB" . completion-at-point) ; Similar to ansi-term (e.g. for vivado tcl-shell)
              ("C-j" . larumbe/compilation-interactive-recompile)) ; sandbox oriented
  :hook ((compilation-mode   . larumbe/compilation-hook)
         (compilation-filter . colorize-compilation-buffer))
  :commands (recompile
             larumbe/compilation-show-buffer
             larumbe/compilation-error-re-set
             larumbe/recompile-set-active-regexp-alist
             larumbe/compilation-interactive
             comint-send-string)
  :config
  (add-to-list 'popwin:special-display-config '(compilation-mode :stick t))

  ;; Compilation motion commands skip less important messages. The value can be either
  ;; 2 -- skip anything less than error,
  ;; 1 -- skip anything less than warning or
  ;; 0 -- don't skip any messages.
  (setq compilation-skip-threshold 2) ; Compilation error jumping settings

  (setq compilation-scroll-output 'first-error)

;;;; Defuns
  ;; Master function
  (defun larumbe/compilation-error-re-set (parser)
    "Sets variables `compilation-error-regexp-alist' and `compilation-error-regexp-alist-alist' according to parser."
    (interactive (list (completing-read "Select parser: " (mapcar 'car larumbe/compilation-custom-regexp-sets))))
    (let* ((regex-alist-quoted (cdr (assoc parser larumbe/compilation-custom-regexp-sets)))
           (regex-alist (apply 'append (mapcar
                                        (lambda (elm) (mapcar 'car (eval elm)))
                                        regex-alist-quoted)))
           (regex-alist-alist (apply 'append (mapcar
                                              (lambda (elm) (eval elm))
                                              regex-alist-quoted))))
      (when (boundp 'compilation-error-regexp-alist-alist)
        (setq compilation-error-regexp-alist regex-alist)
        (setq compilation-error-regexp-alist-alist regex-alist-alist))))



  (defun larumbe/compilation-show-buffer (&optional parser kill-wins)
    "Show custom compilation buffer.
Set *compilation* buffer regexp-alist-alist to its corresponding PARSER regexp.
If KILL-WINS is non-nil then delete every other window."
    (interactive)
    (delete-other-windows)
    (unless kill-wins
      (split-window-below)
      (other-window 1))
    (switch-to-buffer "*compilation*")
    (when parser
      (larumbe/compilation-error-re-set parser))
    (goto-char (point-max)))



  (defun larumbe/compilation-threshold ()
    (interactive)
    (let* ((choices '("error" "warning" "info"))
           (choice   (completing-read "Threshold: " choices)))
      (pcase choice
        ("error"   (setq compilation-skip-threshold 2))
        ("warning" (setq compilation-skip-threshold 1))
        ("info"    (setq compilation-skip-threshold 0)))))



  (defun larumbe/recompile-set-active-regexp-alist ()
    "Set current regexp-alist for EVERY *compilation* buffer.

INFO: Tried to set `larumbe/compilation-custom-regexp-active' locally to each
buffer, but it actually was more effort.  It is assumed that most of the time
work will be done with the same tool consecutively, i.e. there won't be constant
switches between Vivado and IES.  However, if it is set locally to each buffer,
every buffer would require confirmation."
    (interactive)
    (setq larumbe/compilation-custom-regexp-active (completing-read "Select compiler: " (mapcar 'car larumbe/compilation-custom-regexp-sets)))
    (message "Compilation Error Regexp set Globally to: %s" larumbe/compilation-custom-regexp-active))



  (defun larumbe/recompile-with-regexp-alist ()
    "Recompile current *compilation* buffer and set proper regexp-alist for different programs"
    (interactive)
    (when (not (bound-and-true-p larumbe/compilation-custom-regexp-active))
      (larumbe/recompile-set-active-regexp-alist))
    (recompile)
    (larumbe/compilation-error-re-set larumbe/compilation-custom-regexp-active)
    (goto-char (point-max)))



  (defun larumbe/compilation-log-add-re-header (&optional parser)
    "Add elisp header to current visited log file.
Open it in compilation mode with custom regexp parsing.

If passed PARSER, set corresponding regexp to be evaluated at the header."
    (interactive)
    (unless parser
      (setq parser (completing-read "Select parser: " (mapcar 'car larumbe/compilation-custom-regexp-sets))))
    (let ((header (concat "-*- mode: compilation; default-directory: \"" default-directory "\"; eval: (" (symbol-name 'larumbe/compilation-error-re-set) " \"" parser "\") -*-")))
      (read-only-mode -1)
      (goto-char (point-min))
      (open-line 2)
      (insert header)
      (save-buffer)
      (read-only-mode 1)
      (revert-buffer nil t)))


  (defun larumbe/compilation-hook ()
    ;; Do not enable linum-mode since it slows down large compilation buffers
    (setq truncate-lines t)
    ;; Split compilation vertically: https://stackoverflow.com/questions/966191/how-can-i-get-the-compilation-buffer-on-the-bottom-rather-than-on-the-right-in-em/
    (setq-local split-width-threshold nil))



  ;; Print elapsed time in compilation buffer
  ;; https://emacs.stackexchange.com/questions/31493/print-elapsed-time-in-compilation-buffer
  (defvar larumbe/compilation-start-time)

  (defun larumbe/compilation-start-hook (proc)
    (setq-local larumbe/compilation-start-time (current-time)))

  (defun larumbe/compilation-finish-function (buf why)
    (when (boundp 'larumbe/compilation-start-time) ; When finding definitions/references with ggtags, somehow compilation is used under the hood, and `larumbe/compilation-start-time' is not defined (nor is required)
      (let* ((elapsed (time-subtract nil larumbe/compilation-start-time))
             (msg (format "Compilation elapsed time: %s" (format-seconds "%Y, %D, %H, %M, %z%S" elapsed))))
	(save-excursion
          (goto-char (point-max))
          (insert "\n")
          (insert msg)))))

  ;; Add hooks outside of use-package because `compilation-finish-functions' name does not end in -hook
  (add-hook 'compilation-start-hook       #'larumbe/compilation-start-hook)
  (add-hook 'compilation-finish-functions #'larumbe/compilation-finish-function)



  ;; https://stackoverflow.com/questions/13397737/ansi-coloring-in-compilation-mode
  (defun colorize-compilation-buffer ()
    "Apply color to comint buffers (e.g. convert '\033[0;31m' to red)."
    (ansi-color-apply-on-region compilation-filter-start (point)))


;;;; Interactive comint library
  (defvar larumbe/compilation-interactive-buildcmd nil
    "Buffer-local variable used to determine the executed build command.
It's main use is to allow for recompiling easily.")

  (defun larumbe/compilation-interactive (command bufname parser)
    "Create a `compilation-mode' comint shell almost identical to *ansi-term*.
It will have the same environment and aliases without the need of setting
`shell-command-switch' to '-ic'.

Execute COMMAND in the buffer.  Buffer will be renamed to BUFNAME.
Regexp parsing of PARSER is applied.

Useful to spawn a *tcl-shell* with Vivado regexps, or to init sandbox modules."
    (when (get-buffer bufname)
      (pop-to-buffer bufname)
      (error (concat "Buffer " bufname " already in use!")))
    (compile command t)
    (select-window (get-buffer-window "*compilation*"))
    (goto-char (point-max))
    (setq truncate-lines t)
    (larumbe/compilation-error-re-set parser)
    (rename-buffer bufname))


  (defun larumbe/compilation-interactive-sandbox (initcmd buildcmd bufname parser)
    "Initialize a comint Bash sandbox with INITCMD and execute BUILDCMD next.
Buffer will be renamed to BUFNAME, and regexp parsing depending on PARSER.

Acts as wrapper for `larumbe/compilation-interactive'with an additional build command.

INFO: With some minor tweaks could be extended to allow a list
of commands to be executed by sending them through `comint-send-string'"
    (let ((command initcmd)
          (proc))
      (larumbe/compilation-interactive command bufname parser)
      (setq-local larumbe/compilation-interactive-buildcmd buildcmd)
      (setq proc (get-buffer-process bufname))
      (comint-send-string proc buildcmd)
      (comint-send-string proc "\n")))


  (defun larumbe/compilation-interactive-recompile ()
    "Will only work in `comint-mode' after `larumbe/compilation-interactive-sandbox' was executed.
Makes use of buffer-local variable `larumbe/compilation-interactive-buildcmd' to rebuild a target."
    (interactive)
    (unless larumbe/compilation-interactive-buildcmd
      (error "No interactive recompile command was set"))
    (let (proc)
      (when (string= major-mode "comint-mode")
        (setq proc (get-buffer-process (current-buffer)))
        (comint-send-string proc larumbe/compilation-interactive-buildcmd)
        (comint-send-string proc "\n")))))



;;;; Package providing

(provide 'init-compilation)

;;; init-compilation.el ends here
