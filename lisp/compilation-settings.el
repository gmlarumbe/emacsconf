;;; compilation-settings.el --- Compilation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(defvar larumbe/custom-compilation-regexp-sets '("verilog-make" "vivado" "irun" "verilator" "iverilog" "scons" "python" "pax"))
(defvar larumbe/custom-compilation-regexp-active nil)

(defvar vivado-error-regexp-emacs-alist-alist
  '((vivado-error     "^\\(?1:^ERROR: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"            3   4   nil 2 nil (1 compilation-error-face))
    (vivado-error2    "^\\(?1:^ERROR:\\) "                                                        1   nil nil 2 nil)
    (vivado-critical  "^\\(?1:^CRITICAL WARNING: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)" 3   4   nil 2 nil (1 compilation-error-face))
    (vivado-critical2 "^\\(?1:^CRITICAL WARNING:\\) "                                             1   nil nil 2 nil)
    (vivado-warning   "^\\(?1:^WARNING: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"          3   4   nil 1 nil (1 compilation-warning-face))
    (vivado-warning2  "^\\(?1:^WARNING:\\) "                                                      1   nil nil 1 nil)
    (vivado-info      "^\\(?1:^INFO: \\)\\(?2:.*\\[\\(?3:.*\\):\\(?4:[0-9]+\\)\\]\\)"             3   4   nil 0 nil (1 compilation-info-face))
    (vivado-info2     "^\\(?1:^INFO:\\) "                                                         1   nil nil 0 nil)
    ))

;; Leveraged from verilog-mode (verilog-IES: Incisive Enterprise Simulator)
(defvar irun-error-regexp-emacs-alist-alist
  '((verilog-IES-fatal    "^[a-z]+: \\(?1:\\*F\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)" 2 3 nil 2 nil (1 compilation-error-face))
    (verilog-IES-fatal2   "^[a-z]+: \\(?1:\\*F\\),[0-9A-Z]+: " 1 nil nil 2 nil)
    (verilog-IES-error    "^[a-z]+: \\(?1:\\*E\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)" 2 3 nil 2 nil (1 compilation-error-face))
    (verilog-IES-error2   "^[a-z]+: \\(?1:\\*E\\),[0-9A-Z]+: " 1 nil nil 2 nil)
    (verilog-IES-warning  "^[a-z]+: \\(?1:\\*W\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)" 2 3 nil 1 nil (1 compilation-warning-face))
    (verilog-IES-warning2 "^[a-z]+: \\(?1:\\*W\\),[0-9A-Z]+: " 1 nil nil 1 nil)
    (verilog-IES-note     "^[a-z]+: \\(?1:\\*N\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)" 2 3 nil 0 nil (1 compilation-info-face))
    (verilog-IES-note2    "^[a-z]+: \\(?1:\\*N\\),[0-9A-Z]+: " 1 nil nil 0 nil)
    ))

;; Fetched from verilog-mode variable: `verilog-error-regexp-emacs-alist'.
(defvar verilator-error-regexp-emacs-alist-alist
  '((verilator-warning "%?\\(Error\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"    3 4 nil 2 nil (1 compilation-error-face) (2 compilation-line-face))
    (verilator-error   "%?\\(Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"  3 4 nil 1 nil (1 compilation-warning-face) (2 compilation-line-face))
    ))

(defvar iverilog-error-regexp-emacs-alist-alist
  '((iverilog-unsupported  "\\(?1:.*\\):\\(?2:[0-9]+\\):.*sorry:"            1 2 nil   0 nil (1 compilation-info-face) (2 compilation-line-face))
    (iverilog-warning      "\\(?1:.*\\):\\(?2:[0-9]+\\):.*warning:"          1 2 nil   1 nil (1 compilation-warning-face) (2 compilation-line-face))
    (iverilog-warning2     "^\\(?1:warning\\):"                              1 nil nil 1 nil)
    (iverilog-error        "\\(?1:.*\\):\\(?2:[0-9]+\\):.*error:"            1 2 nil   2 nil (1 compilation-error-face)   (2 compilation-line-face))
    (vvp-warning           "^\\(?1:WARNING\\): \\(?2:.*\\):\\(?3:[0-9]+\\):" 2 3 nil   1 nil (1 compilation-warning-face) (2 compilation-warning-face) (3 compilation-line-face))
    (vvp-error             "^\\(?1:ERROR\\): \\(?2:.*\\):\\(?3:[0-9]+\\):"   2 3 nil   2 nil (1 compilation-warning-face) (2 compilation-warning-face) (3 compilation-line-face))
    (vvp-info              "^\\(?1:LXT2 info\\):"                            1 nil nil 0 nil)
    ))

(defvar synopsys-dc-error-regexp-emacs-alist-alist
  '((dc-error     "\\(?1:^Error\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): "       2 3   nil 2 nil (1 compilation-error-face))
    (dc-error-2   "\\(?1:^Error\\): .*"                                                 1 nil nil 2 nil)
    (dc-warning   "\\(?1:^Warning\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): "     2 3   nil 1 nil (1 compilation-warning-face))
    (dc-warning-2 "\\(?1:^Warning\\): .*"                                               1 nil nil 1 nil)
    (dc-info      "\\(?1:^Information\\):  \\(?2:[0-9a-zA-Z./_-]+\\):\\(?3:[0-9]+\\): " 2 3   nil 0 nil (1 compilation-info-face))
    (dc-info-2    "\\(?1:^Information\\): .*"                                           1 nil nil 0 nil)
    ))

;; Adapted from compilation.el for Python tracebacks
(defvar python-error-regexp-emacs-alist-alist
  '((python-tracebacks-and-caml "File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)?" 2 (3 . 4) (5 . 6) (7)) ; Some regexps where not detected on some SCons errors (original one did not have `?' at the end)
    (python-log-error   "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:ERROR\\) - "   3 nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
    (python-log-warning "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:WARNING\\) - " 3 nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
    (python-log-info    "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:INFO\\) - "    3 nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
    ))

(defvar scons-error-regexp-emacs-alist-alist
  '((scons-target-cmd    "\\(?1:^[a-zA-Z_-]+\\)(\\[\"\\(?2:.*\\)\"\\],"   2 nil nil 0 nil (1 compilation-line-face))
    (scons-target-err    "\\(?1:NOK\\)$"                                  1 nil nil 2 nil (1 compilation-error-face))
    (scons-target-cw     "\\(?1:critical warning\\)$"                     1 nil nil 2 nil (1 compilation-warning-face))
    (scons-target-ok     "\\(?1:OK\\)$"                                   1 nil nil 0 nil (1 compilation-info-face))
    ))

(defvar pax-error-regexp-emacs-alist-alist
  '((pax-assert-err  "** \\(?1:assertion failure\\) at time \\(?2:[0-9.]+\\)"   1 nil nil 2 nil (2 compilation-line-face))
    ))


;; INFO: To be used with: `C-u M-x compile RET tail -f Log.txt'
;; Or just make a wrapper function to set up this debug config
(defvar ableton-error-regexp-emacs-alist-alist
  '((ableton-error      "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptError:\\)"    nil nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
    (ableton-exception  "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:Exception:\\)"            nil nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
    (ableton-message    "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptMessage:\\)"  nil nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
    (ableton-others     "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\)"                                nil nil nil 0 2 (1 compilation-line-face))
    ))



;;; Use-package setup
(use-package compile
  :ensure nil
  :bind (:map compilation-mode-map
              ("r"   . rename-buffer)
              ("j"   . larumbe/recompile-with-regexp-alist)
              ("t"   . larumbe/compilation-threshold)
              ("C-(" . larumbe/show-only-vivado-warnings))
  :bind (:map comint-mode-map
              ("TAB" . completion-at-point)                  ; Similar to ansi-term (e.g. for vivado tcl-shell)
              ("C-j" . larumbe/compilation-interactive-recompile)) ; sandbox oriented
  :hook ((compilation-mode . my-compilation-hook))
  :commands (recompile
             larumbe/show-custom-compilation-buffers
             larumbe/custom-error-regexp-set-emacs
             larumbe/recompile-set-active-regexp-alist
             larumbe/vivado-error-regexp-set-emacs
             larumbe/irun-error-regexp-set-emacs
             larumbe/verilator-error-regexp-set-emacs
             larumbe/iverilog-error-regexp-set-emacs
             larumbe/synopsys-dc-error-regexp-set-emacs
             larumbe/scons-error-regexp-set-emacs
             larumbe/python-error-regexp-set-emacs
             larumbe/pax-error-regexp-set-emacs
             larumbe/compilation-interactive
             comint-send-string)
  :config
  (add-to-list 'popwin:special-display-config '(compilation-mode :stick t))

  ;; Compilation motion commands skip less important messages. The value can be either
  ;; 2 -- skip anything less than error,
  ;; 1 -- skip anything less than warning or
  ;; 0 -- don't skip any messages.
  (setq compilation-skip-threshold 2) ; Compilation error jumping settings


  (defun larumbe/show-only-vivado-warnings ()
    "Filter *compilation* buffer to parse only Vivado warnings and critical warnings"
    (interactive)
    (select-window (get-buffer-window "*compilation*"))
    (setq truncate-lines t)
    (goto-char (point-min))
    (setq inhibit-read-only t)
    (keep-lines "WARNING")
    (setq inhibit-read-only nil)
    (goto-char (point-max)))


  (defun larumbe/show-custom-compilation-buffers (&optional regexp-alist-alist kill-wins)
    "Show custom compilation buffers.
If first argument is set then provide it wiith custom regexp to parse the compilation buffer.
If second argument is set then delete every other window."
    (interactive)
    (delete-other-windows)
    (unless kill-wins
      (split-window-below)
      (other-window 1))
    (switch-to-buffer "*compilation*")
    (when regexp-alist-alist
      (larumbe/custom-error-regexp-set-emacs regexp-alist-alist))
    (goto-char (point-max)))


  (defun larumbe/compilation-threshold ()
    (interactive)
    (let* ((choices '("error" "warning" "info"))
           (choice   (completing-read "Threshold: " choices)))
      (pcase choice
        ("error"   (setq compilation-skip-threshold 2))
        ("warning" (setq compilation-skip-threshold 1))
        ("info"    (setq compilation-skip-threshold 0)))))


  ;; Master function
  (defun larumbe/custom-error-regexp-set-emacs (ce-re-alist-alist)
    "Sets variables `compilation-error-regexp-alist' and `compilation-error-regexp-alist-alist' according to parameter"
    (interactive)
    (when (boundp 'compilation-error-regexp-alist-alist)
      (setq compilation-error-regexp-alist (mapcar 'car ce-re-alist-alist)) ; Fetch first element of list of lists
      (setq compilation-error-regexp-alist-alist ce-re-alist-alist)))


  (defun larumbe/recompile-set-active-regexp-alist ()
    "Set current regexp-alist for EVERY *compilation* buffer.

INFO: Tried to set `larumbe/custom-compilation-regexp-active' locally to each
buffer,but it actually was more effort.  It is assumed that most of the time
work will be done with the same tool consecutively, i.e. there won't be constant
switches between Vivado and IES.  However, if it is set locally to each buffer,
every buffer would require confirmation."
    (interactive)
    (setq larumbe/custom-compilation-regexp-active (completing-read "Select compiler: " larumbe/custom-compilation-regexp-sets))
    (message "Compilation Error Regexp set Globally to: %s" larumbe/custom-compilation-regexp-active))


  (defun larumbe/recompile-with-regexp-alist ()
    "Recompile current *compilation* buffer and set proper regexp-alist for different programs"
    (interactive)
    (when (not (bound-and-true-p larumbe/custom-compilation-regexp-active))
      (larumbe/recompile-set-active-regexp-alist))
    (recompile)
    (pcase larumbe/custom-compilation-regexp-active
      ("verilog-make" (larumbe/custom-error-regexp-set-emacs (append iverilog-error-regexp-emacs-alist-alist
                                                                     verilator-error-regexp-emacs-alist-alist
                                                                     vivado-error-regexp-emacs-alist-alist)))
      ("vivado"       (larumbe/vivado-error-regexp-set-emacs))
      ("irun"         (larumbe/irun-error-regexp-set-emacs))
      ("verilator"    (larumbe/verilator-error-regexp-set-emacs))
      ("iverilog"     (larumbe/iverilog-error-regexp-set-emacs))
      ("dc-compiler"  (larumbe/synopsys-dc-error-regexp-set-emacs))
      ("scons"        (larumbe/scons-error-regexp-set-emacs))
      ("python"       (larumbe/python-error-regexp-set-emacs))
      ("pax"          (larumbe/pax-error-regexp-set-emacs)))
    (goto-char (point-max)))


  (defun larumbe/vivado-error-regexp-set-emacs ()
    "Only takes Vivado Errors regexps into account."
    (interactive)
    (larumbe/custom-error-regexp-set-emacs vivado-error-regexp-emacs-alist-alist))

  (defun larumbe/irun-error-regexp-set-emacs ()
    "Only takes Cadence IES regexps into account. "
    (interactive)
    (larumbe/custom-error-regexp-set-emacs irun-error-regexp-emacs-alist-alist))

  (defun larumbe/verilator-error-regexp-set-emacs ()
    "Takes Verilator regexps into account. "
    (interactive)
    (larumbe/custom-error-regexp-set-emacs verilator-error-regexp-emacs-alist-alist))

  (defun larumbe/iverilog-error-regexp-set-emacs ()
    "Takes Iverilog regexps into account."
    (interactive)
    (larumbe/custom-error-regexp-set-emacs iverilog-error-regexp-emacs-alist-alist))

  (defun larumbe/synopsys-dc-error-regexp-set-emacs ()
    "Only takes Synopsys Design Compiler regexps into account."
    (interactive)
    (larumbe/custom-error-regexp-set-emacs synopsys-dc-error-regexp-emacs-alist-alist))

  (defun larumbe/scons-error-regexp-set-emacs ()
    "Takes Vivado, Irun, SCons and python regexps into account."
    (interactive)
    (larumbe/custom-error-regexp-set-emacs
     (append
      irun-error-regexp-emacs-alist-alist
      vivado-error-regexp-emacs-alist-alist
      scons-error-regexp-emacs-alist-alist
      python-error-regexp-emacs-alist-alist)))

  (defun larumbe/pax-error-regexp-set-emacs ()
    "Takes Irun and some others regexps into account."
    (interactive)
    (larumbe/custom-error-regexp-set-emacs
     (append
      irun-error-regexp-emacs-alist-alist
      pax-error-regexp-emacs-alist-alist)))

  (defun larumbe/ableton-error-regexp-set-emacs ()
    "Takes Ableton and python regexps into account."
    (interactive)
    (larumbe/custom-error-regexp-set-emacs
     (append
      python-error-regexp-emacs-alist-alist
      ableton-error-regexp-emacs-alist-alist)))


  (defun my-compilation-hook ()
    (setq truncate-lines t)) ; Do not enable linum-mode since it slows down large compilation buffers


;;;; Interactive comint library
  (defvar larumbe/compilation-interactive-buildcmd nil
    "Buffer-local variable used to determine the executed build command.
It's main use is to allow for recompiling easily.")

  (defun larumbe/compilation-interactive (command bufname re-func)
    "Create a `compilation-mode' comint shell almost identical to *ansi-term*.
It will have the same environment and aliases without the need of setting
`shell-command-switch' to '-ic'.

Execute COMMAND in the buffer.  Buffer will be renamed to BUFNAME.
Regexp parsing function RE-FUNC is applied.

Useful to spawn a *tcl-shell* with Vivado regexps, or to init sandbox modules."
    (when (get-buffer bufname)
      (pop-to-buffer bufname)
      (error (concat "Buffer " bufname " already in use!")))
    (compile command t)
    (select-window (get-buffer-window "*compilation*"))
    (goto-char (point-max))
    (setq truncate-lines t)
    (funcall re-func)
    (rename-buffer bufname))


  (defun larumbe/compilation-interactive-sandbox (initcmd buildcmd bufname re-func)
    "Initialize a comint Bash sandbox with INITCMD and execute BUILDCMD next.
Buffer will be renamed to BUFNAME, and regexp parsing depending on RE-FUNC.

Acts as wrapper for `larumbe/compilation-interactive'with an additional build command.

INFO: With some minor tweaks could be extended to allow a list
of commands to be executed by sending them through `comint-send-string'"
    (let ((command initcmd)
          (proc))
      (larumbe/compilation-interactive command bufname re-func)
      (setq-local larumbe/compilation-interactive-buildcmd buildcmd)
      (setq proc (get-buffer-process bufname))
      (comint-send-string proc buildcmd)
      (comint-send-string proc "\n")))


  (defun larumbe/compilation-interactive-recompile ()
    "Will only work in `comint-mode' after `larumbe/compilation-interactive-sandbox' was executed.
Makes use of buffer-local variable `larumbe/compilation-interactive-buildcmd' to rebuild a target."
    (interactive)
    (let (proc)
      (when (string= major-mode "comint-mode")
        (setq proc (get-buffer-process (current-buffer)))
        (comint-send-string proc larumbe/compilation-interactive-buildcmd)
        (comint-send-string proc "\n")))))



;;;; Package providing

(provide 'compilation-settings)

;;; compilation-settings.el ends here
