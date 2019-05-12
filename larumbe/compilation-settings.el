;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;      COMPILATION-MODE Settings            ;;
;;                                           ;;
;; - Allows for process output parsing     - ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Variable settings
(setq compilation-skip-threshold 2) ; Compilation error jumping settings
    ;; Compilation motion commands skip less important messages. The value can be either
    ;; 2 -- skip anything less than error,
    ;; 1 -- skip anything less than warning or
    ;; 0 -- don't skip any messages.


;;; Hooks
;; INFO: Do not enable linum-mode since it slows down large compilation buffers
(defun my-compilation-hook ()
  (setq truncate-lines t)
  )
(add-hook 'compilation-mode-hook 'my-compilation-hook)
(define-key compilation-mode-map (kbd "r") 'rename-buffer)
(define-key compilation-mode-map (kbd "j") 'larumbe/recompile-with-regexp-alist)
(define-key compilation-mode-map (kbd "C-(") 'larumbe/show-only-vivado-warnings)

;;; Compilation-mode related functions
;;;; Filtering
(defun larumbe/show-only-vivado-warnings ()
  "Filter *compilation* buffer to parse only Vivado warnings and critical warnings"
  (interactive)
  (select-window (get-buffer-window "*compilation*")) ; Select compilation buffer
  (setq truncate-lines t)
  (beginning-of-buffer)
  (setq inhibit-read-only t)
  (keep-lines "WARNING")
  (setq inhibit-read-only nil)
  (end-of-buffer))

;;;; Resizing/regexp
(defun show-custom-compilation-buffers()
  (interactive)
  (delete-other-windows)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*compilation*")
  (end-of-buffer)
  (shrink-window 18)
  )

(defun show-custom-compilation-buffers-vivado()
  (interactive)
  (delete-other-windows)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*compilation*")
  (larumbe/vivado-error-regexp-set-emacs) ; Sets compilation-error-regexp-alist-alist temporarily for the current compilation buffer
  (end-of-buffer)
  (shrink-window 10)
  )

(defun show-custom-compilation-buffers-verilator()
  (interactive)
  (delete-other-windows)
  (split-window-below)
  (other-window 1)
  (switch-to-buffer "*compilation*")
  (larumbe/verilator-error-regexp-set-emacs) ; Sets compilation-error-regexp-alist-alist temporarily for the current compilation buffer
  (end-of-buffer)
  (shrink-window 10)
  )


;;; Compilation error regexp alist
;;;; Common
(setq larumbe/custom-compilation-regexp-sets '("vivado" "irun" "scons" "verilator")) ; Used for custom recompile (edited by hand)
(setq larumbe/custom-compilation-regexp-active nil)                                  ; Current active compilation regexp

;; Recompiling with regexp (active profile needs to be modified manually once set... this should be changed somehow in the future)
(defun larumbe/recompile-set-active-regexp-alist ()
  "Set current regexp-alist for *compilation* buffer"
  (interactive)
  (setq larumbe/custom-compilation-regexp-active (completing-read "Select compiler: " larumbe/custom-compilation-regexp-sets))
  )
(defun larumbe/recompile-with-regexp-alist ()
  "Recompile current *compilation* buffer and set proper regexp-alist for different programs"
  (interactive)
  (when (not (bound-and-true-p larumbe/custom-compilation-regexp-active))
    (larumbe/recompile-set-active-regexp-alist))
  (recompile)
  (pcase larumbe/custom-compilation-regexp-active
    ("vivado"
     (larumbe/vivado-error-regexp-set-emacs))
    ("irun"
     (larumbe/irun-error-regexp-set-emacs))
    ("scons"
     (larumbe/scons-error-regexp-set-emacs))
    ("verilator"
     (larumbe/verilator-error-regexp-set-emacs))
    )
  (end-of-buffer))

;; Master function
(defun larumbe/custom-error-regexp-set-emacs (ce-re-alist-alist)
  "Sets variables `compilation-error-regexp-alist' and `compilation-error-regexp-alist-alist' according to parameter"
  (interactive)
  (when (boundp 'compilation-error-regexp-alist-alist)
    (setq compilation-error-regexp-alist (mapcar 'car ce-re-alist-alist)) ; Fetch first element of list of lists
    (setq compilation-error-regexp-alist-alist ce-re-alist-alist)))


;;;; Vivado
;; Variable to parse regexps with vivado info/warning/errors
(setq vivado-error-regexp-emacs-alist-alist
      '(
        (vivado-error    "^\\(ERROR\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"            3 4 nil 2 nil (1 compilation-error-face))
        (vivado-critical "^\\(CRITICAL WARNING\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*" 3 4 nil 2 nil (1 compilation-error-face))
        (vivado-warning  "^\\(WARNING\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"          3 4 nil 1 nil (1 compilation-warning-face))
        (vivado-info     "^\\(INFO\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"             3 4 nil 0 nil (1 compilation-info-face))
        )
      )

(defun larumbe/vivado-error-regexp-set-emacs ()
  "Only takes Vivado Errors regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs vivado-error-regexp-emacs-alist-alist))


;;;; IRUN (CEE)
;; Fetched from verilog-mode (verilog-IES: Incisive Enterprise Simulator) and improved to fit Emacs
(setq irun-error-regexp-emacs-alist-alist
      '(
        (verilog-IES-error   ".*\\(?1:\\*E\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 2 nil (1 compilation-error-face))
        (verilog-IES-warning ".*\\(?1:\\*W\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 1 nil (1 compilation-warning-face))
        )
      )
(defun larumbe/irun-error-regexp-set-emacs ()
  "Only takes Cadence IES regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs irun-error-regexp-emacs-alist-alist))


;;;; SCons
;; Irun + Vivado + SCons targets + Python
(setq scons-error-regexp-emacs-alist-alist
      '(
        (verilog-IES-error   ".*\\(?1:\\*E\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 2 nil (1 compilation-error-face))
        (verilog-IES-warning ".*\\(?1:\\*W\\),[0-9A-Z]+\\(?:\\(?:\\[[0-9A-Z_,]+\\]\\)? (\\(?2:[^ \t,]+\\),\\(?3:[0-9]+\\)\\)?" 2 3 nil 1 nil (1 compilation-warning-face))
        (vivado-error        "^\\(ERROR\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"            3 4 nil 2 nil (1 compilation-error-face))
        (vivado-critical     "^\\(CRITICAL WARNING\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*" 3 4 nil 2 nil (1 compilation-error-face))
        (vivado-warning      "^\\(WARNING\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"          3 4 nil 1 nil (1 compilation-warning-face))
        (vivado-info         "^\\(INFO\\)\\(.*\\[\\(.*\\):\\([0-9]+\\)\\]\\)*"             3 4 nil 0 nil (1 compilation-info-face))
        ;; (scons-target-cmd    "\\(?1:^[a-zA-Z_-]+\\)(\\[\"\\(?2:.*\\)\"\\],"   2 nil nil 0 nil (1 compilation-info-face))
        (scons-target-cmd    "\\(?1:^[a-zA-Z_-]+\\)(\\[\"\\(?2:.*\\)\"\\],"   2 nil nil 0 nil (1 compilation-line-face))
        (scons-target-err    "\\(?1:NOK\\)$"                                  1 nil nil 2 nil (1 compilation-error-face))
        (scons-target-cw     "\\(?1:critical warning\\)$"                     1 nil nil 2 nil (1 compilation-warning-face))
        (scons-target-ok     "\\(?1:OK\\)$"                                   1 nil nil 0 nil (1 compilation-info-face))
        ;; Adapted from compilation.el for Python tracebacks
        (python-tracebacks-and-caml "File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)?" 2 (3 . 4) (5 . 6) (7)) ; Some regexps where not detected on some SCons errors
        ;; (python-tracebacks-and-caml "^[ \t]*File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)" 2 (3 . 4) (5 . 6) (7)) ;; Original one, without the ? at the end
        ;; Python Logs (fetched from Ableton)
        (python-log-error   "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:ERROR\\) - "   nil nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
        (python-log-warning "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:WARNING\\) - " nil nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
        (python-log-info    "\\(?1:[0-9-]+ [0-9:,]+\\) - \\(?2:[a-zA-Z0-9.]+\\) - \\(?3:INFO\\) - "    nil nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
        )
      )

(defun larumbe/scons-error-regexp-set-emacs ()
  "Takes Vivado, Irun, SCons and python regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs scons-error-regexp-emacs-alist-alist))


;;;; Verilator
;; Fetched from: /home/martigon/.elisp/verilog-mode.el:902
(setq verilator-error-regexp-emacs-alist-alist
      '((verilator-warning "%?\\(Error\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"    3 4 nil 2 nil (1 compilation-error-face) (2 compilation-line-face))
        (verilator-error   "%?\\(Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):"  3 4 nil 1 nil (1 compilation-warning-face) (2 compilation-line-face)))
      )

(defun larumbe/verilator-error-regexp-set-emacs ()
  "Takes Verilator regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs verilator-error-regexp-emacs-alist-alist))




;;;; Ableton MIDI Remote Scripts Regexps
;; INFO: To be used with: `C-u M-x compile RET tail -f Log.txt'
;; Or just make a wrapper function to set up this debug config
(setq ableton-error-regexp-emacs-alist-alist
      '(
        ;; Taken from scons functions present back in the file
        (python-tracebacks-and-caml "File \\(\"?\\)\\([^,\" \n\t<>]+\\)\\1, lines? \\([0-9]+\\)-?\\([0-9]+\\)?\\(?:$\\|, \\(?: characters? \\([0-9]+\\)-?\\([0-9]+\\)?:\\)?\\([ \n]Warning\\(?: [0-9]+\\)?:\\)?\\)?" 2 (3 . 4) (5 . 6) (7)) ; Some regexps where not detected on some SCons errors
        ;; Ableton own ones, extend as desired
        (ableton-error      "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptError:\\)"    nil nil nil 1 2 (1 compilation-line-face) (3 compilation-warning-face))
        (ableton-exception  "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:Exception:\\)"            nil nil nil 2 2 (1 compilation-line-face) (3 compilation-error-face))
        (ableton-message    "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\) \\(?3:RemoteScriptMessage:\\)"  nil nil nil 0 2 (1 compilation-line-face) (3 compilation-info-face))
        (ableton-others     "\\(?1:[0-9-]+T[0-9:.]+:\\) \\(?2:info:\\)"                                nil nil nil 0 2 (1 compilation-line-face))
        )
      )

(defun larumbe/ableton-error-regexp-set-emacs ()
  "Takes Ableton and python regexps into account"
  (interactive)
  (larumbe/custom-error-regexp-set-emacs ableton-error-regexp-emacs-alist-alist))
