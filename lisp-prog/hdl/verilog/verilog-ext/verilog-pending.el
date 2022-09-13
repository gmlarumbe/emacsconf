;;; rx
(require 'rx)

(defmacro rx-verilog (&rest body-forms)
  `(rx-let ((newline-or-space+ (+ (or blank "\n")))
            (newline-or-space* (* (or blank "\n")))
            (keyword* (* (+ (char "a-z")) (+ blank)))
            (verilog-comments* (* (* blank) "//" (* nonl))) ; TODO: Review if this one is necessary
            (verilog-param-port-list (group "(" (opt (+ (not ";"))) ")"))
            (verilog-almost-anything-inside-port (group (opt (1+ (not (any ";./"))))))
            (verilog-array-content (group (* "[" (+ nonl) "]")))
            (verilog-identifier (group symbol-start
                                       (or (group (any letter "_") (* (any letter digit "_$"))) ; Simple identifier
                                           (group "\\" (+ letter)))                              ; Escaped identifier
                                       symbol-end)))
     ,@body-forms))


(defvar verilog-ext-module-instance-re
  (rx-verilog
   (rx bol (* blank)                                     ; Initial optional blanks
       (group-n 1 verilog-identifier) newline-or-space*  ; Identifier
       (* "#" newline-or-space* verilog-param-port-list verilog-almost-anything-inside-port) ; Optional parameters
       ;; verilog-comments*                                 ; TODO: Review if this one is necessary
                                        ; Parameter contents
       (group-n 2 verilog-identifier)                    ; Instance name
       (* blank) verilog-array-content newline-or-space* ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
       "("                                               ; Parenthesis before ports and connections
       )))

;; TODO: Modi, to find header (probably can be removed later)
(defvar verilog-ext-header-words-re
  (regexp-opt
   '("case"
     "class"
     "clocking"
     "`define"
     "function"
     "group"
     "interface"
     "module"
     "program"
     "primitive"
     "package"
     "property"
     "sequence"
     "specify"
     "table"
     "task")
   'symbols))


;; TODO: Maybe use it along with tokens to get capture groups and make these re functions more generic?
(defvar verilog-ext-header-re
  (rx-verilog
   (rx bol (* blank) keyword* ; Optional virtual, local, protected
       (group-n 1 (regex verilog-ext-header-words-re))
       (+ blank) keyword* ;Optional void, static, automatic, ..
       ;; Allow parsing extern methods like class::task
       (group-n 2 (* verilog-identifier "::") verilog-identifier)
       word-boundary)))



(defvar verilog-ext-block-end-keywords '("end"
                                          "join" "join_any" "join_none"
                                          "endchecker"
                                          "endclass"
                                          "endclocking"
                                          "endconfig"
                                          "endfunction"
                                          "endgroup"
                                          "endinterface"
                                          "endmodule"
                                          "endpackage"
                                          "endprimitive"
                                          "endprogram"
                                          "endproperty"
                                          "endsequence"
                                          "endtask")
  "Verilog/SystemVerilog block end keywords.
IEEE 1800-2012 SystemVerilog Section 9.3.4 Block names.")

(defvar verilog-ext-block-end-keywords-re
  (regexp-opt verilog-ext-block-end-keywords 'symbols)
  "Regexp to match the Verilog/SystemVerilog block end keywords.
See `verilog-ext-block-end-keywords' for more.")


(defvar verilog-ext-end-keywords-complete-re
  (rx-verilog
   (rx bol
       (group-n 1 (* blank) (regex verilog-ext-block-end-keywords-re))
       (* blank) "//" (* blank)
       (* (group (or "block:" (group verilog-identifier (* blank) "::")) (* blank)))
       (group-n 2 verilog-identifier)
       (* blank) eol)))

;; (defvar verilog-ext-block-end-keywords-complete-re
;;   (concat "^"
;;           "\\(?1:[[:blank:]]*"
;;           verilog-ext-block-end-keywords-re
;;           "\\)"
;;           "[[:blank:]]*//[[:blank:]]*"
;;           "\\(\\(block:\\|"
;;           modi/verilog-identifier-re "[[:blank:]]*::\\)[[:blank:]]*\\)*"
;;           "\\(?2:" modi/verilog-identifier-re "\\)"
;;           "[[:blank:]]*$"))




;;; Navigation
;; TODO: Use in conjunction with hook that modifies syntax entry for `
;; Currently inside `verilog-ext-hook' in verilog-utils
(defun verilog-ext-electric-verilog-tab ()
  "Wrapper of the homonym verilog function to avoid indentation issues with compiler directives after setting custom hooks."
  (interactive)
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?` "w" table)
    (with-syntax-table table
      (electric-verilog-tab))))
;; End of TODO:


;; TODO: Rename this token thing with something else as this is used inside verilog-mode
;;;; Token/Class-related
(defvar verilog-ext-token-re
  (regexp-opt
   '("module"
     "interface"
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
     "`define")
   'symbols))

(defun verilog-ext-find-token (&optional fwd)
  "Search forward for a Verilog token regexp."
  (let ((token-re verilog-ext-token-re)
        (case-fold-search verilog-case-fold) ; TODO: What about case fold
        (found nil)
        (pos))
    (save-excursion
      (when fwd
        (forward-char)) ; Needed to avoid getting stuck
      (while (and (not found)
                  (if fwd
                      (re-search-forward token-re nil t)
                    (re-search-backward token-re nil t)))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p)
              (setq pos (match-beginning 1))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-token-fwd ()
  "Search forward for a Verilog token regexp."
  (interactive)
  (verilog-ext-find-token t))


(defun verilog-ext-find-token-bwd ()
  "Search backwards for a Verilog token regexp."
  (interactive)
  (verilog-ext-find-token nil))



;;;; Modi
;; TODO: Seems that instance is already handled
;; TODO: What modi calls header would be what I call token
;; TODO: Extend token-re to something more complex (like modi's) so that there are capture groups
;; TODO: And it can be easier
;; TODO: Take into account the rest of rx (like the ones used in imenu for task/func/class) etc


;; TODO: Modi headers are more complex than just looking for a word
(defun verilog-ext-get-header (&optional fwd)
  "Function to return the name of the block (module, class, package,
function, task, `define) under which the point is currently present.

If FWD is non-nil, do the block header search in forward direction;
otherwise in backward direction.

This function updates the local variable `verilog-ext-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"top\"
is returned and `verilog-ext-which-func-xtra' is updated to \"mod\" (short
for \"module\").

   module top ();
   ▯
   endmodule "
  (let (block-type block-name return-val) ;return-val will be nil by default
    (setq-local verilog-ext-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward verilog-ext-header-re nil :noerror)
              (re-search-backward verilog-ext-header-re nil :noerror))
        ;; Ensure that text in line or block comments is not incorrectly
        ;; parsed as a Verilog block header
        (when (not (equal (face-at-point) 'font-lock-comment-face))
          ;; (message "---- 1 ---- %s" (match-string 1))
          ;; (message "---- 2 ---- %s" (match-string 2))
          ;; (message "---- 3 ---- %s" (match-string 3))
          ;; (message "---- 4 ---- %s" (match-string 4))
          (setq block-type (match-string 1))
          (setq block-name (match-string 2))

          (when (and (stringp block-name)
                     (not (string-match verilog-ext-keywords-re
                                        block-name)))
            (setq-local verilog-ext-which-func-xtra
                        (cond
                         ((string= "class"     block-type) "class")
                         ((string= "clocking"  block-type) "clk")
                         ((string= "`define"   block-type) "macro")
                         ((string= "group"     block-type) "group")
                         ((string= "module"    block-type) "mod")
                         ((string= "interface" block-type) "if")
                         ((string= "package"   block-type) "pkg")
                         ((string= "sequence"  block-type) "seq")
                         (t (substring block-type 0 4)))) ;First 4 chars
            (setq return-val block-name)))))
    (when (featurep 'which-func)
      ;; (modi/verilog-update-which-func-format)
      )
    return-val))


;; TODO: Modi headers are more complex than just looking for a word
(defun verilog-ext-jump-to-header-dwim (fwd)
  "Jump to a module instantiation header above the current point. If
a module instantiation is not found, jump to a block header if available.

If FWD is non-nil, do that module instrantiation/header search in forward
direction; otherwise in backward direction.

Few examples of what is considered as a block: module, class, package, function,
task, `define."
  (interactive "P")
  (if (verilog-ext-find-module-instance fwd)
      (if fwd
          (re-search-forward verilog-ext-module-instance-re nil :noerror)
        (re-search-backward verilog-ext-module-instance-re nil :noerror))
    (if fwd
        (re-search-forward verilog-ext-header-re nil :noerror)
      (re-search-backward verilog-ext-header-re nil :noerror))))



;; TODO: How to handle `modi/verilog-identifier-pcre'?
(defun verilog-ext-find-parent-module ()
  "Same as `modi/verilog-find-parent-module'.
Additionally add xref push marker to the stack."
  (interactive)
  (let ((verilog-module-re (concat "^[[:blank:]]*" ;Elisp regexp
                                   "\\(?:module\\)[[:blank:]]+" ;Shy group
                                   "\\(?1:"
                                   modi/verilog-identifier-re ;Elisp regexp here!
                                   "\\)\\b"))
        module-name
        module-instance-pcre)
    (save-excursion
      (re-search-backward verilog-module-re)
      (setq module-name (match-string 1))
      (setq module-instance-pcre ;PCRE regex
            (concat "^\\s*"
                    module-name
                    "\\s+"
                    "(#\\s*\\((\\n|.)*?\\))*" ;optional hardware parameters
                                        ;'(\n|.)*?' does non-greedy multi-line grep
                    "(\\n|.)*?" ;optional newline/space before instance name
                    "([^.])*?" ;do not match ".PARAM (PARAM_VAL)," if any
                    "\\K"       ;don't highlight anything till this point
                    modi/verilog-identifier-pcre ;instance name
                    "(?=[^a-zA-Z0-9_]*\\()")) ;optional space/newline after instance name
                                        ;and before opening parenthesis `('
                                        ;don't highlight anything in (?=..)
      (let* ((ag-arguments ag-arguments)) ;Save the global value of `ag-arguments'
        ;; Search only through verilog type files.
        ;; See "ag --list-file-types".
        (add-to-list 'ag-arguments "--verilog" :append)
        (xref-push-marker-stack) ; INFO: Added by Larumbe
        (ag-regexp module-instance-pcre (projectile-project-root))))))



;;; Utils
;;;; Misc
;; https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
(defvar verilog-ext-open-dirs nil
  "List with directories of current opened `verilog-mode' buffers.
Used for verilog AUTO libraries, flycheck and Verilog-Perl hierarchy.")
(defvar verilog-ext-open-pkgs nil
  "List of currently opened SystemVerilog packages.")
(defvar verilog-ext-open-pkgs-projectile nil
  "List of current open packages at projectile project.")


(defun verilog-ext-dirs-and-pkgs-of-open-buffers ()
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


(defun verilog-ext-update-project-pkg-list ()
  "Update currently open packages on `verilog-ext-open-pkgs-projectile'.

Only packages within current projectile project are added.
To be used with vhier/flycheck.

INFO: Limitations:
 - Packages included as sources might not be in the proper order.
 - Some sorting method could be used in the future:
   - Extracting them from buffer file but in the order they have been
     opened and reverse sorting, for example..."
  (setq verilog-ext-open-pkgs-projectile nil) ; Reset list
  (mapc
   (lambda (pkg)
     (when (string-prefix-p (projectile-project-root) pkg)
       (unless (member pkg verilog-ext-open-pkgs-projectile)
         (push pkg verilog-ext-open-pkgs-projectile))))
   verilog-ext-open-pkgs)
  ;; Return pkg-list
  verilog-ext-open-pkgs-projectile)


;;;; Hooks
(defun verilog-ext-hook ()
  "Verilog hook."
  ;; TODO: Separate into various hooks:
  ;;  1) Open dirs/pkgs: (TODO: Could be rewritten as opened files with .sv and opened files with .svh?)
  (setq verilog-ext-open-dirs (nth 0 (verilog-ext-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-ext-open-pkgs (nth 1 (verilog-ext-dirs-and-pkgs-of-open-buffers)))
  (setq verilog-library-directories verilog-ext-open-dirs) ; Verilog *AUTO* folders (could use `verilog-library-files' for files)
  ;;  2) Flycheck active linter
  (setq verilog-ext-flycheck-verilator-include-path verilog-ext-open-dirs)
  (flycheck-select-checker verilog-ext-flycheck-active-linter)
  ;;  3) Syntax entry (check `verilog-ext-electric-verilog-tab' in pending) TODO
  (modify-syntax-entry ?` ".") ; Avoid including preprocessor tags while isearching. Requires `verilog-ext-electric-verilog-tab' to get back standard table to avoid indentation issues with compiler directives.
  ;;  4) Timestamp (TODO)
  (verilog-ext-time-stamp-update)
  ;;  5) Completion (TODO)
  (setq-local yas-indent-line 'fixed))




;;; Beautify
(defun verilog-ext-clean-port-blanks ()
  "Cleans blanks inside port connections of current buffer.

Capture Groups:
- Group 1: Beginning of line blanks
- Group 2: Port name (after dot connection)
- Group 3: Blanks after identifier
- Group 4: Blanks after beginning of port connection '('
- Group 5: Name of connection
- Group 6: Blanks after end of port connection ')'
"
  (interactive)
  (let ((old-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)(\\(?4:[ ]*\\)\\(?5:[^ ]+\\)\\(?6:[ ]*\\))")
        (new-re "\\1.\\2\\3\(\\5\)"))
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward old-re nil :noerror)
        (replace-match new-re)))
    (message "Removed blanks from current buffer port connections.")))


;;; Editing
;;;; Port connect/disconnect/blank cleaning
(defun verilog-ext-toggle-connect-port (force-connect)
  "Toggle connect/disconnect port at current line.

If regexp detects that port is connected then disconnect it
and viceversa.

If called with universal arg, FORCE-CONNECT parameter will force connection
of current port, no matter if it is connected/disconnected"
  (interactive "P")
  (let* ((case-fold-search verilog-case-fold)
         (port-regex "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)")
         (conn-regex "\\(?4:(\\(?5:.*\\))\\)?")
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
        (message "No port detected at current line")))))


(defun verilog-ext-connect-ports-recursively ()
  "Connect ports of current instance recursively.

Ask for ports to be connected until no port is found at current line."
  (interactive)
  (while (not (equal (verilog-ext-toggle-connect-port t) "No port detected at current line"))
    (verilog-ext-toggle-connect-port t)))




(defun verilog-ext-block-end-comments-to-block-names ()
  "Convert valid block-end comments to ': BLOCK_NAME'.

Examples: endmodule // module_name             → endmodule : module_name
          endfunction // some comment          → endfunction // some comment
          endfunction // class_name::func_name → endfunction : func_name
          end // block: block_name             → end : block_name "
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward verilog-ext-end-keywords-complete-re nil :noerror)
      ;; Make sure that the matched string after "//" is not a verilog keyword.
      (when (not (string-match-p verilog-ext-keywords-re (match-string 2)))
        (replace-match "\\1 : \\2")))))


(define-minor-mode verilog-ext-block-end-comments-to-block-names-mode
  ""
  :global nil
  (if verilog-ext-block-end-comments-to-block-names-mode
      (progn
        (add-hook 'verilog-mode-hook (lambda () (add-hook 'before-save-hook #'verilog-ext-block-end-comments-to-block-names nil :local)))
        (message "Enabled gtags-update-async-minor-mode [current buffer]"))
    (remove-hook 'verilog-mode-hook (lambda () (add-hook 'before-save-hook #'verilog-ext-block-end-comments-to-block-names nil :local)))
    (message "Disabled gtags-update-async-minor-mode [current buffer]")))




;;; Compile
;;;;; Preprocessor
(defun verilog-ext-preprocess ()
  "Allow choosing between programs with a wrapper of `verilog-preprocess'.
All the libraries/incdirs are computed internally at `verilog-mode' via
`verilog-expand'.
INFO: `iverilog' command syntax requires writing to an output file
(defaults to a.out)."
  (interactive)
  (let (iver-out-file)
    (pcase (completing-read "Select tool: " '("verilator" "vppreproc" "iverilog"))
      ("verilator" (setq verilog-preprocessor "verilator -E __FLAGS__ __FILE__"))
      ("vppreproc" (setq verilog-preprocessor "vppreproc __FLAGS__ __FILE__"))
      ("iverilog"  (progn (setq iver-out-file (read-string "Output filename: " (concat (file-name-sans-extension (file-name-nondirectory (buffer-file-name))) "_pp.sv")))
                          (setq verilog-preprocessor (concat "iverilog -E -o" iver-out-file " __FILE__ __FLAGS__")))))
    (verilog-preprocess)))

