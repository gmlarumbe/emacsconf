;;; Generic
;; TODO:
;;   - Review docstrings of every function
;;   ...
;;   - Clean verilog-utils
;;     - find-module-instance and get-header seem deprecable, based on other functions
;;     - Seems I prefer to use tokens instead of blocks/headers
;;   - The block-end-comments-to-block-names review, convert it to a minor-mode maybe?
;;   - What to do with the connect/disconnect/clean blanks ? Where to move? Editing is a nice place?
;;   - Move the regexps of compilation-utils to verilog-compile?
;;   - Overrides, maybe send Bug?
;;   - Navigation: review all of these and check if they work fine with/without shadowing
;;   - Imenu, check what can be reused and moved from/to other places (like navigation)
;;   - Vhier: clean, refactor
;;   - Remove larumbe/ functions and use generic ones (move to utils, use a variable that holds potential functions to do things)
;;   - Flycheck: good shape, but clean
;;   - Font-lock: reuse functions from the rest of the blocks
;;   - Clean up templates/hydra (use columns) and test if the rest work
;;   - Clean up code
;;   - Clean up/review functions doc
;;   - Check timestamp

;; (require 'verilog-rx)
;; (require 'verilog-shadow) ; INFO: Might be useful in the future for some semantic parsing stuff
;; (require 'verilog-editing)
;; (require 'verilog-compile) ; TODO: Rename to makefile? Add compilation regexps?
;; (require 'verilog-vhier)
;; (require 'verilog-flycheck)
;; (require 'verilog-timestamp) ; TODO: Change the 'work' section to a different name
;; (require 'verilog-compile) ; TODO: Add compilation regexp support for verilog here (as a derived compilation mode maybe?)
;; (require 'verilog-lsp)
;; TODO: Add these things for apheleia, tree-sitter, etc...


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
;; In `verilog-ext-find-module-instance-fwd':
;;   TODO: Try to optimize it not to do the forward-line thing
;;   TODO: Right now the `verilog-identifier-sym-re' catches things such as (Rst_n) and .Rst_n
;;   It would be nice if it only recognized things that have an space before and after (a real symbol).
;;   TODO: Could this be done modifying temporarily the syntax table? But that might be an issue for font-locking?
;;
;; In `verilog-ext-find-module-instance-bwd'
;;  TODO: Do something for when point is inside a module, to jump to current module header instead of
;;  to previous one. Ideas:
;;    1. New one:
;;    -  Use the `verilog-ext-instance-at-point'
;;    2. Old one (possibly discard):
;;    -  Check if in parenthesized expression (should return non-nil): (verilog-parenthesis-depth)
;;    -  Go up until not in a parenthsized expression: (while (verilog-backward-up-list 1) ...)
;;    -  Do same logic as with the rest of `verilog-ext-find-module-instance-bwd' from this point on
;;       - Probably this could be grouped/refactored in another function
;;
;;  TODO: Add some check to make sure we are in a module/interface when looking for instances to avoid
;;  considering some classes/parameterized objects as instances.
;;



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


;;;; Jump to module
;;  TODO: Do something in `verilog-ext-jump-to-module-at-point' to parameterize the use of gtags/xref



;;;; Modi
;; TODO: Seems that instance is already handled
;; TODO: What modi calls header would be what I call token
;; TODO: Extend token-re to something more complex (like modi's) so that there are capture groups
;; TODO: And it can be easier
;; TODO: Take into account the rest of rx (like the ones used in imenu for task/func/class) etc

;; TODO: This is required by some modi functions
;; (require 'ag) ; Load `ag' package so `ag-arguments' get updated with --stats to jump to first match


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


;;;; Defun find
;; TODO: These were fetched from verilog-mode, but many things changed
;; Probably can be used with info from tree-sitter
(defun verilog-defun-level-up (&optional arg)
  "Move up one defun-level."
  (interactive)
  ;; Order of conditions is relevant here
  (cond ((or (verilog-in-function-p)
             (verilog-in-task-p))
         (verilog-re-search-backward (concat "\\<\\(function\\|task\\)\\>") nil 'move))
        ((verilog-in-class-p)
         (verilog-re-search-backward "\\<class\\>" nil 'move))
        ((verilog-in-package-p)
         (verilog-re-search-backward "\\<package\\>" nil 'move))
        ((or (verilog-in-module-p)
             (verilog-in-program-p)
             (verilog-in-interface-p))
         (verilog-re-search-backward (concat "\\<\\(module\\|program\\|interface\\)\\>") nil 'move))
        (t
         nil)))

(defun verilog-defun-level-down (&optional arg)
  "Move down one defun-level."
  (interactive)
  (let (limit)
    ;; Order of conditions is relevant here
    (cond ((or (verilog-in-function-p :x)
               (verilog-in-task-p :x))
           nil)
          ((verilog-in-class-p :x)
           (setq limit (verilog-re-search-forward-try (concat "\\<endclass\\>") nil 'move :only-pos))
           (verilog-re-search-forward-try (concat "\\<\\(function\\|task\\)\\>") limit 'move))
          ((verilog-in-package-p :x)
           (setq limit (verilog-re-search-forward-try (concat "\\<endpackage\\>") nil 'move :only-pos))
           (verilog-re-search-forward-try "\\<class\\>" limit 'move))
          ((or (verilog-in-module-p :x)
               (verilog-in-program-p :x)
               (verilog-in-interface-p :x))
           (setq limit (verilog-re-search-forward-try (concat "\\<end\\(package\\|module\\|interface\\)\\>") nil 'move :only-pos))
           (verilog-re-search-forward-try (concat "\\<\\(function\\|task\\)\\>") limit 'move))
          (t
           nil))))

(defun verilog-defun-same-level-next ()
  ""
  (interactive)
  (let (limit)
    ;; Order of conditions is relevant here
    (cond (;; Functions/task inside task/module/package/interface/program
           (or (verilog-in-function-p :x)
               (verilog-in-task-p :x))
           (when (looking-at (concat "\\<\\(function\\|task\\)\\>"))
             (forward-word))
           (setq limit (verilog-re-search-forward-try (concat "\\<end\\(class\\|package\\|module\\|interface\\|program\\)\\>") nil 'move :only-pos))
           (verilog-re-search-forward-try (concat "\\<\\(function\\|task\\)\\>") limit 'move)) ; TODO: Add static, protected, etc.. tags
          (;; Classes inside package
           (verilog-in-class-p :x)
           (when (looking-at (concat "\\<class\\>"))
             (forward-word))
           (setq limit (verilog-re-search-forward-try (concat "\\<endpackage\\>") nil 'move :only-pos))
           (verilog-re-search-forward-try "\\<class\\>" limit 'move))
          (;; Package (top)
           (verilog-in-package-p :x)
           (when (looking-at (concat "\\<package\\>"))
             (forward-word))
           (verilog-re-search-forward-try "\\<package\\>" nil 'move))
          (;; Module/program/interface
           (or (verilog-in-module-p :x)
               (verilog-in-program-p :x)
               (verilog-in-interface-p :x))
           (when (looking-at (concat "\\<\\(module\\|program\\|interface\\)\\>"))
             (forward-word))
           (verilog-re-search-forward-try (concat "\\<\\(module\\|program\\|interface\\)\\>") nil 'move))
          (t
           nil))))

(defun verilog-defun-same-level-prev ()
  ""
  (interactive)
  ;; TODO: Do it analogously to 'prev' function
  )



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
;; TODO: In `verilog-ext-beautify-current-file':
;;  - Remove blanks in port connections
;;  - Align declarations/expressions: (similar to verilog-mode test0.el)
;;  - Add this to docstring

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


;; TODO Add a function (C-c C-M-i) that aligns declarations of current paragraph
;; TODO Add a function (C-c C-M-o) that aligns expressions of current paragraph
;; TODO: Problem: paragraphs might not always be blocks of decl/expressions if there are no blank lines in between

;; (defun verilog-ext-align-decl-current-block ()
;;   ""
;;   (interactive)
;;   ()
;;   ()
;;   )

;; (defun verilog-ext-align-expr-current-block ()
;;   ""
;;   (interactive)

;;   )

;; TODO: Create function to gather typedefs of a directory and subdirectory?
;;  - Useful for typedef alignment



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




;;; Templates
;; TODO: `verilog-ext-templ-testbench-simple-from-file' fails if instantiates a DUT without parameters


;;;; UVM env
;; TODO: Convert this into a UVM env template
;; - Remove 'program' bullshit
;; - Add assertions file (bind to DUT)
;; - And so on...
(defun verilog-ext-templ-testbench-env--clocks (file)
  "Create environment `tb_clocks' and save to FILE."
  (with-temp-file file
    (insert "\
import tb_defs_pkg::CLKT;
// import other clock periods

module tb_clocks (
    output logic Clk
    // Other clocks
    );

    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // Other clocks
    // ...

    // Initial clock values
    initial begin
        Clk = 1;
    end


endmodule: tb_clocks
"))
  (find-file file)
  (verilog-ext-templ-header-hp)
  (save-buffer))


(defun verilog-ext-templ-testbench-env--program (file)
  "Create environment `tb_program' and save to FILE."
  (with-temp-file file
    (insert "\
import tb_defs_pkg::*;
import tb_classes::*;
// import Bfms

program automatic tb_program (
    // Interfaces from/to DUT
    // ...
    input logic Clk,
    output logic Rst_n
    );


    // Testbench tb;

    initial begin
        // tb = new();
        $display(\"Starting simulation...\");



        // tb.finish_simulation();
    end


endprogram: tb_program
"))
  (find-file file)
  (verilog-ext-templ-header-hp)
  (save-buffer))


(defun verilog-ext-templ-testbench-env--defs-pkg (file)
  "Create environment `tb_defs_pkg' and save to FILE."
  (with-temp-file file
    (insert "\
package tb_defs_pkg;
    // Simulation parameters
    timeprecision   = 1ps;
    timeunit        = 1ns;
    localparam CLKT = 10ns;  // 100 MHz

    // DUT instance parameters
    // ...

    // Other parameters
    // ...
endpackage : tb_defs_pkg
"))
  (find-file file)
  (verilog-ext-templ-header-hp)
  (save-buffer))



(defun verilog-ext-templ-testbench-env--classes-pkg (file)
  "Create environment `tb_classes_pkg' and save to FILE."
  (with-temp-file file
    (insert "\
package tb_classes_pkg;

// Drivers
// ...

// Monitor
// ...

// Test
// ...

endpackage : tb_defs_pkg
"))
  (find-file file)
  (verilog-ext-templ-header-hp)
  (save-buffer))


(defun verilog-ext-templ-testbench-env--top (file dut-file clocks-file)
  "Create environment top file and save to FILE.
Instantiate dut from DUT-FILE and clocks from CLOCKS-FILE."
  (find-file file)
  (insert "\
// TODO: unit space imported packages

module tb_top () ;

    logic Clk;
    logic Rst_n;

    // TODO: Declare/Connect interfaces
    // axi4_lite_if axil_if (.AClk(Clk), .AReset_n(Rst_n));
    // ...

    // Clocks

    // Testbench
    tb_program I_TB_PROGRAM (
        .Clk   (Clk),
        .Rst_n (Rst_n)
        );


    // DUT Instantiation

endmodule // tb_<module_name>
")
  (goto-char (point-min))
  (search-forward "// DUT Instantiation")
  (setq current-prefix-arg 4) ; Add DUT instance with parameters and choosing template
  (verilog-ext-templ-inst-auto-from-file dut-file) ; Includes `verilog-auto' expansion
  ;; Clocks
  (goto-char (point-min))
  (search-forward "// Clocks")
  (verilog-ext-templ-inst-auto-from-file clocks-file)
  ;; Header and postprocessing
  (verilog-ext-templ-header-hp)
  (save-buffer))




(defun verilog-ext-templ-testbench-env-from-file (dut-file dir)
  "Create SystemVerilog testbench environment.

DUT-FILE corresponds to the filepath of the DUT (assumes a module per file).
DIR selects the directory where the environment will be created.

If called interactively, prompt for these two previous values.
Environment files will be created at specified DIR (clocks, program, defs_pkg, classes_pkg...)"
  (interactive "FSelect module from file: \nDSelect environment directory: ")
  (let ((module-name (verilog-ext-templ-inst-auto--read-file-modules dut-file))
        (clocks-file      (concat (file-name-as-directory dir) "tb_clocks.sv"))
        (program-file     (concat (file-name-as-directory dir) "tb_program.sv"))
        (defs-pkg-file    (concat (file-name-as-directory dir) "tb_defs_pkg.sv"))
        (classes-pkg-file (concat (file-name-as-directory dir) "tb_classes_pkg.sv"))
        (top-file         (concat (file-name-as-directory dir) "tb_top.sv")))
    ;; Create Environment files
    (verilog-ext-templ-testbench-env--clocks      clocks-file)
    (verilog-ext-templ-testbench-env--program     program-file)
    (verilog-ext-templ-testbench-env--defs-pkg    defs-pkg-file)
    (verilog-ext-templ-testbench-env--classes-pkg classes-pkg-file)
    (verilog-ext-templ-testbench-env--top         top-file dut-file clocks-file)))


;;; Font-lock
;;;; Variables
(defvar verilog-ext-font-lock-variable-type-face 'verilog-ext-font-lock-variable-type-face)
(defface verilog-ext-font-lock-variable-type-face
  '((t (:foreground "powder blue")))
  "Face for variable types."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-variable-name-face 'verilog-ext-font-lock-variable-name-face)
(defface verilog-ext-font-lock-variable-name-face
  '((t (:foreground "DarkSeaGreen1")))
  "Face for variable names."
  :group 'verilog-ext-font-lock-faces)


;; TODO: Do something with this or use default's verilog-mode?
(defvar verilog-ext-highlight-variable-declaration-names nil)


;; TODO: Check `verilog-declaration-varname-matcher' and `verilog-single-declaration-end'
;; TODO: There should be mandatory space between logic[3:0] ? For unpacked arrays is not mandatory, is it?
(defconst verilog-ext-variable-re-1
  (concat "\\<\\(?1:" verilog-identifier-re "\\)\\>" verilog-ext-range-optional-re ; Var type
          "\\<\\(?3:" verilog-identifier-re "\\)\\>" verilog-ext-range-optional-re ; Var name
          "\\s-*\\(?4:=.*\\)?;")                                                  ; Optional initialization value
  "type_t foo;
   type_t [10:0] foo;
   type_t [10:0] foo = 'h0;
")
;; TODO: Check `verilog-declaration-varname-matcher' and `verilog-single-declaration-end'
(defconst verilog-ext-variable-re-2
  (concat "\\<\\(?1:" verilog-identifier-re "\\)\\>"
          "\\s-+\\(?3:\\(" verilog-identifier-re "\\s-*,\\s-*\\)+\\(" verilog-identifier-re "\\s-*\\)\\);")
  "type_t foo1, foo2 , foo4, foo6[], foo7 [25], foo8 ;")

;; TODO: Check `verilog-declaration-varname-matcher' and `verilog-single-declaration-end'
(defconst verilog-ext-variable-re-3
  (concat "\\<\\(input\\|output\\|inout\\|ref\\|parameter\\|localparam\\)\\>\\s-+"
          "\\<\\(?1:" verilog-identifier-re "\\)\\>\\s-+" verilog-ext-range-optional-re
          "\\<\\(?3:" verilog-identifier-re "\\)\\>\\s-*" verilog-ext-range-optional-re)
  " ...
  parameter type_t a = 1,
  localparam type_t b = 2
  ) .. (
  ...
  task foo(
      input type_t foo1,
      input bit [ 4:0] foo2,
      output type_t address,
      inout type_t data []
  );
 ")


(defun verilog-ext-find-verilog-variable-type-fwd (regex limit)
  "Generic search based fontification function of Verilog variable types.
INFO: It is not necessary to check that variable is not within string/comment
since these both have precedence over custom fontify.

Search for REGEX bound to LIMIT."
  (let ((found nil)
        (pos)
        (case-fold-search verilog-case-fold)
        (type)
        (name))
    (save-excursion
      (while (and (not found)
                  (re-search-forward regex limit t))
        (setq type (match-string-no-properties 1))
        (setq name (match-string-no-properties 3))
        (unless (or (string-match verilog-ext-keywords-no-types-re type)
                    (string-match verilog-ext-keywords-no-types-re name))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-verilog-variable-fwd-1 (limit)
  (verilog-ext-find-verilog-variable-type-fwd verilog-ext-variable-re-1 limit))

(defun verilog-ext-find-verilog-variable-fwd-2 (limit)
  (verilog-ext-find-verilog-variable-type-fwd verilog-ext-variable-re-2 limit))

(defun verilog-ext-find-verilog-variable-fwd-3 (limit)
  (verilog-ext-find-verilog-variable-type-fwd verilog-ext-variable-re-3 limit))


(defun verilog-ext-find-verilog-variable-type-fontify-1 (limit)
  "Search based fontification function of Verilog type 1 variable types.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-1 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-name-fontify-1 (limit)
  "Search based fontification function of Verilog type 1 variable names.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-1 limit)
      (setq start (match-beginning 3))
      (setq end (match-end 3))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-type-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable types.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-2 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-name-fontify-2 (limit)
  "Search based fontification function of Verilog type 2 variable names.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-2 limit)
      (setq start (match-beginning 2))
      (setq end (match-end 2))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-type-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable types.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-3 limit)
      (setq start (match-beginning 1))
      (setq end (match-end 1))
      (set-match-data (list start end))
      (point))))

(defun verilog-ext-find-verilog-variable-name-fontify-3 (limit)
  "Search based fontification function of Verilog type 3 variable names.
These are determined by variable `verilog-ext-variable-re-1'.
Regex search bound to LIMIT."
  (let (start end)
    (when (verilog-ext-find-verilog-variable-fwd-3 limit)
      (setq start (match-beginning 3))
      (setq end (match-end 3))
      (set-match-data (list start end))
      (point))))


;;;; Custom constructs
(defconst verilog-ext-special-macros
  (verilog-regexp-words
   '( ;; DMA Macros
     "MY_CUSTOM_MACRO"
     ))) ; Used for non-verilog constructs (i.e. custom preprocessing)

(defconst verilog-ext-special-constructs
  (verilog-regexp-words
   '(;; These constructs contain some special character that prevent them to be detected as symbols
     "@special_construct"
     "%special_construct"
     ))) ; Used for non-verilog constructs (i.e. custom preprocessing)


;; Put inside `verilog-ext-font-lock-keywords', after macros
   ;; Special macros
   (cons (concat "\\<\\(" verilog-ext-special-macros "\\)\\>") 'verilog-ext-font-lock-xilinx-attributes-face)
   ;; Special constructs
   (cons (concat "\\(" verilog-ext-special-constructs "\\)") 'verilog-ext-font-lock-xilinx-attributes-face)


;; Put inside `verilog-ext-font-lock-keywords-3'

    ;; Variable types
    '(verilog-ext-find-verilog-variable-type-fontify-1
      (0 'verilog-ext-font-lock-variable-type-face))
    '(verilog-ext-find-verilog-variable-type-fontify-2
      (0 'verilog-ext-font-lock-variable-type-face))
    '(verilog-ext-find-verilog-variable-type-fontify-3
      (0 'verilog-ext-font-lock-variable-type-face))

   ;; DANGER: Still experimental. Regexps are not solid enough.
   (when verilog-ext-highlight-variable-declaration-names
     (list
      ;; A good approach would be fixing the function search based fontification to detect better variable declarations.
      '(verilog-ext-find-verilog-variable-name-fontify-1
        (0 'verilog-ext-font-lock-variable-name-face))
      '(verilog-ext-find-verilog-variable-name-fontify-2
        (0 'verilog-ext-font-lock-variable-name-face))
      '(verilog-ext-find-verilog-variable-name-fontify-3
        (0 'verilog-ext-font-lock-variable-name-face))
      ))


;; Put inside `verilog-ext-font-lock-keywords-3'
;; TODO: Copied from verilog-mode (to fontify variables controlled by knob)
   ;; Variables fontification
   (list
    verilog-declaration-re
    (list
     ;; Anchored matcher (lookup Search-Based Fontification)
     'verilog-declaration-varname-matcher
     ;; Pre-form for this anchored matcher:
     ;; First, avoid declaration keywords written in comments,
     ;; which can also trigger this anchor.
     '(if (and (not (verilog-in-comment-p))
               (not (member (thing-at-point 'symbol) verilog-keywords)))
          (verilog-single-declaration-end verilog-highlight-max-lookahead)
        (point)) ;; => current declaration statement is of 0 length
     nil ;; Post-form: nothing to be done
     '(0 verilog-ext-font-lock-variable-name-face)))



;;;; Enum/Structs issue
;; INFO: Most likely issue has to do with `font-lock-multiline' stuff.
;; Instead of using an anchor, maybe the best thing is to use the multiline property
;; Same as with modules/instances, instead of using anchors

(defvar verilog-ext-font-lock-struct-face 'verilog-ext-font-lock-struct-face)
(defface verilog-ext-font-lock-struct-face
  '((t (:foreground "light blue")))
  "Face for struct variables."
  :group 'verilog-ext-font-lock-faces)

(defvar verilog-ext-font-lock-enum-face 'verilog-ext-font-lock-enum-face)
(defface verilog-ext-font-lock-enum-face
  '((t (:foreground "light blue")))
  "Face for enum variables."
  :group 'verilog-ext-font-lock-faces)


;; TODO:
;; - [-] font lock checks @ autoinst_bug373
;;   - Branch: font-lock
;;   - [ ] There seemed to be a big issue with enum/struct multi fontifying
;;     - [ ] Everytime there was a change in the text buffer, the font-lock was lost
;;     - [ ] `font-lock-fontify-buffer' or `region' would fix it, but it has to be executed at some type of hook every time the file is saved or modified?

(defun verilog-ext-font-lock-enum-fontify-anchor (limit)
  "Fontify enum declaration anchor."
  (when (and verilog-fontify-variables
             (verilog-re-search-forward verilog-typedef-enum-re limit t)
             (progn (verilog-forward-syntactic-ws)
                    (looking-at "{"))
             (progn (ignore-errors (forward-sexp))
                    (backward-char)
                    (looking-at "}")))
    (forward-char)
    (point)))

(defun verilog-ext-font-lock-struct-fontify-anchor (limit)
  "Fontify struct declarations."
  (when (and verilog-fontify-variables
             (verilog-re-search-forward verilog-ext-font-lock-typedef-struct-re limit t)
             (verilog-re-search-forward "{" limit t)
             (progn (backward-char)
                    (ignore-errors (forward-sexp))
                    (backward-char)
                    (looking-at "}")))
    (forward-char)
    (point)))
;; End of TODO:


;; TODO: Put this inside `verilog-ext-font-lock-keywords-3'
   ;; Fontify (typedef) enum vars
   (list
    'verilog-ext-font-lock-enum-fontify-anchor
    (list
     verilog-identifier-sym-re
     '(verilog-pos-at-end-of-statement)
     nil
     '(0 'font-lock-builtin-face))) ; TODO: Choose proper colors
   ;; Fontify (typedef) struct vars
   (list
    'verilog-ext-font-lock-struct-fontify-anchor
    (list
     verilog-identifier-sym-re
     nil
     nil
     '(0 'font-lock-builtin-face))) ; TODO: Choose proper colors
   ;; ;; End of TODO


;;;; Typedef
(defvar verilog-ext-font-lock-typedef-face 'verilog-ext-font-lock-typedef-face)
(defface verilog-ext-font-lock-typedef-face
  '((t (:foreground "light blue")))
  "Face for user defined types."
  :group 'verilog-ext-font-lock-faces)

(defun verilog-ext-font-lock-typedef-decl-fontify (limit)
  "Fontify typedef declarations."
  (let* ((decl-typedef-re (verilog-get-declaration-typedef-re))
         start end found var-start var-end)
    (when (and verilog-fontify-variables
               (verilog-align-typedef-enabled-p))
      (while (and (not found)
                  (verilog-re-search-forward decl-typedef-re limit t))
        (when (save-excursion
                (beginning-of-line)
                (looking-at decl-typedef-re))
          (setq found t)))
      (when found
        (setq start (match-beginning 5))
        (setq end (match-end 5))
        (setq var-start (car (bounds-of-thing-at-point 'symbol)))
        (setq var-end (cdr (bounds-of-thing-at-point 'symbol)))
        (set-match-data (list start end var-start var-end))
        (point)))))


   ;; ;; TODO
   ;; Fontify user types declarations
   '(verilog-ext-font-lock-typedef-decl-fontify
     (0 'verilog-ext-font-lock-typedef-face)
     (1 'font-lock-doc-face)) ; TODO: Choose proper colors



;;; Completion
;; TODO: Add some CAPF improvements?
;; `verilog-completion-at-point' is added to CAPF. It calls `verilog-completion' which in turns
;; completes depending on the context. This context is determined based on indentation. Since
;; indentation is changed, this could be the reason why it fails. Or maybe it works fine but I didn't use it properly.
;; Study `verilog-completion'.
;;
;; `verilog-complete-word' and `verilog-show-completions' are fallbacks for Emacs versions lacking `completion-at-point'
;;
;; Get some idea for words in opened buffers? Like hippie? Is that a backend for company already?
;;
;; TODO: Add some CAPF that uses global to determine what current definition type is?
;;  - E.g.:
;;   - Use regular completion, except when after .
;;      - if current definition is a class, get its attributes and methods in a list and prompt them as completion candidates, plus randomize() method etc
;;      - if current definition is an array prompt for array methods
;;      - if is an enum for enum methods, if is a queue for queue methods, etc... Some semantic analysis
;;      - Could be done with tree-sitter?

;;;; Hydra
("TE"  (call-interactively #'verilog-ext-templ-testbench-env-from-file)        "TB from DUT file (full env)")



;;; Imenu
;; TODO: Do something to catch class external functions/tasks in a different category and strip the class_identifier
;; Something like parsing function class_identifier::identifier
;;   1 - Create the regexp of task::<name>
;;   2 - Modify current regexp for tasks/functions that include : and is used somewhere else
;;   3 - Add new entry in verilog-ext-imenu-generic-expression
;;   4 - Modify verilog-ext-imenu-find-task-function-outside-class-bwd so that it also includes in the or the new regexp
;;   5 - Adapt capture groups so that the prefix class_name:: is removed
;;   6 - Maybe in the future do something to include it in an subgroup same as classes (a bit more complex)
;;
;; TODO: Do a minor-mode that adds/removes the hooks?
;;  - (add-hook 'verilog-mode-hook #'verilog-ext-imenu-hook)




