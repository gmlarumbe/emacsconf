;;; verilog-modi-setup.el --- Modified Verilog Modi Setup  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;; MIT License
;;
;; Copyright (c) 2016 Kaushal Modi
;;
;; Permission is hereby granted, free of charge, to any person
;; obtaining a copy of this software and associated documentation
;; files (the "Software"), to deal in the Software without
;; restriction, including without limitation the rights to use, copy,
;; modify, merge, publish, distribute, sublicense, and/or sell copies
;; of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:
;;
;; The above copyright notice and this permission notice shall be
;; included in all copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
;; BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
;; ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
;; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.
;;
;;
;; Time-stamp: <2017-09-26 15:49:55 kmodi>
;;
;; Verilog
;;
;; Contents:
;;
;;  Variables
;;  Functions
;;    modi/verilog-find-module-instance
;;    modi/verilog-get-header
;;    modi/verilog-jump-to-header-dwim (interactive)
;;    which-func
;;      modi/verilog-which-func
;;      modi/verilog-update-which-func-format
;;    modi/verilog-jump-to-module-at-point (interactive)
;;    modi/verilog-find-parent-module (interactive)
;;    modi/verilog-selective-indent
;;    modi/verilog-compile
;;    convert block-end comments to block names
;;    Do not open all `included files
;;  hideshow
;;  hydra-verilog-template
;;  imenu + outshine
;;  modi/verilog-mode-customization
;;  Key bindings

;; Larumbe
;; Added minor modifications for setup with current Emacs config.

(defconst modi/verilog-identifier-re
  (concat "\\_<\\(?:"
          "\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)" ;simple identifier
          "\\|\\(?:\\\\[!-~]+\\)"               ;escaped identifier
          "\\)\\_>")
  "Regexp to match a valid Verilog/SystemVerilog identifier.

An identifier is used to give an object a unique name so it can be
referenced.  An identifier is either a simple identifier or an escaped
identifier.

A simple identifier shall be any sequence of letters, digits, dollar signs ( $ ),
and underscore characters ( _ ).

The first character of a simple identifier shall not be a digit or $ ; it can be
a letter or an underscore.  Identifiers shall be case sensitive.

For example:

  shiftreg_a
  busa_index
  error_condition
  merge_ab
  _bus3
  n$657

Escaped identifiers shall start with the backslash character ( \\ ) and end with
white space (space, tab, newline). They provide a means of including any of the
printable ASCII characters in an identifier (the decimal values 33 through 126,
or 21 through 7E in hexadecimal).

Neither the leading backslash character nor the terminating white space is
considered to be part of the identifier. Therefore, an escaped identifier \cpu3
is treated the same as a nonescaped identifier cpu3 .

For example:

  \\busa+index
  \\-clock
  \\***error-condition***
  \\net1/\\net2
  \\{a,b}
  \\a*(b+c)

IEEE 1800-2012 SystemVerilog Section 5.6 Identifiers, keywords,and system names.")

(defconst modi/verilog-identifier-pcre
  (concat "\\b"
          "([a-zA-Z_][a-zA-Z0-9$_]*)" ;simple identifier
          "|(\\\\[!-~]+\\s+)"            ;escaped identifier
          "\\b")
  "Perl regex to match a valid Verilog/SystemVerilog identifier.
This is a Perl regex equivalent of the Elips regexp in
`modi/verilog-identifier-re'.")

(defconst modi/verilog-module-instance-re
  (let* ((newline-or-space-optional "\\(?:[[:blank:]\n]\\)*")
         (newline-or-space-mandatory "\\(?:[[:blank:]\n]\\)+")
         (param-port-list "([^;]+?)"))
    (concat "^[[:blank:]]*"
            "\\(?1:" modi/verilog-identifier-re "\\)" ;module name (subgroup 1)
            newline-or-space-mandatory
            ;; optional port parameters
            "\\("
            "#" newline-or-space-optional param-port-list
            "\\([[:blank:]]*//.*?\\)*"  ;followed by optional comments
            "[^;\\./]+?"  ;followed by 'almost anything' before instance name
            "\\)*"
            "\\(?2:" modi/verilog-identifier-re "\\)" ;instance name (subgroup 2)
            newline-or-space-optional
            "(" ;And finally .. the opening parenthesis `(' before port list
            ))
  "Regexp to match valid Verilog/SystemVerilog module instance declaration.")


(defvar modi/verilog-block-end-keywords '(
                                          ;; ")" ;  INFO: Problem with PAREN with regexp-opt
                                          "join" "join_any" "join_none"
                                          "endchecker"
                                          "endclass"
                                          "endclocking"
                                          "endconfig"
                                          "endfunction"
                                          "endgenerate" ; Added by larumbe
                                          "endgroup"
                                          "endinterface"
                                          ;; "endmodule" ;; INFO: Delete on purpose even though it is implemented
                                          "endpackage"
                                          "endprimitive"
                                          "endprogram"
                                          "endproperty"
                                          "endsequence"
                                          "endtask"
                                          )
  "Verilog/SystemVerilog block end keywords.
IEEE 1800-2012 SystemVerilog Section 9.3.4 Block names.")

(defvar modi/verilog-block-end-keywords-re
  (regexp-opt modi/verilog-block-end-keywords 'symbols)
  "Regexp to match the Verilog/SystemVerilog block end keywords.
See `modi/verilog-block-end-keywords' for more.")

(defvar modi/verilog-block-start-keywords '(
                                            ;; "(" ;  INFO: Problem with PAREN with regexp-opt
                                            "begin"
                                            "fork"
                                            "checker"
                                            "class"
                                            "clocking"
                                            "config"
                                            "function"
                                            "generate" ; Added by larumbe
                                            "covergroup"
                                            "interface"
                                            ;; "module"  ;; INFO: Disable on purpose even though it is implemented
                                            "package"
                                            "primitive"
                                            "program"
                                            "property"
                                            "sequence"
                                            "task"
                                            )
  "Verilog/SystemVerilog block start keywords.

These keywords mirror the block end keywords (See `modi/verilog-block-end-keywords').")

(defvar modi/verilog-block-start-keywords-re
  (regexp-opt modi/verilog-block-start-keywords 'symbols)
  "Regexp to match the Verilog/SystemVerilog block start keywords.
See `modi/verilog-block-start-keywords' for more.")

(defconst modi/verilog-header-re
  (concat "^[[:blank:]]*"
          "\\([a-z]+[[:blank:]]+\\)*"   ;Optional virtual, local, protected
          "\\(?1:"                    ;Force group number to 1
          (regexp-opt '("case"
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
                      'symbols)
          "\\)"
          "[[:blank:]]+"
          "\\([a-z]+[[:blank:]]+\\)*"   ;Optional void, static, automatic, ..
          "\\(?2:"
          "\\(?:" modi/verilog-identifier-re "::\\)*" ;Allow parsing extern methods like class::task
          modi/verilog-identifier-re ;Block name, force group number to 2
          "\\)"
          "\\b"
          )
  "Regexp to match valid Verilog/SystemVerilog block header statement.")

(defvar modi/verilog-keywords-re (regexp-opt verilog-keywords 'symbols)
  "Regexp to match reserved Verilog/SystemVerilog keywords.")


(defvar-local modi/verilog-which-func-xtra nil
  "Variable to hold extra information for `which-func' to show in the
mode-line. For instance, if point is under \"module top\", `which-func' would
show \"top\" but also show extra information that it's a \"module\".")


(defun modi/verilog-find-module-instance (&optional fwd)
  "Return the module instance name within which the point is currently.

If FWD is non-nil, do the verilog module/instance search in forward direction;
otherwise in backward direction.

This function updates the local variable `modi/verilog-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"u_adder\"
is returned and `modi/verilog-which-func-xtra' is updated to \"adder\".

   adder u_adder
   (
    ▯
    );"
  (let (instance-name return-val)   ;return-val will be nil by default
    (setq-local modi/verilog-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward modi/verilog-module-instance-re nil :noerror)
              (re-search-backward modi/verilog-module-instance-re nil :noerror))
        ;; Ensure that text in line or block comments is not incorrectly
        ;; parsed as a module instance
        (when (not (equal (face-at-point) 'font-lock-comment-face))
          ;; (message "---- 1 ---- %s" (match-string 1))
          ;; (message "---- 2 ---- %s" (match-string 2))
          ;; (message "---- 3 ---- %s" (match-string 3))
          (setq-local modi/verilog-which-func-xtra (match-string 1)) ;module name
          (setq instance-name (match-string 2)) ;Instance name

          (when (and (stringp modi/verilog-which-func-xtra)
                     (string-match modi/verilog-keywords-re
                                   modi/verilog-which-func-xtra))
            (setq-local modi/verilog-which-func-xtra nil))

          (when (and (stringp instance-name)
                     (string-match modi/verilog-keywords-re
                                   instance-name))
            (setq instance-name nil))

          (when (and modi/verilog-which-func-xtra
                     instance-name)
            (setq return-val instance-name)))))
    (when (featurep 'which-func)
      (modi/verilog-update-which-func-format))
    return-val))

;;;; modi/verilog-get-header
(defun modi/verilog-get-header (&optional fwd)
  "Function to return the name of the block (module, class, package,
function, task, `define) under which the point is currently present.

If FWD is non-nil, do the block header search in forward direction;
otherwise in backward direction.

This function updates the local variable `modi/verilog-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"top\"
is returned and `modi/verilog-which-func-xtra' is updated to \"mod\" (short
for \"module\").

   module top ();
   ▯
   endmodule "
  (let (block-type block-name return-val) ;return-val will be nil by default
    (setq-local modi/verilog-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward modi/verilog-header-re nil :noerror)
              (re-search-backward modi/verilog-header-re nil :noerror))
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
                     (not (string-match modi/verilog-keywords-re
                                        block-name)))
            (setq-local modi/verilog-which-func-xtra
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
      (modi/verilog-update-which-func-format))
    return-val))

;;;; modi/verilog-jump-to-header-dwim (interactive)
(defun modi/verilog-jump-to-header-dwim (fwd)
  "Jump to a module instantiation header above the current point. If
a module instantiation is not found, jump to a block header if available.

If FWD is non-nil, do that module instrantiation/header search in forward
direction; otherwise in backward direction.

Few examples of what is considered as a block: module, class, package, function,
task, `define."
  (interactive "P")
  (if (modi/verilog-find-module-instance fwd)
      (if fwd
          (re-search-forward modi/verilog-module-instance-re nil :noerror)
        (re-search-backward modi/verilog-module-instance-re nil :noerror))
    (if fwd
        (re-search-forward modi/verilog-header-re nil :noerror)
      (re-search-backward modi/verilog-header-re nil :noerror))))

(defun modi/verilog-jump-to-header-dwim-fwd ()
  "Executes `modi/verilog-jump-to-header' with non-nil argument so that
the point jumps to a module instantiation/block header *below* the current
point."
  (interactive)
  (modi/verilog-jump-to-header-dwim :fwd))

;;;; which-func
(with-eval-after-load 'which-func
;;;;; modi/verilog-which-func
  (defun modi/verilog-which-func ()
    (setq-local which-func-functions '(modi/verilog-find-module-instance
                                       modi/verilog-get-header))
    (which-function-mode))
  (add-hook 'verilog-mode-hook #'modi/verilog-which-func)

;;;;; modi/verilog-update-which-func-format
  (defun modi/verilog-update-which-func-format ()
    (let ((modi/verilog-which-func-echo-help
           (concat "mouse-1/scroll up: jump to header UP" "\n"
                   "mouse-3/scroll-down: jump to header DOWN")))

      (setq-local which-func-keymap
                  (let ((map (make-sparse-keymap)))
                    ;; left click on mode line
                    (define-key map [mode-line mouse-1] #'modi/verilog-jump-to-header-dwim)
                    ;; scroll up action while mouse on mode line
                    (define-key map [mode-line mouse-4] #'modi/verilog-jump-to-header-dwim)
                    ;; middle click on mode line
                    (define-key map [mode-line mouse-2] #'modi/verilog-jump-to-header-dwim-fwd)
                    ;; scroll down action while mouse on mode line
                    (define-key map [mode-line mouse-5] #'modi/verilog-jump-to-header-dwim-fwd)
                    map))

      ;; Customised by Larumbe to keep `which-func' face and a slightly different format
      (if modi/verilog-which-func-xtra
          (setq-local which-func-format
                      `("["
                        (:propertize modi/verilog-which-func-xtra
                                     local-map ,which-func-keymap
                                     face (which-func :weight bold)
                                     mouse-face mode-line-highlight
                                     help-echo ,modi/verilog-which-func-echo-help)
                        ":"
                        (:propertize which-func-current
                                     local-map ,which-func-keymap
                                     face which-func
                                     mouse-face mode-line-highlightp
                                     help-echo ,modi/verilog-which-func-echo-help)
                        "]"))
        (setq-local which-func-format
                    `("["
                      (:propertize which-func-current
                                   local-map ,which-func-keymap
                                   face which-func
                                   mouse-face mode-line-highlight
                                   help-echo ,modi/verilog-which-func-echo-help)
                      "]")))
      ))
  )

;;;; Larumbe Modified to accomodate GLOBAL and ggtags instead of ctags
;;;;; modi/verilog-jump-to-module-at-point (interactive)
(with-eval-after-load 'projectile
  (defun modi/verilog-jump-to-module-at-point ()
    "When in a module instance, jump to that module's definition.

Calling this function again after that *without moving the point* will
call `pop-tag-mark' and jump will be made back to the original position.

Usage: While the point is inside a verilog instance, say, \"core u_core\",
calling this command, will make a jump to \"module core\". When you call this
command again *without moving the point*, the jump will be made back to the
earlier position where the point was inside the \"core u_core\" instance.

It is required to have `ctags' executable and `projectile' package installed,
and to have a `ctags' TAGS file pre-generated for this command to work."
    (interactive)
    (if (and (executable-find "global")
             (projectile-project-root))
        ;; `modi/verilog-which-func-xtra' contains the module name in
        ;; whose instance declaration the point is currently.
        (if (and (modi/verilog-find-module-instance)
                 modi/verilog-which-func-xtra)
            (progn
              (ggtags-find-tag-dwim modi/verilog-which-func-xtra))
          ;; Do `pop-tag-mark' if this command is called when the
          ;; point in *not* inside a verilog instance.
          (pop-tag-mark))
      (user-error "Executable `global' is required for this command to work")))


;;;;; modi/verilog-find-parent-module (interactive)
  (defun modi/verilog-find-parent-module ()
    "Find the places where the current verilog module is instantiated in
the project."
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
          (add-to-list 'ag-arguments "--verilog" :append) ; Modi's
          (when (bound-and-true-p larumbe/ag-use-input-regexps)
            (add-to-list 'ag-arguments "-G" :append)
            (add-to-list 'ag-arguments (concat "\"" (larumbe/project-ag-regexps) "\"") :append))
          (ag-regexp module-instance-pcre (projectile-project-root)))))))

;;;; modi/verilog-selective-indent
;; http://emacs.stackexchange.com/a/8033/115
(defvar modi/verilog-multi-line-define-line-cache nil
  "Variable set to non-nil if the current line is detected as any but the
last line of a multi-line `define such as:

  `define foo(ARG) \          <- non-nil
    begin \                   <- non-nil
      $display(\"Bar\"); \    <- non-nil
      $display(\"Baz\"); \    <- non-nil
    end                       <- nil
 ")

(defun modi/verilog-selective-indent (&rest args)
  "Return non-nil if point is on certain types of lines.

Non-nil return will happen when either of the below is true:
- The current line starts with optional whitespace and then \"// *(space)\".
  Here that * represents one or more consecutive '*' chars.
- The current line contains \"//.\".
  Here that . represents a literal '.' char.
- The current line is part of a multi-line `define like:
    `define foo(ARG) \
      begin \
        $display(\"Bar\"); \
        $display(\"Baz\"); \
      end

If the comment is of \"// *(space)\" style, delete any preceding white space, do
not indent that comment line at all.

This function is used to tweak the `verilog-mode' indentation to skip the lines
containing \"// *(space)\" style of comments in order to not break any
`outline-mode'or `outshine' functionality.

The match with \"//.\" resolves this issue:
  http://www.veripool.org/issues/922-Verilog-mode-Consistent-comment-column
"
  (save-excursion
    (beginning-of-line)
    (let* ((outline-comment (looking-at "^[[:blank:]]*// \\*+\\s-")) ;(blank)// *(space)
           (dont-touch-indentation (looking-at "^.*//\\.")) ;Line contains "//."
           (is-in-multi-line-define (looking-at "^.*\\\\$")) ;\ at EOL
           (do-not-run-orig-fn (or (and (not (bound-and-true-p modi/outshine-allow-space-before-heading))
                                        outline-comment)
                                   dont-touch-indentation
                                   is-in-multi-line-define
                                   modi/verilog-multi-line-define-line-cache)))
      ;; Cache the current value of `is-in-multi-line-define'
      (setq modi/verilog-multi-line-define-line-cache is-in-multi-line-define)
      ;; Force remove any indentation for outline comments
      (when (and (not (bound-and-true-p modi/outshine-allow-space-before-heading))
                 outline-comment)
        (delete-horizontal-space))
      do-not-run-orig-fn)))


;;;; modi/verilog-compile
(defun modi/verilog-compile (option)
  "Compile verilog/SystemVerilog.
If OPTION is \\='(4) (using `\\[universal-argument]' prefix), run simulation.
If OPTION is \\='(16) (using `\\[universal-argument] \\[universal-argument]' prefix), run linter."
  (interactive "P")
  (when (fboundp #'modi/verilog-tool-setup)
    ;; Update values of `verilog-simualator', `verilog-compiler', etc here
    ;; if this function is defined.
    (modi/verilog-tool-setup))
  (cl-case (car option)
    (4  (setq verilog-tool 'verilog-simulator))
    (16 (setq verilog-tool 'verilog-linter))
    (t  (setq verilog-tool 'verilog-compiler)))
  (verilog-set-compile-command)
  (call-interactively #'compile))

(defun modi/verilog-simulate ()
  "Run verilog/SystemVerilog simulation."
  (interactive)
  (modi/verilog-compile '(4)))


;;;; convert block-end comments to block names
(defun modi/verilog-block-end-comments-to-block-names ()
  "Convert valid block-end comments to ': BLOCK_NAME'.

Examples: endmodule // module_name             → endmodule : module_name
          endfunction // some comment          → endfunction // some comment
          endfunction // class_name::func_name → endfunction : func_name
          end // block: block_name             → end : block_name "
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward (concat "^"
                                      "\\(?1:[[:blank:]]*"
                                      modi/verilog-block-end-keywords-re
                                      "\\)"
                                      "[[:blank:]]*//[[:blank:]]*"
                                      "\\(\\(block:\\|"
                                      modi/verilog-identifier-re "[[:blank:]]*::\\)[[:blank:]]*\\)*"
                                      "\\(?2:" modi/verilog-identifier-re "\\)"
                                      "[[:blank:]]*$")
                              nil :noerror)
      ;; Make sure that the matched string after "//" is not a verilog
      ;; keyword.
      (when (not (string-match-p modi/verilog-keywords-re (match-string 2)))
        (replace-match "\\1 : \\2")))))

;;;; Do not open all `included and `defines files for verilog AUTO
(defun modi/verilog-do-not-read-includes ()
  "Replacement for `verilog-read-includes'."
  (message "`verilog-read-includes' has been advised to do nothing"))

(defun modi/verilog-do-not-read-defines ()
  "Replacement for `verilog-read-defines'."
  (message "`verilog-read-defines' has been advised to do nothing"))

(define-minor-mode modi/verilog-do-not-read-includes-defines-mode
  "Do not read all the includes and defines.

Useful to enable this minor mode if you do not want buffers being auto-opened
for all the `included files."
  :init-value nil
  :lighter ""
  (if modi/verilog-do-not-read-includes-defines-mode
      (progn
        (advice-add 'verilog-read-includes :override #'modi/verilog-do-not-read-includes)
        (advice-add 'verilog-read-defines :override #'modi/verilog-do-not-read-defines))
    (progn
      (advice-remove 'verilog-read-includes #'modi/verilog-do-not-read-includes)
      (advice-remove 'verilog-read-defines #'modi/verilog-do-not-read-defines))))

;;;; hideshow
(with-eval-after-load 'hideshow
  (add-to-list 'hs-special-modes-alist
               `(verilog-mode ,(concat "(\\|" modi/verilog-block-start-keywords-re)
                              ,(concat ")\\|" modi/verilog-block-end-keywords-re)
                              nil
                              verilog-forward-sexp-function))
  )



;;;; imenu + outshine
(with-eval-after-load 'outshine
  (defun modi/verilog-outshine-imenu-generic-expression (&rest _)
    "Update `imenu-generic-expression' when using outshine."
    (when (derived-mode-p 'verilog-mode)
      (setq-local imenu-generic-expression
                  (append `(("*Level 1*"
                             ,(concat "^"
                                      (if (bound-and-true-p modi/outshine-allow-space-before-heading)
                                          "[[:blank:]]*"
                                        "")
                                      "// \\*\\{1\\} \\(?1:.*$\\)")
                             1)
                            ("*Level 2*"
                             ,(concat "^"
                                      (if (bound-and-true-p modi/outshine-allow-space-before-heading)
                                          "[[:blank:]]*"
                                        "")
                                      "// \\*\\{2\\} \\(?1:.*$\\)")
                             1)
                            ("*Level 3*"
                             ,(concat "^"
                                      (if (bound-and-true-p modi/outshine-allow-space-before-heading)
                                          "[[:blank:]]*"
                                        "")
                                      "// \\*\\{3\\} \\(?1:.*$\\)")
                             1))
                          verilog-imenu-generic-expression))))

  ;; INFO: Larumbe: Commented out, since `helm-navi' seems to do the trick in a much cleaner manner
  ;; (advice-add 'outshine-mode :after #'modi/verilog-outshine-imenu-generic-expression)
  ;; (advice-remove 'outshine-hook-function #'modi/verilog-outshine-imenu-generic-expression)
  )

;;;; modi/verilog-mode-customization
(defun modi/verilog-mode-customization ()
  "My customization for `verilog-mode'."
  ;; Convert block-end comments to ': BLOCK_NAME' in verilog-mode
  ;; Do this *only* for .sv files. This prevents the slowness of saving
  ;; super-huge .v RTL/Netlist files.
  (when (and (buffer-file-name)
             (string= "sv" (file-name-extension (buffer-file-name)))
             ;; Do not add this hook when working in the verilog-mode reop
             ;; DANGER: Larumbe: Emacs 26.1, the `vc-git--out-ok' causes to paste the git repo URL at the SV visited buffer (probably unintended)
             ;; (not (and (buffer-file-name) ;Has to be a file, and
             ;;           (vc-git-root (buffer-file-name)) ;In a git repo, and
             ;;           (when-let* ((git-repo-remote (vc-git--out-ok "config" "remote.upstream.url")))
             ;;             (string-match-p "veripool/verilog-mode" git-repo-remote)))) ;Upstream URL has to match this.
             ;; End of DANGER
             )
    (add-hook 'before-save-hook #'modi/verilog-block-end-comments-to-block-names nil :local))

  ;; INFO: Larumbe: Seems outshine alignment it is being overriden by own indentation functions
  (with-eval-after-load 'outshine
    ;; Do not require the "// *" style comments used by `outshine' to
    ;; start at column 0 just for this major mode.
    (setq-local modi/outshine-allow-space-before-heading t)))

;; Fri Aug 25 10:51:34 EDT 2017 - kmodi
;; Above, the `modi/outshine-allow-space-before-heading' variable is set to
;; `t' specifically for `verilog-mode'. So do not set the APPEND argument of
;; `add-hook' to non-nil when adding the container function
;; `modi/verilog-mode-customization' to `verilog-mode-hook'. This ensures
;; that that variable is set correctly *before* `outline-minor-mode' is
;; enabled (the act of which runs `outshine-hook-function').



(provide 'verilog-modi-setup)

;;; verilog-modi-setup.el ends here
