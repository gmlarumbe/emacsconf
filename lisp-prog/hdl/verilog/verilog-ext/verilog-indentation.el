;;; verilog-indentation.el --- Custom Verilog Indentation  -*- lexical-binding: nil -*-
;;; Commentary:
;;
;; INFO: `lexical-binding' is set to nil in this file, since `verilog-mode'
;; doesn't have this variable set either. The overriden function
;; `verilog-ext-do-indent' gave some errors with lexical-binding enabled.
;;
;; Functions of these file are copied from `verilog-mode' with the purpose of
;; advising them to obtain a custom indentation scheme.
;;
;;; Code:


(require 'verilog-mode)


;;;; Variables
;; Modify zero-indent words to exclude 'class' since they will normally be declared within packages.
;; Simply override value of `verilog-zero-indent-re' excluding "class" and
;; "endclass" from their respective lists.
(defconst verilog-ext-zero-indent-defun-re
  (eval-when-compile (verilog-regexp-words '("macromodule" "connectmodule" "module" "program" "interface" "package" "primitive" "config"))))
(defconst verilog-ext-zero-indent-end-defun-re
  (eval-when-compile (verilog-regexp-words '("endconnectmodule" "endmodule" "endprogram" "endinterface" "endpackage" "endprimitive" "endconfig"))))
(defconst verilog-zero-indent-re
  (concat verilog-ext-zero-indent-defun-re "\\|" verilog-ext-zero-indent-end-defun-re))



;; Following section is intended to add a hook via `verilog-ext-custom-declaration-core-re'
;; variable to add new keywords for indentation of SystemVerilog interface port declarations.
(defvar verilog-ext-custom-declaration-core-re nil
  "Verilog custom declaration keywords used for indentation.")

;; Same as original `verilog-mode' constant but appending list of strings
;; `verilog-ext-custom-declaration-core-re' to existent list of strings.
(defconst verilog-declaration-core-re
  (eval-when-compile
    (verilog-regexp-words
     (append '(;; port direction (by themselves)
               "inout" "input" "output"
               ;; integer_atom_type
               "byte" "shortint" "int" "longint" "integer" "time"
               ;; integer_vector_type
               "bit" "logic" "reg"
               ;; non_integer_type
               "shortreal" "real" "realtime"
               ;; net_type
               "supply0" "supply1" "tri" "triand" "trior" "trireg" "tri0" "tri1" "uwire" "wire" "wand" "wor"
               ;; misc
               "string" "event" "chandle" "virtual" "enum" "genvar"
               "struct" "union"
               ;; builtin classes
               "mailbox" "semaphore")
             ;; INFO: Custom declaration constructs hook
             verilog-ext-custom-declaration-core-re))))


(defconst verilog-declaration-re
  (concat "\\(" verilog-declaration-prefix-re "\\s-*\\)?" verilog-declaration-core-re))

(defconst verilog-declaration-re-2-no-macro
  (concat "\\s-*" verilog-declaration-re
          "\\s-*\\(\\(" verilog-optional-signed-range-re "\\)\\|\\(" verilog-delay-re "\\)"
          "\\)"))
(defconst verilog-declaration-re-2-macro
  (concat "\\s-*" verilog-declaration-re
          "\\s-*\\(\\(" verilog-optional-signed-range-re "\\)\\|\\(" verilog-delay-re "\\)"
          "\\|\\(" verilog-macroexp-re "\\)"
          "\\)"))
(defconst verilog-declaration-re-1-macro
  (concat "^" verilog-declaration-re-2-macro))

(defconst verilog-declaration-re-1-no-macro (concat "^" verilog-declaration-re-2-no-macro))



;;;; Functions
(defun verilog-ext-beg-of-statement ()
  "Move backward to beginning of statement."
  (interactive)
  (if (verilog-in-comment-p)
      (verilog-backward-syntactic-ws))
  (let ((pt (point)))
    (catch 'done
      (while (not (looking-at verilog-defun-level-not-generate-re))
        (setq pt (point))
        (verilog-backward-syntactic-ws)
        (if (or (bolp)
                (= (preceding-char) ?\;)
                (progn
                  (verilog-backward-token)
                  ;; INFO: Difference with respect to `verilog-beg-of-statement-1'
                  (or
                   (looking-at verilog-ends-re)
                   (looking-at "begin")  ; First instance within generate
                   ;; End of INFO
                   )))
            (progn
              (goto-char pt)
              (throw 'done t)))))
    (verilog-forward-syntactic-ws)))



(defun verilog-ext-calculate-indent ()
  "Same as `verilog-calculate-indent'.
Modified to avoid issues when indent parameters/ports if `verilog-indent-lists'
is nil"
  (save-excursion
    (let* ((starting_position (point))
           (case-fold-search nil)
           (par 0)
           (begin (looking-at "[ \t]*begin\\>"))
           (lim (save-excursion (verilog-re-search-backward "\\(\\<begin\\>\\)\\|\\(\\<\\(connect\\)?module\\>\\)" nil t)))
           (structres nil)
           (type (catch 'nesting
                   ;; Keep working backwards until we can figure out
                   ;; what type of statement this is.
                   ;; Basically we need to figure out
                   ;; 1) if this is a continuation of the previous line;
                   ;; 2) are we in a block scope (begin..end)

                   ;; if we are in a comment, done.
                   (if (verilog-in-star-comment-p)
                       (throw 'nesting 'comment))

                   ;; if we have a directive, done.
                   (if (save-excursion (beginning-of-line)
                                       (and (looking-at verilog-directive-re-1)
                                            (not (or (looking-at "[ \t]*`[ou]vm_")
                                                     (looking-at "[ \t]*`vmm_")))))
                       (throw 'nesting 'directive))
                   ;; indent structs as if there were module level
                   (setq structres (verilog-in-struct-nested-p))
                   (cond ((not structres) nil)
                         ;;((and structres (equal (char-after) ?\})) (throw 'nesting 'struct-close))
                         ((> structres 0) (throw 'nesting 'nested-struct))
                         ((= structres 0) (throw 'nesting 'block))
                         (t nil))

                   ;; if we are in a parenthesized list, and the user likes to indent these, return.
                   ;; unless we are in the newfangled coverpoint or constraint blocks
                   (if (and
                        ;; INFO: Comment to avoid issues when indenting parameters and ports if this parameter is set to nil
                        ;; verilog-indent-lists
                        ;; End of INFO
                        (verilog-in-paren)
                        (not (verilog-in-coverage-p))
                        )
                       (progn (setq par 1)
                              (throw 'nesting 'block)))

                   ;; See if we are continuing a previous line
                   (while t
                     ;; trap out if we crawl off the top of the buffer
                     (if (bobp) (throw 'nesting 'cpp))

                     (if (and (verilog-continued-line-1 lim)
                              (or (not (verilog-in-coverage-p))
                                  (looking-at verilog-in-constraint-re) ))  ; may still get hosed if concat in constraint
                         (let ((sp (point)))
                           (if (and
                                (not (looking-at verilog-complete-reg))
                                (verilog-continued-line-1 lim))
                               (progn (goto-char sp)
                                      (throw 'nesting 'cexp))

                             (goto-char sp))
                           (if (and (verilog-in-coverage-p)
                                    (looking-at verilog-in-constraint-re))
                               (progn
                                 (beginning-of-line)
                                 (skip-chars-forward " \t")
                                 (throw 'nesting 'constraint)))
                           (if (and begin
                                    (not verilog-indent-begin-after-if)
                                    (looking-at verilog-no-indent-begin-re))
                               (progn
                                 (beginning-of-line)
                                 (skip-chars-forward " \t")
                                 (throw 'nesting 'statement))
                             (progn
                               (throw 'nesting 'cexp))))
                       ;; not a continued line
                       (goto-char starting_position))

                     (if (looking-at "\\<else\\>")
                         ;; search back for governing if, striding across begin..end pairs
                         ;; appropriately
                         (let ((elsec 1))
                           (while (verilog-re-search-backward verilog-ends-re nil 'move)
                             (cond
                              ((match-end 1) ; else, we're in deep
                               (setq elsec (1+ elsec)))
                              ((match-end 2) ; if
                               (setq elsec (1- elsec))
                               (if (= 0 elsec)
                                   (if verilog-align-ifelse
                                       (throw 'nesting 'statement)
                                     (progn  ; back up to first word on this line
                                       (beginning-of-line)
                                       (verilog-forward-syntactic-ws)
                                       (throw 'nesting 'statement)))))
                              ((match-end 3) ; assert block
                               (setq elsec (1- elsec))
                               (verilog-beg-of-statement)  ; doesn't get to beginning
                               (if (looking-at verilog-property-re)
                                   (throw 'nesting 'statement)  ; We don't need an endproperty for these
                                 (throw 'nesting 'block)        ; We still need an endproperty
                                 ))
                              (t ; endblock
                               ;; try to leap back to matching outward block by striding across
                               ;; indent level changing tokens then immediately
                               ;; previous line governs indentation.
                               (let (( reg) (nest 1))
                                 ;;      verilog-ends =>  else|if|end|join(_any|_none|)|endcase|endclass|endtable|endspecify|endfunction|endtask|endgenerate|endgroup
                                 (cond
                                  ((match-end 4) ; end
                                   ;; Search back for matching begin
                                   (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" ))
                                  ((match-end 5) ; endcase
                                   ;; Search back for matching case
                                   (setq reg "\\(\\<randcase\\>\\|\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" ))
                                  ((match-end 6) ; endfunction
                                   ;; Search back for matching function
                                   (setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" ))
                                  ((match-end 7) ; endtask
                                   ;; Search back for matching task
                                   (setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" ))
                                  ((match-end 8) ; endspecify
                                   ;; Search back for matching specify
                                   (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
                                  ((match-end 9) ; endtable
                                   ;; Search back for matching table
                                   (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" ))
                                  ((match-end 10) ; endgenerate
                                   ;; Search back for matching generate
                                   (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
                                  ((match-end 11) ; joins
                                   ;; Search back for matching fork
                                   (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|none\\)?\\>\\)" ))
                                  ((match-end 12) ; class
                                   ;; Search back for matching class
                                   (setq reg "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)" ))
                                  ((match-end 13) ; covergroup
                                   ;; Search back for matching covergroup
                                   (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)" )))
                                 (catch 'skip
                                   (while (verilog-re-search-backward reg nil 'move)
                                     (cond
                                      ((match-end 1) ; begin
                                       (setq nest (1- nest))
                                       (if (= 0 nest)
                                           (throw 'skip 1)))
                                      ((match-end 2) ; end
                                       (setq nest (1+ nest)))))
                                   )))))))
                     (throw 'nesting (verilog-calc-1)))
                   )  ; catch nesting
                 ) ; type
           )
      ;; Return type of block and indent level.
      (if (not type)
          (setq type 'cpp))
      (if (> par 0)                     ; Unclosed Parenthesis
          (list 'cparenexp par)
        (cond
         ((eq type 'case)
          (list type (verilog-case-indent-level)))
         ((eq type 'statement)
          (list type (current-column)))
         ((eq type 'defun)
          (list type 0))
         ((eq type 'constraint)
          (list 'block (current-column)))
         ((eq type 'nested-struct)
          (list 'block structres))
         (t
          (list type (verilog-current-indent-level))))))))



(defun verilog-ext-do-indent (indent-str)
  "Same as `verilog-do-indent'.
Modified to avoid issues when indent parameters/ports if `verilog-indent-lists'
is nil.
INFO: -*- lexical-binding: t -*- gave some errors."
  (let ((type (car indent-str))
        (ind (car (cdr indent-str))))
    (cond
     (; handle continued exp
      (eq type 'cexp)
      (let ((here (point)))
        (verilog-backward-syntactic-ws)
        (cond
         ((or
           (= (preceding-char) ?\,)
           (save-excursion
             (verilog-beg-of-statement-1)
             (looking-at verilog-declaration-re)))
          (let* ( fst
                  (val
                   (save-excursion
                     (backward-char 1)
                     (verilog-beg-of-statement-1)
                     (setq fst (point))
                     (if (looking-at verilog-declaration-re)
                         (progn  ; we have multiple words
                           (goto-char (match-end 0))
                           (skip-chars-forward " \t")
                           (cond
                            ((and verilog-indent-declaration-macros
                                  (= (following-char) ?\`))
                             (progn
                               (forward-char 1)
                               (forward-word-strictly 1)
                               (skip-chars-forward " \t")))
                            ((= (following-char) ?\[)
                             (progn
                               (forward-char 1)
                               (verilog-backward-up-list -1)
                               (skip-chars-forward " \t"))))
                           (current-column))
                       (progn
                         (goto-char fst)
                         (+ (current-column) verilog-cexp-indent))))))
            (goto-char here)
            (indent-line-to val)
            (if (and (not verilog-indent-lists)
                     (verilog-in-paren))
                (verilog-pretty-declarations-auto))
            ))
         ((= (preceding-char) ?\) )
          (goto-char here)
          (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
            (indent-line-to val)))
         (t
          (goto-char here)
          (let ((val))
            (verilog-beg-of-statement-1)
            (if (and (< (point) here)
                     (verilog-re-search-forward "=[ \t]*" here 'move)
                     ;; not at a |=>, #=#, or [=n] operator
                     (not (string-match "\\[=.\\|#=#\\||=>"
                                        (or (buffer-substring (- (point) 2) (1+ (point)))
                                            ""))))  ; don't let buffer over/under-run spoil the party
                (setq val (current-column))
              (setq val (eval (cdr (assoc type verilog-indent-alist)))))
            (goto-char here)
            (indent-line-to val))))))

     (; handle inside parenthetical expressions
      (eq type 'cparenexp)
      (let* ( here
              ;; INFO: New code to indent with `verilog-indent-lists' as `t' as if it was false
              (close-par (looking-at ")"))
              (val (save-excursion
                     (verilog-backward-up-list 1)
                     (verilog-ext-beg-of-statement)
                     (setq here (point))
                     (if close-par
                         (current-column)
                       (+ (current-column) verilog-indent-level))))
              ;; End of INFO
              (decl (save-excursion
                      (goto-char here)
                      (verilog-forward-syntactic-ws)
                      (setq here (point))
                      (looking-at verilog-declaration-re))))
        (indent-line-to val)
        (if decl
            (verilog-pretty-declarations-auto))))

     (;-- Handle the ends
      (or
       (looking-at verilog-end-block-re)
       (verilog-at-close-constraint-p)
       (verilog-at-close-struct-p))
      (let ((val (if (eq type 'statement)
                     (- ind verilog-indent-level)
                   ind)))
        (indent-line-to val)))

     (;-- Case -- maybe line 'em up
      (and (eq type 'case) (not (looking-at "^[ \t]*$")))
      (progn
        (cond
         ((looking-at "\\<endcase\\>")
          (indent-line-to ind))
         (t
          (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
            (indent-line-to val))))))

     (;-- defun
      (and (eq type 'defun)
           (looking-at verilog-zero-indent-re))
      (indent-line-to 0))

     (;-- declaration
      (and (or
            (eq type 'defun)
            (eq type 'block))
           (looking-at verilog-declaration-re)
           ;; Do not consider "virtual function", "virtual task", "virtual class"
           ;; as declarations
           (not (looking-at (concat verilog-declaration-re
                                    "\\s-+\\(function\\|task\\|class\\)\\b"))))
      (verilog-indent-declaration ind))

     (;-- form feeds - ignored as bug in indent-line-to in < 24.5
      (looking-at "\f"))

     (;-- Everything else
      t
      ;; INFO: Issues with lexical binding
      (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
        (indent-line-to val))))
    ;; End of INFO

    (if (looking-at "[ \t]+$")
        (skip-chars-forward " \t"))
    indent-str                          ; Return indent data
    ))


;;;; Config
(advice-add 'verilog-calculate-indent :override #'verilog-ext-calculate-indent)
(advice-add 'verilog-do-indent        :override #'verilog-ext-do-indent)



;;;; Modi
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
;; Advise the indentation behavior of `indent-region' done using `C-M-\'
;; (advice-add 'verilog-indent-line-relative :before-until #'modi/verilog-selective-indent)
;; Advise the indentation done by hitting `TAB'
;; (advice-add 'verilog-indent-line :before-until #'modi/verilog-selective-indent)



;; Do not break any `outline-mode'or `outshine' functionality
(advice-add 'verilog-indent-line-relative :before-until #'modi/verilog-selective-indent) ;; Advise the indentation behavior of `indent-region' done using `C-M-\'
(advice-add 'verilog-indent-line          :before-until #'modi/verilog-selective-indent) ;; Advise the indentation done by hitting `TAB' (modi multi-line defines)




(provide 'verilog-indentation)

;;; verilog-indentation.el ends here
