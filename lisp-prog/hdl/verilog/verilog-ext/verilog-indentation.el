;;; verilog-indentation.el --- Custom Verilog Indentation  -*- lexical-binding: nil -*-
;;; Commentary:
;;; Code:


(require 'verilog-mode)


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
