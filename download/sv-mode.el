;;; sv-mode.el --- Major mode for editing SystemVerilog files

;; Copyright (C) 2017 Enze Chi

;; Author: Enze Chi <enze.chi@gmail.com>
;; Keywords: systemverilog
;; Version: 0.0.1

;; This file is not part of Emacs

;;; Commentary:

;; This is a major mode for editing SystemVerilog file.  It was
;; initially developed by Enzo Chi.

;;; Installation:

;; To install, just drop this file into a directory in your
;; `load-path' and (optionally) byte-compile it.  To automatically
;; handle files ending in '.sv[h]', add something like:
;;
;;    (require 'sv-mode)
;;    (add-to-list 'auto-mode-alist '("\\.sv[h]$" . sv-mode))
;;
;; to your .emacs file.
;;

;;; Known Bugs:

;;; Code:


;; User definable variables

;;;###autoload
(defgroup sv nil
  "Support for the SystemVerilog serialization format"
  :group 'languages
  :prefix "sv-")

(defcustom sv-mode-hook nil
  "*Hook run by `sv-mode'."
  :type 'hook
  :group 'sv)

(defcustom sv-indent-offset 2
  "*Amount of offset per level of indentation."
  :type 'integer
  :group 'sv)

(defcustom sv-backspace-function 'backward-delete-char-untabify
  "*Function called by `sv-electric-backspace' when deleting backwards.
It will receive one argument, the numeric prefix value."
  :type 'function
  :group 'sv)

(defcustom sv-block-literal-search-lines 100
  "*Maximum number of lines to search for start of block literals."
  :type 'integer
  :group 'sv)

(defcustom sv-block-literal-electric-alist
  '((?| . "") (?> . "-"))
  "*Characters for which to provide electric behavior.
The association list key should be a key code and the associated value
should be a string containing additional characters to insert when
that key is pressed to begin a block literal."
  :type 'alist
  :group 'sv)

(defface sv-tab-face
   '((((class color)) (:background "red" :foreground "red" :bold t))
     (t (:reverse-video t)))
  "Face to use for highlighting tabs in SystemVerilog files."
  :group 'faces
  :group 'sv)

(defcustom sv-imenu-generic-expression
  '((nil  "^\\(:?[a-zA-Z_-]+\\):"          1))
  "The imenu regex to parse an outline of the sv file."
  :type 'string
  :group 'sv)


;; Constants

(defconst sv-mode-version "0.0.1" "Version of `sv-mode'.")

(defconst sv-blank-line-re "^ *$"
  "Regexp matching a line containing only (valid) whitespace.")

(defconst sv-directive-re "^\\(?:--- \\)? *%\\(\\w+\\)"
  "Regexp matching a line contatining a SystemVerilog directive.")

(defconst sv-document-delimiter-re "^ *\\(?:---\\|[.][.][.]\\)"
  "Rexexp matching a SystemVerilog document delimiter line.")

(defconst sv-node-anchor-alias-re "[&*][a-zA-Z0-9_-]+"
  "Regexp matching a SystemVerilog node anchor or alias.")

(defconst sv-tag-re "!!?[^ \n]+"
  "Rexexp matching a SystemVerilog tag.")

(defconst sv-bare-scalar-re
  "\\(?:[^-:,#!\n{\\[ ]\\|[^#!\n{\\[ ]\\S-\\)[^#\n]*?"
  "Rexexp matching a SystemVerilog bare scalar.")

(defconst sv-hash-key-re
  (concat "\\(?:^\\(?:--- \\)?\\|{\\|\\(?:[-,] +\\)+\\) *"
          "\\(?:" sv-tag-re " +\\)?"
          "\\(" sv-bare-scalar-re "\\) *:"
          "\\(?: +\\|$\\)")
  "Regexp matching a single SystemVerilog hash key.")

(defconst sv-scalar-context-re
  (concat "\\(?:^\\(?:--- \\)?\\|{\\|\\(?:[-,] +\\)+\\) *"
          "\\(?:" sv-bare-scalar-re " *: \\)?")
  "Regexp indicating the begininng of a scalar context.")

(defconst sv-nested-map-re
  (concat ".*: *\\(?:&.*\\|{ *\\|" sv-tag-re " *\\)?$")
  "Regexp matching a line beginning a SystemVerilog nested structure.")

(defconst sv-block-literal-base-re " *[>|][-+0-9]* *\\(?:\n\\|\\'\\)"
  "Regexp matching the substring start of a block literal.")

(defconst sv-block-literal-re
  (concat sv-scalar-context-re
          "\\(?:" sv-tag-re "\\)?"
          sv-block-literal-base-re)
  "Regexp matching a line beginning a SystemVerilog block literal.")

(defconst sv-nested-sequence-re
  (concat "^\\(?: *- +\\)+"
          "\\(?:" sv-bare-scalar-re " *:\\(?: +.*\\)?\\)?$")
  "Regexp matching a line containing one or more nested SystemVerilog sequences.")

(defconst sv-constant-scalars-re
  (concat "\\(?:^\\|\\(?::\\|-\\|,\\|{\\|\\[\\) +\\) *"
          (regexp-opt
           '("~" "null" "Null" "NULL"
             ".nan" ".NaN" ".NAN"
             ".inf" ".Inf" ".INF"
             "-.inf" "-.Inf" "-.INF"
             "y" "Y" "yes" "Yes" "YES" "n" "N" "no" "No" "NO"
             "true" "True" "TRUE" "false" "False" "FALSE"
             "on" "On" "ON" "off" "Off" "OFF") t)
          " *$")
  "Regexp matching certain scalar constants in scalar context.")


;; Mode setup

(defvar sv-mode-map ()
  "Keymap used in `sv-mode' buffers.")
(if sv-mode-map
    nil
  (setq sv-mode-map (make-sparse-keymap))
  (define-key sv-mode-map "|" 'sv-electric-bar-and-angle)
  (define-key sv-mode-map ">" 'sv-electric-bar-and-angle)
  (define-key sv-mode-map "-" 'sv-electric-dash-and-dot)
  (define-key sv-mode-map "." 'sv-electric-dash-and-dot)
  (define-key sv-mode-map [backspace] 'sv-electric-backspace))

(defvar sv-mode-syntax-table nil
  "Syntax table in use in `sv-mode' buffers.")
(if sv-mode-syntax-table
    nil
  (setq sv-mode-syntax-table (make-syntax-table))
  (modify-syntax-entry ?\' "\"" sv-mode-syntax-table)
  (modify-syntax-entry ?\" "\"" sv-mode-syntax-table)
  (modify-syntax-entry ?# "<" sv-mode-syntax-table)
  (modify-syntax-entry ?\n ">" sv-mode-syntax-table)
  (modify-syntax-entry ?\\ "\\" sv-mode-syntax-table)
  (modify-syntax-entry ?- "w" sv-mode-syntax-table)
  (modify-syntax-entry ?_ "_" sv-mode-syntax-table)
  (modify-syntax-entry ?\( "." sv-mode-syntax-table)
  (modify-syntax-entry ?\) "." sv-mode-syntax-table)
  (modify-syntax-entry ?\{ "(}" sv-mode-syntax-table)
  (modify-syntax-entry ?\} "){" sv-mode-syntax-table)
  (modify-syntax-entry ?\[ "(]" sv-mode-syntax-table)
  (modify-syntax-entry ?\] ")[" sv-mode-syntax-table))

;;;###autoload
(define-derived-mode sv-mode fundamental-mode "SystemVerilog"
  "Simple mode to edit SystemVerilog.

\\{sv-mode-map}"
  :syntax-table sv-mode-syntax-table
  (set (make-local-variable 'comment-start) "# ")
  (set (make-local-variable 'comment-start-skip) "#+ *")
  (set (make-local-variable 'indent-line-function) 'sv-indent-line)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set (make-local-variable 'font-lock-defaults)
       '(sv-font-lock-keywords
         nil nil nil nil
         (font-lock-syntactic-keywords . sv-font-lock-syntactic-keywords)))
  (font-lock-fontify-buffer))


;; Font-lock support

(defvar sv-font-lock-keywords
   (list
    (cons sv-constant-scalars-re '(1 font-lock-constant-face))
    (cons sv-tag-re '(0 font-lock-type-face))
    (cons sv-node-anchor-alias-re '(0 font-lock-function-name-face))
    (cons sv-hash-key-re '(1 font-lock-variable-name-face))
    (cons sv-document-delimiter-re '(0 font-lock-comment-face))
    (cons sv-directive-re '(1 font-lock-builtin-face))
    '(sv-font-lock-block-literals 0 font-lock-string-face)
    '("^[\t]+" 0 'sv-tab-face t))
   "Additional expressions to highlight in SystemVerilog mode.")

(defvar sv-font-lock-syntactic-keywords
  (list '(sv-syntactic-block-literals 0 "."))
  "Additional syntax features to highlight in SystemVerilog mode.")


(defun sv-font-lock-block-literals (bound)
  "Find lines within block literals.
Find the next line of the first (if any) block literal after point and
prior to BOUND.  Returns the beginning and end of the block literal
line in the match data, as consumed by `font-lock-keywords' matcher
functions.  The function begins by searching backwards to determine
whether or not the current line is within a block literal.  This could
be time-consuming in large buffers, so the number of lines searched is
artificially limitted to the value of
`sv-block-literal-search-lines'."
  (if (eolp) (goto-char (1+ (point))))
  (unless (or (eobp) (>= (point) bound))
    (let ((begin (point))
          (end (min (1+ (point-at-eol)) bound)))
      (goto-char (point-at-bol))
      (while (and (looking-at sv-blank-line-re) (not (bobp)))
        (forward-line -1))
      (let ((nlines sv-block-literal-search-lines)
            (min-level (current-indentation)))
      (forward-line -1)
      (while (and (/= nlines 0)
                  (/= min-level 0)
                  (not (looking-at sv-block-literal-re))
                  (not (bobp)))
        (set 'nlines (1- nlines))
        (unless (looking-at sv-blank-line-re)
          (set 'min-level (min min-level (current-indentation))))
        (forward-line -1))
      (cond
       ((and (< (current-indentation) min-level)
             (looking-at sv-block-literal-re))
          (goto-char end) (set-match-data (list begin end)) t)
         ((progn
            (goto-char begin)
            (re-search-forward (concat sv-block-literal-re
                                       " *\\(.*\\)\n")
                               bound t))
          (set-match-data (nthcdr 2 (match-data))) t))))))

(defun sv-syntactic-block-literals (bound)
  "Find quote characters within block literals.
Finds the first quote character within a block literal (if any) after
point and prior to BOUND.  Returns the position of the quote character
in the match data, as consumed by matcher functions in
`font-lock-syntactic-keywords'.  This allows the mode to treat ['\"]
characters in block literals as punctuation syntax instead of string
syntax, preventing unmatched quotes in block literals from painting
the entire buffer in `font-lock-string-face'."
  (let ((found nil))
    (while (and (not found)
                (/= (point) bound)
                (sv-font-lock-block-literals bound))
      (let ((begin (match-beginning 0)) (end (match-end 0)))
        (goto-char begin)
        (cond
         ((re-search-forward "['\"]" end t) (setq found t))
         ((goto-char end)))))
    found))


;; Indentation and electric keys

(defun sv-compute-indentation ()
  "Calculate the maximum sensible indentation for the current line."
  (save-excursion
    (beginning-of-line)
    (if (looking-at sv-document-delimiter-re) 0
      (forward-line -1)
      (while (and (looking-at sv-blank-line-re)
                  (> (point) (point-min)))
        (forward-line -1))
      (+ (current-indentation)
         (if (looking-at sv-nested-map-re) sv-indent-offset 0)
         (if (looking-at sv-nested-sequence-re) sv-indent-offset 0)
         (if (looking-at sv-block-literal-re) sv-indent-offset 0)))))

(defun sv-indent-line ()
  "Indent the current line.
The first time this command is used, the line will be indented to the
maximum sensible indentation.  Each immediately subsequent usage will
back-dent the line by `sv-indent-offset' spaces.  On reaching column
0, it will cycle back to the maximum sensible indentation."
  (interactive "*")
  (let ((ci (current-indentation))
        (cc (current-column))
        (need (sv-compute-indentation)))
    (save-excursion
      (beginning-of-line)
      (delete-horizontal-space)
      (if (and (equal last-command this-command) (/= ci 0))
          (indent-to (* (/ (- ci 1) sv-indent-offset) sv-indent-offset))
        (indent-to need)))
      (if (< (current-column) (current-indentation))
          (forward-to-indentation 0))))

(defun sv-electric-backspace (arg)
  "Delete characters or back-dent the current line.
If invoked following only whitespace on a line, will back-dent to the
immediately previous multiple of `sv-indent-offset' spaces."
  (interactive "*p")
  (if (or (/= (current-indentation) (current-column)) (bolp))
      (funcall sv-backspace-function arg)
    (let ((ci (current-column)))
      (beginning-of-line)
      (delete-horizontal-space)
      (indent-to (* (/ (- ci (* arg sv-indent-offset))
                       sv-indent-offset)
                    sv-indent-offset)))))

(defun sv-electric-bar-and-angle (arg)
  "Insert the bound key and possibly begin a block literal.
Inserts the bound key.  If inserting the bound key causes the current
line to match the initial line of a block literal, then inserts the
matching string from `sv-block-literal-electric-alist', a newline,
and indents appropriately."
  (interactive "*P")
  (self-insert-command (prefix-numeric-value arg))
  (let ((extra-chars
         (assoc last-command-event
                sv-block-literal-electric-alist)))
    (cond
     ((and extra-chars (not arg) (eolp)
           (save-excursion
             (beginning-of-line)
             (looking-at sv-block-literal-re)))
      (insert (cdr extra-chars))
      (newline-and-indent)))))

(defun sv-electric-dash-and-dot (arg)
  "Insert the bound key and possibly de-dent line.
Inserts the bound key.  If inserting the bound key causes the current
line to match a document delimiter, de-dent the line to the left
margin."
  (interactive "*P")
  (self-insert-command (prefix-numeric-value arg))
  (save-excursion
    (beginning-of-line)
    (if (and (not arg) (looking-at sv-document-delimiter-re))
        (delete-horizontal-space))))


(defun sv-set-imenu-generic-expression ()
  (make-local-variable 'imenu-generic-expression)
  (make-local-variable 'imenu-create-index-function)
  (setq imenu-create-index-function 'imenu-default-create-index-function)
  (setq imenu-generic-expression sv-imenu-generic-expression))

(add-hook 'sv-mode-hook 'sv-set-imenu-generic-expression)


(defun sv-mode-version ()
  "Diplay version of `sv-mode'."
  (interactive)
  (message "sv-mode %s" sv-mode-version)
  sv-mode-version)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.[ds]?vh\\'" . sv-mode))

(provide 'sv-mode)

;;; sv-mode.el ends here
