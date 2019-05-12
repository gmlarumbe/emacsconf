;; ============================================================================
;;
;; Program  : rdl-mode.el
;; Language : emacs mode rdl-mode-el -- Major mode for editing RDL files (Register Description Language)
;; Purpose  :
;;            This is a major mode for editing Register Description Language files,
;;            which are used by blueprint tool. RDL is defined in
;;            EDCS-355800.  This mode is based on the wpdl-mode.el file that is
;;            used in the following tutorial: http://two-wugs.net/emacs/mode-tutorial.html
;;
;; Support  : For Tech Support please submit request to:
;;            http:                                        // www.denali.com/support
;;
;; ============================================================================
;;
;;    ******************************************************************
;;    * COPYRIGHT (c) 2005 Denali Software, Inc.  All rights reserved. *
;;    * -------------------------------------------------------------- *
;;    * This code is proprietary and confidential information of       *
;;    * Denali Software. It may not be reproduced, used or transmitted *
;;    * in any form whatsoever without the express and written         *
;;    * permission of Denali Software.                                 *
;;    ******************************************************************
;;
;; ============================================================================
;;; rdl-mode-el -- Major mode for editing RDL files

;; Keywords: RDL major-mode

;;; Commentary:
;;
;; This is a major mode for editing Register Description Language files,
;; which are used by Version 3 of the "blueprint" tool. RDL is defined in
;; EDCS-355800.  This mode is based on the wpdl-mode.el file that is
;; used in the following tutorial:
;; http://two-wugs.net/emacs/mode-tutorial.html
;;
;; This is my first attempt at an emacs mode. I'm not lisp literate, and
;; I wouldn't have had a clue how to do this without the aforementioned
;; tutorial.
;;
;; Note that the indentation rules are entirely inherited from c++-mode.
;; This seems to work reasonably well as long as all embedded perl is
;; treated as if it were a comment. This, however, messes up the
;; colorization of lines with embedded perl variables. "altrdl-mode" is
;; provided for times when the colorization is more important than the
;; indentation of standalone embedded perl lines.  See the comment near
;; the end of this file.
;;
;; So basically this mode is all about font-lock colorization.
;;
;; **** It is highly recommended that you use Emacs 21 if you use  ****
;; **** this mode.  It really doesn't work well with Emacs 20, and ****
;; **** it probably doesn't work at all with Emacs 19.  I don't    ****
;; **** know about Xemacs.                                         ****
;;
;;

;;; Code:
(require 'font-lock)

(defvar rdl-mode-running-xemacs
  (string-match "XEmacs" emacs-version)
  "Are we running XEmacs?")

(defvar rdl-mode-hook nil)

(defvar rdl-mode-map
  (let ((rdl-mode-map (make-keymap)))
    (define-key rdl-mode-map "\C-j" 'newline-and-indent)
    rdl-mode-map)
  "Keymap for RDL major mode")

;; Files with .rdl and .rdlh extensions automatically invoke rdl-mode
(add-to-list 'auto-mode-alist '("\\.rdlh?\\'" . rdl-mode))

(defvar rdl-mode-syntax-table
  (let ((rdl-mode-syntax-table (make-syntax-table)))

    ;; This is added so entity names with underscores can be more easily
    ;; parsed
    (modify-syntax-entry ?_ "w" rdl-mode-syntax-table)

    ;; Comment styles are same as C++

;;     (cond
;;      ((memq '8-bit c-emacs-features)      ; XEmacs
;;       (modify-syntax-entry ?/ ". 1456" rdl-mode-syntax-table))
;;      ((memq '1-bit c-emacs-features)      ; GNU Emacs
;;       (modify-syntax-entry ?/ ". 124b" rdl-mode-syntax-table))
;;      (t (error "RDL Mode is incompatible with this version of Emacs")))
    (if rdl-mode-running-xemacs
        (modify-syntax-entry ?/ ". 1456" rdl-mode-syntax-table)
      (modify-syntax-entry ?/ ". 124b" rdl-mode-syntax-table))

    (modify-syntax-entry ?* ". 23" rdl-mode-syntax-table)
    (modify-syntax-entry ?\n "> b" rdl-mode-syntax-table)

    ;; These lines cause embedded perl to be treated like comments too
;;     (modify-syntax-entry ?< ". 1" rdl-mode-syntax-table)
;;     (modify-syntax-entry ?% ". 23" rdl-mode-syntax-table)
;;     (modify-syntax-entry ?> ". 4" rdl-mode-syntax-table)

    ;; Treat apostrophe as simple punctuation, not a string-quote
    (modify-syntax-entry ?\' "." rdl-mode-syntax-table)

    rdl-mode-syntax-table)
  "Syntax table for rdl-mode")

;; Define rdl-mode as being derived from c++-mode
(define-derived-mode rdl-mode c++-mode "RDL"
  "Major mode for editing Register Description Language files."
  (set (make-local-variable 'font-lock-defaults) '(rdl-font-lock-keywords))
  )

(or (facep 'font-lock-builtin-face)     ; GNU Emacs >= 1996-10-23
    (find-face 'font-lock-builtin-face) ; XEmacs    >= 2002-08-02
    (defface font-lock-builtin-face
      '((((class color) (background light)) (:foreground "Purple"))
        (((class color) (background dark)) (:foreground "Cyan"))
        (((class grayscale) (background light)) (:foreground "LightGray" :bold t))
        (((class grayscale) (background dark)) (:foreground "DimGray" :bold t))
        (t (:bold t)))
      "Font Lock mode face used to highlight builtins."
      :group 'font-lock-faces))

(defconst rdl-font-lock-keywords-1
  (list
   ;; These are RDL component and enum definitions:
   ;; "addrmap" "regfile" "reg" "field" "signal" "enum".
   ;; These are highlighted with the "builtin" face, and the name
   ;; following them (if any) is highlighted with the "variable-name"
   ;; face.
   ;; face.
   ;; Emacs 20 chokes on this for some reason
   ;;    '("\\<\\(addrmap\\|field\\|reg\\(?:file\\)?\\|signal\\|enum\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>"
   ;;      (1 font-lock-builtin-face)
   ;;      (2 font-lock-variable-name-face))
   '("\\<addrmap\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>" ; Emacs 20 workaround
     (1 font-lock-variable-name-face))             ; Emacs 20 workaround
   '("\\<field\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>"   ; Emacs 20 workaround
     (1 font-lock-variable-name-face))             ; Emacs 20 workaround
   '("\\<reg\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>"     ; Emacs 20 workaround
     (1 font-lock-variable-name-face))             ; Emacs 20 workaround
   '("\\<regfile\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>" ; Emacs 20 workaround
     (1 font-lock-variable-name-face))             ; Emacs 20 workaround
   '("\\<signal\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>"  ; Emacs 20 workaround
     (1 font-lock-variable-name-face))             ; Emacs 20 workaround
   '("\\<enum\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>"    ; Emacs 20 workaround
     (1 font-lock-variable-name-face))
   '("\\<\\(addrmap\\|field\\|reg\\(?:file\\)?\\|signal\\|enum\\)\\>"
     (1 font-lock-builtin-face))

   ;; A name following right curly brace is highlighted with the
   ;; "variable-name" face.
   '("}\\s-*\\([a-zA-Z0-9_:<%>=$]+\\)\\s-*[;[=]"
     (1 font-lock-variable-name-face t))

   ;; These are RDL component properties:
   ;; "name" "desc" "rclr" "woclr" "woset" "we" "wel" "swwe"
   ;; "swwel" "hwset" "hwclr" "swmod" "swacc" "sticky"
   ;; "stickybit" "intr" "anded" "ored" "xored" "counter"
   ;; "overflow" "paritycheck" "sharedextbus" "saturate"
   ;; "threshold" "reset" "incr" "incrwidth" "alignment" "width"
   ;; "regwidth" "fieldwidth" "signalwidth" "accesswidth"
   ;; "serialize" "sw" "hw" "addressing" "precedence" "encode"
   ;; "resetsignal" "clock" "mask" "enable" "hwenable" "hwmask"
   ;; "swenable" "swmask" "haltmask" "haltenable" "next" "event"
   ;; "source"
   ;; They are highlighted with the "keyword" face.
   '("\\<\\(a\\(?:ccesswidth\\|ddressing\\|lignment\\|nded\\)\\|c\\(?:lock\\|ounter\\)\\|desc\\|e\\(?:n\\(?:\\(?:abl\\|cod\\)e\\)\\|vent\\)\\|fieldwidth\\|h\\(?:alt\\(?:enable\\|mask\\)\\|w\\(?:clr\\|enable\\|mask\\|set\\)?\\)\\|in\\(?:cr\\(?:width\\)?\\|tr\\)\\|mask\\|n\\(?:ame\\|ext\\)\\|o\\(?:red\\|verflow\\)\\|p\\(?:aritycheck\\|recedence\\)\\|r\\(?:clr\\|e\\(?:gwidth\\|set\\(?:signal\\)?\\)\\)\\|s\\(?:aturate\\|erialize\\|haredextbus\\|ignalwidth\\|ource\\|ticky\\(?:bit\\)?\\|w\\(?:acc\\|enable\\|m\\(?:ask\\|od\\)\\|wel?\\)?\\)\\|threshold\\|w\\(?:el?\\|idth\\|o\\(?:clr\\|set\\)\\)\\|xored\\)\\>" . font-lock-keyword-face)

   ;; These are RDL property modifiers:
   ;; "default" "posedge" "negedge" "bothedge" "level" "nonsticky"
   ;; They are highlighted with the "keyword" face.
   '("\\<\\(bothedge\\|default\\|level\\|n\\(?:egedge\\|onsticky\\)\\|posedge\\)\\>" . font-lock-keyword-face)

   ;; These are field types (names ending in "_field").  They are
   ;; highlighted with the "type" face, and the name following them is
   ;; highlighted with the "variable-name" face.
   '("\\<\\([a-zA-Z0-9_:<%>=$]+_field\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>"
     (1 font-lock-type-face)
     (2 font-lock-variable-name-face))

   ;; These are external types. The word "external" is highlighted with
   ;; the "keyword" face.  The type name is highlighted with the "type"
   ;; face. And the variable name is highlighted with the
   ;; "variable-name" face.

   '("\\<\\(external\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>"
     (1 font-lock-keyword-face)
     (2 font-lock-type-face)
     (3 font-lock-variable-name-face))

   ;; These are alias types. The word "alias" is highlighted with the
   ;; "keyword" face.  The aliased component's name is highlighted with
   ;; the "variable-name" face. The type name is highlighted with the
   ;; "type" face. And the new component's name is highlighted with the
   ;; "variable-name" face.
   '("\\<\\(alias\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\>"
     (1 font-lock-keyword-face)
     (2 font-lock-variable-name-face)
     (3 font-lock-type-face)
     (4 font-lock-variable-name-face))

   ;; These are instantiation types. The type name is highlighted with
   ;; the "type" face. And the instantiation name is highlighted with
   ;; the "variable-name" face.
   '("^\\s-*\\([a-zA-Z0-9_:<%>=$]+\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)[;[]"
     (1 font-lock-type-face)
     (2 font-lock-variable-name-face))
   '("^\\s-*\\([a-zA-Z0-9_:<%>=$]+\\)\\s-+\\([a-zA-Z0-9_:<%>=$]+\\)\\s-+[@]"
     (1 font-lock-type-face)
     (2 font-lock-variable-name-face))

   ;; 'include and 'timescale get font-lock-function-name-face
   '("\\(`\\(?:\\(?:includ\\|timescal\\)e\\)\\)"
     (1 font-lock-function-name-face))

   )
  "Highlighting expressions for RDL mode.")

(defconst rdl-font-lock-keywords-2
  (append rdl-font-lock-keywords-1
          (list
           ;; Highlight the embedded perl start and end indicators and anything
           ;; between them (if on the same line) with "warning" face. This comes
           ;; last so it can override other colors.
           '("<%" 0 font-lock-warning-face t)
           '("%>" 0 font-lock-warning-face t)
           '("@\\s-*[a-zA-Z0-9_]+" 0 font-lock-variable-name-face)
           '("$\\s-*[a-zA-Z0-9_]+" 0 font-lock-variable-name-face)
           '("\\([a-zA-Z0-9_]+\\)\\s-*(" 1 font-lock-function-name-face)
;;            '("<%.*?%>" 0 font-lock-warning-face t)
           ))
  "Highlighting embedded perl in RDL mode.")

(defvar rdl-font-lock-keywords rdl-font-lock-keywords-2
  "Default highlighting expressions for RDL mode.")

;; define functions for embedding a region of perl
(defun rdl-embed-region ()
  "Add <% to the beginning of each line in the region, and >% to the end
of each line."
  (interactive)
  (let ((original-comment-start comment-start)
        (original-comment-end comment-end))
    (setq comment-start "<%")
    (setq comment-end "%>")
    (comment-region (region-beginning) (region-end))
    (setq comment-start original-comment-start)
    (setq comment-end original-comment-end)))

(defun rdl-embed-region-and-indent ()
  "Same as rdl-embed-region, but also indents the region according to
the indentation rules."
  (interactive)
  (rdl-embed-region)
  (indent-region (region-beginning) (region-end) nil)
  )

;; define functions for un-embedding a region of perl
(defun rdl-unembed-region ()
  "Remove all <% and %> from all lines in the region.  Unfortunately not
exactly the reverse of rdl-embed-region if there are <% and %> within
the line. It will remove those too, and rdl-embed-region will not put
them back."
  (interactive)
  (let ((original-comment-start comment-start)
        (original-comment-end comment-end))
    (setq comment-start "<%")
    (setq comment-end "%>")
    (uncomment-region (region-beginning) (region-end))
    (setq comment-start original-comment-start)
    (setq comment-end original-comment-end)))

(defun rdl-unembed-region-and-indent ()
  "Same as rdl-unembed-region, but also indents the region according to
the indentation rules."
  (interactive)
  (rdl-unembed-region)
  (indent-region (region-beginning) (region-end) nil)
  )

;; define RDL mode menu
(require 'easymenu)
(defun rdl-mode-menu (modestr)
  (let ((m
         '(["Embed Region"               rdl-embed-region-and-indent (c-fn-region-is-active-p)]
           ["Unembed Region"             rdl-unembed-region-and-indent (c-fn-region-is-active-p)]
           ["Embed Region (no indent)"   rdl-embed-region (c-fn-region-is-active-p)]
           ["Unembed Region (no indent)" rdl-unembed-region (c-fn-region-is-active-p)]
           ["Alternate RDL mode (better colors)" altrdl-mode (eq major-mode 'rdl-mode)]
           ["Standard RDL mode (better indenting)" rdl-mode (eq major-mode 'altrdl-mode)]
           )))
    (cons modestr m)))

;; add menu to menubar
(easy-menu-define rdl-menu rdl-mode-map "RDL Mode Commands"
  (rdl-mode-menu "RDL"))
(easy-menu-add (rdl-mode-menu "RDL"))

(provide 'rdl-mode)

;; altrdl-mode
;;
;; This is a hack to work around a very minor deficiency in the
;; fontification in rdl-mode. The deficiency is that lines that have
;; embedded perl variables are not always colorized correctly. This
;; problem only occurs when the syntax table is modified to define the
;; embedded perl start and end character sequences (<% and %>) as
;; comment start and end character sequences. But without that
;; modification to the syntax table, standalone lines with embedded perl
;; are not indented correctly. Someday maybe I'll figure out how to make
;; both work in the same mode.  For now there is altrdl-mode, which has
;; better colorization, but improper indentation of standalone imbedded
;; perl lines. Entries in the RDL menu allow for quick switching back
;; and forth between the modes.
;;
(defvar altrdl-mode-hook nil)

(defvar altrdl-mode-syntax-table
  (let ((altrdl-mode-syntax-table (make-syntax-table)))

    ;; This is added so entity names with underscores can be more easily
    ;; parsed
    (modify-syntax-entry ?_ "w" altrdl-mode-syntax-table)

    ; Comment styles are same as C++

;     (cond
;      ((memq '8-bit c-emacs-features)     ; XEmacs
;       (modify-syntax-entry ?/ ". 1456" altrdl-mode-syntax-table))
;      ((memq '1-bit c-emacs-features)      ; GNU Emacs
;       (modify-syntax-entry ?/ ". 124b" altrdl-mode-syntax-table))
;      (t (error "RDL Mode is incompatible with this version of Emacs")))
    (if rdl-mode-running-xemacs
        (modify-syntax-entry ?/ ". 1456" altrdl-mode-syntax-table)
      (modify-syntax-entry ?/ ". 124b" altrdl-mode-syntax-table))

    (modify-syntax-entry ?* ". 23" altrdl-mode-syntax-table)
    (modify-syntax-entry ?\n "> b" altrdl-mode-syntax-table)

    ;; Treat apostrophe as simple punctuation, not a string-quote
    (modify-syntax-entry ?\' "." altrdl-mode-syntax-table)

    altrdl-mode-syntax-table)
  "Syntax table for altrdl-mode")

;; Define altrdl-mode as being derived from rdl-mode
(define-derived-mode altrdl-mode rdl-mode "ALTRDL"
  "Alternate Major mode for editing Register Description Language files.")

(provide 'altrdl-mode)

;;; rdl-mode.el ends here
