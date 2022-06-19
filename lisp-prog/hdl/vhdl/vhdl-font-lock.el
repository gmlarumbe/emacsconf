;;; vhdl-font-lock.el --- VHDL Custom Font Lock  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Strong customization is done on vhdl-keywords-2, as the rest depend on parameters and Emacs groups customizing
;;
;;; Code:

(require 'init-hdl-font-lock)
(require 'init-vhdl)

;;;; Variables
(defvar larumbe/vhdl-common-constructs-re
  (concat
   "^\\s-*\\(\\w+\\)\\s-*:[ \t\n\r\f]*\\(\\("
   "assert\\|block\\|case\\|exit\\|for\\|if\\|loop\\|next\\|null\\|"
   "postponed\\|process\\|"
   "with\\|while"
   "\\)\\>\\|\\w+\\s-*\\(([^\n]*)\\|\\.\\w+\\)*\\s-*<=\\)"))
(defvar larumbe/vhdl-labels-in-block-and-components-re
  (concat
   "^\\s-*for\\s-+\\(\\w+\\(,\\s-*\\w+\\)*\\)\\>\\s-*"
   "\\(:[ \t\n\r\f]*\\(\\w+\\)\\|[^i \t]\\)"))
(defvar larumbe/vhdl-brackets-content-range-re "\\(?1:(\\)\\(?2:[ )+*/$0-9a-zA-Z:_-]*\\)\\s-+\\(?3:\\(down\\)?to\\)\\s-+\\(?4:[ (+*/$0-9a-zA-Z:_-]*\\)\\(?5:)\\)")
(defvar larumbe/vhdl-brackets-content-index-re "\\(?1:(\\)\\s-*\\(?2:[0-9]+\\)\\s-*\\(?3:)\\)")
(defvar larumbe/vhdl-directive-keywords-re (regexp-opt '("psl" "pragma" "synopsys" "synthesis") 'symbols))
(defvar larumbe/vhdl-highlight-variable-declaration-names nil)


;;;; Functions
;; INFO: Search based fontification:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Search_002dbased-Fontification.html
;;     Look for 'function' section.
;; - Based on `verilog-match-translate-off'

(defun larumbe/vhdl-within-translate-off ()
  "Same as analogous `vhdl-mode' function.
Take `larumbe/vhdl-directive-keywords-re' words into account instead of only 'pragma'."
  (and (save-excursion
         (re-search-backward
          (concat
           "^\\s-*--\\s-*" larumbe/vhdl-directive-keywords-re "\\s-*translate_\\(on\\|off\\)\\s-*\n") nil t))
       (equal "off" (match-string 1))
       (point)))

(defun larumbe/vhdl-start-translate-off (limit)
  "Same as analogous `vhdl-mode' function.
Regex search bound to LIMIT.
Take `larumbe/vhdl-directive-keywords-re' words into account instead of only 'pragma'."
  (when (re-search-forward
         (concat
          "^\\s-*--\\s-*" larumbe/vhdl-directive-keywords-re "\\s-*translate_off\\s-*\n") limit t)
    (match-beginning 0)))

(defun larumbe/vhdl-end-translate-off (limit)
  "Same as analogous `vhdl-mode' function.
Regex search bound to LIMIT.
Take `larumbe/vhdl-directive-keywords-re' words into account instead of only 'pragma'."
  (re-search-forward
   (concat "^\\s-*--\\s-*" larumbe/vhdl-directive-keywords-re "\\s-*translate_on\\s-*\n") limit t))

(defun larumbe/vhdl-match-translate-off (limit)
  "Same as analogous `vhdl-mode' function.
Regex search bound to LIMIT.
Take `larumbe/vhdl-directive-keywords-re' words into account instead of only 'pragma'."
  (when (< (point) limit)
    (let ((start (or (larumbe/vhdl-within-translate-off)
                     (larumbe/vhdl-start-translate-off limit)))
          (case-fold-search t))
      (when start
        (let ((end (or (larumbe/vhdl-end-translate-off limit) limit)))
          (put-text-property start end 'font-lock-multiline t)
          (set-match-data (list start end))
          (goto-char end))))))

(defun larumbe/vhdl-match-common-constructs-fontify (limit)
  "Search based fontification function for VHDL common constructs.
Needed since it sets match property as `font-lock-multiline'.
Regex search bound to LIMIT."
  (while (re-search-forward larumbe/vhdl-common-constructs-re limit t)
    (put-text-property (match-beginning 0) (match-end 0) 'font-lock-multiline t)
    (point)))

(defun larumbe/vhdl-match-labels-in-block-and-components-fontify (limit)
  "Search based fontification function for VHDL labels in blocks and components.
Needed since it sets match property as `font-lock-multiline'.
Regex search bound to LIMIT."
  (while (re-search-forward larumbe/vhdl-labels-in-block-and-components-re limit t)
    (put-text-property (match-beginning 0) (match-end 0) 'font-lock-multiline t)
    (point)))



;;;; Font-lock keywords
(defvar larumbe/vhdl-font-lock-keywords-0
  (list
   (list (concat "\\(^\\|[ \t(.']\\)\\(<" vhdl-template-prompt-syntax ">\\)")
         2 'vhdl-font-lock-prompt-face t)
   (list (concat "--\\s-*" larumbe/vhdl-directive-keywords-re "\\s-+\\(.*\\)$")
         '(0 'larumbe/font-lock-translate-off-face prepend)
         '(1 'larumbe/font-lock-preprocessor-face prepend))
   ;; highlight c-preprocessor directives
   (list "^#[ \t]*\\(\\w+\\)\\([ \t]+\\(\\w+\\)\\)?"
         '(1 font-lock-builtin-face)
         '(3 font-lock-variable-name-face nil t))))

;; highlight keywords and standardized types, attributes, enumeration, values, and subprograms
(defvar larumbe/vhdl-font-lock-keywords-1
  (list
   (list (concat "'" vhdl-attributes-regexp)
         1 'vhdl-font-lock-attribute-face)
   (list vhdl-types-regexp       1 'font-lock-type-face)
   (list vhdl-functions-regexp   1 'font-lock-builtin-face)
   (list vhdl-packages-regexp    1 'font-lock-builtin-face)
   (list vhdl-enum-values-regexp 1 'vhdl-font-lock-enumvalue-face)
   (list vhdl-constants-regexp   1 'font-lock-constant-face)
   (list vhdl-keywords-regexp    1 'font-lock-keyword-face)))

;; Strong customization
(defvar larumbe/vhdl-font-lock-keywords-2
  (append
   (list
    ;; highlight names of units, subprograms, and components when declared
    (list
     (concat
      "^\\s-*\\("
      "architecture\\|configuration\\|context\\|entity\\|package"
      "\\(\\s-+body\\)?\\|"
      "\\(\\(impure\\|pure\\)\\s-+\\)?function\\|procedure\\|component"
      "\\)\\s-+\\(\\w+\\)")
     5 'font-lock-function-name-face)

    ;; highlight entity names of architectures and configurations
    (list
     "^\\s-*\\(architecture\\|configuration\\)\\s-+\\w+\\s-+of\\s-+\\(\\w+\\)"
     2 'font-lock-function-name-face)

    ;; highlight labels of common constructs (use function to add `font-lock-multiline' property)
    '(larumbe/vhdl-match-common-constructs-fontify
      (1 'font-lock-function-name-face))

    ;; highlight label and component name of every instantiation (configuration, component and entity)
    (list
     larumbe/vhdl-instance-re
     '(1 larumbe/font-lock-instance-face prepend)
     '(5 larumbe/font-lock-dot-expression-face nil t) ; 3rd argument nil avoids font-locking in case there is no match (no entity instantiation)
     '(6 larumbe/font-lock-module-face prepend))

    ;; highlight names and labels at end of constructs
    (list
     (concat
      "^\\s-*end\\s-+\\(\\("
      "architecture\\|block\\|case\\|component\\|configuration\\|context\\|"
      "entity\\|for\\|function\\|generate\\|if\\|loop\\|package"
      "\\(\\s-+body\\)?\\|procedure\\|\\(postponed\\s-+\\)?process\\|"
      "units"
      "\\)\\s-+\\)?\\(\\w*\\)")
     5 'font-lock-function-name-face)

    ;; highlight labels in exit and next statements
    (list
     (concat
      "^\\s-*\\(\\w+\\s-*:\\s-*\\)?\\(exit\\|next\\)\\s-+\\(\\w*\\)")
     3 'font-lock-function-name-face)

    ;; highlight entity name in attribute specifications
    (list
     (concat
      "^\\s-*attribute\\s-+\\w+\\s-+of\\s-+\\(\\w+\\(,\\s-*\\w+\\)*\\)\\s-*:")
     1 'font-lock-function-name-face)

    ;; highlight labels in block and component specifications
    '(larumbe/vhdl-match-labels-in-block-and-components-fontify
      (1 font-lock-function-name-face) (4 font-lock-function-name-face nil t))

    ;; highlight names in library clauses
    (list "^\\s-*library\\>"
          '(vhdl-font-lock-match-item nil nil (1 font-lock-function-name-face)))

    ;; highlight names in use clauses
    (list
     (concat
      "\\<\\(context\\|use\\)\\s-+\\(\\(entity\\|configuration\\)\\s-+\\)?"
      "\\(\\w+\\)\\(\\.\\(\\w+\\)\\)?\\((\\(\\w+\\))\\)?")
     '(4 font-lock-function-name-face) '(6 font-lock-function-name-face nil t)
     '(8 font-lock-function-name-face nil t))

    ;; highlight attribute name in attribute declarations/specifications
    (list
     (concat
      "^\\s-*attribute\\s-+\\(\\w+\\)")
     1 'vhdl-font-lock-attribute-face)

    ;; highlight type/nature name in (sub)type/(sub)nature declarations
    (list
     (concat
      "^\\s-*\\(\\(sub\\)?\\(nature\\|type\\)\\|end\\s-+\\(record\\|protected\\)\\)\\s-+\\(\\w+\\)")
     5 'font-lock-type-face)

    ;; highlight formal parameters in component instantiations and subprogram
    ;; calls
    (list "\\(=>\\)"
          '(vhdl-font-lock-match-item
            (progn (goto-char (match-beginning 1))
                   (skip-syntax-backward " ")
                   (while (= (preceding-char) ?\)) (backward-sexp))
                   (skip-syntax-backward "w_")
                   (skip-syntax-backward " ")
                   (when (memq (preceding-char) '(?n ?N ?|))
                     (goto-char (point-max))))
            (goto-char (match-end 1)) (1 larumbe/font-lock-port-connection-face)))

    ;; highlight alias/group/quantity declaration names and for-loop/-generate
    ;; variables
    (list "\\<\\(alias\\|for\\|group\\|quantity\\)\\s-+\\w+\\s-+\\(across\\|in\\|is\\)\\>"
          '(vhdl-font-lock-match-item
            (progn (goto-char (match-end 1)) (match-beginning 2))
            nil (1 font-lock-variable-name-face)))

    ;; highlight tool directives
    (list
     (concat
      "^\\s-*\\(`\\w+\\)")
     1 'font-lock-preprocessor-face)


    ;; Own Verilog-based customization
    (list larumbe/punctuation-re                0 larumbe/font-lock-punctuation-face)
    (list larumbe/punctuation-bold-re           0 larumbe/font-lock-punctuation-bold-face)
    (list larumbe/vhdl-brackets-content-range-re ; Bit range
          '(1 larumbe/font-lock-curly-brackets-face prepend)
          '(5 larumbe/font-lock-curly-brackets-face prepend)
          '(2 larumbe/font-lock-braces-content-face prepend)
          '(4 larumbe/font-lock-braces-content-face prepend)
          '(3 larumbe/font-lock-dot-expression-face prepend))
    (list larumbe/vhdl-brackets-content-index-re ; Bit index
          '(1 larumbe/font-lock-curly-brackets-face prepend)
          '(3 larumbe/font-lock-curly-brackets-face prepend)
          '(2 larumbe/font-lock-braces-content-face prepend))
    (list larumbe/braces-re                  0 larumbe/font-lock-braces-face)
    (list larumbe/brackets-re                0 larumbe/font-lock-brackets-face)
    (list larumbe/curly-brackets-re          0 larumbe/font-lock-curly-brackets-face)
    )

   ;; highlight signal/variable/constant declaration names
   (when larumbe/vhdl-highlight-variable-declaration-names
     (list "\\(:[^=]\\)"
           '(vhdl-font-lock-match-item
             (progn (goto-char (match-beginning 1))
                    (skip-syntax-backward " ")
                    (skip-syntax-backward "w_")
                    (skip-syntax-backward " ")
                    (while (= (preceding-char) ?,)
                      (backward-char 1)
                      (skip-syntax-backward " ")
                      (skip-syntax-backward "w_")
                      (skip-syntax-backward " ")))
             (goto-char (match-end 1)) (1 larumbe/font-lock-variable-name-face))))
   )
  ;;   "For consideration as a value of `vhdl-font-lock-keywords'.
  ;; This does context sensitive highlighting of names and labels."
  )


;; highlight words with special syntax.
(defvar larumbe/vhdl-font-lock-keywords-3
  (let ((syntax-alist vhdl-special-syntax-alist) ; "generic/constant" "type" "variable"
        keywords)
    (while syntax-alist
      (setq keywords
            (cons
             (list (concat "\\(" (nth 1 (car syntax-alist)) "\\)") 1
                   (vhdl-function-name
                    "vhdl-font-lock" (nth 0 (car syntax-alist)) "face")
                   (nth 4 (car syntax-alist)))
             keywords))
      (setq syntax-alist (cdr syntax-alist)))
    keywords))

;; highlight additional reserved words
(defvar larumbe/vhdl-font-lock-keywords-4
  (list (list vhdl-reserved-words-regexp 1
              'vhdl-font-lock-reserved-words-face)))

;; highlight translate_off regions
(defvar larumbe/vhdl-font-lock-keywords-5
  '((larumbe/vhdl-match-translate-off
     (0 larumbe/font-lock-translate-off-face prepend))))

;; highlight everything together
(defvar larumbe/vhdl-font-lock-keywords
  (append
   larumbe/vhdl-font-lock-keywords-0
   larumbe/vhdl-font-lock-keywords-1
   larumbe/vhdl-font-lock-keywords-4 ; Empty by default
   larumbe/vhdl-font-lock-keywords-3
   larumbe/vhdl-font-lock-keywords-2
   larumbe/vhdl-font-lock-keywords-5
   ))



;;;; Config
(font-lock-add-keywords 'vhdl-mode larumbe/vhdl-font-lock-keywords 'set)


(provide 'vhdl-font-lock)

;;; vhdl-font-lock.el ends here
