;;; python-ts-font-lock.el --- Python tree-sitter custom font-lock scheme  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defgroup python-ts-font-lock nil
  "Python tree-sitter faces."
  :group 'python)

;; INFO: For some reason, if using the prefix 'larumbe/' with a slash yielded query errors
(defvar larumbe--python-ts-self-face 'larumbe--python-ts-self-face)
(defface larumbe--python-ts-self-face
  '((t (:foreground "dark olive green")))
  "Face for python self keyword."
  :group 'python-ts-font-lock)

(defvar larumbe--python-ts-punctuation-face 'larumbe--python-ts-punctuation-face)
(defface larumbe--python-ts-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols, e.g:
!,;:?'=<>*"
  :group 'python-ts-font-lock)

(defvar larumbe--python-ts-punctuation-bold-face 'larumbe--python-ts-punctuation-bold-face)
(defface larumbe--python-ts-punctuation-bold-face
  '((t (:inherit larumbe--python-ts-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|."
  :group 'python-ts-font-lock)

(defvar larumbe--python-ts-brackets-face 'larumbe--python-ts-brackets-face)
(defface larumbe--python-ts-brackets-face
  '((t (:foreground "goldenrod")))
  "Face for brackets []."
  :group 'python-ts-font-lock)

(defvar larumbe--python-ts-parenthesis-face 'larumbe--python-ts-parenthesis-face)
(defface larumbe--python-ts-parenthesis-face
  '((t (:foreground "dark goldenrod")))
  "Face for parenthesis ()."
  :group 'python-ts-font-lock)

(defvar larumbe--python-ts-curly-braces-face 'larumbe--python-ts-curly-braces-face)
(defface larumbe--python-ts-curly-braces-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly braces {}."
  :group 'python-ts-font-lock)

(defvar larumbe--python-ts-braces-content-face 'larumbe--python-ts-braces-content-face)
(defface larumbe--python-ts-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces (subscripts)."
  :group 'python-ts-font-lock)


(setq python--treesit-settings
      (treesit-font-lock-rules
       :feature 'comment
       :language 'python
       '((comment) @font-lock-comment-face)

       :feature 'string
       :language 'python
       '((string) @python--treesit-fontify-string)

       ;; HACK: This feature must come after the string feature and before
       ;; other features.  Maybe we should make string-interpolation an
       ;; option rather than a feature.
       :feature 'string-interpolation
       :language 'python
       '((interpolation) @python--treesit-fontify-string-interpolation)

       :feature 'keyword
       :language 'python
       `([,@python--treesit-keywords] @font-lock-keyword-face
         ((identifier) @larumbe--python-ts-self-face ; DANGER: Changed this font
          (:match "^self$" @larumbe--python-ts-self-face))
         ;; DANGER: Added the following punctuation queries here to avoid modifying the body of `python-ts-mode'
         ["="  "." ","] @larumbe--python-ts-punctuation-face ; DANGER: Check brackets/operators/delimiters below
         ["(" ")"] @larumbe--python-ts-parenthesis-face
         ["[" "]"] @larumbe--python-ts-brackets-face
         ["{" "}"] @larumbe--python-ts-curly-brackets-face

         ([,@python--treesit-operators] @larumbe--python-ts-punctuation-bold-face) ; TODO: Check operators

         ;; (subscript subscript: (integer) @larumbe--python-ts-braces-content-face)
         (subscript subscript: (integer) @larumbe--python-ts-braces-content-face)
         (subscript subscript: (identifier) @larumbe--python-ts-braces-content-face)
         (subscript subscript: (slice) @larumbe--python-ts-braces-content-face)
         ;; (slice @larumbe--python-ts-braces-content-face)
         )

       :feature 'definition
       :language 'python
       '((function_definition
          name: (identifier) @font-lock-function-name-face)
         (class_definition
          name: (identifier) @font-lock-type-face)
         (parameters (identifier) @font-lock-variable-name-face))

       ;; DANGER: Removed this
       ;; :feature 'function
       ;; :language 'python
       ;; '((call function: (identifier) @font-lock-function-call-face)
       ;;   (call function: (attribute
       ;;                    attribute: (identifier) @font-lock-function-call-face)))
       ;; Enf of DANGER

       :feature 'builtin
       :language 'python
       `(((identifier) @font-lock-builtin-face
          (:match ,(rx-to-string
                    `(seq bol
                          (or ,@python--treesit-builtins
                                ,@python--treesit-special-attributes)
                          eol))
           @font-lock-builtin-face)))

       :feature 'constant
       :language 'python
       '([(true) (false) (none)] @font-lock-constant-face)

       ;; DANGER
       ;; :feature 'assignment
       ;; :language 'python
       ;; `(;; Variable names and LHS.
       ;;   (assignment left: (identifier)
       ;;               @font-lock-variable-name-face)
       ;;   (assignment left: (attribute
       ;;                      attribute: (identifier)
       ;;                      @font-lock-property-use-face))
       ;;   (pattern_list (identifier)
       ;;                 @font-lock-variable-name-face)
       ;;   (tuple_pattern (identifier)
       ;;                  @font-lock-variable-name-face)
       ;;   (list_pattern (identifier)
       ;;                 @font-lock-variable-name-face)
       ;;   (list_splat_pattern (identifier)
       ;;                       @font-lock-variable-name-face))
       ;; End of DANGER

       :feature 'decorator
       :language 'python
       '((decorator "@" @font-lock-type-face)
         (decorator (call function: (identifier) @font-lock-type-face))
         (decorator (identifier) @font-lock-type-face))

       :feature 'type
       :language 'python
       `(((identifier) @font-lock-type-face
          (:match ,(rx-to-string
                    `(seq bol (or ,@python--treesit-exceptions)
                          eol))
           @font-lock-type-face))
         (type (identifier) @font-lock-type-face))

       :feature 'escape-sequence
       :language 'python
       :override t
       '((escape_sequence) @font-lock-escape-face)

       :feature 'number
       :language 'python
       '([(integer) (float)] @font-lock-number-face)

       :feature 'property
       :language 'python
       '(
         ;; DANGER
         ;; (attribute
         ;;  attribute: (identifier) @font-lock-property-use-face)
         ;; End of DANGER
         (class_definition
          body: (block
                 (expression_statement
                  (assignment left:
                              (identifier) @font-lock-property-use-face)))))

       :feature 'operator
       :language 'python
       `([,@python--treesit-operators] @font-lock-operator-face)

       :feature 'bracket
       :language 'python
       '(["(" ")" "[" "]" "{" "}"] @font-lock-bracket-face)

       :feature 'delimiter
       :language 'python
       '(["," "." ":" ";" (ellipsis)] @font-lock-delimiter-face)

       :feature 'variable
       :language 'python
       '(
         ;; (identifier) @python--treesit-fontify-variable

         ;; INFO: Added by Larumbe
         (keyword_argument name: (identifier) @font-lock-property-use-face)

         )
       ))


(provide 'python-ts-font-lock)

;;; python-ts-font-lock.el ends here
