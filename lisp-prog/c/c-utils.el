;;; c-utils.el --- C/C++ Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defvar larumbe/c-utils-use-lsp nil)

(require 'cc-mode)
(require 'c-ts-mode)
(require 'lsp-mode)

;;;; Tree-sitter
(defgroup c-ts-font-lock nil
  "C/C++ tree-sitter faces."
  :group 'c)

;; INFO: For some reason, if using the prefix 'larumbe/' with a slash yielded query errors
(defvar larumbe--c-ts-namespace-id-face 'larumbe--c-ts-namespace-id-face)
(defface larumbe--c-ts-namespace-id-face
  '((t (:foreground "gray70")))
  "Face for namespace and class identifiers for external methods."
  :group 'c-ts-font-lock)

(defvar larumbe--c-ts-brackets-face 'larumbe--c-ts-brackets-face)
(defface larumbe--c-ts-brackets-face
  '((t (:foreground "goldenrod")))
  "Face for brackets []."
  :group 'c-ts-font-lock)

(defvar larumbe--c-ts-parenthesis-face 'larumbe--c-ts-parenthesis-face)
(defface larumbe--c-ts-parenthesis-face
  '((t (:foreground "dark goldenrod")))
  "Face for parenthesis ()."
  :group 'c-ts-font-lock)

(defvar larumbe--c-ts-curly-braces-face 'larumbe--c-ts-curly-braces-face)
(defface larumbe--c-ts-curly-braces-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly braces {}."
  :group 'c-ts-font-lock)

(defvar larumbe--c-ts-braces-content-face 'larumbe--c-ts-braces-content-face)
(defface larumbe--c-ts-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces (subscripts)."
  :group 'c-ts-font-lock)

(defvar larumbe--c-ts-punctuation-face 'larumbe--c-ts-punctuation-face)
(defface larumbe--c-ts-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols, e.g:
!,;:?'=<>*"
  :group 'c-ts-font-lock)

(defvar larumbe--c-ts-punctuation-bold-face 'larumbe--c-ts-punctuation-bold-face)
(defface larumbe--c-ts-punctuation-bold-face
  '((t (:inherit larumbe--c-ts-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|."
  :group 'c-ts-font-lock)


(defun larumbe/c-ts-mode--fontify-declarator (node override start end &rest _args)
  "Fontify a declarator (whatever under the \"declarator\" field).
For NODE, OVERRIDE, START, END, and ARGS, see
`treesit-font-lock-rules'."
  (let* ((identifier (c-ts-mode--declarator-identifier node))
         (qualified-root
          (treesit-parent-while (treesit-node-parent identifier)
                                (lambda (node)
                                  (equal (treesit-node-type node)
                                         "qualified_identifier"))))
         (face (pcase (treesit-node-type (treesit-node-parent
                                          (or qualified-root
                                              identifier)))
                 ;; ("field_declaration" 'font-lock-property-name-face)
                 ("function_declarator" 'font-lock-function-name-face)
                 ;; (_ 'font-lock-variable-name-face)
                 ))) ; DANGER: Overrid this, removed `font-lock-variable-name-face'
    (when identifier
      (treesit-fontify-with-override
       (treesit-node-start identifier) (treesit-node-end identifier)
       face override start end))))


(defun larumbe/c-ts-mode--font-lock-settings (mode)
  "Tree-sitter font-lock settings.
MODE is either `c' or `cpp'."
  (treesit-font-lock-rules
   :language mode
   :feature 'comment
   `((comment) @font-lock-comment-face
     (comment) @contextual)

   :language mode
   :feature 'preprocessor
   `((preproc_directive) @font-lock-preprocessor-face

     ;; (preproc_def
     ;;  name: (identifier) @font-lock-variable-name-face)

     ;; (preproc_ifdef
     ;;  name: (identifier) @font-lock-variable-name-face)

     (preproc_function_def
      name: (identifier) @font-lock-function-name-face)

     ;; (preproc_params
     ;;  (identifier) @font-lock-variable-name-face)

     (preproc_defined) @font-lock-preprocessor-face
     (preproc_defined (identifier) @font-lock-variable-name-face)
     [,@c-ts-mode--preproc-keywords] @font-lock-preprocessor-face)

   :language mode
   :feature 'constant
   `((true) @font-lock-constant-face
     (false) @font-lock-constant-face
     (null) @font-lock-constant-face
     ,@(when (eq mode 'cpp)
         '((nullptr) @font-lock-constant-face)))

   :language mode
   :feature 'keyword
   `([,@(c-ts-mode--keywords mode)] @font-lock-keyword-face
     ,@(when (eq mode 'cpp)
         '((auto) @font-lock-keyword-face
           (this) @font-lock-keyword-face)))

   :language mode
   :feature 'operator
   `(;; DANGER
     ;; [,@c-ts-mode--operators] @font-lock-operator-face
     ;; ----------------------
     (["<" ">"]) @larumbe--c-ts-parenthesis-face ; Place before operators to override it
     (["." "," ";" "::" "=" "&"]) @larumbe--c-ts-punctuation-face
     ;; [,@c-ts-mode--operators] @larumbe--c-ts-punctuation-bold-face
     [,@c-ts-mode--operators] @larumbe--c-ts-punctuation-face
     "!" @font-lock-negation-char-face)
   ;; End of DANGER

   :language mode
   :feature 'string
   `((string_literal) @font-lock-string-face
     (system_lib_string) @font-lock-string-face
     ,@(when (eq mode 'cpp)
         '((raw_string_literal) @font-lock-string-face)))

   :language mode
   :feature 'literal
   `(;; (number_literal) @font-lock-number-face
     (number_literal) @font-lock-constant-face
     (char_literal) @font-lock-constant-face)

   :language mode
   :feature 'type
   `((primitive_type) @font-lock-type-face
     (type_identifier) @font-lock-type-face
     (sized_type_specifier) @font-lock-type-face
     ,@(when (eq mode 'cpp)
         '((type_qualifier) @font-lock-type-face

           (qualified_identifier
            scope: (namespace_identifier) @larumbe--c-ts-namespace-id-face) ; DANGER: Changed

           (operator_cast) type: (type_identifier) @font-lock-type-face))
     [,@c-ts-mode--type-keywords] @font-lock-type-face)

   :language mode
   :feature 'definition
   ;; Highlights identifiers in declarations.
   `(
     ;; (declaration
     ;;  declarator: (_) @c-ts-mode--fontify-declarator)

     (field_declaration
      declarator: (_) @c-ts-mode--fontify-declarator)

     (function_definition
      declarator: (_) @c-ts-mode--fontify-declarator)

     ;; DANGER
     ;; (parameter_declaration
     ;;  declarator: (_) @c-ts-mode--fontify-declarator)
     ;; End of DANGER

     ;; (enumerator
     ;;  name: (identifier) @font-lock-property-name-face)
     )

   :language mode
   :feature 'assignment
   ;; TODO: Recursively highlight identifiers in parenthesized
   ;; expressions, see `c-ts-mode--fontify-declarator' for
   ;; inspiration.
   '(;; DANGER
     ;; (assignment_expression
     ;;  left: (identifier) @font-lock-variable-name-face)
     ;; End of DANGER
     (assignment_expression
      left: (field_expression field: (_) @font-lock-property-use-face))
     (assignment_expression
      left: (pointer_expression
             (identifier) @font-lock-variable-name-face))
     ;; DANGER
     ;; (assignment_expression
     ;;  left: (subscript_expression
     ;;         (identifier) @font-lock-variable-name-face))
     ;; End of DANGER
     (init_declarator declarator: (_) @c-ts-mode--fontify-declarator))

   ;; DANGER
   ;; :language mode
   ;; :feature 'function
   ;; '((call_expression
   ;;    function:
   ;;    [(identifier) @font-lock-function-call-face
   ;;     (field_expression field: (field_identifier) @font-lock-function-call-face)]))
   ;; End of DANGER

   ;; DANGER
   ;; Based on use of `font-lock-variable-use-face'. Remove for now
   ;; :language mode
   ;; :feature 'variable
   ;; '((identifier) @c-ts-mode--fontify-variable) ;
   ;; End of DANGER

   :language mode
   :feature 'label
   '((labeled_statement
      label: (statement_identifier) @font-lock-constant-face))

   ;; :language mode
   ;; :feature 'error
   ;; '((ERROR) @c-ts-mode--fontify-error)

   :feature 'escape-sequence
   :language mode
   :override t
   '((escape_sequence) @font-lock-escape-face)

   ;; :language mode
   ;; :feature 'property
   ;; '((field_identifier) @font-lock-property-use-face)

   :language mode
   :feature 'bracket
   :feature 'bracket
   '(;; DANGER
     ;; (["(" ")" "[" "]" "{" "}"]) @font-lock-bracket-face
     (["(" ")"]) @larumbe--c-ts-parenthesis-face
     (["[" "]"]) @larumbe--c-ts-brackets-face
     (["{" "}"]) @larumbe--c-ts-curly-braces-face
     )

   :language mode
   :feature 'delimiter
   '((["," ":" ";"]) @font-lock-delimiter-face)

   :language mode
   :feature 'emacs-devel
   :override t
   '(((call_expression
       (call_expression function: (identifier) @fn)
       @c-ts-mode--fontify-defun)
      (:match "^DEFUN$" @fn)))))

(defun larumbe/c-ts-mode-override ()
  "Override builtin font-lock settings for C/C++ tree sitter modes."
  (interactive)
  (advice-add 'c-ts-mode--font-lock-settings :override #'larumbe/c-ts-mode--font-lock-settings)
  (advice-add 'c-ts-mode--fontify-declarator :override #'larumbe/c-ts-mode--fontify-declarator))


;;;; Hooks
(defun larumbe/c-and-c++-mode-hook ()
  "Custom C/C++ hook."
  (hide-ifdef-mode 1)
  (c-toggle-comment-style -1)) ; Default to line-style comment instead of block-style

(defun larumbe/c-and-c++-ts-mode-hook ()
  "Custom C/C++ tree sitter hook."
  (hide-ifdef-mode 1)
  (unless (executable-find "clangd")
    (user-error "Requires clangd"))
  (when larumbe/c-utils-use-lsp
    (lsp)))



(provide 'c-utils)

;;; c-utils.el ends here
