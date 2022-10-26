;;; vhdl-font-lock.el --- VHDL Custom Font Lock  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Strong customization is done on vhdl-keywords-2, as the rest depend on
;; parameters and Emacs groups customizing
;;
;;; Code:

(require 'init-hdl-font-lock)
(require 'init-vhdl)

;;;; Faces
(defvar vhdl-ext-font-lock-punctuation-face 'vhdl-ext-font-lock-punctuation-face)
(defface vhdl-ext-font-lock-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols: !,;:?'=<>*"
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-punctuation-bold-face 'vhdl-ext-font-lock-punctuation-bold-face)
(defface vhdl-ext-font-lock-punctuation-bold-face
  '((t (:inherit vhdl-ext-font-lock-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|."
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-braces-face 'vhdl-ext-font-lock-braces-face)
(defface vhdl-ext-font-lock-braces-face
  '((t (:foreground "goldenrod")))
  "Face for braces []."
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-brackets-face 'vhdl-ext-font-lock-brackets-face)
(defface vhdl-ext-font-lock-brackets-face
  '((t (:foreground "dark goldenrod")))
  "Face for brackets ()."
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-curly-brackets-face 'vhdl-ext-font-lock-curly-brackets-face)
(defface vhdl-ext-font-lock-curly-brackets-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly brackets {}."
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-braces-content-face 'vhdl-ext-font-lock-braces-content-face)
(defface vhdl-ext-font-lock-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces: arrays, bit vector width and indexing."
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-port-connection-face 'vhdl-ext-font-lock-port-connection-face)
(defface vhdl-ext-font-lock-port-connection-face
  '((t (:foreground "bisque2")))
  "Face for port connections of instances.
portA => signalA,
portB => signalB
);
"
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-entity-face 'vhdl-ext-font-lock-entity-face)
(defface vhdl-ext-font-lock-entity-face
  '((t (:foreground "green1")))
  "Face for entity names."
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-instance-face 'vhdl-ext-font-lock-instance-face)
(defface vhdl-ext-font-lock-instance-face
  '((t (:foreground "medium spring green")))
  "Face for instance names."
  :group 'vhdl-ext-font-lock-faces)

(defvar vhdl-ext-font-lock-instance-lib-face 'vhdl-ext-font-lock-instance-lib-face)
(defface vhdl-ext-font-lock-instance-lib-face
  '((t (:foreground "gray70")))
  "Face for interfaces prefix (also applies to objects methods calling)
...
axi_if.Ready <= 1'b1;
obj.method();
"
  :group 'vhdl-ext-font-lock-faces)


;;;; Variables
(defconst vhdl-ext-font-lock-punctuation-re "\\([!,;:?'=<>]\\|\\*\\)")
(defconst vhdl-ext-font-lock-punctuation-bold-re "\\([&^~+-]\\||\\|\\.\\|\\/\\)")
(defconst vhdl-ext-font-lock-brackets-re "[()]")
(defconst vhdl-ext-font-lock-curly-brackets-re "[{}]")
(defconst vhdl-ext-font-lock-braces-re "\\(\\[\\|\\]\\)")

(defconst vhdl-ext-common-constructs-re
  (concat
   "^\\s-*\\(\\w+\\)\\s-*:[ \t\n\r\f]*\\(\\("
   "assert\\|block\\|case\\|exit\\|for\\|if\\|loop\\|next\\|null\\|"
   "postponed\\|process\\|"
   "with\\|while"
   "\\)\\>\\|\\w+\\s-*\\(([^\n]*)\\|\\.\\w+\\)*\\s-*<=\\)"))
(defconst vhdl-ext-labels-in-block-and-components-re
  (concat
   "^\\s-*for\\s-+\\(\\w+\\(,\\s-*\\w+\\)*\\)\\>\\s-*"
   "\\(:[ \t\n\r\f]*\\(\\w+\\)\\|[^i \t]\\)"))
(defconst vhdl-ext-brackets-content-range-re "\\(?1:(\\)\\(?2:[ )+*/$0-9a-zA-Z:_-]*\\)\\s-+\\(?3:\\(down\\)?to\\)\\s-+\\(?4:[ (+*/$0-9a-zA-Z:_-]*\\)\\(?5:)\\)")
(defconst vhdl-ext-brackets-content-index-re "\\(?1:(\\)\\s-*\\(?2:[0-9]+\\)\\s-*\\(?3:)\\)")
(defconst vhdl-ext-directive-keywords-re (regexp-opt '("psl" "pragma" "synopsys" "synthesis") 'symbols))
(defconst vhdl-ext-highlight-variable-declaration-names nil)


;;;; Functions
;; INFO: Search based fontification:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Search_002dbased-Fontification.html
;;     Look for 'function' section.
;; - Based on `verilog-match-translate-off'

(defun vhdl-ext-within-translate-off ()
  "Same as analogous `vhdl-mode' function.
Take `vhdl-ext-directive-keywords-re' words into account instead of only 'pragma'."
  (and (save-excursion
         (re-search-backward
          (concat
           "^\\s-*--\\s-*" vhdl-ext-directive-keywords-re "\\s-*translate_\\(on\\|off\\)\\s-*\n") nil t))
       (equal "off" (match-string 1))
       (point)))

(defun vhdl-ext-start-translate-off (limit)
  "Same as analogous `vhdl-mode' function.
Regex search bound to LIMIT.
Take `vhdl-ext-directive-keywords-re' words into account instead of only 'pragma'."
  (when (re-search-forward
         (concat
          "^\\s-*--\\s-*" vhdl-ext-directive-keywords-re "\\s-*translate_off\\s-*\n") limit t)
    (match-beginning 0)))

(defun vhdl-ext-end-translate-off (limit)
  "Same as analogous `vhdl-mode' function.
Regex search bound to LIMIT.
Take `vhdl-ext-directive-keywords-re' words into account instead of only 'pragma'."
  (re-search-forward
   (concat "^\\s-*--\\s-*" vhdl-ext-directive-keywords-re "\\s-*translate_on\\s-*\n") limit t))

(defun vhdl-ext-match-translate-off (limit)
  "Same as analogous `vhdl-mode' function.
Regex search bound to LIMIT.
Take `vhdl-ext-directive-keywords-re' words into account instead of only 'pragma'."
  (when (< (point) limit)
    (let ((start (or (vhdl-ext-within-translate-off)
                     (vhdl-ext-start-translate-off limit)))
          (case-fold-search t))
      (when start
        (let ((end (or (vhdl-ext-end-translate-off limit) limit)))
          (put-text-property start end 'font-lock-multiline t)
          (set-match-data (list start end))
          (goto-char end))))))

(defun vhdl-ext-match-common-constructs-fontify (limit)
  "Search based fontification function for VHDL common constructs.
Needed since it sets match property as `font-lock-multiline'.
Regex search bound to LIMIT."
  (while (re-search-forward vhdl-ext-common-constructs-re limit t)
    (put-text-property (match-beginning 0) (match-end 0) 'font-lock-multiline t)
    (point)))

(defun vhdl-ext-match-labels-in-block-and-components-fontify (limit)
  "Search based fontification function for VHDL labels in blocks and components.
Needed since it sets match property as `font-lock-multiline'.
Regex search bound to LIMIT."
  (while (re-search-forward vhdl-ext-labels-in-block-and-components-re limit t)
    (put-text-property (match-beginning 0) (match-end 0) 'font-lock-multiline t)
    (point)))



;;;; Font-lock keywords
(defvar vhdl-ext-font-lock-keywords-0
  (list
   (list (concat "\\(^\\|[ \t(.']\\)\\(<" vhdl-template-prompt-syntax ">\\)")
         2 'vhdl-font-lock-prompt-face t)
   (list (concat "--\\s-*" vhdl-ext-directive-keywords-re "\\s-+\\(.*\\)$")
         '(0 'vhdl-ext-font-lock-translate-off-face prepend)
         '(1 'vhdl-ext-font-lock-preprocessor-face prepend))
   ;; highlight c-preprocessor directives
   (list "^#[ \t]*\\(\\w+\\)\\([ \t]+\\(\\w+\\)\\)?"
         '(1 font-lock-builtin-face)
         '(3 font-lock-variable-name-face nil t))))

;; highlight keywords and standardized types, attributes, enumeration, values, and subprograms
(defvar vhdl-ext-font-lock-keywords-1
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
(defvar vhdl-ext-font-lock-keywords-2
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
    '(vhdl-ext-match-common-constructs-fontify
      (1 'font-lock-function-name-face))

    ;; highlight label and component name of every instantiation (configuration, component and entity)
    (list
     vhdl-ext-instance-re
     '(1 vhdl-ext-font-lock-instance-face prepend)
     '(5 vhdl-ext-font-lock-instance-lib-face nil t) ; 3rd argument nil avoids font-locking in case there is no match (no entity instantiation)
     '(6 vhdl-ext-font-lock-entity-face prepend))

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
    '(vhdl-ext-match-labels-in-block-and-components-fontify
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
            (goto-char (match-end 1)) (1 vhdl-ext-font-lock-port-connection-face)))

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
    (list vhdl-ext-font-lock-punctuation-re                0 vhdl-ext-font-lock-punctuation-face)
    (list vhdl-ext-font-lock-punctuation-bold-re           0 vhdl-ext-font-lock-punctuation-bold-face)
    (list vhdl-ext-brackets-content-range-re ; Bit range
          '(1 vhdl-ext-font-lock-curly-brackets-face prepend)
          '(5 vhdl-ext-font-lock-curly-brackets-face prepend)
          '(2 vhdl-ext-font-lock-braces-content-face prepend)
          '(4 vhdl-ext-font-lock-braces-content-face prepend)
          '(3 vhdl-ext-font-lock-instance-lib-face   prepend))
    (list vhdl-ext-brackets-content-index-re ; Bit index
          '(1 vhdl-ext-font-lock-curly-brackets-face prepend)
          '(3 vhdl-ext-font-lock-curly-brackets-face prepend)
          '(2 vhdl-ext-font-lock-braces-content-face prepend))
    (list vhdl-ext-font-lock-braces-re                  0 vhdl-ext-font-lock-braces-face)
    (list vhdl-ext-font-lock-brackets-re                0 vhdl-ext-font-lock-brackets-face)
    (list vhdl-ext-font-lock-curly-brackets-re          0 vhdl-ext-font-lock-curly-brackets-face)
    )

   ;; highlight signal/variable/constant declaration names
   (when vhdl-ext-highlight-variable-declaration-names
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
             (goto-char (match-end 1)) (1 vhdl-ext-font-lock-variable-name-face))))
   )
  ;;   "For consideration as a value of `vhdl-font-lock-keywords'.
  ;; This does context sensitive highlighting of names and labels."
  )


;; highlight words with special syntax.
(defvar vhdl-ext-font-lock-keywords-3
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
(defvar vhdl-ext-font-lock-keywords-4
  (list (list vhdl-reserved-words-regexp 1
              'vhdl-font-lock-reserved-words-face)))

;; highlight translate_off regions
(defvar vhdl-ext-font-lock-keywords-5
  '((vhdl-ext-match-translate-off
     (0 vhdl-ext-font-lock-translate-off-face prepend))))

;; highlight everything together
(defvar vhdl-ext-font-lock-keywords
  (append
   vhdl-ext-font-lock-keywords-0
   vhdl-ext-font-lock-keywords-1
   vhdl-ext-font-lock-keywords-4 ; Empty by default
   vhdl-ext-font-lock-keywords-3
   vhdl-ext-font-lock-keywords-2
   vhdl-ext-font-lock-keywords-5
   ))



;;;; Config
(font-lock-add-keywords 'vhdl-mode vhdl-ext-font-lock-keywords 'set)


(provide 'vhdl-font-lock)

;;; vhdl-font-lock.el ends here
