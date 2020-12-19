;;; init-hdl-font-lock.el --- HDL Font-locking (VHDL/SystemVerilog)  -*- lexical-binding: t -*-
;;; Commentary:
;; INFO: Multiline Font Locking has reliability limitations in Emacs.
;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Multiline-Font-Lock.html
;;  - https://www.gnu.org/software/emacs/manual/html_node/elisp/Font-Lock-Multiline.html
;;
;;  - One way to ensure reliable rehighlighting of multiline font-lock constructs is by using the `font-lock-multiline' text property.
;;  - The `font-lock-multiline' variable might seem to be working but is not reliable.
;;  - Using the `font-lock-multiline' property might apply to a few lines (such is the case).
;;    For longer sections it is necessary to create font lock custom functions and gets more complicated.
;;
;;; Code:


;;;; Faces
(defvar larumbe/font-lock-punctuation-face 'larumbe/font-lock-punctuation-face)
(defface larumbe/font-lock-punctuation-face
  '((t (:foreground "burlywood")))
  "Face for punctuation symbols: !,;:?'=<>* "
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-punctuation-bold-face 'larumbe/font-lock-punctuation-bold-face)
(defface larumbe/font-lock-punctuation-bold-face
  '((t (:inherit larumbe/font-lock-punctuation-face :weight extra-bold)))
  "Face for bold punctuation symbols, such as &^~+-/|. "
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-port-connection-face 'larumbe/font-lock-port-connection-face)
(defface larumbe/font-lock-port-connection-face
  '((t (:foreground "bisque2")))
  "Face for instances port connections
...
.portA (signalA),
.portB (signalB)
);
 "
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-dot-expression-face 'larumbe/font-lock-dot-expression-face)
(defface larumbe/font-lock-dot-expression-face
  '((t (:foreground "gray70")))
  "Face for interfaces prefix (also applies to objects methods calling)
...
axi_if.Ready <= 1'b1;
obj.method();
"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-braces-content-face 'larumbe/font-lock-braces-content-face)
(defface larumbe/font-lock-braces-content-face
  '((t (:foreground "yellow green")))
  "Face for content between braces: bit vector width and indexing "
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-braces-face 'larumbe/font-lock-braces-face)
(defface larumbe/font-lock-braces-face
  '((t (:foreground "goldenrod")))
  "Face for braces []"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-brackets-face 'larumbe/font-lock-brackets-face)
(defface larumbe/font-lock-brackets-face
  '((t (:foreground "dark goldenrod")))
  "Face for brackets ()"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-curly-brackets-face 'larumbe/font-lock-curly-brackets-face)
(defface larumbe/font-lock-curly-brackets-face
  '((t (:foreground "DarkGoldenrod2")))
  "Face for curly brackets {}"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-width-num-face 'larumbe/font-lock-width-num-face)
(defface larumbe/font-lock-width-num-face
  '((t (:foreground "chartreuse2")))
  "Face for the bit width number expressions:
{1}'b1,
{4}'hF,
{3}'o7,
"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-width-type-face 'larumbe/font-lock-width-type-face)
(defface larumbe/font-lock-width-type-face
  '((t (:foreground "sea green" :weight bold)))
  "Face for the bit width type expressions:
1'{b}1,
4'{h}F,
3'{o}7,
"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-module-face 'larumbe/font-lock-module-face)
(defface larumbe/font-lock-module-face
  '((t (:foreground "green1")))
  "Face for module names."
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-instance-face 'larumbe/font-lock-instance-face)
(defface larumbe/font-lock-instance-face
  '((t (:foreground "medium spring green")))
  "Face for instance names."
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-time-event-face 'larumbe/font-lock-time-event-face)
(defface larumbe/font-lock-time-event-face
  '((t (:foreground "deep sky blue" :weight bold)))
  "Face for time-events: @ and #"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-time-unit-face 'larumbe/font-lock-time-unit-face)
(defface larumbe/font-lock-time-unit-face
  '((t (:foreground "light steel blue")))
  "Face for time-units: ms, us, ns, ps, fs (used by delays and timescale/timeprecision)"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-preprocessor-face 'larumbe/font-lock-preprocessor-face)
(defface larumbe/font-lock-preprocessor-face
  '((t (:foreground "pale goldenrod")))
  "Face for preprocessor compiler directives (`include, `define...)"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-variable-type-face 'larumbe/font-lock-variable-type-face)
(defface larumbe/font-lock-variable-type-face
  '((t (:foreground "powder blue")))
  "Face for variables types (i.e. Verilog typedef types, defined `larumbe/verilog-variable-re-1', `larumbe/verilog-variable-re-2' and `larumbe/verilog-variable-re-3'"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-variable-name-face 'larumbe/font-lock-variable-name-face)
(defface larumbe/font-lock-variable-name-face
  '((t (:foreground "DarkSeaGreen1")))
  "Face for variables names (i.e. Verilog typedef names, defined `larumbe/verilog-variable-re-1', `larumbe/verilog-variable-re-2' and `larumbe/verilog-variable-re-3'"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/xilinx-attributes-face 'larumbe/xilinx-attributes-face)
(defface larumbe/xilinx-attributes-face
  '((t (:foreground "orange1")))
  "Face for Xilinx Vivado RTL synthesis attributes."
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-grouping-keywords-face 'larumbe/font-lock-grouping-keywords-face)
(defface larumbe/font-lock-grouping-keywords-face
  '((t (:foreground "dark olive green")))
  "Face for overriding grouping keywords (begin/end)"
  :group 'hdl-font-lock-highlighting-faces)


(defvar larumbe/font-lock-translate-off-face 'larumbe/font-lock-translate-off-face)
(defface larumbe/font-lock-translate-off-face
  '((t (:background "gray20" :slant italic)))
  "Face for pragmas between comments: * translate_off / * translate_on"
  :group 'hdl-font-lock-highlighting-faces)


;;;; Common regexps
(defvar larumbe/brackets-regex "[()]")
(defvar larumbe/curly-brackets-regex "[{}]")
(defvar larumbe/braces-regex "\\(\\[\\|\\]\\)")
(defvar larumbe/punctuation-regex "\\([!,;:?'=<>]\\|\\*\\)")
(defvar larumbe/punctuation-bold-regex "\\([&^~+-]\\||\\|\\.\\|\\/\\)")


(provide 'init-hdl-font-lock)

;;; init-hdl-font-lock.el ends here
