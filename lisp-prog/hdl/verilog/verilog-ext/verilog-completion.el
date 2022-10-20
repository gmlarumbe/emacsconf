;;; verilog-completion.el --- Verilog Completion   -*- lexical-binding: t -*-

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
;;; Code:

(require 'verilog-mode)
(require 'company-keywords)
(require 'yasnippet)
(require 'verilog-templates)


;;;; Company keywords for Verilog
(add-to-list 'company-keywords-alist (append '(verilog-mode) verilog-keywords))


;;;; Yasnippet
(defvar verilog-ext-snippets-dir nil
  "Snippets directory: ./verilog-snippets/verilog-mode")

(defun verilog-ext-insert-yasnippet (snippet)
  "Insert SNIPPET programatically."
  (insert snippet)
  (yas-expand))

(defun verilog-ext-add-snippets ()
  "Add snippets and reload Yasnippet to make them available."
  (add-to-list 'yas-snippet-dirs verilog-ext-snippets-dir)
  (yas-reload-all))


;;;; Hydra
(defhydra verilog-ext-hydra (:color blue
                             :hint nil)
  ("aa"  (verilog-ext-insert-yasnippet "aa")      "always" :column "A-C")
  ("ac"  (verilog-ext-insert-yasnippet "ac")      "always_comb")
  ("af"  (verilog-ext-insert-yasnippet "af")      "always_ff")
  ("ai"  (verilog-ext-insert-yasnippet "ai")      "assert immediate")
  ("ap"  (verilog-ext-insert-yasnippet "ap")      "assert property")
  ("as"  (verilog-ext-insert-yasnippet "as")      "assign")
  ("beg" (verilog-ext-insert-yasnippet "beg")     "begin/end")
  ("cc"  (verilog-ext-templ-case)                 "case")
  ("cls" (verilog-ext-insert-yasnippet "cls")     "class")
  ("cb"  (verilog-ext-insert-yasnippet "cb")      "clocking block")
  ("ct"  (verilog-ext-insert-yasnippet "ct")      "constraint")
  ("cg"  (verilog-ext-insert-yasnippet "cg")      "covergroup")
  ("d"   (verilog-ext-insert-yasnippet "d")       "display" :column "D-F")
  ("ei"  (verilog-ext-insert-yasnippet "ei")      "else if")
  ("el"  (verilog-ext-insert-yasnippet "el")      "else")
  ("en"  (verilog-ext-templ-enum-typedef nil)     "enum")
  ("fl"  (verilog-ext-insert-yasnippet "fl")      "final")
  ("for" (verilog-ext-insert-yasnippet "for")     "for")
  ("fv"  (verilog-ext-insert-yasnippet "fv")      "forever")
  ("fe"  (verilog-ext-insert-yasnippet "fe")      "foreach")
  ("fj"  (verilog-ext-insert-yasnippet "fj")      "fork join")
  ("fa"  (verilog-ext-insert-yasnippet "fa")      "fork join_any")
  ("fn"  (verilog-ext-insert-yasnippet "fn")      "fork join_none")
  ("ff"  (verilog-ext-insert-yasnippet "ff")      "function")
  ("gen" (verilog-ext-insert-yasnippet "gen")     "generate" :column "G-M")
  ("if"  (verilog-ext-insert-yasnippet "if")      "if")
  ("in"  (verilog-ext-insert-yasnippet "in")      "initial")
  ("itf" (verilog-ext-insert-yasnippet "itf")     "interface")
  ("ll"  (verilog-ext-insert-yasnippet "ll")      "logic")
  ("lv"  (verilog-ext-insert-yasnippet "lv")      "logic vector")
  ("lp"  (verilog-ext-insert-yasnippet "lp")      "localparam")
  ("ms"  (verilog-ext-insert-yasnippet "ms")      "module (simple)")
  ("md"  (verilog-ext-insert-yasnippet "md")      "module (params)")
  ("mp"  (verilog-ext-insert-yasnippet "mp")      "modport")
  ("pkg" (verilog-ext-insert-yasnippet "pkg")     "package" :column "P-S")
  ("pgm" (verilog-ext-insert-yasnippet "pgm")     "program")
  ("pm"  (verilog-ext-insert-yasnippet "pm")      "parameter")
  ("pr"  (verilog-ext-insert-yasnippet "pr")      "property")
  ("rp"  (verilog-ext-insert-yasnippet "rp")      "repeat")
  ("seq" (verilog-ext-insert-yasnippet "seq")     "sequence")
  ("st"  (verilog-ext-templ-struct-typedef nil)   "struct")
  ("ta"  (verilog-ext-insert-yasnippet "ta")      "task (one-line)" :column "T-W")
  ("tk"  (verilog-ext-templ-task)                 "task (port prompt)")
  ("td"  (verilog-ext-insert-yasnippet "td")      "typedef generic")
  ("te"  (verilog-ext-templ-enum-typedef t)       "typedef enum")
  ("ts"  (verilog-ext-templ-struct-typedef t)     "typedef struct")
  ("tu"  (verilog-ext-templ-struct-typedef t t)   "typedef union")
  ("un"  (verilog-ext-templ-struct-typedef nil t) "union")
  ("wh"  (verilog-ext-insert-yasnippet "wh")      "while")
  ("wd"  (verilog-ext-insert-yasnippet "wd")      "while-do")

  ("@"   (verilog-ext-insert-yasnippet "@") "Clk posedge" :column "Others")
  ("D"   (verilog-ext-templ-def-logic) "Define signal")
  ("FS"  (verilog-ext-templ-fsm)   "FSM Sync")
  ("FA"  (verilog-ext-templ-fsm t) "FSM Async")
  ("IS"  (call-interactively #'verilog-ext-templ-inst-auto-from-file-simple) "Instance (simple)")
  ("IP"  (call-interactively #'verilog-ext-templ-inst-auto-from-file-params) "Instance (params)")
  ("TS"  (call-interactively #'verilog-ext-templ-testbench-simple-from-file) "TB from DUT (simple)")

  ("uc"  (verilog-ext-insert-yasnippet "uc") "UVM Component" :column "UVM")
  ("uo"  (verilog-ext-insert-yasnippet "uo") "UVM Object")
  ("ut"  (verilog-ext-insert-yasnippet "ut") "UVM TypeId Create")
  ("ui"  (verilog-ext-insert-yasnippet "ui") "UVM Info")
  ("ue"  (verilog-ext-insert-yasnippet "ue") "UVM Error")
  ("uw"  (verilog-ext-insert-yasnippet "uw") "UVM Warning")
  ("ur"  (verilog-ext-insert-yasnippet "ur") "UVM Report")

  ("/*"  (verilog-ext-insert-yasnippet "/*")             "Star comment" :column "Comments")
  ("B"   (verilog-ext-templ-block-comment)               "Block comment")
  ("hd"  (call-interactively #'verilog-ext-templ-header) "Header")

  ;;;;;;;;;;
  ;; Exit ;;
  ;;;;;;;;;;
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))



(provide 'verilog-completion)

;;; verilog-completion.el ends here

;; Local Variables:
;; byte-compile-warnings: (not docstrings)
;; End:
