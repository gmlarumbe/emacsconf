;;; vhdl-imenu.el --- VHDL Imenu  -*- lexical-binding: t -*-

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
;; VHDL Imenu
;;
;;; Code:


(require 'vhdl-mode)
(require 'vhdl-utils)


(defconst vhdl-ext-imenu-generic-expression
  `(("Subprogram"    "^\\s-*\\(\\(\\(impure\\|pure\\)\\s-+\\|\\)function\\|procedure\\)\\s-+\\(\"?\\(\\w\\|\\s_\\)+\"?\\)" 4)
    ("Instances"     vhdl-ext-find-module-instance-bwd 6)
    ("Component"     "^\\s-*\\(component\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)" 2)
    ("Procedural"    "^\\s-*\\(\\(\\w\\|\\s_\\)+\\)\\s-*:\\(\\s-\\|\n\\)*\\(procedural\\)" 1)
    ("Process"       "^\\s-*\\(\\(\\w\\|\\s_\\)+\\)\\s-*:\\(\\s-\\|\n\\)*\\(\\(postponed\\s-+\\|\\)process\\)" 1)
    ("Block"         "^\\s-*\\(\\(\\w\\|\\s_\\)+\\)\\s-*:\\(\\s-\\|\n\\)*\\(block\\)" 1)
    ("Package"       "^\\s-*\\(package\\( body\\|\\)\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)" 3)
    ("Configuration" "^\\s-*\\(configuration\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\s-+of\\s-+\\(\\w\\|\\s_\\)+\\)" 2)
    ("Architecture"  "^\\s-*\\(architecture\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\s-+of\\s-+\\(\\w\\|\\s_\\)+\\)" 2)
    ("Entity"        ,vhdl-ext-entity-re 2)
    ("Context"       "^\\s-*\\(context\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)" 2))
  "Imenu generic expression for VHDL Mode.  See `imenu-generic-expression'.")


(defun vhdl-ext-index-menu-init ()
  "Initialize index menu."
  (setq-local imenu-case-fold-search t)
  (setq-local imenu-generic-expression vhdl-ext-imenu-generic-expression)
  (when (and vhdl-index-menu
             (fboundp 'imenu))
    (imenu-add-to-menubar "Index")))


(advice-add 'vhdl-index-menu-init :override #'vhdl-ext-index-menu-init)


(provide 'vhdl-imenu)

;;; vhdl-imenu.el ends here
