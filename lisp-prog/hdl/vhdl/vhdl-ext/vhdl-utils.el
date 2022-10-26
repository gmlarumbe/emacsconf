;;; vhdl-utils.el --- VHDL Utilities  -*- lexical-binding: t -*-

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
;; Utility regexp constants and functions.
;;
;;; Code:


(require 'vhdl-mode)


(defconst vhdl-ext-entity-re "^\\s-*\\(entity\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)")
(defconst vhdl-ext-blank-optional-re "[[:blank:]\n]*")
(defconst vhdl-ext-blank-mandatory-re "[[:blank:]\n]+")
(defconst vhdl-ext-identifier-re "[a-zA-Z_][a-zA-Z0-9_-]*")
(defconst vhdl-ext-instance-re
  (concat "^\\s-*\\(?1:" vhdl-ext-identifier-re "\\)\\s-*:" vhdl-ext-blank-optional-re ; Instance name
          "\\(?2:\\(?3:component\\s-+\\|configuration\\s-+\\|\\(?4:entity\\s-+\\(?5:" vhdl-ext-identifier-re "\\)\.\\)\\)\\)?"
          "\\(?6:" vhdl-ext-identifier-re "\\)" vhdl-ext-blank-optional-re ; Module name
          "\\(--[^\n]*" vhdl-ext-blank-mandatory-re "\\)*\\(generic\\|port\\)\\s-+map\\>"))


(defun vhdl-ext-entity-from-file (file &optional port-copy)
  "Find first entity declaration in FILE.
If optional arg PORT-COPY is non-nil, get generic and port information from an
entity or component declaration via `vhdl-port-copy'."
  (with-temp-buffer
    (insert-file-contents file)
    (when (re-search-forward vhdl-ext-entity-re nil t)
      (when port-copy
        (save-match-data
          (vhdl-port-copy)))
      (match-string-no-properties 2))))


(provide 'vhdl-utils)

;;; vhdl-utils.el ends here
