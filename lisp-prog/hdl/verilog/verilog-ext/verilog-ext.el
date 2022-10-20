;;; verilog-ext.el --- Verilog Extensions  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/verilog-ext
;; Version: 0.0.0
;; Keywords: Verilog, IDE, Tools
;; Package-Requires: ((emacs "28.1"))

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

(require 'verilog-utils)
(require 'verilog-navigation)
(require 'verilog-which-func)
(require 'verilog-hideshow)
(require 'verilog-beautify)
(require 'verilog-imenu)
(require 'verilog-templates)
(require 'verilog-font-lock)
(require 'verilog-completion)
(require 'verilog-vhier)
(require 'verilog-flycheck)


(provide 'verilog-ext)

;;; verilog-ext.el ends here
