;;; vhdl-ext.el --- VHDL Extensions for Emacs  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/vhdl-ext
;; Version: 0.0.0
;; Keywords: VHDL, IDE, Tools
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

;; Extensions for VHDL Mode

;;; Code:

(require 'vhdl-utils)
(require 'vhdl-templates)
(require 'vhdl-navigation)
(require 'vhdl-imenu)
(require 'vhdl-flycheck)
(require 'vhdl-font-lock)


(provide 'vhdl-ext)

;;; vhdl-ext.el ends here
