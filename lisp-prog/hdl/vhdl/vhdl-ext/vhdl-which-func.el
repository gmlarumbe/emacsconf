;;; vhdl-which-func.el --- VHDL which func  -*- lexical-binding: t -*-

;; Copyright (C) 2023 Gonzalo Larumbe

;; Author: Gonzalo Larumbe <gonzalomlarumbe@gmail.com>
;; URL: https://github.com/gmlarumbe/vhdl-ext

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
;; Support and setup for `which-func'.
;;
;;; Code:


(require 'which-func)
(require 'vhdl-navigation)
(require 'vhdl-utils)


(defvar-local vhdl-ext-which-func-extra nil
  "Variable to hold extra information for `which-func'.")


(defun vhdl-ext-which-func-function ()
  "Retrieve `which-func' candidates."
  (let (data)
    (cond ((setq data (vhdl-ext-instance-at-point))
           (setq vhdl-ext-which-func-extra (cdr data))
           (car data))
          ((setq data (vhdl-ext-block-at-point)) ; TODO: `vhdl-ext-block-at-point' not implemented, not worth doing it
           (setq vhdl-ext-which-func-extra (cdr data))
           (vhdl-ext-which-func-shorten-block (car data)))
          (t
           (setq vhdl-ext-which-func-extra nil)
           ""))))

(defun vhdl-ext-which-func ()
  "Hook for `vhdl-mode' to enable `which-func'."
  (setq-local which-func-functions '(vhdl-ext-which-func-function))
  (setq-local which-func-format
              `("["
                (:propertize which-func-current
                 face (which-func :weight bold)
                 mouse-face mode-line-highlight)
                ":"
                (:propertize vhdl-ext-which-func-extra
                 face which-func
                 mouse-face mode-line-highlight)
                "]")))

;;;###autoload
(define-minor-mode vhdl-ext-which-func-mode
  "Enhanced extensions for `which-func' in VHDL."
  :lighter ""
  (if vhdl-ext-which-func-mode
      (progn
        (add-hook 'vhdl-mode-hook #'vhdl-ext-which-func)
        (message "Enabled vhdl-ext-which-func-mode"))
    (remove-hook 'vhdl-mode-hook #'vhdl-ext-which-func)
    (message "Disabled vhdl-ext-which-func-mode")))



(provide 'vhdl-which-func)

;;; vhdl-which-func.el ends here
