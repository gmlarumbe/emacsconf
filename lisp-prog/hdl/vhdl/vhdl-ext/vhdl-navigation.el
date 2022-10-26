;;; vhdl-navigation.el --- VHDL Navigation  -*- lexical-binding: t -*-

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
;; Navigation functions:
;;  - Find instances forward/backwards
;;  - Jump to definition/reference of module at point (requires gtags/xref)
;;  - Jump to parent module
;;
;;; Code:


(require 'vhdl-utils)


;; TODO: Rewrite `vhdl-ext-find-module-instance-fwd' and `vhdl-ext-find-module-instance-bwd' to use a similar common reusable function
;; TODO: Rewrite `vhdl-ext-jump-to-module-at-point' to not depend on which-func
;; TODO: Rewrite `vhdl-ext-find-parent-module' so that it resembles that one of verilog-ext

(defun vhdl-ext-find-module-instance-fwd (&optional limit)
  "Search forward for a VHDL entity/instance regexp.
Optional LIMIT argument bounds the search."
  (interactive)
  (let ((found nil)
        (pos))
    (save-excursion
      (when (called-interactively-p 'interactive)
        (forward-char))
      (while (and (not found)
                  (re-search-forward vhdl-ext-instance-re limit t))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p 'interactive)
              (setq pos (match-beginning 6))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun vhdl-ext-find-module-instance-bwd (&optional limit)
  "Search backwards for a VHDL module/instance regexp.
Optional LIMIT argument bounds the search."
  (interactive)
  (let ((found nil)
        (pos))
    (save-excursion
      (when (called-interactively-p 'interactive) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (backward-char))             ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-backward vhdl-ext-instance-re limit t))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p 'interactive)
              (setq pos (match-beginning 6))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


;;;; Jump to modules
;; INFO: By default `which-func' would get Info from Imenu.
;;  - This was far faster for which-func updating than using the custom `vhdl-ext-find-module-instance-bwd' function
;;  and performing analogous to modi's functions.

(defun vhdl-ext-jump-to-module-at-point ()
  "When in a module instance, jump to that module's definition.
Fetched from `modi/verilog-jump-to-module-at-point'"
  (interactive)
  (if (and (executable-find "global")
           (projectile-project-root))
      (let ((module (gethash (get-buffer-window) which-func-table))) ; INFO: modi/verilog analogous uses `which-func-current' but it didn't work well here...
                                        ; Maybe replace with `hdl-ext-which-func-current'?
        (if (save-excursion
              (vhdl-ext-find-module-instance-bwd))
            (ggtags-find-tag-dwim module))
        ;; Do `pop-tag-mark' if this command is called when the
        ;; point in *not* inside a verilog instance.
        (pop-tag-mark))
    (user-error "Executable `global' is required for this command to work")))


(defun vhdl-ext-find-parent-module ()
  "Find the places where the current VHDL module is instantiated in the project.
Fetched from `modi/verilog-find-parent-module'"
  (interactive)
  (let ((module-name)
        (module-instance-pcre)
        (regexp)
        (ag-arguments ag-arguments)) ; Save the global value of `ag-arguments'
    ;; Get entity name
    (save-excursion
      (re-search-backward vhdl-ext-entity-re))
    (setq module-name (match-string-no-properties 2))
    ;; Reformat regexp to PCRE:
    ;; INFO: Regexp fetched from `vhdl-ext-instance-re', replaced "\\s-" with "[ ]", and dismissing \n to allow for easy elisp to pcre conversion
    ;; Otherwise it was getting a real hell since `rxt-elisp-to-pcre' does not seem to support newlines conversion.
    (setq regexp (concat "^[ ]*\\([a-zA-Z_][a-zA-Z0-9_-]*\\)[ ]*:[ ]*"
                         "\\(\\(component[ ]+\\|configuration[ ]+\\|\\(entity[ ]+\\([a-zA-Z_][a-zA-Z0-9_-]*\\).\\)\\)\\)?"
                         "\\(" module-name "\\)[ ]*"))
    (setq module-instance-pcre (rxt-elisp-to-pcre regexp))
    (setq ag-arguments (append ag-arguments '("--vhdl")))
    (xref-push-marker-stack)
    (ag-regexp module-instance-pcre (projectile-project-root))))



(provide 'vhdl-navigation)

;;; vhdl-navigation.el ends here
