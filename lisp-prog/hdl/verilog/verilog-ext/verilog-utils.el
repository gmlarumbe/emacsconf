;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-

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
;; Utility functions called from different features.
;;
;;; Code:


(require 'verilog-mode)


(defconst verilog-ext-keywords-re
  (eval-when-compile
    (regexp-opt verilog-keywords 'symbols)))

(defconst verilog-ext-top-instantiable-re
  (eval-when-compile
    (concat "\\<\\(?1:module\\|interface\\)\\>\\(\\s-+\\<automatic\\>\\)?\\s-+\\(?2:\\<" verilog-identifier-re "\\>\\)")))

(defconst verilog-ext-task-re     "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*task\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?2:[A-Za-z_][A-Za-z0-9_:]+\\)") ; Can't use `verilog-identifier-re' for external declared tasks
(defconst verilog-ext-function-re "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*function\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?:\\w+\\s-+\\)?\\(?:\\(?:un\\)signed\\s-+\\)?\\(?2:[A-Za-z_][A-Za-z0-9_:]+\\)") ; Can't use `verilog-identifier-re' for external declared functions
(defconst verilog-ext-class-re    (concat "\\(?1:\\(?:\\(?:virtual\\)\\s-+\\)?class\\)\\s-+\\(?2:" verilog-identifier-re "\\)"))
(defconst verilog-ext-top-re      (concat "\\<\\(?1:package\\|program\\|module\\|interface\\)\\>\\(\\s-+\\<automatic\\>\\)?\\s-+\\(?2:\\<" verilog-identifier-re "\\>\\)"))


;;;; Utility
(defun verilog-ext-forward-syntactic-ws ()
  "Wrap `verilog-forward-syntactic-ws' and return point."
  (verilog-forward-syntactic-ws)
  (point))

(defun verilog-ext-backward-syntactic-ws ()
  "Wrap `verilog-backward-syntactic-ws' and return point."
  (verilog-backward-syntactic-ws)
  (point))

(defun verilog-ext-forward-char ()
  "Wrap `forward-char' and return point."
  (forward-char)
  (point))

(defun verilog-ext-backward-char ()
  "Wrap `backward-char' and return point."
  (backward-char)
  (point))

(defun verilog-ext-forward-sexp ()
  "Wrap `verilog-forward-sexp', ignore errors and return point."
  (ignore-errors
    (verilog-forward-sexp)
    (point)))

(defun verilog-ext-backward-sexp ()
  "Wrap `verilog-backward-sexp' ignore errors and return point."
  (ignore-errors
    (verilog-backward-sexp)
    (point)))

(defun verilog-ext-skip-identifier-backwards ()
  "Return non-nil if point skipped backwards verilog identifier chars."
  (< (skip-chars-backward "a-zA-Z0-9_") 0))

(defun verilog-ext-skip-identifier-forward ()
  "Return non-nil if point skipped forward verilog identifier chars."
  (> (skip-chars-forward "a-zA-Z0-9_") 0))

(defmacro when-t (cond &rest body)
  "Same function `when' from subr.el but returning t if COND is nil."
  (declare (indent 1) (debug t))
  (list 'if cond (cons 'progn body) t))

(defun verilog-ext-path-join (arg1 arg2)
  "Join path of ARG1 and ARG2."
  (if (and arg1 arg2)
      (concat (file-name-as-directory arg1) arg2)
    (error "Cannot join path with nil arguments")
    nil))

(defun verilog-ext-replace-regexp (regexp to-string start end)
  "Wrapper function for programatic use of `replace-regexp'.
Replace REGEXP with TO-STRING from START to END."
  (let* ((marker (make-marker))
         (endpos (when end (set-marker marker end))))
    (save-excursion
      (goto-char start)
      (while (re-search-forward regexp endpos t)
        (replace-match to-string)))))

(defun verilog-ext-replace-regexp-whole-buffer (regexp to-string)
  "Replace REGEXP with TO-STRING on whole `current-buffer'."
  (verilog-ext-replace-regexp regexp to-string (point-min) nil))

(defun verilog-ext-replace-string (string to-string start end &optional fixedcase)
  "Wrapper function for programatic use of `replace-string'.
Replace STRING with TO-STRING from START to END.

If optional arg FIXEDCASE is non-nil, do not alter the case of
the replacement text (see `replace-match' for more info)."
  (let* ((marker (make-marker))
         (endpos (when end (set-marker marker end))))
    (save-excursion
      (goto-char start)
      (while (search-forward string endpos t)
        (replace-match to-string fixedcase)))))

(defun verilog-ext-read-file-modules (file)
  "Find modules in FILE.
Return list with found modules or nil if not found."
  (let (modules
        (debug nil))
    (with-temp-buffer
      (when debug
        (clone-indirect-buffer-other-window "*debug*" t))
      (insert-file-contents file)
      (verilog-mode) ; Needed to set the syntax table to avoid searching in comments
      (while (verilog-re-search-forward verilog-ext-top-instantiable-re nil t)
        (push (match-string-no-properties 2) modules)))
    (delete-dups modules)))

(defun verilog-ext-select-file-module (file)
  "Select file module from FILE.
If only one module was found return it as a string.
If more than one module was found, select between available ones.
Return nil if no module was found."
  (let ((modules (verilog-ext-read-file-modules file)))
    (if (cdr modules)
        (completing-read "Select module: " modules)
      (car modules))))

(defun verilog-ext-point-inside-block-p (block)
  "Return block name if cursor is inside specified BLOCK type."
  (let ((pos (point))
        (re (cond ((eq block 'function)  "\\<\\(function\\)\\>")
                  ((eq block 'task)      "\\<\\(task\\)\\>")
                  ((eq block 'class)     "\\<\\(class\\)\\>")
                  ((eq block 'module)    "\\<\\(module\\)\\>")
                  ((eq block 'interface) "\\<\\(interface\\)\\>")
                  ((eq block 'package)   "\\<\\(package\\)\\>")
                  ((eq block 'program)   "\\<\\(program\\)\\>")
                  ((eq block 'always)    "\\<\\(always\\(_ff\\|_comb\\|_latch\\)?\\)\\>")
                  ((eq block 'initial)   "\\<\\(initial\\)\\>")
                  ((eq block 'final)     "\\<\\(final\\)\\>")
                  ((eq block 'generate)  "\\<\\(generate\\)\\>")
                  (t (error "Incorrect block argument"))))
        temp-pos block-beg-point block-end-point block-type block-name)
    (save-match-data
      (save-excursion
        (cond ((member block '(function task class module interface package program))
               (and (verilog-re-search-backward re nil t)
                    (setq block-type (match-string-no-properties 1))
                    (or (looking-at verilog-ext-function-re)
                        (looking-at verilog-ext-task-re)
                        (looking-at verilog-ext-class-re)
                        (looking-at verilog-ext-top-re))
                    (setq block-name (match-string-no-properties 2))
                    (setq temp-pos (point))
                    (verilog-re-search-forward ";" nil t)
                    (setq block-beg-point (point))
                    (goto-char temp-pos)
                    (verilog-ext-forward-sexp)
                    (backward-word)
                    (setq block-end-point (point))))
              ((member block '(always initial final))
               (and (verilog-re-search-backward re nil t)
                    (setq block-type (match-string-no-properties 1))
                    (verilog-ext-skip-identifier-forward)
                    (verilog-ext-forward-syntactic-ws)
                    (setq block-beg-point (point))
                    (setq block-name (buffer-substring-no-properties (point) (line-end-position)))
                    (verilog-re-search-forward "begin" nil t)
                    (verilog-ext-forward-sexp)
                    (backward-word)
                    (setq block-end-point (point))))
              ((equal block 'generate)
               (and (verilog-re-search-backward re nil t)
                    (setq block-type (match-string-no-properties 1))
                    (verilog-ext-skip-identifier-forward)
                    (save-excursion
                      (verilog-ext-forward-syntactic-ws)
                      (setq block-name (buffer-substring-no-properties (point) (line-end-position))))
                    (setq block-beg-point (point))
                    (verilog-ext-forward-sexp)
                    (backward-word)
                    (setq block-end-point (point))))
              (t
               (error "Invalid condition")))
        (if (and block-beg-point block-end-point
                 (>= pos block-beg-point)
                 (< pos block-end-point))
            (cons block-type block-name)
          nil)))))

(defun verilog-ext-block-at-point ()
  "Return current block and name at point."
  (or (verilog-ext-point-inside-block-p 'function)
      (verilog-ext-point-inside-block-p 'task)
      (verilog-ext-point-inside-block-p 'class)
      (verilog-ext-point-inside-block-p 'package)
      (verilog-ext-point-inside-block-p 'always)
      (verilog-ext-point-inside-block-p 'initial)
      (verilog-ext-point-inside-block-p 'final)
      (verilog-ext-point-inside-block-p 'generate)
      (verilog-ext-point-inside-block-p 'module)
      (verilog-ext-point-inside-block-p 'interface)
      (verilog-ext-point-inside-block-p 'program)))


(provide 'verilog-utils)

;;; verilog-utils.el ends here
