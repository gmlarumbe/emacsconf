;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defconst verilog-ext-keywords-re
  (eval-when-compile
    (regexp-opt verilog-keywords 'symbols)))


(defconst verilog-ext-top-re
  (eval-when-compile
    (concat "\\<\\(?1:package\\|program\\|module\\|interface\\)\\>\\(\\s-+\\<automatic\\>\\)?\\s-+\\(?2:\\<" verilog-identifier-re "\\>\\)")))

(defconst verilog-ext-top-instantiable-re
  (eval-when-compile
    (concat "\\<\\(?1:module\\|interface\\)\\>\\(\\s-+\\<automatic\\>\\)?\\s-+\\(?2:\\<" verilog-identifier-re "\\>\\)")))


;;;; Utility
(defun verilog-ext-forward-syntactic-ws ()
  (verilog-forward-syntactic-ws)
  (point))

(defun verilog-ext-backward-syntactic-ws ()
  (verilog-backward-syntactic-ws)
  (point))

(defun verilog-ext-forward-char ()
  (forward-char)
  (point))

(defun verilog-ext-backward-char ()
  (backward-char)
  (point))

(defun verilog-ext-forward-sexp ()
  (ignore-errors
    (forward-sexp)
    (point)))

(defun verilog-ext-backward-sexp ()
  (ignore-errors
    (backward-sexp)
    (point)))

(defun verilog-ext-skip-identifier-backwards ()
  ""
  (< (skip-chars-backward "a-zA-Z0-9_") 0))

(defun verilog-ext-skip-identifier-forward ()
  ""
  (> (skip-chars-forward "a-zA-Z0-9_") 0))

(defmacro when-t (cond &rest body)
  "Same as `when' from subr.el but returning t if COND is nil."
  (declare (indent 1) (debug t))
  (list 'if cond (cons 'progn body) t))




(defun verilog-ext-path-join (arg1 arg2)
  "Join path of ARG1 and ARG2."
  (if (and arg1 arg2)
      (concat (file-name-as-directory arg1) arg2)
    (error "Cannot join path with nil arguments.")
    nil))


(defun verilog-ext-point-inside-block-p (block)
  "Return non-nil if cursor is inside specified BLOCK."
  (let ((pos (point))
        (re (cond ((eq block 'function)  "\\<\\(function\\)\\>")
                  ((eq block 'task)      "\\<\\(task\\)\\>")
                  ((eq block 'class)     "\\<\\(class\\)\\>")
                  ((eq block 'module)    "\\<\\(module\\)\\>")
                  ((eq block 'interface) "\\<\\(interface\\)\\>")
                  ((eq block 'package)   "\\<\\(package\\)\\>")
                  ((eq block 'program)   "\\<\\(program\\)\\>")
                  (t (error "Incorrect block argument"))))
        temp-pos block-beg-point block-end-point)
    (save-match-data
      (save-excursion
        (and (verilog-re-search-backward re nil t)
             (setq temp-pos (point))
             (verilog-re-search-forward ";" nil t)
             (setq block-beg-point (point))
             (goto-char temp-pos)
             (verilog-ext-forward-sexp) ; Make sure there are no errors and return non-nil
             (backward-word)
             (setq block-end-point (point))))
      (if (and block-beg-point block-end-point
               (>= pos block-beg-point)
               (< pos block-end-point))
          t
        nil))))




(provide 'verilog-utils)

;;; verilog-utils.el ends here
