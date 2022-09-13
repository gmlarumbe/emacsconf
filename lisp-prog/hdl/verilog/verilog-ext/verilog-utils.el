;;; verilog-utils.el --- Verilog Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;; TODO: Add some eval-when-compile?
(defvar verilog-ext-keywords-re (regexp-opt verilog-keywords 'symbols))


(defun verilog-ext-path-join (arg1 arg2)
  "Join path of ARG1 and ARG2.
If more than 2 args are required, use `f-join'"
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
             (verilog-forward-sexp)
             (backward-word)
             (setq block-end-point (point))))
      (if (and block-beg-point block-end-point
               (>= pos block-beg-point)
               (< pos block-end-point))
          t
        nil))))




(provide 'verilog-utils)

;;; verilog-utils.el ends here
