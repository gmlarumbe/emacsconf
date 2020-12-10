;;; verilog-overrides.el --- Syntax table overrides  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;; Syntax table override functions
;; Fetched from: https://www.veripool.org/issues/724-Verilog-mode-How-to-make-word-navigation-commands-stop-at-underscores-
(defun larumbe/verilog-forward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores withouth destroying verilog-mode syntax highlighting/indentation."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (forward-word arg))))


(defun larumbe/verilog-backward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores withouth destroying verilog-mode syntax highlighting/indentation."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-word arg))))


;; TODO: Destroys syntax highlighting due to syntax-table modifying with isearch
(defun larumbe/verilog-isearch-forward ()
  "Make verilog Isearch word navigation stop at underscores withouth destroying verilog-mode syntax highlighting/indentation."
  (interactive)
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (isearch-forward))))


(defun larumbe/verilog-isearch-backward ()
  "Make verilog Isearch word navigation stop at underscores withouth destroying verilog-mode syntax highlighting/indentation."
  (interactive)
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (isearch-backward))))
;; End of TODO


(defun larumbe/verilog-isearch-forward-symbol-at-point ()
  "Make verilog symbol Isearch case sensitive."
  (interactive)
  (let ((case-fold-search verilog-case-fold))
    (isearch-forward-symbol-at-point)))


(defun larumbe/electric-verilog-tab ()
  "Wrapper of the homonym verilog function to avoid indentation issues with compiler directives after setting custom hooks.."
  (interactive)
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?` "w" table)
    (with-syntax-table table
      (electric-verilog-tab))))


(defun larumbe/electric-verilog-terminate-line ()
  "Wrapper for RET key to add functionality when there is an AG search buffer.
This will normally happen after calling `modi/verilog-find-parent-module'."
  (interactive)
  (let* ((ag-buf "*ag search*")
         (ag-win (get-buffer-window ag-buf)))
    (if ag-win
        (delete-window ag-win)
      (electric-verilog-terminate-line))))


;; https://emacs.stackexchange.com/questions/8032/configure-indentation-logic-to-ignore-certain-lines/8033#8033
(defun larumbe/verilog-avoid-indenting-outshine-comments (&rest args)
  "Ignore outshine comments for indentation.
Return t if the current line starts with '// *'."
  (interactive)
  (let ((match (looking-at "^[[:blank:]]*// \\*")))
    (when match (delete-horizontal-space))
    match))



(provide 'verilog-overrides)

;;; verilog-overrides.el ends here
