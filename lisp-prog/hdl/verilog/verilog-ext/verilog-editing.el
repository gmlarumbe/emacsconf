;;; verilog-editing.el --- Editing  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Port connect/disconnect/blank cleaning
(defun verilog-ext-toggle-connect-port (force-connect)
  "Toggle connect/disconnect port at current line.

If regexp detects that port is connected then disconnect it
and viceversa.

If called with universal arg, FORCE-CONNECT parameter will force connection
of current port, no matter if it is connected/disconnected"
  (interactive "P")
  (let* ((case-fold-search verilog-case-fold)
         (port-regex "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)")
         (conn-regex "\\(?4:(\\(?5:.*\\))\\)?")
         (line-regex (concat port-regex conn-regex))
         port conn sig
         (start (point)))
    ;; Find '.port (conn)' verilog regexp
    (beginning-of-line)
    (if (re-search-forward line-regex (point-at-eol) t)
        (progn
          (setq port (match-string-no-properties 2))
          (setq conn (match-string-no-properties 5))
          (if (or (string-equal conn "") force-connect) ; If it is disconnected or connection is forced via parameter...
              (progn ; Connect
                (setq sig (read-string (concat "Connect [" port "] to: ") port))
                (replace-match (concat "\\1.\\2\\3\(" sig "\)") t))
            (progn ; Else disconnect
              (replace-match (concat "\\1.\\2\\3\(" nil "\)") t)))
          (goto-char start)
          (forward-line))
      (progn ; No port found
        (goto-char start)
        (message "No port detected at current line")))))


(defun verilog-ext-connect-ports-recursively ()
  "Connect ports of current instance recursively.

Ask for ports to be connected until no port is found at current line."
  (interactive)
  (while (not (equal (verilog-ext-toggle-connect-port t) "No port detected at current line"))
    (verilog-ext-toggle-connect-port t)))


(defun verilog-ext-clean-port-blanks ()
  "Cleans blanks inside port connections of current buffer.

Capture Groups:
- Group 1: Beginning of line blanks
- Group 2: Port name (after dot connection)
- Group 3: Blanks after identifier
- Group 4: Blanks after beginning of port connection '('
- Group 5: Name of connection
- Group 6: Blanks after end of port connection ')'
"
  (interactive)
  (let ((old-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)(\\(?4:[ ]*\\)\\(?5:[^ ]+\\)\\(?6:[ ]*\\))")
        (new-re "\\1.\\2\\3\(\\5\)"))
    ;; TODO: Replace with more generic function
    (larumbe/replace-regexp-whole-buffer old-re new-re)
    (message "Removed blanks from current buffer port connections.")))


(defun verilog-ext-block-end-comments-to-block-names ()
  "Convert valid block-end comments to ': BLOCK_NAME'.

Examples: endmodule // module_name             → endmodule : module_name
          endfunction // some comment          → endfunction // some comment
          endfunction // class_name::func_name → endfunction : func_name
          end // block: block_name             → end : block_name "
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward verilog-ext-block-end-keywords-complete-re nil :noerror)
      ;; Make sure that the matched string after "//" is not a verilog keyword.
      (when (not (string-match-p verilog-ext-keywords-re (match-string 2)))
        (replace-match "\\1 : \\2")))))


(define-minor-mode verilog-ext-block-end-comments-to-block-names-mode
  ""
  :global nil
  (if verilog-ext-block-end-comments-to-block-names-mode
      (progn
        (add-hook 'verilog-mode-hook (lambda () (add-hook 'before-save-hook #'verilog-ext-block-end-comments-to-block-names nil :local)))
        (message "Enabled gtags-update-async-minor-mode [current buffer]"))
    (remove-hook 'verilog-mode-hook (lambda () (add-hook 'before-save-hook #'verilog-ext-block-end-comments-to-block-names nil :local)))
    (message "Disabled gtags-update-async-minor-mode [current buffer]")))


(provide 'verilog-editing)

;;; verilog-editing.el ends here
