;;; Present in verilog-ext not in vhdl-ext
;;;; Not very time consuming
;;;; A bit more time consuming
;; TODO: Hierarchy extraction and navigation
;;;; Probably won't do
;; TODO: Find definitions and references
;; TODO: Auto-completion with dot and scope completion

;;  All of these require some type of project/workspace analysis
;;  Could reuse what's already existing in vhdl-mode?

;;;; Not needed
;; Formatter or beautifier


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; INFO: Maybe it's better to implement these in tree-sitter?
;;; Utils
(defun vhdl-ext-point-inside-block-p (block)
  "Return block name if cursor is inside specified BLOCK type."
  (let ((pos (point))
        ;; TODO: Also consider generates
        (re (cond ((eq block 'entity)        "^\\<\\(entity\\)\\>")
                  ((eq block 'architecture)  "^\\<\\(architecture\\)\\>")
                  ((eq block 'function)      "\\<\\(function\\)\\>")
                  ((eq block 'procedure)     "\\<\\(procedure\\)\\>")
                  ((eq block 'component)     "^\\<\\(component\\)\\>")
                  ((eq block 'process)       "^\\<\\(process\\)\\>")
                  ((eq block 'block)         "^\\<\\(block\\)\\>")
                  ((eq block 'package)       "^\\<\\(package\\)\\>")
                  ((eq block 'configuration) "^\\<\\(configuration\\)\\>")
                  ((eq block 'context)       "^\\<\\(context\\)\\>")
                  (t (error "Incorrect block argument"))))
        temp-pos block-beg-point block-end-point block-type block-name)
    (save-match-data
      (save-excursion
        (and (vhdl-re-search-backward re nil t)
             (setq block-type (match-string-no-properties 1))
             (setq temp-pos (point))
             (progn
               (beginning-of-line)
               t)
             (save-excursion
               (vhdl-forward-syntactic-ws (line-end-position))
               (setq block-beg-point (point)))
             ;; TODO: Here I stopped
             (cond ((looking-at vhdl-ext-entity-re)
                    (setq block-name (match-string-no-properties 3))
                    (vhdl-re-search-forward "is" nil t)
                    (goto-char (match-beginning 0))
                    (vhdl-forward-sexp)
                    (backward-word)
                    (setq block-end-point (point)))
                   ((looking-at vhdl-ext-architecture-re)
                    ))
                    )
                   ((or (looking-at vhdl-ext-function-re)
                        (looking-at vhdl-ext-procedure-re))
                    (setq block-name (match-string-no-properties 3)))
                   (t
                    (error "Invalid condition")))
             (goto-char temp-pos)
             (progn
               (vhdl-forward-sexp)
               t)
             (progn
               (backward-word)
               t)
             (setq block-end-point (point)))
        (if (and block-beg-point block-end-point
                 (>= pos block-beg-point)
                 (< pos block-end-point))
            (cons block-type block-name)
          nil)))


;;;; Others
;; TODO: This one shouldn't be needed anymore...
(defun vhdl-ext-electric-return ()
  "Wrapper for RET key to add functionality when there is an AG search buffer.
This will normally happen after calling `vhdl-ext-find-parent-module'"
  (interactive)
  (let* ((ag-buf "*ag search*")
         (ag-win (get-buffer-window ag-buf)))
    (if ag-win
        (delete-window ag-win)
      (vhdl-electric-return))))

;; Keys
;; ("<return>" . larumbe/vhdl-electric-return)
;; ("RET"      . larumbe/vhdl-electric-return)



;;; Lsp
;; vhdl-tool: not-free didn't try
;; ghdl-ls: didn't try, seems it only offers linting, same as GHDL flycheck builtin
;; hdl_checker: only compilation?
;; rust_hdl: A nice one, navigation with defs/refs plus linting and hover


;;; Hierarchy with GHDL
;; Check page 11/11: http://www.dossmatik.de/ghdl/ghdl_unisim_eng.pdf
;; Compile
ghdl -c src/core_fsm/rtl/core_fsm.vhd src/core_fsm/tb/tb_core_fsm.vhd
;; Run without 'running and display tree (similar to vhier)
;; See how to process it and show it with hierarchy
ghdl -r tb_core_fsm --no-run --disp-tree=inst
