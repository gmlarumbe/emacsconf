;;; verilog-overrides.el --- Syntax table overrides  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(require 'verilog-mode)


;;;; Syntax table override functions
;; https://www.veripool.org/issues/724-Verilog-mode-How-to-make-word-navigation-commands-stop-at-underscores-
(defun larumbe/verilog-forward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores.
Move forward ARG words."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (forward-word arg))))


(defun larumbe/verilog-backward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores.
Move backward ARG words."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-word arg))))


(defun larumbe/electric-verilog-tab ()
  "Wrapper of the homonym verilog function to avoid indentation issues with compiler directives after setting custom hooks."
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
        (progn
          (delete-window ag-win)
          (kill-buffer ag-buf))
      (call-interactively #'electric-verilog-terminate-line))))



;;;; Advising
(defun larumbe/verilog-forward-sexp ()
  "Same as `verilog-forward-sexp' but with additional support for:
- checker/endchecker
- config/endconfig
Also allows for proper working of hideshow within this constructs.
BUG: Fixes a bug when finding generate/covergroups/property etc... "
  (let ((reg)
        (md 2)
        (st (point))
        (nest 'yes))
    (if (not (looking-at "\\<"))
        (forward-word-strictly -1))
    (cond
     ((verilog-skip-forward-comment-or-string)
      (verilog-forward-syntactic-ws))
     ((looking-at verilog-beg-block-re-ordered)
      (cond
       ((match-end 1);
        ;; Search forward for matching end
        (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" ))
       ((match-end 2)
        ;; Search forward for matching endcase
        (setq reg "\\(\\<randcase\\>\\|\\(\\<unique0?\\>\\s-+\\|\\<priority\\>\\s-+\\)?\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" )
        (setq md 3)  ; ender is third item in regexp
        )
       ((match-end 4)
        ;; might be "disable fork" or "wait fork"
        (let
            (here)
          (if (or
               (looking-at verilog-disable-fork-re)
               (and (looking-at "fork")
                    (progn
                      (setq here (point))  ; sometimes a fork is just a fork
                      (forward-word-strictly -1)
                      (looking-at verilog-disable-fork-re))))
              (progn  ; it is a disable fork; ignore it
                (goto-char (match-end 0))
                (forward-word-strictly 1)
                (setq reg nil))
            (progn  ; it is a nice simple fork
              (goto-char here)   ; return from looking for "disable fork"
              ;; Search forward for matching join
              (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" )))))
       ((match-end 6)
        ;; Search forward for matching endclass
        (setq reg "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)" ))

       ((match-end 7)
        ;; Search forward for matching endtable
        (setq reg "\\<endtable\\>" )
        (setq nest 'no))
       ((match-end 8)
        ;; Search forward for matching endspecify
        (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
       ((match-end 9)
        ;; Search forward for matching endfunction
        (setq reg "\\<endfunction\\>" )
        (setq nest 'no))
       ((match-end 10)
        ;; Search forward for matching endfunction
        (setq reg "\\<endfunction\\>" )
        (setq nest 'no))
       ((match-end 11)
        ;; Search forward for matching endtask
        (setq reg "\\<endtask\\>" )
        (setq nest 'no))
       ((match-end 12)
        ;; Search forward for matching endtask
        (setq reg "\\<endtask\\>" )
        (setq nest 'no))
       ;; DANGER: There is a BUG with the index of match-end in subsequent cases:
       ;;   - These expressions must be compared with `verilog-beg-block-re-ordered' at the beginning of this function.
       ;;   - Since match-end 12 is repeated, indexes are shifted and this function will not work properly
       ((match-end 13)
        ;; Search forward for matching endgenerate
        (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
       ((match-end 14)
        ;; Search forward for matching endgroup
        (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)" ))
       ((match-end 15)
        ;; Search forward for matching endproperty
        (setq reg "\\(\\<property\\>\\)\\|\\(\\<endproperty\\>\\)" ))
       ((match-end 16)
        ;; Search forward for matching endsequence
        (setq reg "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<endsequence\\>\\)" )
        (setq md 3)) ; 3 to get to endsequence in the reg above
       ;; End of DANGER
       ((match-end 17)
        ;; Search forward for matching endclocking
        (setq reg "\\(\\<clocking\\>\\)\\|\\(\\<endclocking\\>\\)" )))
      (if (and reg
               (forward-word-strictly 1))
          (catch 'skip
            (if (eq nest 'yes)
                (let ((depth 1)
                      here)
                  (while (verilog-re-search-forward reg nil 'move)
                    (cond
                     ((match-end md) ; a closer in regular expression, so we are climbing out
                      (setq depth (1- depth))
                      (if (= 0 depth) ; we are out!
                          (throw 'skip 1)))
                     ((match-end 1) ; an opener in the r-e, so we are in deeper now
                      (setq here (point)) ; remember where we started
                      (goto-char (match-beginning 1))
                      (cond
                       ((if (or
                             (looking-at verilog-disable-fork-re)
                             (and (looking-at "fork")
                                  (progn
                                    (forward-word-strictly -1)
                                    (looking-at verilog-disable-fork-re))))
                            (progn  ; it is a disable fork; another false alarm
                              (goto-char (match-end 0)))
                          (progn  ; it is a simple fork (or has nothing to do with fork)
                            (goto-char here)
                            (setq depth (1+ depth))))))))))
              (if (verilog-re-search-forward reg nil 'move)
                  (throw 'skip 1))))))
     ;; INFO: Modified code
     ((looking-at (concat
                   "\\(?1:\\<\\(macro\\)?module\\>\\)\\|"
                   "\\(?2:\\<primitive\\>\\)\\|"
                   "\\(?3:\\<class\\>\\)\\|"
                   "\\(?4:\\<program\\>\\)\\|"
                   "\\(?5:\\<interface\\>\\)\\|"
                   "\\(?6:\\<package\\>\\)\\|"
                   "\\(?7:\\<connectmodule\\>\\)\\|"
                   "\\(?8:\\<generate\\>\\)\\|"
                   "\\(?9:\\<checker\\>\\)\\|"
                   "\\(?10:\\<config\\>\\)"
                   ))
      (cond
       ((match-end 1)
        (verilog-re-search-forward "\\<endmodule\\>" nil 'move))
       ((match-end 2)
        (verilog-re-search-forward "\\<endprimitive\\>" nil 'move))
       ((match-end 3)
        (verilog-re-search-forward "\\<endclass\\>" nil 'move))
       ((match-end 4)
        (verilog-re-search-forward "\\<endprogram\\>" nil 'move))
       ((match-end 5)
        (verilog-re-search-forward "\\<endinterface\\>" nil 'move))
       ((match-end 6)
        (verilog-re-search-forward "\\<endpackage\\>" nil 'move))
       ((match-end 7)
        (verilog-re-search-forward "\\<endconnectmodule\\>" nil 'move))
       ((match-end 8)
        (verilog-re-search-forward "\\<endgenerate\\>" nil 'move))
       ((match-end 9)
        (verilog-re-search-forward "\\<endchecker\\>" nil 'move))
       ((match-end 10)
        (verilog-re-search-forward "\\<endconfig\\>" nil 'move))
       ;; End of modified code
       (t
        (goto-char st)
        (if (= (following-char) ?\) )
            (forward-char 1)
          (forward-sexp 1)))))
     (t
      (goto-char st)
      (if (= (following-char) ?\) )
          (forward-char 1)
        (forward-sexp 1))))))



(defun larumbe/verilog-backward-sexp ()
  "Same as `verilog-backward-sexp' but with additional support for:
- checker/endchecker
- config/endconfig
Also allows for proper working of hideshow within this constructs."
  (let ((reg)
        (elsec 1)
        (found nil)
        (st (point)))
    (if (not (looking-at "\\<"))
        (forward-word-strictly -1))
    (cond
     ((verilog-skip-backward-comment-or-string))
     ((looking-at "\\<else\\>")
      (setq reg (concat
                 verilog-end-block-re
                 "\\|\\(\\<else\\>\\)"
                 "\\|\\(\\<if\\>\\)"))
      (while (and (not found)
                  (verilog-re-search-backward reg nil 'move))
        (cond
         ((match-end 1) ; matched verilog-end-block-re
          ;; try to leap back to matching outward block by striding across
          ;; indent level changing tokens then immediately
          ;; previous line governs indentation.
          (verilog-leap-to-head))
         ((match-end 2) ; else, we're in deep
          (setq elsec (1+ elsec)))
         ((match-end 3) ; found it
          (setq elsec (1- elsec))
          (if (= 0 elsec)
              ;; Now previous line describes syntax
              (setq found 't))))))
     ((looking-at verilog-end-block-re)
      (verilog-leap-to-head))
     ;; INFO: Modified code
     ((looking-at (concat
                   "\\(?1:endmodule\\>\\)\\|"
                   "\\(?2:\\<endprimitive\\>\\)\\|"
                   "\\(?3:\\<endclass\\>\\)\\|"
                   "\\(?4:\\<endprogram\\>\\)\\|"
                   "\\(?5:\\<endinterface\\>\\)\\|"
                   "\\(?6:\\<endpackage\\>\\)\\|"
                   "\\(?7:\\<endconnectmodule\\>\\)\\|"
                   "\\(?8:\\<endchecker\\>\\)\\|"
                   "\\(?9:\\<endconfig\\>\\)"
                   ))
      (cond
       ((match-end 1)
        (verilog-re-search-backward "\\<\\(macro\\)?module\\>" nil 'move))
       ((match-end 2)
        (verilog-re-search-backward "\\<primitive\\>" nil 'move))
       ((match-end 3)
        (verilog-re-search-backward "\\<class\\>" nil 'move))
       ((match-end 4)
        (verilog-re-search-backward "\\<program\\>" nil 'move))
       ((match-end 5)
        (verilog-re-search-backward "\\<interface\\>" nil 'move))
       ((match-end 6)
        (verilog-re-search-backward "\\<package\\>" nil 'move))
       ((match-end 7)
        (verilog-re-search-backward "\\<connectmodule\\>" nil 'move))
       ((match-end 8)
        (verilog-re-search-backward "\\<checker\\>" nil 'move))
       ((match-end 9)
        (verilog-re-search-backward "\\<config\\>" nil 'move))
       ;; End of modified code
       (t
        (goto-char st)
        (backward-sexp 1))))
     (t
      (goto-char st)
      (backward-sexp)))))




;;;; Config
(advice-add 'verilog-forward-sexp :override #'larumbe/verilog-forward-sexp)
(advice-add 'verilog-backward-sexp :override #'larumbe/verilog-backward-sexp)


(provide 'verilog-overrides)

;;; verilog-overrides.el ends here
