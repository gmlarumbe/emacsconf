;;; verilog-navigation.el --- Verilog Navigation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'verilog-mode)
(require 'ggtags)

;; TODO: This is required by some modi functions
(require 'ag) ; Load `ag' package so `ag-arguments' get updated with --stats to jump to first match



;;;; Syntax table override functions
;; https://www.veripool.org/issues/724-Verilog-mode-How-to-make-word-navigation-commands-stop-at-underscores-
(defun verilog-ext-forward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores.
Move forward ARG words."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (forward-word arg))))


(defun verilog-ext-backward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores.
Move backward ARG words."
  (interactive "p")
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-word arg))))



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


;;;; Module related
;; TODO: Try to optimize it not to do the forward-line thing
;; TODO: Right now the `verilog-identifier-sym-re' catches things such as (Rst_n) and .Rst_n
;; It would be nice if it only recognized things that have an space before and after (a real symbol).
;; TODO: Could this be done modifying temporarily the syntax table? But that might be an issue for font-locking?
(defun verilog-ext-find-module-instance-fwd (&optional limit)
  "Search for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (interactive)
  (let ((case-fold-search verilog-case-fold) ; TODO: What about case-fold?
        (identifier-re (concat "\\(" verilog-identifier-sym-re "\\)"))
        (module-end (make-marker))
        found module-name instance-name module-pos
        module-match-data instance-match-data
        pos)
    (save-excursion
      (save-match-data
        (when (called-interactively-p) ; INFO: If applied to verilog-font-locking will break multiline font locking.
          (forward-char))  ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
        (while (and (not (eobp))
                    (when-t limit
                      (> limit (point)))
                    (not (and (verilog-re-search-forward (concat "\\s-*" identifier-re) limit 'move) ; Initial blank + module name identifier
                              (not (verilog-parenthesis-depth)) ; Optimize search by avoiding looking for identifiers in parenthesized expressions
                              (set-marker module-end (point))
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq module-name (match-string-no-properties 1))
                                (setq module-pos (match-beginning 1))
                                (setq module-match-data (match-data)))
                              (verilog-ext-forward-syntactic-ws)
                              (when-t (= (following-char) ?\#)
                                (and (verilog-ext-forward-char)
                                     (verilog-ext-forward-syntactic-ws)
                                     (= (following-char) ?\()
                                     (verilog-ext-forward-sexp)
                                     (= (preceding-char) ?\))
                                     (verilog-ext-forward-syntactic-ws)))
                              (looking-at identifier-re) ; Instance name just afterwards
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq instance-name (match-string-no-properties 1))
                                (setq instance-match-data (match-data)))
                              (verilog-ext-skip-identifier-forward)
                              (verilog-ext-forward-syntactic-ws)
                              (when-t (= (following-char) ?\[)
                                (and (verilog-ext-forward-sexp)
                                     (= (preceding-char) ?\])
                                     (verilog-ext-forward-syntactic-ws)))
                              (= (following-char) ?\()
                              (verilog-ext-forward-sexp)
                              (= (preceding-char) ?\))
                              (verilog-ext-forward-syntactic-ws)
                              (= (following-char) ?\;)
                              (setq found t)
                              (if (called-interactively-p)
                                  (progn
                                    (setq pos module-pos)
                                    (message "%s : %s" module-name instance-name))
                                (setq pos (point))))))
          (if (verilog-parenthesis-depth)
              (verilog-backward-up-list -1)
            (forward-line)))))
    (if found
        (progn
          (set-match-data (list (nth 0 module-match-data)     ; Beg of whole expression for module-match-data
                                module-end
                                ;; (nth 3 instance-match-data)   ; End of whole expression for instance-match-data
                                (nth 2 module-match-data)     ; (match-beginning 1)
                                (nth 3 module-match-data)     ; (match-end 1)
                                (nth 2 instance-match-data)   ; (match-beginning 2)
                                (nth 3 instance-match-data))) ; (match-end 2)
          (goto-char pos)
          (if (called-interactively-p)
              (message "%s : %s" module-name instance-name)
            (point))) ; INFO: Need to return point for fontification
      (when (called-interactively-p)
        (message "Could not find any instance forward")))))


;; TODO: Do something for when point is inside a module, to jump to current module header instead of
;; to previous one. Ideas:
;;   -  Check if in parenthesized expression (should return non-nil): (verilog-parenthesis-depth)
;;   -  Go up until not in a parenthsized expression: (while (verilog-backward-up-list 1) ...)
;;   -  Do same logic as with the rest of `verilog-ext-find-module-instance-bwd' from this point on
;;      - Probably this could be grouped/refactored in another function
;;
;; TODO: Add some check to make sure we are in a module/interface when looking for instances to avoid
;; considering some classes/parameterized objects as instances.
;;
(defun verilog-ext-find-module-instance-bwd (&optional limit)
  "Search backwards for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (interactive)
  (let ((case-fold-search verilog-case-fold) ; TODO: What about case-fold
        (identifier-re (concat "\\(" verilog-identifier-sym-re "\\)"))
        (module-end (make-marker))
        found module-name instance-name module-pos
        module-match-data instance-match-data
        pos)
    (save-excursion
      (save-match-data
        ;; TODO: Check if this was used before (it was but not sure if it's needed anymore)
        ;; (when (called-interactively-p) ; INFO: If applied to verilog-font-locking will break multiline font locking.
        ;;   (backward-char))  ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
        (while (and (not (bobp))
                    (when-t limit
                      (< limit (point)))
                    (not (and (verilog-re-search-backward ";" limit 'move)
                              (not (verilog-parenthesis-depth))
                              (set-marker module-end (point))
                              (verilog-ext-backward-syntactic-ws)
                              (= (preceding-char) ?\))
                              (verilog-ext-backward-sexp)
                              (= (following-char) ?\()
                              (verilog-ext-backward-syntactic-ws)
                              (when-t (= (preceding-char) ?\])
                                (and (verilog-ext-backward-sexp)
                                     (= (following-char) ?\[)
                                     (verilog-ext-backward-syntactic-ws)))
                              (verilog-ext-skip-identifier-backwards)
                              (looking-at identifier-re)
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq instance-name (match-string-no-properties 1))
                                (setq instance-match-data (match-data)))
                              (verilog-ext-backward-syntactic-ws)
                              (when-t (= (preceding-char) ?\))
                                (and (verilog-ext-backward-sexp)
                                     (= (following-char) ?\()
                                     (verilog-ext-backward-syntactic-ws)
                                     (= (preceding-char) ?\#)
                                     (verilog-ext-backward-char)
                                     (verilog-ext-backward-syntactic-ws)))
                              (verilog-ext-skip-identifier-backwards)
                              (looking-at identifier-re)
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq module-name (match-string-no-properties 1))
                                (setq module-pos (match-beginning 1))
                                (setq module-match-data (match-data)))
                              (setq found t)
                              (if (called-interactively-p)
                                  (setq pos module-pos)
                                (setq pos (point))))))
          (if (verilog-parenthesis-depth)
              (verilog-backward-up-list 1)
            (beginning-of-line)))))
    (if found
        (progn
          (set-match-data (list (nth 0 module-match-data)     ; Beg of whole expression for module-match-data
                                module-end
                                ;; (nth 3 instance-match-data)   ; End of whole expression for instance-match-data
                                (nth 2 module-match-data)     ; (match-beginning 1)
                                (nth 3 module-match-data)     ; (match-end 1)
                                (nth 2 instance-match-data)   ; (match-beginning 2)
                                (nth 3 instance-match-data))) ; (match-end 2)
          (goto-char pos)
          (if (called-interactively-p)
              (message "%s : %s" module-name instance-name)
            (point)))
      (when (called-interactively-p)
        (message "Could not find any instance backwards")))))



(defun verilog-ext-instance-at-point ()
  "Return if point is inside a Verilog instance.
Return list with TYPE and NAME."
  (let ((point-cur (point))
        point-instance-begin
        point-instance-end
        instance-type
        instance-name)
    (save-excursion
      (when (and (verilog-re-search-forward ";" nil t)
                 (setq point-instance-end (point))
                 (verilog-ext-forward-char)
                 (verilog-ext-find-module-instance-bwd)) ; INFO: Important! Sets match data for this function
        (setq instance-type (match-string-no-properties 1))
        (setq instance-name (match-string-no-properties 2))
        (setq point-instance-begin (point))
        (if (and (>= point-cur point-instance-begin)
                 (<= point-cur point-instance-end))
            (list instance-type instance-name)
          nil)))))


;; TODO: Requires having ggtags/global/xref configured
(defun verilog-ext-jump-to-module-at-point (&optional ref)
  "Same as `modi/verilog-jump-to-module-at-point' but using ggtags."
  (interactive)
  (let (module)
    (if (and (executable-find "global")
             ggtags-project-root)
             ;; (projectile-project-root))
        (if (setq module (car (verilog-ext-instance-at-point)))
            (progn
              (if ref
                  (xref-find-references module)
                (xref-find-definitions module))
              module) ; TODO: Return module name for reporting?
          (user-error "Not inside a Verilog instance"))
      (user-error "Couldn't find `global' or `ggtags-project-root'"))))


(defun verilog-ext-jump-to-module-at-point-def ()
  "Same as `modi/verilog-jump-to-module-at-point' but using ggtags."
  (interactive)
  (verilog-ext-jump-to-module-at-point))

(defun verilog-ext-jump-to-module-at-point-ref ()
  "Same as `modi/verilog-jump-to-module-at-point' but using ggtags."
  (interactive)
  (verilog-ext-jump-to-module-at-point :ref))



;; TODO: Rename this token thing with something else as this is used inside verilog-mode
;;;; Token/Class-related
(defvar verilog-ext-token-re
  (regexp-opt
   '("module"
     "interface"
     "program"
     "package"
     "class"
     "function"
     "task"
     "initial"
     "always"
     "always_ff"
     "always_comb"
     "generate"
     "property"
     "sequence"
     "`define")
   'symbols))

(defun verilog-ext-find-token (&optional fwd)
  "Search forward for a Verilog token regexp."
  (let ((token-re verilog-ext-token-re)
        (case-fold-search verilog-case-fold) ; TODO: What about case fold
        (found nil)
        (pos))
    (save-excursion
      (when fwd
        (forward-char)) ; Needed to avoid getting stuck
      (while (and (not found)
                  (if fwd
                      (re-search-forward token-re nil t)
                    (re-search-backward token-re nil t)))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p)
              (setq pos (match-beginning 1))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-token-fwd ()
  "Search forward for a Verilog token regexp."
  (interactive)
  (verilog-ext-find-token t))


(defun verilog-ext-find-token-bwd ()
  "Search backwards for a Verilog token regexp."
  (interactive)
  (verilog-ext-find-token nil))





(provide 'verilog-navigation)

;;; verilog-navigation.el ends here
