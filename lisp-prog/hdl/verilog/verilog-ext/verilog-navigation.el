;;; verilog-navigation.el --- Verilog Navigation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'verilog-mode)
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


(defun verilog-ext-electric-verilog-tab ()
  "Wrapper of the homonym verilog function to avoid indentation issues with compiler directives after setting custom hooks."
  (interactive)
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?` "w" table)
    (with-syntax-table table
      (electric-verilog-tab))))


;;;; Navigation
(defun verilog-ext-find-module-instance (&optional limit fwd)
  "Search for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (let ((instance-re verilog-ext-module-instance-re)
        (case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    ;; (with-verilog-shadow
    (save-excursion
      (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (if fwd
            (forward-char) ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
          (backward-char)))
      (while (and (not found)
                  (if fwd
                      (re-search-forward instance-re limit t)
                    (re-search-backward instance-re limit t)))
        (unless (or (string-match verilog-ext-keywords-re (match-string-no-properties 1))
                    (string-match verilog-ext-keywords-re (match-string-no-properties 2)))
          ;; TODO: Add thing of comments back when not using shadowing?
          ;; TODO: Still fails to find some regexps (can see it with coloring)
          (setq found t)
          (if (called-interactively-p)
              (progn
                (setq pos (match-beginning 1))
                (message (match-string 1)))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


;; TODO: Trying with verilog-regexp-search with a line by line approach
(defun verilog-ext-find-module-instance-2 (&optional limit fwd)
  "Search for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (let ((instance-re '("^\\s-*"))             ; Each element of the list is a line to search
        (case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    ;; TODO Maybe can be done more efficiently with looking-at than with re-search-forward (cdr (bounds-of-thing-at-point 'symbol)) since with
    ;; (verilog-forward-syntactic-ws) comments are already skipped
    (verilog-re-search-forward "^\\s-*\\(\\<[a-zA-Z_][a-zA-Z0-9_]*\\>\\)" nil t) ; Initial blank + module name identifier
    (verilog-forward-syntactic-ws)                                        ; Whitespace/comments
    ;; TODO: Implement the # + parameters option
    ;; (verilog-re-search-forward-try "#" nil t)
    ;; End of TODO
    (verilog-re-search-forward "\\(\\<[a-zA-Z_][a-zA-Z0-9_]*\\>\\)" (cdr (bounds-of-thing-at-point 'symbol)) t) ; Instance name just afterwards
    (verilog-forward-syntactic-ws)
    (verilog-re-search-forward "(" (cdr (bounds-of-thing-at-point 'symbol)) t)
    (verilog-forward-syntactic-ws)
    (verilog-re-search-forward ";" (cdr (bounds-of-thing-at-point 'symbol)) t)
    (verilog-backward-syntactic-ws)
    (verilog-re-search-backward ")" (cdr (bounds-of-thing-at-point 'symbol)) t)

    ;; TODO: Implement optional verilog-array-content
    ;; (verilog-re-search-forward "(" (cdr (bounds-of-thing-at-point 'symbol)) t)
    ;; End of TODO
))

; TODO: Trying with verilog-regexp-search with a line by line approach
(defun verilog-forward-syntactic-ws-t ()
  (verilog-forward-syntactic-ws)
  t)

(defun forward-word-t ()
  (forward-word)
  t)

(defun forward-char-t ()
  (forward-char)
  t)

(defun verilog-ext-find-module-instance-3 (&optional limit fwd)
  "Search for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (let ((case-fold-search verilog-case-fold)
        (start (point))
        found
        module-name
        instance-name)
    (and (verilog-re-search-forward "^\\s-*\\(\\<[a-zA-Z_][a-zA-Z0-9_]*\\>\\)" nil t) ; Initial blank + module name identifier
         (setq module-name (match-string-no-properties 1))
         (verilog-forward-syntactic-ws-t)
         (if (looking-at "#")
             (and (forward-char-t)
                  (verilog-forward-syntactic-ws-t)
                  (looking-at "(")
                  (progn
                    (verilog-forward-sexp)
                    t)
                  (verilog-forward-syntactic-ws-t))
           t)
         (looking-at "\\(\\<[a-zA-Z_][a-zA-Z0-9_]*\\>\\)") ; Instance name just afterwards
         (setq instance-name (match-string-no-properties 1))
         (forward-word)
         (verilog-forward-syntactic-ws-t)
         (looking-at "(")
         (progn
           (verilog-forward-sexp)
           t)
         (verilog-forward-syntactic-ws-t)
         (looking-at ";")
         (setq found t))
    (if found
        (cons module-name instance-name)
      (goto-char start))))


;; TODO: Try to optimize it not to do the forward-line thing
(defun verilog-ext-find-module-instance-fwd-4 (&optional limit)
  "Search for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (start (point))
        (identifier-re "\\(\\<[a-zA-Z_][a-zA-Z0-9_]*\\>\\)")
        found module-name instance-name module-pos
        module-match-data instance-match-data )
    (save-excursion
      (save-match-data
        (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
          (forward-char))  ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
        (while (and (not (eobp))
                    (if limit
                        (> limit (point))
                      t)
                    (not (and (verilog-re-search-forward (concat "\\s-*" identifier-re) limit t) ; Initial blank + module name identifier
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq module-name (match-string-no-properties 1))
                                (setq module-pos (match-beginning 1))
                                ;; (setq module-match-data (match-data :integers)))
                                (setq module-match-data (match-data)))
                              (verilog-forward-syntactic-ws-t)
                              (if (looking-at "#")
                                  (and (forward-char-t)
                                       (verilog-forward-syntactic-ws-t)
                                       (looking-at "(")
                                       (progn
                                         ;; TODO: Do this condition-case or ignore-errors to make sure it works
                                         (verilog-forward-sexp)
                                         t)
                                       (verilog-forward-syntactic-ws-t))
                                t)
                              (looking-at identifier-re) ; Instance name just afterwards
                              (unless (member (match-string-no-properties 1) verilog-keywords)
                                (setq instance-name (match-string-no-properties 1))
                                ;; (setq instance-match-data (match-data :integers)))
                                (setq instance-match-data (match-data)))
                              (forward-word)
                              (verilog-forward-syntactic-ws-t)
                              (if (looking-at "\\[")
                                  (and (progn
                                         (verilog-forward-sexp)
                                         t)
                                       (verilog-forward-syntactic-ws-t))
                                t)
                              (looking-at "(")
                              (progn
                                ;; TODO: Do this condition-case or ignore-errors to make sure it works
                                (verilog-forward-sexp)
                                t)
                              (verilog-forward-syntactic-ws-t)
                              (looking-at ";")
                              (setq found t)
                              (if (called-interactively-p)
                                  (progn
                                    (setq pos module-pos)
                                    (message module-name))
                                (setq pos (point))))))
          ;; (verilog-end-of-statement)        ; INFO: Gave problems in some instances inside generate begin blocks
          (forward-line)                    ; Find something maybe more efficient?
          ))
      )
    (when found
      ;; (set-match-data `(,module-name ,instance-name))
      ;; https://www.gnu.org/software/emacs/manual/html_node/elisp/Entire-Match-Data.html
      (set-match-data (list (nth 0 module-match-data)     ; Beg of whole expression for module-match-data
                            (nth 3 instance-match-data)   ; End of whole expression for instance-match-data
                            (nth 2 module-match-data)     ; (match-beginning 1)
                            (nth 3 module-match-data)     ; (match-end 1)
                            (nth 2 instance-match-data)   ; (match-beginning 2)
                            (nth 3 instance-match-data))) ; (match-end 2)
      ;; (set-match-data (append module-match-data instance-match-data))

      ;; INFO: This one worked with integers
      ;; (set-match-data (list (nth 0 module-match-data)   ; Beg of whole expression for module-match-data
      ;;                       (nth 1 instance-match-data) ; End of whole expression for instance-match-data
      ;;                       (nth 2 module-match-data)   ; (match-beginning 1)
      ;;                       (nth 3 module-match-data)   ; (match-end 1)
      ;;                       (nth 2 instance-match-data) ; (match-beginning 2)
      ;;                       (nth 3 instance-match-data) ; (match-end 2)
      ;;                       (car (last module-match-data))    ; Buffer name
      ;;                       ))
      ;; (remove (car ) module-match-data)
      ;; (remove (car (cdr instance-match-data)) instance-match-data)))
      (goto-char pos))))

    ;; (save-excursion
    ;;   (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
    ;;     (if fwd
    ;;         (forward-char) ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
    ;;       (backward-char)))
    ;;   (while (and (not found)
    ;;               (if fwd
    ;;                   (re-search-forward instance-re limit t)
    ;;                 (re-search-backward instance-re limit t)))
    ;;     (unless (or (string-match verilog-ext-keywords-re (match-string-no-properties 1))
    ;;                 (string-match verilog-ext-keywords-re (match-string-no-properties 2)))
    ;;       ;; TODO: Add thing of comments back when not using shadowing?
    ;;       ;; TODO: Still fails to find some regexps (can see it with coloring)
    ;;       (setq found t)
    ;;       (if (called-interactively-p)
    ;;           (progn
    ;;             (setq pos (match-beginning 1))
    ;;             (message (match-string 1)))
    ;;         (setq pos (point))))))
    ;; (when found
    ;;   (goto-char pos))))
;; End of TODO:


(defun verilog-ext-find-module-instance-fwd (&optional limit)
  "Search forward for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (interactive)
  (verilog-ext-find-module-instance limit t))


(defun verilog-ext-find-module-instance-bwd (&optional limit)
  "Search backwards for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (interactive)
  (verilog-ext-find-module-instance limit nil))



(defun verilog-ext-find-token (&optional fwd)
  "Search forward for a Verilog token regexp."
  (let ((token-re verilog-ext-token-re)
        (case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (save-excursion
      ;; (with-verilog-shadow
      (when fwd
        (forward-char)) ; Needed to avoid getting stuck
      (while (and (not found)
                  (if fwd
                      (re-search-forward token-re nil t)
                    (re-search-backward token-re nil t)))
        ;; TODO: Does not work with shadow, only with font-locked mode and save-excursion
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          ;; TODO: Does not work with shadow, only with font-locked mode and save-excursion
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



(defun verilog-ext-jump-to-module-at-point (&optional ref)
  "Same as `modi/verilog-jump-to-module-at-point' but using ggtags."
  (interactive)
  (let (module)
    (if (and (executable-find "global")
             (projectile-project-root))
        (if (setq module (verilog-ext-point-at-instance-p))
            (progn
              (if ref
                  (xref-find-references module)
                (xref-find-definitions module))
              module) ; Return module name for reporting
          (user-error "Not inside a Verilog instance"))
      (user-error "Couldn't find `global' or `projectile-project-root'."))))



;;;; Modi
;; TODO: Seems that instance is already handled
;; TODO: What modi calls header would be what I call token
;; TODO: Extend token-re to something more complex (like modi's) so that there are capture groups
;; TODO: And it can be easier
;; TODO: Take into account the rest of rx (like the ones used in imenu for task/func/class) etc


;; TODO: Modi headers are more complex than just looking for a word
(defun verilog-ext-get-header (&optional fwd)
  "Function to return the name of the block (module, class, package,
function, task, `define) under which the point is currently present.

If FWD is non-nil, do the block header search in forward direction;
otherwise in backward direction.

This function updates the local variable `verilog-ext-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"top\"
is returned and `verilog-ext-which-func-xtra' is updated to \"mod\" (short
for \"module\").

   module top ();
   ▯
   endmodule "
  (let (block-type block-name return-val) ;return-val will be nil by default
    (setq-local verilog-ext-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward verilog-ext-header-re nil :noerror)
              (re-search-backward verilog-ext-header-re nil :noerror))
        ;; Ensure that text in line or block comments is not incorrectly
        ;; parsed as a Verilog block header
        (when (not (equal (face-at-point) 'font-lock-comment-face))
          ;; (message "---- 1 ---- %s" (match-string 1))
          ;; (message "---- 2 ---- %s" (match-string 2))
          ;; (message "---- 3 ---- %s" (match-string 3))
          ;; (message "---- 4 ---- %s" (match-string 4))
          (setq block-type (match-string 1))
          (setq block-name (match-string 2))

          (when (and (stringp block-name)
                     (not (string-match verilog-ext-keywords-re
                                        block-name)))
            (setq-local verilog-ext-which-func-xtra
                        (cond
                         ((string= "class"     block-type) "class")
                         ((string= "clocking"  block-type) "clk")
                         ((string= "`define"   block-type) "macro")
                         ((string= "group"     block-type) "group")
                         ((string= "module"    block-type) "mod")
                         ((string= "interface" block-type) "if")
                         ((string= "package"   block-type) "pkg")
                         ((string= "sequence"  block-type) "seq")
                         (t (substring block-type 0 4)))) ;First 4 chars
            (setq return-val block-name)))))
    (when (featurep 'which-func)
      ;; (modi/verilog-update-which-func-format)
      )
    return-val))


;; TODO: Modi headers are more complex than just looking for a word
(defun verilog-ext-jump-to-header-dwim (fwd)
  "Jump to a module instantiation header above the current point. If
a module instantiation is not found, jump to a block header if available.

If FWD is non-nil, do that module instrantiation/header search in forward
direction; otherwise in backward direction.

Few examples of what is considered as a block: module, class, package, function,
task, `define."
  (interactive "P")
  (if (verilog-ext-find-module-instance fwd)
      (if fwd
          (re-search-forward verilog-ext-module-instance-re nil :noerror)
        (re-search-backward verilog-ext-module-instance-re nil :noerror))
    (if fwd
        (re-search-forward verilog-ext-header-re nil :noerror)
      (re-search-backward verilog-ext-header-re nil :noerror))))



;; TODO: How to handle `modi/verilog-identifier-pcre'?
(defun verilog-ext-find-parent-module ()
  "Same as `modi/verilog-find-parent-module'.
Additionally add xref push marker to the stack."
  (interactive)
  (let ((verilog-module-re (concat "^[[:blank:]]*" ;Elisp regexp
                                   "\\(?:module\\)[[:blank:]]+" ;Shy group
                                   "\\(?1:"
                                   modi/verilog-identifier-re ;Elisp regexp here!
                                   "\\)\\b"))
        module-name
        module-instance-pcre)
    (save-excursion
      (re-search-backward verilog-module-re)
      (setq module-name (match-string 1))
      (setq module-instance-pcre ;PCRE regex
            (concat "^\\s*"
                    module-name
                    "\\s+"
                    "(#\\s*\\((\\n|.)*?\\))*" ;optional hardware parameters
                                        ;'(\n|.)*?' does non-greedy multi-line grep
                    "(\\n|.)*?" ;optional newline/space before instance name
                    "([^.])*?" ;do not match ".PARAM (PARAM_VAL)," if any
                    "\\K"       ;don't highlight anything till this point
                    modi/verilog-identifier-pcre ;instance name
                    "(?=[^a-zA-Z0-9_]*\\()")) ;optional space/newline after instance name
                                        ;and before opening parenthesis `('
                                        ;don't highlight anything in (?=..)
      (let* ((ag-arguments ag-arguments)) ;Save the global value of `ag-arguments'
        ;; Search only through verilog type files.
        ;; See "ag --list-file-types".
        (add-to-list 'ag-arguments "--verilog" :append)
        (xref-push-marker-stack) ; INFO: Added by Larumbe
        (ag-regexp module-instance-pcre (projectile-project-root))))))




;;;; Auxiliary
;; TODO: Could be rewritten with a macro??
(defun verilog-ext-find-class-bwd ()
  "Meant to be used for Imenu class entry."
  (let (found pos)
    (save-excursion
      (while (and (not found)
                  (verilog-ext-find-token-bwd))
        (when (looking-at verilog-ext-class-re)
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-task-function-class-bwd ()
  "Meant to be used for Imenu class entry."
  (let (found pos)
    (save-excursion
      (while (and (not found)
                  (verilog-ext-find-token-bwd))
        (when (or (looking-at verilog-ext-function-re)
                  (looking-at verilog-ext-task-re)
                  (looking-at verilog-ext-class-re))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-task-function-outside-class-bwd ()
  "Meant to be used for Imenu class entry."
  (let (found pos)
    (save-excursion
      (while (and (not found)
                  (verilog-ext-find-token-bwd))
        (when (and (or (looking-at verilog-ext-function-re)
                       (looking-at verilog-ext-task-re))
                   (not (verilog-ext-point-inside-class-p)))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))



(defun verilog-ext-find-top-bwd ()
  "Return non-nil if cursor is pointing at verilog top module."
  (let (found pos)
    (save-excursion
      (while (and (not found)
                  (verilog-ext-find-token-bwd))
        (when (looking-at verilog-ext-top-re)
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))






(provide 'verilog-navigation)

;;; verilog-navigation.el ends here
