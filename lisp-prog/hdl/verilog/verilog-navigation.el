;;; verilog-navigation.el --- Verilog Navigation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'verilog-mode)
(require 'ag) ; Load `ag' package so `ag-arguments' get updated with --stats to jump to first match


(defun larumbe/verilog-find-semicolon-in-instance-comments ()
  "Find semicolons in instance comments.

Main purpose is to avoid missing instantiation detections with `imenu' and
`larumbe/find-verilog-module-instance-fwd' functions.

Point to problematic regexp in case it is found."
  (let ((case-fold-search verilog-case-fold)
        (problem-re ")[, ]*\\(//\\|/\\*\\).*;") ; DANGER: Does not detect semicolon if newline within /* comment */
        (found))
    (save-excursion
      (goto-char (point-min))
      (when (re-search-forward problem-re nil t)
        (setq found t)))
    (when found
      (goto-char (point-min))
      (re-search-forward problem-re nil t)
      (message "Imenu DANGER!: semicolon in comment instance!!"))))



(defun larumbe/find-verilog-module-instance-fwd (&optional limit)
  "Search forward for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (with-verilog-shadow
      (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (forward-char))              ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-forward larumbe/verilog-module-instance-re limit t))
        (unless (or (string-match modi/verilog-keywords-re (match-string-no-properties 1))
                    (string-match modi/verilog-keywords-re (match-string-no-properties 2)))
          (setq found t)
          (if (called-interactively-p)
              (progn
                (setq pos (match-beginning 1))
                (message (match-string 1)))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun larumbe/find-verilog-module-instance-bwd (&optional limit)
  "Search backwards for a Verilog module/instance regexp.

Since this regexp might collide with other Verilog constructs,
it ignores the ones that contain Verilog keywords and continues until found.

LIMIT argument is included to allow the function to be used to fontify Verilog buffers."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (with-verilog-shadow
      (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (backward-char))             ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-backward larumbe/verilog-module-instance-re limit t))
        (unless (or (string-match modi/verilog-keywords-re (match-string-no-properties 1))
                    (string-match modi/verilog-keywords-re (match-string-no-properties 2)))
          (setq found t)
          (if (called-interactively-p)
              (progn
                (setq pos (match-beginning 1))
                (message (match-string 1)))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun larumbe/find-verilog-token-fwd ()
  "Search forward for a Verilog token regexp."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (with-verilog-shadow
      (forward-char) ; Needed to avoid getting stuck
      (while (and (not found)
                  (re-search-forward larumbe/verilog-token-re nil t))
        (setq found t)
        (if (called-interactively-p)
            (setq pos (match-beginning 1))
          (setq pos (point)))))
    (when found
      (goto-char pos))))


(defun larumbe/find-verilog-token-bwd ()
  "Search backwards for a Verilog token regexp."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (with-verilog-shadow
      (while (and (not found)
                  (re-search-backward larumbe/verilog-token-re nil t))
        (setq found t)
        (if (called-interactively-p)
            (setq pos (match-beginning 1))
          (setq pos (point)))))
    (when found
      (goto-char pos))))



;;;; Modi
(defun modi/verilog-find-module-instance (&optional fwd)
  "Return the module instance name within which the point is currently.

If FWD is non-nil, do the verilog module/instance search in forward direction;
otherwise in backward direction.

This function updates the local variable `modi/verilog-which-func-xtra'.

For example, if the point is as below (indicated by that rectangle), \"u_adder\"
is returned and `modi/verilog-which-func-xtra' is updated to \"adder\".

   adder u_adder
   (
    ▯
    );"
  (let (instance-name return-val)   ;return-val will be nil by default
    (setq-local modi/verilog-which-func-xtra nil) ;Reset
    (save-excursion
      (when (if fwd
                (re-search-forward modi/verilog-module-instance-re nil :noerror)
              (re-search-backward modi/verilog-module-instance-re nil :noerror))
        ;; Ensure that text in line or block comments is not incorrectly
        ;; parsed as a module instance
        (when (not (equal (face-at-point) 'font-lock-comment-face))
          ;; (message "---- 1 ---- %s" (match-string 1))
          ;; (message "---- 2 ---- %s" (match-string 2))
          ;; (message "---- 3 ---- %s" (match-string 3))
          (setq-local modi/verilog-which-func-xtra (match-string 1)) ;module name
          (setq instance-name (match-string 2)) ;Instance name

          (when (and (stringp modi/verilog-which-func-xtra)
                     (string-match modi/verilog-keywords-re
                                   modi/verilog-which-func-xtra))
            (setq-local modi/verilog-which-func-xtra nil))

          (when (and (stringp instance-name)
                     (string-match modi/verilog-keywords-re
                                   instance-name))
            (setq instance-name nil))

          (when (and modi/verilog-which-func-xtra
                     instance-name)
            (setq return-val instance-name)))))
    (when (featurep 'which-func)
      (modi/verilog-update-which-func-format))
    return-val))


(defun modi/verilog-jump-to-header-dwim (fwd)
  "Jump to a module instantiation header above the current point. If
a module instantiation is not found, jump to a block header if available.

If FWD is non-nil, do that module instrantiation/header search in forward
direction; otherwise in backward direction.

Few examples of what is considered as a block: module, class, package, function,
task, `define."
  (interactive "P")
  (if (modi/verilog-find-module-instance fwd)
      (if fwd
          (re-search-forward modi/verilog-module-instance-re nil :noerror)
        (re-search-backward modi/verilog-module-instance-re nil :noerror))
    (if fwd
        (re-search-forward modi/verilog-header-re nil :noerror)
      (re-search-backward modi/verilog-header-re nil :noerror))))


(defun modi/verilog-jump-to-header-dwim-fwd ()
  "Executes `modi/verilog-jump-to-header' with non-nil argument so that
the point jumps to a module instantiation/block header *below* the current
point."
  (interactive)
  (modi/verilog-jump-to-header-dwim :fwd))


(defun modi/verilog-jump-to-module-at-point ()
  "When in a module instance, jump to that module's definition.

Calling this function again after that *without moving the point* will
call `pop-tag-mark' and jump will be made back to the original position.

Usage: While the point is inside a verilog instance, say, \"core u_core\",
calling this command, will make a jump to \"module core\". When you call this
command again *without moving the point*, the jump will be made back to the
earlier position where the point was inside the \"core u_core\" instance.

It is required to have `ctags' executable and `projectile' package installed,
and to have a `ctags' TAGS file pre-generated for this command to work."
  (interactive)
  ;; You need to have ctags installed.
  (if (and (executable-find "ctags")
           (projectile-project-root))
      (let ((tags-file (expand-file-name "TAGS" (projectile-project-root))))
        ;; You need to have the ctags TAGS file pre-generated.
        (if (file-exists-p tags-file)
            ;; `modi/verilog-which-func-xtra' contains the module name in
            ;; whose instance declaration the point is currently.
            (if (and (modi/verilog-find-module-instance)
                     modi/verilog-which-func-xtra)
                (progn
                  (modi/update-etags-table)
                  (find-tag modi/verilog-which-func-xtra))
              ;; Do `pop-tag-mark' if this command is called when the
              ;; point in *not* inside a verilog instance.
              (pop-tag-mark))
          (user-error "Ctags TAGS file `%s' was not found" tags-file)))
    (user-error "Executable `ctags' is required for this command to work")))


(defun modi/verilog-find-parent-module ()
  "Find the places where the current verilog module is instantiated in
the project."
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
      ;; (message module-instance-pcre)
      (let* ((ag-arguments ag-arguments)) ;Save the global value of `ag-arguments'
        ;; Search only through verilog type files.
        ;; See "ag --list-file-types".
        (add-to-list 'ag-arguments "--verilog" :append)
        (ag-regexp module-instance-pcre (projectile-project-root))))))


(defun larumbe/verilog-find-parent-module ()
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



(defun larumbe/verilog-jump-to-module-at-point ()
  "Same as `modi/verilog-jump-to-module-at-point' but using ggtags."
  (interactive)
  (if (and (executable-find "global")
           (projectile-project-root))
      ;; `modi/verilog-which-func-xtra' contains the module name in
      ;; whose instance declaration the point is currently.
      (if (and (modi/verilog-find-module-instance)
               modi/verilog-which-func-xtra)
          (progn
            (ggtags-find-tag-dwim modi/verilog-which-func-xtra))
        ;; Do `pop-tag-mark' if this command is called when the
        ;; point in *not* inside a verilog instance.
        (pop-tag-mark))
    (user-error "Executable `global' is required for this command to work")))


(advice-add 'modi/verilog-find-parent-module      :override #'larumbe/verilog-find-parent-module)
(advice-add 'modi/verilog-jump-to-module-at-point :override #'larumbe/verilog-jump-to-module-at-point)



(provide 'verilog-navigation)

;;; verilog-navigation.el ends here
