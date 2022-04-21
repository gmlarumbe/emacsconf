;;; verilog-navigation.el --- Verilog Navigation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'verilog-mode)
(require 'ag) ; Load `ag' package so `ag-arguments' get updated with --stats to jump to first match


(defun verilog-ext-find-module-instance-fwd (&optional limit)
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
                  (re-search-forward verilog-ext-module-instance-re limit t))
        (unless (or (string-match verilog-ext-keywords-re (match-string-no-properties 1))
                    (string-match verilog-ext-keywords-re (match-string-no-properties 2)))
          ;; TODO: Add thing of comments back when not using shadowing?
          (setq found t)
          (if (called-interactively-p)
              (progn
                (setq pos (match-beginning 1))
                (message (match-string 1)))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-module-instance-bwd (&optional limit)
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
                  (re-search-backward verilog-ext-module-instance-re limit t))
        (unless (or (string-match verilog-ext-keywords-re (match-string-no-properties 1))
                    (string-match verilog-ext-keywords-re (match-string-no-properties 2)))
          ;; TODO: Add thing of comments back when not using shadowing?
          (setq found t)
          (if (called-interactively-p)
              (progn
                (setq pos (match-beginning 1))
                (message (match-string 1)))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-token-fwd ()
  "Search forward for a Verilog token regexp."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (with-verilog-shadow
      (forward-char) ; Needed to avoid getting stuck
      (while (and (not found)
                  (re-search-forward verilog-ext-verilog-token-re nil t))
        (setq found t)
        (if (called-interactively-p)
            (setq pos (match-beginning 1))
          (setq pos (point)))))
    (when found
      (goto-char pos))))


(defun verilog-ext-find-token-bwd ()
  "Search backwards for a Verilog token regexp."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (with-verilog-shadow
      (while (and (not found)
                  (re-search-backward verilog-ext-verilog-token-re nil t))
        (setq found t)
        (if (called-interactively-p)
            (setq pos (match-beginning 1))
          (setq pos (point)))))
    (when found
      (goto-char pos))))



;;;; Modi
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



(defun verilog-ext-jump-to-module-at-point ()
  "Same as `modi/verilog-jump-to-module-at-point' but using ggtags."
  (interactive)
  (if (and (executable-find "global")
           (projectile-project-root))
      ;; `verilog-ext-which-func-xtra' contains the module name in
      ;; whose instance declaration the point is currently.
      (if (and (verilog-ext-find-module-instance)
               verilog-ext-which-func-xtra)
          (progn
            (ggtags-find-tag-dwim verilog-ext-which-func-xtra))
        ;; Do `pop-tag-mark' if this command is called when the
        ;; point in *not* inside a verilog instance.
        (pop-tag-mark))
    (user-error "Executable `global' is required for this command to work")))




(provide 'verilog-navigation)

;;; verilog-navigation.el ends here
