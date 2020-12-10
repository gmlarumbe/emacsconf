;;; verilog-navigation.el --- Verilog Navigation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;; Custom navigation functions
(defvar larumbe/newline-or-space-optional "\\(?:[[:blank:]\n]\\)*")
(defvar larumbe/newline-or-space-mandatory "\\(?:[[:blank:]\n]\\)+")
(defvar larumbe/verilog-identifier-re ;; Same as modi's one
      (concat "\\_<\\(?:"
              "\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)" ; simple identifier
              "\\|\\(?:\\\\[!-~]+\\)"           ; escaped identifier
              "\\)\\_>"))
(defvar larumbe/param-port-list "([^;]+?)")
(defvar larumbe/verilog-module-instance-re
      (concat "^[[:blank:]]*"
              "\\(?1:" larumbe/verilog-identifier-re "\\)" ;module name (subgroup 1)
              larumbe/newline-or-space-optional ; For modi its mandatory, but thats a problem since it could be: btd#(
              ;; optional port parameters
              "\\("
              "#" larumbe/newline-or-space-optional larumbe/param-port-list
              "\\([[:blank:]]*//.*?\\)*"  ;followed by optional comments
              "[^;\\./]+?"  ;followed by 'almost anything' before instance name
              "\\)*"
              "\\(?2:" larumbe/verilog-identifier-re "\\)" ;instance name (subgroup 2)
              ;; Added by Larumbe
              "\\s-*\\(\\[.*\\]\\)*"         ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
              larumbe/newline-or-space-optional
              "(" ; And finally .. the opening parenthesis `(' before port list
              ))

(defvar larumbe/verilog-module-instance-full-re ; INFO: Not used for the time being even though it worked for a while... regex too complex
      (concat larumbe/verilog-module-instance-re
              ;; Includes content inside parenthesis of instance. Currently not being used
              larumbe/newline-or-space-optional
              ;; "[^;]+?"  ;followed by 'almost anything' before instance name -> This one requires content between brackets (instances only)
              "[^;]*?"  ;followed by 'almost anything' before instance name -> This one does not require contents necessarily between brackets (instances+interfaces)
              ")"
              larumbe/newline-or-space-optional
              ";"
              ))

(defvar larumbe/verilog-token-re
  (regexp-opt '("module"
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
                ) 'symbols))



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
    (save-excursion
      (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (forward-char))              ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-forward larumbe/verilog-module-instance-re limit t))
        (unless (or (string-match modi/verilog-keywords-re (match-string-no-properties 1))
                    (string-match modi/verilog-keywords-re (match-string-no-properties 2))
                    (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p)
              (setq pos (match-beginning 1))
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
    (save-excursion
      (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (backward-char))             ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-backward larumbe/verilog-module-instance-re limit t))
        (unless (or (string-match modi/verilog-keywords-re (match-string-no-properties 1))
                    (string-match modi/verilog-keywords-re (match-string-no-properties 2))
                    (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p)
              (setq pos (match-beginning 1))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun larumbe/find-verilog-token-fwd ()
  "Search forward for a Verilog token regexp."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (save-excursion
      (forward-char) ; Needed to avoid getting stuck
      (while (and (not found)
                  (re-search-forward larumbe/verilog-token-re nil t))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p)
              (setq pos (match-beginning 1))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun larumbe/find-verilog-token-bwd ()
  "Search backwards for a Verilog token regexp."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (found nil)
        (pos))
    (save-excursion
      (while (and (not found)
                  (re-search-backward larumbe/verilog-token-re nil t))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p)
              (setq pos (match-beginning 1))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(provide 'verilog-navigation)

;;; verilog-navigation.el ends here
