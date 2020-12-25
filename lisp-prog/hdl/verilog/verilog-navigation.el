;;; verilog-navigation.el --- Verilog Navigation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'verilog-mode)


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
