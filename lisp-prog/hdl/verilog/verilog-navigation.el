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


;; (defmacro with-verilog-shadow (&rest body)
;;   "Ensure command is executed in associated verilog shadow buffer."
;;   (declare (debug t))
;;   `(save-excursion
;;      (unless (get-buffer (larumbe/verilog-shadow-buffer))
;;        (error "Shadow buf does not exist!"))
;;      (let ((orig-pos (point)))
;;        (with-current-buffer (larumbe/verilog-shadow-buffer)
;;          (goto-char orig-pos)
;;          ,@body))))


;; (defmacro with-verilog-shadow (&rest body)
;;   "Ensure command is executed in associated verilog shadow buffer."
;;   (declare (debug t))
;;   `(save-excursion
;;      (let ((buf (get-buffer (larumbe/verilog-shadow-buffer)))
;;            (orig-pos (point))
;;            (orig-buffer (current-buffer)))
;;        (unless buf
;;          (setq buf (get-buffer-create (larumbe/verilog-shadow-buffer)))
;;          (with-current-buffer buf
;;            (insert-buffer-substring-no-properties orig-buffer)
;;            (larumbe/verilog-replace-comments-with-blanks)
;;            (goto-char (point-min))))
;;        (with-current-buffer buf
;;          (goto-char orig-pos)
;;          ,@body))))


;; (with-verilog-shadow
;;  (message"hello"))


(add-hook 'verilog-mode-hook (lambda () (add-hook 'after-save-hook #'larumbe/verilog-shadow-buffer-update nil :local)))
(add-hook 'verilog-mode-hook (lambda () (add-hook 'kill-buffer-hook #'larumbe/verilog-shadow-buffer-kill nil :local)))



(defun larumbe/verilog-shadow-buffer ()
  (concat " #" buffer-file-name "#"))

(defmacro with-verilog-shadow (&rest body)
  "Ensure command is executed in associated verilog shadow buffer."
  (declare (indent 0) (debug t))
  `(save-excursion
     (unless (get-buffer (larumbe/verilog-shadow-buffer))
       (larumbe/verilog-shadow-buffer-create))
     (let ((orig-pos (point)))
       (with-current-buffer (larumbe/verilog-shadow-buffer)
         (goto-char orig-pos)
         ,@body))))

(defun larumbe/verilog-shadow-buffer-create ()
  "Create shadow buffer if it does not already exist."
  (let ((buf (larumbe/verilog-shadow-buffer))
        (orig (current-buffer)))
    (unless (get-buffer buf)
      (get-buffer-create buf))
    (with-current-buffer buf
      (erase-buffer)
      (insert-buffer-substring-no-properties orig)
      (larumbe/verilog-replace-comments-with-blanks)
      (goto-char (point-min)))))


(defun larumbe/verilog-shadow-buffer-update ()
  "Update shadow buffer and fontify."
  (larumbe/verilog-shadow-buffer-create)
  (font-lock-fontify-block))



(defun larumbe/verilog-shadow-buffer-kill ()
  "Kill shadow buffer after killing its buffer to avoid Emacs cluttering."
  (let ((buf (larumbe/verilog-shadow-buffer)))
    (when (get-buffer buf)
      (kill-buffer buf))))


;; INFO: Very promising!!
;; The only missing thing is to insert the buffer and remove blanks when colorizing ONLY
;; once at the beginning.
;; So it's necessary to have a buffer with the blanks in parallel to do the coloring
;; Check `larumbe/find-verilog-module-instance-fontify' and check about the buffer without blanks there.
;; font-lock does it gradually, but with this function is extremely expensive


(defun larumbe/verilog-replace-comments-with-blanks ()
  "Remove comments from current buffer and replace them with blanks.
Main purpose is to have a reformatted buffer without comments that has
the same structure (point) as original buffer."
  (let ((unicode-spc 32)
        posA posB num)
    (save-excursion
      ;; Remove // style comments
      (goto-char (point-min))
      (while (re-search-forward "//" (point-max) :noerror)
        (backward-char 2)
        (setq posA (point))
        (setq posB (point-at-eol))
        (setq num (- posB posA))
        (kill-line)
        (insert-char unicode-spc num))
      ;; Remove /* */ style comments
      (goto-char (point-min))
      (while (re-search-forward "/\\*" (point-max) :noerror)
        (backward-char 2)
        (setq posA (point))
        (re-search-forward "\\*/" (point-max) :noerror)
        (setq posB (point))
        (setq num (- posB posA))
        (kill-backward-chars num)
        (insert-char unicode-spc num)))))



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
    (with-verilog-shadow
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
