;;; verilog-shadow.el --- Verilog Shadow Buffers  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


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


(define-minor-mode verilog-shadow-mode
  "Use verilog shadow buffers (without comments) for regexp parsing to detect instances."
  :global nil
  (if verilog-shadow-mode
      (progn
        ;; Enable
        (add-hook 'verilog-mode-hook (lambda () (add-hook 'after-save-hook #'larumbe/verilog-shadow-buffer-update nil :local)))
        (add-hook 'verilog-mode-hook (lambda () (add-hook 'kill-buffer-hook #'larumbe/verilog-shadow-buffer-kill nil :local))))
    ;; Disable
    (remove-hook 'verilog-mode-hook (lambda () (add-hook 'after-save-hook #'larumbe/verilog-shadow-buffer-update nil :local)))
    (remove-hook 'verilog-mode-hook (lambda () (add-hook 'kill-buffer-hook #'larumbe/verilog-shadow-buffer-kill nil :local)))))



(provide 'verilog-shadow)

;;; verilog-shadow.el ends here
