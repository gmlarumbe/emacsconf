;;; verilog-timestamp.el --- Timestamp  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Timestamp
(defvar verilog-ext-verilog-time-stamp-profiles '("work" "personal"))
(defvar verilog-ext-verilog-time-stamp-active-profile "work") ; Defaults to work

(defun verilog-ext-verilog-time-stamp-set-profile ()
  "Set active profile for verilog timestamp: work or personal."
  (interactive)
  (let ((profile (completing-read "Set timestamp profile: " verilog-ext-verilog-time-stamp-profiles)))
    (setq verilog-ext-verilog-time-stamp-active-profile profile)))


(defun verilog-ext-verilog-time-stamp-update ()
  "Update `time-stamp' variables depending on current active profile."
  (if (string= verilog-ext-verilog-time-stamp-active-profile "work")
      (verilog-ext-verilog-time-stamp-work-update) ; Work
    (verilog-ext-verilog-time-stamp-pers-update))) ; Personal


;;;;; Work
(defvar verilog-ext-time-stamp-work-boundary-re "\\(?1:[ ]?\\)\\* ------------------------------------------------------------------------------")
(defvar verilog-ext-verilog-time-stamp-work-created-re  "\\(?1:^* \\)\\(?2:[a-z]+\\)\\(?3:[ ]+\\)\\(?4:[^ ]+\\)\\(?5:[ ]+\\)\\(?6:Created\\)")
(defvar verilog-ext-verilog-time-stamp-work-modified-re "\\(?1:^* \\)\\(?2:[a-z]+\\)\\(?3:[ ]+\\)\\(?4:[^ ]+\\)\\(?5:[ ]+\\)\\(?6:Modified\\)")

(defvar verilog-ext-verilog-time-stamp-work-start  (concat "* " user-login-name "  "))
(defvar verilog-ext-verilog-time-stamp-work-format "%Y/%m/%d")
(defvar verilog-ext-verilog-time-stamp-work-end    "   Modified")


(defun verilog-ext-verilog-time-stamp-work-buffer-end-pos ()
  "Return position of point at the end of the buffer timestamp.
Return nil if no timestamp structure was found."
  (save-excursion
    (goto-char (point-min))
    (re-search-forward verilog-ext-verilog-time-stamp-work-boundary-re nil t)
    (re-search-forward verilog-ext-verilog-time-stamp-work-created-re nil t)
    (re-search-forward verilog-ext-verilog-time-stamp-work-boundary-re nil t)))


(defun verilog-ext-time-stamp-work-new-entry ()
  "Create new time-stamp entry at header."
  (interactive)
  (let (initial-blank
        pos)
    (save-excursion
      (setq pos (verilog-ext-verilog-time-stamp-work-buffer-end-pos))
      (if pos
          (progn
            (goto-char pos)
            (verilog-ext-verilog-time-stamp-work-buffer-end-pos)
            (setq initial-blank (match-string-no-properties 1))
            (beginning-of-line)
            (open-line 1)
            (insert (concat initial-blank verilog-ext-verilog-time-stamp-work-start))
            (insert (format-time-string verilog-ext-verilog-time-stamp-work-format))
            (insert verilog-ext-verilog-time-stamp-work-end))
        (message "Could not find proper time-stamp structure!")))))


(defun verilog-ext-verilog-time-stamp-work-update ()
  "Update the 'Modified' entry `time-stamp.'"
  (save-excursion
    (goto-char (point-min))
    (when (verilog-ext-verilog-time-stamp-work-buffer-end-pos) ; Activate time-stamp if structure is present
      (setq-local time-stamp-start  verilog-ext-verilog-time-stamp-work-start)
      (setq-local time-stamp-format verilog-ext-verilog-time-stamp-work-format)
      (setq-local time-stamp-end    verilog-ext-verilog-time-stamp-work-end))))


;;;;; Personal
(defvar verilog-ext-verilog-time-stamp-pers-regex   "^// Last modified : ")
(defvar verilog-ext-verilog-time-stamp-pers-pattern (concat verilog-ext-verilog-time-stamp-pers-regex "%%$"))
(defvar verilog-ext-verilog-time-stamp-pers-format  "%:y/%02m/%02d")


(defun verilog-ext-verilog-time-stamp-pers-update ()
  "Setup `time-stamp' format for Verilog files."
  (setq-local time-stamp-pattern verilog-ext-verilog-time-stamp-pers-pattern)
  (setq-local time-stamp-format  verilog-ext-verilog-time-stamp-pers-format))





(provide 'verilog-timestamp)

;;; verilog-timestamp.el ends here
