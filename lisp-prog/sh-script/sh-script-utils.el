;;; sh-script-utils.el --- Shell Script Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun larumbe/sh-send-line-or-region-and-step (buffer)
  "Same as `sh-send-line-or-region-and-step' but for process in BUFFER."
  (interactive)
  (unless (get-buffer buffer)
    (error "Buffer %s does not exist" buffer))
  (let (from to end)
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    (process-send-string (get-buffer-process buffer)
                         (concat (buffer-substring-no-properties from to) "\n"))
    (goto-char end)))


(defun larumbe/sh-send-line-or-region-and-step-ansi ()
  "Send current line or region to *ansi-term* and go to next line."
  (interactive)
  (larumbe/sh-send-line-or-region-and-step "*ansi-term*"))


(defun larumbe/sh-send-line-or-region-and-step-vterm ()
  "Send current line or region to *vterm* go to next line."
  (interactive)
  (larumbe/sh-send-line-or-region-and-step "*vterm*"))


(defun larumbe/sh-man-thing-at-point ()
  "Find man entry for thing-at-point."
  (interactive)
  (Man-getpage-in-background (thing-at-point 'symbol :no-props)))


(defun larumbe/sh-mode-hook ()
  "Custom shell script hook."
  ;; INFO: At some point ?- was set as punctuation "." to handle Bash variable default values.
  ;; However, that conflicted with some symbols separated with hypens, such as Debian/Ubuntu package names.
  (modify-syntax-entry ?+ ".")
  (modify-syntax-entry ?: "."))


(provide 'sh-script-utils)

;;; sh-script-utils.el ends here
