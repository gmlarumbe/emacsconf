;;; sh-script-utils.el --- Shell Script Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun larumbe/sh-send-line-or-region-and-step-ansi ()
  "Same as `sh-send-line-or-region-and-step' but for *ansi-term* process"
  (interactive)
  (unless (get-buffer "*ansi-term*")
    (error "Buffer *ansi-term* does not exist"))
  (let (from to end)
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    (comint-send-string (get-buffer-process "*ansi-term*")
                        (concat (buffer-substring-no-properties from to) "\n"))
    (goto-char end)))


(defun sh-switch-to-process-buffer ()
  (interactive)
  (pop-to-buffer (process-buffer (get-process "shell")) t))


(defun my-sh-mode-hook ()
  (set 'ac-sources '(ac-source-gtags ac-source-symbols)))



(provide 'sh-script-utils)

;;; sh-script-utils.el ends here
