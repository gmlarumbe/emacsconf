;;; term-settings.el --- Terminals  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package term
  :bind (:map term-raw-map
              ("M-o" . other-window)
              ("M-x" . helm-M-x)
              ("M->" . end-of-buffer)
              ("M-<" . beginning-of-buffer))
  :commands (larumbe/ansi-term)
  :config
  (setq comint-process-echoes t)

  (defun larumbe/ansi-term ()
    "Check if there is an existing *ansi-term* buffer and pops to it (if not visible open on the same window).
Otherwise create it"
    (interactive)
    (let ((buf "*ansi-term*"))
      (if (get-buffer buf)
          (if (get-buffer-window buf)
              (pop-to-buffer buf)
            (switch-to-buffer buf))
        (ansi-term "/bin/bash")))))


(provide 'term-settings)

;;; term-settings.el ends here
