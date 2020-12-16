;;; init-term.el --- Terminals  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package term
  :bind (:map term-raw-map
              ("M-o" . other-window)
              ("M-x" . helm-M-x)
              ("M->" . end-of-buffer)
              ("M-<" . beginning-of-buffer))
  :bind (("C-," . larumbe/ansi-term-dwim)
         ("C-." . larumbe/ansi-term-new))
  :config
  (setq comint-process-echoes t)

  (defun larumbe/ansi-term-dwim ()
    "Check if there is an existing *ansi-term* buffer and pops to it.
If not visible open on the same window. Otherwise create it."
    (interactive)
    (let ((buf "*ansi-term*"))
      (if (get-buffer buf)
          (if (get-buffer-window buf)
              (pop-to-buffer buf)
            (switch-to-buffer buf))
        (ansi-term "/bin/bash"))))

  (defun larumbe/ansi-term-new ()
    "Spawn a new Bash *ansi-term* shell."
    (interactive)
    (ansi-term "/bin/bash")))


(provide 'init-term)

;;; init-term.el ends here
