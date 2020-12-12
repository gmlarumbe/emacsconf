;;; elisp-utils.el --- Elisp Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:



(defun larumbe/xref-find-definitions-at-point-dwim ()
  "Find definition of symbol at point.
If pointing a file, visit that file instead."
  (interactive)
  (if (file-exists-p (thing-at-point 'filename))
      (larumbe/find-file-at-point)
    (xref-find-definitions (thing-at-point 'symbol))))


(defun larumbe/xref-find-reference-at-point ()
  "Find reference of symbol at point."
  (interactive)
  (xref-find-references (thing-at-point 'symbol)))


(defun larumbe/byte-compile-current-buffer ()
  "Byte-compile file of current visited buffer."
  (interactive)
  (byte-compile-file buffer-file-name))


(defun larumbe/elisp-flycheck-mode (&optional enable)
  "Flycheck-mode Elisp wrapper function.
Disable `eldoc-mode' if flycheck is enabled to avoid minibuffer collisions.
Argument ENABLE sets `flycheck-mode' non-interactively."
  (interactive)
  ;; Interactive toggling
  (unless enable
    (if eldoc-mode
        (progn
          (eldoc-mode -1)
          (flycheck-mode 1)
          (message "Flycheck enabled"))
      (eldoc-mode 1)
      (flycheck-mode -1)
      (message "Flycheck disabled")))
  ;; Non-interactive
  (when enable
    (if (> enable 0)
        (progn
          (flycheck-mode 1)
          (eldoc-mode -1))
      (flycheck-mode -1)
      (eldoc-mode 1))))


;; Thanks to Steve Purcell
(defun sanityinc/headerise-elisp ()
  "Add minimal header and footer to an elisp buffer in order to placate flycheck."
  (interactive)
  (let* ((fname (if (buffer-file-name)
                    (file-name-nondirectory (buffer-file-name))
                  (error "This buffer is not visiting a file")))
         (pname (file-name-sans-extension fname))
         (desc (read-string "Package description: ")))
    (save-excursion
      (goto-char (point-min))
      (insert ";;; " fname " --- " desc  "  -*- lexical-binding: t -*-\n"
              ";;; Commentary:\n"
              ";;; Code:\n\n")
      (goto-char (point-max))
      (insert "\n\n(provide '" pname ")\n\n")
      (insert ";;; " fname " ends here\n"))))


(provide 'elisp-utils)

;;; elisp-utils.el ends here
