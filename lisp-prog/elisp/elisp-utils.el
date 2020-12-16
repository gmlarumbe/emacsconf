;;; elisp-utils.el --- Elisp Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defun larumbe/byte-compile-current-buffer ()
  "Byte-compile file of current visited buffer."
  (interactive)
  (byte-compile-file buffer-file-name))


(defun larumbe/elisp-flycheck-mode (&optional arg)
  "Flycheck-mode Elisp wrapper function.
Disable function `eldoc-mode' if flycheck is enabled
to avoid minibuffer collisions.
Argument ARG sets `flycheck-mode' non-interactively."
  (interactive)
  ;; Non-interactive
  (if arg
      (progn
        (flycheck-mode arg)
        (eldoc-mode    (* -1 arg)))
    ;; Interactive
    (if eldoc-mode
        (progn
          (eldoc-mode -1)
          (flycheck-mode 1)
          (message "Flycheck enabled"))
      (eldoc-mode 1)
      (flycheck-mode -1)
      (message "Flycheck disabled"))))


(defun my-elisp-hook ()
  "Custom elisp hook."
  (sanityinc/enable-check-parens-on-save)
  (prettify-symbols-mode 1)
  (rainbow-delimiters-mode 1)
  (larumbe/elisp-flycheck-mode 1)
  (set 'ac-sources '(ac-source-gtags ac-source-symbols)))


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


(defun sanityinc/enable-check-parens-on-save ()
  "Run `check-parens' when the current buffer is saved."
  (add-hook 'after-save-hook #'check-parens nil t))


(provide 'elisp-utils)

;;; elisp-utils.el ends here
