;;; elisp-utils.el --- Elisp Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Own functions
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
        (eldoc-mode (* -1 arg)))
    ;; Interactive
    (if eldoc-mode
        (progn
          (eldoc-mode -1)
          (flycheck-mode 1)
          (message "Flycheck enabled"))
      (eldoc-mode 1)
      (flycheck-mode -1)
      (message "Flycheck disabled"))))


(defun larumbe/newline ()
  "Wrapper for RET key when there is an *xref* search buffer.
This will normally happen after calling `larumbe/prog-mode-definitions' in elisp."
  (interactive)
  (let* ((xref-buf "*xref*")
         (xref-win (get-buffer-window xref-buf)))
    (if xref-win
        (progn
          (delete-window xref-win)
          (kill-buffer xref-buf))
      (newline))))


(defun larumbe/insert-time-stamp-elisp ()
  "Insert time-stamp for Elisp buffers.
Try to add it before Commentary section."
  (interactive)
  (larumbe/insert-time-stamp "^;;; Commentary:"))


(defun larumbe/elisp-hook ()
  "Custom elisp hook."
  (sanityinc/enable-check-parens-on-save)
  (prettify-symbols-mode 1)
  (rainbow-delimiters-mode 1)
  (larumbe/elisp-flycheck-mode 1)
  (set 'ac-sources '(ac-source-gtags ac-source-symbols)))



;;;; Steve Purcell
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





;;;; Packages
;; Many thanks to Kaushal Modi
(use-package command-log-mode
  :commands (hydra-command-log/body)
  :init
  ;; Do not bind `clm/open-command-log-buffer' by default to "C-c o"
  (setq command-log-mode-key-binding-open-log nil)
  :config
  (setq command-log-mode-window-size 60)

  (defhydra hydra-command-log (:color teal
                                      :columns 6)
    "Command Log"
    ("c" command-log-mode "toggle mode")
    ("o" clm/open-command-log-buffer "open log buffer")
    ("l" clm/open-command-log-buffer "open log buffer")
    ("C" clm/command-log-clear "clear log buffer")
    ("t" clm/toggle-command-log-buffer "toggle log buffer")
    ("s" clm/save-command-log "save log")
    ("x" clm/close-command-log-buffer "close log buffer")
    ("q" nil "cancel" :color blue)))



(provide 'elisp-utils)

;;; elisp-utils.el ends here
