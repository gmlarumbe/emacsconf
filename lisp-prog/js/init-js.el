;;; init-js.el --- JavaScript init  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; JavaScript
(use-package js
  :straight nil
  :mode (("\\.js\\'" . js-ts-mode))
  :bind (:map js-ts-mode-map
         ("M-." . nil)) ; Unmap `js-find-symbol' to leave space for `larumbe/xref-find-definitions'
  :config
  (require 'js-ts-font-lock)

  ;; "js" is included but doesn't work for some reason with js-ts-mode, TODO: Maybe open a PR/issue?
  (with-eval-after-load 'lspce
    (add-to-list 'lspce-server-programs '("javascript" "typescript-language-server" "--stdio")))

  (defun larumbe/js-tree-sitter-find-def (def)
    "Find definition of a tree-sitter grammar identifier."
    (interactive)
    (let (found)
      (save-excursion
        (goto-char (point-min))
        (if (re-search-forward (concat "\\_<\\(?1:" def "\\)\\_>\\s-*:\\s-*\\$\\s-*=>") nil :noerror)
            (setq found (match-beginning 1))
          (user-error "%s not found" def)))
      (xref-push-marker-stack)
      (goto-char found)
      (pulse-momentary-highlight-region (match-beginning 1) (match-end 1) 'next-error)))

  (defun larumbe/js-hook ()
    "Prevent cursor in `js-mode' (not `js-ts-mode'!!) from moving to the beginning of indentation with C-p/C-n."
    (interactive)
    (setq-local goal-column nil)))


(provide 'init-js)

;;; init-js.el ends here
