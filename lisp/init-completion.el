;;; init-completion.el --- Completion  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Company + Yasnippet + Hydra
;;
;;; Code:

;;;; Company
(use-package company
  :diminish
  :bind ("<S-return>" . company-complete-common)
  :bind (:map company-active-map
         ("C-n" . company-select-next-or-abort)
         ("C-p" . company-select-previous-or-abort)
         ("C-j" . company-complete-selection))
  :config
  (setq company-idle-delay nil) ; Disable auto complete
  (defvar larumbe/company-backends-common '((company-keywords
                                             company-capf
                                             company-gtags))))


;;;; Yasnippet
(use-package yasnippet
  :commands (yas-reload-all
             yas-insert-snippet
             yas-visit-snippet-file
             larumbe/yas-insert-snippet-dwim)
  :diminish yasnippet yas-minor-mode
  :bind ("<C-M-return>" . yas-expand)
  :config
  ;; MELPA Snippets database
  (use-package yasnippet-snippets
    :straight (:repo "AndreaCrotti/yasnippet-snippets"
               :fork (:repo "gmlarumbe/yasnippet-snippets"))
    :config
    ;; Snippets directories are set in `yas-snippet-dirs' variable.
    ;; `yasnippet-snippets' will add the directory of `yasnippet-snippets-dir' to
    ;; the list of available snippets. So we reset it's value to look only in one directory.
    (setq yas-snippet-dirs '(yasnippet-snippets-dir)))

  ;; Unmap TAB, use it for indentation only
  (define-key yas-minor-mode-map (kbd "TAB") nil)
  (define-key yas-minor-mode-map [tab] nil)
  ;; Load snippets
  (yas-reload-all)

  (defun larumbe/yas-insert-snippet-dwim (&optional arg)
    "Insert yasnippet snippet.
If universal ARG is provided, visit a snippet file."
    (interactive "P")
    (if arg
        (call-interactively #'yas-visit-snippet-file)
      (call-interactively #'yas-insert-snippet))))


;;;; Hydra
(use-package hydra
  :commands (larumbe/hydra-yasnippet)
  :config
  (defun larumbe/hydra-yasnippet (snippet)
    "Function/Macro to integrate YASnippet within Hydra."
    (interactive)
    (insert snippet)
    (yas-expand)))



;;;; Hippie-expand
(use-package hippie-expand
  :straight nil
  :bind ([remap dabbrev-expand] . hippie-expand))




(provide 'init-completion)

;;; init-completion.el ends here
