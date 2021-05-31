;;; init-completion.el --- Completion  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Company + Yasnippet + Hydra
;;
;;; Code:

;;;; Company
(defvar larumbe/company-enable t
  "Conditionally determine in a hook if mode is enabled.")


(use-package company
  :diminish
  :commands (larumbe/company-mode)
  :bind ("<S-return>" . company-complete-common)
  :bind (:map company-active-map
         ("C-n" . company-select-next-or-abort)
         ("C-p" . company-select-previous-or-abort)
         ("C-j" . company-complete-selection))
  :config
  (setq company-idle-delay nil) ; Disable auto complete
  (defvar larumbe/company-backends-common '((company-keywords
                                             company-capf
                                             company-gtags)))

  (defun larumbe/company-mode (&optional arg)
    "Enable company-mode depending on value of `larumbe/company-enable'.

Purpose is to use this function as a conditional hook.
ARG will be passed to `company-mode' wrapped function."
    (interactive)
    (if larumbe/company-enable
        (company-mode arg)
      (company-mode -1))))


;;;; Yasnippet
(use-package yasnippet
  :commands (yas-reload-all
             yas-insert-snippet
             yas-visit-snippet-file
             larumbe/yas-melpa-snippets-prevent-load)
  :diminish yasnippet yas-minor-mode
  :bind ("<C-M-return>" . yas-expand)
  :config
  ;; MELPA Snippets database
  (use-package yasnippet-snippets) ; evals and initializes after yasnippet loading

  ;; `yasnippet-snippets' will add the directory of `yasnippet-snippets-dir' to
  ;; the list of available snippets. So we advice the function and do it manually.
  (advice-add 'yasnippet-snippets-initialize :override #'larumbe/yas-melpa-snippets-prevent-load)
  (setq yas-snippet-dirs '(yasnippet-snippets-dir))
  (add-to-list 'yas-snippet-dirs "~/.elisp/snippets") ; Own snippets will have precedence over MELPA ones

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
      (call-interactively #'yas-insert-snippet)))

  (defun larumbe/yas-melpa-snippets-prevent-load ()
    "Prevent automatic loading of MELPA snippets.
Allows a selective loading/overriding of the desired snippets/modes."
    (interactive)
    (message "Avoiding loading of Melpa snippets")))



;;;; Hydra
(use-package hydra
  :config
  (defun larumbe/hydra-yasnippet (snippet)
    "Function/Macro to integrate YASnippet within Hydra."
    (interactive)
    (insert snippet)
    (yas-expand)))



;;;; Hippie-expand
(use-package hippie-expand
  :ensure nil
  :bind ([remap dabbrev-expand] . hippie-expand))




(provide 'init-completion)

;;; init-completion.el ends here
