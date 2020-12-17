;;; init-completion.el --- Completion  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Auto-complete + Yasnippet + Hydra
;;
;;; Code:

;;;; Auto-complete
(defvar larumbe/auto-complete-enable t
  "Conditionally determine in a hook if mode is enabled.")


(use-package auto-complete
  :diminish
  :commands (larumbe/auto-complete-mode)
  :bind ("<S-return>" . auto-complete)
  :bind (:map ac-completing-map
              ("C-n" . ac-next)
              ("C-p" . ac-previous)
              ("C-j" . ac-complete)
              ("C-g" . ac-stop) ; Prevents aborting YAsnippet if occurs at the same time as autocompleting
              ("RET" . ac-complete))
  :config
  (setq ac-delay 1.3)
  ;; INFO: Auto-complete has 3 mode-maps: https://emacs.stackexchange.com/questions/3958/remove-tab-trigger-from-auto-complete
  (define-key ac-mode-map       (kbd "TAB") nil)
  (define-key ac-completing-map (kbd "TAB") nil)
  (define-key ac-completing-map [tab] nil)

  ;; AC-Sources
  ;; Default sources will be `ac-source-words-in-same-mode-buffers'

  ;; Provides `ac-source-gtags'
  (use-package auto-complete-gtags
    :ensure nil
    :config
    (setq ac-gtags-modes '(c-mode cc-mode c++-mode verilog-mode emacs-lisp-mode vhdl-mode sh-mode python-mode tcl-mode)))

  ;; Provides `ac-source-verilog'
  (use-package auto-complete-verilog
    :ensure nil)

  (defun larumbe/auto-complete-mode (&optional arg)
    "Enable auto-complete-mode depending on value of `larumbe/auto-complete-enable'.

Purpose is to use this function as a conditional hook.
ARG will be passed to `auto-complete-mode' wrapped function."
    (interactive)
    (if larumbe/auto-complete-enable
        (auto-complete-mode arg)
      (auto-complete-mode -1))))



;;;; Yasnippet
(use-package yasnippet
    :commands (yas-expand yas-reload-all larumbe/yas-melpa-snippets-prevent-load)
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
