;;; init-completion.el --- Completion  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Company + Yasnippet + Hydra + Hippie Expand
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; INFO: Main differences between CAPF and Company:
;;  - CAPF uses `completion-at-point-functions', which are defined by
;;  specific major-modes (such as `ggtags-mode', `verilog-mode' or `emacs-lisp-mode').
;;  - Company uses the variable `company-backends', which can in turn include
;;  the CAPF backend, plus company-gtags backend and company-keywords backend (only for some specific languages).
;; - CAPF uses only one backend/capf function at a time, while company can group various backends at once:
;;   i.e: it is possible to get both completion values with both major-mode capf and gtags with company but not with capf.
;;
;; However, it could be a bit confusing because for example for Elisp, the CAPF uses the function
;; `elisp-completion-at-point', which somehow uses company but filters according to context
;; (depending if function or variable).
;; In turn, company can use the CAPF backend for completion.
;; Plus, both can use ggtags:
;;  - CAPF with `ggtags-completion-at-point', placed at ~/.emacs.d/straight/repos/ggtags/ggtags.el:836
;;  - company with `company-gtags' backend, placed at ~/.emacs.d/straight/repos/company-mode/company-gtags.el
;;
;; The summary for Elisp would be:
;; - CAPF would use `completion-at-point-functions', i.e. `elisp-completion-at-point' or `ggtags-completion-at-point'
;; (there is some t function as well, don't know why...)
;; - Company would use CAPF backend (including `elisp-completion-at-point' or `ggtags-completion-at-point')
;;   plus its own backend for company-gtags and its own backend for keywords and files.
;;
;; INFO: So, for the time being the recommended workflow would be to only use Company as it already includes CAPF completion.
;;  - `company-complete' will pop up a company menu and show exact matches (not-incremental).
;;  - `counsel-company' will incrementally complete in the minibuffer after inserting the beginning (company common part).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; More INFO:
;; - https://www.gnu.org/software/emacs/manual/html_node/elisp/Completion-in-Buffers.html
;; - https://github.com/minad/corfu/issues/9
;; - Documentation of `completion-at-point-functions':
;;     Each function on this hook is called in turn without any argument [...]
;;     The first function in completion-at-point-functions to return a non-nil value is used by completion-at-point.
;;     The remaining functions are not called.  The exception to this is when there is an :exclusive specification, as described above.
;;     Properties:
;;        ‘:exclusive’ value of ‘no’ means that if the completion table fails to
;;         match the text at point, then instead of reporting a completion
;;         failure, the completion should try the next completion function.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; More INFO:
;;  - CAPF is aware of the context, e.g.:
;;    - Elisp: results are different if capf is called inside a comment or after a parenthesis (functions)
;;    - Verilog: results are different if capf is called within a module, task/function or class (according to indentation functions)
;;
;;  - Icons on candidate list depend on `company-text-icons-mapping'.
;;    - Normally, the backend function should provide a (kind '<something>).
;;    - `company-gtags' does not provide it, and `verilog-completion-at-point' neither does it.
;;
;;  - Changed default binding to `company-other-backend' to switch between backends/groups of backends.
;;
;;; Code:


;;;; CAPF
;; Override company keybindings to use `completion-at-point' when executing "M-:" `eval-expression' at minibuffer.
(use-package minibuffer
  :straight nil
  :bind (:map minibuffer-local-map
         ("C-<return>" . completion-at-point)
         ("M-RET"      . completion-at-point))
  :config
  (setq enable-recursive-minibuffers t) ; Allow minibuffer commands while in the minibuffer.
  (setq completions-detailed t)) ; New in Emacs 28


;;;; Company
(use-package company
  :diminish
  :bind ("M-RET" . company-other-backend)
  :bind (:map company-active-map
         ("C-n" . company-select-next-or-abort)
         ("C-p" . company-select-previous-or-abort)
         ("C-j" . company-complete-selection))
  :config
  (setq company-idle-delay nil) ; Disable auto complete
  (setq company-transformers '(delete-consecutive-dups company-sort-by-occurrence)) ; Remove duplicate and sort by occurrence
  (setq company-tooltip-align-annotations t) ; Align annotations to the right

  ;; Flex search: Searches for characters in the given order, with anything in between.
  ;; e.g. "a-t-l" to find `add-to-list'
  ;; Default is `regexp-quote' which looks for an exact match.
  (setq company-search-regexp-function #'company-search-flex-regexp)

  ;; Company only uses one backend at a time, so set a backend for files/dirs and a grouped backend with keywords/tags/etc...
  ;; To keep the candidates organized in accordance with the grouped backends order, add the keyword :separate to the list of the grouped backends.
  ;; - https://company-mode.github.io/manual/Backends.html#Grouped-Backends
  (defvar larumbe/company-backends-common '(company-files (company-capf company-keywords company-gtags :separate)))

  (defun larumbe/company-backend-report ()
    "Show current backend used when running `company-other-backend'."
    (interactive)
    (let (formatted-backend
          backend-list)
      (if (listp company-backend)
          (progn
            (setq backend-list (remove :separate company-backend))
            (setq formatted-backend (propertize (mapconcat #'symbol-name backend-list ", ")
                                                'face '(:foreground "green"))))
        (setq formatted-backend (propertize (symbol-name company-backend)
                                            'face '(:foreground "green"))))
      ;; Run with timer to overwrite first suggestion from company after showing results
      (run-with-timer 0.1 nil (lambda () (message "Backend(s): %s" formatted-backend)))))

  (advice-add 'company-other-backend :after #'larumbe/company-backend-report))


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
