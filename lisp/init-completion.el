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
;;; Code:


;;;; Company
(use-package company
  :diminish
  :bind ("<C-return>" . company-complete)
  :bind (:map company-active-map
         ("C-n" . company-select-next-or-abort)
         ("C-p" . company-select-previous-or-abort)
         ("C-j" . company-complete-selection))
  :config
  (setq company-idle-delay nil) ; Disable auto complete
  ;; Since company only uses one backend at a time, set only one grouped backend including all the desired ones.
  (defvar larumbe/company-backends-common '((company-keywords company-capf company-gtags company-files))))


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
