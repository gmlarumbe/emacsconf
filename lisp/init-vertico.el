;;; init-vertico.el --- Vertico -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package vertico
  :init
  (vertico-mode))

;; Persist history over Emacs restarts. Vertico sorts by history position.
(use-package savehist
  :init
  (savehist-mode))

(use-package orderless
  :after vertico
  :demand
  :config
  (setq completion-styles '(orderless basic)
        completion-category-defaults nil
        completion-category-overrides '((file (styles basic partial-completion))))
  ;; (add-to-list 'orderless-matching-styles 'char-fold-to-regexp)
  )

;; INFO: Last time I looked for it didn't appear on recommended packages of vertico/orderless
;; (use-package prescient
;;   :after vertico
;;   :demand)

(use-package marginalia
  :after vertico
  :demand
  :init
  (marginalia-mode))


(use-package consult
  :after vertico
  :demand
  :bind (("C-s"     . consult-line)
         ("M-s ."   . larumbe/consult-symbol-at-point)
         ("M-g r"   . consult-ripgrep)
         ("M-I"     . consult-imenu)
         ("C-x c /" . larumbe/consult-find)
         ;; ("C-x c p" . counsel-list-processes)
         ("C-#"     . consult-outline)
         )
  :config
  (use-package consult-ag
    :straight (:host github :repo "yadex205/consult-ag")
    :bind (("M-g a" . consult-ag)))
  (use-package consult-company
    :bind (("<C-return>" . consult-company))) ; Replaces `minibuffer' function `completion-at-point'

  ;; TODO: Issue with symbol/case detection in consult symbol at point:
  ;; https://github.com/minad/consult/issues/469
  ;;  - Recommendation for support of regexps in `consult-line' is to use orderless
  ;;  - It works well for everything if setting a symbol except if it's the last word of a line:
  ;;    e.g: Running M-x `consult-line' and looking for \_<consult\_> will find everything except for:
  ;;     (use-package consult
  ;;  - However, adding a dot (hidden character?) after consult will only detect this previous line:
  ;;     - \_<consult.\_>
  ;;  - I read something about hidden characters added by `consult-buffer' in following issue:
  ;;    - https://github.com/minad/consult/issues/365
  ;;    In the wiki there is a section covering this:
  ;;      - https://github.com/minad/consult/wiki
  ;;    Orderless style dispatchers (Ensure that the $ regexp works with consult-buffer)
  ;;      Unfortunately $ does not work out of the box with consult-buffer and consult-line since
  ;;      these commands add disambiguation suffixes to the candidate strings. The problem can be
  ;;      fixed by adjusting the filter regular expressions accordingly.
  ;;      See this reddit post for more context.
  ;;   There was a post afterwards about a sophisticated way of using orderless. Too much effort I guess...
  ;;   Get back to ivy! I think I gave it a try...
  (defun larumbe/consult-symbol-at-point ()
    ""
    (interactive)
    (let* (
           (case-fold-search nil)
           (orderless-smart-case nil)   ; INFO: This is the one that has (or should) have an effect
           (sym-atp (thing-at-point 'symbol :noprops))
           (initial-input (concat "\\_<" sym-atp "\\_>"))
           )
       (consult-line initial-input)))

  ;; https://github.com/minad/consult/wiki#find-files-using-fd
  (defvar consult--fd-command nil)
  (defun consult--fd-builder (input)
    (unless consult--fd-command
      (setq consult--fd-command
            (if (eq 0 (call-process-shell-command "fdfind"))
                "fdfind"
              "fd")))
    (pcase-let* ((`(,arg . ,opts) (consult--command-split input))
                 (`(,re . ,hl) (funcall consult--regexp-compiler
                                        arg 'extended t)))
      (when re
        (list :command (append
                        (list consult--fd-command
                              "--color=never" "--full-path"
                              (consult--join-regexps re 'extended))
                        opts)
              :highlight hl))))

  (defun consult-fd (&optional dir initial)
    (interactive "P")
    (let* ((prompt-dir (consult--directory-prompt "Fd" dir))
           (default-directory (cdr prompt-dir)))
      (find-file (consult--find (car prompt-dir) #'consult--fd-builder initial))))

  ;; Own commands
  (defun larumbe/consult-find (args)
    "Use `consult-fd' if fd is available. Otherwise fallback to `consult-find'."
    (interactive "P")
    (if (executable-find "fd")
        (call-interactively #'consult-fd)
      (call-interactively #'consult-find)))

  )


(use-package embark
  :after vertico
  :demand
  :bind
  (("C-;"   . embark-act)
   ("C-:"   . embark-dwim)
   ("C-h B" . embark-bindings)) ;; alternative for `describe-bindings'
  :init
  ;; Optionally replace the key help with a completing-read interface
  (setq prefix-help-command #'embark-prefix-help-command)
  :config
  ;; Hide the mode line of the Embark live/completions buffers
  (add-to-list 'display-buffer-alist
               '("\\`\\*Embark Collect \\(Live\\|Completions\\)\\*"
                 nil
                 (window-parameters (mode-line-format . none)))))

;; Consult users will also want the embark-consult package.
(use-package embark-consult
  :after (embark consult)
  :demand ; only necessary if you have the hook below
  ;; if you want to have consult previews as you move around an
  ;; auto-updating embark collect buffer
  :hook
  (embark-collect-mode . consult-preview-at-point-mode))



;; TODO: Still case fold doesn't seem to completely work with symbol at point
;; (use-packages consult

;; (Use-package consult)

;; (USE-PACKAGE consult)

;; (USE-PACKAGES consult)


(provide 'init-vertico)

;;; init-vertico.el ends here
