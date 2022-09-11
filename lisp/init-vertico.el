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
        completion-category-overrides '((file (styles basic partial-completion)))))

(use-package prescient
  :after vertico
  :demand)

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
         ("C-x c p" . counsel-list-processes)
         ("C-#"     . consult-outline)
         )
  :config
  (use-package consult-ag
    :straight (:host github :repo "yadex205/consult-ag")
    :bind (("M-g a" . consult-ag)))
  (use-package consult-company
    :bind (("<C-return>" . consult-company))) ; Replaces `minibuffer' function `completion-at-point'

  (defun larumbe/consult-symbol-at-point ()
    ""
    (interactive)
    (let* ((case-fold-search nil)
           (sym-atp (thing-at-point 'symbol :noprops))
           (initial-input (concat "\\_<" sym-atp "\\_>")))
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
