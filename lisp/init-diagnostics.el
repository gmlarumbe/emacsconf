;;; init-diagnostics.el --- Flycheck & Flymake  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defface larumbe/diagnostics-info-face
  '((t (:foreground "light green")))
  "Face for popup tip (info)."
  :group 'larumbe-faces)

(defface larumbe/diagnostics-warning-face
  '((t (:foreground "yellow")))
  "Face for popup tip (warning)."
  :group 'larumbe-faces)

(defface larumbe/diagnostics-error-face
  '((t (:foreground "red")))
  "Face for popup tip (error)."
  :group 'larumbe-faces)


(use-package flycheck
  :diminish
  :commands (flycheck-display-error-messages-unless-error-list)
  :config
  ;; Elisp flychecker
  (setq flycheck-emacs-lisp-load-path 'inherit)
  (setq flycheck-emacs-lisp-initialize-packages t)
  ;; Seems it shows full error if multiline
  (setq flycheck-display-errors-function #'flycheck-display-error-messages-unless-error-list))


(use-package flycheck-inline
  :hook ((flycheck-mode . flycheck-inline-mode))
  :config
  (set-face-attribute 'flycheck-inline-info nil :foreground "light green"))
;; Replaces `lsp-ui-sideline-mode' from `lsp-ui':
;;  - Better since diagnostic error appears right below the error
;;    (in lsp-ui it appeared at the side, sometime quite far from the error)
;;
;; Seems maintained and works out of the box:
;;  - Tried `flycheck-popup-tip' but there was something that did not work well
;;  related to `flycheck-popup-tip-delete-popup' and `pre-command-hook' not working well
;;
;; Provides a similar alternative to `flymake-diagnostic-at-point' for buffers
;; in LSP that use flymake


(use-package flymake
  :straight nil
  :hook ((flymake-mode . larumbe/flymake-hook))
  :init
  (setq flymake-note-bitmap '(exclamation-mark larumbe/diagnostics-info-face))
  :config
  (set-face-attribute 'flymake-warning nil :underline '(:style wave :color "orange"))
  (defun larumbe/flymake-hook ()
    "Allow use of M-n and M-p to navigate flymake errors.

     From /opt/emacs-29.3/share/emacs/29.3/lisp/progmodes/flymake.el.gz:1109
Documentation string of `flymake-mode'."
    (setq-local next-error-function #'flymake-goto-next-error)))


(use-package flymake-diagnostic-at-point
  :after flymake
  :ensure t
  :hook ((flymake-mode . flymake-diagnostic-at-point-mode))
  :init
  (setq flymake-diagnostic-at-point-display-diagnostic-function #'larumbe/flymake-diagnostic-at-point-display-popup)
  :config
  ;; Same as original function in the package but using different faces depending on severity
  (defun larumbe/flymake-diagnostic-at-point-display-popup (text)
    "Display the flymake diagnostic TEXT inside a popup."
    (let* ((text (flymake--diag-text (get-char-property (point) 'flymake-diagnostic)))
           (type (flymake--diag-type (get-char-property (point) 'flymake-diagnostic)))
           (face (pcase type
                   (:note 'larumbe/diagnostics-info-face)
                   (:warning 'larumbe/diagnostics-warning-face)
                   (:error 'larumbe/diagnostics-error-face)
                   (_ 'larumbe/popup-tip-flymake-error-face))))
      (popup-tip text :face face))))


(use-package flyspell
  :straight nil
  :init
  (setq flyspell-use-meta-tab nil) ; Leave M-TAB (C-M-i) for indent block
  (setq flyspell-auto-correct-binding (kbd "M-=")) ; Cannot be nil, overriden later in :bind section
  :bind (:map flyspell-mode-map
         ("C-=" . flyspell-goto-next-error)
         ("C-+" . flyspell-auto-correct-word)
         ("M-=" . flyspell-buffer)) ; Override `flyspell-auto-correct-binding'
  :bind (("C-M-=" . flyspell-mode)))



(provide 'init-diagnostics)

;;; init-diagnostics.el ends here
