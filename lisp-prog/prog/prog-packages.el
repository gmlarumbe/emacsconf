;;; prog-packages.el --- Prog-mode Common Packages  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package fic-mode
  :commands (larumbe/clean-fic-keywords-dir
             larumbe/wrap-danger-region)
  :config
  (setq fic-activated-faces '(font-lock-doc-face  font-lock-comment-face))
  (setq fic-highlighted-words '("FIXME" "TODO" "BUG" "DANGER" "INFO" "NOTE"))

  (defun larumbe/clean-fic-keywords-dir ()
    "Perform `counsel-ag' of `fic-mode' highlighted keywords in selected DIR
in order to check pending project actions."
    (interactive)
    (require 'counsel)
    (let ((kwd (completing-read "Select keyword: " fic-highlighted-words))
          (path (read-directory-name "Directory: "))
          (files (completing-read "Select file regex: " '("(System)Verilog" "Python" "elisp")))
          (counsel-ag-base-command counsel-ag-base-command) ; Save the global value of `counsel-ag-base-command'
          (regex))
      (pcase files
        ("(System)Verilog" (setq regex ".[s]?v[h]?$")) ; +Headers
        ("Python"          (setq regex ".py$"))
        ("elisp"           (setq regex ".el$")))
      ;; `counsel-ag' glob search
      (setq counsel-ag-base-command (append counsel-ag-base-command '("-G")))
      (setq counsel-ag-base-command (append counsel-ag-base-command (list regex)))
      (counsel-ag kwd path)))


  (defun larumbe/wrap-danger-region ()
    "Wrap current line or region with DANGER comments for `fic-mode' highlighting."
    (interactive)
    (let ((text-begin "DANGER")
          (text-end   "End of DANGER"))
      (larumbe/comment-tag-line-or-region text-begin text-end))))



(use-package hideshow
  :straight nil
  :diminish hs-minor-mode)



(use-package outline
  :straight nil
  :diminish outline-minor-mode)


(use-package outshine
  :diminish outshine-mode)


(use-package flycheck
  :diminish
  :commands (flycheck-display-error-messages-unless-error-list)
  :bind (:map flycheck-mode-map
         ;; INFO: Precedence on current file over existing compilation/gtags/ag
         ("M-n" . flycheck-next-error)
         ("M-p" . flycheck-previous-error))
  :config
  ;; Seems it shows full error if multiline
  (setq flycheck-display-errors-function #'flycheck-display-error-messages-unless-error-list))


(use-package flyspell
  :straight nil
  :commands (flyspell-toggle)
  :config
  (defun flyspell-toggle ()
    "Toggle flyspell mode on current buffer."
    (interactive)
    (if flyspell-mode
        (progn
          (flyspell-mode -1)
          (message "Flyspell disabled..."))
      (flyspell-mode 1)
      (message "Flyspell enabled..."))))



(use-package diff-mode
  :bind (:map diff-mode-map
              ("M-o" . other-window)) ; Remove `M-o' binding (Overrides 'diff-goto-source, which is defined by `o' as well)
  :hook ((diff-mode . (lambda () (setq truncate-lines t)))
         (diff-mode . linum-mode)))

(use-package ediff
  :config
  ;; Layout configuration
  (require 'ediff-wind)
  (setq ediff-split-window-function #'split-window-horizontally)
  (setq ediff-window-setup-function #'ediff-setup-windows-plain)

  ;; Restoring windows and layout after an Ediff session:
  ;; https://emacs.stackexchange.com/questions/7482/restoring-windows-and-layout-after-an-ediff-session
  (defvar larumbe/ediff-last-windows nil)

  (defun larumbe/store-pre-ediff-winconfig ()
    (setq larumbe/ediff-last-windows (current-window-configuration)))

  (defun larumbe/restore-pre-ediff-winconfig ()
    (set-window-configuration larumbe/ediff-last-windows))

  (add-hook 'ediff-before-setup-hook #'larumbe/store-pre-ediff-winconfig)
  (add-hook 'ediff-quit-hook         #'larumbe/restore-pre-ediff-winconfig)


  ;; INFO: Face highlighting color fix due to theme customization
  ;; These faces were set by 'deeper-blue-theme.el': ~/.emacs.d/straight/repos/emacs/etc/themes/deeper-blue-theme.el:57
  ;; Ediff comparison of buffers in Magit assumes the following Git convention to compare old to new: revision^..revision
  ;; This caused that when comparing with ediff with the same range the diffB color was orange and diffA green.
  ;; That was misleading since it showed adittions in orange and removed things in green.
  (set-face-attribute 'ediff-current-diff-B nil :background "green4"      :foreground "white" :inherit nil)
  (set-face-attribute 'ediff-fine-diff-B    nil :background "skyblue4"    :foreground "white" :inherit nil)
  (set-face-attribute 'ediff-odd-diff-B     nil :background "Grey50"      :foreground "White" :inherit nil)
  (set-face-attribute 'ediff-current-diff-A nil :background "darkorange3" :foreground "white" :inherit nil)
  (set-face-attribute 'ediff-fine-diff-A    nil :background "cyan4"       :foreground "white" :inherit nil)
  (set-face-attribute 'ediff-even-diff-A    nil :background "Grey50"      :foreground "White" :inherit nil)
  ;; Last tweak to show green changes at the left
  ;; Meant to be used for 2 buffers. If three are used then it will rotate just once after startup.
  (add-hook 'ediff-startup-hook #'ediff-swap-buffers))



(use-package imenu-list
  :bind (("M-i" . modi/imenu-list-display-toggle))
  :bind ((:map imenu-list-major-mode-map
          ("M-RET" . modi/imenu-list-goto-entry-and-hide)))
  :config
  (setq imenu-list-size 0.15)
  (setq imenu-auto-rescan t)

  (defun modi/imenu-list-hide ()
    (interactive)
    (switch-to-buffer-other-window imenu-list-buffer-name)
    (quit-window))

  (defun modi/imenu-list-visible-p ()
    "Returns `t' if the `imenu-list' buffer is visible."
    (catch 'break
      (dolist (win (window-list))
        (when (string= imenu-list-buffer-name (buffer-name (window-buffer win)))
          (throw 'break t)))))

  (defun modi/imenu-list-display-toggle (noselect)
    "Toggle the display of Imenu-list buffer.

If NOSELECT is non-nil, do not select the imenu-list buffer."
    (interactive "P")
    (if (modi/imenu-list-visible-p)
        (modi/imenu-list-hide)
      (if noselect
          (imenu-list-noselect)
        (imenu-list))))

  (defun modi/imenu-list-goto-entry-and-hide ()
    "Execute `imenu-list-goto-entry' and hide the imenu-list buffer."
    (interactive)
    (imenu-list-goto-entry)
    (modi/imenu-list-hide))

  (defun modi/imenu-auto-update (orig-fun &rest args)
    "Auto update the *Ilist* buffer if visible."
    (prog1 ; Return value of the advising fn needs to be the same as ORIG-FUN
        (apply orig-fun args)
      (when (modi/imenu-list-visible-p)
        (imenu-list-update-safe)))) ; update `imenu-list' buffer

  (advice-add 'switch-to-buffer :around #'modi/imenu-auto-update)
  (advice-add 'revert-buffer    :around #'modi/imenu-auto-update))


(use-package hide-comnt
  :straight (:host github :repo "emacsmirror/emacswiki.org" :branch "master" :files ("hide-comnt.el"))
  :commands (hide/show-comments-toggle))


(use-package rainbow-delimiters)


(use-package wide-column
  :diminish
  :commands (wide-column-mode))


(use-package time-stamp
  :straight nil
  :hook ((before-save . time-stamp))
  :config
  (setq time-stamp-format "%:y-%02m-%02d %02H:%02M") ; Do not include user nor seconds
  (setq time-stamp-line-limit 20)) ; Default 8


;; Global mode used by C, Python, HTML and others
(use-package semantic
  :bind (:map semantic-mode-map
         ("C-c ," . nil)) ; INFO: Unbinds ALL semantic commands, since C-c , is the prefix
  :hook ((c-mode-common . larumbe/semantic-mode))
  :config
  (defvar larumbe/semantic-enable nil
    "Conditionally determine in a hook if mode is enabled.")

  (defun larumbe/semantic-mode (&optional arg)
    "Enable semantic depending on value of `larumbe/semantic-enable'.

Purpose is to use this function as a conditional hook.
ARG will be passed to wrapped function `semantic-mode'."
    (interactive)
    (if larumbe/semantic-enable
        (semantic-mode arg)
      (semantic-mode -1))))


(provide 'prog-packages)

;;; prog-packages.el ends here
