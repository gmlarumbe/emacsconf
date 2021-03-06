;;; prog-packages.el --- Prog-mode Common Packages  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package fic-mode
  :config
  (require 'ag)

  (setq fic-activated-faces '(font-lock-doc-face  font-lock-comment-face))
  (setq fic-highlighted-words '("FIXME" "TODO" "BUG" "DANGER" "INFO" "NOTE"))

  (defun larumbe/clean-fic-keywords-dir ()
    "Perform an `ag-regexp' of `fic-mode' highlighted keywords in selected DIR
in order to check pending project actions. "
    (interactive)
    (let ((kwd (completing-read "Select keyword: " fic-highlighted-words))
          (path (read-directory-name "Directory: "))
          (files (completing-read "Select file regex: " '("(System)Verilog" "Python" "elisp")))
          (ag-arguments ag-arguments) ; Save the global value of `ag-arguments'
          (regex))
      (pcase files
        ("(System)Verilog" (setq regex ".[s]?v[h]?$")) ; +Headers
        ("Python"          (setq regex ".py$"))
        ("elisp"           (setq regex ".el$")))
      ;; ag glob search
      (setq ag-arguments (append ag-arguments '("-G")))
      (setq ag-arguments (append ag-arguments (list regex)))
      (ag-regexp kwd path))))



(use-package hideshow
  :ensure nil
  :diminish hs-minor-mode)



(use-package outline
  :ensure nil
  :diminish outline-minor-mode)


(use-package outshine
  :diminish outshine-mode)


(use-package flycheck
  :diminish
  :commands (flycheck-display-error-messages-unless-error-list)
  :config
  (setq flycheck-display-errors-function ; Seems it shows full error if multiline
        #'flycheck-display-error-messages-unless-error-list))


(use-package flyspell
  :ensure nil
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
         (diff-mode . linum-mode))
  :config
  (require 'ediff-wind)
  (setq ediff-split-window-function #'split-window-horizontally)
  (setq ediff-window-setup-function #'ediff-setup-windows-plain))



(use-package imenu-list
  :bind (("M-i" . modi/imenu-list-display-toggle))
  :bind ((:map imenu-list-major-mode-map
          ("C-<return>" . modi/imenu-list-goto-entry-and-hide)))
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
  :ensure nil)


(use-package rainbow-delimiters)


(use-package wide-column
  :diminish
  :commands (wide-column-mode))


(use-package time-stamp
  :ensure nil
  :config
  (setq time-stamp-format "%:y-%02m-%02d %02H:%02M:%02S") ; Do not include user
  (setq time-stamp-line-limit 20)) ; Default 8


;; Global mode used by C, Python, HTML and others
(use-package semantic
  :bind (:map semantic-mode-map
         ("C-c ," . nil)) ; INFO: Unbinds ALL semantic commands, since C-c , is the prefix
  :hook ((c-mode-common . larumbe/semantic-mode))
  :config
  (defvar larumbe/semantic-enable t
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
