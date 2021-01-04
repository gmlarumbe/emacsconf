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
  :bind (("M-i" . imenu-list))
  :config
  (setq imenu-list-size 0.15)
  (setq imenu-auto-rescan t))


(use-package hide-comnt
  :ensure nil)


(use-package rainbow-delimiters)


(use-package wide-column
  :diminish
  :commands (wide-column-mode))


(use-package devdocs)


(use-package time-stamp
  :ensure nil
  :config
  (setq time-stamp-format "%:y-%02m-%02d %02H:%02M:%02S") ; Do not include user
  (setq time-stamp-line-limit 20)) ; Default 8


(provide 'prog-packages)

;;; prog-packages.el ends here
