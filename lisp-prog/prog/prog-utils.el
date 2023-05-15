;;; prog-utils.el --- Prog-mode derived modes utils  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;  Semantic adds an Xref backend for specific modes such as Python/HTML/C.
;;  That's the reason why they are included in `larumbe/prog-mode-references'.
;;  DANGER: Tried to check this on 3 April 2022 and dunno if it was certain...?
;;
;;; Code:

(require 'init-completion)

(defun larumbe/prog-mode-keys ()
  "Hook to set keys that will override the ones set in the derived major mode."
  (local-set-key (kbd "C-<tab>") #'hs-toggle-hiding)
  (local-set-key (kbd "C-c C-n") #'align-regexp)
  (local-set-key (kbd "C-c C-s") #'larumbe/yas-insert-snippet-dwim)
  (unless (or (eq major-mode 'verilog-mode)
              (eq major-mode 'verilog-ts-mode))
    (local-set-key (kbd "C-c C-f") #'flycheck-mode)))

(defun larumbe/prog-mode-indent-tabs-mode ()
  "Do not use TAB for indentation, except for Makefile modes."
  (interactive)
  (if (string-match "makefile-" (format "%s" major-mode))
      (setq indent-tabs-mode t)
    (setq indent-tabs-mode nil)))

(defun larumbe/prog-mode-hook ()
  "Basic Hook for derived programming modes."
  (ggtags-mode               1)
  (projectile-mode           1)
  (company-mode              1)
  (show-paren-mode           1)
  (display-line-numbers-mode 1)
  (outshine-mode             1)
  (fic-mode                  1)
  (yas-minor-mode            1)
  (hs-minor-mode             1)
  (wide-column-mode          1)
  (lsp-ui-sideline-mode      1) ; Flycheck/company frontend enhancements without enabling lsp mode
  (setq truncate-lines       t)
  (setq fill-column         80)
  (setq-local company-backends larumbe/company-backends-common)
  (larumbe/dumb-jump-local-enable)
  (gtags-update-async-minor-mode 1)
  (larumbe/prog-mode-indent-tabs-mode))


(provide 'prog-utils)

;;; prog-utils.el ends here
