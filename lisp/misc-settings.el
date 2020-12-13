;;; misc-settings.el --- Misc settings  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;; There are 2 packages, unison and unison-mode.
;; The first one for process invocation
;; The second one for syntax highlighting and process invocation -> Using this
(use-package unison-mode
  :bind (:map unison-mode-map
              ("C-c C-c" . unison-my-run))
  :mode (("\\.prf\\'" . unison-mode))
  :hook ((unison-mode . unison-sync-minor-mode))
  :config
  (use-package unison-sync-minor-mode
    :ensure nil))


(provide 'misc-settings)

;;; misc-settings.el ends here
