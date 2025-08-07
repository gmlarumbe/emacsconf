;;; init-grep.el --- Grep/Silver Searcher/RipGrep  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Silver-searcher
(use-package ag
  :commands (ag/search)
  :init
  (setq ag-arguments           ; Fetched from modi verilog config
        '("--numbers"          ; Line numbers
          "--smart-case"
          "--follow"           ; Follow symlinks
          "--ignore" "#*#"     ; Adding "*#*#" or "#*#" to .ignore does not work for ag (works for rg)
          "--ignore" "*~"
          "--stats"))
  (setq ag-reuse-buffers t)
  (setq ag-reuse-window t)
  (setq ag-highlight-search t)
  (setq ag-group-matches t))


;;;; Ripgrep
(defvar larumbe/rg-arguments
  `("--line-number"       ; Line numbers
    "--smart-case"
    "--follow"            ; Follow symlinks
    "--max-columns" "240" ; Emacs doesn't handle long line lengths very well
    "--ignore-file" ,larumbe/gitignore-global-file)
  "Default rg arguments used in functions (helm, counsel, `projectile')")

(use-package ripgrep
  :straight (:repo "nlamirault/ripgrep.el")
  :init
  (setq ripgrep-arguments (append larumbe/rg-arguments '("-w")))
  :config
  ;; Remove --line-number since it's already in `larumbe/rg-arguments'
  (setq ripgrep--base-arguments '("--with-filename" "--no-heading")))


;;;; Own utils
(use-package grep-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/grep-utils.el"))
  :hook ((ag-search-finished . ag/jump-to-result-if-only-one-match))
  :commands (larumbe/ripgrep-regexp-symbol-at-point
             larumbe/ripgrep-xref))


;;;; Wgrep
;; https://github.com/mhayashi1120/Emacs-wgrep
;; Workflow:
;; - C-c C-p to switch to wgrep
;; - Make changes (an overlay shows up)
;; - C-c C-e to apply changes
;; - C-x s to save changes
;; - C-x C-s to leave wgrep editing mode
(use-package wgrep
  :bind (:map wgrep-mode-map
         ("C-x s" . wgrep-save-all-buffers)))


;; Allow editing in *ag* buffers
;; BUG: Could not make it work, always detects the buffer as read-only.
;;  - Solution: use `ivy-occur' as a great alternative with swiper/counsel.
(use-package wgrep-ag
  :hook ((ag-mode . wgrep-ag-setup)))


;;; Provide
(provide 'init-grep)

;;; init-grep.el ends here
