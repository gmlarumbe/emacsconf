; Wombat Custom Theme

;; Added by Package.el.  This must come before configurations of
;; installed packages.  Don't delete this line.  If you don't want it,
;; just comment it out by adding a semicolon to the start of the line.
;; You may delete these explanatory comments.
;; (package-initialize)

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(custom-enabled-themes (quote (deeper-blue)))
 '(custom-safe-themes
   (quote
    ("3c83b3676d796422704082049fc38b6966bcad960f896669dfc21a7a37a748fa" "a27c00821ccfd5a78b01e4f35dc056706dd9ede09a8b90c6955ae6a390eb1c1e" default)))
 '(package-selected-packages
   (quote
    (elgrep magithub csv csv-mode jinja2-mode ssh-tunnels yasnippet-snippets yasnippet html-mode conf-space-mode python-mode matlab-mode helm-ag ggtag unison-mode dired vc-mode vc-dir vc-svn move-lines whole-line-or-region virtualenv use-package sudo-ext smart-mode-line popwin php-runtime markdown-mode magit json-mode jenkins jedi-core imenu-list helm-youtube helm-projectile helm-navi google-this go-mode ggtags fic-mode exwm elmacro dsvn dired-quick-sort dired-narrow diminish conda coin-ticker bind-chord auto-complete ag))))

(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(outshine-level-1 ((t (:inherit outline-7))))
 '(outshine-level-2 ((t (:inherit outline-8))))
 '(outshine-level-3 ((t (:inherit outline-6))))
 '(outshine-level-4 ((t (:inherit outline-5))))
 '(outshine-level-5 ((t (:inherit outline-1))))
 '(outshine-level-6 ((t (:inherit outline-4))))
 '(outshine-level-7 ((t (:inherit outline-2))))
 '(outshine-level-8 ((t (:inherit outline-3))))
 '(verilog-font-lock-grouping-keywords-face ((t (:foreground "dark olive green" :weight bold))))
 '(which-func ((t (:foreground "green")))))


;; Emacs Basic config setup
(load "~/.elisp/larumbe/config-basic.el")

;; Emacs Packages setup
(load "~/.elisp/larumbe/packages-config.el")

;; Custom functions
(load "~/.elisp/larumbe/custom-functions.el")

;; Custom Macros as functions
(load "~/.elisp/larumbe/macros.el")

;; Process/Compilation buffers config
(load "~/.elisp/larumbe/compilation-settings.el")

;; Programming languages config
(load "~/.elisp/larumbe/programming-settings.el")

;; Emacs X-Window Manager config
(load "~/.elisp/larumbe/exwm-config.el")

;; Machine specific settings files:
;;   - This file will not be present in the repo
;;   - It will have specific content to the machine (e.g. EXWM enabling)
(load "~/.emacs.d/.elisp_private/machine/machine-config.el" t)
