;;; init-xref.el --- Xref config  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Xref uses different backends to search for definitions and references. These backends are set in variable/hook `xref-backend-functions'.
;; Once a definition/reference is asked, the function `xref-find-backend' will execute `run-hook-with-args-until-success' which
;; actually executes the hooks sequentially (in order) until one of them is true. It is expected that this variable last element be
;; 't element (similar to `completion-at-point-functions'). In this case, the result of `run-hook-with-args-until-success' will be 'etags,
;; probably part of Emacs built-in defaults. Fortunately for Elisp the `elisp--xref-backend' is automatically added and always finds something,
;; preventing unwanted use of Etags. For other major-modes, the use of `dumb-jump' allows greping through ag, rg, and git-grep to fallback
;; for definitions/references findings.
;;
;; Xref will choose ONLY one backend through `xref-find-backend', the first one of `xref-backend-functions' that returns non-nil.
;;
;; Xref uses semantic engine to retrieve references through various backends: Global, IDutils, CScope or grep as a fallback.
;; Check variables: `semantic-symref-tool'. It makes use of `project-root' and project.el, a projectile-like based GNU ELPA
;; core package, probably intended to be added in future versions of Emacs.
;;
;; Working principles of xref and references:
;;   By default `xref-find-references' will search for a GPATH file (plus idutils and cscope files)
;;   on every directory/project. If non of these are found, it will use grep to find definitions and references.
;;   Current project is found through project.el `project-find-functions', which seems to work well, and external
;;   projects related to current one through the execution of the function `project-vc-external-roots-function'.
;;   By default, the value of `project-vc-external-roots-function' is (lambda () tags-table-list) and `xref-find-backend'
;;   defaults to t, so Etags is the default.
;;
;;; Code:


(use-package xref
  :straight nil
  :config
  (setq xref-auto-jump-to-first-definition t)
  (setq xref-auto-jump-to-first-xref t)
  (remove-hook 'xref-backend-functions #'etags--xref-backend) ; Avoid using etags (and asking for TAGS table)
  (add-hook 'xref--xref-buffer-mode-hook (lambda () (setq truncate-lines t))))


(use-package xref-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/xref-utils.el"))
  :after xref ; Otherwise functions get overriden the default ones in `xref'
  :bind (("M-." . larumbe/xref-find-definitions)  ; Allow using it in non-prog modes (e.g. open files/URLs with fundamental/conf modes)
         ("M-?" . larumbe/xref-find-references))) ; Let them being overriden by major-mode specific keybindings (e.g. `org-open-at-point')


(use-package dumb-jump
  :commands (larumbe/dumb-jump-local-enable)
  :config
  (defun larumbe/dumb-jump-local-enable ()
    "Set depth value of 't to 100 to give it the least possible priority with
    respect to other backends."
    (remove-hook 'xref-backend-functions 't t)
    (add-hook 'xref-backend-functions 't 100 t)
    (add-hook 'xref-backend-functions #'dumb-jump-xref-activate 1 t))

  ;; DANGER: Seems to work 'fine' if git-grep is left as the default searcher without modifications
  ;; However, if setting ripgrep as the preferred for everything except for git with (setq dumb-jump-prefer-searcher 'rg)
  ;; it will not find the definitions. Neither will it succeed if 'rg is forced for everything with (setq dumb-jump-force-searcher 'rg)
  ;; I tried with the following without sucess:
  ;;  - (setq dumb-jump-prefer-searcher 'rg)
  ;;  - (setq dumb-jump-force-searcher 'rg)
  ;;
  ;; NOTE: Also consider that `larumbe/projectile-project-root-or-current-dir' advice to
  ;; `dumb-jump-get-project-root' makes that `dumb-jump-xref-activate' will always return true
  ;; inside `xref-backend-functions', not allowing etags to execute.
  ;;
  ;; Also I am not completely sure if adding .repo/GTAGS denoters will make these
  ;; have precedence over .git since the dumb-jump-get-project-root is advised
  (add-to-list 'dumb-jump-project-denoters ".repo")
  (add-to-list 'dumb-jump-project-denoters "GTAGS")
  (advice-add 'dumb-jump-get-project-root :override #'larumbe/projectile-project-root-or-current-dir))



(provide 'init-xref)

;;; init-xref.el ends here

