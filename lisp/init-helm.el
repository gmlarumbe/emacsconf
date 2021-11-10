;;; init-helm.el --- Helm & related   -*- lexical-binding: t -*-
;;; Commentary:
;;
;; INFO: ido should not be enabled since compatibility with helm is managed by `helm-completing-read-handlers-alist'
;; However, if ido is not enabled, `ido-buffer-completion-map' does not get loaded
;; and therefore its not possible to make use of buffer killing while switching.
;;
;; If enabled, at some point the function `helm--generic-read-file-name' will disable it.
;; Besides, `helm-mode--disable-ido-maybe' will try to disable ido when `ido-everywhere' is set.
;;
;; Best solution is to use `ivy-switch-buffer' to switch buffers with ivy-mode disabled
;;
;;; Code:


;;;; Helm
(when (equal larumbe/completion-framework 'helm)
  (use-package helm
    :diminish
    :init
    (require 'helm-mode)   ; Required config/definitions (like `helm-completing-read-handlers-alist')
    (require 'helm-config) ; Helm autoloads
    :bind (("M-x"     . helm-M-x)
           ("C-x k"   . helm-mini)       ; Relay on ido for switch-buffer and C-k for individual kills
           ("C-x C-f" . helm-find-files)
           ("C-x r b" . helm-filtered-bookmarks)
           ("M-s o"   . helm-occur)      ; Might be advised
           ("M-g a"   . helm-do-grep-ag) ; Avoid `C-x c' prefix
           ("M-g r"   . helm-rg)
           ("M-I"     . helm-imenu)
           ("C-x c /" . helm-find) ; Enable C-x c prefix commands
           ("C-x c p" . helm-list-emacs-process)
           ("C-x c t" . helm-top)
           ("C-x c y" . helm-youtube)
           ("C-x C-h" . larumbe/helm-help-major-mode-or-scratch)) ; Could be deprecated after `which-key'
    :config
    (setq helm-grep-ag-command (concat "ag --line-numbers -S --color --nogroup -p " larumbe/gitignore-global-file " %s %s %s"))
    (use-package helm-rg
      :config
      (setq helm-rg-default-extra-args `("--ignore-file" ,larumbe/gitignore-global-file)))

    (use-package helm-youtube)

    (use-package helm-org) ; Required by helm-havi
    (use-package helm-navi
      :straight (:repo "emacs-helm/helm-navi"
                 :fork (:repo "gmlarumbe/helm-navi" :branch "fix-headings"))
      :bind (("C-#" . helm-navi-headings)
             ("M-#" . helm-navi))
      :diminish outshine-mode outline-minor-mode)

    ;; Actual config
    (helm-mode 1)
    (helm-autoresize-mode 1)


    (defun larumbe/helm-help-major-mode-or-scratch (&optional arg)
      "Get helm `M-x' commands list/shortcuts for the last time it was used.
It is assumed to be used after a `M-x' then e.g. `org-', then `C-g' and finally this function for window arrangement.

If universal ARG is provided, then switch to *scratch* buffer instead."
      (interactive "P")
      (delete-other-windows)
      (split-window-right)
      (other-window 1)
      (shrink-window 40 t)
      (if (not arg)
          (progn
            (switch-to-buffer "*helm M-x*")
            (other-window 1))
        (switch-to-buffer "*scratch*")
        (shrink-window -40 t)))

    ;; Function redefinitions for advising
    (defun larumbe/helm-occur (&optional prefix)
      "Copied from `helm-occur' and slightly modified to allow searching symbols.
If called without PREFIX argument search for symbol and case-sensitive.
If called with PREFIX, search for string and no case sensitive."
      (interactive "P")
      ;; DANGER: Added to do a case-sensitive search
      (let ((case-fold-search prefix))
        ;; End of DANGER
        (setq helm-source-occur
              (car (helm-occur-build-sources (list (current-buffer)) "Helm occur")))
        (helm-set-local-variable 'helm-occur--buffer-list (list (current-buffer))
                                 'helm-occur--buffer-tick
                                 (list (buffer-chars-modified-tick (current-buffer))))
        (save-restriction
          (let (def pos)
            (when (use-region-p)
              ;; When user mark defun with `mark-defun' with intention of
              ;; using helm-occur on this region, it is relevant to use the
              ;; thing-at-point located at previous position which have been
              ;; pushed to `mark-ring'.
              (setq def (save-excursion
                          (goto-char (setq pos (car mark-ring)))
                          (helm-aif (thing-at-point 'symbol) (regexp-quote it))))
              (narrow-to-region (region-beginning) (region-end)))
            (unwind-protect
                (helm :sources 'helm-source-occur
                      :buffer "*helm occur*"
                      :default (or def (helm-aif (thing-at-point 'symbol)
                                           ;; DANGER: Modified at this point
                                           (if (not prefix)
                                               (concat "\\_<" (regexp-quote it) "\\_>")
                                             (regexp-quote it))
                                         ;; End of DANGER
                                         ))
                      :preselect (and (memq 'helm-source-occur
                                            helm-sources-using-default-as-input)
                                      (format "^%d:" (line-number-at-pos
                                                      (or pos (point)))))
                      :truncate-lines helm-occur-truncate-lines)
              (deactivate-mark t))))))


    ;; Better advising instead of forking since it's not a bug but a customization.
    ;; Otherwise would need to get updated manually to latest helm changes.
    (advice-add 'helm-occur :override #'larumbe/helm-occur)))




(provide 'init-helm)

;;; init-helm.el ends here
