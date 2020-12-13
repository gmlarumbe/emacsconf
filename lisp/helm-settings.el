;;; helm-settings.el --- Helm & related   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;; (require 'custom-functions)
;; (require 'navi-mode)

;;;; Helm
(use-package helm
  :diminish
  :preface
  (require 'helm-mode) ; definition of `helm-completing-read-handlers-alist'
  (require 'helm-config)
  ;; INFO: ido should not be enabled since compatibility with helm is managed by `helm-completing-read-handlers-alist'
  ;; However, if ido is not enabled, `ido-buffer-completion-map' does not get loaded
  ;; and therefore its not possible to make use of buffer killing while switching.
  ;; Enable, so that commands like `ido-kill-buffer-at-head' can be performed
  (ido-mode 1)

  ;; TODO: Maybe it is because they are not bound to any map?
  :bind (("C-x c /" . helm-find) ; Enable C-x c prefix commands
         ("C-x c p" . helm-list-emacs-process)
         ("C-x c t" . helm-top))
  :config
  (use-package helm-projectile :diminish)
  (use-package helm-ag)
  (use-package helm-org) ; Required by helm-havi

  (add-to-list 'helm-completing-read-handlers-alist '(switch-to-buffer . ido))
  (add-to-list 'helm-completing-read-handlers-alist '(kill-buffer      . ido))
  (helm-mode 1)
  (helm-autoresize-mode 1)

  (defun larumbe/helm-help-major-mode ()
    "Get helm `M-x' commands list/shortcuts for the last time it was used.
It is assumed to be used after a `M-x' then e.g. `org-', then `C-g' and finally this function for window arrangement."
    (interactive)
    (delete-other-windows)
    (split-window-right)
    (other-window 1)
    (shrink-window 40 t)
    (switch-to-buffer "*helm M-x*")
    (other-window 1))

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
  (advice-add 'helm-occur :override #'larumbe/helm-occur))



;; `helm-navi' loads `navi-mode', and this last one loads `outshine'
(use-package helm-navi
  :diminish outshine-mode outline-minor-mode
  :defer ; Defer to fetch local version after load-path manual overriding
  )


(provide 'helm-settings)

;;; helm-settings.el ends here
