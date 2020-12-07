;;; helm-settings.el --- Helm & related   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Helm
(use-package helm
  :diminish
  :bind (("C-x c /" . helm-find) ; Enable C-x c prefix commands
         ("C-x c p" . helm-list-emacs-process)
         ("C-x c t" . helm-top))
  :config
  (setq helm-completing-read-handlers-alist
        '((describe-function         . helm-completing-read-symbols)
          (describe-variable         . helm-completing-read-symbols)
          (describe-symbol           . helm-completing-read-symbols)
          (debug-on-entry            . helm-completing-read-symbols)
          (find-function             . helm-completing-read-symbols)
          (disassemble               . helm-completing-read-symbols)
          (trace-function            . helm-completing-read-symbols)
          (trace-function-foreground . helm-completing-read-symbols)
          (trace-function-background . helm-completing-read-symbols)
          (find-tag                  . helm-completing-read-default-find-tag)
          (org-capture               . helm-org-completing-read-tags)
          (org-set-tags              . helm-org-completing-read-tags)
          (ffap-alternate-file)
          (tmm-menubar)
          (find-file)
          (find-file-at-point        . helm-completing-read-sync-default-handler)
          (ffap                      . helm-completing-read-sync-default-handler)
          (execute-extended-command)
          ;; IDO support, theoretically without enabling ido-mode, but `ido-buffer-completion-map'
          ;; does not get loaded if ido-mode is not enabled, and therefore its not
          ;; possible to make use of buffer killing while switching.
          (switch-to-buffer . ido)
          (kill-buffer      . ido)
          ))
  (helm-mode 1)
  (helm-autoresize-mode 1))


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



;;;; Projectile + Helm-Projectile + Helm AG
(use-package projectile
  :bind (:map projectile-mode-map ; Projectile 2.0 removes automatic keybindings
              ("C-c p j" . projectile-find-tag)
              ("C-c p r" . projectile-regenerate-tags)
              ("C-c p c" . projectile-compile-project)
              ("C-c p f" . projectile-find-file)
              ("C-c p a" . helm-projectile-ag)
              ("C-c p g" . helm-projectile-grep))
  :config
  (use-package helm-projectile
    :diminish
    :config
    (use-package helm-ag))

  (add-to-list 'projectile-project-root-files-bottom-up ".repo") ; Detect `repo' Git sandboxes (Sandbox preference over IP)
  (setq projectile-completion-system 'helm)
  (setq projectile-mode-line-prefix " P") ; Modeline

  (defun larumbe/projectile-custom-mode-line ()
    "Report ONLY project name (without type) in the modeline.
Replaces `projectile-default-mode-line' that also showed ':generic' type of project"
    (let ((project-name (projectile-project-name)))
      (format "%s[%s]"
              projectile-mode-line-prefix
              (or project-name "-")
              )))
  (setq projectile-mode-line-function #'larumbe/projectile-custom-mode-line))



;;;; Helm-Navi + Outshine
(use-package outshine
  :config
  (setq outshine-imenu-show-headlines-p nil) ; Do not include outshine tags at imenu
  )


;; `helm-navi' loads `navi-mode', and this last one loads `outshine'
(use-package helm-navi
  :diminish outshine-mode outline-minor-mode
  :config
  (use-package helm-org) ; Required by helm-havi

;;;;; Function overriding
  ;; BUG: Issue with helm-navi in last MELPA package
  ;; https://github.com/emacs-helm/helm-navi/pull/3
  ;; These functions needs to be redefined and:
  ;;  Search and replace of: outline-promotion-headings -> outshine-promotion-headings
  (defun helm-navi--get-candidates-in-buffer (buffer &optional regexp)
    "Return Outshine heading candidates in BUFFER.
Optional argument REGEXP is a regular expression to match, a
function to return a regular expression, or
`outshine-promotion-headings' by default."
    ;; Much of this code is copied from helm-org.el
    (with-current-buffer buffer
      ;; Make sure outshine is loaded
      (unless outshine-promotion-headings
        (error "Outshine is not activated in buffer \"%s\".  Activate `outline-minor-mode', or consult Outshine's documentation for further instructions if necessary" (buffer-name buffer)))
      (let* ((heading-regexp (pcase regexp
                               ((pred functionp) (funcall regexp))
                               ((pred stringp) regexp)
                               ((pred null) (concat "^\\("
                                                    (mapconcat (lambda (s)                                     ;; DANGER: Modified to fix issue with // * headings,
                                                                 (replace-in-string "*" "\\*" (s-trim (car s)))) ;; asterisk is wrongly inserted into the regexp
                                                               outshine-promotion-headings
                                                               "\\|")
                                                    "\\)"
                                                    "\s+\\(.*\\)$"))))
             (match-fn (if helm-navi-fontify
                           #'match-string
                         #'match-string-no-properties))
             (search-fn (lambda ()
                          (re-search-forward heading-regexp nil t))))
        (save-excursion
          (save-restriction
            (goto-char (point-min))
            (cl-loop while (funcall search-fn)
                     for beg = (point-at-bol)
                     for end = (point-at-eol)
                     when (and helm-navi-fontify
                               (null (text-property-any
                                      beg end 'fontified t)))
                     do (jit-lock-fontify-now beg end)
                     for level = (length (match-string-no-properties 1))
                     for heading = (if regexp
                                       (funcall match-fn 0)
                                     (concat (match-string 1) " " (funcall match-fn 2)))
                     if (or regexp
                            (and (>= level helm-org-headings-min-depth)
                                 (<= level helm-org-headings-max-depth)))
                     collect `(,heading . ,(point-marker))))))))


  (defun helm-navi--get-regexp ()
    "Return regexp for all headings and keywords in current buffer."
    (concat (navi-make-regexp-alternatives
             (navi-get-regexp (car
                               (split-string
                                (symbol-name major-mode)
                                "-mode" 'OMIT-NULLS))
                              :ALL)
             (mapconcat (lambda (s)
                          (s-trim (car s)))
                        outshine-promotion-headings
                        "\\|"))
            ".*$")))



(provide 'helm-settings)

;;; helm-settings.el ends here
