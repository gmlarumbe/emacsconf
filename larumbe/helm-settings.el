;;; helm-settings.el --- Helm & related   -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'custom-functions)
(require 'navi-mode)

;;;; Helm
(use-package helm
  :diminish
  :init
  ;; INFO: ido should not be enabled since compatibility with helm is managed by `helm-completing-read-handlers-alist'
  ;; However, if ido is not enabled, `ido-buffer-completion-map' does not get loaded
  ;; and therefore its not possible to make use of buffer killing while switching.
  (ido-mode 1) ; Enable, so that commands like `ido-kill-buffer-at-head' can be performed
  ;; Added in :init section because in config it only adds autoloads and ido
  ;; might be executed before helm loads these.

  :preface
  ;; Only included to avoid flycheck warnings, since `helm-M-x' is an autoload
  ;; for the files that declare the otherwise free variables.
  (require 'helm-mode)
  (require 'helm-occur)

  :commands (helm-autoresize-mode helm-set-local-variable larumbe/helm-occur)

  :bind (("C-x c /" . helm-find) ; Enable C-x c prefix commands
         ("C-x c p" . helm-list-emacs-process)
         ("C-x c t" . helm-top))
  :config
  (use-package helm-projectile :diminish)
  (use-package helm-ag)
  (use-package helm-org) ; Required by helm-havi

  (add-to-list 'helm-completing-read-handlers-alist '((switch-to-buffer . ido)
                                                      (kill-buffer      . ido)))
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


  ;; Advising
  (advice-add 'helm-occur :override #'larumbe/helm-occur))



;; `helm-navi' loads `navi-mode', and this last one loads `outshine'
(use-package helm-navi
  :diminish outshine-mode outline-minor-mode
  :commands (larumbe/helm-navi--get-candidates-in-buffer larumbe/helm-navi--get-regexp)
  :config
  ;; Function overriding:
  ;; BUG: Issue with helm-navi in last MELPA package
  ;; https://github.com/emacs-helm/helm-navi/pull/3
  ;; These functions needs to be redefined and:
  ;;  Search and replace of: outline-promotion-headings -> outshine-promotion-headings
  ;; INFO: This function also includes some modifications to fix an issue with
  ;; // * headings (do not remember if in Python or in SystemVerilog)
  (defun larumbe/helm-navi--get-candidates-in-buffer (buffer &optional regexp)
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


  (defun larumbe/helm-navi--get-regexp ()
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
            ".*$"))

  ;; Advising
  (advice-add 'helm-navi--get-candidates-in-buffer :override #'larumbe/helm-navi--get-candidates-in-buffer)
  (advice-add 'helm-navi--get-regexp               :override #'larumbe/helm-navi--get-regexp))



(provide 'helm-settings)

;;; helm-settings.el ends here
