;;; init-ggtags.el --- Ggtags/Global  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Ggtags & Xref:
;;  - Xref uses the backends in the `xref-backend-functions' hook, similar to how
;;    CAPF works (check commentary section of `init-completion').
;;  - If ggtags is enabled the `ggtags--xref-backend' function will be added to the
;;    hook and therefore gtags will be used as a backend for Xref.
;;  - Besides, some major modes define their own backends for Xref (e.g. `elisp--xref-backend')
;;  - Semantic adds a backend for other specific modes such as Python/HTML/C
;;
;;; Code:


(use-package ggtags
  :straight (:host github :repo "leoliu/ggtags"
             :fork (:repo "gmlarumbe/ggtags" :branch "xref-sync"))
  :diminish
  :commands (ggtags-create-tags
             modi/ggtags-tag-at-point
             larumbe/ggtags-global-handle-exit-advice)
  :bind (:map ggtags-navigation-map
         ("M-o"     . nil)
         ("C-c C-k" . nil) ; EXWM character mode
         ("M->"     . nil)
         ("M-<"     . nil))
  :bind (:map ggtags-mode-map
         ;; C-c `ggtags-mode-prefix-map' functions
         ("C-c M-DEL" . nil) ; Unmap `ggtags-delete-tags'
         ("C-c M-p"   . nil) ; Unmap `ggtags-prev-mark'
         ("C-c M-n"   . nil) ; Unmap `ggtags-next-mark'
         ("C-c M-f"   . nil) ; Unmap `ggtags-find-file'
         ("C-c M-o"   . nil) ; Unmap `ggtags-find-other-symbol'
         ("C-c M-g"   . nil) ; Unmap `ggtags-grep'
         ("C-c M-i"   . nil) ; Unmap `ggtags-idutils-query'
         ("C-c M-b"   . nil) ; Unmap `ggtags-browse-file-as-hypertext'
         ("C-c M-k"   . nil) ; Unmap `ggtags-kill-file-buffers'
         ("C-c M-h"   . nil) ; Unmap `ggtags-view-tag-history'
         ("C-c M-j"   . nil) ; Unmap `ggtags-visit-project-root'
         ("C-c M-/"   . nil) ; Unmap `ggtags-view-search-history'
         ("C-c M-SPC" . nil) ; Unmap `ggtags-save-to-register'
         ("C-c M-%"   . nil) ; Unmap `ggtags-query-replace'
         ("C-c M-?"   . nil) ; Unmap `ggtags-show-definition'
         ;; `ggtags-mode-map' functions
         ("M-."     . nil) ; Unmap `ggtags-find-tag-dwim'
         ("M-]"     . nil) ; Unmap `ggtags-find-references'
         ("C-M-."   . nil)) ; Remap back `xref-find-apropos'
  :bind (:map ggtags-global-mode-map
         ("r" . ggtags-query-replace))
  :config
  (setq ggtags-sort-by-nearness nil) ; INFO: If set to non-nil it will not work if using symlinks to external directories
  (setq ggtags-navigation-mode-lighter nil)
  (setq ggtags-mode-line-project-name nil)
  ;; INFO: Set to 1 to avoid the `global -u' automatic GTAGS update if tags file is smaller than the variable.
  (setq ggtags-oversize-limit 1)   ; If set to nil it seems that there is no limit...
  (setq ggtags-update-on-save nil) ; Try to avoid the `global -u in progress...'


;;;; Function overriding/wrapping
  ;; Don't consider ` (back quote) as part of `tag' when looking for a Verilog macro definition
  (defun modi/ggtags-tag-at-point ()
    (pcase (funcall ggtags-bounds-of-tag-function)
      (`(,beg . ,end)
       (if (eq ?` (string-to-char (buffer-substring beg end)))
           ;; If `(buffer-substring beg end)' returns "`uvm_info" (for example),
           ;; discard the ` and return just "uvm_info"
           (buffer-substring (1+ beg) end)
         ;; else return the whole `(buffer-substring beg end)'
         (buffer-substring beg end)))))

  ;; INFO: It is not a good idea to advice ggtags-mode as it also advices the
  ;; buffer-local variable `ggtags-mode', with some side-effects such as
  ;; recursive function calling when testing `ggtags-mode' variable...
  (advice-add 'ggtags-tag-at-point :override #'modi/ggtags-tag-at-point)


  ;; Similar to `ggtags-navigation-mode-done' but killing gtags buffer to avoid conflicts with
  ;; flycheck/compilation when moving to previous/next error.
  ;; Change at last call (ggtags-navigation-mode-cleanup nil t) setting 2nd argument to t to kill buffer
  (defun larumbe/ggtags-navigation-mode-done ()
    (interactive)
    (ggtags-navigation-mode -1)
    (setq tags-loop-scan t
          tags-loop-operate '(ggtags-find-tag-continue))
    (ggtags-navigation-mode-cleanup nil t))

  ;; Advice
  (advice-add 'ggtags-navigation-mode-done :override #'larumbe/ggtags-navigation-mode-done)


  ;; INFO: Issue with `ggtags-global-handle-exit' on remote machines where
  ;; *global* buffer was killed before `compilation-auto-jump' could jump to
  ;; first match, when there was only one match.
  ;; The problem was that `ggtags' relies heavily on `compilation-auto-jump'
  ;; executing as a hook of `compilation-finish-functions', and it runs through
  ;; a timer, so on slow/remote machines sometimes the buffer was killed before
  ;; jumping to the first/only match, giving an error.
  ;;
  ;; The workaround implied runnin `ggtags-navigation-mode-cleanup' also with a
  ;; programmable timer through the variable `larumbe/ggtags-global-handle-exit-timer-time'
  ;;
  ;; NOTE: This fix works only the first time a tag is visited if `ggtags-auto-jump-to-match'
  ;; is 'history since somehow once it has been stored in `ggtags-global-search-history'
  ;; it does not execute the adviced snippet of code.

  (defvar larumbe/ggtags-global-handle-exit-timer-time 1
    "Time for the timer to wait until global buffer is killed when there is only 1 result.
Default to 1 sec only if function has been advised through `larumbe/ggtags-global-handle-exit-advice'")
  (defvar larumbe/ggtags-global-handle-exit-use-idle-timer nil
    "If set to non-nil run an idle timer.")

  (defun larumbe/ggtags-global-handle-exit (buf how)
    "A function for `compilation-finish-functions' (which see)."
    (cond
     (ggtags-global-continuation
      (let ((cont (prog1 ggtags-global-continuation
                    (setq ggtags-global-continuation nil))))
        (funcall cont buf how)))
     ((string-prefix-p "exited abnormally" how)
      ;; If exit abnormally display the buffer for inspection.
      (ggtags-global--display-buffer)
      (when (save-excursion
              (goto-char (point-max))
              (re-search-backward
               (eval-when-compile
                 (format "^global: %s not found.$"
                         (regexp-opt '("GTAGS" "GRTAGS" "GSYMS" "GPATH"))))
               nil t))
        (ggtags-echo "WARNING: Global tag files missing in `%s'"
                     ggtags-project-root)
        (remhash ggtags-project-root ggtags-projects)))
     (ggtags-auto-jump-to-match
      (if (pcase (compilation-next-single-property-change
                  (point-min) 'compilation-message)
            ((and pt (guard pt))
             (compilation-next-single-property-change
              (save-excursion (goto-char pt) (end-of-line) (point))
              'compilation-message)))
          ;; INFO: Case when there are multiple matches
          ;; There are multiple matches so pop up the buffer.
          (and ggtags-navigation-mode (ggtags-global--display-buffer))

        ;; INFO: Else clause when there is only one match and global buffer gets killed.
        ;; Similar to the one in `ggtags-global-handle-exit' but running
        ;; the cleanup also with a timer.

        ;; Manually run the `compilation-auto-jump' timer. Hackish but
        ;; everything else seems unreliable. See:
        ;;
        ;; - http://debbugs.gnu.org/13829
        ;; - http://debbugs.gnu.org/23987
        ;; - https://github.com/leoliu/ggtags/issues/89
        ;;
        (pcase (cl-find 'compilation-auto-jump timer-list :key #'timer--function)
          (`nil )
          (timer (timer-event-handler timer)))
        (ggtags-navigation-mode -1)
        (if larumbe/ggtags-global-handle-exit-use-idle-timer
            (run-with-idle-timer larumbe/ggtags-global-handle-exit-timer-time
                                 nil
                                 #'ggtags-navigation-mode-cleanup buf t)
          (run-with-timer larumbe/ggtags-global-handle-exit-timer-time
                          nil
                          #'ggtags-navigation-mode-cleanup buf t))))))

  ;; Advice function (not used on every machine, only in remote slow ones)
  (defun larumbe/ggtags-global-handle-exit-advice (enable)
    "Advice `ggtags-global-handle-exit' if ENABLE is set to non-nil and
remove advice is ENABLE is set to nil."
    (if enable
        (progn
          (advice-add 'ggtags-global-handle-exit :override #'larumbe/ggtags-global-handle-exit)
          (message "Adviced `ggtags-global-handle-exit' with a %s secs timer" larumbe/ggtags-global-handle-exit-timer-time))
      (advice-remove 'ggtags-global-handle-exit #'larumbe/ggtags-global-handle-exit)
      (message "Removed advice on `ggtags-global-handle-exit'. Killing global buffer without timer!"))))



;; Own gtags async utilities
(use-package gtags-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/gtags-utils.el")))



(provide 'init-ggtags)

;;; init-ggtags.el ends here
