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

  (defun larumbe/ggtags-tag-at-point ()
    "Don't consider ` (back quote) as part of `tag' when looking for a Verilog macro definition.
Used by `xref' among others."
    (pcase (funcall ggtags-bounds-of-tag-function)
      (`(,beg . ,end)
       (if (and (or (equal major-mode 'verilog-mode)
                    (equal major-mode 'verilog-ts-mode))
                (eq ?` (string-to-char (buffer-substring beg end))))
           (buffer-substring (1+ beg) end)
         (buffer-substring beg end)))))

  (advice-add 'ggtags-tag-at-point :override #'larumbe/ggtags-tag-at-point)

  ;; Similar to `ggtags-navigation-mode-done' but killing gtags buffer to avoid conflicts with
  ;; flycheck/compilation when moving to previous/next error.
  ;; Change at last call (ggtags-navigation-mode-cleanup nil t) setting 2nd argument to t to kill buffere
  ;; INFO: Should not be needed anymore if using `xref' instead of `ggtags' derived from compilation mode
  (defun larumbe/ggtags-navigation-mode-done ()
    (interactive)
    (ggtags-navigation-mode -1)
    (setq tags-loop-scan t
          tags-loop-operate '(ggtags-find-tag-continue))
    (ggtags-navigation-mode-cleanup nil t))

  (advice-add 'ggtags-navigation-mode-done :override #'larumbe/ggtags-navigation-mode-done))


(use-package gtags-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/gtags-utils.el")))



(provide 'init-ggtags)

;;; init-ggtags.el ends here
