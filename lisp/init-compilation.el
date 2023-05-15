;;; init-compilation.el --- Compilation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package compile
  :straight nil
  :bind (([f5]  . compile))
  :bind (:map compilation-mode-map
         ("r"     . rename-buffer)
         ("M-."   . larumbe/xref-find-definitions)) ; Browse URLs and files
  :bind (:map compilation-shell-minor-mode-map
         ("M-RET" . nil)) ; Leave space for `company-complete'
  :bind (:map comint-mode-map
         ("TAB"   . completion-at-point))  ; Similar to ansi-term (e.g. for vivado/diamond tcl-shell)
  :hook ((compilation-mode   . larumbe/compilation-hook)
         (compilation-filter . colorize-compilation-buffer))
  :commands (recompile
             comint-send-string)
  :config
  (require 'popwin)
  (require 'ansi-color) ; Buffer colorizing

  (add-to-list 'popwin:special-display-config '(compilation-mode :stick t))

  ;; Compilation motion commands skip less important messages. The value can be either
  ;; 2 -- skip anything less than error,
  ;; 1 -- skip anything less than warning or
  ;; 0 -- don't skip any messages.
  (setq compilation-skip-threshold 2) ; Compilation error jumping settings
  (setq compilation-message-face nil) ; Set to nil to remove underlines from compilation faces (defaults to 'underline)
  (setq compilation-scroll-output 'first-error)

  (defun larumbe/compilation-hook ()
    ;; Do not enable line numbers since it slows down large compilation buffers
    (setq truncate-lines t)
    ;; Split compilation vertically: https://stackoverflow.com/questions/966191/how-can-i-get-the-compilation-buffer-on-the-bottom-rather-than-on-the-right-in-em/
    (setq-local split-width-threshold nil))

  ;; https://stackoverflow.com/questions/13397737/ansi-coloring-in-compilation-mode
  (defun colorize-compilation-buffer ()
    "Apply color to comint buffers (e.g. convert '\033[0;31m' to red)."
    (ansi-color-apply-on-region compilation-filter-start (point)))

  ;; Print elapsed time in compilation buffer
  ;; https://emacs.stackexchange.com/questions/31493/print-elapsed-time-in-compilation-buffer
  (defvar larumbe/compilation-start-time)

  (defun larumbe/compilation-start-hook (proc)
    (setq-local larumbe/compilation-start-time (current-time)))

  (defun larumbe/compilation-finish-function (buf why)
    (when (boundp 'larumbe/compilation-start-time) ; When finding definitions/references with ggtags, somehow compilation is used under the hood, and `larumbe/compilation-start-time' is not defined (nor is required)
      (let* ((elapsed (time-subtract nil larumbe/compilation-start-time))
             (msg (format "Compilation elapsed time: %s" (format-seconds "%Y, %D, %H, %M, %z%S" elapsed))))
        (save-excursion
          (goto-char (point-max))
          (insert "\n")
          (insert msg)))))

  ;; Add hooks outside of use-package because `compilation-finish-functions' name does not end in -hook
  (add-hook 'compilation-start-hook       #'larumbe/compilation-start-hook)
  (add-hook 'compilation-finish-functions #'larumbe/compilation-finish-function))



(use-package compilation-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/compilation-utils.el"))
  :after compile
  :demand
  :mode (("\\.srr\\'" . synplify-log-mode))
  :bind (:map compilation-mode-map
         ("j" . larumbe/recompile-with-regexp-alist)
         ("t" . larumbe/compilation-threshold)
         ("w" . larumbe/uvm-copy-timestamp-vsim))
  :bind (:map comint-mode-map
         ("C-j" . larumbe/compilation-interactive-recompile)))


;;;; Package providing

(provide 'init-compilation)

;;; init-compilation.el ends here
