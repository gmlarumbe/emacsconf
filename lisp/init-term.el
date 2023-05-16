;;; init-term.el --- Terminals  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; At some point these packages/links showed up while looking at ways to have a fully colorized terminal:
;;
;; - https://emacs.stackexchange.com/questions/24784/getting-more-than-8-colors-in-a-terminal-emulator-inside-emacs
;;    - However, `less' and `bat' didn't seem to work even after 'export TERM=eterm-256color'
;;
;; - https://github.com/atomontage/xterm-color
;;    - Propertize comint, eshell, compilation and other buffers
;;
;; - eterm-256color (use-package eterm-256color :hook (term-mode . eterm-256color-mode))
;;    - However didn't seem to fix the mess with term/ansi-term own colors and the ones provided by the package
;;
;; The best solution was to use a fully-fledge emulator: vterm
;;
;;; Code:

(use-package term
  :bind (:map term-raw-map
         ("M-o" . other-window)
         ("C-u" . nil)
         ("M-'" . nil)
         ("M->" . end-of-buffer)
         ("M-<" . beginning-of-buffer)
         ("M-x" . counsel-M-x))
  :hook ((term-mode . larumbe/term-hook))
  :config
  (setq comint-process-echoes t)

  (defvar term-no-process-map
    (let ((map (make-keymap)))
      (define-key map "\C-d" 'term-delchar-or-maybe-eof)
      map))

  ;; INFO: These ones apply to `ansi-term', not to `vterm'
  (defun larumbe/term-sentinel (proc msg)
    "Function to advice `term-sentinel'.
This function unmaps local map and therefore it's not possible
to use `larumbe/term-delchar-or-maybe-eof' to kill the buffer
with `C-d', taking advantange of keystroke inertia."
    (use-local-map term-no-process-map))

  (defun larumbe/term-delchar-or-maybe-eof (arg)
    "Advice to kill term buffer if there's no process."
    (interactive "p")
    (unless (get-buffer-process (current-buffer))
      (kill-current-buffer)))

  (advice-add 'term-sentinel :after #'larumbe/term-sentinel)
  (advice-add 'term-delchar-or-maybe-eof :before-until #'larumbe/term-delchar-or-maybe-eof)

  (defun larumbe/ansi-term-dwim ()
    "Check if there is an existing *ansi-term* buffer and pops to it.
If not visible open on the same window. Otherwise create it.

If prefix arg is provided, force creation of a new ansi-term."
    (interactive)
    (cond (current-prefix-arg
           (ansi-term "/bin/bash")
           (message "Spawning a new %s shell" (buffer-name)))
          (t
           (let ((buf "*ansi-term*"))
             (if (get-buffer buf)
                 (if (get-buffer-window buf)
                     (pop-to-buffer buf)
                   (switch-to-buffer buf))
               (ansi-term "/bin/bash"))))))

  (defun larumbe/term-hook ()
    "`term-hode' own hook"
    (interactive)
    (hardcore-mode -1)))



(use-package vterm
  :bind (:map vterm-mode-map
         ("C-c C-t" . nil) ; Remap `vterm-copy-mode' to C-c C-k
         ("C-c C-k" . vterm-copy-mode))
  :bind (:map vterm-copy-mode-map
         ("C-c C-t" . nil)
         ("C-c C-k" . vterm-copy-mode-done))
  :bind (("C-M-/" . vterm)) ; Unmap `dabbrev-completion'
  :init
  (setq vterm-keymap-exceptions '("C-c" "C-x" "C-u" "C-h" "C-l" "M-x" "M-O" "M-o" "C-y" "M-y")) ; Exclude C-g
  (setq vterm-shell "zsh")

  (defun larumbe/sh-send-string-vterm (string)
    "Send STRING to *vterm* process."
    (interactive)
    (let* ((buf "*vterm*")
           (proc (get-buffer-process buf)))
      (unless (get-buffer buf)
        (error "Buffer %s does not exist" buffer))
      (process-send-string proc string))))


(use-package aweshell
  :straight (:host github :repo "manateelazycat/aweshell")
  :bind (("C-x C-M-/" . larumbe/aweshell-dwim))
  :bind (:map eshell-mode-map
         ("C-d" . larumbe/aweshell-delchar-or-eof))
  :init
  (setq aweshell-search-history-key "C-r")
  :config
  (setq eshell-visual-subcommands '(("git" "log" "diff" "show")))

  ;; TODO: Tweak the ls commands
  ;; TODO: Remove the aliases (ls is an internal elisp command, the aliases break everything)

  ;; INFO: Plan9 style shell (eshell related things)
  (require 'em-smart)
  (eshell-smart-initialize)

  (defun larumbe/aweshell-delchar-or-eof (arg)
    "Delete ARG characters forward, or send an EOF to process if at end of buffer."
    (interactive "p")
    (let ((buf (buffer-name)))
      (if (save-excursion
            (eshell-bol)
            (eobp))
          (progn
            (kill-current-buffer)
            (message "Killed %s" buf))
        (delete-char arg))))

  (defun larumbe/aweshell-dwim ()
    "Check if there is an existing aweshell buffer and pops to it.
If not visible open on the same window. Otherwise create it.

If prefix arg is provided, force creation of a new aweshell."
    (interactive)
    (cond (current-prefix-arg
           (aweshell-new)
           (message "Spawning a new %s shell" (buffer-name)))
          (t
           (let ((buf (car aweshell-buffer-list)))
             (if (and buf
                      (get-buffer buf))
                 (if (get-buffer-window buf)
                     (pop-to-buffer buf)
                   (switch-to-buffer buf))
               (aweshell-new))))))

  ;; TODO: Fork/send PR at some point:
  ;;   Right now uses ido, (change of 2018) If setting back to `completing-read'
  ;;   it would use ivy out-of-the-box, or even helm or whatever backend
  ;;   overrides the `completing-read-function'
  (defun aweshell-search-history ()
    "Interactive search eshell history."
    (interactive)
    (save-excursion
      (let* ((start-pos (eshell-beginning-of-input))
             (input (eshell-get-old-input))
             (all-shell-history (aweshell-parse-shell-history)))
        (let* ((command (completing-read "Search history: " all-shell-history)))
          (eshell-kill-input)
          (insert command)
          )))
    ;; move cursor to eol
    (end-of-line)))


(provide 'init-term)

;;; init-term.el ends here
