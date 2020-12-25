;;; unison-sync-minor-mode.el --- Unison Sync Minor mode  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Basic info
;; Minor Mode created by Larumbe for Local/Remote unison synchronization
;; Fetched from: http://nullprogram.com/blog/2013/02/06/
;;
;; By default, every time a file is visited again, unison-sync-minor-mode will be disabled
;; Therefore, it must be enabled manually (no shortcut) and the first synchronization
;; requires selecting a profile available at '~/.unison/'.
;; Do not forget to SYNC manually at the beginning with the `unison-manually-sync-projects'!!!
;;
;;;; Merging with unison:
;; Merging was very tricky to set up since emacsclient coordination with server required 'unison' to wait for emacsclient's merge.
;; Afterwards unison would update both sides. However, if the merge option uses only emacsclient --eval parameters, it returns immediately (before merge has been done) and unison triggers and error.
;; Using 'emacsclient -c' option makes unison wait for emacs, but (maybe because of EXWM) after killing that new frame no finish signal is sent back to unison.
;; Therefore, the only workaround is to make a script that waits until merge file is created/updated after ediff and then synchronized.
;; INFO: https://superuser.com/questions/81958/how-to-make-emacsclient-wait-when-using-the-eval-option/81980
;;
;;;; Integration with EXWM
;; Be careful to override unison-run command to use start-process instead of EXWM blocking shell-command.
;;
;;; Code


;;;; Variables and profiles
(make-variable-buffer-local (defvar unison-active-profile nil))
(defvar larumbe/unison-show-process-window nil)
(defvar larumbe/unison-sync-hook-active nil)
(defvar larumbe/unison-folder "/home/martigon/.unison/")
(defvar larumbe/unison-buffer "*unison*")
(defvar larumbe/unison-command-name "unison")


(defun unison-set-active-profile ()
  "Set active profile after checking availability at previously set unison folder"
  (interactive)
  (setq unison-active-profile (completing-read "Select profile: " (directory-files larumbe/unison-folder nil ".*\.prf$"))))


;;;; Aux functions
(defun unison-toggle-enable-process-window ()
  "Toggle activation of process window when running Unison"
  (interactive)
  (if (not (bound-and-true-p larumbe/unison-show-process-window))
      (progn
        (setq larumbe/unison-show-process-window t)
        (message "Show %s buffer enabled" larumbe/unison-buffer))
    (setq larumbe/unison-show-process-window nil)
    (message "Show %s buffer disabled" larumbe/unison-buffer)))


(defun unison-show-process-window ()
  "Show unison buffer in a window to check sync progress"
  (interactive)
  (popwin:pop-to-buffer larumbe/unison-buffer t)
  (view-mode t)
  (setq truncate-lines t)
  (end-of-buffer))


(defun unison-pop-show-unison-buffer ()
  "Pop to unison buffer if not visible, and select it if visible"
  (interactive)
  (if (not (get-buffer-window larumbe/unison-buffer))
      (progn
        (popwin:pop-to-buffer larumbe/unison-buffer)
        (enlarge-window 10)
        (view-mode t)
        (setq truncate-lines t)
        (end-of-buffer))
    (select-window (get-buffer-window larumbe/unison-buffer))
    (view-mode t)
    (setq truncate-lines t)
    (end-of-buffer)))


(defun unison-sentinel-finished (process signal)
  "Check whether unison process has already finished.
Reference: http://nic.ferrier.me.uk/blog/2011_10/emacs_lisp_is_good_further_reports_suggest"
  (cond
   ((equal signal "finished\n")
    (message "Synchronization successful"))
   ('t
    (message "Unison process open message got signal %s" signal)
    (display-buffer (process-buffer process)))))


;;;; Run program functions
(defun unison-my-run ()
  "Run an instance of Unison.
If opening a prf conf file, the update will be over that file.
Otherwise, it will depend on buffer local selected profile."
  (interactive)
  (let (proc)
    (when (string-equal (file-name-extension (buffer-file-name)) "prf")
      (setq unison-active-profile (file-relative-name (buffer-file-name))))
    (unless (bound-and-true-p unison-active-profile)
      (unison-set-active-profile))
    (setq proc (start-process larumbe/unison-buffer larumbe/unison-buffer larumbe/unison-command-name unison-active-profile "-auto" "-batch"))
    (message "Synchronizing...")
    (when (bound-and-true-p larumbe/unison-show-process-window)
      (unison-show-process-window))
    (set-process-sentinel proc 'unison-sentinel-finished)))


(defun unison-manually-sync-projects (&optional prompt)
  "Sometimes, when files are identical but have different timestamps/permissions unison will detect it and will skip them.
Manually sync them will allow for a proper output at unison buffer.
User will have to choose which of the repos has priority on the synchronization"
  (interactive "P")
  (unless (bound-and-true-p unison-active-profile)
    (setq unison-active-profile (file-name-nondirectory (buffer-file-name))))
  (let (local remote choice)
    (save-window-excursion
      ;; Get sync folders from active profile
      (find-file (concat larumbe/unison-folder unison-active-profile))
      (switch-to-buffer unison-active-profile)
      ;; Get Local
      (beginning-of-buffer)
      (re-search-forward "^root=/home")
      (backward-char 5)
      (setq local (buffer-substring (point) (progn (end-of-line) (point))))
      ;; Get remote
      (beginning-of-buffer)
      (re-search-forward "^root=ssh://")
      (backward-char 6)
      (setq remote (thing-at-point 'url t))
      (setq choice local)               ; Default local
      ;; Prompt for remote/local precedence and invoke a different process depending on which has precedence
      (when prompt
        (if (y-or-n-p "Override with remote's data? [y->remote] [n->local]")
            (setq choice remote)
          (setq choice local)))
      (start-process larumbe/unison-buffer larumbe/unison-buffer larumbe/unison-command-name unison-active-profile "-auto" "-batch" "-force" choice))))


;;;; Pending
;; TODO: https://emacs.stackexchange.com/questions/12374/make-shell-command-async-shell-command-respect-carriage-return
;; Meanwhile...
;; Function to avoid visualizing so many annoying `^M' during the file transmission.
;; Trick is to set encoding/decoding to utf-8
;; /usr/share/emacs/25.1/lisp/international/mule.el.gz:1520
;; FIXME: It did not work to use this function at the end of `unison-my-run' to automate it more
(defun set-unison-process-coding-system (&optional silent)
  "Set coding systems for the unison buffer"
  (interactive)
  (let ((proc (get-buffer-process larumbe/unison-buffer))
        (decoding 'utf-8)
        (encoding 'utf-8))
    (if (null proc)
        (error "No process")
      (check-coding-system decoding)
      (check-coding-system encoding)
      (set-process-coding-system proc decoding encoding)
      (unless silent
        (message "Set decoding/encoding system: %s/%s" decoding encoding))))
  (force-mode-line-update))


;; Fetched from: https://stackoverflow.com/questions/6138029/how-to-add-a-hook-to-only-run-in-a-particular-mode
(defun unison-sync-save-hook ()
  (unison-my-run))


;; TODO: Still does not work properly...
;; This function properly adds/clears hooks on unison-sync-minor-mode-hook
;; It also adds/clears hooks on after-save-hook with the C-c C-s keyshortcut
;; But effect does not take place until buffer is revisited. That might be Emacs normal behaviour?
(defun unison-toggle-sync-save-hook ()
  "Toggle sync save hook for current file."
  (interactive)
  (if larumbe/unison-sync-hook-active
      (progn
        (remove-hook 'after-save-hook 'unison-sync-save-hook)
        ;; (remove-hook 'write-file-functions 'unison-sync-save-hook)
        (remove-hook 'unison-sync-minor-mode-hook
                     (lambda ()
                       (add-hook 'after-save-hook 'unison-sync-save-hook nil 'make-it-local)))
        ;; (remove-hook 'unison-sync-minor-mode-hook
        ;;              (lambda ()
        ;;                (add-hook 'write-file-functions 'unison-sync-save-hook nil 'make-it-local)))
        (setq larumbe/unison-sync-hook-active nil)
        (message "Unison save-sync disabled..."))
    ;; Not active
    (add-hook 'unison-sync-minor-mode-hook
              (lambda ()
                (add-hook 'after-save-hook 'unison-sync-save-hook nil 'make-it-local)))
    ;; (add-hook 'unison-sync-minor-mode-hook
    ;;           (lambda ()
    ;;             (add-hook 'write-file-functions 'unison-sync-save-hook nil 'make-it-local)))
    (setq larumbe/unison-sync-hook-active t)
    (message "Unison save-sync enabled!")))




;;;; Keymap
;;;###autoload
(define-minor-mode unison-sync-minor-mode
  "Frontend for unison synchronization between machines."
  :lighter " [U]"
  :keymap
  '(
    ;; ("\C-c\C-s" . unison-toggle-sync-save-hook)
    ("\C-c\C-c" . unison-my-run)
    ("\C-c\C-v" . unison-toggle-enable-process-window)
    ("\C-c\C-b" . unison-pop-show-unison-buffer)
    ("\C-c\C-z" . unison-manually-sync-projects))
  ;; Customizations
  (add-to-list 'popwin:special-display-config '("*unison*" :stick t)))


;;;; Provide
(provide 'unison-sync-minor-mode)

;;; unison-sync-minor-mode.el ends here
