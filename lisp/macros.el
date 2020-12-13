;;; macros.el --- Macros & Elmacro  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Own macros for exwm Automation
;;
;; 1) Go to EXWM buffer
;; 2) F3 (start recording macro)
;; 3) record macro
;; 4) F4 (stop recording macro)
;; 5) M-x kmacro-name-last-macro
;; 6) insert-kbd-macro
;; 7) Assign into a function/keystroke
;;
;;
;; For elmacro:
;;   - Record Macro
;;   - elmacro-show-last-macro
;;   - copy/use it as desired!
;;
;; https://emacs.stackexchange.com/questions/70/how-to-save-a-keyboard-macro-as-a-lisp-function
;;
;;; Code:

(require 'elmacro)

;; Recorded from insert-kbd-macro
(fset 'open-google
   [?\C-g ?\C-l ?w ?w ?w ?. ?g ?o ?o ?g ?l ?e ?. ?c ?o ?m return return])

(defun larumbe/exwm-firefox-open-search-engine ()
  "Script for opening a search engine in an EXWM buffer."
  (interactive)
  (start-process-shell-command "firefox" nil "firefox")
  (sleep-for 1)
  (switch-to-buffer "Firefox-esr")
  ;; https://stackoverflow.com/questions/28039958/emacs-call-a-kbd-macro-in-defun-function
  (execute-kbd-macro 'open-google)) ; open-google is not a function but a macro, so it needs to be executed this way


(fset 'copy-firefox-link
   [?\C-l ?\M-w ?\C-g])


(defun larumbe/exwm-firefox-youtube-dl ()
  "Download MP3 from current's Firefox window link.
Use `C-w' instead of `M-w' to check that link is being killed properly."
  (interactive)
  (let ((link)
        (dir "~/youtube-dl-mp3"))
    (save-window-excursion
      (switch-to-buffer "Firefox")
      ;; https://stackoverflow.com/questions/28039958/emacs-call-a-kbd-macro-in-defun-function
      (execute-kbd-macro 'copy-firefox-link)
      (setq link (current-kill 0))
      (setq dir "")
      (async-shell-command
       (concat
        "mkdir -p " dir " && "
        "cd " dir " && "
        "youtube-dl --extract-audio --audio-format mp3 "
               link)
       "*youtube-dl*"))))


;; DANGER: Legacy. Use only as a reference to create other macros!
(defun larumbe/show-svn-buffers-hp ()
  "Show SVN buffers."
  (interactive)
  (switch-to-buffer "*svn-update<metaljf>*")
  (delete-other-windows)
  (split-window-below nil)
  (split-window-right nil)
  (split-window-right nil)
  (universal-argument)
  (digit-argument
   `(4))
  (digit-argument 1)
  (enlarge-window-horizontally 15)
  (other-window 1)
  (universal-argument)
  (digit-argument
   `(4))
  (digit-argument 1)
  (enlarge-window-horizontally 15)
  (universal-argument)
  (digit-argument
   `(4))
  (digit-argument 1)
  (enlarge-window-horizontally 15)
  (other-window 1)
  (other-window 1)
  (split-window-below nil)
  (other-window 1)
  (delete-window)
  (split-window-right nil)
  (other-window 1)
  (switch-to-buffer "*svn-update<lamarr>*")
  (other-window 1)
  (switch-to-buffer "*svn-update<asterix>*")
  (other-window 1)
  (switch-to-buffer "*svn-update<smc>*")
  (other-window 1)
  (switch-to-buffer "*svn-update<tools>*")
  (toggle-truncate-lines nil)
  (other-window 1)
  (toggle-truncate-lines nil)
  (other-window 1)
  (toggle-truncate-lines nil)
  (other-window 1)
  (toggle-truncate-lines nil)
  (other-window 1)
  (toggle-truncate-lines nil)
  (other-window 1)
  (other-window 1))


;; DANGER: Legacy. Use only as a reference to create other macros!
(defun larumbe/show-repo-sync-buffers ()
  "Show repo buffers."
  (interactive)
  (setq last-command-event 49)
  (delete-other-windows)
  (switch-to-buffer "*<git_metaljf>*" nil 'force-same-window)
  (split-window-right nil)
  (split-window-below nil)
  (handle-focus-out
   `(focus-out ,(elmacro-get-frame "0x6cabe70")))
  (other-window 1)
  (handle-focus-in
   `(focus-in ,(elmacro-get-frame "0x6cabe70")))
  (switch-to-buffer "*<git_smc_metaljf>*" nil 'force-same-window)
  (insert "g")
  (delete-char 1 nil)
  (handle-focus-out
   `(focus-out ,(elmacro-get-frame "0x6cabe70")))
  (other-window 1)
  (handle-focus-in
   `(focus-in ,(elmacro-get-frame "0x6cabe70")))
  (split-window-below nil)
  (switch-to-buffer "*<git_metaljf_integration>*" nil 'force-same-window)
  (handle-focus-out
   `(focus-out ,(elmacro-get-frame "0x6cabe70")))
  (other-window 1)
  (handle-focus-in
   `(focus-in ,(elmacro-get-frame "0x6cabe70")))
  (switch-to-buffer "*<git_lamarr>*" nil 'force-same-window))


(defun larumbe/kill-repo-sync-buffers ()
  "Kill repo buffers."
  (interactive)
  (handle-focus-out
   `(focus-out ,(elmacro-get-frame "0x6cabe70")))
  (larumbe/kill-current-buffer)
  (handle-focus-in
   `(focus-in ,(elmacro-get-frame "0x6cabe70")))
  (delete-window)
  (handle-focus-out
   `(focus-out ,(elmacro-get-frame "0x6cabe70")))
  (larumbe/kill-current-buffer)
  (handle-focus-in
   `(focus-in ,(elmacro-get-frame "0x6cabe70")))
  (delete-window)
  (handle-focus-out
   `(focus-out ,(elmacro-get-frame "0x6cabe70")))
  (setq last-command-event 134217767)
  (larumbe/kill-current-buffer)
  (setq last-command-event 134217767)
  (handle-focus-in
   `(focus-in ,(elmacro-get-frame "0x6cabe70")))
  (delete-window)
  (handle-focus-out
   `(focus-out ,(elmacro-get-frame "0x6cabe70")))
  (setq last-command-event 134217767)
  (larumbe/kill-current-buffer)
  (setq last-command-event 134217767)
  (handle-focus-in
   `(focus-in ,(elmacro-get-frame "0x6cabe70")))
  (setq last-command-event 'f4))


(defun larumbe/show-buffers-rr-ansi-term ()
  "Show rr ansi term buffers."
  (interactive)
  (delete-other-windows)
  (switch-to-buffer "*tetra*")
  (split-window-right nil)
  (other-window 1)
  (split-window-below nil)
  (switch-to-buffer "*microtron*")
  (other-window 1)
  (switch-to-buffer "*microtron--mct*")
  (other-window 1))


(defun larumbe/kill-buffers-rr-ansi-term ()
  "Kill rr ansi term buffers."
  (interactive)
  (set-process-query-on-exit-flag (get-process "*tetra*") nil)
  (kill-buffer "*tetra*")
  (set-process-query-on-exit-flag (get-process "*microtron--mct*") nil)
  (kill-buffer "*microtron--mct*")
  (set-process-query-on-exit-flag (get-process "*microtron*") nil)
  (kill-buffer "*microtron*")
  (delete-other-windows))



(provide 'macros)

;;; macros.el ends here
