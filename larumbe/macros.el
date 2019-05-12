;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; OWN MACROS FOR EXWM Automation      ;;
;; 1) Go to EXWM buffer                ;;
;; 2) F3 (start recording macro)       ;;
;; 3) record macro                     ;;
;; 4) F4 (stop recording macro)        ;;
;; 5) M-x kmacro-name-last-macro       ;;
;; 6) insert-kbd-macro                 ;;
;; 7) Assign into a function/keystroke ;;
;;                                     ;;
;;                                     ;;
;; For elmacro:                        ;;
;;   - Record Macro                    ;;
;;   - elmacro-show-last-macro         ;;
;;   - copy/use it as desired!         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; https://emacs.stackexchange.com/questions/70/how-to-save-a-keyboard-macro-as-a-lisp-function

;; Recorded from insert-kbd-macro
(fset 'open-google
   [?\C-g ?\C-l ?w ?w ?w ?. ?g ?o ?o ?g ?l ?e ?. ?c ?o ?m return return])

(defun larumbe/exwm-firefox-open-search-engine ()
  "Script for opening a search engine in an EXWM buffer"
  (interactive)
  (start-process-shell-command "firefox" nil "firefox")
  (sleep-for 1)
  (switch-to-buffer "Firefox-esr")
  ;; https://stackoverflow.com/questions/28039958/emacs-call-a-kbd-macro-in-defun-function
  (execute-kbd-macro 'open-google) ; open-google is not a function but a macro, so it needs to be executed this way
)


(fset 'copy-firefox-link
   [?\C-l ?\C-w])


(defun larumbe/exwm-firefox-youtube-dl ()
  "Download MP3 from current's Firefox window link. Use `C-w' instead of `M-w' to check that link is being killed properly"
  (interactive)
  (let (link dir)
    (save-window-excursion
      (switch-to-buffer "Firefox-esr")
      ;; https://stackoverflow.com/questions/28039958/emacs-call-a-kbd-macro-in-defun-function
      (execute-kbd-macro 'copy-firefox-link)
      (setq link (current-kill 0))
      (setq dir larumbe/youtube-dl-download-folder)
      (async-shell-command
       (concat
        "mkdir -p " dir " && "
        "cd " dir " && "
        "youtube-dl --extract-audio --audio-format mp3 "
               link)
       "*youtube-dl*"))))


(defun larumbe/show-svn-buffers-hp ()
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



(defun larumbe/verilog-clean-parenthesis-blanks ()
  "Cleans blanks inside parenthesis blocks (Verilog port connections).
If region is not used, then a query replacement is performed instead"
  (interactive)
  (let ((old-start "([ ]+\\(.*\\))")
        (new-start "(\\1)")
        (old-end "[ ]+)")
        (new-end ")"))
    (if (use-region-p)
        (progn
          (message "Removing blanks at the beginning...")
          (replace-regexp old-start new-start nil (region-beginning) (region-end))
          (replace-regexp old-end   new-end   nil (region-beginning) (region-end)))
      (progn
        (message "Removing blanks at the end...")
        (query-replace-regexp old-start new-start nil (point-min) (point-max))
        (query-replace-regexp old-end   new-end   nil (point-min) (point-max))))))

