;;; init-elfeed.el --- Elfeed  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package elfeed
  :demand
  :init
  (setq elfeed-feeds '(("https://www.reddit.com/r/Emacs/new/.rss"   emacs)
                       ("https://www.reddit.com/r/FPGA/new/.rss"    fpga)
                       ("https://www.reddit.com/r/Verilog/new/.rss" verilog)
                       ("https://www.reddit.com/r/VHDL/new/.rss"    vhdl)))
  ;; (setq elfeed-search-filter)
  (defvar larumbe/reddit-alert-keywords
    '(("Emacs"   . ("verilog" "systemverilog" "vhdl" "tree-sitter-systemverilog" "tree-sitter-verilog" "tree-sitter-vhdl" "fpga" "asic"))
      ("FPGA"    . ("IDE" "editor" "Emacs" "tree-sitter"))
      ("Verilog" . ("IDE" "editor" "Emacs" "tree-sitter"))
      ("VHDL"    . ("IDE" "editor" "Emacs" "tree-sitter"))))
  (defvar larumbe/reddit-alert-keywords-regexps
    (mapcar (lambda (feed)
              (cons (car feed) (list (regexp-opt (cdr feed) 'words))))
            larumbe/reddit-alert-keywords))
  ;; Variables
  (defvar larumbe/reddit-alert-user-name)
  (defvar larumbe/reddit-alert-from-email)
  (defvar larumbe/reddit-alert-to-email)

  :config
  (defun larumbe/reddit-alert-send-email (subject body)
    (let* ((user-full-name larumbe/reddit-alert-user-name)
           (user-mail-address larumbe/reddit-alert-from-email)
           (sendmail-program (executable-find "msmtp"))
           (buffer (get-buffer-create "*elfeed-reddit-fpga*"))
           proc proc-in)
      (unless sendmail-program
        (error "Couldn't find msmtp in PATH"))
      (setq proc (make-process
                  :name "sendmail-reddit"
                  :buffer buffer
                  :command (list sendmail-program "-t" "-i")
                  :connection-type 'pipe
                  :sentinel
                  (lambda (process event)
                    (when (memq (process-status process) '(exit signal))
                      (message "sendmail finished: %s (status %d)"
                               (string-trim event)
                               (process-exit-status process))))))
      (process-send-string
       proc
       (concat "From: " larumbe/reddit-alert-user-name " <" larumbe/reddit-alert-from-email ">\n"
               "To: " larumbe/reddit-alert-to-email "\n"
               "Subject: " subject "\n"
               "\n"
               body))
      ;; Close stdin so sendmail processes the message
      (process-send-eof proc)))

  (defun larumbe/reddit-alert-hook (entry)
    (let* ((title (elfeed-entry-title entry))
           (link  (elfeed-entry-link entry))
           (feed  (elfeed-deref (elfeed-entry-feed entry)))
           (url   (elfeed-feed-url feed))
           my-feed)
      ;; Match subreddit
      (dolist (feed-elm (mapcar #'car larumbe/reddit-alert-keywords-regexps))
        (when (string-match-p feed-elm url)
          (setq my-feed feed-elm)))
      (when my-feed
        (message "my-feed=%s" my-feed)
        (message "URL=%s" url)
        ;; Match keywords
        (when (string-match-p (cadr (assoc my-feed larumbe/reddit-alert-keywords-regexps)) title)
          (larumbe/reddit-alert-send-email
           (format "[Reddit] %s" title)
           (format
            "Feed: %s\n\nTitle:\n%s\n\nLink:\n%s\n"
            url
            title
            link))
          (message "Reddit alert: %s" title)))))

  (add-hook 'elfeed-new-entry-hook #'larumbe/reddit-alert-hook)
  (run-at-time nil (* 5 60) #'elfeed-update))

(provide 'init-elfeed)

;;; init-elfeed.el ends here
