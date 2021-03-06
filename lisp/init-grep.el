;;; init-grep.el --- Grep/Silver Searcher/RipGrep  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Silver-searcher
(use-package ag
  :commands (ag/search
             larumbe/ag-search-file-list
             projectile-project-root)
  :config
  (defun larumbe/ag-search-file-list (regex file directory)
    "Search REGEX limited to the files included in FILE in DIRECTORY.
INFO: Might block Emacs for large filelists during search as it is not
asynchronous.

FILE is expected to be something of the format of gtags.files or similar,
i.e. one absolute file path per line"
    (let ((files))
      (with-temp-buffer
        (insert-file-contents file)
        (setq files (split-string (buffer-string) "\n")))
      (ag/search regex directory :files files)))


  (defun larumbe/ag-search-project-gtags ()
    "Search `symbol-at-point' based on current projectile project.
List of files provided by project's 'gtags.file' will filter the search."
    (interactive)
    (let* ((proj-dir   (projectile-project-root))
           (gtags-file (concat proj-dir "gtags.files")))
      (unless (file-exists-p gtags-file)
        (error "Error: gtags.files not found for current project"))
      (larumbe/ag-search-file-list (thing-at-point 'symbol) gtags-file
    proj-dir)))



  ;; Thanks to Kaushal Modi
  (defun ag/jump-to-result-if-only-one-match ()
    "Jump to the first ag result if that ag search came up with just one match."
    (let (only-one-match)
      (when (member "--stats" ag-arguments)
        (save-excursion
          (goto-char (point-min))
          (setq only-one-match (re-search-forward "^1 matches\\s-*$" nil :noerror)))
        (when only-one-match
          (next-error)
          (kill-buffer (current-buffer))
          (message (concat "ag: Jumping to the only found match and "
                           "killing the *ag* buffer."))))))


  ;; wgrep-ag
  ;; Allow editing in *ag* buffers
  ;; https://github.com/mhayashi1120/Emacs-wgrep
  (use-package wgrep-ag
    :config
    (add-hook 'ag-mode-hook #'wgrep-ag-setup)
    :bind (:map wgrep-mode-map
                ("C-x s" . wgrep-save-all-buffers)))


;;;;; Config
  (setq ag-arguments           ; Fetched from modi verilog config
        '("--nogroup"          ; mandatory argument for ag.el as per https://github.com/Wilfred/ag.el/issues/41
          "--skip-vcs-ignores" ; Ignore files/dirs ONLY from `.ignore'
          "--numbers"          ; Line numbers
          "--smart-case"
          "--follow"           ; Follow symlinks
          "--ignore" "#*#"     ; Adding "*#*#" or "#*#" to .ignore does not work for ag (works for rg)
          "--ignore" "*~"
          "--stats"))
  (setq ag-reuse-buffers t)
  (setq ag-reuse-window t)
  (setq ag-highlight-search t)
  (add-hook 'ag-search-finished-hook #'ag/jump-to-result-if-only-one-match))



;;;; RipGrep
(use-package ripgrep)

(use-package deadgrep)

;; INFO: Even though these two packages are downloaded,
;; `helm-rg' and `helm-projectile-rg' seem to be just enough


(provide 'init-grep)

;;; init-grep.el ends here
