;;; ag-settings.el --- Silver Searcher  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package ag
  :defines (ag-arguments)
  :commands (ag/search
             larumbe/ag-search-file-list
             projectile-project-root)
  :config
  (setq ag-arguments           ; Fetched from modi verilog config
        '("--nogroup"          ; mandatory argument for ag.el as per https://github.com/Wilfred/ag.el/issues/41
          "--skip-vcs-ignores" ; Ignore files/dirs ONLY from `.ignore'
          "--numbers"          ; Line numbers
          "--smart-case"
          ;; "--one-device"       ; Do not cross mounts when searching
          "--follow"           ; Follow symlinks
          "--ignore" "#*#"     ; Adding "*#*#" or "#*#" to .ignore does not work for ag (works for rg)
          "--ignore" "*~"
          "--stats"))
  (setq ag-reuse-buffers t)
  (setq ag-reuse-window t)

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
      (larumbe/ag-search-file-list (thing-at-point 'symbol) gtags-file proj-dir))))


(provide 'ag-settings)

;;; ag-settings.el ends here
