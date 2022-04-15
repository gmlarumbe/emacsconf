;;; verilog-beautify.el --- Verilog Beautify  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Code beautifying
(defun larumbe/verilog-align-ports-current-module ()
  "Align parenthesis ports of current module.
Current module is the one pointed to by `modi/verilog-find-module-instance'.

Alignment is performed between instance name and end of instantiation."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module)
        (current-instance)
        (beg)
        (end)
        (re-beg-pos)
        (re-end-pos))
    (setq current-module modi/verilog-which-func-xtra)
    (setq current-instance (modi/verilog-find-module-instance))
    (save-excursion
      (setq re-beg-pos (re-search-backward (concat "\\_<" current-instance "\\_>") nil t))
      (forward-line) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq re-end-pos (re-search-forward ");" nil t))
      (setq end re-end-pos))
    (if (and re-beg-pos re-end-pos)
        (progn
          (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
          (message "Ports of %s aligned..." current-module))
      (message "Could not align ports!"))))


(defun larumbe/verilog-align-parameters-current-module (&optional module)
  "Align parameters of current module, the one pointed to by `which-func'.

Alignment is performed between module name and instance name.

If used programatically perform a backwards regexp-search of MODULE
and start indentation at that point.
This is because current-module is determined by `which-func' and it takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module)
        (current-instance)
        (beg)
        (end)
        (re-beg-pos)
        (re-end-pos))
    (setq current-instance (modi/verilog-find-module-instance))
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (setq re-beg-pos (re-search-backward (concat "\\_<" current-module "\\_>") nil t))
      (forward-line) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (when current-instance
        (setq re-end-pos (re-search-forward current-instance nil t)))
      (setq end re-end-pos))
    (if (and re-beg-pos re-end-pos)
        (progn
          (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
          (message "Parameters of %s  aligned..." current-module))
      (message "Could not align parameters!"))))


(defun larumbe/verilog-indent-current-module (&optional module)
  "Indent current module, the one pointed to by `which-func'.

If used programatically perform a backwards regexp-search of MODULE
and start indentation at that point.
This is because current-module is determined by `which-func' and it takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module)
        (re-beg-pos)
        (re-end-pos)))
  (if module
      (setq current-module module)
    (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
  (save-excursion
    (setq re-beg-pos (re-search-backward (concat "\\_<" current-module "\\_>") nil t))
    (beginning-of-line)
    (setq re-end-pos (re-search-forward larumbe/verilog-module-instance-re nil t)))
  (if (and re-beg-pos re-end-pos)
      (save-excursion
        (goto-char re-beg-pos)
        (beginning-of-line)
        (set-mark (point))
        (goto-char re-end-pos)
        (backward-char)                 ; Point at instance opening parenthesis
        (electric-verilog-forward-sexp) ; Point at instance closing parenthesis
        (end-of-line)
        (electric-verilog-tab)
        (message "Indented %s" current-module))
    (message "Point is not inside a module instantiation")))


(defun larumbe/verilog-beautify-current-module ()
  "Beautify current module (open parenthesis, indent and align)."
  (interactive)
  (save-excursion
    ;; Leave indentation for the end to avoid conflicts with
    ;; point position due to update delay in which-func
    (larumbe/verilog-align-ports-current-module)
    (larumbe/verilog-align-parameters-current-module)
    (larumbe/verilog-indent-current-module)))


(defun larumbe/verilog-beautify-current-buffer ()
  "Beautify current buffer.

Indent whole buffer, beautify every instantiated module and
remove blanks in port connections."
  (interactive)
  (save-excursion
    (indent-region (point-min) (point-max))
    (larumbe/verilog-clean-port-blanks)
    (goto-char (point-min))
    (while (larumbe/find-verilog-module-instance-fwd)
      (larumbe/verilog-beautify-current-module))))


(defun larumbe/verilog-beautify-files (files)
  "Beautify Verilog FILES.

FILES is a list of strings containing the paths to the files to beautify."
  (dolist (file files)
    (unless (file-exists-p file)
      (error "File %s does not exist! Aborting..." file)))
  (dolist (file files)
    (with-temp-file file
      (verilog-mode)
      (insert-file-contents file)
      (larumbe/verilog-beautify-current-buffer)
      (untabify-trailing-whitespace)
      (write-file file))))


(defun larumbe/verilog-beautify-files-current-dir ()
  "Beautify Verilog files on current dired directory."
  (interactive)
  (unless (string= major-mode "dired-mode")
    (error "Must be used in dired!"))
  (let ((files (directory-files-recursively default-directory "\\.[s]?v[h]?$")))
    (larumbe/verilog-beautify-files files)))



(provide 'verilog-beautify)

;;; verilog-beautify.el ends here
