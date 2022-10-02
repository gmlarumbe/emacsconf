;;; verilog-beautify.el --- Verilog Beautify  -*- lexical-binding: t -*-
;;; Commentary:
;;
;;; Code:


;;;; Code beautifying
(defun verilog-ext-module-at-point--align (thing)
  "Align THING of current module (ports/parameters)."
  (let ((case-fold-search nil)
        (re "\\(\\s-*\\)(")
        (current-ids (verilog-ext-instance-at-point))
        (idx (cond ((eq thing 'parameters) 1)
                   ((eq thing 'ports) 2)
                   (t (error "Invalid thing to align"))))
        current-module beg end)
    (unless current-ids
      (user-error "Not inside an instance!"))
    (setq current-module (car current-ids))
    (save-excursion
      (goto-char (match-beginning idx))
      (verilog-re-search-forward "(" nil t)
      (verilog-forward-syntactic-ws)
      (setq beg (point))
      (verilog-backward-up-list -1)
      (backward-char)
      (verilog-backward-syntactic-ws)
      (setq end (point)))
    (align-regexp beg end re 1 1 nil)
    (if (eq idx 1)
        (message "Parameters of %s aligned..." current-module)
      (message "Ports of %s aligned..." current-module))))


(defun verilog-ext-module-at-point-align-ports ()
  "Align parenthesis ports of current module."
  (interactive)
  (verilog-ext-module-at-point--align 'ports))


(defun verilog-ext-module-at-point-align-params ()
  "Align parameters of current module."
  (interactive)
  (verilog-ext-module-at-point--align 'parameters))


(defun verilog-ext-module-at-point-indent ()
  "Indent current module."
  (interactive)
  (let ((case-fold-search nil)
        (current-ids (verilog-ext-instance-at-point))
        current-module beg end)
    (unless current-ids
      (user-error "Not inside an instance!"))
    (setq current-module (car current-ids))
    (save-excursion
      (goto-char (match-beginning 0))
      (beginning-of-line)
      (setq beg (point))
      (goto-char (match-end 0))
      (end-of-line)
      (setq end (point)))
    (indent-region beg end)
    (message "Indented %s" current-module)))


(defun verilog-ext-module-at-point-beautify ()
  "Beautify current module: indent, align ports and parameters."
  (interactive)
  (save-excursion
    (verilog-ext-module-at-point-indent)
    (verilog-ext-module-at-point-align-ports)
    (verilog-ext-module-at-point-align-params)))



(defun verilog-ext-beautify-current-file ()
  "Beautify current buffer:
- Indent whole buffer
- Beautify every instantiated module"
  (interactive)
  (save-excursion
    (indent-region (point-min) (point-max))
    (goto-char (point-min))
    (while (verilog-ext-find-module-instance-fwd)
      (verilog-ext-beautify-module-at-point))))


(defun verilog-ext-beautify-files (files)
  "Beautify Verilog FILES.

FILES is a list of strings containing the files paths."
  (dolist (file files)
    (unless (file-exists-p file)
      (error "File %s does not exist! Aborting..." file)))
  (dolist (file files)
    (with-temp-file file
      (verilog-mode)
      (insert-file-contents file)
      (verilog-ext-beautify-current-file)
      (untabify (point-min) (point-max))
      (delete-trailing-whitespace (point-min) (point-max))
      (write-file file))))


(defun verilog-ext-beautify-files-current-dir ()
  "Beautify Verilog files on current dired directory."
  (interactive)
  (unless (string= major-mode "dired-mode")
    (error "Must be used in dired!"))
  (let ((files (directory-files-recursively default-directory "\\.[s]?v[h]?$")))
    (verilog-ext-beautify-files files)))



(provide 'verilog-beautify)

;;; verilog-beautify.el ends here
