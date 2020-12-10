;;; verilog-indentation.el --- Verilog Indentation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;; Custom indentation/alignment and other functions
(defun larumbe/verilog-indent-current-module (&optional module)
  "Indent current module, the one pointed to by `which-func' (not instant)

For use programatically, an argument needs to be specified as current-module is determined by `which-func' and that takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module))
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (re-search-backward (concat "\\_<" current-module "\\_>"))
      ;; Mark region for the whole module
      (beginning-of-line)
      (set-mark (point))
      (re-search-forward larumbe/verilog-module-instance-re nil t)
      (backward-char)                            ; Point at instance opening parenthesis
      (electric-verilog-forward-sexp)            ; Point at instance closing parenthesis
      (end-of-line)
      (electric-verilog-tab))))


(defun larumbe/verilog-align-parameters-current-module (&optional module)
  "Align parenthesis PARAMETERS of current module, the one pointed to by `which-func' (not instant).
It will align parameters contained between module name and instance name.

For use programatically, an argument needs to be specified as current-module is determined by `which-func' and that takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-module)
        (current-instance)
        (beg)
        (end))
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (re-search-backward (concat "\\_<" current-module "\\_>"))
      (next-line 1) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward current-instance)))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Parameters aligned...")))


(defun larumbe/verilog-align-ports-current-module ()
  "Align parenthesis PORTS of current module, the one pointed to by `modi/verilog-find-module-instance'
It will only align ports, i.e., between instance name and end of instantiation."
  (interactive)
  (let ((case-fold-search verilog-case-fold)
        (current-instance)
        (beg)
        (end))
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (save-excursion
      (re-search-backward (concat "\\_<" current-instance "\\_>"))
      (next-line 1) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward ");")))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Ports aligned...")))


(defun larumbe/verilog-beautify-current-module ()
  "Beautify current module (open parenthesis +indent + align)"
  (interactive)
  (save-excursion
    (larumbe/verilog-indent-current-module)
    (larumbe/verilog-align-ports-current-module)
    (larumbe/verilog-align-parameters-current-module)))


(defvar larumbe/connect-disconnect-port-re "\\(?1:^\\s-*\\)\\.\\(?2:[a-zA-Z0-9_-]+\\)\\(?3:[[:blank:]]*\\)")
(defvar larumbe/connect-disconnect-conn-re "\\(?4:(\\(?5:.*\\))\\)?")
(defvar larumbe/connect-disconnect-not-found "No port detected at current line")

(defun larumbe/verilog-toggle-connect-port (force-connect)
  "Connect/disconnect port @ current line (regexp based).
If regexp detects that port is connected, then disconnect it. The other way round works the same.
If called with universal arg, `force-connect' parameter will force connection of current port, no matter it is connected/disconnected"
  (interactive "P")
  (let* ((case-fold-search verilog-case-fold)
         (port-regex larumbe/connect-disconnect-port-re)
         (conn-regex larumbe/connect-disconnect-conn-re)
         (line-regex (concat port-regex conn-regex))
         port conn sig
         (start (point)))
    ;; Find '.port (conn)' verilog regexp
    (beginning-of-line)
    (if (re-search-forward line-regex (point-at-eol) t)
        (progn
          (setq port (match-string-no-properties 2))
          (setq conn (match-string-no-properties 5))
          (if (or (string-equal conn "") force-connect) ; If it is disconnected or connection is forced via parameter...
              (progn ; Connect
                (setq sig (read-string (concat "Connect [" port "] to: ") port))
                (replace-match (concat "\\1.\\2\\3\(" sig "\)") t))
            (progn ; Else disconnect
              (replace-match (concat "\\1.\\2\\3\(" sig "\)") t)))
          (goto-char start)
          (next-line 1))
      (progn ; No port found
        (goto-char start)
        (message larumbe/connect-disconnect-not-found)))))


(defun larumbe/verilog-connect-ports-recursively ()
  "Ask recursively for ports to be connected until no port is found at current line"
  (interactive)
  (while (not (string-equal (larumbe/verilog-toggle-connect-port t) larumbe/connect-disconnect-not-found))))


(defun larumbe/verilog-def-logic (sig)
  "Replaces `verilog-sk-def-reg' for use within `larumbe/verilog-define-signal'"
  (let (width str)
    (split-line) ;; Keep indentation
    (setq width (larumbe/verilog-compute-vector-width))
    (setq str (concat "logic " width " " sig ";"))
    (insert str)
    (message (concat "[Line " (format "%s" (line-number-at-pos)) "]: " str))))


(defun larumbe/verilog-define-signal ()
  "INFO: Copied/modified from `verilog-mode.el' function: `verilog-sk-define-signal'.
There were some issues with this skeleton, an a function offers more flexibility.

Insert a definition of signal under point at top of module."
  (interactive "*")
  (let* ((sig-re "[a-zA-Z0-9_]*")
         (sig (buffer-substring
               (save-excursion
                 (skip-chars-backward sig-re)
                 (point))
               (save-excursion
                 (skip-chars-forward sig-re)
                 (point)))))
    (if (not (member sig verilog-keywords))
        (save-excursion
          (verilog-beg-of-defun)
          (verilog-end-of-statement)
          (verilog-forward-syntactic-ws)
          (larumbe/verilog-def-logic sig))
      (message "object at point (%s) is a keyword" sig))))



;; INFO: Global does not allow to find external definitions outside project root directory (probably due to security reasons).
;; In order to do so, there are 2 methods:
;;   - Use symbolic links to external directories.
;;   - Make use of GTAGSLIBPATH environment variable.
;; Associated thread: https://emacs.stackexchange.com/questions/13254/find-external-definition-with-gtags-or-ggtags
(defun larumbe/gtags-verilog-files-pwd-recursive (&optional exclude-re dir append)
  "Generate gtags.files for current directory, unless optional DIR is set.
If optional EXCLUDE-RE is set, delete paths with that regexp from generated file.
If DIR is not specified, use current-directory.
If APPEND is set, append directory files to already existing tags file. "
  (let (tags-dir)
    (if dir
        (setq tags-dir dir)
      (setq tags-dir default-directory))
    (larumbe/directory-files-recursively-to-file tags-dir "gtags.files" ".[s]?v[h]?$" append exclude-re)))


(defun larumbe/ggtags-create-verilog-tags-recursive ()
  "Create Verilog gtags.files for current directory.
Do not include SCons generated '*_targets' folders. "
  (interactive)
  (let ((exclude-re (concat (projectile-project-root) "[^/]+_targets")))
    (shell-command "touch GTAGS")
    (larumbe/gtags-verilog-files-pwd-recursive exclude-re)
    (ggtags-create-tags default-directory)))


(defun larumbe/verilog-clean-parenthesis-blanks ()
  "Cleans blanks inside parenthesis blocks (Verilog port connections).
If region is not used, then a query replacement is performed instead.
DANGER: It may wrongly detect some `old-end' regexp matches, but seems too complex for the effort..."
  (interactive)
  (let ((old-start "([ ]+\\(.*\\))")
        (new-start "(\\1)")
        (old-end "(\\([^ ]+\\)[ ]+)")
        (new-end "(\\1)"))
    (if (use-region-p)
        (progn
          (message "Removing blanks at the beginning...")
          (replace-regexp old-start new-start nil (region-beginning) (region-end))
          (replace-regexp old-end   new-end   nil (region-beginning) (region-end)))
      (progn
        (message "Removing blanks at the end...")
        (query-replace-regexp old-start new-start nil (point-min) (point-max))
        (query-replace-regexp old-end   new-end   nil (point-min) (point-max))))))


(defun larumbe/verilog-dirs-and-pkgs-of-open-buffers ()
  "Base content fetched from: https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
Returns a list of directories from current verilog opened files.
It also updates currently opened SystemVerilog packages."
  (let ((verilog-opened-dirs)
        (verilog-opened-pkgs)
        (pkg-regexp "^\\s-*\\(?1:package\\)\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)"))
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "verilog-mode")
          (add-to-list 'verilog-opened-dirs default-directory)
          (save-excursion
            (beginning-of-buffer)
            (when (re-search-forward pkg-regexp nil t)
              (add-to-list 'verilog-opened-pkgs (buffer-file-name)))))))
    `(,verilog-opened-dirs ,verilog-opened-pkgs)))  ; Return list of dirs and packages


(provide 'verilog-indentation)

;;; verilog-indentation.el ends here
