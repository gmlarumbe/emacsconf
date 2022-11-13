;;; elisp-utils.el --- Elisp Utils  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Own functions
(defun larumbe/load-file-current-buffer ()
  "Load current buffer .el file."
  (interactive)
  (if (string-equal "el" (file-name-extension buffer-file-name))
      (load-file buffer-file-name)
    (error "Cannot load non-Elisp files")))


(defun larumbe/byte-compile-current-buffer-or-dir (&optional dir)
  "Byte-compile file of current visited buffer.
If prefix-arg is provided, recompile current DIR."
  (interactive "P")
  (if current-prefix-arg
      (byte-recompile-directory default-directory 0 :force))
  (byte-compile-file buffer-file-name))


(defun larumbe/insert-time-stamp-elisp ()
  "Insert time-stamp for Elisp buffers.
Try to add it before Commentary section."
  (interactive)
  (larumbe/insert-time-stamp "^;;; Commentary:"))


;;;; Xref
;; For elisp, the external-roots directories are considered to be the `load-path' since `emacs-lisp-mode'
;; sets the variable `project-vc-external-roots-function' locally to `elisp-load-path-roots'.
;; On remote machines, it could take very long times to grep every straight directory to find references.
;; So the options are to create global GTAGS/GPATH on each of these directories, or whether change the
;; `project-vc-external-roots-function' to not use the `load-path' and custom directories instead.
;;
;; The first thing is to set the value of `larumbe/elisp-xref-dirs':
;;  - If set to nil:
;;     + References will be looked-up in all the dirs of the `load-path'
;;     + `larumbe/elisp-xref-create-gtags' will create tags on every writable project directory of the `load-path'
;;  - If set to non-nil:
;;     + References will be looked-up in the specified directories.
;;     + `larumbe/elisp-xref-create-gtags' will create tags on these specified directories
;;
;; More INFO: https://emacs.stackexchange.com/questions/56198/how-to-use-xref-find-references-on-elisp-files-without-no-references-found-for
;;            2nd answer

(defvar larumbe/elisp-xref-dirs larumbe/emacs-conf-repos-devel
  "Set to nil by default, assumming a local/fast machine without many straight repos.")


(defun larumbe/elisp-xref-set-dirs (dirs)
  "Ask for which directories are to be used to find xrefs for elisp.

If called non-interactively, valid values are 'all, 'non-straight and 'mine.
Other values will set it to nil, enabling all folders for xref lookup."
  (interactive
   (list (intern (completing-read "Select dirs: " '(all
                                                    non-straight
                                                    mine)))))
  ;; Set variable according to choice
  (pcase dirs
    ('all
     (setq larumbe/elisp-xref-dirs nil))
    ('non-straight
     (setq larumbe/elisp-xref-dirs (append (seq-filter #'larumbe/straight-not-repo-p load-path)
                                           larumbe/emacs-conf-repos-packages)))
    ('mine
     (setq larumbe/elisp-xref-dirs larumbe/emacs-conf-repos-devel))
    (_
     (setq larumbe/elisp-xref-dirs nil)))
  ;; Echo value set
  (message "xref dirs set to: %s" larumbe/elisp-xref-dirs))


(defun larumbe/elisp-xref-create-gtags ()
  "Create gtags for Elisp directories depending on value of `larumbe/elisp-xref-dirs':
- If `larumbe/elisp-xref-dirs' is nil, create references for every writable project directory of `load-path'.
- If `larumbe/elisp-xref-dirs' is non-nil, create references for repos in `larumbe/elisp-xref-dirs'."
  (interactive)
  (let ((dirs (larumbe/elisp-project-vc-external-roots-function)))
    (larumbe/gtags-create-tags-async-dirs dirs)))


(defun larumbe/elisp-project-vc-external-roots-function ()
  "Return list of strings of external roots projects where to look for xref references.
Meant to be used as a hook to override default functionality of the whole `load-path'."
  (let ((dirs (if (bound-and-true-p larumbe/elisp-xref-dirs)
                  larumbe/elisp-xref-dirs
                load-path)))
    (delete-dups (mapcar #'(lambda (dir) (if (projectile-project-root dir)
                                        (expand-file-name (projectile-project-root dir))
                                      (expand-file-name dir)))
                         dirs))))


(defun larumbe/elisp-hook ()
  "Custom elisp hook."
  (sanityinc/enable-check-parens-on-save)
  (prettify-symbols-mode 1)
  (rainbow-delimiters-mode 1)
  ;; Xrefs limited to specified directories
  (when (bound-and-true-p larumbe/elisp-xref-dirs)
    (setq-local project-vc-external-roots-function #'larumbe/elisp-project-vc-external-roots-function))
  ;; Eldoc mode hook for Lisp related modes
  (dolist (hook '(emacs-lisp-mode-hook
                  lisp-interaction-mode-hook
                  ielm-mode-hook
                  eval-expression-minibuffer-setup-hook))
    (add-hook hook #'eldoc-mode)))



(defun larumbe/edebug-defun (arg)
  "Wrapper for `edebug-defun'.
Call `modi/toggle-edebug' when universal ARG is provided.

Modi's version allows instrumentation within `use-package'.
However, uninstrumentation is done by evaluating the whole buffer."
  (interactive "P")
  (if arg
      (call-interactively #'modi/toggle-edebug)
    (call-interactively #'edebug-defun)))


(defun larumbe/elisp-indent-defun ()
  "Indent current defun."
  (interactive)
  (save-excursion
    (mark-defun)
    (indent-region (region-beginning) (region-end))))



;;;; Steve Purcell
(defun sanityinc/headerise-elisp ()
  "Add minimal header and footer to an elisp buffer in order to placate flycheck."
  (interactive)
  (let* ((fname (if (buffer-file-name)
                    (file-name-nondirectory (buffer-file-name))
                  (error "This buffer is not visiting a file")))
         (pname (file-name-sans-extension fname))
         (desc (read-string "Package description: ")))
    (save-excursion
      (goto-char (point-min))
      (insert ";;; " fname " --- " desc  "  -*- lexical-binding: t -*-\n"
              ";;; Commentary:\n"
              ";;; Code:\n\n")
      (goto-char (point-max))
      (insert "\n\n(provide '" pname ")\n\n")
      (insert ";;; " fname " ends here\n"))))


(defun sanityinc/enable-check-parens-on-save ()
  "Run `check-parens' when the current buffer is saved."
  (add-hook 'after-save-hook #'check-parens nil t))




;;;; Kaushal Modi
;; Solution to toggle debug on a function whether it is defined inside or
;; outside a `use-package' wrapper
;; http://emacs.stackexchange.com/q/7643/115

;;;;; Edebug a defun or defmacro
(defvar modi/fns-in-edebug nil
  "List of functions for which `edebug' is instrumented.")

(defconst modi/fns-regexp (concat "([[:blank:]]*"
                                  "\\(cl-\\)*"
                                  "\\(defun\\|defmacro\\|defsubst\\)"
                                  "\\**"
                                  "[[:blank:]]+"
                                  "\\(?1:\\(\\w\\|\\s_\\)+\\)\\_>") ; word or symbol char
  "Regexp to find defun or defmacro definition.")

(defun modi/toggle-edebug ()
  (interactive)
  (save-excursion
    (re-search-backward modi/fns-regexp)
    (let ((start (point))
          (fn (match-string 1))
          end
          selection)
      ;; (message "Parsed: %s fns-in-edebug: %s" fn modi/fns-in-edebug)
      (forward-sexp 1)
      (setq end (point))
      (if (member fn modi/fns-in-edebug)
          ;; If the function is already being edebugged, uninstrument it
          (progn
            (setq modi/fns-in-edebug (delete fn modi/fns-in-edebug))
            (eval-buffer)
            (setq-default eval-expression-print-length 12)
            (setq-default eval-expression-print-level  4)
            (message "Edebug disabled: %s" fn))
        ;; If the function is not being edebugged, instrument it
        (save-restriction
          (narrow-to-region start end)
          (add-to-list 'modi/fns-in-edebug fn)
          (setq-default eval-expression-print-length nil)
          (setq-default eval-expression-print-level  nil)
          (edebug-defun)
          (message "Edebug: %s" fn))))))


;;;;; Debug on entry
(defvar modi/fns-in-debug nil
  "List of functions for which `debug-on-entry' is instrumented.")

(defun modi/toggle-debug ()
  (interactive)
  (let (fn)
    (save-excursion
      (re-search-backward modi/fns-regexp)
      (setq fn (match-string 1)))
    (if (member fn modi/fns-in-debug)
        ;; If the function is already being debugged, cancel its debug on entry
        (progn
          (setq modi/fns-in-debug (delete fn modi/fns-in-debug))
          (cancel-debug-on-entry (intern fn))
          (message "Debug-on-entry disabled: %s" fn))
      ;; If the function is not being debugged, debug it on entry
      (progn
        (add-to-list 'modi/fns-in-debug fn)
        (debug-on-entry (intern fn))
        (message "Debug-on-entry: %s" fn)))))



;;;;; Indentation
;; Change the default indentation function for `emacs-lisp-mode' to
;; improve the indentation of blocks like below:
;; (defhydra hydra-rectangle (:body-pre (rectangle-mark-mode 1)
;;                            :color pink
;;                            :post (deactivate-mark))

;; Solution 1
;; (add-hook 'emacs-lisp-mode-hook
;;           (lambda () (setq-local lisp-indent-function #'common-lisp-indent-function)))

;; Solution 2
;; http://emacs.stackexchange.com/q/10230/115
;; https://github.com/Fuco1/.emacs.d/blob/af82072196564fa57726bdbabf97f1d35c43b7f7/site-lisp/redef.el#L12-L94
(defun Fuco1/lisp-indent-function (indent-point state)
  "This function is the normal value of the variable `lisp-indent-function'.
The function `calculate-lisp-indent' calls this to determine
if the arguments of a Lisp function call should be indented specially.

INDENT-POINT is the position at which the line being indented begins.
Point is located at the point to indent under (for default indentation);
STATE is the `parse-partial-sexp' state for that position.

If the current line is in a call to a Lisp function that has a non-nil
property `lisp-indent-function' (or the deprecated `lisp-indent-hook'),
it specifies how to indent.  The property value can be:

* `defun', meaning indent `defun'-style
  \(this is also the case if there is no property and the function
  has a name that begins with \"def\", and three or more arguments);

* an integer N, meaning indent the first N arguments specially
  (like ordinary function arguments), and then indent any further
  arguments like a body;

* a function to call that returns the indentation (or nil).
  `lisp-indent-function' calls this function with the same two arguments
  that it itself received.

This function returns either the indentation to use, or nil if the
Lisp function does not specify a special indentation."
  (let ((normal-indent (current-column))
        (orig-point (point)))
    (goto-char (1+ (elt state 1)))
    (parse-partial-sexp (point) calculate-lisp-indent-last-sexp 0 t)
    (cond
     ;; car of form doesn't seem to be a symbol, or is a keyword
     ((and (elt state 2)
           (or (not (looking-at "\\sw\\|\\s_"))
               (looking-at ":")))
      (if (not (> (save-excursion (forward-line 1) (point))
                  calculate-lisp-indent-last-sexp))
          (progn (goto-char calculate-lisp-indent-last-sexp)
                 (beginning-of-line)
                 (parse-partial-sexp (point)
                                     calculate-lisp-indent-last-sexp 0 t)))
      ;; Indent under the list or under the first sexp on the same
      ;; line as calculate-lisp-indent-last-sexp.  Note that first
      ;; thing on that line has to be complete sexp since we are
      ;; inside the innermost containing sexp.
      (backward-prefix-chars)
      (current-column))
     ((and (save-excursion
             (goto-char indent-point)
             (skip-syntax-forward " ")
             (not (looking-at ":")))
           (save-excursion
             (goto-char orig-point)
             (looking-at ":")))
      (save-excursion
        (goto-char (+ 2 (elt state 1)))
        (current-column)))
     (t
      (let ((function (buffer-substring (point)
                                        (progn (forward-sexp 1) (point))))
            method)
        (setq method (or (function-get (intern-soft function)
                                       'lisp-indent-function)
                         (get (intern-soft function) 'lisp-indent-hook)))
        (cond ((or (eq method 'defun)
                   (and (null method)
                        (> (length function) 3)
                        (string-match "\\`def" function)))
               (lisp-indent-defform state indent-point))
              ((integerp method)
               (lisp-indent-specform method state
                                     indent-point normal-indent))
              (method
               (funcall method indent-point state))))))))


(defun modi/set-emacs-lisp-indentation ()
  "Customize the indentation for `emacs-lisp-mode'."
  (setq-local lisp-indent-function #'Fuco1/lisp-indent-function))



;;;; Lint
;; Needed to submit packages to MELPA. Helpful to write other modes.
(use-package package-lint)
;; Only enabled if package has comments with: "Version" "Package-Version" "Package-Requires"
;; i.e: `package-lint-looks-like-a-package-p' is t for `current-buffer'
(use-package flycheck-package
  :after package-lint)


;;;; Misc
(use-package lively
  :demand
  :config
  (setq lively-interval 1)

  (defun larumbe/lively-dwim (arg)
    "docstring"
    (interactive "P")
    (if arg
        (lively-stop)
      (if (region-active-p)
          (lively-region (region-beginning) (region-end))
        (lively)))))



;; Many thanks to Kaushal Modi
(use-package command-log-mode
  :demand
  :init
  ;; Do not bind `clm/open-command-log-buffer' by default to "C-c o"
  (setq command-log-mode-key-binding-open-log nil)
  :config
  (setq command-log-mode-window-size 60)

  (defhydra hydra-command-log (:color teal
                               :columns 6)
    "Command Log"
    ("c" command-log-mode "toggle mode")
    ("o" clm/open-command-log-buffer "open log buffer")
    ("l" clm/open-command-log-buffer "open log buffer")
    ("C" clm/command-log-clear "clear log buffer")
    ("t" clm/toggle-command-log-buffer "toggle log buffer")
    ("s" clm/save-command-log "save log")
    ("x" clm/close-command-log-buffer "close log buffer")
    ("q" nil "cancel" :color blue)))



;; https://github.com/cpitclaudel/easy-escape
(use-package easy-escape
  :demand
  :diminish easy-escape-minor-mode)


(use-package eros
  :demand
  :config
  (eros-mode 1))


(use-package el2markdown)



(provide 'elisp-utils)

;;; elisp-utils.el ends here

