;;;;;;;;;;;;;;;;;;;;;;
;; CUSTOM FUNCTIONS ;;
;;;;;;;;;;;;;;;;;;;;;;

;;; Restart code
(defun launch-separate-emacs-in-terminal ()
  (suspend-emacs "fg ; emacs -nw"))

(defun launch-separate-emacs-under-x ()
  (call-process "sh" nil nil nil "-c" "emacs &"))

(defun restart-emacs ()
  (interactive)
  ;; We need the new emacs to be spawned after all kill-emacs-hooks
  ;; have been processed and there is nothing interesting left
  (let ((kill-emacs-hook (append kill-emacs-hook (list (if (display-graphic-p)
                                                         #'launch-separate-emacs-under-x
                                                         #'launch-separate-emacs-in-terminal)))))
    (save-buffers-kill-emacs)))



;;; Buffer management
(defun close-all-buffers ()
  (interactive)
  (mapc 'kill-buffer (buffer-list)))

(defun only-current-buffer ()
  (interactive)
  (mapc 'kill-buffer (cdr (buffer-list (current-buffer)))))

;; https://stackoverflow.com/questions/2238418/emacs-lisp-how-to-get-buffer-major-mode
(defun buffer-mode (buffer-or-string)
  "Returns the major mode associated with a buffer."
  (with-current-buffer buffer-or-string
     major-mode))
;; with-current-buffer will restore your buffer when it returns.

(defun larumbe/enlarge-window-horizontally ()
  "Uses shrink-window as a wrapper"
  (interactive)
  (shrink-window larumbe/shrink-window-horizontally-delta t))

(defun larumbe/shrink-window-horizontally ()
  "Uses shrink-window as a wrapper"
  (interactive)
  (shrink-window (- larumbe/shrink-window-horizontally-delta) t))

(defun larumbe/enlarge-window-vertically ()
  "Uses shrink-window as a wrapper"
  (interactive)
  (shrink-window larumbe/shrink-window-vertically-delta))

(defun larumbe/shrink-window-vertically ()
  "Uses shrink-window as a wrapper"
  (interactive)
  (shrink-window (- larumbe/shrink-window-vertically-delta)))


;;; Movement
;; Search-At-Point
;; Move to beginning of word before yanking word in isearch-mode.
;; Make C-s C-w and C-r C-w act like Vim's g* and g#, keeping Emacs'
;; C-s C-w [C-w] [C-w]... behaviour.

(defun my-isearch-yank-word-or-char-from-beginning ()
  "Move to beginning of word before yanking word in isearch-mode."
  (interactive)
  ;; Making this work after a search string is entered by user
  ;; is too hard to do, so work only when search string is empty.
  (if (= 0 (length isearch-string))
      (beginning-of-thing 'word))
  (isearch-yank-word-or-char)
  ;; Revert to 'isearch-yank-word-or-char for subsequent calls
  (substitute-key-definition 'my-isearch-yank-word-or-char-from-beginning
                             'isearch-yank-word-or-char
                             isearch-mode-map))

(add-hook 'isearch-mode-hook
          (lambda ()
            "Activate my customized Isearch word yank command."
            (substitute-key-definition 'isearch-yank-word-or-char
                                       'my-isearch-yank-word-or-char-from-beginning
                                       isearch-mode-map)))

;; Expect them to be overriden in specific major modes (list advance in Lisp mode)
;; (Copied from vhdl-mode)
(defun forward-same-indent ()
  "Move forward to next line with same indent."
  (interactive)
  (let ((pos (point))
        (indent (current-indentation)))
    (beginning-of-line 2)
    (while (and (not (eobp))
                (or (looking-at "^\\s-*\\(--.*\\)?$")
                    (> (current-indentation) indent)))
      (beginning-of-line 2))
    (if (= (current-indentation) indent)
        (back-to-indentation)
      (message "No following line with same indent found in this block")
      (goto-char pos)
      nil)))

(defun backward-same-indent ()
  "Move backward to previous line with same indent."
  (interactive)
  (let ((pos (point))
        (indent (current-indentation)))
    (beginning-of-line -0)
    (while (and (not (bobp))
                (or (looking-at "^\\s-*\\(--.*\\)?$")
                    (> (current-indentation) indent)))
      (beginning-of-line -0))
    (if (= (current-indentation) indent)
        (back-to-indentation)
      (message "No preceding line with same indent found in this block")
      (goto-char pos)
      nil)))


;;; Editing
(defun duplicate-line()
  (interactive)
  (move-beginning-of-line 1)
  (kill-line)
  (yank)
  (open-line 1)
  (next-line 1)
  (yank)
  (move-beginning-of-line 1)
  )

(defun larumbe/kill-current-buffer ()
  "Kill current buffer without confirmation.(buffer-name) defaults to current-buffer name"
  (interactive)
  (kill-buffer (buffer-name)))


(defun larumbe/delete-comments-from-buffer ()
  "Fetched from https://emacs.stackexchange.com/questions/5441/function-to-delete-all-comments-from-a-buffer-without-moving-them-to-kill-ring "
  (interactive)
  (goto-char (point-min))
  (let (kill-ring)
    (comment-kill (count-lines (point-min) (point-max)))))


(defun do-lines (fun &optional start end)
  "Invoke function FUN on the text of each line from START to END."
  (interactive
   (let ((fn   (intern (completing-read "Function: " obarray 'functionp t))))
     (if (use-region-p)
         (list fn (region-beginning) (region-end))
       (list fn (point-min) (point-max)))))
  (save-excursion
    (goto-char start)
    (while (< (point) end)
      (funcall fun (buffer-substring (line-beginning-position) (line-end-position)))
      (forward-line 1))))


(defun read-lines (filePath)
  "Return a list of lines of a file at filePath."
  (with-temp-buffer
    (insert-file-contents filePath)
    (split-string (buffer-string) "\n" t)))


(defun larumbe/buffer-expand-filenames ()
  "Expands filenames path present in `current-buffer' line by line"
  (interactive)
  (let (cur-line)
    (save-excursion
      (beginning-of-buffer)
      (while (< (point) (point-max))
        (delete-horizontal-space)
        (setq cur-line (expand-file-name (thing-at-point 'line) default-directory))
        (kill-line 1)
        (insert cur-line)))))


(defun larumbe/sort-regexp-at-the-beginning-of-file (regexp)
  "Move lines containing REGEXP recursively at the beginning of the file, line by line
This might be useful when managing a list of files, one file at a line, and there is some need of sorting by regexp
For example, in SystemVerilog packages might need to be included before reading other files."
  (interactive)
  (beginning-of-buffer)
  (while (not sorted-files-p)
    (save-excursion
      (if (not (search-forward-regexp regexp nil 1))
          (setq sorted-files-p t))
      (beginning-of-line)
      (kill-line 1)) ; 1 kills trailing newline as well
    (yank)))




;;; Specific Mode oriented functions
;;;; Dired
(defun larumbe/toggle-dired-deletion-confirmer ()
  "Toggles deletion confirmer for dired from (y-or-n) to nil and viceversa"
  (interactive)
  (if (equal dired-deletion-confirmer 'yes-or-no-p)
      (progn
        (setq dired-deletion-confirmer '(lambda (x) t))
        (message "Dired deletion confirmation: FALSE"))
    (progn
      (setq dired-deletion-confirmer 'yes-or-no-p)
      (message "Dired deletion confirmation: TRUE"))))


(defun larumbe/dired-do-async-shell-command-okular ()
  "Same as `dired-do-async-shell-command' but if on a PDF will open Okular directly"
  (interactive)
  (when (not (string-equal major-mode "dired-mode"))
    (error "Needs to be executed in dired...! "))
  (let ((program "okular")
        (filename (thing-at-point 'filename t)))
    (if (string-equal (file-name-extension filename) "pdf")
        (progn
          (dired-do-async-shell-command program filename (list filename))
          (delete-window (get-buffer-window "*Async Shell Command*")))
      (call-interactively 'dired-do-async-shell-command))))



;;;; FIC
;; Fetched from /home/martigon/.elisp/larumbe/lang/verilog-settings.el -> larumbe/lfp-clean-project-fic-keywords-ag-files
;; Generalizes to a directory and certain files
(defun larumbe/clean-fic-keywords-dir ()
  "Perform a `ag-regexp' of `fic-mode' highlighted keywords in order to check pending project actions. "
  (interactive)
  (let ((kwd)
        (path)
        (ag-arguments ag-arguments) ; Save the global value of `ag-arguments' (copied from modi)
        (regex)
        (files)
        )
    (setq kwd (completing-read "Select keyword: " 'fic-highlighted-words))
    (setq path (read-directory-name "Directory: "))
    ;; (setq regex (completing-read "Select file regex: " 'regex))
    (setq files (completing-read "Select file regex: " '("(System)Verilog" "Python" "elisp")))
    (pcase files
      ("(System)Verilog" (setq regex ".[s]?v[h]?$")) ; +Headers
      ("Python"          (setq regex ".py$"))
      ("elisp"           (setq regex ".el$"))
      )
    ;; Copied from AG for `modi/verilog-find-parent-module'
    (add-to-list 'ag-arguments "-G" :append)
    (add-to-list 'ag-arguments regex :append)
    (ag-regexp kwd path)))



;;;; Locked Mode
(define-minor-mode locked-buffer-mode
  "Make the current window always display this buffer."
  nil " locked" nil
  (set-window-dedicated-p (selected-window) locked-buffer-mode))



;;;; Flyspell
(defun flyspell-toggle ()
  "Toggle flyspell mode on current buffer (verilog oriented at first)"
  (interactive)
  (if (bound-and-true-p flyspell-mode)
      (call-interactively 'flyspell-mode nil)
    (progn
      (call-interactively 'flyspell-mode 1)
      (call-interactively 'flyspell-prog-mode 1)
      (call-interactively 'flyspell-buffer))))


;;;; YASnippet/Hydra
(defun larumbe/hydra-yasnippet (snippet)
  "Function/Macro to integrate YASnippet within Hydra"
  (interactive)
  (progn
    (insert snippet)
    (yas-expand)))

(defhydra hydra-nxml-docbook-template (:color blue
                                       :hint nil)
      "
_p_aragraph     _b_old           itemized_L_ist   _r_egisters
_s_ection       _i_talic         _l_istitem
_t_itle         _B_oldRegion
_c_hapter       _I_talicRegion
"
      ;; ("p"   (larumbe/hydra-yasnippet "para")) ; Leaves a line between tag and text
      ("p"   (larumbe/hydra-yasnippet "parahp")) ; Right after the tag
      ("s"   (larumbe/hydra-yasnippet "section"))
      ("t"   (larumbe/hydra-yasnippet "title"))
      ("c"   (larumbe/hydra-yasnippet "chapter"))
      ("b"   (larumbe/hydra-yasnippet "bold"))
      ("i"   (larumbe/hydra-yasnippet "italic"))
      ("B"   (larumbe/nxml-docbook-bold-region))
      ("I"   (larumbe/nxml-docbook-italic-region))
      ("r"   (larumbe/hydra-yasnippet "registers"))
      ("L"   (larumbe/hydra-yasnippet "itemizedlist"))
      ("l"   (larumbe/hydra-yasnippet "listitem"))
      ("q"   nil nil :color blue)
      ("C-g" nil nil :color blue)
      )


;;;; TCL
;; Copied from sh-send-line-or-regin-and-step for SH Shell scripting
(defun tcl-send-line-or-region-and-step ()
  "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead."
  (interactive)
  (let (from to end (proc (inferior-tcl-proc)))
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    (tcl-send-string proc (buffer-substring-no-properties from to))
    (tcl-send-string proc "\n")
    (goto-char end)))


(setq larumbe/vivado-tcl-shell-buffer "*vivado-tcl*")
;; Same as before but intended for sending text to a *compilation* Vivado Shell with regexps
(defun tcl-send-line-or-region-and-step-vivado-shell ()
  "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead."
  (interactive)
  (let (from to end (proc (get-buffer-process larumbe/vivado-tcl-shell-buffer)))
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    (comint-send-string proc (buffer-substring-no-properties from to))
    (comint-send-string proc "\n")
    (goto-char end)))


;; Fake TCL Shell based on compilation/comint modes to allow for regexps
;; Advantages over `inferior-tcl': Can parse Regexps
;; Drawbacks over `inferior-tcl': Requires custom function to send lines/regions from a .tcl buffer
;;   - This would be previous function :)
(defun larumbe/vivado-tcl-shell-compilation ()
  "Invoke a TCL vivado shell with the proper regexps, suited for compilation"
  (interactive)
  (compile (concat tcl-application " " (mapconcat 'identity tcl-command-switches " ")) t)
  (select-window (get-buffer-window "*compilation*"))
  (end-of-buffer)
  (setq truncate-lines t)
  (linum-mode)
  (larumbe/vivado-error-regexp-set-emacs)
  (rename-buffer larumbe/vivado-tcl-shell-buffer))



;;;; Python
;; Copied from sh-send-line-or-region-and-step for SH Shell scripting
(defun python-send-line-or-region-and-step ()
  "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead."
  (interactive)
  (let (from to end (proc (python-shell-get-process-or-error)))
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    (python-shell-send-string (buffer-substring-no-properties from to))
    (python-shell-send-string "\n")
    (goto-char end)))



;; INFO: These two latter functions were created for development in Python setup (for remote targets)
(defun larumbe/python-send-line-or-region-and-step-remote-from-host ()
  "Similar to previous one but sends data to *ansi-term* and when a region needs to be sent, instead of creating
a temp file that is later deleted through Python interpreter, is instead parsed in a temp-buffer
and newlines are erased. That was the main issue when sending text, as a newline is interpreted as Enter "
  (interactive)
  (let (from to end string)
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))

    ;; Prepare output to send to console to avoid errors
    (setq string (buffer-substring-no-properties from to))
    (with-temp-buffer
      (insert-string string)
      (flush-lines "^\\s-*$" (point-min) (point-max)) ; Remove newlines before sending to console
      (delete-trailing-whitespace)
      (setq string (buffer-string)))
    ;; Send to console *ansi-term*
    (comint-send-string "*ansi-term*" (concat string "\n"))
    (goto-char end)))


(defun larumbe/python-send-line-and-step-ansi-no-indent ()
  "Similar to `larumbe/sh-send-line-or-region-and-step-ansi', but useful for python individual
statements to avoid indentation errors when testing"
  (interactive)
  (let (from to end string)
    (if (use-region-p)
        (error "Region not supported while bypassing indentation!")
      (setq from (progn (beginning-of-line-text) ; DANGER: Does not take comments into account!
                        (point))
            to (line-end-position)
            end (1+ to)))

    (setq string (buffer-substring-no-properties from to))
    (comint-send-string "*ansi-term*" string)
    (comint-send-string "*ansi-term*" "\n")
    (goto-char end)
    (message "Bypassing indentation...")))


;; Global Tags functions (copied from the ones of verilog)
(defun larumbe/gtags-python-files-pwd-recursive ()
  "Generate gtags.files for current directory. Purpose is to be used with dired mode for small projects, to save the regexp"
  (interactive)
  (larumbe/directory-files-recursively-to-file (list default-directory) "gtags.files" ".py$")
  )

(defun larumbe/ggtags-create-python-tags-recursive ()
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-python-files-pwd-recursive)
  (ggtags-create-tags default-directory))

;;;; Ansi-term/Shell
(defun larumbe/ansi-term ()
  "Checks if there is an existing *ansi-term* buffer and pops to it (if not visible open on the same window).
Otherwise create it"
  (interactive)
  (let ((buf "*ansi-term*"))
    (if (get-buffer buf)
        (if (get-buffer-window buf)
            (pop-to-buffer buf)
          (switch-to-buffer buf))
      (ansi-term "/bin/bash"))))


;; Fetched from: /usr/share/emacs/25.1/lisp/progmodes/sh-script.el.gz:1551
(defun larumbe/sh-send-line-or-region-and-step-ansi ()
  "Same as `sh-send-line-or-region-and-step-ansi' but for *ansi-term* process"
  (interactive)
  (let (from to end)
    (if (use-region-p)
        (setq from (region-beginning)
              to (region-end)
              end to)
      (setq from (line-beginning-position)
            to (line-end-position)
            end (1+ to)))
    ;; DANGER: Changes went here
    (comint-send-string (get-buffer-process "*ansi-term*")
                        (concat (buffer-substring-no-properties from to) "\n"))
    ;; End of DANGER
    (goto-char end)))

(defun sh-switch-to-process-buffer ()
  (interactive)
  (pop-to-buffer (process-buffer (get-process "shell")) t))

;;;; XML
(defun larumbe/nxml-docbook-bold-region ()
  "Get region bold"
  (interactive)
  (let (beg end)
    (if (use-region-p)
        (progn
          (setq beg (region-beginning))
          (setq end (region-end))
          (save-excursion
            (goto-char end)
            (insert "</emphasis>"))
            (goto-char beg)
            (insert "<emphasis role=\"bold\">"))
      (message "No region selected motherfucker!"))))

(defun larumbe/nxml-docbook-italic-region ()
  "Get region bold"
  (interactive)
  (let (beg end)
    (if (use-region-p)
        (progn
          (setq beg (region-beginning))
          (setq end (region-end))
          (save-excursion
            (goto-char end)
            (insert "</emphasis>"))
            (goto-char beg)
            (insert "<emphasis role=\"italic\">"))
      (message "No region selected motherfucker!"))))


;;;; Docbook
;; https://stackoverflow.com/questions/2615002/how-to-generate-pdf-from-docbook-5-0/2651158
(setq larumbe/docbook-xsl-program "xsltproc")
(setq larumbe/docbook-fo-program "fop")

(defun larumbe/docbook-to-pdf ()
  "Render XML Docbook file to PDF"
  (interactive)
  (let (xml-file pdf-out fo-file cmd)
    (setq xml-file (read-file-name "Docbook file: "))
    (if (string-equal (file-name-extension xml-file) "xml") ; File must be a xml
        (progn
          (setq pdf-out (concat (file-name-sans-extension (file-name-nondirectory xml-file)) ".pdf"))
          (setq fo-file (concat (file-name-sans-extension (file-name-nondirectory xml-file)) ".fo"))
          (setq cmd
                (concat
                 larumbe/docbook-xsl-program " "
                 "-xinclude "
                 larumbe/docbook-xsl-stylesheet " "
                 xml-file " > " fo-file " "
                 "&& "
                 larumbe/docbook-fo-program " -fo " fo-file " -pdf " pdf-out))
          (shell-command "ln -s images/* .") ;; Create symlinks to all images to get them rendered (assumed to be contained within a 'images' folder)
          (shell-command cmd "*Docbook2PDF*")
          (shell-command "find . -lname 'images/*' -delete") ;; Remove all the symbolic links to images once file has been rendered to PDF
          )
      (message "File isn't .xml!!"))))


(defun larumbe/docbook-to-pdf-current-buffer (&optional no-preview)
  "Render current buffer XML Docbook file to PDF.
If Universal Argument is provided, then do not preview file"
  (interactive "P")
  (let (xml-file pdf-out fo-file cmd docbuf-pdf docbuf-okular)
    (setq docbuf-pdf "*Docbook2PDF*")
    (setq docbuf-okular "*DocbookOkular*")
    (setq xml-file (file-name-nondirectory buffer-file-name))
    (if (string-equal (file-name-extension xml-file) "xml") ; File must be a xml
        (progn
          (setq pdf-out (concat (file-name-sans-extension (file-name-nondirectory xml-file)) ".pdf"))
          (setq fo-file (concat (file-name-sans-extension (file-name-nondirectory xml-file)) ".fo"))
          (setq cmd
                (concat
                 larumbe/docbook-xsl-program " "
                 "-xinclude "
                 larumbe/docbook-xsl-stylesheet " "
                 xml-file " > " fo-file " "
                 "&& "
                 larumbe/docbook-fo-program " -fo " fo-file " -pdf " pdf-out))
          (message (concat "Rendering " xml-file "..."))
          (shell-command "ln -sf images/* .") ;; Create symlinks to all images to get them rendered (assumed to be contained within a 'images' folder)
          (shell-command cmd docbuf-pdf)
          (shell-command (concat "rm " fo-file))
          (shell-command "find . -lname 'images/*' -delete") ;; Remove all the symbolic links to images once file has been rendered to PDF
          (unless no-preview
            (start-process-shell-command docbuf-okular docbuf-okular (concat "okular " pdf-out))))
      (message "File isn't .xml!!"))))



;;; My functions
;;;; Aux functions from other programmers
;; https://gist.github.com/ffevotte/9345586#file-gistfile1-el
(defun source (filename)
  "Update environment variables from a shell source file."
  (interactive "fSource file: ")
  (message "Sourcing environment from `%s'..." filename)
  (with-temp-buffer
    (shell-command (format "diff -u <(true; export) <(source %s; export)" filename) '(4))
    (let ((envvar-re "declare -x \\([^=]+\\)=\\(.*\\)$"))
      ;; Remove environment variables
      (while (search-forward-regexp (concat "^-" envvar-re) nil t)
        (let ((var (match-string 1)))
          (message "%s" (prin1-to-string `(setenv ,var nil)))
          (setenv var nil)))
      ;; Update environment variables
      (goto-char (point-min))
      (while (search-forward-regexp (concat "^+" envvar-re) nil t)
        (let ((var (match-string 1))
              (value (read (match-string 2))))
          (message "%s" (prin1-to-string `(setenv ,var ,value)))
          (setenv var value)))))
  (message "Sourcing environment from `%s'... done." filename))


;; Read file content into a String
;; http://ergoemacs.org/emacs/elisp_read_file_content.html
(defun get-string-from-file (filePath)
  "Return filePath's file content."
  (with-temp-buffer
    (insert-file-contents filePath)
    (buffer-string)))
;; thanks to “Pascal J Bourguignon” and “TheFlyingDutchman 〔zzbba…@aol.com〕”. 2010-09-02


;; https://www.gnu.org/software/emacs/manual/html_node/eintr/print_002delements_002dof_002dlist.html
(defun print-elements-of-list (list)
  "Print each element of LIST on a line of its own."
  (while list
    (print (car list))
    (setq list (cdr list))))


;;;; Larumbe's generic functions
;; Read file content into a String"
;; (Modified version, replaces newline with space, for ag-verilog arguments parsing)
(defun larumbe/get-string-from-file-ag-arguments (filePath)
  "Return filePath's file content."
  (with-temp-buffer
    (insert-file-contents filePath)
    (replace-regexp "\n" " " nil (point-min) (point-max))
    (buffer-string)))
;; thanks to “Pascal J Bourguignon” and “TheFlyingDutchman 〔zzbba…@aol.com〕”. 2010-09-02


;; Load current buffer .el file (useful for rudimentary debugging)
(defun larumbe/load-file-current-buffer ()
  "Load current buffer .el file "
  (interactive)
  (load-file buffer-file-name)
  )


;; Copy current pwd to kill-ring (useful to deal with files without the need of switching to dired)
(defun larumbe/pwd-to-kill-ring ()
  "Copy current file path to kill-ring"
  (interactive)
  (kill-new (buffer-file-name))
  (message (buffer-file-name)))


(defun larumbe/pwd-to-kill-ring-with-line ()
  "Copy current file path to kill-ring"
  (interactive)
  (let ((file-name (concat (buffer-file-name) ":" (format "%s" (line-number-at-pos)))))
    (kill-new file-name)
    (message (buffer-file-name))))


(defun larumbe/revert-buffer-no-confirm ()
  "Revert current buffer without asking"
  (interactive)
  (revert-buffer nil t t))


(defun larumbe/directory-files-recursively-to-file (dirs file re)
  "Retrieve every file matching `Regexp' of a specified `Dir' to output `file'"
  (interactive)
  (with-temp-buffer
    (mapc
     (lambda (dir) (insert (mapconcat 'identity (directory-files-recursively dir re) "\n")))
     dirs)
    (write-file file)))


(defun larumbe/current-buffer-to-file (out-file)
  "Export current buffer to output-file passed as parameter.
Can be called interactively or not.
It was first thought for exporting SCons compilations."
  (interactive "FEnter output path: "
               (setq out-file s))
  (append-to-file (point-min) (point-max) out-file))


(defun larumbe/print-elements-of-list-of-strings (list)
  "Print each element of LIST on a line of its own."
  (let (return-string)
    (while list
      (setq return-string (concat return-string (message "%s\n" (car list))))
      (setq list (cdr list)))
    (message "%s" return-string)))


(defun larumbe/diff-recursive-directories (dir1 dir2 out-file)
  "Export diff between two directories to output file.
It uses an exclude schema that leaves out of the diff the files/expresions in exclude.list
This is because there is no include option for `diff' utils.
`https://stackoverflow.com/questions/3775377/how-do-you-diff-a-directory-for-only-files-of-a-specific-type'"
  (interactive "DSelect first directory: \nDSelect second directory: \nFSelect output file:")
  (let ((exclude-file)
        (exclude-patterns '("*.wdf"
                            "*.xml"
                            "*.bxml"
                            "*.wpc"
                            "*.target"
                            "*.rdl.ast"
                            "file_list.py"
                            "source_list.tcl"
                            "run_vivado.tcl")))
    (setq exclude-file (concat (file-name-directory out-file) "exclude.pats"))
    (f-write-text (larumbe/print-elements-of-list-of-strings exclude-patterns) 'utf-8 exclude-file)
    ;; If return value is `1' is because differences were found
    (start-process-shell-command
     "*diff-dirs*" nil
     (concat "diff -X " exclude-file " -r " dir1 " " dir2 " > " out-file))))



(defun larumbe/help-major-mode-helm ()
  "Get helm M-x commands list and shortcuts for the last time it was used (before a C-g)
It is assumed to be used after a `M-x' then e.g. `org-', then `C-g' and finally this function for window arrangement."
  (interactive)
  (delete-other-windows)
  (split-window-right)
  (other-window 1)
  ;; (shrink-window 30) ;; TODO: Does not seem to work
  (switch-to-buffer "*helm M-x*")
  (other-window 1))




(defun larumbe/verilog-imenu-hide-all (&optional first)
  "Hides all the blocks @ Imenu-list buffer.
If optional FIRST is used, then shows first block (Verilog *instances/interfaces*)"
  (interactive)
  (if (string-equal major-mode "imenu-list-major-mode")
      (progn
        (beginning-of-buffer)
        (while (< (point) (point-max))
          (hs-hide-block)
          (next-line))
        (beginning-of-buffer)
        ;; If there is an optional argument, unfold first block
        (when first
          (hs-show-block)))
    (message "Not in imenu-list mode !!")))


(defun larumbe/untabify-trailing-whitespace-toggle ()
  "Toggle untabify and trailing whitespace for some customized programming modes."
  (interactive)
  (if untabify-delete-trailing-whitespace
      (progn ;; Disable
        (setq untabify-delete-trailing-whitespace nil)
        (remove-hook 'write-file-functions (lambda() (untabify (point-min) (point-max)) nil))
        (remove-hook 'write-file-functions (lambda() (delete-trailing-whitespace (point-min) (point-max)) nil))
        (message "Untabify set to: %s" untabify-delete-trailing-whitespace))
    (progn   ;; Enable
      (setq untabify-delete-trailing-whitespace t)
      (add-hook 'write-file-functions (lambda() (untabify (point-min) (point-max)) nil))
      (add-hook 'write-file-functions (lambda() (delete-trailing-whitespace (point-min) (point-max)) nil))
      (message "Untabify set to: %s" untabify-delete-trailing-whitespace))))


;; TODO: Still does not seem to work...
(defun larumbe/init-emacs-function-hp ()
  "Initial steps to be performed after hp config has been loaded.
Load TODO.org and see agenda for today..."
  (interactive)
  (let ((buf "TODO.org")
        (file "/home/martigon/TODO.org"))
    (when (not (get-buffer buf))
      (find-file file))
    (switch-to-buffer "TODO.org")
    (call-interactively 'org-agenda-list)))


(defun larumbe/pop-to-previous-mark ()
  "Pop to previous mark"
  (interactive)
  (set-mark-command 4))



;;;; SVN customizations
(defun larumbe/update-svn-repos (repo-paths)
  "Update all svn-repos passed as parameter (to be used in local and cee)"
  (while repo-paths
    (async-shell-command
     (concat "svn update " (nth 0 (car repo-paths)))
     (concat "*svn-update" "<" (nth 1 (car repo-paths)) ">" "*"))
    (setq repo-paths (cdr repo-paths))))



;;;; Git customizations
;;;;; Repo sync
(defun larumbe/repo-sync-sandboxes (repo-paths)
  "Update all .repo sandboxes passed as parameter (to be used in local and cee)"
  (while repo-paths
    (async-shell-command
     (concat "cd " (nth 0 (car repo-paths)) " && repo sync")
     (concat "*<" (nth 1 (car repo-paths)) ">*"))
    (setq repo-paths (cdr repo-paths))))


;;;;; Manual/Ediff Merging
;;;;;; Aux functions
(defun larumbe/git-find-changed-files-between-branches ()
  "Returns a list of strings with changed files"
  (let ((str)
        (buffer-name "*shell-git-diff-output*"))
    (save-window-excursion
      (shell-command
       (concat "git diff --name-status " larumbe/git-branch-a ".." larumbe/git-branch-b)
       buffer-name)
      (switch-to-buffer buffer-name)
      (replace-regexp "[MAD]\t" "" nil (point-min) (point-max)) ; Modified/Added/Deleted = MAD
      (setq str (split-string (buffer-string))))))


(defun larumbe/git-exclude-files-before-ediff (merge-files exclude-files)
  "Remove EXCLUDE-FILES from MERGE-FILES parameter list.
https://stackoverflow.com/questions/25009453/how-to-delete-a-list-of-elements-from-another-list-in-elisp
It is the same as solution 1 but using delete instead of delq, and printing the value of temp variable at the end"
  (let (temp)
    (setq temp merge-files)
    (mapcar
     (lambda (x)
       (setq temp (delete x temp)))
     exclude-files)
    (setq temp temp) ; Return only last value after all the iterations
    ))


(defun larumbe/git-merge-all-files-between-branches (changed-files)
  "Ediff/Merge every changed file (present in `files' argument)"
  (mapcar
   (lambda (file)
     (magit-ediff-compare
      larumbe/git-sync-repo-a
      larumbe/git-sync-repo-b
      file file))
   changed-files))



;;;;;; Interactive functions
;; TODO: Needs to be tested after erasing `repohome.el'
;; Ediff/Merge 2 branches manually by doing checkouts
;; This is based on old .repohome sync example. Fill with current development repo branches
;;;;;;; Variables to check which repos must get synced
(setq larumbe/git-available-branches '("hp" "cee" "master"))
(setq larumbe/git-branch-a "origin/master")
(setq larumbe/git-branch-b "origin/hp")

;;;;;;; Variables to set which files must be excluded from ediff/merging
(setq larumbe/git-branch-files-to-exclude-from-merge
      '(".elisp/larumbe/hp-settings.el"
        ".elisp/larumbe/cee-settings.el"
        ".bashrc"
        ".ctags"
        ".gitconfig"
        ".xinitrc"
        ".globalrc"
        "TODO.org"))


(defun larumbe/git-checkout-file-from-another-branch ()
  "Used when an override needs to be performed."
  (interactive)
  (let (fetch-file-from-branch
        fetch-file-to-branch
        filename
        files-changed)
    (save-window-excursion
      ;; Prepare variables according to initial setup and prompts
      (setq fetch-file-from-branch (completing-read "Checkout file from branch: " larumbe/git-available-branches))
      (setq fetch-file-to-branch   (completing-read "Checkout file to branch: "   larumbe/git-available-branches))
      (setq files-changed (larumbe/git-find-changed-files-between-branches))
      (setq files-changed (larumbe/git-exclude-files-before-ediff files-changed larumbe/git-branch-files-to-exclude-from-merge))
      (setq filename (completing-read "Choose file to checkout: " files-changed))
      ;; And finally choose between the possible files and execute the shell-command to checkout the file
      (shell-command
       (concat
        larumbe/gite-cmd " checkout " fetch-file-to-branch " && "
        larumbe/gite-cmd " "
        "checkout "
        "origin/" fetch-file-from-branch " -- "
        larumbe/gite-work-tree "/" filename)))))


(defun larumbe/git-manual-branch-ediff-merge ()
  "Ediff manual inspection/merging on every file that has changed between two branches"
  (interactive)
  (let (changed-files)
    ;; First part is to find which files have changed between both branches
    (setq changed-files (larumbe/git-find-changed-files-between-branches))
    ;; An (optional) step would be to determine which of previous files require manual merging
    (setq changed-files
          (larumbe/git-exclude-files-before-ediff
           changed-files
           larumbe/git-branch-files-to-exclude-from-merge))
    ;; Last step would be to merge manually these files
    (larumbe/git-merge-all-files-between-branches changed-files)))


;;;; Repohome
(defun larumbe/repohome-magit-status ()
  "Perform magit-status with `git-dir' and `work-tree' changed accordingly"
  (interactive)
  (larumbe/repohome-reset-git-args)
  (setq magit-git-global-arguments (append magit-git-global-arguments (split-string larumbe/gite-args))) ; Append `gite' args
  (message "gite arguments set...")
  (magit-status larumbe/gite-work-tree))


;; https://emacs.stackexchange.com/questions/3022/reset-custom-variable-to-default-value-programmatically
(defun larumbe/repohome-reset-git-args ()
  "Resets git global arguments to switch between `gite' workspace and the rest"
  (interactive)
  (message "Git arguments reset!")
  (setq magit-git-global-arguments (eval (car (get 'magit-git-global-arguments 'standard-value)))))




;;; Xah Lee functions from ergoemacs.org tutorial
;;;; Bracket Movement
(defvar xah-brackets nil "string of left/right brackets pairs.")
(setq xah-brackets "()[]{}<>（）［］｛｝⦅⦆〚〛⦃⦄“”‘’‹›«»「」〈〉《》【】〔〕⦗⦘『』〖〗〘〙｢｣⟦⟧⟨⟩⟪⟫⟮⟯⟬⟭⌈⌉⌊⌋⦇⦈⦉⦊❛❜❝❞❨❩❪❫❴❵❬❭❮❯❰❱❲❳〈〉⦑⦒⧼⧽﹙﹚﹛﹜﹝﹞⁽⁾₍₎⦋⦌⦍⦎⦏⦐⁅⁆⸢⸣⸤⸥⟅⟆⦓⦔⦕⦖⸦⸧⸨⸩｟｠⧘⧙⧚⧛⸜⸝⸌⸍⸂⸃⸄⸅⸉⸊᚛᚜༺༻༼༽⏜⏝⎴⎵⏞⏟⏠⏡﹁﹂﹃﹄︹︺︻︼︗︘︿﹀︽︾﹇﹈︷︸")

(defvar xah-left-brackets '("(" "{" "[" "<" "〔" "【" "〖" "〈" "《" "「" "『" "“" "‘" "‹" "«" )
  "List of left bracket chars.")
(progn
;; make xah-left-brackets based on xah-brackets
  (setq xah-left-brackets '())
  (dotimes ($x (- (length xah-brackets) 1))
    (when (= (% $x 2) 0)
      (push (char-to-string (elt xah-brackets $x))
            xah-left-brackets)))
  (setq xah-left-brackets (reverse xah-left-brackets)))

(defvar xah-right-brackets '(")" "]" "}" ">" "〕" "】" "〗" "〉" "》" "」" "』" "”" "’" "›" "»")
  "list of right bracket chars.")
(progn
  (setq xah-right-brackets '())
  (dotimes ($x (- (length xah-brackets) 1))
    (when (= (% $x 2) 1)
      (push (char-to-string (elt xah-brackets $x))
            xah-right-brackets)))
  (setq xah-right-brackets (reverse xah-right-brackets)))

(defun xah-backward-left-bracket ()
  "Move cursor to the previous occurrence of left bracket.
The list of brackets to jump to is defined by `xah-left-brackets'.
URL `http://ergoemacs.org/emacs/emacs_navigating_keys_for_brackets.html'
Version 2015-10-01"
  (interactive)
  (search-backward-regexp (regexp-opt xah-left-brackets) nil t))

(defun xah-forward-right-bracket ()
  "Move cursor to the next occurrence of right bracket.
The list of brackets to jump to is defined by `xah-right-brackets'.
URL `http://ergoemacs.org/emacs/emacs_navigating_keys_for_brackets.html'
Version 2015-10-01"
  (interactive)
  (re-search-forward (regexp-opt xah-right-brackets) nil t))

(defun xah-goto-matching-bracket ()
  "Move cursor to the matching bracket.
If cursor is not on a bracket, call `backward-up-list'.
The list of brackets to jump to is defined by `xah-left-brackets' and `xah-right-brackets'.
URL `http://ergoemacs.org/emacs/emacs_navigating_keys_for_brackets.html'
Version 2016-11-22"
  (interactive)
  (if (nth 3 (syntax-ppss))
      (backward-up-list 1 'ESCAPE-STRINGS 'NO-SYNTAX-CROSSING)
    (cond
     ((eq (char-after) ?\") (forward-sexp))
     ((eq (char-before) ?\") (backward-sexp ))
     ((looking-at (regexp-opt xah-left-brackets))
      (forward-sexp))
     ((looking-back (regexp-opt xah-right-brackets) (max (- (point) 1) 1))
      (backward-sexp))
     (t (backward-up-list 1 'ESCAPE-STRINGS 'NO-SYNTAX-CROSSING)))))


;;;; Quote Movement
(defun xah-forward-quote-smart ()
  "Move cursor to the current or next string quote.
Place cursor at the position after the left quote.
Repeated call will find the next string.
URL `http://ergoemacs.org/emacs/emacs_navigating_keys_for_brackets.html'
Version 2016-11-22"
  (interactive)
  (let (($pos (point)))
    (if (nth 3 (syntax-ppss))
        (progn
          (backward-up-list 1 'ESCAPE-STRINGS 'NO-SYNTAX-CROSSING)
          (forward-sexp)
          (re-search-forward "\\\"" nil t))
      (progn (re-search-forward "\\\"" nil t)))
    (when (<= (point) $pos)
      (progn (re-search-forward "\\\"" nil t)))))

(defun xah-backward-quote ()
  "Move cursor to the previous occurrence of \".
If there are consecutive quotes of the same char, keep moving until none.
Returns `t' if found, else `nil'.
URL `http://ergoemacs.org/emacs/emacs_navigating_keys_for_brackets.html'
Version 2016-07-23"
  (interactive)
  (if (search-backward-regexp "\\\"+" nil t)
      (when (char-before) ; isn't nil, at beginning of buffer
        (while (char-equal (char-before) (char-after))
          (left-char)
          t))
    (progn
      (message "No more quotes before cursor.")
      nil)))


;;;; Text Selecting
(defun xah-select-text-in-quote ()
  "Select text between the nearest left and right delimiters.
Delimiters here includes the following chars: \"<>(){}[]“”‘’‹›«»「」『』【】〖〗《》〈〉〔〕（）
This command select between any bracket chars, not the inner text of a bracket. For example, if text is

 (a(b)c▮)

 the selected char is “c”, not “a(b)c”.

URL `http://ergoemacs.org/emacs/modernization_mark-word.html'
Version 2016-12-18"
  (interactive)
  (let (
        ($skipChars
         (if (boundp 'xah-brackets)
             (concat "^\"" xah-brackets)
           "^\"<>(){}[]“”‘’‹›«»「」『』【】〖〗《》〈〉〔〕（）"))
        $pos
        )
    (skip-chars-backward $skipChars)
    (setq $pos (point))
    (skip-chars-forward $skipChars)
    (set-mark $pos)))

(defun xah-select-line ()
  "Select current line. If region is active, extend selection downward by line.
URL `http://ergoemacs.org/emacs/modernization_mark-word.html'
Version 2017-11-01"
  (interactive)
  (if (region-active-p)
      (progn
        (forward-line 1)
        (end-of-line))
    (progn
      (end-of-line)
      (set-mark (line-beginning-position)))))

(defun xah-select-current-line ()
  "Select current line.
URL `http://ergoemacs.org/emacs/modernization_mark-word.html'
Version 2016-07-22"
  (interactive)
  (end-of-line)
  (set-mark (line-beginning-position)))

(defun xah-select-block ()
  "Select the current/next block of text between blank lines.
If region is active, extend selection downward by block.

URL `http://ergoemacs.org/emacs/modernization_mark-word.html'
Version 2017-11-01"
  (interactive)
  (if (region-active-p)
      (re-search-forward "\n[ \t]*\n" nil "move")
    (progn
      (skip-chars-forward " \n\t")
      (when (re-search-backward "\n[ \t]*\n" nil "move")
        (re-search-forward "\n[ \t]*\n"))
      (push-mark (point) t t)
      (re-search-forward "\n[ \t]*\n" nil "move"))))

(defun xah-select-current-block ()
  "Select the current block of text between blank lines.

URL `http://ergoemacs.org/emacs/modernization_mark-word.html'
Version 2017-07-02"
  (interactive)
  (progn
    (skip-chars-forward " \n\t")
    (when (re-search-backward "\n[ \t]*\n" nil "move")
      (re-search-forward "\n[ \t]*\n"))
    (push-mark (point) t t)
    (re-search-forward "\n[ \t]*\n" nil "move")))


(defun xah-extend-selection ()
  "Select the current word, bracket/quote expression, or expand selection.
Subsequent calls expands the selection.

when no selection,
• if cursor is on a bracket, select whole bracketed thing including bracket
• if cursor is on a quote, select whole quoted thing including quoted
• if cursor is on the beginning of line, select the line.
• else, select current word.

when there's a selection, the selection extension behavior is still experimental.
Roughly:
• if 1 line is selected, extend to next line.
• if multiple lines is selected, extend to next line.
• if a bracketed text is selected, extend to include the outer bracket. If there's no outer, select current line.

 to line, or bracket/quoted text,
or text block, whichever is the smallest.

URL `http://ergoemacs.org/emacs/modernization_mark-word.html'
Version 2017-01-15"
  (interactive)
  (if (region-active-p)
      (progn
        (let (($rb (region-beginning)) ($re (region-end)))
          (goto-char $rb)
          (cond
           ((looking-at "\\s(")
            (if (eq (nth 0 (syntax-ppss)) 0)
                (progn
                  (message "left bracket, depth 0.")
                  (end-of-line) ; select current line
                  (set-mark (line-beginning-position)))
              (progn
                (message "left bracket, depth not 0")
                (up-list -1 t t)
                (mark-sexp))))
           ((eq $rb (line-beginning-position))
            (progn
              (goto-char $rb)
              (let (($firstLineEndPos (line-end-position)))
                (cond
                 ((eq $re $firstLineEndPos)
                  (progn
                    (message "exactly 1 line. extend to next whole line." )
                    (forward-line 1)
                    (end-of-line)))
                 ((< $re $firstLineEndPos)
                  (progn
                    (message "less than 1 line. complete the line." )
                    (end-of-line)))
                 ((> $re $firstLineEndPos)
                  (progn
                    (message "beginning of line, but end is greater than 1st end of line" )
                    (goto-char $re)
                    (if (eq (point) (line-end-position))
                        (progn
                          (message "exactly multiple lines" )
                          (forward-line 1)
                          (end-of-line))
                      (progn
                        (message "multiple lines but end is not eol. make it so" )
                        (goto-char $re)
                        (end-of-line)))))
                 (t (error "logic error 42946" ))))))
           ((and (> (point) (line-beginning-position)) (<= (point) (line-end-position)))
            (progn
              (message "less than 1 line" )
              (end-of-line) ; select current line
              (set-mark (line-beginning-position))))
           (t (message "last resort" ) nil))))
    (progn
      (cond
       ((looking-at "\\s(")
        (message "left bracket")
        (mark-sexp)) ; left bracket
       ((looking-at "\\s)")
        (message "right bracket")
        (backward-up-list) (mark-sexp))
       ((looking-at "\\s\"")
        (message "string quote")
        (mark-sexp)) ; string quote
       ((and (eq (point) (line-beginning-position)) (not (looking-at "\n")))
        (message "beginning of line and not empty")
        (end-of-line)
        (set-mark (line-beginning-position)))
       ((or (looking-back "\\s_" 1) (looking-back "\\sw" 1))
        (message "left is word or symbol")
        (skip-syntax-backward "_w" )
        ;; (re-search-backward "^\\(\\sw\\|\\s_\\)" nil t)
        (mark-sexp))
       ((and (looking-at "\\s ") (looking-back "\\s " 1))
        (message "left and right both space" )
        (skip-chars-backward "\\s " ) (set-mark (point))
        (skip-chars-forward "\\s "))
       ((and (looking-at "\n") (looking-back "\n" 1))
        (message "left and right both newline")
        (skip-chars-forward "\n")
        (set-mark (point))
        (re-search-forward "\n[ \t]*\n")) ; between blank lines, select next text block
       (t (message "just mark sexp" )
          (mark-sexp))
       ;;
       ))))


;;;; Brackets
(defun xah-delete-backward-char-or-bracket-text ()
  "Delete backward 1 character, but if it's a \"quote\" or bracket ()[]{}【】「」 etc, delete bracket and the inner text, push the deleted text to `kill-ring'.

What char is considered bracket or quote is determined by current syntax table.

If `universal-argument' is called first, do not delete inner text.

URL `http://ergoemacs.org/emacs/emacs_delete_backward_char_or_bracket_text.html'
Version 2017-07-02"
  (interactive)
  (if (and delete-selection-mode (region-active-p))
      (delete-region (region-beginning) (region-end))
    (cond
     ((looking-back "\\s)" 1)
      (if current-prefix-arg
          (xah-delete-backward-bracket-pair)
        (xah-delete-backward-bracket-text)))
     ((looking-back "\\s(" 1)
      (progn
        (backward-char)
        (forward-sexp)
        (if current-prefix-arg
            (xah-delete-backward-bracket-pair)
          (xah-delete-backward-bracket-text))))
     ((looking-back "\\s\"" 1)
      (if (nth 3 (syntax-ppss))
          (progn
            (backward-char )
            (xah-delete-forward-bracket-pairs (not current-prefix-arg)))
        (if current-prefix-arg
            (xah-delete-backward-bracket-pair)
          (xah-delete-backward-bracket-text))))
     (t
      (delete-char -1)))))

(defun xah-delete-backward-bracket-text ()
  "Delete the matching brackets/quotes to the left of cursor, including the inner text.

This command assumes the left of point is a right bracket, and there's a matching one before it.

What char is considered bracket or quote is determined by current syntax table.

URL `http://ergoemacs.org/emacs/emacs_delete_backward_char_or_bracket_text.html'
Version 2017-07-02"
  (interactive)
  (progn
    (forward-sexp -1)
    (mark-sexp)
    (kill-region (region-beginning) (region-end))))

(defun xah-delete-backward-bracket-pair ()
  "Delete the matching brackets/quotes to the left of cursor.

After the command, mark is set at the left matching bracket position, so you can `exchange-point-and-mark' to select it.

This command assumes the left of point is a right bracket, and there's a matching one before it.

What char is considered bracket or quote is determined by current syntax table.

URL `http://ergoemacs.org/emacs/emacs_delete_backward_char_or_bracket_text.html'
Version 2017-07-02"
  (interactive)
  (let (( $p0 (point)) $p1)
    (forward-sexp -1)
    (setq $p1 (point))
    (goto-char $p0)
    (delete-char -1)
    (goto-char $p1)
    (delete-char 1)
    (push-mark (point) t)
    (goto-char (- $p0 2))))

(defun xah-delete-forward-bracket-pairs ( &optional @delete-inner-text-p)
  "Delete the matching brackets/quotes to the right of cursor.
If *delete-inner-text-p is true, also delete the inner text.

After the command, mark is set at the left matching bracket position, so you can `exchange-point-and-mark' to select it.

This command assumes the char to the right of point is a left bracket or quote, and have a matching one after.

What char is considered bracket or quote is determined by current syntax table.

URL `http://ergoemacs.org/emacs/emacs_delete_backward_char_or_bracket_text.html'
Version 2017-07-02"
  (interactive)
  (if @delete-inner-text-p
      (progn
        (mark-sexp)
        (kill-region (region-beginning) (region-end)))
    (let (($pt (point)))
      (forward-sexp)
      (delete-char -1)
      (push-mark (point) t)
      (goto-char $pt)
      (delete-char 1))))
