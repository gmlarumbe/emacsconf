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
  "Kill all buffers"
  (interactive)
  (mapc #'kill-buffer (buffer-list)))

(defun only-current-buffer ()
  "Kill all buffers except active one."
  (interactive)
  (mapc #'kill-buffer (cdr (buffer-list (current-buffer)))))

(defun buffer-mode (&optional buffer)
  "Returns the major mode associated with a buffer."
  (let (buf)
    (if buffer
        (setq buf buffer)
      (setq buf (current-buffer)))
    (with-current-buffer buf
      major-mode)))

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


(defun file-title ()
  "Return file title; eg returns asdf for /otp/asdf.txt ."
  (file-name-sans-extension(file-name-nondirectory (buffer-file-name))))


(defun larumbe/kill-current-buffer ()
  "Kill current buffer without confirmation.(buffer-name) defaults to current-buffer name"
  (interactive)
  (kill-buffer (buffer-name)))


(defun larumbe/load-file-current-buffer ()
  "Load current buffer .el file "
  (interactive)
  (load-file buffer-file-name))


(defun larumbe/revert-buffer-no-confirm ()
  "Revert current buffer without asking"
  (interactive)
  (revert-buffer nil t t))


(defun larumbe/current-buffer-to-file (out-file)
  "Export current buffer to output-file passed as parameter.
Can be called interactively or not.
It was first thought for exporting SCons compilations."
  (interactive "FEnter output path: "
               (setq out-file s))
  (append-to-file (point-min) (point-max) out-file))


(defun larumbe/pwd-to-kill-ring (&optional no-line)
  "Copy current file path to kill-ring.
If optional NO_LINE is given, then do not copy line to kill ring"
  (interactive "P")
  (let (file-name)
    (if no-line
        (setq file-name (buffer-file-name))
      (setq file-name (concat (buffer-file-name) ":" (format "%s" (line-number-at-pos)))))
    (kill-new file-name)
    (message (buffer-file-name))))


;;; Navigation
(defun my-isearch-yank-word-or-char-from-beginning ()
  "Move to beginning of word before yanking word in isearch-mode.
Make C-s C-w and C-r C-w act like Vim's g* and g#, keeping Emacs'
C-s C-w [C-w] [C-w]... behaviour. "
  (interactive)
  ;; Making this work after a search string is entered by user
  ;; is too hard to do, so work only when search string is empty.
  (if (= 0 (length isearch-string))
      (beginning-of-thing 'word))
  (isearch-yank-word-or-char)
  ;; Revert to 'isearch-yank-word-or-char for subsequent calls
  (substitute-key-definition #'my-isearch-yank-word-or-char-from-beginning
                             #'isearch-yank-word-or-char
                             isearch-mode-map))


(defun forward-same-indent ()
  "Move forward to next line with same indent (copied from `vhdl-mode').
DANGER: Comment needs to be substituted from '--' to  mode-specific comment."
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
  "Move backward to previous line with same indent (copied from `vhdl-mode').
DANGER: Comment needs to be substituted from '--' to  mode-specific comment."
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


(defun larumbe/find-file-at-point ()
  "Wrapper for `ffap' without asking for the file."
  (interactive)
  (let ((file (thing-at-point 'filename)))
    (if (file-exists-p file)
        (progn
          (xref-push-marker-stack)
          (ffap file))
      (error "File \"%s\" does not exist (check point or current path)" file))))


(defun larumbe/pop-to-previous-mark ()
  "Pop to previous mark"
  (interactive)
  (set-mark-command 4))


;;; Editing
(defun duplicate-line()
  (interactive)
  (move-beginning-of-line 1)
  (kill-line)
  (yank)
  (open-line 1)
  (next-line 1)
  (yank)
  (move-beginning-of-line 1))


(defun larumbe/copy-region-or-symbol-at-point ()
  (interactive)
  (let ((symbol (thing-at-point 'symbol t)))
    (if (use-region-p)
        (call-interactively #'kill-ring-save)
      (progn
        (kill-new symbol)
        (message symbol)))))


(defun larumbe/delete-comments-from-buffer ()
  "Delete comments from buffer without moving them to the kill ring.

Fetched from https://emacs.stackexchange.com/questions/5441/function-to-delete-all-comments-from-a-buffer-without-moving-them-to-kill-ring "
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


;;; Lists/strings/files/directories
(defun read-lines (filePath)
  "Return a list of lines of a file at filePath."
  (with-temp-buffer
    (insert-file-contents filePath)
    (split-string (buffer-string) "\n" t)))


(defun print-elements-of-list (list)
  "Print each element of LIST on a line of its own.

https://www.gnu.org/software/emacs/manual/html_node/eintr/print_002delements_002dof_002dlist.html "
  (while list
    (print (car list))
    (setq list (cdr list))))


(defun larumbe/print-elements-of-list-of-strings (list-of-strings)
  "Print each element of LIST-OF-STRINGS on a line of its own."
  (let (return-string)
    (while list-of-strings
      (setq return-string (concat return-string (message "%s\n" (car list-of-strings))))
      (setq list-of-strings (cdr list-of-strings)))
    (message "%s" return-string)))


(defun get-string-from-file (filePath)
  "Return filePath's file content as a string.

http://ergoemacs.org/emacs/elisp_read_file_content.html"
  (with-temp-buffer
    (insert-file-contents filePath)
    (buffer-string)))


(defun replace-in-string (what with in)
  "Replace WHAT to WITH in string IN.

https://stackoverflow.com/questions/17325713/looking-for-a-replace-in-string-function-in-elisp"
  (replace-regexp-in-string (regexp-quote what) with in nil 'literal))


(defun larumbe/directory-files-recursively-to-file (base-dir file re &optional append exclude-re)
  "Retrieve every file matching regexp RE of a specified BASE-DIR to output FILE.
If optional APPEND is set to non-nil, append result to existing FILE.
Otherwise, overwrite old existing FILE with new results.
If optional EXCLUDE-RE is set, delete paths with that regexp from generated file."
  (let (buf)
    (save-window-excursion
      (with-temp-buffer
        (mapc
         (lambda (dir) (insert (mapconcat #'identity (directory-files-recursively dir re) "\n")))
         (list base-dir))
        ;; Append to existing file
        (when (and (file-exists-p (concat base-dir file))
                   append)
          (setq buf (current-buffer))
          (find-file file)
          (end-of-buffer)
          (newline)
          (insert-buffer-substring buf))
        ;; Filter according to optional parameter
        (when exclude-re
          (flush-lines exclude-re (point-min) (point-max)))
        (write-file file)))))


(defun larumbe/directory-diff-recursive (dir1 dir2 out-file)
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



;;; Misc
(defun source (filename)
  "Update environment variables from a shell source file.

https://gist.github.com/ffevotte/9345586#file-gistfile1-el"
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
