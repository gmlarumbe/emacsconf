;;; modi-functions.el --- Kaushal Modi various functions  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defvar modi/rwins-max 100
  "Default maximum number of replacements.")

(defvar modi/rwins-incr 1
  "Default number by which the number suffixes will increment in the
replacements.")

;;;###autoload
(defun modi/replace-with-incr-num-suffix (start)
  "Replace selected region/symbol at point with incrementing number suffixes.

If START is non-nil, the replacements will be suffixes with the START number
and increment by 1 on each replacement.

If START is nil and if the selected region or symbol already ends in a number,
the replacements will use that number as the START number.

If START is nil and if the selected region or symbol does NOT end in a number,
the replacements will use 1 as the START number.

`modi/rwins-max' controls the maximum number till which the suffix number
increments. After the max number is reached, the suffixes will restart from
START (behavior of `map-query-replace-regexp').

`modi/rwins-incr' controls the increments between the number suffixes in
consecutive replacements.

  Example:
  Initial text:
     Here3 Here3 Here3 Here3 Here3
  After replacement text:
     Here3 Here4 Here5 Here6 Here7

Note that the selected region cannot contain any spaces."
  (interactive "p")
  (let (raw-str beg non-number-str to-strings)
    (cond ((use-region-p)
           (setq raw-str (buffer-substring-no-properties
                          (region-beginning) (region-end)))
           (setq beg (region-beginning)))
          ((symbol-at-point)
           (setq raw-str (substring-no-properties
                          (symbol-name (symbol-at-point))))
           (setq beg (car (bounds-of-thing-at-point 'symbol)))))
    (if (string-match "\\b\\(\\w*?\\)\\([0-9]+\\)$" raw-str)
        (progn
          (setq non-number-str (match-string-no-properties 1 raw-str))
          (when (null current-prefix-arg)
            (setq start (string-to-number (match-string-no-properties 2 raw-str)))))
      (setq non-number-str raw-str))
    ;; http://www.gnu.org/software/emacs/manual/html_node/elisp/Mapping-Functions.html
    (setq to-strings (mapconcat (lambda (x) (concat non-number-str (number-to-string x)))
                                (number-sequence
                                 start
                                 (+ start (* modi/rwins-incr (1- modi/rwins-max)))
                                 modi/rwins-incr)
                                " "))
    (goto-char beg) ; Go to the start of the selection/symbol
    (map-query-replace-regexp (regexp-quote raw-str) to-strings)))



;; http://emacs.stackexchange.com/q/7519/115
;;;###autoload
(defun modi/pull-up-line ()
  "Join the following line onto the current one.

This is analogous to \\[move-end-of-line] followed by
\\[delete-foward], or \\[universal-argument] \\[delete-indentation],
or \\[universal-argument] \\[join-line].

If the current line is a comment and the pulled-up line is also a
comment, remove the leading comment characters from that line."
  (interactive)
  (join-line -1)
  (when (nth 4 (syntax-ppss))           ;If the current line is a comment
    ;; Remove comment prefix chars from the pulled-up line if present.
    (save-excursion
      ;; Delete all comment-start and space characters, one at a time.
      (while (looking-at (concat "\\s<"  ;Comment-start char as per syntax table
                                 "\\|" (substring comment-start 0 1) ;First char of `comment-start'
                                 "\\|" "[[:blank:]]"))               ;Extra spaces
        (delete-forward-char 1))
      (insert-char ? ))))               ;Insert space



;; Example:
;; (modi/search-replace-pairs '(("larumbe/" . "someone/") ("modi/" . "kmodi/")))
;;;###autoload
(defun modi/search-replace-pairs (sr-pairs)
  "Search/replace in the buffer/region using SR-PAIRS.
SR-PAIRS is a list of cons (SEARCH-REGEX . REPLACE-EXPR) where
the cons elements are strings."
  (let ((cnt 0)
        (beg (if (use-region-p) (region-beginning) (point-min)))
        (end (if (use-region-p) (region-end) (point-max))))
    (dolist (pair sr-pairs)
      (let ((search-regex (car pair))
            (replace-expr (cdr pair)))
        (save-restriction
          (narrow-to-region beg end)
          (save-excursion
            (goto-char (point-min))
            (while (re-search-forward search-regex nil :noerror)
              (replace-match replace-expr)
              (cl-incf cnt))))))
    (message "Finished %d replacements" cnt)))




(provide 'modi-functions)

;;; modi-functions.el ends here
