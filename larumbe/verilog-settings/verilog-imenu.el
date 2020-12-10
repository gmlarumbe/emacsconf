;;; verilog-imenu.el --- Verilog Imenu  -*- lexical-binding: t -*-
;;; Commentary:
;; INFO: Issues with instance detection
;;
;; 1 - Imenu must work on current buffer.  Creates an alist of (elements . #<mark pos at buffer>)
;;     Therefore, must be executed on the buffer on which it will have the effect (cannot use with-temp-buffer in a buffer with no comments
;;     and trying to reassociate afterwards)
;;
;; 2 - Imenu just ignores comments starting at the beginning of line, not inline comments that might be within the instance regexp.
;;
;; 3 - It is not possible to work with (with-comments-hidden) since it makes comments invisible, and imenu ignores invisible characters
;;     by looking for the next non-invisible regexp, since `re-search-forward' cannot ignore invisible, just skip to the next.
;;     The problem is that instances regexp are multiline, and if an unexpected character such as comment with semicolon appears, it won't
;;     be recognized, and there wont be any chance of skip to the next.  It will be missed.
;;
;; 4 - A first solution seemed to be executing `imenu' after erasing comments from current buffer and then returning it to its initial state
;;     But that would require use of `larumbe/delete-comments-from-buffer' (very slow) and `undo', with some issues programatically.
;;     That would need  to be done with `larumbe/find-verilog-module-instance-fwd' as well.
;;     The profit would not be worth the effort due to an extreme fall in performance.
;;
;; 5 - Best solution is to create a function that checks if there are problematic regexps in a verilog file, and set is as a hook every time
;;     a file is opened, or Imenu is executed.
;;
;;
;; INFO: There are 3 ways of creating the index-alist for Imenu mode (from simpler to more complex):
;;
;;   1 - Define `imenu-generic-expression' (categories and regexps).  This is the most common and default one.
;;
;;   2 - Define `imenu-prev-index-position-function' and `imenu-extract-index-name-function'.
;;       If these variables are defined, the imenu-list creation function uses them to find the tags.  For example:
;;
;;         (setq imenu-prev-index-position-function 'larumbe/verilog-imenu-prev-index-position-function)
;;         (setq imenu-extract-index-name-function 'larumbe/verilog-imenu-extract-index-name)
;;
;;       Check `larumbe/verilog-imenu-prev-index-position-function' and `larumbe/verilog-imenu-extract-index-name'
;;
;;   3 - Redefine `imenu-create-index-function' to make a custom more complex alist (e.g a tree recursively for nested classes)
;;       This is the most complex and the one used in python mode.  Check `larumbe/verilog-imenu-index'.
;;
;;; Code:


;; Search by regexp: Used as regexps in `larumbe/verilog-imenu-generic-expression'
(defvar larumbe/verilog-imenu-top-re        "^\\s-*\\(?1:connectmodule\\|m\\(?:odule\\|acromodule\\)\\|p\\(?:rimitive\\|rogram\\|ackage\\)\\)\\(\\s-+automatic\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defvar larumbe/verilog-imenu-localparam-re "^\\s-*localparam\\(?1:\\s-+\\(logic\\|bit\\|int\\|integer\\)\\s-*\\(\\[.*\\]\\)?\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defvar larumbe/verilog-imenu-define-re     "^\\s-*`define\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defvar larumbe/verilog-imenu-assign-re     "^\\s-*assign\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defvar larumbe/verilog-imenu-generate-re   "^\\s-*generate[ \t\n]*\\(?1:.*\\)")
(defvar larumbe/verilog-imenu-always-re     "^\\s-*always\\(_ff\\|_comb\\|_latch\\)?\\s-*\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")
(defvar larumbe/verilog-imenu-initial-re    "^\\s-*initial\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")
;; Search by function: Used for functions that will be passed as an argument of `larumbe/verilog-imenu-generic-expression'
(defvar larumbe/verilog-task-re     "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*task\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?2:[A-Za-z_][A-Za-z0-9_:]+\\)")
(defvar larumbe/verilog-function-re "\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*function\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?:\\w+\\s-+\\)?\\(?:\\(?:un\\)signed\\s-+\\)?\\(?2:[A-Za-z_][A-Za-z0-9_:]+\\)")
(defvar larumbe/verilog-class-re    "\\(?1:\\(?:\\(?:virtual\\|interface\\)\\s-+\\)?class\\)\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)")
(defvar larumbe/verilog-top-re      "\\(?1:package\\|program\\|module\\)\\(\\s-+automatic\\)?\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)")

(defvar larumbe/verilog-imenu-generic-expression
      `((nil                ,larumbe/verilog-imenu-top-re 2)
        ("*Localparams*"    ,larumbe/verilog-imenu-localparam-re 2)
        ("*Defines*"        ,larumbe/verilog-imenu-define-re 1)
        ("*Assigns*"        ,larumbe/verilog-imenu-assign-re 1)
        ("*Generates*"      ,larumbe/verilog-imenu-generate-re 1)
        ("*Always blocks*"  ,larumbe/verilog-imenu-always-re 4)
        ("*Initial blocks*" ,larumbe/verilog-imenu-initial-re 3)
        ("*Task/Func*"      larumbe/find-verilog-task-function-outside-class-bwd 2)
        ("*Instances*"      larumbe/find-verilog-module-instance-bwd 1)))  ;; Use capture group index 2 if want to get instance name instead


(defun larumbe/verilog-imenu-format-class-item-label (type name)
  "Return Imenu label for single node using TYPE and NAME."
  (let (short-type)
    (setq short-type
          (pcase type
            ("task"      "T")
            ("function"  "F")
            (_           type)))
    (format "%s (%s)" name short-type)))


(defun larumbe/verilog-imenu-class-put-parent (type name pos tree &optional add)
  "Create parent tag with TYPE and NAME.
If optional ADD, add the parent with TYPE, NAME and POS to the TREE."
  (let* ((label      (funcall #'larumbe/verilog-imenu-format-class-item-label type name))
         (jump-label label))
    (if (not tree)
        (cons label pos)
      (if add
          (cons label (cons (cons jump-label pos) tree))
        (cons label tree)))))


(defun larumbe/verilog-imenu-build-class-tree (&optional tree)
  "Build the imenu alist TREE.
Coded to work with verification files with CLASSES and METHODS.
Adapted from `python-mode' imenu build-tree function."
  (save-restriction
    (narrow-to-region (point-min) (point))
    (let* ((pos
            (progn
              (larumbe/find-verilog-class-bwd)
              (verilog-forward-sexp)
              (larumbe/find-verilog-task-function-class-bwd)))
           type
           (name (when (and pos (or (looking-at larumbe/verilog-task-re)
                                    (looking-at larumbe/verilog-function-re)
                                    (looking-at larumbe/verilog-class-re)))
                   (setq type (match-string-no-properties 1))
                   (match-string-no-properties 2)))
           (label (when name
                    (funcall #'larumbe/verilog-imenu-format-class-item-label type name))))
      (cond ((not pos)
             nil)
            ((looking-at larumbe/verilog-class-re)
             (larumbe/verilog-imenu-class-put-parent type name pos tree nil)) ; Do not want class imenu redundancy (tags+entries)
            (t
             (larumbe/verilog-imenu-build-class-tree
              (if (or (looking-at larumbe/verilog-task-re)
                      (looking-at larumbe/verilog-function-re))
                  (cons (cons label pos) tree)
                (cons
                 (larumbe/verilog-imenu-build-class-tree
                  (list (cons label pos)))
                 tree))))))))


(defun larumbe/verilog-imenu-classes-index ()
  "Obtain entries of tasks/functions within classes.

INFO: Tasks/functions outside classes are obtained with a custom function search
in the generic imenu-generic-function stage.
INFO: Detection of nested classes is unsupported and leads to bad detection of class
tasks/functions."
  (save-excursion
    (goto-char (point-max))
    (let ((index)
          (tree))
      (while (setq tree (larumbe/verilog-imenu-build-class-tree))
        (setq index (cons tree index)))
      (when index
        (list (cons "Classes" index))))))



(defun larumbe/verilog-imenu-index ()
  "Custom index builder for Verilog Imenu.
First creates a list with the entries that correspond to *Classes* tag by
performing a recursive search.  Afterwards it appends the contents of the
list obtained by using the imenu generic function."
  (append
   (larumbe/verilog-imenu-classes-index)
   (imenu--generic-function larumbe/verilog-imenu-generic-expression)))


(defun larumbe/verilog-imenu ()
"Wrapper interactive Imenu function for Verilog mode.
Checks if there is an instance with semicolon in mutiline comments of parameters."
  (interactive)
  (let (issue)
    (setq imenu-create-index-function #'larumbe/verilog-imenu-index)
    (setq issue (larumbe/verilog-find-semicolon-in-instance-comments))
    (imenu-list)
    (larumbe/verilog-imenu-hide-all t)
    (when issue
      (error "Imenu DANGER!: semicolon in comment instance!!"))))


(defun larumbe/verilog-imenu-hide-all (&optional first)
  "Hides all the blocks @ Imenu-list buffer.
If optional FIRST is used, then shows first block (Verilog *instances/interfaces*)"
  (interactive)
  (if (string-equal major-mode "imenu-list-major-mode")
      (progn
        (goto-char (point-min))
        (while (< (point) (point-max))
          (hs-hide-block)
          (forward-line))
        (beginning-of-buffer)
        ;; If there is an optional argument, unfold first block
        (when first
          (hs-show-block)))
    (message "Not in imenu-list mode !!")))


;; DANGER: These two methods were insufficient to implement Imenu with functions/tasks within classes.
;; Code kept in case it is used in the future to add something new tag.
(defun larumbe/verilog-imenu-prev-index-position-function ()
  "Function to search backwards in the buffer for Imenu alist generation."
  (larumbe/find-verilog-module-instance-bwd))

(defun larumbe/verilog-imenu-extract-index-name ()
  "Function to extract the tag."
  (verilog-forward-syntactic-ws)
  (thing-at-point 'symbol t))


(provide 'verilog-imenu)

;;; verilog-imenu.el ends here
