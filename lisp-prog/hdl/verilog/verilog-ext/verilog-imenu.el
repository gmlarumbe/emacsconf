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
;;     But that would require use of `delete-comments-from-buffer' (very slow) and `undo', with some issues programatically.
;;     That would need  to be done with `verilog-ext-find-module-instance-fwd' as well.
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
;;         (setq imenu-prev-index-position-function 'verilog-ext-imenu-prev-index-position-function)
;;         (setq imenu-extract-index-name-function 'verilog-ext-imenu-extract-index-name)
;;
;;       Check `verilog-ext-imenu-prev-index-position-function' and `verilog-ext-imenu-extract-index-name'
;;
;;   3 - Redefine `imenu-create-index-function' to make a custom more complex alist (e.g a tree recursively for nested classes)
;;       This is the most complex and the one used in python mode.  Check `verilog-ext-imenu-index'.
;;
;;; Code:

(require 'imenu)
(require 'verilog-mode)
(require 'verilog-navigation)
(require 'verilog-rx)

;;;; Variables
(defvar verilog-ext-imenu-generic-expression
      `((nil                ,verilog-ext-imenu-top-re 2)
        ("*Localparams*"    ,verilog-ext-imenu-localparam-re 2)
        ("*Defines*"        ,verilog-ext-imenu-define-re 1)
        ("*Assigns*"        ,verilog-ext-imenu-assign-re 1)
        ("*Generates*"      ,verilog-ext-imenu-generate-re 1)
        ("*Always blocks*"  ,verilog-ext-imenu-always-re 4)
        ("*Initial blocks*" ,verilog-ext-imenu-initial-re 3)
        ("*Task/Func*"      verilog-ext-find-task-function-outside-class-bwd 2)
        ("*Instances*"      verilog-ext-find-module-instance-bwd 1)))  ;; Use capture group index 2 if want to get instance name instead


;;;; Tree building
(defun verilog-ext-imenu-format-class-item-label (type name)
  "Return Imenu label for single node using TYPE and NAME."
  (let (short-type)
    (setq short-type
          (pcase type
            ("task"      "T")
            ("function"  "F")
            (_           type)))
    (format "%s (%s)" name short-type)))


(defun verilog-ext-imenu-class-put-parent (type name pos tree &optional add)
  "Create parent tag with TYPE and NAME.
If optional ADD, add the parent with TYPE, NAME and POS to the TREE."
  (let* ((label      (funcall #'verilog-ext-imenu-format-class-item-label type name))
         (jump-label label))
    (if (not tree)
        (cons label pos)
      (if add
          (cons label (cons (cons jump-label pos) tree))
        (cons label tree)))))


(defun verilog-ext-imenu-build-class-tree (&optional tree)
  "Build the imenu alist TREE.
Coded to work with verification files with CLASSES and METHODS.
Adapted from `python-mode' imenu build-tree function."
  (save-restriction
    (narrow-to-region (point-min) (point))
    (let* ((pos
            (progn
              (verilog-ext-find-class-bwd)
              (verilog-forward-sexp)
              (verilog-ext-find-task-function-class-bwd)))
           type
           (name (when (and pos (or (looking-at verilog-ext-task-re)
                                    (looking-at verilog-ext-function-re)
                                    (looking-at verilog-ext-class-re)))
                   (setq type (match-string-no-properties 1))
                   (match-string-no-properties 2)))
           (label (when name
                    (funcall #'verilog-ext-imenu-format-class-item-label type name))))
      (cond ((not pos)
             nil)
            ((looking-at verilog-ext-class-re)
             (verilog-ext-imenu-class-put-parent type name pos tree nil)) ; Do not want class imenu redundancy (tags+entries)
            (t
             (verilog-ext-imenu-build-class-tree
              (if (or (looking-at verilog-ext-task-re)
                      (looking-at verilog-ext-function-re))
                  (cons (cons label pos) tree)
                (cons
                 (verilog-ext-imenu-build-class-tree
                  (list (cons label pos)))
                 tree))))))))


(defun verilog-ext-imenu-classes-index ()
  "Obtain entries of tasks/functions within classes.

INFO: Tasks/functions outside classes are obtained with a custom function search
in the generic imenu-generic-function stage.
INFO: Detection of nested classes is unsupported and leads to bad detection of class
tasks/functions."
  (save-excursion
    (goto-char (point-max))
    (let ((index)
          (tree))
      (while (setq tree (verilog-ext-imenu-build-class-tree))
        (setq index (cons tree index)))
      (when index
        (list (cons "Classes" index))))))



(defun verilog-ext-imenu-index ()
  "Custom index builder for Verilog Imenu.
First creates a list with the entries that correspond to *Classes* tag by
performing a recursive search.  Afterwards it appends the contents of the
list obtained by using the imenu generic function."
  (append
   (verilog-ext-imenu-classes-index)
   (imenu--generic-function verilog-ext-imenu-generic-expression)))



(defun verilog-ext-imenu-hide-all (&optional first)
  "Hides all the blocks @ Imenu-list buffer.
If optional FIRST is used, then shows first block (Verilog *instances/interfaces*)"
  (if (string-equal major-mode "imenu-list-major-mode")
      (progn
        (goto-char (point-min))
        (while (< (point) (point-max))
          (hs-hide-block)
          (line-move-visual 1))
        (goto-char (point-min))
        ;; If there is an optional argument, unfold first block
        (when first
          (hs-show-block)))
    (message "Not in imenu-list mode !!")))



;;;###autoload
(defun verilog-ext-imenu ()
  "Wrapper interactive Imenu function for Verilog mode."
  (interactive)
  (setq imenu-create-index-function #'verilog-ext-imenu-index)
  (imenu-list)
  (verilog-ext-imenu-hide-all t))





;;;; Provide
(provide 'verilog-imenu)

;;; verilog-imenu.el ends here
