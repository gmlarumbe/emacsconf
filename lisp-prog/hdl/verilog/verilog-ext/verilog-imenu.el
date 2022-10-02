;;; verilog-imenu.el --- Verilog Imenu  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(require 'verilog-mode)
(require 'imenu)
(require 'hideshow)
(require 'verilog-utils)

;;;; Imenu-regexp
(defconst verilog-ext-imenu-top-re        "^\\s-*\\(?1:connectmodule\\|m\\(?:odule\\|acromodule\\)\\|p\\(?:rimitive\\|rogram\\|ackage\\)\\)\\(\\s-+automatic\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-localparam-re "^\\s-*localparam\\(?1:\\s-+\\(logic\\|bit\\|int\\|integer\\)\\s-*\\(\\[.*\\]\\)?\\)?\\s-+\\(?2:[a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-define-re     "^\\s-*`define\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-assign-re     "^\\s-*assign\\s-+\\([a-zA-Z0-9_.:]+\\)")
(defconst verilog-ext-imenu-generate-re   "^\\s-*generate[ \t\n]*\\(?1:.*\\)")
(defconst verilog-ext-imenu-always-re     "^\\s-*always\\(_ff\\|_comb\\|_latch\\)?\\s-*\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")
(defconst verilog-ext-imenu-initial-re    "^\\s-*initial\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)")


;;;; Variables
(defvar verilog-ext-imenu-generic-expression
      `(;; Search by regexp
        (nil                ,verilog-ext-imenu-top-re 2)
        ("*Localparams*"    ,verilog-ext-imenu-localparam-re 2)
        ("*Defines*"        ,verilog-ext-imenu-define-re 1)
        ("*Assigns*"        ,verilog-ext-imenu-assign-re 1)
        ("*Generates*"      ,verilog-ext-imenu-generate-re 1)
        ("*Always blocks*"  ,verilog-ext-imenu-always-re 4)
        ("*Initial blocks*" ,verilog-ext-imenu-initial-re 3)
        ;; Search by function
        ("*Task/Func*"      verilog-ext-imenu-find-task-function-outside-class-bwd 2)
        ("*Instances*"      verilog-ext-find-module-instance-bwd 1)))  ;; Use capture group index 2 to get instance name



;;;; Utility
(defun verilog-ext-imenu-find-task-function-outside-class-bwd ()
  "Meant to be used for Imenu class entry."
  (let ((tf-re "\\<\\(task\\|function\\)\\>")
        found pos)
    (save-excursion
      (while (and (not found)
                  (verilog-re-search-backward tf-re nil t))
        (when (and (or (looking-at verilog-ext-task-re) ; INFO: Will start looking from the task/function part, without the static/pure/virtual/local/protected
                       (looking-at verilog-ext-function-re))
                   (not (verilog-ext-point-inside-block-p 'class)))
          (setq found t)
          (setq pos (point)))))
    (when found
      (goto-char pos))))


;;;; Tree building
(defun verilog-ext-imenu-format-class-item-label (type name)
  "Return Imenu label for single node using TYPE and NAME."
  (let (short-type)
    (setq short-type (pcase type
                       ("task"     "T")
                       ("function" "F")
                       (_          type)))
    (format "%s (%s)" name short-type)))


(defun verilog-ext-imenu-class-put-parent (type name pos tree &optional add)
  "Create parent tag with TYPE and NAME.
If optional ADD, add the parent with TYPE, NAME and POS to the TREE."
  (let* ((label (funcall #'verilog-ext-imenu-format-class-item-label type name))
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
    (let* ((pos (progn
                  (verilog-re-search-backward verilog-ext-class-re nil t)
                  (verilog-forward-sexp)
                  (verilog-re-search-backward "\\<\\(function\\|task\\|class\\)\\>" nil t)))
           type
           (name (when (and pos
                            (or (looking-at verilog-ext-task-re)
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
INFO: Detection of nested classes is unsupported and leads to bad detection of
class tasks/functions."
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
  (append (verilog-ext-imenu-classes-index)
          (imenu--generic-function verilog-ext-imenu-generic-expression)))


(defun verilog-ext-imenu-hook ()
  ""
  (setq-local imenu-create-index-function #'verilog-ext-imenu-index))



;;;; Imenu-list
(defun verilog-ext-imenu-hide-all (&optional first)
  "Hides all the blocks @ Imenu-list buffer.
If optional FIRST is used, then shows first block
(Verilog *instances/interfaces*)"
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
(defun verilog-ext-imenu-list ()
  "Wrapper interactive Imenu function for Verilog mode."
  (interactive)
  (imenu-list)
  (verilog-ext-imenu-hide-all t))



;;;; Setup
(add-hook 'verilog-mode-hook #'verilog-ext-imenu-hook)


;;;; Provide
(provide 'verilog-imenu)

;;; verilog-imenu.el ends here
