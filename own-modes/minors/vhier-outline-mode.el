;;; vhier-outline-mode.el --- Verilog Hierarchy  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Navigate with `outline-minor-mode' through extracted Verilog-Perl hierarchy.
;; Author: Larumbe
;; Date: 3/3/2018
;;
;;; Code:


;;;###autoload
(define-minor-mode vhier-outline-mode
  "Frontend for Verilog-Perl `vhier' processed output for outline-minor-mode with outshine visualization."
  :lighter " vH"
  :keymap
  '(;; Fetched from https://www.emacswiki.org/emacs/OutlineMinorMode
    ;; HIDE
    ("k" . vhier-hide-sublevels)      ; Hide everything but the top-level headings
    ("K" . outline-hide-other)        ; Hide other branches
    ;; SHOW
    ("a" . outline-show-all)          ; Show (expand) everything
    ("i" . outline-show-children)     ; Show this heading's immediate child sub-headings
    ("I" . outline-show-branches)     ; Show all sub-headings under this heading
    ;; MOVE
    ("u" . vhier-up-heading)               ; Up
    ("n" . vhier-next-visible-heading)     ; Next
    ("p" . vhier-previous-visible-heading) ; Previous
    ("f" . vhier-forward-same-level)       ; Forward - same level
    ("b" . vhier-backward-same-level)      ; Backward - same level
    ;; JUMP
    ("j" . vhier-outline-jump-to-file)     ; INFO: Added by Larumbe
    ))

;; Still needs to be polished...
;; For example: if added imenu-list, it would parse the vhier-outline buffer instead of the verilog one.
;; Moreover, since there is delay in finding the tag, if set a read-only it would affect the vhier-outlin buffer as well...
(defun vhier-outline-jump-to-file ()
  "Jump to file at cursor on hierarchy.v file."
  (interactive)
  (when (not vhier-outline-mode)
    (error "Vhier mode not enabled on current buffer"))
  (when (not (executable-find "global"))
    (error "Vhier mode requires global to work"))
  (when (not (ggtags-find-project))
    (error "Associated GTAGS file not found.  Make sure hierarchy file is in the same folder as its matching GTAGS file"))
  (delete-other-windows)
  (split-window-right)
  (shrink-window-horizontally 60)
  (other-window 1)
  (end-of-line)
  (ggtags-find-tag-dwim (thing-at-point 'symbol t)))


(defun vhier-previous-visible-heading ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-previous-visible-heading)
  (skip-chars-forward "/ *"))


(defun vhier-next-visible-heading ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-next-visible-heading)
  (skip-chars-forward "/ *"))


(defun vhier-up-heading ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-up-heading)
  (skip-chars-forward "/ *"))


(defun vhier-forward-same-level ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-forward-same-level)
  (skip-chars-forward "/ *"))


(defun vhier-backward-same-level ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (call-interactively #'outline-backward-same-level)
  (skip-chars-forward "/ *"))


(defun vhier-hide-sublevels ()
  "Move through headings and point at the beginning of the tag.
This way gtags can be easily integrated in the workflow."
  (interactive)
  (beginning-of-line)
  (call-interactively #'outline-hide-sublevels)
  (skip-chars-forward "/ *"))


(provide 'vhier-outline-mode)

;;; vhier-outline-mode.el ends here
