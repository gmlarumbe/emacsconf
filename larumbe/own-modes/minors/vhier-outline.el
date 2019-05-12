;;; Description
;; Minor Mode created by Larumbe to navigate with outline-minor-mode through Verilog-Perl created Hierarchy
;; Author: Larumbe
;; Date: 3/3/2018
;; Still in progress...

;;; Code
;;;###autoload
(define-minor-mode vhier-outline-mode
  "Frontend for Verilog-Perl `vhier' processed output for outline-minor-mode with outshine visualization."
  :lighter " vH"
  :keymap
  '(
    ;; Fetched from https://www.emacswiki.org/emacs/OutlineMinorMode
    ;; HIDE
    ("q" . outline-hide-sublevels)    ; Hide everything but the top-level headings
    ("t" . outline-hide-body)         ; Hide everything but headings (all body lines)
    ("o" . outline-hide-other)        ; Hide other branches
    ("c" . outline-hide-entry)        ; Hide this entry's body
    ("l" . outline-hide-leaves)       ; Hide body lines in this entry and sub-entries
    ("d" . outline-hide-subtree)      ; Hide everything in this entry and sub-entries
    ;; SHOW
    ("a" . outline-show-all)          ; Show (expand) everything
    ("e" . outline-show-entry)        ; Show this heading's body
    ("i" . outline-show-children)     ; Show this heading's immediate child sub-headings
    ("k" . outline-show-branches)     ; Show all sub-headings under this heading
    ("s" . outline-show-subtree)      ; Show (expand) everything in this heading & below
    ;; MOVE
    ("u" . outline-up-heading)                ; Up
    ("n" . outline-next-visible-heading)      ; Next
    ("p" . outline-previous-visible-heading)  ; Previous
    ("f" . outline-forward-same-level)        ; Forward - same level
    ("b" . outline-backward-same-level)       ; Backward - same level
    ;; OWN
    ("j" . vhier-outline-jump-to-file)  ; Added by Larumbe
    )
  )

;; Still needs to be polished...
;; For example: if added imenu-list, it would parse the vhier-outline buffer instead of the verilog one.
;; Moreover, since there is delay in finding the tag, if set a read-only it would affect the vhier-outlin buffer as well...
(defun vhier-outline-jump-to-file ()
  "Jump to file at cursor on hierarchy.v file"
  (interactive)
  (when (not vhier-outline-mode)
    (error "vhier mode not enabled on current buffer..."))
  (when (not (executable-find "global"))
    (error "vhier mode requires global to work..."))
  (when (not (ggtags-find-project))
    (error "Associated GTAGS file not found. Make sure hierarchy file is in the same folder as its matching GTAGS file..."))
  (delete-other-windows)
  (split-window-right)
  (shrink-window-horizontally 60)
  (other-window 1)
  (end-of-line)
  (ggtags-find-tag-dwim (thing-at-point 'symbol t)))


(provide 'vhier-outline-mode)
