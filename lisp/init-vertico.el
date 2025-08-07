;;; init-vertico.el --- Vertico -*- lexical-binding: t -*-
;;; Commentary:
;;
;; TODO: Issue with symbol/case detection in consult symbol at point:
;;
;; - Case search gets fixed in `larumbe/consult-symbol-at-point' with `orderless-smart-case' set to nil
;;
;; https://github.com/minad/consult/issues/469
;;
;;  - Recommendation for support of regexps in `consult-line' is to use orderless
;;
;;  - It works well for everything if setting a symbol except if it's the last word of a line:
;;    e.g: Running M-x `consult-line' and looking for \_<consult\_> will find everything except for:
;;     (use-package consult
;;
;;  - However, adding a dot (hidden character?) after consult will only detect this previous line:
;;     - \_<consult.\_>
;;
;;  - I read something about hidden characters added by `consult-buffer' in following issue:
;;    - https://github.com/minad/consult/issues/365
;;
;;    In the wiki there is a section covering this:
;;      - https://github.com/minad/consult/wiki
;;
;;    Orderless style dispatchers (Ensure that the $ regexp works with consult-buffer)
;;      Unfortunately $ does not work out of the box with consult-buffer and consult-line since
;;      these commands add disambiguation suffixes to the candidate strings. The problem can be
;;      fixed by adjusting the filter regular expressions accordingly.
;;      See this reddit post for more context.
;;
;;   There was a post afterwards about a sophisticated way of using orderless. Too much effort I guess...
;;   Get back to ivy! I think I gave it a try...
;;
;; --------------------------------------------------------------------------------
;; Test snippet for `consult-line' and thing at point functions
;; --------------------------------------------------------------------------------
;;
;; foo  a
;; foos a
;; FOO  a
;; FOOS a
;; a foo
;; a foos
;; A FOO
;; A FOOS
;;
;; --------------------------------------------------------------------------------
;;
;;; Code:


(use-package vertico
  :init
  (vertico-mode))


;; Persist history over Emacs restarts. Vertico sorts by history position.
(use-package savehist
  :init
  (savehist-mode))


(use-package orderless
  :after vertico
  :demand
  :config
  (setq completion-styles '(orderless basic)
        completion-category-defaults nil
        completion-category-overrides '((file (styles basic partial-completion)))))


(use-package marginalia
  :after vertico
  :demand
  :init
  (marginalia-mode))


(use-package embark-consult ; Consult users will also want the embark-consult package.
  :after (embark consult)
  :demand ; only necessary if you have the hook below
  ;; if you want to have consult previews as you move around an
  ;; auto-updating embark collect buffer
  :hook
  (embark-collect-mode . consult-preview-at-point-mode))


(use-package consult
  :after vertico
  :demand
  :bind (("C-s"     . consult-line)
         ("M-s C-." . larumbe/consult-symbol-at-point)
         ("M-s ."   . consult-line-thing-at-point)
         ("M-g r"   . consult-ripgrep)
         ("M-I"     . consult-imenu)
         ("C-x c /" . consult-find)
         ("C-#"     . consult-outline))
  :config
  (use-package consult-ag
    :straight (:host github :repo "yadex205/consult-ag")
    :bind (("M-g a" . consult-ag)))
  (use-package consult-company
    :bind (("<C-return>" . consult-company))) ; Replaces `minibuffer' function `completion-at-point'

  (defun larumbe/consult-symbol-at-point ()
    "Alternative to `consult-line-thing-at-point' using `orderless'."
    (interactive)
    (let* ((case-fold-search (derived-mode-p '(vhdl-mode)))
           (orderless-smart-case nil) ; This is the one that has (or should) have an effect (not `case-fold-search')
           (sym-atp (thing-at-point 'symbol :noprops))
           (last-char (cdr (bounds-of-thing-at-point 'symbol)))
           ;; TODO: Initial inputs to try to match symbols referenced in the Commentary section
           (initial-input (concat "\\_<" sym-atp "\\_>"))   ; Does not detect symbol if it is at the end of the line
           ;; (initial-input (concat "\\_<" sym-atp ".?\\_>")) ; This one matches symbol and symbol ended in symbol+anything (e.g: use-package and use-packages)
           ;; (initial-input (concat "\\_<" sym-atp "\\_>.?")) ;  This one doesn't match match at the end of the line
           ;; (initial-input (concat "\\_<" sym-atp (when (eq last-char (line-end-position)) ".") "\\_>")) ; Now it detects if it's at the end of the line with the hidden char, but not the rest
           ;; (initial-input (concat "\\<" sym-atp "\\>")) ; With this it will take some chars such as points as part of the symbol
           )
       (consult-line initial-input)))

  ;; https://www.reddit.com/r/emacs/comments/1jwk4dg/consultlinesymbolatpoint/
  ;; - Same issue stated in the comments
  (consult-customize
   consult-line
   :add-history (seq-some #'thing-at-point '(region symbol)))

  (defalias 'consult-line-thing-at-point 'consult-line)

  (consult-customize
   consult-line-thing-at-point
   :initial (thing-at-point 'symbol)))


(use-package embark
  :after vertico
  :demand
  :bind
  (("C-;"   . embark-act)
   ("C-:"   . embark-dwim)
   ("C-h B" . embark-bindings)) ;; alternative for `describe-bindings'
  :init
  ;; Optionally replace the key help with a completing-read interface
  (setq prefix-help-command #'embark-prefix-help-command)
  :config
  ;; Hide the mode line of the Embark live/completions buffers
  (add-to-list 'display-buffer-alist
               '("\\`\\*Embark Collect \\(Live\\|Completions\\)\\*"
                 nil
                 (window-parameters (mode-line-format . none)))))



(provide 'init-vertico)

;;; init-vertico.el ends here
