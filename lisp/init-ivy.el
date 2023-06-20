;;; init-ivy.el --- Ivy/Counsel/Swiper  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package ivy
  :diminish
  :bind (("C-x b"   . ivy-switch-buffer))
  :bind (:map ivy-minibuffer-map
         ("C-l"     . ivy-backward-kill-word) ; Useful for `dired-do-copy'. Complement with M-i if want to yank result at point.
         ("C-o"     . ivy-occur)
         ("S-SPC"   . nil)) ; Unmap `ivy-restrict-to-matches' that erases input unintentionally if writing uppercase words
  :config
  (setq ivy-use-virtual-buffers t) ; Add recent files and bookmarks to the ivy-switch-buffer
  (setq ivy-count-format "%d/%d ") ; Displays the current and total number in the collection in the prompt
  ;; Do not break compatibility with Helm for switching buffers
  (if (equal larumbe/completion-framework 'ivy)
      (ivy-mode 1)
    ;; Else (using helm)
    (ivy-mode -1)))


(use-package ivy-rich
  :demand
  :after ivy
  :config
  (ivy-rich-mode 1))


(use-package orderless
  :demand
  :after ivy
  :config
  ;; Ivy config, according to orderless GitHub README
  (setq ivy-re-builders-alist '((t . orderless-ivy-re-builder)))
  (add-to-list 'ivy-highlight-functions-alist '(orderless-ivy-re-builder . orderless-ivy-highlight)))
  ;; This has a similar effect to setting:  (setq ivy-re-builders-alist '((t . ivy--regex-ignore-order)))
  ;; However it has the benefit that adds some more flexibility using orderless.
  ;; It could be set, for example: (add-to-list 'orderless-matching-styles 'orderless-flex)
  ;;
  ;; The only issue is that in `ivy-highlight-functions-alist', for key `orderless-ivy-re-builder',
  ;; value `orderless-ivy-highlight' does not work properly in swiper. This can be overcome by
  ;; forcing using `ivy--regex-plus' with local let bindings inside swiper functions


(when (equal larumbe/completion-framework 'ivy)
  (use-package swiper
    :bind (:map swiper-map
           ("C-r"   . swiper-isearch-C-r)
           ("C-w"   . bjm/ivy-yank-whole-word)
           ("C->"   . swiper-mc)
           ("C-<"   . swiper-mc)
           ("C-;"   . swiper-avy))
    :bind (("C-s"   . larumbe/search-forward)
           ("C-r"   . larumbe/search-backward)
           ("M-s ." . larumbe/symbol-at-point))
    :config
    (setq search-default-mode 'auto)
    (defvar larumbe/swiper-re-builders-alist '((t . ivy--regex-plus)))

    ;; Search wrappers
    (defun larumbe/search-forward (&optional uarg)
      "Use isearch for dired-mode and swiper for the rest.
Use `swiper-isearch' not showing lines for compilation buffers or if uarg is
provided (e.g. large files where showing lines with `swiper' could be a bit
slow)."
      (interactive "P")
      (let ((ivy-re-builders-alist larumbe/swiper-re-builders-alist)) ; Override `orderless' for swiper, keep it for ivy
        (cond ((string= major-mode "dired-mode")
               (call-interactively #'isearch-forward))
              (uarg
               (call-interactively #'swiper))
              (t
               (call-interactively #'swiper-isearch)))))

    (defun larumbe/search-backward (&optional uarg)
      "Use isearch for dired-mode and swiper for the rest.
Use `swiper-isearch' not showing lines for compilation buffers or if uarg is
provided (e.g. large files where showing lines with `swiper' could be a bit
slow)."
      (interactive "P")
      (let ((ivy-re-builders-alist larumbe/swiper-re-builders-alist)) ; Override `orderless' for swiper, keep it for ivy
        (cond ((string= major-mode "dired-mode")
               (call-interactively #'isearch-backward))
              (uarg
               (call-interactively #'swiper-backward))
              (t
               (call-interactively #'swiper-isearch)))))

    (defun larumbe/symbol-at-point (&optional uarg)
      "Use isearch for dired-mode, swiper-isearch (no-line info) if UARG and swiper for the rest."
      (interactive "P")
      (let ((ivy-re-builders-alist larumbe/swiper-re-builders-alist)) ; Override `orderless' for swiper, keep it for ivy
        (cond ((string= major-mode "dired-mode")
               (call-interactively #'isearch-forward-symbol-at-point))
              (uarg
               (call-interactively #'swiper-symbol-at-point))
              (t
               (call-interactively #'swiper-isearch-symbol-at-point)))))

    ;; https://github.com/abo-abo/swiper/issues/1068
    ;; INFO: abo-abo's answer was fine but didn't take into account ignoring
    ;; case-fold while searching for symbols.
    ;; Besides, it didn't actually searched for symbols according to current
    ;; mode syntax-table, since it was necessary to add the \_< \_> to the search.
    ;;
    ;; A temporary binding on `search-default-mode' to #'isearch-symbol-regexp
    ;; fixed it without the need of \_< \_>, but did not work with some symbols when
    ;; there were hyphens (like elisp functions) or parenthesis.
    ;;
    ;; Lastly, using let binding on `ivy-initial-inputs-alist' instead of on
    ;; ivy-related `initial-input' first arg caused swiper to jump to last result on
    ;; buffer instead of to current one.
    ;;
    ;; The only issue with this approach is that if there is no symbol under the point
    ;; the \_< \_> is still added to an empty string, and it is necessary to move the point
    ;; 3 positions on the ivy buffer. Worked around with `larumbe/swiper-C-s'
    (defun swiper-symbol-at-point ()
      (interactive)
      (let* ((ivy-case-fold-search-default nil)
             (sym-atp (thing-at-point 'symbol :noprops))
             (initial-input (concat "\\_<" sym-atp "\\_>")))
        (swiper initial-input)))

    (defun swiper-isearch-symbol-at-point ()
      (interactive)
      (let* ((ivy-case-fold-search-default nil)
             (sym-atp (thing-at-point 'symbol :noprops))
             (initial-input (concat "\\_<" sym-atp "\\_>")))
        (swiper-isearch initial-input)))

    (defun larumbe/swiper-C-s (&optional arg)
      "Move cursor vertically down ARG candidates.
If the input is empty, select the previous history element instead.

INFO: If performed a symbol search with no symbol at point, center
point between the symbol boundaries."
      (interactive "p")
      (let ((ivy-re-builders-alist larumbe/swiper-re-builders-alist)) ; Override `orderless' for swiper, keep it for ivy
        (cond ((string= ivy-text "")
               (ivy-previous-history-element 1))
              ((search-backward "\\_<\\_>" nil t)
               (forward-char 3))
              (t
               (ivy-next-line arg)))))

    (advice-add 'swiper-C-s :override #'larumbe/swiper-C-s)


    ;; http://pragmaticemacs.com/emacs/search-or-swipe-for-the-current-word/
    (defun bjm/ivy-yank-whole-word ()
      "Pull next word from buffer into search string."
      (interactive)
      (let (amend)
        (with-ivy-window
          ;;move to last word boundary
          (re-search-backward "\\b")
          (let ((pt (point))
                (le (line-end-position)))
            (forward-word 1)
            (if (> (point) le)
                (goto-char pt)
              (setq amend (buffer-substring-no-properties pt (point))))))
        (when amend
          (insert (replace-regexp-in-string "  +" " " amend))))))


  ;; INFO: Counsel find file:
  ;;   Press "/ TAB" to go to root directory
  ;;   Press "~" to go to $HOME
  ;;   Press "$" to go to some env variable defined path
  (use-package counsel
    :bind (("M-x"        . counsel-M-x)
           ("C-x r b"    . counsel-bookmark)
           ("<C-return>" . counsel-company) ; Replaces `minibuffer' function `completion-at-point'
           ("M-g a"      . larumbe/counsel-ag)
           ("M-g r"      . larumbe/counsel-rg)
           ("M-I"        . counsel-imenu)
           ("C-x c /"    . counsel-file-jump)
           ("C-x c p"    . counsel-list-processes)
           ("C-#"        . counsel-outline))
    :bind (:map counsel-find-file-map
           ("C-l" . counsel-up-directory))
    :config
    ;; Use ffap to open files
    (setq counsel-find-file-at-point t)
    ;; Use same outline faces as org
    (setq counsel-outline-face-style 'org)

    (require 'ag)
    ;; Format `counsel-ag' and `counsel-rg' commands from `ag-arguments' and `larumbe/rg-arguments'
    ;; INFO: These commands are also used for counsel projectile implementations.
    (setq counsel-ag-base-command (append '("ag") ag-arguments))
    (delete "--stats" counsel-ag-base-command)
    (dolist (arg `("--nocolor" "-p" ,larumbe/gitignore-global-file "%s"))
      (add-to-list 'counsel-ag-base-command arg :append))

    (setq counsel-rg-base-command (append '("rg") larumbe/rg-arguments))
    ;; Needed for fixing the 'os error (2) error'
    ;; - https://github.com/doomemacs/doomemacs/issues/3038 (solution with Doom Emacs macros by hlissner, and always returning 0 by io12)
    ;; - https://github.com/abo-abo/swiper/issues/2339
    ;; Removing the --follow option seems to fix it for current configuration
    (delete "--follow" counsel-rg-base-command)
    (dolist (arg `("--with-filename" "--no-heading" "--color" "never" "%s"))
      (add-to-list 'counsel-rg-base-command arg :append))


    ;; INFO: `counsel-ag'/ `counsel-rg' by default look for a .git directory and start a search from the directory containing it.
    ;; This is better performed with projectile, and leave `default-directory' for non-projectile implementations.
    (defun larumbe/counsel--search (cmd)
      "Auxiliary shared function between `counsel-ag' and `counsel-rg'.

Intended to do ag/rg with current symbol at point if cursor is over a symbol
and prompt for input otherwise. If in dired-mode do not consider an initial input
to allow for searches over specific dirs.

If prefix ARG is provided, do case-sensitive search and with whole word.
Otherwise, smart-case is performed (similar to case-fold-search)."
      (let* ((ivy-case-fold-search-default ivy-case-fold-search-default)
             (initial-input (thing-at-point 'symbol))
             (extra-args nil)
             (prog-name (string-remove-prefix "counsel-" (symbol-name cmd)))
             (prompt (concat "[" prog-name " @ " default-directory "]: ")))
        (when current-prefix-arg
          (setq ivy-case-fold-search-default nil) ; Implicitly sets case-sensitive "-s" flag, which overrides "--smart-case"
          (setq extra-args "-w")
          (setq prompt (concat "(Case/Word) " prompt)))
        (when (string= major-mode "dired-mode")
          (setq initial-input nil))
        (funcall cmd initial-input default-directory extra-args prompt)))


    (defun larumbe/counsel-ag ()
      "Execute `counsel-ag' wrapper."
      (interactive)
      (larumbe/counsel--search #'counsel-ag))


    (defun larumbe/counsel-rg ()
      "Execute `counsel-rg' wrapper."
      (interactive)
      (larumbe/counsel--search #'counsel-rg)))


  (use-package ivy-youtube
    :bind (("C-x c y" . ivy-youtube))))


(provide 'init-ivy)

;;; init-ivy.el ends here
