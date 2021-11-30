;;; init-ivy.el --- Ivy/Counsel/Swiper  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package ivy
  :diminish
  :bind (("C-x b"   . ivy-switch-buffer))
  :bind (:map ivy-minibuffer-map
         ("C-l"     . ivy-backward-kill-word) ; Useful for `dired-do-copy'. Complement with M-i if want to yank result at point.
         ("C-o"     . ivy-occur)
         ("C-c C-o" . hydra-ivy/body))
  :config
  (setq ivy-use-virtual-buffers t)      ; Add recent files and bookmarks to the ivy-switch-buffer
  (setq ivy-count-format "%d/%d ")      ; Displays the current and total number in the collection in the prompt
  (setq enable-recursive-minibuffers t) ; Allow minibuffer commands while in the minibuffer.
  ;; Do not break compatibility with Helm for switching buffers
  (if (equal larumbe/completion-framework 'ivy)
      (progn
        (ivy-mode 1)
        (use-package ivy-rich
          :demand
          :config
          (ivy-rich-mode 1)))
    ;; Else (using helm)
    (ivy-mode -1))


  ;; Dependencies
  (use-package ivy-hydra))



(when (equal larumbe/completion-framework 'ivy)
  (use-package swiper
    :bind (:map swiper-map
           ("C-r"   . swiper-isearch-C-r)
           ("C-w"   . bjm/ivy-yank-whole-word)
           ("C->"   . swiper-mc)
           ("C-<"   . swiper-mc))
    :bind (("C-s"   . swiper)
           ("C-r"   . swiper-backward)
           ("M-s ." . swiper-symbol-at-point))
    :config
    (setq search-default-mode 'auto)

    ;; https://github.com/abo-abo/swiper/issues/1068
    ;; INFO: abo-abo's answer was fine but didn't take into account ignoring
    ;; case-fold while searching for symbols.
    ;; Besides, it didn't actually searched for symbols according to current
    ;; mode syntax-table, since it was necessary to add the \_< \_> to the search.
    ;;
    ;; A temporary binding on `search-default-mode' to #'isearch-symbol-regexp
    ;; fixed it without the need of \_< \_>, but did not work with some symbols when
    ;; there were hyphens (like elisp functions) or parenthesys.
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


    (defun larumbe/swiper-C-s (&optional arg)
      "Move cursor vertically down ARG candidates.
If the input is empty, select the previous history element instead.

INFO: If performed a symbol search with no symbol at point, center
point between the symbol boundaries."
      (interactive "p")
      (cond ((string= ivy-text "")
             (ivy-previous-history-element 1))
            ((search-backward "\\_<\\_>" nil t)
             (forward-char 3))
            (t
             (ivy-next-line arg))))

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
           ("C-x C-f"    . larumbe/counsel-find-file)
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
    ;; Avoid writing 'larumbe/' for all these prefixed functions
    (add-to-list 'ivy-initial-inputs-alist '(counsel-M-x . " "))
    ;; Use ffap to open files
    (setq counsel-find-file-at-point t)


    (require 'ag)
    ;; Format `counsel-ag' and `counsel-rg' commands from `ag-arguments' and `larumbe/rg-arguments'
    ;; INFO: These commands are also used for counsel projectile implementations.
    (setq counsel-ag-base-command (append '("ag") ag-arguments))
    (delete "--stats" counsel-ag-base-command)
    (dolist (arg `("--nocolor" "-p" ,larumbe/gitignore-global-file "%s"))
      (add-to-list 'counsel-ag-base-command arg :append))

    (setq counsel-rg-base-command (append '("rg") larumbe/rg-arguments))
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
      (larumbe/counsel--search #'counsel-rg))


    ;; Inspiration from:
    ;; https://stackoverflow.com/questions/3139970/open-a-file-at-line-with-filenameline-syntax
    (defun larumbe/counsel-find-file ()
      "Execute `counsel-find-file' wrapper.

Check if current file-at-point has a line number and jump to it after opening the file."
      (interactive)
      (let ((line-num nil)
            (bounds (bounds-of-thing-at-point 'filename)))
        (when bounds
          (save-excursion
            (goto-char (car bounds))
            (search-forward-regexp "[^ ]:" (cdr bounds) t)
            (if (looking-at "[0-9]+")
                (setq line-num (string-to-number (buffer-substring (match-beginning 0) (match-end 0)))))))
        (find-file-at-point)
        (unless (equal line-num nil)
          (goto-line line-num)))))


  (use-package ivy-youtube
    :straight (:repo "squiter/ivy-youtube"
               :fork (:repo "gmlarumbe/ivy-youtube"))
    :bind (("C-x c y" . ivy-youtube))))



(provide 'init-ivy)

;;; init-ivy.el ends here
