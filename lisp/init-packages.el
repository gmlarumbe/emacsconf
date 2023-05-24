;;; init-packages.el --- Basic Packages configuration  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Libraries
(use-package dash)
(use-package s)
(use-package f)
(use-package ht)
(use-package pcre2el)
(use-package with-editor)
(use-package request)
(use-package bind-key :straight nil)
(use-package yaml :commands (yaml-parse-string yaml-encode-object)) ; Full Elisp, worse performance but portable
(use-package emacs-libyaml :straight (:host github :repo "syohex/emacs-libyaml")) ; Dinamic binding for libyaml


;;;; Functions & Utils
(use-package xah-lee-functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/xah-lee-functions.el")))

(use-package modi-functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/modi-functions.el"))
  :bind (("C-]" . modi/pull-up-line)))

(use-package others-functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("site-lisp/others-functions.el"))
  :bind (("C-x C-r" . er-sudo-edit)                       ; Unmap `find-file-read-only'
         ("C-x d"   . duplicate-current-line-or-region))) ; Replaces Dired (C-x C-j works better)

(use-package larumbe-functions
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/larumbe-functions.el"))
  :bind (("C-x C-f" . larumbe/find-file-dwim)                 ; Context based `find-file-at-point'
         ("M-w"     . larumbe/copy-region-or-symbol-at-point) ; Overrides `kill-ring-save'
         ("C-z"     . larumbe/pop-to-previous-mark)           ; Unmaps suspending frame
         ("C-x C-/" . larumbe/pwd-to-kill-ring)
         ("C-x C-," . larumbe/revert-buffer-maybe-no-confirm)
         ("C-x C-h" . larumbe/scratch-toggle)))

(use-package larumbe-macros
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("macros/larumbe-macros.el")))

(use-package fpga-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/fpga-utils.el")))

(use-package vivado-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/vivado-utils.el"))
  :mode (("\\.xdc\\'" . larumbe/vivado-xdc-mode))
  :bind (:map tcl-mode-map
         ("C-c C-l" . larumbe/vivado-shell-tcl-send-line-or-region-and-step)))

(use-package lattice-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("major-modes/lattice-utils.el")))


;;;; Window/Frame Display
(use-package smart-mode-line
  :commands (larumbe/sml-enable)
  :config
  (defun larumbe/sml-enable (theme)
    "Wrapper around `sml/enable'.
Takes into account if current theme exists and if it has been added to `custom-safe-themes'.
This was needed in order to allow GitHub actions to work properly."
    (interactive)
    (unless theme
      (error "No theme selected!"))
    ;; Handle `custom-safe-themes'.
    (let* ((straight-repos-dir (expand-file-name (concat (file-name-as-directory straight-base-dir) "straight/repos")))
           (theme-file (concat (file-name-as-directory straight-repos-dir) "smart-mode-line/smart-mode-line-dark-theme.el"))
           (hash (with-temp-buffer
                   (insert-file-contents theme-file)
                   (secure-hash 'sha256 (current-buffer)))))
      (unless (member hash custom-safe-themes)
        (push hash custom-safe-themes)))
    ;; Set theme and save
    (setq sml/theme theme) ; Other choices would be 'light or 'respectful. By default, sml will try to figure out the best sml theme to go with your Emacs theme.
    (sml/setup)))


(use-package diminish)


(use-package time
  :straight nil
  :config
  (setq display-time-default-load-average nil)) ; Display time on the status bar


(use-package winner
  :straight nil
  :config)


(use-package popwin
  :config
  (popwin-mode 1))


(use-package buffer-move
  :bind (("<C-S-up>"    . buf-move-up)
         ("<C-S-down>"  . buf-move-down)
         ("<C-S-left>"  . buf-move-left)
         ("<C-S-right>" . buf-move-right)))


(use-package ibuffer
  :bind (("C-x C-b" . ibuffer))
  :config
  (setq ibuffer-default-sorting-mode 'major-mode)
  (setq ibuffer-expert t))


(use-package ibuffer-projectile
    :hook ((ibuffer . modi/ibuffer-customization))
    :after ibuffer
    :config
    (defun modi/ibuffer-customization ()
      "My customization for `ibuffer'."
      ;; ibuffer-projectile setup
      (ibuffer-projectile-set-filter-groups)
      (unless (eq ibuffer-sorting-mode 'alphabetic)
        (ibuffer-do-sort-by-alphabetic) ; first do alphabetic sort
        (ibuffer-do-sort-by-major-mode))))


(use-package ibuf-ext
  :straight nil
  :config
  (setq ibuffer-show-empty-filter-groups nil))


;;;; Navigation
(use-package isearch
  :straight nil
  :bind (("M-s M-." . isearch-forward-symbol-at-point))
  :bind (:map isearch-mode-map
         ("C-w" . my-isearch-yank-word-or-char-from-beginning) ; Override `isearch-yank-word-or-char'
         ("C-j" . isearch-exit)  ; Overrides `isearch-printing-char' to search for newlines
         ("C-n" . isearch-repeat-forward)
         ("C-p" . isearch-repeat-backward)
         ("M-<" . isearch-beginning-of-buffer)
         ("M->" . isearch-end-of-buffer))
  :config
  ;; Default was 'not-yanks, so text yanked into the search string in Isearch mode was always downcased.
  ;; Setting to t, upper case chars disable case fold searching (e.g. search symbol at point)
  (setq search-upper-case t)

  ;; https://www.emacswiki.org/emacs/SearchAtPoint
  (defun my-isearch-yank-word-or-char-from-beginning ()
    "Move to beginning of word before yanking word in `isearch-mode'.
Make \\keymapC-s C-w and C-r C-w act like Vim's g* and g#, keeping Emacs'
C-s C-w [C-w] [C-w]... behaviour. "
    (interactive)
    ;; Making this work after a search string is entered by user
    ;; is too hard to do, so work only when search string is empty.
    (let ((search-upper-case 'not-yanks)) ; INFO: Ignore case when searching. To take case into account better use symbol search
      (if (= 0 (length isearch-string))
          (beginning-of-thing 'word))
      ;; At some point in Emacs it required a '1' argument to fix a "Wrong type argument: number-or-marker-p, nil" error
      (isearch-yank-word-or-char 1))))


(use-package view
  :straight nil
  :diminish
  :bind (:map view-mode-map
         ("n"   . next-line)
         ("p"   . previous-line)
         ("f"   . forward-char)
         ("b"   . backward-char)
         ("C-j" . scroll-up-command)
         ("C-k" . scroll-down-command)
         ("j"   . View-scroll-line-forward)
         ("k"   . View-scroll-line-backward)
         ("l"   . recenter-top-bottom)
         ("RET" . nil)
         ("C-m" . nil))
  :config
  (setq view-read-only t))


(use-package outshine
  :bind (:map outshine-mode-map
         ("M-RET" . nil)  ; Leave space for `company-complete'
         ("C-M-i" . nil)) ; Leave space for defun indentation, unmaps `outshine-cycle-buffer'
  :config
  ;; Do not include outshine tags at imenu
  (setq outshine-imenu-show-headlines-p nil))


(use-package navi-mode)


(use-package beacon
  :diminish
  :init
  (setq beacon-blink-when-window-scrolls nil) ; Issue #76: https://github.com/Malabarba/beacon/issues/76
  :config
  (setq beacon-size 10)
  (setq beacon-color "light green")
  (setq beacon-blink-when-focused t)
  (dolist (mode '(term-mode vterm-mode))
    (add-to-list 'beacon-dont-blink-major-modes mode)))


(use-package speedbar
  :straight nil
  :commands (speedbar-toggle-line-expansion)) ; Used by `vhdl-speedbar' own customization


(use-package sr-speedbar
  ;; Default would be fetched from emacsorphanage
  :straight (:host github :repo "emacsmirror/emacswiki.org" :branch "master" :files ("sr-speedbar.el"))
  :bind (:map speedbar-mode-map
         ("q" . larumbe/kill-current-buffer)
         ("j" . speedbar-edit-line))
  :config
  (setq speedbar-show-unknown-files t)
  (setq speedbar-use-images nil)
  (setq sr-speedbar-right-side t))


(use-package hardcore-mode
  :diminish hardcore-mode
  :init
  (setq too-hardcore-backspace t)
  (setq too-hardcore-return    t))


(use-package avy
  :bind (("C-:" . avy-goto-char-2)))


;;;; Editing
(use-package drag-stuff
  :bind (("<C-M-up>"   . drag-stuff-up)
         ("<C-M-down>" . drag-stuff-down))
  :hook ((drag-stuff-before-drag . modi/drag-stuff--adj-pt-pre-drag)
         (drag-stuff-after-drag  . modi/drag-stuff--rst-pt-post-drag))
  :config
  ;; kmodi hack to avoid dragging line of where currently point is
  ;; https://emacs.stackexchange.com/questions/13941/move-selected-lines-up-and-down
  (defvar modi/drag-stuff--point-adjusted nil)
  (defvar modi/drag-stuff--point-mark-exchanged nil)

  (defun modi/drag-stuff--adj-pt-pre-drag ()
    "If a region is selected AND the `point' is in the first column, move
back the point by one char so that it ends up on the previous line. If the
point is above the mark, exchange the point and mark temporarily."
    (when (region-active-p)
      (when (< (point) (mark)) ; selection is done starting from bottom to up
        (exchange-point-and-mark)
        (setq modi/drag-stuff--point-mark-exchanged t))
      (if (zerop (current-column))
          (progn
            (backward-char 1)
            (setq modi/drag-stuff--point-adjusted t))
        ;; If point did not end up being on the first column after the
        ;; point/mark exchange, revert that exchange.
        (when modi/drag-stuff--point-mark-exchanged
          (exchange-point-and-mark) ; restore the original point and mark loc
          (setq modi/drag-stuff--point-mark-exchanged nil)))))

  (defun modi/drag-stuff--rst-pt-post-drag ()
    "Restore the `point' to where it was by forwarding it by one char after
the vertical drag is done."
    (when modi/drag-stuff--point-adjusted
      (forward-char 1)
      (setq modi/drag-stuff--point-adjusted nil))
    (when modi/drag-stuff--point-mark-exchanged
      (exchange-point-and-mark) ; restore the original point and mark loc
      (setq modi/drag-stuff--point-mark-exchanged nil))))


(use-package untabify-trailing-ws
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("minor-modes/untabify-trailing-ws.el"))
  :config
  (dolist (file `(,(file-name-concat user-emacs-directory "straight/repos/verilog-mode/verilog-mode.el")
                  ,(file-name-concat user-emacs-directory "straight/repos/verilog-mode/verilog-test.el")
                  ,(file-name-concat user-emacs-directory "straight/repos/cperl-mode/cperl-mode.el")
                  ,(file-name-concat user-emacs-directory "straight/repos/verilog-ext/snippets/makefile-mode/verilog-template")))
    (push file untabify-trailing-disable-on-files)))


(use-package align
  :straight nil
  :config
  (setq align-default-spacing 1)
  (setq align-to-tab-stop nil))


(use-package elec-pair
  :straight nil)


(use-package whole-line-or-region
  :bind (("C-w" . whole-line-or-region-kill-region)))


(use-package multiple-cursors
  :bind (("C->"     . mc/mark-next-like-this)
         ("C-<"     . mc/mark-previous-like-this)
         ("C-c C->" . mc/edit-lines)
         ("C-c C-<" . mc/mark-all-like-this)
         ("C-c C-#" . mc/insert-numbers))
  :config
  (when (equal larumbe/completion-framework 'ivy)
    (add-to-list 'mc/cmds-to-run-once 'swiper-mc)))


(use-package expand-region
  :bind (("C-=" . er/expand-region))
  :config
  (setq expand-region-contract-fast-key "|")
  (setq expand-region-reset-fast-key "<ESC><ESC>"))


;;;; Programming
;; LSP: lsp & eglot will override some variables/functionality:
;; - For code navigation they use `xref' under the hood, they set the proper value to `xref-backend-functions'
;; - For syntax checking, they override `flymake' and `flycheck' variables, e.g. they execute (flycheck-select-checker 'lsp) or similar
;; - For code completion, they change `company-backends', overriding it with `company-capf' or adding it to existing ones
;; - etc...

(use-package eglot
  :straight nil
  :config
  ;; Prevent eglot from overriding value of `company-backends' (eglot value of `completion-at-point-functions' still works)
  (setq eglot-stay-out-of '(company eldoc flymake)))


(use-package lsp-mode
  :init
  (setq lsp-keymap-prefix "C-x l")
  (setq lsp-headerline-breadcrumb-enable nil)
  (setq lsp-enable-imenu nil))


(use-package lsp-ui :commands (lsp-ui-sideline-mode)) ; Flycheck side-line even without lsp enabled
;; INFO: At some point tried with `flycheck-pos-tip' and `flycheck-popup-tip' to show messages
;; right in front of the cursor. However none of the tooltips seemed to work properly and the
;; result obtained with `lsp-ui-sideline-mode' was far better and less obtrusive.


(use-package lsp-ivy) ; interactive ivy interface to the workspace symbol functionality offered by lsp-mode


(use-package realgud)


(use-package apheleia :diminish)


(use-package fic-mode
  :commands (larumbe/clean-fic-keywords-dir
             larumbe/wrap-danger-region)
  :config
  (setq fic-activated-faces '(font-lock-doc-face font-lock-comment-face))
  (setq fic-highlighted-words '("FIXME" "TODO" "BUG" "DANGER" "INFO" "NOTE"))

  (defun larumbe/clean-fic-keywords-dir ()
    "Perform `counsel-ag' of `fic-mode' highlighted keywords in selected DIR
in order to check pending project actions."
    (interactive)
    (require 'counsel)
    (let ((kwd (completing-read "Select keyword: " fic-highlighted-words))
          (path (read-directory-name "Directory: "))
          (files (completing-read "Select file regex: " '("(System)Verilog" "Python" "elisp")))
          (counsel-ag-base-command counsel-ag-base-command) ; Save the global value of `counsel-ag-base-command'
          (regex))
      (pcase files
        ("(System)Verilog" (setq regex ".[s]?v[h]?$")) ; +Headers
        ("Python"          (setq regex ".py$"))
        ("elisp"           (setq regex ".el$")))
      ;; `counsel-ag' glob search
      (setq counsel-ag-base-command (append counsel-ag-base-command '("-G")))
      (setq counsel-ag-base-command (append counsel-ag-base-command (list regex)))
      (counsel-ag kwd path)))

  (defun larumbe/wrap-danger-region ()
    "Wrap current line or region with DANGER comments for `fic-mode' highlighting."
    (interactive)
    (let ((text-begin "DANGER")
          (text-end   "End of DANGER"))
      (larumbe/comment-tag-line-or-region text-begin text-end))))


(use-package hideshow
  :straight nil
  :diminish hs-minor-mode
  :config
  ;; Advice `hs-toggle-hiding':
  ;;   - There was a 'bug' when doing hs-toggle if the block start symbol was at the end of the line.
  ;;     The block would hid properly and the point is set to the block start but if toggling
  ;;     again to show the hidden block it would not work (it is necessary to go back one char
  ;;     for it to show again).
  ;;
  ;;   - e.g. in verilog, this worked with hs with the begin/end keywords:
  ;;         begin : foo
  ;;            something();
  ;;         end : foo
  ;;
  ;;     But this didn't
  ;;         begin
  ;;            something();
  ;;         end
  ;;
  ;;  - The only difference is that it is needed that the point be inside the block
  ;;    for it to hide, it is not enough that point is over the block start symbol,
  ;;    it has to be after it (not a major problem though).
  (defun larumbe/hs-toggle-hiding (&optional e)
    "Advice function for `hs-toggle-hiding'.

Same as `hs-toggle-hiding', but do not exec: (posn-set-point (event-end e))"
    (interactive)
    (hs-life-goes-on
     ;; (posn-set-point (event-end e)) ;; INFO: Disabled action
     (if (hs-already-hidden-p)
         (hs-show-block)
       (hs-hide-block))))

  ;; Apply advice
  (advice-add 'hs-toggle-hiding :override #'larumbe/hs-toggle-hiding))


(use-package outline
  :straight nil
  :diminish outline-minor-mode)


(use-package outshine
  :diminish outshine-mode)


(use-package flycheck
  :diminish
  :commands (flycheck-display-error-messages-unless-error-list)
  :config
  ;; Elisp flychecker
  (setq flycheck-emacs-lisp-load-path 'inherit)
  (setq flycheck-emacs-lisp-initialize-packages t)
  ;; Seems it shows full error if multiline
  (setq flycheck-display-errors-function #'flycheck-display-error-messages-unless-error-list))


(use-package flyspell
  :straight nil
  :commands (flyspell-toggle)
  :config
  (defun flyspell-toggle ()
    "Toggle flyspell mode on current buffer."
    (interactive)
    (if flyspell-mode
        (progn
          (flyspell-mode -1)
          (message "Flyspell disabled..."))
      (flyspell-mode 1)
      (message "Flyspell enabled..."))))


(use-package indent-guide
  :bind (("C-<f10>" . indent-guide-global-mode)))


(use-package which-func
  :straight nil
  :config
  (set-face-attribute 'which-func nil :foreground "green"))


(use-package display-line-numbers
  :config
  ;; Even though `line-number-current-line' does not belong to `display-line-numbers' package,
  ;; it is used indirectly by it, so it's the best place to set it outside of customize.
  (set-face-attribute 'line-number-current-line nil :foreground "white"))


(use-package diff-mode
  :bind (:map diff-mode-map
              ("M-o" . other-window)) ; Remove `M-o' binding (Overrides 'diff-goto-source, which is defined by `o' as well)
  :hook ((diff-mode . (lambda () (setq truncate-lines t)))
         (diff-mode . display-line-numbers-mode)))


(use-package ediff
  :config
  ;; Layout configuration
  (require 'ediff-wind)
  (setq ediff-split-window-function #'split-window-horizontally)
  (setq ediff-window-setup-function #'ediff-setup-windows-plain)

  ;; Restoring windows and layout after an Ediff session:
  ;; https://emacs.stackexchange.com/questions/7482/restoring-windows-and-layout-after-an-ediff-session
  (defvar larumbe/ediff-last-windows nil)

  (defun larumbe/store-pre-ediff-winconfig ()
    (setq larumbe/ediff-last-windows (current-window-configuration)))

  (defun larumbe/restore-pre-ediff-winconfig ()
    (set-window-configuration larumbe/ediff-last-windows))

  (add-hook 'ediff-before-setup-hook #'larumbe/store-pre-ediff-winconfig)
  (add-hook 'ediff-quit-hook         #'larumbe/restore-pre-ediff-winconfig)

  ;; INFO: Face highlighting color fix due to theme customization:
  ;;   These faces were set by 'deeper-blue-theme.el': ~/.emacs.d/straight/repos/emacs/etc/themes/deeper-blue-theme.el:57
  ;;   Ediff comparison of buffers in Magit assumes the following Git convention to compare old to new: revision^..revision
  ;;   This caused that when comparing with ediff with the same range the diffB color was orange and diffA green.
  ;;   That was misleading since it showed adittions in orange and removed things in green.
  (set-face-attribute 'ediff-current-diff-B nil :background "green4"      :foreground "white" :inherit nil)
  (set-face-attribute 'ediff-fine-diff-B    nil :background "skyblue4"    :foreground "white" :inherit nil)
  (set-face-attribute 'ediff-odd-diff-B     nil :background "Grey50"      :foreground "White" :inherit nil)
  (set-face-attribute 'ediff-current-diff-A nil :background "darkorange3" :foreground "white" :inherit nil)
  (set-face-attribute 'ediff-fine-diff-A    nil :background "cyan4"       :foreground "white" :inherit nil)
  (set-face-attribute 'ediff-even-diff-A    nil :background "Grey50"      :foreground "White" :inherit nil))


(use-package diff-ansi
  :straight (:host codeberg
             :repo "ideasman42/emacs-diff-ansi")
  :commands (diff-ansi-mode diff-ansi-buffer)
  :config
  ;; INFO: Requires enabling of `diff-ansi-mode', which is buffer local.
  ;;       diff-so-fancy experience:
  ;;         - Requires updating .gitconfig with .e.g $ diff-so-fancy --set-defaults
  ;;         - Plus, configuration doesn't allow navigating chunks in magit, while `magit-delta' does.
  (setq diff-ansi-tool 'diff-so-fancy)
  (setq diff-ansi-use-magit-revision-diff t))


(use-package imenu-list
  :bind (("M-i" . modi/imenu-list-display-toggle))
  :bind ((:map imenu-list-major-mode-map
          ("M-RET" . modi/imenu-list-goto-entry-and-hide)))
  :config
  (setq imenu-list-size 0.15)
  (setq imenu-auto-rescan t)

  (defun modi/imenu-list-hide ()
    (interactive)
    (switch-to-buffer-other-window imenu-list-buffer-name)
    (quit-window))

  (defun modi/imenu-list-visible-p ()
    "Returns `t' if the `imenu-list' buffer is visible."
    (catch 'break
      (dolist (win (window-list))
        (when (string= imenu-list-buffer-name (buffer-name (window-buffer win)))
          (throw 'break t)))))

  (defun modi/imenu-list-display-toggle (noselect)
    "Toggle the display of Imenu-list buffer.

If NOSELECT is non-nil, do not select the imenu-list buffer."
    (interactive "P")
    (if (modi/imenu-list-visible-p)
        (modi/imenu-list-hide)
      (if noselect
          (imenu-list-noselect)
        (imenu-list))))

  (defun modi/imenu-list-goto-entry-and-hide ()
    "Execute `imenu-list-goto-entry' and hide the imenu-list buffer."
    (interactive)
    (imenu-list-goto-entry)
    (modi/imenu-list-hide))

  (defun modi/imenu-auto-update (orig-fun &rest args)
    "Auto update the *Ilist* buffer if visible."
    (prog1 ; Return value of the advising fn needs to be the same as ORIG-FUN
        (apply orig-fun args)
      (when (modi/imenu-list-visible-p)
        (imenu-list-update-safe)))) ; update `imenu-list' buffer

  (advice-add 'switch-to-buffer :around #'modi/imenu-auto-update)
  (advice-add 'revert-buffer    :around #'modi/imenu-auto-update))


(use-package hide-comnt
  :straight (:host github :repo "emacsmirror/emacswiki.org" :branch "master" :files ("hide-comnt.el"))
  :commands (hide/show-comments-toggle))


(use-package rainbow-delimiters)


(use-package wide-column
  :straight (:host github :repo "phillord/wide-column"
             :fork (:repo "gmlarumbe/wide-column"))
  :diminish
  :commands (wide-column-mode))


(use-package time-stamp
  :straight nil
  :hook ((before-save . time-stamp))
  :config
  (setq time-stamp-format "%:y-%02m-%02d %02H:%02M") ; Do not include user nor seconds
  (setq time-stamp-line-limit 20)) ; Default 8


(use-package indent-tools
  :bind (:map indent-tools-mode-map
         ("C-c >" . indent-tools-hydra/body)))


;;;; Sysadmin
(use-package server
  :demand
  :config
  (unless (server-running-p)
    (server-start)))


(use-package arch-packer
  :straight (:repo "brotzeit/arch-packer"
             :fork (:repo "gmlarumbe/arch-packer"))
  :bind (("C-x a" . arch-packer-hydra/body))
  :config
  (defun larumbe/arch-packer-command-toggle ()
    "Toggle between 'pacman' and 'paru'."
    (interactive)
    (if (string= arch-packer-default-command "pacman")
        (setq arch-packer-default-command "paru")
      (setq arch-packer-default-command "pacman"))
    (message "Set arch-packer command to: %s" arch-packer-default-command))

  (defhydra arch-packer-hydra (:color blue
                               :hint nil)
    ;; Pacman/Paru
    ("i" (arch-packer-install-package) "install" :column "Pacman/Paru")
    ("d" (arch-packer-delete-package) "delete")
    ("s" (arch-packer-search-package) "search")
    ("r" (arch-packer-list-packages) "list")
    ("t" (larumbe/arch-packer-command-toggle) "toggle")
    ;; Menu
    ("m" (arch-packer-menu-mark-unmark) "mark/unmark" :column "Menu")
    ("u" (arch-packer-menu-mark-upgrade) "mark-upgrade")
    ("U" (arch-packer-menu-mark-all-upgrades) "mark-all-upgrades")
    ("d" (arch-packer-menu-mark-delete) "mark-delete")
    ("x" (arch-packer-menu-execute) "execute")
    ("b" (arch-packer-menu-visit-homepage) "visit homepage")
    ("o" (arch-packer-display-output-buffer) "display output buffer")
    ;; Exit ;;
    ("q"   nil nil :color blue)
    ("C-g" nil nil :color blue)))


(use-package aurel) ;; Similar to `arch-packer', but just for AUR. Seems better to get info/voting. Supports AUR package downloading but not installation.


(use-package google-this
  :diminish
  :bind (("C-c / t" . google-this)
         ("C-c / l" . google-this-line)
         ("C-c / c" . google-this-translate-query-or-region))
  :config
  ;; Once a command present in :bind is executed the rest of `google-this-mode' commands will be available
  (google-this-mode 1))


(use-package google-translate
  :init
  (setq google-translate-default-source-language "en") ; English
  (setq google-translate-default-target-language "es") ; Spanish
  ;; Check `google-translate-supported-languages-alist'.
  ;; Use prefix arg to query for language, or set variables to nil
  :config
  (setq google-translate-backend-method 'curl))


(use-package howdoi
  :straight (:host github :repo "arthurnn/howdoi-emacs"))


(use-package deferred)


(use-package async)


(use-package pcap-mode)


(use-package jenkins
  :straight (:repo "rmuslimov/jenkins.el"
             :fork (:repo "gmlarumbe/jenkins.el" :branch "deferred"))
  :bind (:map jenkins-job-view-mode-map
         ("n" . next-line)
         ("p" . previous-line))
  :config
  (setq jenkins-colwidth-name 50)
  (setq larumbe/jenkins-compilation-parser "xrun")

  (defun larumbe/jenkins-switch-regex-parsing ()
    "Switch Jenkins regexp parsing for large files to save loading time.
This is because regexp parsing blocks Emacs execution and might not be useful for large files."
    (interactive)
    (if larumbe/jenkins-compilation-parse-console-output
        (progn
          (setq larumbe/jenkins-compilation-parse-console-output nil)
          (message "Disabling parsing of Jenkins console output"))
      (setq larumbe/jenkins-compilation-parse-console-output t)
      (message "Enabling parsing of Jenkins console output"))))


(use-package unison-mode
  ;; There are 2 packages, unison and unison-mode.
  ;; The first one for process invocation
  ;; The second one for syntax highlighting and process invocation -> Using this
  :mode (("\\.prf\\'" . unison-mode)))


(use-package unison-sync-minor-mode
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("minor-modes/unison-sync-minor-mode.el"))
  :after unison-mode
  :demand
  :bind (:map unison-mode-map
         ("C-c C-c" . unison-my-run))
  :hook ((unison-mode . unison-sync-minor-mode)))


(use-package ssh-tunnels
  :config
  (setq ssh-tunnels-name-width 25)
  (setq ssh-tunnels-host-width 20))


(use-package erc
  :straight nil
  :config
  (add-to-list 'erc-modules 'sasl))


(use-package env-switch
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/env-switch.el")))


(use-package exec-path-from-shell) ; Updates `exec-path' from $PATH. https://emacs.stackexchange.com/questions/550/exec-path-and-path


(use-package ytdl)


;;;; Misc
(use-package select ; GUI and Clipboard
  :straight nil
  :config
  (setq select-enable-clipboard t) ; Clipboard enabling: default = t
  (setq select-enable-primary t))  ; Primary clipboard:  default = nil


(use-package simple
  :diminish auto-fill-function
  :straight nil
  :bind (("M-n"     . next-error)     ; M-n and M-p are already overwritten at mode-line.el.
         ("M-p"     . previous-error) ; This mapping allows to step through errors in a non-compilation buffer
         ("C-<f12>" . auto-fill-mode)
         ("<f12>"   . toggle-truncate-lines))
  :config
  (setq line-number-mode nil)   ; Hide current line number from mode-line
  (setq save-interprogram-paste-before-kill t)
  (setq next-error-verbose nil)) ; Hide "next-locus on <file> minibuffer messages that interfered with flycheck/eldoc"


(use-package simple-utils
  :straight (:host github :repo "gmlarumbe/my-elisp-packages" :files ("libs/simple-utils.el"))
  :after simple
  :demand
  :config
  (advice-add 'newline :before-until #'larumbe/newline-advice) ; Kill *ag*/*xref* and other active buffers with RET/C-m
  (advice-add 'next-error-find-buffer :override #'larumbe/next-error-find-buffer)) ; Let flycheck and compilation-based coexist in a sensible manner.


(use-package hi-lock
  :straight nil
  :bind (("C-\\" . highlight-symbol-at-point)
         ("C-'" . unhighlight-regexp)))


(use-package elmacro
  :diminish elmacro-mode)


(use-package re-builder
  :config
  (setq reb-re-syntax 'read))  ;; Emacs double escaping (for single escaping use 'string)


(use-package man
  :straight nil
  :commands (Man-getpage-in-background) ; Used by `sh-script'
  :config
  (setq Man-notify-method 'pushy))


(use-package which-key
  :diminish)


(use-package browse-url
  :straight nil
  :config
  (setq browse-url-browser-function 'browse-url-firefox))


(use-package pdf-tools
  :bind (:map pdf-view-mode-map
              ("j"   . pdf-view-next-line-or-next-page)
              ("k"   . pdf-view-previous-line-or-previous-page)
              ("M-w" . pdf-view-kill-ring-save))
  :config
  (pdf-loader-install t))


(use-package autorevert
  :straight nil
  :diminish auto-revert-mode)


(use-package btc-ticker) ;; API of `coin-ticker' was outdated. Also tried `crypto-ticker-mode' but was a bit more complex than this one


(use-package htmlize)
;; https://emacs.stackexchange.com/questions/14403/how-can-i-copy-syntax-highlighted-code-as-rtf-or-html
;; Steps:
;;  1 - Open *scratch* buffer and set proper major-mode
;;  2 - Copy code snippet to *scratch* buffer
;;  3 - Run `htmlize-buffer'
;;  4 - Copy text to file.html
;;  5 - In apps like Outlook (Insert as text)
;;
;; Considerations
;;  - If using `htmlize-region' directly on a non-scratch buffer the black background shows up (and not as a square)
;;  - Check if `modi/htmlize-region-to-file' is defined for my-elisp-packages
;;    + This one uses a CSS based on leuven css (light theme maybe more suitable for blank background emails)
;;  - Package `highlight2clipboard' did not support gnu/linux


(use-package screenshot)
;; Requires ImageMagick and makes use of binary "import"
;;
;; Prerequisites:
;; - /etc/ImageMagick-7/policy.xml
;; Change to:
;; <policy domain="coder" rights="read | write" pattern="PS" />
;;
;; Procedure:
;;  a) - `screenshot'
;;     - Set filename: file.png, file.jpg, etc...
;;     - Scheme: local (save in ~/images/ requires previous mkdir)
;;  b) After executing a:
;;     - `screenshot-take' (reuses previous filename and scheme)


(use-package camcorder
  :commands (camcorder-start
             camcorder-record
             camcorder-stop))


(use-package font-lock-studio)


(use-package helpful
  :bind (("C-h f" . helpful-callable)
         ("C-h v" . helpful-variable)
         ("C-h k" . helpful-key)
         ("C-h d" . helpful-at-point)
         ("C-h F" . helpful-function)
         ("C-h C" . helpful-command))
  :config
  (setq counsel-describe-function-function #'helpful-callable)
  (setq counsel-describe-variable-function #'helpful-variable))


(use-package hierarchy
  :straight nil) ; INFO: For some reason, straight is downloading the repo instead of using the Emacs core one



;;;; Provide package
(provide 'init-packages)

;;; init-packages.el ends here
