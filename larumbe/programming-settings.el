;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PROGRAMMING MODES CONFIGURATION FOR EMACS ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Common configuration
(use-package prog-mode
  :ensure nil
  :bind (:map prog-mode-map
              ("C-<tab>" . hs-toggle-hiding)
              ("C-c C-n" . align-regexp))
  :hook ((prog-mode . my-prog-mode-hook)
         (prog-mode . my-prog-mode-hook-perf))
  :config
  (defun my-prog-mode-hook ()
    "Basic Hook for derived programming modes."
    ;; Verilog has its own flycheck-mode wrapper function
    (unless (string-equal major-mode "verilog-mode")
      (local-set-key (kbd "C-c C-f") #'flycheck-mode))
    ;; Customizations
    (show-paren-mode     1)
    (linum-mode          1)
    (outshine-mode       1)
    (fic-mode            1)
    (setq truncate-lines t))

  (defun my-prog-mode-hook-perf ()
    "Hook for programming modes that require a bit more of CPU performance.
Could be removed independently from previous one if needed in remote machines with resource issues."
    (projectile-mode     1)
    (larumbe/ggtags-mode 1)
    (auto-complete-mode  1)
    (yas-minor-mode      1)
    (hs-minor-mode       1)))



(use-package flycheck
  :diminish)


(use-package flyspell
  :ensure nil
  :config
  (defun flyspell-toggle ()
    "Toggle flyspell mode on current buffer."
    (interactive)
    (if (bound-and-true-p flyspell-mode)
        (call-interactively #'flyspell-mode nil)
      (progn
        (call-interactively #'flyspell-mode 1)
        (call-interactively #'flyspell-prog-mode 1)
        (call-interactively #'flyspell-buffer)))))


(use-package hydra
  :config
  (defun larumbe/hydra-yasnippet (snippet)
    "Function/Macro to integrate YASnippet within Hydra"
    (interactive)
    (progn
      (insert snippet)
      (yas-expand))))


(use-package yasnippet
  :diminish yasnippet yas-minor-mode
  :config
  (use-package yasnippet-snippets)                      ; Install MELPA snippets database
  (add-to-list 'yas-snippet-dirs "~/.elisp/snippets")   ; Add snippets fetched from GitHub and customized ones. DO NOT Append to give them more precendence in case of collision
  (yas-reload-all))


(use-package diff-mode
  :bind (:map diff-mode-map
              ("M-o" . other-window)) ; Remove `M-o' binding (Overrides 'diff-goto-source, which is defined by `o' as well)
  :hook ((diff-mode . (lambda () (setq truncate-lines t)))
         (diff-mode . linum-mode))
  :config
  (setq ediff-split-window-function #'split-window-horizontally)
  (setq ediff-window-setup-function #'ediff-setup-windows-plain))


(use-package fic-mode
  :config
  (setq fic-activated-faces '(font-lock-doc-face  font-lock-comment-face))
  (setq fic-highlighted-words '("FIXME" "TODO" "BUG" "DANGER" "INFO"))

  (defun larumbe/clean-fic-keywords-dir ()
    "Perform an `ag-regexp' of `fic-mode' highlighted keywords in selected DIR
in order to check pending project actions. "
    (interactive)
    (let ((kwd)
          (path)
          (ag-arguments ag-arguments) ; Save the global value of `ag-arguments' (copied from modi)
          (regex)
          (files)
          )
      (setq kwd (completing-read "Select keyword: " 'fic-highlighted-words))
      (setq path (read-directory-name "Directory: "))
      ;; (setq regex (completing-read "Select file regex: " 'regex))
      (setq files (completing-read "Select file regex: " '("(System)Verilog" "Python" "elisp")))
      (pcase files
        ("(System)Verilog" (setq regex ".[s]?v[h]?$")) ; +Headers
        ("Python"          (setq regex ".py$"))
        ("elisp"           (setq regex ".el$"))
        )
      ;; Copied from AG for `modi/verilog-find-parent-module'
      (add-to-list 'ag-arguments "-G" :append)
      (add-to-list 'ag-arguments regex :append)
      (ag-regexp kwd path))))


(use-package auto-complete
  :diminish
  :bind (:map ac-completing-map
              ("C-n" . ac-next)
              ("C-p" . ac-previous)
              ("C-j" . ac-complete)
              ("RET" . ac-complete))
  :config
  (setq ac-delay 1.3)
  (setq ac-etags-requires 1)
  ;; INFO: Auto-complete has 3 mode-maps: https://emacs.stackexchange.com/questions/3958/remove-tab-trigger-from-auto-complete
  (define-key ac-mode-map       (kbd "TAB") nil)
  (define-key ac-completing-map (kbd "TAB") nil)
  (define-key ac-completing-map [tab] nil)

  ;; Default sources will be `ac-source-words-in-same-mode-buffers'

  ;; Provides `ac-source-gtags'
  (use-package auto-complete-gtags
    :load-path "~/.elisp/download"
    :config
    (setq ac-gtags-modes '(c-mode cc-mode c++-mode verilog-mode emacs-lisp-mode vhdl-mode sh-mode python-mode tcl-mode)))

  ;; Provides `ac-source-verilog'
  (use-package auto-complete-verilog
    :load-path "~/.elisp/download/"))


(use-package imenu-list
  :config
  (setq imenu-list-size 0.15)
  (setq imenu-auto-rescan t))


(use-package hide-comnt
  :load-path "~/.elisp/download/")



;;; Programming Languages Setups
;;;; Verilog / SystemVerilog
(load "~/.elisp/larumbe/verilog-settings.el")
;;;; VHDL
(load "~/.elisp/larumbe/vhdl-settings.el")
;;;; Font-lock for HDLs
(load "~/.elisp/larumbe/hdl-font-lock.el")


;;;; PYTHON
(load "~/.elisp/larumbe/python-settings.el")


;;;; ELISP
(use-package elisp-mode
  :ensure nil
  :bind (:map emacs-lisp-mode-map
              ("C-x C-." . larumbe/load-file-current-buffer)
              ("C-c C-e" . edebug-defun)
              ("C-M-z"   . eval-region)
              ("M-."     . larumbe/xref-find-definitions)
              ("M-?"     . larumbe/xref-find-reference-at-point))
  :hook ((emacs-lisp-mode . my-elisp-hook))
  :config
  (defun larumbe/xref-find-definitions ()
    "Wrapper of `xref-find-definitions' to visit a tags/files depending
on where the point is (similar to `larumbe/ggtags-find-tag-dwim')"
    (interactive)
    (if (file-exists-p (thing-at-point 'filename))
        (larumbe/find-file-at-point)
      (xref-find-definitions (thing-at-point 'symbol))))

  (defun larumbe/xref-find-reference-at-point ()
    "Find reference of symbol at point"
    (interactive)
    (xref-find-references (thing-at-point 'symbol)))

  (defun my-elisp-hook ()
    (set 'ac-sources '(ac-source-gtags ac-source-symbols))))



;;;; SHELL-SCRIPT
(use-package sh-script
  :ensure nil
  :bind (:map sh-mode-map
              ("C-c C-j" . sh-switch-to-process-buffer)
              ("C-c C-k" . sh-send-line-or-region-and-step)
              ("C-c C-p" . larumbe/sh-send-line-or-region-and-step-ansi)
              ("C-c C-t" . hydra-sh-template/body))
  :hook ((sh-mode . my-sh-mode-hook))
  :config
  (defun my-sh-mode-hook ()
    (set 'ac-sources '(ac-source-gtags ac-source-symbols)))

  (defhydra hydra-sh-template (:color blue :hint nil) "
for si_m_ple           _i_f            _p_rintf            _a_rgs
fo_r_ c-style          if-e_l_se       printf _d_ebug      _b_ang
_u_ntil                _c_ase          _e_cho              safe ba_n_g
_w_hile                _f_unction
while inde_x_ed        _+_ add
^^                     _s_elect
^^
^^
^^
"
    ("r"   (larumbe/hydra-yasnippet "forc"))
    ("m"   (larumbe/hydra-yasnippet "for"))
    ("u"   (larumbe/hydra-yasnippet "until"))
    ("w"   (larumbe/hydra-yasnippet "while"))
    ("f"   (larumbe/hydra-yasnippet "f"))
    ("p"   (larumbe/hydra-yasnippet "pr"))
    ("e"   (larumbe/hydra-yasnippet "e"))
    ("d"   (larumbe/hydra-yasnippet "pd"))
    ("a"   (larumbe/hydra-yasnippet "args"))
    ("b"   (larumbe/hydra-yasnippet "!"))
    ("n"   (larumbe/hydra-yasnippet "s!"))
    ("x"   (sh-indexed-loop))
    ("i"   (larumbe/hydra-yasnippet "if"))
    ("l"   (sh-if)) ;;  if - elif - else
    ("c"   (sh-case))
    ("+"   (call-interactively #'sh-add))
    ("s"   (sh-select))
    ("q"   nil nil :color blue)
    ("C-g" nil nil :color blue))

  (defun larumbe/sh-send-line-or-region-and-step-ansi ()
    "Same as `sh-send-line-or-region-and-step' but for *ansi-term* process"
    (interactive)
    (let (from to end)
      (if (use-region-p)
          (setq from (region-beginning)
                to (region-end)
                end to)
        (setq from (line-beginning-position)
              to (line-end-position)
              end (1+ to)))
      (comint-send-string (get-buffer-process "*ansi-term*")
                          (concat (buffer-substring-no-properties from to) "\n"))
      (goto-char end)))

  (defun sh-switch-to-process-buffer ()
    (interactive)
    (pop-to-buffer (process-buffer (get-process "shell")) t)))



;;;; C/C++
(use-package cc-mode
  :mode (("\\.ino\\'" . c-or-c++-mode))
  :bind (:map c-mode-map ; Also inherited by c++ buffers, not in the other direction!
              ("C-c f" . semantic-ia-show-summary)
              ("C-c ." . semantic-ia-fast-jump)
              ("C-c ," . pop-global-mark) ; Requires unbinding of <C-c ,> at semantic-mode-map
              )
  :hook ((c-mode-common . my-cc-mode-hook))
  :config
  (setq c-default-style "linux") ; Indent and style
  (setq c-basic-offset 4)

  (defun my-cc-mode-hook ()
    (set 'ac-sources '(ac-source-semantic-raw ac-source-gtags)))

  (use-package semantic
    :bind (:map semantic-mode-map
                ("C-c ," . nil)) ; INFO: Unbinds ALL semantic commands, since C-c , is the prefix
    :hook ((c-mode-common . semantic-mode))))


;;;; TCL
(use-package tcl
  :bind (:map tcl-mode-map
              ("C-c C-p" . larumbe/tcl-send-line-or-region-and-step)
              ("C-c C-k" . larumbe/tcl-send-line-or-region-and-step-vivado-shell))
  :hook ((tcl-mode . my-tcl-hook))
  :config
  (defun my-tcl-hook ()
    (modify-syntax-entry ?$ ".")
    ;; Reuse hdl font-lock faces
    (setq larumbe/tcl-font-lock-additional-keywords
          (list
           (list larumbe/braces-regex         0 larumbe/font-lock-braces-face)
           (list larumbe/brackets-regex       0 larumbe/font-lock-brackets-face)
           ))
    (font-lock-add-keywords 'tcl-mode larumbe/tcl-font-lock-additional-keywords))

  (defun larumbe/tcl-send-line-or-region-and-step ()
    "Send the current line to the inferior shell and step to the next line.
When the region is active, send the region instead.
Copied from `sh-send-line-or-regin-and-step' for SH Shell scripting "
    (interactive)
    (let (from to end (proc (inferior-tcl-proc)))
      (if (use-region-p)
          (setq from (region-beginning)
                to (region-end)
                end to)
        (setq from (line-beginning-position)
              to (line-end-position)
              end (1+ to)))
      (tcl-send-string proc (buffer-substring-no-properties from to))
      (tcl-send-string proc "\n")
      (goto-char end))))



;;;; XML
(use-package nxml-mode
  :ensure nil
  :hook ((nxml-mode . my-xml-mode-hook)
         (nxml-mode . my-prog-mode-hook)) ; Since it is not a child of prog-mode, requires common configuration settings
  :config
  (setq nxml-child-indent 4)

  (defun my-xml-mode-hook ()
    (set 'ac-sources '(ac-source-gtags
                       ac-source-symbols))))


;;;; DOCBOOK
(use-package docbook-mode
  :load-path "~/.elisp/larumbe/own-modes/majors/"
  :mode (("\\.docbook\\.xml" . docbook-mode)))


;;;; VIVADO
(use-package vivado-utils
  :load-path "~/.elisp/larumbe/own-modes/majors/"
  :mode (("\\.xdc\\'" . vivado-xdc-mode))
  :hook ((vivado-mode . my-vivado-mode-hook))
  :demand t ; INFO: Force loading of all the functions in the file
  :config
  (defun my-vivado-mode-hook ()
    (set 'ac-sources '(ac-source-gtags
                       ac-source-symbols))))


;;;; HTML
(use-package mhtml-mode
  :bind (:map mhtml-mode-map
              ("C-M-u" . sgml-skip-tag-backward)
              ("C-M-d" . sgml-skip-tag-forward))
  :hook ((mthml-mode . my-mhtml-mode-hook))
  :config
  (setq sgml-basic-offset 4) ; Indentation of parent mode
  (defun my-mhtml-mode-hook ()
    (set 'ac-sources
         '(ac-source-gtags
           ac-source-symbols)))

  (use-package web-beautify
    ;; Requires 'js-beautify' binary installed from npm (nodejs)
    :bind (:map mhtml-mode-map
                ("C-c b h" . web-beautify-html)
                ("C-c b j" . web-beautify-js)
                ("C-c b c" . web-beautify-css))))




;;;; MARKDOWN
(use-package markdown-mode
  :config
  (setq markdown-command "/usr/bin/pandoc -s"))


;;;; CONF
(use-package conf-mode
  :mode (("\\.service\\'"      . conf-mode)
         ("\\.sby\\'"          . conf-mode)
         ("\\reg.sim.files\\'" . conf-mode)
         )
  :hook ((conf-mode . my-prog-mode-hook))) ; Since it is not a childe of prog-mode, requires common configuration settings


;;;; MAKEFILE
(use-package make-mode
  :mode (("\\.mf\\'" . makefile-mode))
  :ensure nil)

;;;; PERL
(defalias 'perl-mode 'cperl-mode)

;;;; JSON
(use-package json-mode)

;;;; GO!
(use-package go-mode)

;;;; MATLAB
(use-package matlab
  :ensure matlab-mode
  :mode (("\\.m\\'" . matlab-mode))
  :config
  (setq matlab-indent-function t)
  (setq matlab-shell-command "matlab"))

;;;; NASL
(use-package nasl-mode
  :load-path "~/.elisp/download/")

;;;; RDL
(use-package rdl-mode
  :load-path "~/.elisp/download/")

;;;; Yocto
(use-package mmm-mode) ; Multi-major-mode
(use-package bitbake)  ; Recipes
(use-package dts-mode) ; Device tree

;;;; PHP
(use-package php-mode
  :bind
  (:map php-mode-map
        ;; Overrides `c-backward-conditional' but this is only used for interactive testing of PHP functions
        ("C-c C-p" . larumbe/sh-send-line-or-region-and-step-ansi)))

;;;; AHK
(use-package ahk-mode
  ;; DANGER: Even though it is definde as prog-mode derived, hooks are not automatically loaded
  :hook ((ahk-mode . my-prog-mode-hook)
         (ahk-mode . my-prog-mode-hook-perf))
  :config
  (setq ahk-indentation 2))
