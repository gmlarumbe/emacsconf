;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PROGRAMMING MODES CONFIGURATION FOR EMACS ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Common configuration
(use-package prog-mode
  :ensure nil
  :bind (:map prog-mode-map
              ("C-<tab>" . hs-toggle-hiding)
              ("C-c C-n" . align-regexp))
  :hook ((prog-mode . my-prog-mode-hook))
  :config
  (defun my-prog-mode-hook ()
    ;; Verilog has its own flycheck-mode wrapper function
    (unless (string-equal major-mode "verilog-mode")
      (local-set-key (kbd "C-c C-f") #'flycheck-mode))
    ;; Customizations
    (show-paren-mode     1)
    (linum-mode          1)
    (hs-minor-mode       1)
    (outshine-mode       1)
    (yas-minor-mode      1)
    (fic-mode            1)
    (larumbe/ggtags-mode 1)
    (auto-complete-mode  1)
    (projectile-mode     1)
    (setq truncate-lines t)))


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
    (modify-syntax-entry ?$ "."))

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
(use-package vivado-mode
  :load-path "~/.elisp/download/"
  :mode (("\\.xdc\\'" . vivado-mode))
  :hook ((vivado-mode . my-vivado-mode-hook))
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
           ac-source-symbols))))


;;;; MARKDOWN
(use-package markdown-mode
  :config
  (setq markdown-command "/usr/bin/pandoc -s"))


;;;; CONF
(use-package conf-mode
  :mode (("\\.service\\'" . conf-mode)
         ("\\rc\\'"       . conf-mode)
         ("\\.sby\\'"     . conf-mode))
  :hook ((conf-mode . my-prog-mode-hook))) ; Since it is not a childe of prog-mode, requires common configuration settings


;;;; MAKEFILE
(use-package make-mode
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

