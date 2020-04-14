;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PROGRAMMING MODES CONFIGURATION FOR EMACS ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Common configuration
;;;; Common Programming modes hooks
(add-hook 'prog-mode-hook 'show-paren-mode)
(add-hook 'prog-mode-hook 'linum-mode)
(add-hook 'prog-mode-hook '(lambda () (setq truncate-lines t)))
(add-hook 'prog-mode-hook 'hs-minor-mode)
(add-hook 'prog-mode-hook 'outshine-mode)
(add-hook 'prog-mode-hook 'yas-minor-mode)
(add-hook 'prog-mode-hook 'fic-mode)
(add-hook 'prog-mode-hook 'ggtags-mode)
(unless (string-equal (system-name) "vl159.plano.hpicorp.net")
  (add-hook 'prog-mode-hook 'auto-complete-mode)
  (add-hook 'prog-mode-hook 'projectile-mode))

;;;; Keymapping
(defun my-prog-mode-hook ()
  (local-set-key (kbd "C-<tab>") 'hs-toggle-hiding)
  (local-set-key (kbd "C-c C-n") 'align-regexp)
  (local-set-key (kbd "C-c <C-f5>") 'flycheck-mode)
  )
(add-hook 'prog-mode-hook 'my-prog-mode-hook)



;;; Programming Languages Setups
;;;; Verilog / SystemVerilog
(load "~/.elisp/larumbe/verilog-settings.el")
;;;; VHDL
(load "~/.elisp/larumbe/vhdl-settings.el")


;;;; ELISP
;;;;; Hooks
(defun my-elisp-hook ()
  (set 'ac-sources
             '(
               ac-source-gtags
               ac-source-symbols
               )
             )
  (local-set-key (kbd "C-x C-.") 'larumbe/load-file-current-buffer) ; Own function useful to debug elisp (rudimentary)
  (local-set-key (kbd "C-c .") 'ffap)
  (local-set-key (kbd "C-c C-e") 'edebug-defun)
  (local-set-key (kbd "C-M-z") 'eval-region)
  )
(add-hook 'emacs-lisp-mode-hook 'my-elisp-hook)
(add-hook 'emacs-lisp-mode-hook '(lambda ()           ; TODO: Order in hooks cannot be ensured, so this might not work
                                   (interactive)      ; To avoid loading ggtags, just remove GTAGS, GGTAGS and GPATH generated files from (projectile-project-root)
                                   (ggtags-mode -1))) ; Better to use xref-find-definitions (since ggtags is generally enabled for prog-mode)



;;;; PYTHON
(use-package python-mode
  :mode (("\\SConstruct\\'" . python-mode))
  :config
  (setq py-number-face           font-lock-doc-face)
  (setq py-object-reference-face verilog-font-lock-grouping-keywords-face)
  (setq py-pseudo-keyword-face   font-lock-constant-face) ; True/False/None
  (setq py-try-if-face           font-lock-doc-face)
  (setq py-variable-name-face    font-lock-variable-name-face)
  (setq py-use-font-lock-doc-face-p t)
  )

;;;;; Variables
(setq python-check-command "pylint")

;;;;; Hooks
(defun my-python-hook ()
  (local-set-key (kbd "C-c C-p") 'python-send-line-or-region-and-step) ; Overrides `run-python'
  (local-set-key (kbd "C-c C-c") 'run-python)                          ; Overrides `python-shell-send-buffer'
  (local-set-key (kbd "C-M-n") 'forward-same-indent)
  (local-set-key (kbd "C-M-p") 'backward-same-indent)
  (local-set-key (kbd "C-c RET") 'ac-complete-jedi-direct)

  ;; Send text to an *ansi-term* running a Python interpreter (that may run in a remote machine)
  (local-set-key (kbd "C-c C-k") 'larumbe/python-send-line-or-region-and-step-remote-from-host)
  ;; Ignore indentation and send to an *ansi-term* running a Python interpretera Python term individual statements (that may run in a remote machine).
  (local-set-key (kbd "C-c C-l") 'larumbe/python-send-line-and-step-ansi-no-indent) ; Overrides `python-shell-send-file'
  ;; Allow for jedi-core pop not to be override
  ;; (define-key semantic-mode-map (kbd "C-c ,") nil)
  )

(add-hook 'python-mode-hook 'my-python-hook)
(unless (string-equal (system-name) "vl159.plano.hpicorp.net")
  (use-package jedi-core)
  (add-hook 'python-mode-hook 'jedi:setup))



;;;; SHELL-SCRIPT
(defun my-sh-mode-hook ()
  (local-set-key (kbd "C-c C-j") 'sh-switch-to-process-buffer)
  (local-set-key (kbd "C-c C-k") 'sh-send-line-or-region-and-step)
  (local-set-key (kbd "C-c C-p") 'larumbe/sh-send-line-or-region-and-step-ansi)
  (local-set-key (kbd "C-c C-t") 'hydra-sh-template/body)
  (set 'ac-sources
             '(
               ac-source-gtags
               ac-source-symbols
               )
             )
  )
(add-hook 'sh-mode-hook 'my-sh-mode-hook)


(defhydra hydra-sh-template (:color blue
                                    :hint nil)
  "
for s_e_quence           _i_f            _p_rintf            _a_rgs
for a_r_ithmetic         _c_ase          ec_h_o              _b_ang
for si_m_ple             _f_unction      printf _d_ebug      safe ba_n_g
_u_ntil                  _+_ add
_w_hile                  _s_elect
while inde_x_ed          _p_rint
^^
^^
"

  ("e"   (larumbe/hydra-yasnippet "for-seq"))
  ("r"   (larumbe/hydra-yasnippet "for-ar"))
  ("m"   (larumbe/hydra-yasnippet "for-simple"))
  ("u"   (larumbe/hydra-yasnippet "until"))
  ("w"   (larumbe/hydra-yasnippet "while"))
  ("f"   (larumbe/hydra-yasnippet "f"))
  ("p"   (larumbe/hydra-yasnippet "pr"))
  ("h"   (larumbe/hydra-yasnippet "e"))
  ("d"   (larumbe/hydra-yasnippet "pd"))
  ("a"   (larumbe/hydra-yasnippet "args"))
  ("b"   (larumbe/hydra-yasnippet "!"))
  ("n"   (larumbe/hydra-yasnippet "s!"))
  ("x"   (sh-indexed-loop))
  ("i"   (sh-if))
  ("c"   (sh-case))
  ("+"   (call-interactively 'sh-add))
  ("s"   (sh-select))
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))


;;;; C/C++
(defun my-cc-mode-hook ()
  (setq c-default-style "linux"         ; Indent and style
        c-basic-offset 4)

  (local-set-key (kbd "C-c .") 'semantic-ia-fast-jump)
  (local-set-key (kbd "C-c ,") 'pop-global-mark)
  (local-set-key (kbd "C-c C-.") 'semantic-complete-jump)
  (local-set-key (kbd "C-c f") 'semantic-ia-show-summary)
  (local-set-key (kbd "C-c <return>") 'semantic-analyze-possible-completions)

  (set 'ac-sources
             '(
               ac-source-semantic-raw
               ac-source-gtags
               )
             )
  )

(add-hook 'c-mode-common-hook 'my-cc-mode-hook)
(add-to-list 'auto-mode-alist '("\\.ino\\'" . c++-mode)) ;; Arduino Files in C-mode



;;;; TCL
(defun my-tcl-hook ()
  (local-set-key (kbd "C-c C-p") 'larumbe/tcl-send-line-or-region-and-step)
  (local-set-key (kbd "C-c C-k") 'larumbe/tcl-send-line-or-region-and-step-vivado-shell)

  (modify-syntax-entry ?$ ".")
  )
(add-hook 'tcl-mode-hook 'my-tcl-hook)



;;;; PERL
(defalias 'perl-mode 'cperl-mode)


;;;; XML
;;;;; Variables
(setq nxml-child-indent 4)
;;;;; Hooks
(defun my-xml-mode-hook ()
  (local-set-key (kbd "C-c C-p") 'larumbe/docbook-to-pdf-current-buffer)
  (local-set-key (kbd "C-c C-k") 'larumbe/docbook-to-pdf-current-buffer-no-preview)
  (local-set-key (kbd "C-c C-t") 'hydra-nxml-docbook-template/body)

  (set 'ac-sources
             '(ac-source-gtags
               ac-source-symbols))
  )

(add-hook 'nxml-mode-hook 'my-xml-mode-hook)
;; INFO: Since it is not a childe of prog-mode, requires common configuration settings
(add-hook 'nxml-mode-hook 'show-paren-mode)
(add-hook 'nxml-mode-hook 'linum-mode)
(add-hook 'nxml-mode-hook '(lambda () (setq truncate-lines t)))
(add-hook 'nxml-mode-hook 'hs-minor-mode)
(add-hook 'nxml-mode-hook 'outshine-mode)
(add-hook 'nxml-mode-hook 'yas-minor-mode)
(add-hook 'nxml-mode-hook 'fic-mode)
(add-hook 'nxml-mode-hook 'ggtags-mode)
;; Prog-mode hook keybindings
(add-hook 'nxml-mode-hook 'my-prog-mode-hook)

(unless (string-equal (system-name) "vl159.plano.hpicorp.net")
  (add-hook 'nxml-mode-hook 'auto-complete-mode)
  (add-hook 'nxml-mode-hook 'projectile-mode))


;;;; VIVADO
(use-package vivado-mode
  :load-path "~/elisp/download/"
  :mode (("\\.xdc\\'" . vivado-mode))
  :hook ((vivado-mode . my-vivado-mode-hook))
  :config
  (defun my-vivado-mode-hook ()
    (set 'ac-sources
         '(ac-source-gtags
           ac-source-symbols)))
  )


;;;; HTML
(use-package mhtml-mode
  :bind (:map mhtml-mode-map
              ("C-M-u" . sgml-skip-tag-backward)
              ("C-M-d" . sgml-skip-tag-forward))
  :config
  (setq sgml-basic-offset 4) ; Indentation of parent mode
  (defun my-mhtml-mode-hook ()
    (set 'ac-sources
         '(
           ac-source-gtags
           ac-source-symbols
           )
         )
    )
  (add-hook 'mhtml-mode-hook 'my-mhtml-mode-hook)
  )


;;;; MARKDOWN
(use-package markdown-mode
  :config
  (setq markdown-command "/usr/bin/pandoc -s")
  )


;;;; CONF
(use-package conf-mode
  :mode (("\\.service\\'" . conf-mode)
         ("\\rc\\'"       . conf-mode)
         ("\\.sby\\'"     . conf-mode)
         )
  :config
  ;; INFO: Since it is not a childe of prog-mode, requires common configuration settings
  (add-hook 'conf-mode-hook 'show-paren-mode)
  (add-hook 'conf-mode-hook 'linum-mode)
  (add-hook 'conf-mode-hook '(lambda () (setq truncate-lines t)))
  (add-hook 'conf-mode-hook 'hs-minor-mode)
  (add-hook 'conf-mode-hook 'outshine-mode)
  (add-hook 'conf-mode-hook 'yas-minor-mode)
  (add-hook 'conf-mode-hook 'fic-mode)
  (add-hook 'conf-mode-hook 'ggtags-mode)
  ;; Prog-mode keybindings
  (add-hook 'conf-mode-hook 'my-prog-mode-hook)
  )

;;;; JSON
(use-package json-mode)

;;;; GO!
(use-package go-mode)

;;;; MATLAB
;; BUG: use-package installs it properly but cannot load matlab-mode...
;; (use-package matlab-mode)

;;;; NASL
(use-package nasl-mode
  :load-path "~/.elisp/download/")

;;;; RDL
(use-package rdl-mode
  :load-path "~/.elisp/download/")
