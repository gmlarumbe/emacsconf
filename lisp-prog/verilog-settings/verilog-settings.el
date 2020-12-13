;;; verilog-settings.el --- Verilog/SystemVerilog  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;; (require 'compilation-settings)


(defvar larumbe/verilog-indent-level 4)
(defvar larumbe/verilog-use-own-custom-fontify t)

(defvar larumbe/verilog-open-dirs nil
  "List with directories of current opened `verilog-mode' buffers.
Used for verilog AUTO libraries, flycheck and Verilo-Perl hierarchy.")
(defvar larumbe/verilog-open-pkgs nil
  "List of currently opened SystemVerilog packages.")
(defvar larumbe/verilog-project-pkg-list nil
  "List of current open packages at projectile project.")

(defvar larumbe/flycheck-verilator-include-path nil)


;;; Basic settings
(use-package verilog-mode
  :mode (("\\.[st]*v[hp]*\\'" . verilog-mode) ;.v, .sv, .svh, .tv, .vp
         ("\\.psl\\'"         . verilog-mode)
         ("\\.vams\\'"        . verilog-mode)
         ("\\.vinc\\'"        . verilog-mode)
         ;; Other custom formats
         ("\\.vsrc\\'"        . verilog-mode)
         ("\\.vsrc.pp\\'"     . verilog-mode)
         ("\\.v.pp\\'"        . verilog-mode)
         ("\\.ppv\\'"         . verilog-mode)
         )
  :hook ((verilog-mode . larumbe/my-verilog-hook-machine-hooked)
         (verilog-mode . modi/verilog-mode-customization))
  :bind (:map verilog-mode-map
              ;; TODO: Breaks highlighting of comments since it modifies syntax table with isearch
              ;; ("C-s"      . larumbe/verilog-isearch-forward)
              ;; ("C-r"      . larumbe/verilog-isearch-backward)
              ;; End of TODO
              ("<return>" . larumbe/electric-verilog-terminate-line)
              ([delete]   . delete-forward-char)
              ("C-%"      . hide/show-comments-toggle)
              ("M-s ."    . larumbe/verilog-isearch-forward-symbol-at-point)
              ("M-f"      . larumbe/verilog-forward-word)
              ("M-b"      . larumbe/verilog-backward-word)
              ("M-i"      . larumbe/verilog-imenu)
              ("TAB"      . larumbe/electric-verilog-tab)
              ("C-M-a"    . verilog-beg-of-defun)
              ("C-M-e"    . verilog-end-of-defun)
              ("C-M-n"    . larumbe/find-verilog-token-fwd)
              ("C-M-p"    . larumbe/find-verilog-token-bwd)
              ("C-M-u"    . larumbe/find-verilog-module-instance-bwd)
              ("C-M-d"    . larumbe/find-verilog-module-instance-fwd)
              ("C-M-h"    . xah-select-current-block)
              ("C-c l"    . larumbe/verilog-insert-instance-from-file)
              ("C-c i"    . larumbe/verilog-indent-current-module)
              ("C-c a"    . larumbe/verilog-align-ports-current-module)
              ("C-c b"    . larumbe/verilog-beautify-current-module)
              ("C-c c"    . larumbe/verilog-toggle-connect-port)
              ("C-c C-t"  . hydra-verilog/body)
              ("C-c C-l"  . larumbe/verilog-align-parameters-current-module)
              ("C-c C-c"  . larumbe/verilog-connect-ports-recursively)
              ("C-c C-p"  . larumbe/verilog-preprocess)
              ("C-c C-f"  . larumbe/verilog-flycheck-mode)
              ("<f8>"     . larumbe/verilog-vhier-current-file))
  :config
  (setq verilog-indent-level             larumbe/verilog-indent-level)
  (setq verilog-indent-level-module      larumbe/verilog-indent-level)
  (setq verilog-indent-level-declaration larumbe/verilog-indent-level)
  (setq verilog-indent-level-behavioral  larumbe/verilog-indent-level)
  (setq verilog-indent-level-directive   larumbe/verilog-indent-level)
  (setq verilog-case-indent              larumbe/verilog-indent-level)
  (setq verilog-cexp-indent              larumbe/verilog-indent-level)

  (setq verilog-auto-delete-trailing-whitespace t) ; ‘delete-trailing-whitespace’ in ‘verilog-auto’.
  (setq verilog-auto-indent-on-newline          t) ; Self-explaining
  (setq verilog-auto-lineup                   nil) ; other options are 'declarations or 'all
  (setq verilog-auto-newline                  nil)
  (setq verilog-auto-endcomments                t)

  (setq verilog-indent-lists                    t) ; If set to nil, indentation will not properly detect we are inside a parenthesized expression (instance or ports/parameters)
  (setq verilog-indent-begin-after-if           t)
  (setq verilog-tab-always-indent               t) ; Indent even though we are not at the beginning of line
  (setq verilog-tab-to-comment                nil)
  (setq verilog-date-scientific-format          t)
  (setq verilog-case-fold                     nil) ; Regexps should NOT ignore case
  (setq verilog-align-ifelse                  nil)
  (setq verilog-minimum-comment-distance       10)

  ;; In case no custom schema is used, take following settings into account:
  (unless larumbe/verilog-use-own-custom-fontify
    (setq verilog-highlight-grouping-keywords     t)  ; begin/end DANGER: Overriden in verilog-font-lock.el (has no effect nowadays...)
    (setq verilog-highlight-translate-off         t)  ; Background highlight expressions such as // synopsys translate_off ... // synopsys translate_on
    (setq verilog-highlight-modules             nil)) ; Analogous to `verilog-highlight-includes', would highlight module while hovering mouse. However it's experimental/incomplete as the regexp is not consistent.

  ;; Many thanks to Kaushal Modi (https://scripter.co/)
  (load "~/.elisp/lisp-prog/verilog-settings/verilog-modi-setup.el")
  ;; TODO: Move it to another directory at some point

  ;; Bind chords
  (bind-chord "\\\\" #'modi/verilog-jump-to-module-at-point verilog-mode-map)
  (when (executable-find "ag")
    (bind-chord "\|\|" #'modi/verilog-find-parent-module verilog-mode-map))

  (modi/verilog-do-not-read-includes-defines-mode -1) ;; INFO: Larumbe: For Verilog AUTO. Set to 1 by modi to: "Stop cluttering my buffer list by not opening all the `included files."

  ;; Own advice to avoid indentation of outshine (overrides modi setup of `modi/outshine-allow-space-before-heading')
  (advice-add 'verilog-indent-line-relative :before-until #'larumbe/verilog-avoid-indenting-outshine-comments)
  ;; Modi multi-line defines (and allegedly outshine) indentation advice: DANGER: Still issues with following lines after multiline defines!
  (advice-add 'verilog-indent-line-relative :before-until #'modi/verilog-selective-indent) ;; Advise the indentation behavior of `indent-region' done using `C-M-\'
  (advice-add 'verilog-indent-line :before-until #'modi/verilog-selective-indent)          ;; Advise the indentation done by hitting `TAB' (modi multi-line defines)

  (require 'verilog-utils)
  (require 'verilog-templates)
  (require 'verilog-overrides)
  (require 'verilog-navigation)
  (require 'verilog-imenu)
  (require 'verilog-vhier)
  (require 'verilog-flycheck))


(provide 'verilog-settings)

;;; verilog-settings.el ends here
