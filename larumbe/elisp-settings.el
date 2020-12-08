;;; elisp-settings.el --- Elisp  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package elisp-mode
  :ensure nil
  :bind (:map emacs-lisp-mode-map
              ("C-x C-." . larumbe/load-file-current-buffer)
              ("C-c C-e" . edebug-defun)
              ("C-M-z"   . eval-region)
              ("C-c C-b" . larumbe/byte-compile-current-buffer)
              ("C-c C-f" . larumbe/elisp-flycheck-mode)
              ("C-c h"   . sanityinc/headerise-elisp)
              ("M-."     . larumbe/xref-find-definitions)
              ("M-?"     . larumbe/xref-find-reference-at-point))
  :hook ((emacs-lisp-mode . my-elisp-hook))
  :config
  (setq flycheck-emacs-lisp-load-path 'inherit)
  (setq flycheck-emacs-lisp-initialize-packages t)

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
    (prettify-symbols-mode 1)
    (rainbow-delimiters-mode 1)
    (larumbe/elisp-flycheck-mode 1)
    (set 'ac-sources '(ac-source-gtags ac-source-symbols)))


  (defun larumbe/byte-compile-current-buffer ()
    "Byte-compile file of current visited buffer."
    (interactive)
    (byte-compile-file buffer-file-name))


  (defun larumbe/elisp-flycheck-mode (&optional enable)
    "Flycheck-mode Elisp wrapper function.
Disable `eldoc-mode' if flycheck is enabled to avoid minibuffer collisions."
    (interactive)
    ;; Interactive toggling
    (unless enable
      (if eldoc-mode
          (progn
            (eldoc-mode -1)
            (flycheck-mode 1)
            (message "Flycheck enabled"))
        (eldoc-mode 1)
        (flycheck-mode -1)
        (message "Flycheck disabled")))
    ;; Non-interactive
    (when enable
      (if (> enable 0)
          (progn
            (flycheck-mode 1)
            (eldoc-mode -1))
        (flycheck-mode -1)
        (eldoc-mode 1))))

  ;; Copied from Steve Purcell
  (defun sanityinc/headerise-elisp ()
    "Add minimal header and footer to an elisp buffer in order to placate flycheck."
    (interactive)
    (let* ((fname (if (buffer-file-name)
                      (file-name-nondirectory (buffer-file-name))
                    (error "This buffer is not visiting a file")))
           (pname (file-name-sans-extension fname))
           (desc (read-string "Package description: ")))
      (save-excursion
        (goto-char (point-min))
        (insert ";;; " fname " --- " desc  "  -*- lexical-binding: t -*-\n"
                ";;; Commentary:\n"
                ";;; Code:\n\n")
        (goto-char (point-max))
        (insert "\n\n(provide '" pname ")\n\n")
        (insert ";;; " fname " ends here\n"))))

  ;; INFO: Copied from modi's setup
  (defhydra hydra-edebug (:color amaranth
                                 :hint  nil)
    "
    EDEBUG MODE
^^_<SPC>_ step             ^^_f_ forward sexp         _b_reakpoint set                previous _r_esult      _w_here                    ^^_d_ebug backtrace
^^_n_ext                   ^^goto _h_ere              _u_nset breakpoint              _e_val expression      bounce _p_oint             _q_ top level (_Q_ nonstop)
_g_o (_G_ nonstop)         ^^_I_nstrument callee      next _B_reakpoint               _E_val list            _v_iew outside             ^^_a_bort recursive edit
_t_race (_T_ fast)         step _i_n/_o_ut            _x_ conditional breakpoint      eval _l_ast sexp       toggle save _W_indows      ^^_S_top
_c_ontinue (_C_ fast)      ^^^^                       _X_ global breakpoint
"
    ("<SPC>" edebug-step-mode)
    ("n"     edebug-next-mode)
    ("g"     edebug-go-mode)
    ("G"     edebug-Go-nonstop-mode)
    ("t"     edebug-trace-mode)
    ("T"     edebug-Trace-fast-mode)
    ("c"     edebug-continue-mode)
    ("C"     edebug-Continue-fast-mode)

    ("f"     edebug-forward-sexp)
    ("h"     edebug-goto-here)
    ("I"     edebug-instrument-callee)
    ("i"     edebug-step-in)
    ("o"     edebug-step-out)

    ;; breakpoints
    ("b"     edebug-set-breakpoint)
    ("u"     edebug-unset-breakpoint)
    ("B"     edebug-next-breakpoint)
    ("x"     edebug-set-conditional-breakpoint)
    ("X"     edebug-set-global-break-condition)

    ;; evaluation
    ("r"     edebug-previous-result)
    ("e"     edebug-eval-expression)
    ("l"     edebug-eval-last-sexp)
    ("E"     edebug-visit-eval-list)

    ;; views
    ("w"     edebug-where)
    ("p"     edebug-bounce-point)
    ("v"     edebug-view-outside) ; maybe obsolete??
    ("P"     edebug-view-outside) ; same as v
    ("W"     edebug-toggle-save-windows)

    ("d"     edebug-backtrace)

    ;; quitting and stopping
    ("q"     top-level :color blue)
    ("Q"     edebug-top-level-nonstop :color blue)
    ("a"     abort-recursive-edit :color blue)
    ("S"     edebug-stop :color blue))
  (with-eval-after-load 'edebug
    (bind-key "?" #'hydra-edebug/body edebug-mode-map)))


(provide 'elisp-settings)

;;; elisp-settings.el ends here
