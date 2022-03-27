;;; verilog-modi.el --- Kaushal Modi's customization  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; This file includes functions fetched from modi's modified `setup-verilog'
;; that are adviced to provide some extra/complementary functionality.
;;
;; It also includes hooks adding and modi's variable tweaking for personal customization.
;;
;;; Code:


(require 'setup-verilog)
(require 'ag) ; Load `ag' package so `ag-arguments' get updated with --stats to jump to first match

;;;; Navigation
(defun larumbe/verilog-find-parent-module ()
  "Same as `modi/verilog-find-parent-module'.
Additionally add xref push marker to the stack."
  (interactive)
  (let ((verilog-module-re (concat "^[[:blank:]]*" ;Elisp regexp
                                   "\\(?:module\\)[[:blank:]]+" ;Shy group
                                   "\\(?1:"
                                   modi/verilog-identifier-re ;Elisp regexp here!
                                   "\\)\\b"))
        module-name
        module-instance-pcre)
    (save-excursion
      (re-search-backward verilog-module-re)
      (setq module-name (match-string 1))
      (setq module-instance-pcre ;PCRE regex
            (concat "^\\s*"
                    module-name
                    "\\s+"
                    "(#\\s*\\((\\n|.)*?\\))*" ;optional hardware parameters
                                        ;'(\n|.)*?' does non-greedy multi-line grep
                    "(\\n|.)*?" ;optional newline/space before instance name
                    "([^.])*?" ;do not match ".PARAM (PARAM_VAL)," if any
                    "\\K"       ;don't highlight anything till this point
                    modi/verilog-identifier-pcre ;instance name
                    "(?=[^a-zA-Z0-9_]*\\()")) ;optional space/newline after instance name
                                        ;and before opening parenthesis `('
                                        ;don't highlight anything in (?=..)
      (let* ((ag-arguments ag-arguments)) ;Save the global value of `ag-arguments'
        ;; Search only through verilog type files.
        ;; See "ag --list-file-types".
        (add-to-list 'ag-arguments "--verilog" :append)
        (xref-push-marker-stack) ; INFO: Added by Larumbe
        (ag-regexp module-instance-pcre (projectile-project-root))))))



(defun larumbe/verilog-jump-to-module-at-point ()
  "Same as `modi/verilog-jump-to-module-at-point' but using ggtags."
  (interactive)
  (if (and (executable-find "global")
           (projectile-project-root))
      ;; `modi/verilog-which-func-xtra' contains the module name in
      ;; whose instance declaration the point is currently.
      (if (and (modi/verilog-find-module-instance)
               modi/verilog-which-func-xtra)
          (progn
            (ggtags-find-tag-dwim modi/verilog-which-func-xtra))
        ;; Do `pop-tag-mark' if this command is called when the
        ;; point in *not* inside a verilog instance.
        (pop-tag-mark))
    (user-error "Executable `global' is required for this command to work")))


;;;;; Setup
(advice-add 'modi/verilog-find-parent-module      :override #'larumbe/verilog-find-parent-module)
(advice-add 'modi/verilog-jump-to-module-at-point :override #'larumbe/verilog-jump-to-module-at-point)


;;;; Which-func
(defun larumbe/verilog-update-which-func-format ()
  "Same as `modi/verilog-update-which-func-format'.
Modify `which-func' face color and set a slightly different format from modi's."
  (let ((modi/verilog-which-func-echo-help
         (concat "mouse-1/scroll up: jump to header UP" "\n"
                 "mouse-3/scroll-down: jump to header DOWN")))

    (setq-local which-func-keymap
                (let ((map (make-sparse-keymap)))
                  ;; left click on mode line
                  (define-key map [mode-line mouse-1] #'modi/verilog-jump-to-header-dwim)
                  ;; scroll up action while mouse on mode line
                  (define-key map [mode-line mouse-4] #'modi/verilog-jump-to-header-dwim)
                  ;; middle click on mode line
                  (define-key map [mode-line mouse-2] #'modi/verilog-jump-to-header-dwim-fwd)
                  ;; scroll down action while mouse on mode line
                  (define-key map [mode-line mouse-5] #'modi/verilog-jump-to-header-dwim-fwd)
                  map))

    ;; Customised by Larumbe to keep `which-func' face and a slightly different format
    (if modi/verilog-which-func-xtra
        (setq-local which-func-format
                    `("["
                      (:propertize modi/verilog-which-func-xtra
                                   local-map ,which-func-keymap
                                   face (which-func :weight bold)
                                   mouse-face mode-line-highlight
                                   help-echo ,modi/verilog-which-func-echo-help)
                      ":"
                      (:propertize which-func-current
                                   local-map ,which-func-keymap
                                   face which-func
                                   mouse-face mode-line-highlightp
                                   help-echo ,modi/verilog-which-func-echo-help)
                      "]"))
      (setq-local which-func-format
                  `("["
                    (:propertize which-func-current
                                 local-map ,which-func-keymap
                                 face which-func
                                 mouse-face mode-line-highlight
                                 help-echo ,modi/verilog-which-func-echo-help)
                    "]")))))


;;;;; Setup
(advice-add 'modi/verilog-update-which-func-format :override #'larumbe/verilog-update-which-func-format)
(add-hook 'verilog-mode-hook #'modi/verilog-which-func)


;;;; Hideshow
(add-to-list 'modi/verilog-block-start-keywords "generate")
(add-to-list 'modi/verilog-block-end-keywords "endgenerate")
(delete "module" modi/verilog-block-start-keywords)
(delete "endmodule" modi/verilog-block-end-keywords)

(setq modi/verilog-block-start-keywords-re (regexp-opt modi/verilog-block-start-keywords 'symbols))
(setq modi/verilog-block-end-keywords-re (regexp-opt modi/verilog-block-end-keywords 'symbols))

(add-to-list 'hs-special-modes-alist
             `(verilog-mode ,(concat "(\\|" modi/verilog-block-start-keywords-re)
                            ,(concat ")\\|" modi/verilog-block-end-keywords-re)
                            nil
                            verilog-forward-sexp-function))


;;;; Misc
(add-hook 'verilog-mode-hook (lambda () (add-hook 'before-save-hook #'modi/verilog-block-end-comments-to-block-names nil :local)))

;; Do not break any `outline-mode'or `outshine' functionality
(advice-add 'verilog-indent-line-relative :before-until #'modi/verilog-selective-indent) ;; Advise the indentation behavior of `indent-region' done using `C-M-\'
(advice-add 'verilog-indent-line          :before-until #'modi/verilog-selective-indent) ;; Advise the indentation done by hitting `TAB' (modi multi-line defines)



(provide 'verilog-modi)

;;; verilog-modi.el ends here
