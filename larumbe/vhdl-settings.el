;;;;;;;;;;;;;;;;
;; VHDL setup ;;
;;;;;;;;;;;;;;;;

;;; Variables
(setq vhdl-clock-edge-condition (quote function))
(setq vhdl-company-name "HPInc")
(setq vhdl-conditions-in-parenthesis t)
(setq vhdl-default-library "xil_defaultlib")
(setq vhdl-end-comment-column 120)
(setq vhdl-platform-spec "Debian 9.1 VM")
(setq vhdl-reset-kind (quote sync))
(setq vhdl-speedbar-auto-open nil)

;;; Hooks
(defun my-vhdl-hook ()
  (setq tab-width 4)                    ; TAB Width for indentation
  (setq indent-tabs-mode nil)           ; Replace TAB with Spaces when indenting
  (setq vhdl-basic-offset 4)

  (fset 'insert-tab-vhdl (kbd "C-u 4 SPC")) ; Custom 4 spaces TAB key
  (fset 'remove-tab-vhdl (kbd "C-u 4 DEL")) ; Custom remove 4 spaces TAB key
  (local-set-key [f5] 'vhdl-compile)
  (local-set-key (kbd "<C-iso-lefttab>") 'insert-tab-vhdl)
  (local-set-key (kbd "C-M-<tab>") 'remove-tab-vhdl)

  ;; Autocomplete sources
  (set 'ac-sources
             '(
               ac-source-gtags
               )
             )

  ;; GHDL custom linter setup
  (setq vhdl-custom-ghdl-list
        '("GHDL-custom" "ghdl" "-i --ieee=synopsys -fexplicit -fno-color-diagnostics" "make" "-f \\1" nil "mkdir \\1" "./" "work/" "Makefile" "ghdl"
          ("ghdl_p: \\*E,\\w+ (\\([^ \\t\\n]+\\),\\([0-9]+\\)|\\([0-9]+\\)):" 1 2 3)
          ("" 0)
          ("\\1/entity" "\\2/\\1" "\\1/configuration" "\\1/package" "\\1/body" downcase)
          )
        )
  (add-to-list 'vhdl-compiler-alist vhdl-custom-ghdl-list)
  (vhdl-set-compiler "GHDL-custom")
  )

(add-hook 'vhdl-mode-hook 'my-vhdl-hook)
(add-hook 'vhdl-mode-hook 'vhdl-electric-mode)
(add-hook 'vhdl-mode-hook '(lambda () (setq compilation-error-regexp-alist (delete 'gnu compilation-error-regexp-alist))))



;;; Gtags
(defun larumbe/gtags-vhdl-files-pwd-recursive ()
  "Generate gtags.files for current directory. Purpose is to be used with dired mode for small projects, to save the regexp"
  (interactive)
  (larumbe/directory-files-recursively-to-file (list default-directory) "gtags.files" ".vhd[l]?$")
  )


(defun larumbe/ggtags-create-vhdl-tags-recursive ()
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-vhdl-files-pwd-recursive)
  (ggtags-create-tags default-directory))



;;; Functions redefinition
;; ...
