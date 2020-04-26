;;;;;;;;;;;;;;;;
;; VHDL setup ;;
;;;;;;;;;;;;;;;;

;;; Basic settings
(use-package vhdl-mode
  :load-path "~/.elisp/larumbe/own-modes/override"
  :bind (:map vhdl-mode-map
              ("C-M-a"           . vhdl-beginning-of-defun)
              ("C-M-e"           . vhdl-end-of-defun)
              ("C-M-d"           . larumbe/find-vhdl-module-instance-fwd)
              ("C-M-u"           . larumbe/find-vhdl-module-instance-bwd)
              ("C-M-p"           . vhdl-backward-same-indent)
              ("C-M-n"           . vhdl-forward-same-indent)
              ("<f5>"            . vhdl-compile)
              ("<C-iso-lefttab>" . insert-tab-vhdl)
              ("C-M-<tab>"       . remove-tab-vhdl)
              )
  :init   ; INFO: Requires to be set before loading package in order to variables like faces to take effect
  (fset 'insert-tab-vhdl (kbd "C-u 4 SPC")) ; Custom 4 spaces TAB key
  (fset 'remove-tab-vhdl (kbd "C-u 4 DEL")) ; Custom remove 4 spaces TAB key
  ;; Fontify
  (setq larumbe/vhdl-use-own-custom-fontify t) ; To refresh font-lock call `larumbe/vhdl-font-lock-init'

  :config
  (setq vhdl-clock-edge-condition (quote function))
  (setq vhdl-company-name "")
  (setq vhdl-conditions-in-parenthesis t)
  (setq vhdl-default-library "xil_defaultlib")
  (setq vhdl-end-comment-column 120)
  (setq vhdl-platform-spec "Debian 9.1")
  (setq vhdl-reset-kind (quote sync))
  (setq vhdl-speedbar-auto-open nil)
  (setq vhdl-standard '(08 nil))
  (setq vhdl-project "AXI Interface Converter")

  (setq vhdl-basic-offset 4)
  (setq tab-width 4)                    ; TAB Width for indentation
  (setq indent-tabs-mode nil)           ; Replace TAB with Spaces when indenting

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
  (vhdl-electric-mode 1)

  (bind-chord "\\\\" #'larumbe/vhdl-jump-to-module-at-point vhdl-mode-map)
  (when (executable-find "ag")
    (bind-chord "\|\|" #'larumbe/vhdl-find-parent-module vhdl-mode-map))
  )



;;; Hooks
(defun my-vhdl-hook ()
  (set 'ac-sources '(ac-source-gtags))
  )
(add-hook 'vhdl-mode-hook 'my-vhdl-hook)


;;; Gtags
(defun larumbe/gtags-vhdl-files-pwd-recursive ()
  "Generate gtags.files for current directory. Purpose is to be used with dired mode for small projects, to save the regexp"
  (larumbe/directory-files-recursively-to-file default-directory "gtags.files" ".vhd[l]?$")
  )


(defun larumbe/ggtags-create-vhdl-tags-recursive ()
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-vhdl-files-pwd-recursive)
  (ggtags-create-tags default-directory))



;;; Navigation
(defvar larumbe/vhdl-entity-re "^\\s-*\\(entity\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)")
(defvar larumbe/vhdl-blank-opt-re "[[:blank:]\n]*")
(defvar larumbe/vhdl-blank-mand-re "[[:blank:]\n]+")
(defvar larumbe/vhdl-identifier-re "[a-zA-Z_][a-zA-Z0-9_-]*")
(defvar larumbe/vhdl-instance-re
  (concat "^\\s-*\\(?1:" larumbe/vhdl-identifier-re "\\)\\s-*:" larumbe/vhdl-blank-opt-re ; Instance TAG
          "\\(?2:\\(?3:component\\s-+\\|configuration\\s-+\\|\\(?4:entity\\s-+\\(?5:" larumbe/vhdl-identifier-re "\\)\.\\)\\)\\)?"
          "\\(?6:" larumbe/vhdl-identifier-re "\\)" larumbe/vhdl-blank-opt-re ; Module name
          "\\(--[^\n]*" larumbe/vhdl-blank-mand-re "\\)*\\(generic\\|port\\)\\s-+map\\>"))


(defun larumbe/find-vhdl-module-instance-fwd (&optional limit)
  "Searches forward for a VHDL module/instance regexp.

LIMIT argument is included to allow the function to be used to fontify VHDL buffers."
  (interactive)
  (let ((found nil)
        (pos))
    (save-excursion
      (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (forward-char))              ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-forward larumbe/vhdl-instance-re limit t))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p)
              (setq pos (match-beginning 6))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun larumbe/find-vhdl-module-instance-bwd (&optional limit)
  "Searches backwards for a VHDL module/instance regexp.

LIMIT argument is included to allow the function to be used to fontify VHDL buffers."
  (interactive)
  (let ((found nil)
        (pos))
    (save-excursion
      (when (called-interactively-p) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (backward-char))             ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-backward larumbe/vhdl-instance-re limit t))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p)
              (setq pos (match-beginning 6))
            (setq pos (point))))))
    (when found
      (goto-char pos))))



;;; Imenu
(defconst larumbe/vhdl-imenu-generic-expression
  `(
    ("Subprogram"
     "^\\s-*\\(\\(\\(impure\\|pure\\)\\s-+\\|\\)function\\|procedure\\)\\s-+\\(\"?\\(\\w\\|\\s_\\)+\"?\\)"
     4)
    ("Instances"
     larumbe/find-vhdl-module-instance-bwd
     6)
    ("Component"
     "^\\s-*\\(component\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)"
     2)
    ("Procedural"
     "^\\s-*\\(\\(\\w\\|\\s_\\)+\\)\\s-*:\\(\\s-\\|\n\\)*\\(procedural\\)"
     1)
    ("Process"
     "^\\s-*\\(\\(\\w\\|\\s_\\)+\\)\\s-*:\\(\\s-\\|\n\\)*\\(\\(postponed\\s-+\\|\\)process\\)"
     1)
    ("Block"
     "^\\s-*\\(\\(\\w\\|\\s_\\)+\\)\\s-*:\\(\\s-\\|\n\\)*\\(block\\)"
     1)
    ("Package"
     "^\\s-*\\(package\\( body\\|\\)\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)"
     3)
    ("Configuration"
     "^\\s-*\\(configuration\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\s-+of\\s-+\\(\\w\\|\\s_\\)+\\)"
     2)
    ("Architecture"
     "^\\s-*\\(architecture\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\s-+of\\s-+\\(\\w\\|\\s_\\)+\\)"
     2)
    ("Entity"
     ,larumbe/vhdl-entity-re
     2)
    ("Context"
     "^\\s-*\\(context\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)"
     2)
    )
  "Imenu generic expression for VHDL Mode.  See `imenu-generic-expression'.")


(defun larumbe/vhdl-index-menu-init ()
  "Initialize index menu."
  (set (make-local-variable 'imenu-case-fold-search) t)
  (set (make-local-variable 'imenu-generic-expression)
       larumbe/vhdl-imenu-generic-expression)
  (when (and vhdl-index-menu (fboundp 'imenu))
    (imenu-add-to-menubar "Index")))


;;; Jump to modules
;; INFO: By default `which-func' would get Info from Imenu.
;;  - This was far faster for which-func updating than using the custom `larumbe/find-vhdl-module-instance-bwd' function
;;  and performing analogous to modi's functions.

(defun larumbe/vhdl-jump-to-module-at-point ()
  "When in a module instance, jump to that module's definition.
Fetched from `modi/verilog-jump-to-module-at-point'"
  (interactive)
  (if (and (executable-find "global")
           (projectile-project-root))
      (let ((module (gethash (get-buffer-window) which-func-table))) ; INFO: modi/verilog analogous uses `which-func-current' but it didn't work well here...
        (if (save-excursion
              (larumbe/find-vhdl-module-instance-bwd))
            (ggtags-find-tag-dwim module))
        ;; Do `pop-tag-mark' if this command is called when the
        ;; point in *not* inside a verilog instance.
        (pop-tag-mark))
    (user-error "Executable `global' is required for this command to work")))


(defun larumbe/vhdl-find-parent-module ()
  "Find the places where the current VHDL module is instantiated in the project.
Fetched from `modi/verilog-find-parent-module'"
  (interactive)
  (let (module-name
        module-instance-pcre
        regexp)
    ;; Get entity name
    (save-excursion
      (re-search-backward larumbe/vhdl-entity-re))
    (setq module-name (match-string-no-properties 2))
    ;; Reformat regexp to PCRE:
    ;; INFO: Regexp fetched from `larumbe/vhdl-instance-re', replaced "\\s-" with "[ ]", and dismissing \n to allow for easy elisp to pcre conversion
    ;; Otherwise it was getting a real hell since `rxt-elisp-to-pcre' does not seem to support newlines conversion.
    (setq regexp (concat "^[ ]*\\([a-zA-Z_][a-zA-Z0-9_-]*\\)[ ]*:[ ]*"
                         "\\(\\(component[ ]+\\|configuration[ ]+\\|\\(entity[ ]+\\([a-zA-Z_][a-zA-Z0-9_-]*\\).\\)\\)\\)?"
                         "\\(" module-name "\\)[ ]*"))
    (setq module-instance-pcre (rxt-elisp-to-pcre regexp))
    (let* ((ag-arguments ag-arguments)) ;Save the global value of `ag-arguments'
      ;; Search only through vhdl type files.
      ;; See "ag --list-file-types".
      (add-to-list 'ag-arguments "--vhdl" :append)
      (ag-regexp module-instance-pcre (projectile-project-root)))))
