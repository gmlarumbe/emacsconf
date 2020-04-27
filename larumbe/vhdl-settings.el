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
              ("C-c C-t"         . hydra-vhdl-template/body)
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
  ;; Indentation
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
  (vhdl-electric-mode -1)
  ;; Bind chords
  (bind-chord "\\\\" #'larumbe/vhdl-jump-to-module-at-point vhdl-mode-map)
  (when (executable-find "ag")
    (bind-chord "\|\|" #'larumbe/vhdl-find-parent-module vhdl-mode-map))
  )



;;; Hooks
(defun my-vhdl-hook ()
  (set 'ac-sources '(ac-source-gtags))
  ;; Flycheck
  (setq flycheck-ghdl-include-path (larumbe/vhdl-list-directories-of-open-buffers))
  (setq flycheck-ghdl-language-standard "08")
  (setq flycheck-ghdl-work-lib vhdl-default-library) ; "xil_defaultlib"
  (setq flycheck-ghdl-workdir (concat (projectile-project-root) "library/" vhdl-default-library)) ; Used @ axi_if_converter
  (setq flycheck-ghdl-ieee-library "synopsys")
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


;;; Flycheck
;; Fetched and adapted from Flycheck Verilator
;; INFO: Configured @ my-vhdl-hook previously on this file.
(flycheck-def-option-var flycheck-ghdl-include-path nil vhdl-ghdl
  "A list of include directories for GHDL

The value of this variable is a list of strings, where each
string is a directory to add to the include path of GHDL. "
  :type '(repeat (directory :tag "Include directory"))
  :safe #'flycheck-string-list-p
  :package-version '(flycheck . "32"))


;; Created to adapt GHDL to Xilinx libraries
(flycheck-def-option-var flycheck-ghdl-work-lib nil vhdl-ghdl
  "Work library name to be used for GHDL."
  :type '(choice (const :tag "Work library" nil)
                 (string :tag "Work library to be used (work, xil_defaultlib, etc...)"))
  :safe #'stringp
  :package-version '(flycheck . "32"))


;; Overrides the default @ flycheck.el
(flycheck-define-checker vhdl-ghdl
  "A VHDL syntax checker using GHDL.
See URL `https://github.com/ghdl/ghdl'."
  :command ("ghdl"
            "-s" ; only do the syntax checking
            (option "--std=" flycheck-ghdl-language-standard concat)
            (option "--workdir=" flycheck-ghdl-workdir concat)
            (option "--ieee=" flycheck-ghdl-ieee-library concat)
            (option "--work=" flycheck-ghdl-work-lib concat)
            (option-list "-P" flycheck-ghdl-include-path concat)
            source)
  :error-patterns
  ((error line-start (file-name) ":" line ":" column ": " (message) line-end))
  :modes vhdl-mode)


;;; Other custom functions
(defun larumbe/vhdl-list-directories-of-open-buffers ()
  "Base content fetched from: https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
Returns a list of directories from current VHDL opened files. Useful for `ghdl' linter flycheck include directories"
  (let (vhdl-opened-dirs)
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "vhdl-mode")
          (add-to-list 'vhdl-opened-dirs default-directory))))
    (eval 'vhdl-opened-dirs)))



(defun larumbe/vhdl-insert-instance-from-file (file)
  "Insert instance at point from file.
Copied and adapted from `larumbe/verilog-insert-instance-from-file'"
  (interactive "FSelect entity from file:")
  (let* ((entity-name (with-temp-buffer
                        (insert-file-contents file)
                        (if (re-search-forward larumbe/vhdl-entity-re nil t)
                            (progn
                              (save-match-data
                                (vhdl-port-copy))
                              (match-string-no-properties 2))
                          (error "No VHDL entity found in that file!"))))
         (instance-name (read-string "Instance-name: " (concat "I_" (upcase entity-name)))))
    (vhdl-port-paste-instance instance-name)))


(defun larumbe/vhdl-insert-testbench-from-file (file)
  "Create testbench from entity of selected file in current buffer directory."
  (interactive "FSelect entity from file:")
  (let* ((entity-name (with-temp-buffer
                        (insert-file-contents file)
                        (if (re-search-forward larumbe/vhdl-entity-re nil t)
                            (progn
                              (save-match-data
                                (vhdl-port-copy))
                              (match-string-no-properties 2))
                          (error "No VHDL entity found in that file!")))))
    (if (buffer-file-name)
        (vhdl-port-paste-testbench)
      (error "Not visiting a file. TB is created in current file directory!!"))))




;;;; Hydra
(defhydra hydra-vhdl-template (:color blue
                                      :hint nil)
  "
RTL                   TESTBENCH             COMMON            PACKAGES
^^
_ps_: process seq       _@_:  clocked wait      _for_: for          _pb_: package body
_pc_: process comb      _pr_: procedure         _fn_: function      _pd_: package declaration
_en_: entity            _rp_: report            _sg_: signal        _pkg_: library package
_ac_: architecture      _as_: assert            _va_: variable
_gn_: generate          _fl_: file              _ct_: constant
_cp_: component         _TS_: TestBench         _ge_: generic
_at_: attribute         ^^                      _ty_: type
_IS_: Instance          ^^                      _al_: alias
^^                      ^^                      _if_: if-then
^^                      ^^                      _cc_: case
^^                      ^^                      _wh_: while
^^                      ^^                      _hd_: header
"
  ;;;;;;;;;
  ;; RTL ;;
  ;;;;;;;;;
  ("ps"  (vhdl-template-process-seq))
  ("pc"  (vhdl-template-process-comb))
  ("en"  (vhdl-template-entity))
  ("ac"  (vhdl-template-architecture))
  ("gn"  (vhdl-template-generate))
  ("cp"  (vhdl-template-component))
  ("at"  (vhdl-template-attribute))
  ("IS"  (call-interactively 'larumbe/vhdl-insert-instance-from-file))

  ;;;;;;;;;;;;;;;
  ;; TestBench ;;
  ;;;;;;;;;;;;;;;
  ("@"  (vhdl-template-clocked-wait))
  ("pr" (vhdl-template-procedure))
  ("rp" (vhdl-template-report))
  ("as" (vhdl-template-assert))
  ("fl" (vhdl-template-file))
  ("TS"  (call-interactively 'larumbe/vhdl-insert-testbench-from-file))

  ;;;;;;;;;;;;
  ;; Common ;;
  ;;;;;;;;;;;;
  ("for" (vhdl-template-for))
  ("fn"  (vhdl-template-function))
  ("sg"  (vhdl-template-signal))
  ("va"  (vhdl-template-variable))
  ("ct"  (vhdl-template-constant))
  ("ge"  (vhdl-template-generic))
  ("ty"  (vhdl-template-type))
  ("al"  (vhdl-template-alias))
  ("if"  (vhdl-template-if-then))
  ("cc"  (vhdl-template-case))
  ("wh"  (vhdl-template-while-loop))
  ("hd"  (vhdl-template-header))

  ("pb"  (vhdl-template-package-body))
  ("pd"  (vhdl-template-package-decl))
  ("pkg" (call-interactively 'vhdl-template-insert-package))

  ;;;;;;;;;;;;
  ;; Others ;;
  ;;;;;;;;;;;;
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))
