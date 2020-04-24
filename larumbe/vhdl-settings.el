;;;;;;;;;;;;;;;;
;; VHDL setup ;;
;;;;;;;;;;;;;;;;

;;; Basic settings
(use-package vhdl-mode
  :load-path "~/.elisp/larumbe/own-modes/override"
  :bind (:map vhdl-mode-map
              ("C-M-d"           . larumbe/find-vhdl-module-instance-fwd)
              ("C-M-u"           . larumbe/find-vhdl-module-instance-bwd)
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



;;; Custom functions
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
