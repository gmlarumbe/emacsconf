;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Verilog/SystemVerilog setup ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Basic settings
(use-package verilog-mode
  :load-path "~/.elisp/larumbe/own-modes/override"
  :mode (("\\.[st]*v[hp]*\\'" . verilog-mode) ;.v, .sv, .svh, .tv, .vp
         ("\\.psl\\'"         . verilog-mode)
         ("\\.vams\\'"        . verilog-mode)
         ("\\.vinc\\'"        . verilog-mode)
         ("\\.vsrc\\'"        . verilog-mode)) ; Custom, for Gigatron vsrc files
  :bind (:map verilog-mode-map
              ("M-i"     . larumbe/verilog-imenu)
              ("M-f"     . verilog-forward-word)
              ("M-b"     . verilog-backward-word)
              ("TAB"     . larumbe/electric-verilog-tab)
              ([delete]  . delete-forward-char)
              ("C-M-n"   . modi/verilog-jump-to-header-dwim-fwd)
              ("C-M-p"   . modi/verilog-jump-to-header-dwim)
              ("C-M-u"   . larumbe/find-verilog-module-instance-bwd)
              ("C-M-d"   . larumbe/find-verilog-module-instance-fwd)
              ("C-M-h"   . xah-select-current-block)
              ("C-%"     . hide/show-comments-toggle)
              ("C-c C-t" . hydra-verilog-template/body)
              ("C-c l"   . larumbe/verilog-insert-instance-from-file)
              ("C-c i"   . larumbe/verilog-indent-current-module)
              ("C-c a"   . larumbe/verilog-align-ports-current-module)
              ("C-c C-l" . larumbe/verilog-align-parameters-current-module)
              ("C-c b"   . larumbe/verilog-beautify-current-module)
              ("C-c c"   . larumbe/verilog-toggle-connect-port)
              ("C-c C-c" . larumbe/verilog-connect-ports-recursively)
              ("C-c C-p" . larumbe/verilog-preprocess)
              ("<f8>"    . larumbe/verilog-vhier-current-file)
              )
  :demand ; INFO: Avoid deferring to properly load modi settings
  :init   ; INFO: Requires to be set before loading package in order to variables like faces to take effect
  (setq larumbe/verilog-indent-level 4)

  (setq verilog-indent-level             larumbe/verilog-indent-level)
  (setq verilog-indent-level-module      larumbe/verilog-indent-level)
  (setq verilog-indent-level-declaration larumbe/verilog-indent-level)
  (setq verilog-indent-level-behavioral  larumbe/verilog-indent-level)
  (setq verilog-case-indent              larumbe/verilog-indent-level)
  (setq verilog-indent-level-directive   larumbe/verilog-indent-level)
  (setq verilog-cexp-indent              larumbe/verilog-indent-level)

  (setq verilog-auto-delete-trailing-whitespace t) ; ‘delete-trailing-whitespace’ in ‘verilog-auto’.
  (setq verilog-highlight-grouping-keywords     t) ; begin/end
  (setq verilog-auto-indent-on-newline          t) ; Self-explaining
  (setq verilog-tab-always-indent               t) ; Indent even though we are not at the beginning of line
  (setq verilog-indent-begin-after-if           t)
  (setq verilog-auto-endcomments                t)
  (setq verilog-date-scientific-format          t)
  (setq verilog-case-fold                       nil) ; Regexps should NOT ignore case

  (setq verilog-indent-lists      t)   ; If set to nil, indentation will not properly detect we are inside a parenthesized expression (instance or ports/parameters)
  (setq verilog-auto-lineup       nil) ; other options are 'declarations or 'all
  (setq verilog-auto-newline      nil)
  (setq verilog-align-ifelse      nil)
  (setq verilog-tab-to-comment    nil)
  (setq verilog-highlight-modules nil) ; Experimental for highlight-buffer. TODO: Test how this works (plus `verilog-highlight-includes')

  (setq verilog-minimum-comment-distance 10)


  :config
  ;; Many thanks to Kaushal Modi (https://scripter.co/)
  (load "~/.elisp/larumbe/verilog-modi-setup.el")

  ;; Bind chords
  (bind-chord "\\\\" #'modi/verilog-jump-to-module-at-point verilog-mode-map) ;"\\"
  (when (executable-find "ag")
    (bind-chord "\|\|" #'modi/verilog-find-parent-module verilog-mode-map))

  (modi/verilog-do-not-read-includes-defines-mode -1) ;; INFO: Larumbe: For Verilog AUTO. Set to 1 by modi to: "Stop cluttering my buffer list by not opening all the `included files."

  ;; Own advice to avoid indentation of outshine (overrides modi setup of `modi/outshine-allow-space-before-heading')
  (advice-add 'verilog-indent-line-relative :before-until #'larumbe/verilog-avoid-indenting-outshine-comments)
  ;; Modi multi-line defines (and allegedly outshine) indentation advice: DANGER: Still issues with following lines after multiline defines!
  (advice-add 'verilog-indent-line-relative :before-until #'modi/verilog-selective-indent) ;; Advise the indentation behavior of `indent-region' done using `C-M-\'
  (advice-add 'verilog-indent-line :before-until #'modi/verilog-selective-indent)          ;; Advise the indentation done by hitting `TAB' (modi multi-line defines)
  )


;;; Common settings and hooks
(defvar larumbe/verilog-open-dirs nil
  "List with directories of current opened `verilog-mode' buffers.
Used for verilog AUTO libraries, flycheck and Verilo-Perl hierarchy.")


(defun my-verilog-hook ()
  (set 'ac-sources '(ac-source-verilog ac-source-gtags)) ; Auto-complete verilog-sources
  (setq larumbe/verilog-open-dirs (larumbe/verilog-list-directories-of-open-buffers))
  (setq verilog-library-directories larumbe/verilog-open-dirs) ; Verilog *AUTO* folders (could use `verilog-library-files' for files)
  (setq flycheck-verilator-include-path larumbe/verilog-open-dirs)
  (modify-syntax-entry ?` ".") ; Avoid including preprocessor tags while isearching. Requires `larumbe/electric-verilog-tab' to get back standard table to avoid indentation issues with compiler directives.
  (key-chord-mode 1)
  (larumbe/verilog-find-semicolon-in-instance-comments)
  )

;; Verilog Hooks
(add-hook 'verilog-mode-hook 'my-verilog-hook)
(add-hook 'verilog-mode-hook #'modi/verilog-mode-customization) ; Modi: block comments to names


;;; Lint, Compilation and Simulation Tools
;; INFO: Discarding the following `verilog-set-compile-command' variables:
;; - `verilog-linter:' replaced by FlyCheck with opened buffers as additional arguments, plus custom project parsing functions
;; - `verilog-simulator': replaced by XSim and ncsim sim project funcions
;; - `verilog-compiler': replaced by Vivado elaboration/synthesis project functions
;; - `verilog-preprocessor': `larumbe/verilog-preprocess' wrapper of verilog-mode internal function' does the trick
;; - `verilog-coverage' still not implemented as there are not many free alternatives...


;;;; Preprocessor
(defun larumbe/verilog-preprocess ()
  "Wrapper for `verilog-preprocess' that allows to choose between `verilator' and Verilog-Perl `vppreproc'.
Seems that all the libraries/incdirs are computed internally at verilog-mode"
  (interactive)
  (pcase (completing-read "Select tool: " '("verilator" "vppreproc"))
    ("verilator" (setq verilog-preprocessor "verilator -E __FLAGS__ __FILE__"))
    ("vppreproc" (setq verilog-preprocessor "vppreproc __FLAGS__ __FILE__")))
  (verilog-preprocess))


;;;; Iverilog/verilator Makefile development
(defun larumbe/verilog-makefile-create ()
  "Creates Iverilog/verilator Yasnippet based Makefile only if in a projectile project
and the Makefile does not already exist."
  (interactive)
  (let (file)
    (if (projectile-project-p)
        (if (file-exists-p (setq file (concat (projectile-project-root) "Makefile")))
            (error "File %s already exists!" file)
          (progn
            (find-file file)
            (larumbe/hydra-yasnippet "verilog")))
      (error "Not in a projectile project!"))))


(defun larumbe/verilog-makefile-compile-project ()
  "Prompts to available previous Makefile targets and compiles then with various verilog regexps."
  (interactive)
  (let ((makefile (concat (projectile-project-root) "Makefile"))
        target
        cmd)
    (unless (file-exists-p makefile)
      (error "%s does not exist!" makefile))
    (with-temp-buffer
      (insert-file-contents makefile)
      (makefile-pickup-targets)
      (setq target (completing-read "Target: " makefile-target-table)))
    ;; INFO: Tried with `projectile-compile-project' but without sucess.
    ;; Plus, it was necessary to change `compilation-read-command' which is unsafe.
    (setq cmd (concat "make " target))
    (cd (projectile-project-root))
    (compile cmd)
    (larumbe/custom-error-regexp-set-emacs
     (append iverilog-error-regexp-emacs-alist-alist
             verilator-error-regexp-emacs-alist-alist
             vivado-error-regexp-emacs-alist-alist))
    (show-custom-compilation-buffers)))


;;; Own Verilog templates
;; Should be deprecated by Hydra+YASnippet
;; Customized functions extracted from verilog-mode.el at .elisp/ dir
;;;; Common
(defvar verilog-reset-custom "Rst_n")
(defun larumbe/verilog-prompt-reset-custom ()
  "Prompt for the name of a state machine reset."
  (setq verilog-reset-custom (read-string "Active Low Reset Name: " "Rst_n")))

(defun larumbe/verilog-prompt-clock-custom ()
  "Prompt for the name of a clock."
  (setq verilog-clock-custom (read-string "Posedge clock name: " "Clk")))


;;;; Begin/end block
;; Replace old begin-end from verilog-mode skeleton
(defun larumbe/verilog-begin-custom ()
  "Insert begin end block.  Uses the minibuffer to prompt for name.
Written as verilog-mode original defun had issues with indentation."
  (interactive)
  (electric-verilog-tab)                ; Initial indent (we wont know where we are...)
  (insert "begin")
  (progn (electric-verilog-terminate-line) nil)
  (save-excursion
    (progn (electric-verilog-terminate-line) nil)
    (insert "end")
    (electric-verilog-tab)
    )
  (electric-verilog-tab)
  )


;;;; Comments
;; Had some issues trying to implement it with skeletons. Finally decided on interactive defun
(defun larumbe/verilog-add-block-comment ()
  "Custom function. Creates a Verilog comment block. Useful to separate sections within code.
Char code 47 corresponds to '/' character in Verilog"
  (interactive)
  (setq verilog-block-comment-custom (read-string "Name: "))
  (setq verilog-block-comment-width (string-width verilog-block-comment-custom))
  ;; Top line
  (electric-verilog-tab)              ; Start indentation for comment block
  (insert (concat (insert-char 47 (+ verilog-block-comment-width 6) nil)))
  (electric-verilog-terminate-line)
  ;; Comment line
  (insert (concat
           (insert-char 47 2 nil)
           (insert " ")
           (insert verilog-block-comment-custom)
           (insert " ")
           (insert-char 47 2 nil)
           ))
  (electric-verilog-terminate-line)
  ;; Bottom line
  (insert (concat (insert-char 47 (+ verilog-block-comment-width 6) nil)))
  (electric-verilog-terminate-line)
  )


;;;; State Machines
;; Variables used to add parameters on-the-fly
(defvar larumbe/verilog-fsm-parameter-position nil)

;; 1 parameter keyword per parameter declaration
(defun larumbe/verilog-state-machine-add-case (param-read)
  "Fills cases within the Next state and output logic and declares them as parameters at the beginning of the FSM "
  (save-excursion
    (goto-char larumbe/verilog-fsm-parameter-position)
    (electric-verilog-terminate-line)
    (insert (concat "parameter " param-read " = " (read-string "Param value: ") ";"))
    (setq larumbe/verilog-fsm-parameter-position (point))))


;; Adds a state machine with two always blocks.
(defun larumbe/verilog-state-machine-async-custom-simple ()
  "Insert a state machine custom definition     .
Two always blocks, one for next state and output logic and one for the state registers"
  (interactive)
  (let (param-read)
    (setq verilog-custom-state (read-string "Name of state variable: " "state"))
    (electric-verilog-tab)              ; Start indentation for comment block
    (insert (concat "// State registers for " verilog-custom-state))                                                                    (progn (electric-verilog-terminate-line) nil)
    (insert (concat "reg [" (read-string "msb: " "31") ":" (read-string "lsb: " "0") "] " verilog-custom-state ", next_" verilog-custom-state ";"))
    (setq larumbe/verilog-fsm-parameter-position (point))                                                                                       (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " verilog-custom-state))                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " (larumbe/verilog-prompt-clock-custom) " or negedge " (larumbe/verilog-prompt-reset-custom) ") begin"))   (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ")"))                                                                               (progn (electric-verilog-terminate-line) nil)
    (insert (concat verilog-custom-state " <= IDLE;"))                                                                                  (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else"))                                                                                                            (progn (electric-verilog-terminate-line) nil)
    (insert (concat  verilog-custom-state " <= next_" verilog-custom-state ";"))                                                        (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; Next state and output logic
    (insert (concat "// Output and next State Logic for " verilog-custom-state))                                                        (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always @ (posedge " verilog-clock-custom  " or negedge " verilog-reset-custom  ") begin"))                   (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ") begin"))                                                                         (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= IDLE;"))                                                                          (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output resets..."))                                                                                             (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else begin"))                                                                                                      (progn (electric-verilog-terminate-line) nil)
    (insert (concat "case (" verilog-custom-state ") "))
    ;; Case reading
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (larumbe/verilog-state-machine-add-case  param-read)                                                                                   (progn (electric-verilog-terminate-line) nil)
      (insert (concat param-read ": begin"))                                                                                            (progn (electric-verilog-terminate-line) nil)
      (insert (concat "// Output statements... "))                                                                                      (progn (electric-verilog-terminate-line) nil)
      (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                     (progn (electric-verilog-terminate-line) nil)
      (insert (concat "end"))                                                                                                           (progn (electric-verilog-terminate-line) nil)
      )
    (insert (concat "endcase"))                                                                                                         (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                             (progn (electric-verilog-terminate-line) nil)
    )
  )


;; Only 1 parameter keyword for all parameter declarations (improves readability)
(defun larumbe/verilog-state-machine-add-case-fold (param-read pfx idx )
  "Fills cases within the Next state and output logic and declares them as parameters at the beginning of the FSM.
Parameter keyword is used only once, improving readability."
  (save-excursion
    (goto-char larumbe/verilog-fsm-parameter-position)
    (delete-char -1)
    (insert ",")
    (electric-verilog-terminate-line)
    (insert (concat param-read " = " (read-string "Param value: " (concat pfx (number-to-string idx) ";"))))
    (setq larumbe/verilog-fsm-parameter-position (point))))





;; Returns "4'h." or "1'b." depending on msb and lsb.
(defun larumbe/verilog-state-machine-get-prefix (msb-str lsb-str)
  "Very neat function that gets the prefix depending on the FSM state width.
For the time being, since not very complex FSMs are being immplemented,
just binary and hexadecimal prefix are returned"
  (let (width msb lsb)
    (setq msb (string-to-number msb-str))
    (setq lsb (string-to-number lsb-str))
    (setq width (-  msb  lsb))
    (if (/= (% (1+ width) 4) 0)
        (message "1'b")
      (message "4'h"))))


;; Adds a state machine with two always blocks.
;; Improves previous function with automatic reset state insertion and automatic parameter width insertion
(defun larumbe/verilog-state-machine-sync-custom ()
  "Insert a state machine custom definition     .
Two always blocks, one for next state and output logic and one for the state registers"
  (interactive)
  (let (param-read rst-state-name msb lsb pfx (idx 0))
    (setq verilog-custom-state (read-string "Name of state variable: " "state"))
    (electric-verilog-tab)              ; Start indentation for comment block
    (insert (concat "// State registers for " verilog-custom-state))                                                                                                       (progn (electric-verilog-terminate-line) nil)
    (insert (concat "logic [" (setq msb (read-string "msb: " "3")) ":" (setq lsb (read-string "lsb: " "0")) "] " verilog-custom-state ", next_" verilog-custom-state ";")) (progn (electric-verilog-terminate-line) nil)
    (setq pfx (larumbe/verilog-state-machine-get-prefix msb  lsb))
    (insert (concat "localparam " (setq rst-state-name (read-string "Reset State Name: " "IDLE"))  " = " (read-string "Reset Value: " (concat pfx "0;"))))
    (setq larumbe/verilog-fsm-parameter-position (point))                                                                                                                          (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; State registers
    (insert (concat "// State FF for " verilog-custom-state))                                                                                                              (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always_ff @ (posedge " (larumbe/verilog-prompt-clock-custom) ") begin"))                                                                                      (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ")"))                                                                                                                     (progn (electric-verilog-terminate-line) nil)
    (insert (concat verilog-custom-state " <= " rst-state-name ";"))                                                                                                       (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else"))                                                                                                                                               (progn (electric-verilog-terminate-line) nil)
    (insert (concat  verilog-custom-state " <= next_" verilog-custom-state ";"))                                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (electric-verilog-terminate-line)
    ;; Next state and output logic
    (insert (concat "// Output and next State Logic for " verilog-custom-state))                                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "always_ff @ (posedge " verilog-clock-custom  ") begin"))                                                                                              (progn (electric-verilog-terminate-line) nil)
    (insert (concat "if (!" verilog-reset-custom ") begin"))                                                                                                               (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= "rst-state-name ";"))                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output resets..."))                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "else begin"))                                                                                                                                         (progn (electric-verilog-terminate-line) nil)
    (insert (concat "case (" verilog-custom-state ") "))                                                                                                                   (progn (electric-verilog-terminate-line) nil)
    ;; Reset State text insertion
    (insert (concat rst-state-name ": begin"))                                                                                                                             (progn (electric-verilog-terminate-line) nil)
    (insert (concat "// Output statements... "))                                                                                                                           (progn (electric-verilog-terminate-line) nil)
    (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                                                          (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    ;; Case reading
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (setq idx (1+ idx))
      (larumbe/verilog-state-machine-add-case-fold param-read pfx idx)                                                                                                             (progn (electric-verilog-terminate-line) nil)
      (insert (concat param-read ": begin"))                                                                                                                               (progn (electric-verilog-terminate-line) nil)
      (insert (concat "// Output statements... "))                                                                                                                         (progn (electric-verilog-terminate-line) nil)
      (insert (concat "next_" verilog-custom-state " <= <state>;"))                                                                                                        (progn (electric-verilog-terminate-line) nil)
      (insert (concat "end"))                                                                                                                                              (progn (electric-verilog-terminate-line) nil)
      )
    (insert (concat "endcase"))                                                                                                                                            (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    (insert (concat "end"))                                                                                                                                                (progn (electric-verilog-terminate-line) nil)
    )
  )

;;;; Headers
(defun larumbe/verilog-header ()
  "Insert a standard Verilog file header.
See also `verilog-sk-header' for an alternative format."
  (interactive)
  (let ((start (point)))
    (insert "\
//-----------------------------------------------------------------------------
// Title         : <title>
// Project       : <project>
//-----------------------------------------------------------------------------
// File          : <filename>
// Author        : <author>
// Created       : <credate>
// Last modified : <moddate>
//-----------------------------------------------------------------------------
// Description :
// <description>
//-----------------------------------------------------------------------------
// Copyright (c) <author>
//
//------------------------------------------------------------------------------
// Modification history :
// <modhist>
//-----------------------------------------------------------------------------

")
    (goto-char start)
    (search-forward "<filename>")
    (replace-match (buffer-name) t t)
    (search-forward "<author>") (replace-match "" t t)
    (insert (user-full-name))
    (search-forward "<credate>") (replace-match "" t t)
    (verilog-insert-date)
    (search-forward "<moddate>") (replace-match "" t t)
    (verilog-insert-date)
    (search-forward "<author>") (replace-match "" t t)
    (insert (user-full-name))
    (insert "  <gonzalomlarumbe@gmail.com> ")
    (search-forward "<modhist>") (replace-match "" t t)
    (verilog-insert-date)
    (insert " : created")
    (goto-char start)
    (let (string)
      (setq string (read-string "title: "))
      (search-forward "<title>")
      (replace-match string t t)
      (setq string (read-string "project: " verilog-project))
      (setq verilog-project string)
      (search-forward "<project>")
      (replace-match string t t)
      (replace-match string t t)
      (search-forward "<description>")
      (replace-match "" t t))))



(defun larumbe/verilog-header-hp ()
  "Insert an HP Verilog file header.
See also `verilog-header' for an alternative format."
  (interactive)
  (save-excursion
    (let ((start (point-min)))
      (goto-char start)
      (insert "\
/********1*********2*********3*********4*********5*********6*********7*********8
 *
 * FILE      : <filename>
 * HIERARCHY :
 * FUNCTION  : <function>
 * AUTHOR    : <author>
 *
 *_______________________________________________________________________________
 *
 * REVISION HISTORY
 *
 * Name         Date          Comments
 * ------------------------------------------------------------------------------
 * <user>    <credate>     Created
 * ------------------------------------------------------------------------------
 *_______________________________________________________________________________
 *
 * FUNCTIONAL DESCRIPTION
 * <description>
 *_______________________________________________________________________________
 *
 * (c) Copyright Hewlett-Packard Company, year
 * All rights reserved. Copying or other reproduction of this
 * program except for archival purposes is prohibited without
 * written consent of Hewlett-Packard Company.
 * HEWLETT-PACKARD COMPANY
 * INKJET COMERCIAL DIVISION
 *
 *********1*********2*********3*********4*********5*********6*********7*********/

")
      (goto-char start)
      (search-forward "<filename>")
      (replace-match (buffer-name) t t)
      (search-forward "<author>") (replace-match "" t t)
      (insert (user-full-name))
      (insert "  <gonzalo.martinez.larumbe@hp.com>")
      (search-forward "<user>")
      (replace-match (user-login-name) t t)
      (search-forward "<credate>") (replace-match "" t t)
      (verilog-insert-date)
      (if (called-interactively-p 'any)
          (progn
            (let (string)
              (goto-char start)
              (setq string (read-string "Function: "))
              (search-forward "<function>")
              (replace-match string t t)
              (setq string (read-string "Description: "))
              (search-forward "<description>")
              (replace-match string t t)))
        (progn
          (goto-char start)
          (search-forward "<function>")
          (replace-match "" t t)
          (search-forward "<description>")
          (replace-match "" t t))))))

;;;; Instances
(setq larumbe/verilog-auto-template-header "// Beginning of Larumbe's Verilog AUTO_TEMPLATE")
(setq larumbe/verilog-auto-template-footer "// End of Larumbe's Verilog AUTO_TEMPLATE")

(defmacro larumbe/verilog-auto-template (template)
  (concat "\n" larumbe/verilog-auto-template-header " " template " " larumbe/verilog-auto-template-footer "\n"))


(setq larumbe/verilog-auto-template-connected-ports
      (larumbe/verilog-auto-template "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (\\1),
 ); */"
))

(setq larumbe/verilog-auto-template-disconnected-ports
      (larumbe/verilog-auto-template "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (),
 ); */"
))

(setq larumbe/verilog-auto-template-connected-ports-subscripts
      (larumbe/verilog-auto-template "
/* <module> AUTO_TEMPLATE (
 .\\(.*\\) (\\1[]),
 ); */"
))


(setq larumbe/verilog-autoinst-template-simple "\
<module> <instance_name> (/*AUTOINST*/);
")

(setq larumbe/verilog-autoinst-autoparam-template "\
<module> # (/*AUTOINSTPARAM*/) <instance_name> (/*AUTOINST*/);
")



(defun larumbe/verilog-choose-template ()
  "Choose current // AUTO_TEMPLATE for instantiation"
  (let (templates-list)
    (setq templates-list (completing-read "AUTO_TEMPLATE: " '("Connected Ports" "Disconnected Ports" "Connected Ports with subscripts")))
    (pcase templates-list
      ("Connected Ports"                 (eval larumbe/verilog-auto-template-connected-ports))
      ("Disconnected Ports"              (eval larumbe/verilog-auto-template-disconnected-ports))
      ("Connected Ports with subscripts" (eval larumbe/verilog-auto-template-connected-ports-subscripts))
      (_                                 (error "Error @ larumbe/verilog-choose-template: Unexpected string")))))

(defun larumbe/verilog-choose-autoinst ()
  "Choose current /*AUTOINST*/ (and /*AUTOPARAMINST*/) for instantiation"
  (let (autoinst-list)
    (setq autoinst-list (completing-read "AUTOINST:" '("Simple" "With Parameters")))
    (pcase autoinst-list
      ("Simple"          (eval larumbe/verilog-autoinst-template-simple))
      ("With Parameters" (eval larumbe/verilog-autoinst-autoparam-template))
      (_                 (error "Error @ larumbe/verilog-choose-autoinst: Unexpected string")))))


(defun larumbe/verilog-autoinst-processing ()
  "Called from `larumbe/verilog-insert-instance-from-file' (refactoring purposes)"
  (let (beg end)
    (save-excursion ;; Remove comments
      (setq beg (point))
      (setq end (re-search-forward ")[[:blank:]]*;[[:blank:]]*// Templated"))
      (replace-regexp "[[:blank:]]*// Templated" "" nil beg end))
    (save-excursion ;; Open final parenthesis
      (re-search-forward "));")
      (backward-char 2)
      (electric-verilog-terminate-line))
    (save-excursion ;; Remove /*AUTOINST*/
      (setq beg (point))
      (setq end (re-search-forward ");")) ; Last /*AUTOINST*/ comment by AUTO_TEMPLATE
      (replace-string "/*AUTOINST*/" "" nil beg end))))


(defun larumbe/verilog-autoparam-processing ()
  "Called from `larumbe/verilog-insert-instance-from-file' (refactoring purposes)"
  (let (beg end)
    (save-excursion
      (setq beg (point))
      (setq end (re-search-forward "))"))
      (backward-char 1)
      (electric-verilog-terminate-line))
    (save-excursion ; Remove /*AUTOINSTPARAM*/
      (setq beg (point))
      (setq end (re-search-forward ");"))
      (replace-string "/*AUTOINSTPARAM*/" "" nil beg end))
    (save-excursion ; Remove ' // Parameters ' string
      (next-line 1)
      (beginning-of-line)
      (kill-line 1))))


(defun larumbe/verilog-insert-instance-from-file (file)
  "DANGER: Assumes filename and module name are the same.
INFO: In the future, a list that returns modules in a file could be retrieved and used as an input"
  (interactive "FSelect module from file:")
  (let* ((module-name (file-name-sans-extension (file-name-nondirectory file)))
         (instance-name (read-string "Instance-name: " (concat "I_" (upcase module-name))))
         (start-template (point))
         start-instance template inst-template autoparam)
    ;; Prepare instantiation template
    (add-to-list 'verilog-library-files file)
    (if current-prefix-arg
        (setq template (larumbe/verilog-choose-template)) ; If universal-arg given ask for AUTO_TEMPLATE and parameterized module to choose
      (setq template larumbe/verilog-auto-template-connected-ports)) ; Default template
    (insert template)
    (save-excursion
      (goto-char start-template)
      (replace-string "<module>" module-name))
    (if current-prefix-arg
        (when (equal larumbe/verilog-autoinst-autoparam-template (setq inst-template (larumbe/verilog-choose-autoinst))) ; If Universal Argument given, then ask for AUTOINST template
          (setq autoparam t))
      (setq inst-template larumbe/verilog-autoinst-template-simple)) ; Default AUTOINST with no parameters
    (setq start-instance (point))
    ;; Instantiate module/instance
    (save-excursion
      (insert inst-template)
      (goto-char start-instance)
      (replace-string "<module>" module-name)
      (goto-char start-instance)
      (replace-string "<instance_name>" instance-name)
      (verilog-auto))
    ;; PostProcess instantiation
    (larumbe/verilog-autoinst-processing)
    (when autoparam
      (larumbe/verilog-autoparam-processing))
    ;; Remove AUTO_TEMPLATE comment code
    (setq start-template (search-backward larumbe/verilog-auto-template-header))
    (setq start-instance (search-forward larumbe/verilog-auto-template-footer))
    (delete-region start-template (1+ start-instance))
    ;; Beautify instantiation
    (save-excursion
      (search-forward instance-name)
      (larumbe/verilog-indent-current-module module-name))
    (save-excursion
      (search-forward instance-name)
      (next-line 1)
      (larumbe/verilog-align-ports-current-module))
    (when autoparam
      (save-excursion
        (search-forward instance-name)
        (next-line 1)
        (larumbe/verilog-align-parameters-current-module module-name)))))


(defun larumbe/verilog-insert-instance-from-file-with-params (file)
  "Necessary to be passed as a parameter for Hydra templates"
  (interactive "FSelect module from file:")
  (setq current-prefix-arg 4)
  (larumbe/verilog-insert-instance-from-file file))


;;;; Testbenches
(defun larumbe/verilog-testbench-insert-template-simple (file)
  "WIP: Just a first sketch to check which AUTOS are needed"
  (interactive "FSelect DUT from file:")
  (let ((start (point))
        (module-name (file-name-sans-extension (file-name-nondirectory file)))
        (current-prefix-arg)
        beg end)
    (insert "\
// TODO: unit space imported packages
// import AxiLiteBfm_pkg::*;

module tb_<module_name> () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;
    localparam CLKT = 10ns;  // 100 MHz

    // TODO: Don't forget to INIT after (verilog-auto)!!
    // DUT instance parameters
    /*AUTOINOUTPARAM(\"<module_name>\")*/
    // End of /*AUTOINOUTPARAM*/

    // Non-auto signals
    logic Clk   = 1'b0;
    logic Rst_n = 1'b1;

    // TODO: Init during declaration (before simulation time 0) to avoid unexpected triggering events
    /* DUT Inputs */
    /*AUTOREGINPUT*/

    /* DUT Outputs */
    /*AUTOLOGIC*/


    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // TODO: Declare/Connect interfaces
    // axi4_lite_if axil_if_<module_name> (.AClk(Clk), .AReset_n(Rst_n));
    // ...

    // TODO: Ensure SV interfaces connections
    // DUT Instantiation

    // TODO: Tasks
    // ...

    // TODO: TB Object declarations
    // AxiLiteBfm axil;

    // TODO: Stimuli
    initial begin
        // axil = new(axil_if_<module_name>);
        // axil.wait_out_of_reset();
        // ...
        // #10 Rst_n = 0;
        // ...
        // $display(\"@%0d: TEST PASSED\", $time);
        // $finish;
        // ...
    end


endmodule // tb_<module_name>
")
    (goto-char start)
    (replace-string "<module_name>" module-name)
    (goto-char start)
    (search-forward "// DUT Instantiation")
    (setq current-prefix-arg 4) ; Add DUT instance with parameters and choosing template
    (larumbe/verilog-insert-instance-from-file file) ; Includes `verilog-auto' expansion
    (goto-char start)
    (search-forward "/*AUTOINOUTPARAM") ;; Postprocess /*AUTOINOUTPARAM*/
    (save-excursion
      (replace-regexp "logic[[:blank:]]+" "localparam " nil (point) (search-forward "// End of /*AUTOINOUTPARAM*/")))
    (save-excursion
      (replace-regexp "\\(localparam [a-zA-Z0-9_-]+\\);" "\\1 = 0;" nil (point) (search-forward "// End of /*AUTOINOUTPARAM*/")))
    (call-interactively 'larumbe/verilog-header-hp)
    (goto-char start)
    ;; Beautify declarations and initialize values
    (save-excursion
      (search-forward "/*AUTOREGINPUT*/")
      (beginning-of-line)
      (verilog-pretty-declarations)
      (save-excursion ; Init to '0 every input signal
        (setq beg (point))
        (forward-paragraph 1)
        (setq end (point))
        (replace-regexp "\\(logic [a-zA-Z0-9_-]+\\);" "\\1 = '0;" nil beg end))
      (save-excursion ; Align // To or // From auto comments
        (setq beg (point))
        (forward-paragraph 2)
        (setq end (point))
        (align-regexp beg end "\\(\\s-*\\)//" 1 1 nil)))
    ;; Delete /*AUTO[.*]*/ and generated code
    (save-excursion
      (while (re-search-forward "/\\*AUTO.*\*\/" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (save-excursion
      (while (search-forward "// Beginning of automatic" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (save-excursion
      (while (search-forward "// End of automatics" nil t)
        (beginning-of-line)
        (kill-line 1)))
    (search-forward "// TODO")))



(defun larumbe/verilog-testbench-environment-clocks (file)
  "Create `tb_clocks' file and module from template"
  (with-temp-file file
    (insert "\
import tb_defs_pkg::CLKT;
// import other clock periods

module tb_clocks (
    output logic Clk
    // Other clocks
    );

    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // Other clocks
    // ...

    // Initial clock values
    initial begin
        Clk = 1;
    end


endmodule: tb_clocks
"))
  (find-file file)
  (larumbe/verilog-header-hp)
  (save-buffer))


(defun larumbe/verilog-testbench-environment-program (file)
  "Create `tb_program' module from template"
  (with-temp-file file
    (insert "\
import tb_defs_pkg::*;
import tb_classes::*;
// import Bfms

program automatic tb_program (
    // Interfaces from/to DUT
    // ...
    input logic Clk,
    output logic Rst_n
    );


    // Testbench tb;

    initial begin
        // tb = new();
        $display(\"Starting simulation...\");



        // tb.finish_simulation();
    end


endprogram: tb_program
"))
  (find-file file)
  (larumbe/verilog-header-hp)
  (save-buffer))


(defun larumbe/verilog-testbench-environment-defs-pkg (file)
  "Create `tb_defs_pkg' module from template"
  (with-temp-file file
    (insert "\
package tb_defs_pkg;
    // Simulation parameters
    timeprecision   = 1ps;
    timeunit        = 1ns;
    localparam CLKT = 10ns;  // 100 MHz

    // DUT instance parameters
    // ...

    // Other parameters
    // ...
endpackage : tb_defs_pkg
"))
  (find-file file)
  (larumbe/verilog-header-hp)
  (save-buffer))



(defun larumbe/verilog-testbench-environment-classes-pkg (file)
  "Create `tb_classes_pkg' module from template"
  (with-temp-file file
    (insert "\
package tb_classes_pkg;

// Drivers
// ...

// Monitor
// ...

// Test
// ...

endpackage : tb_defs_pkg
"))
  (find-file file)
  (larumbe/verilog-header-hp)
  (save-buffer))


(defun larumbe/verilog-testbench-environment-top (file dut-file clocks-file)
  "Create `tb_classes_pkg' module from template"
  (find-file file)
  (insert "\
// TODO: unit space imported packages

module tb_top () ;

    logic Clk;
    logic Rst_n;

    // TODO: Declare/Connect interfaces
    // axi4_lite_if axil_if (.AClk(Clk), .AReset_n(Rst_n));
    // ...

    // Clocks

    // Testbench
    tb_program I_TB_PROGRAM (
        .Clk   (Clk),
        .Rst_n (Rst_n)
        );


    // DUT Instantiation

endmodule // tb_<module_name>
")
  (goto-char (point-min))
  (search-forward "// DUT Instantiation")
  (setq current-prefix-arg 4) ; Add DUT instance with parameters and choosing template
  (larumbe/verilog-insert-instance-from-file dut-file) ; Includes `verilog-auto' expansion
  ;; Clocks
  (goto-char (point-min))
  (search-forward "// Clocks")
  (larumbe/verilog-insert-instance-from-file clocks-file)
  ;; Header and postprocessing
  (larumbe/verilog-header-hp)
  (save-buffer))





(defun larumbe/verilog-testbench-environment (dut-file dir)
  "DUT-FILE corresponds to the path of the DUT, assumming there is a module per file
Environment files will be created at specified DIR (clocks, program, defs_pkg, classes_pkg...)"
  (interactive "FSelect module from file: \nDSelect environment directory: ")
  (let ((module-name      (file-name-sans-extension (file-name-nondirectory dut-file)))
        (clocks-file      (concat (file-name-as-directory dir) "tb_clocks.sv"))
        (program-file     (concat (file-name-as-directory dir) "tb_program.sv"))
        (defs-pkg-file    (concat (file-name-as-directory dir) "tb_defs_pkg.sv"))
        (classes-pkg-file (concat (file-name-as-directory dir) "tb_classes_pkg.sv"))
        (top-file         (concat (file-name-as-directory dir) "tb_top.sv")))
    ;; Create Environment files
    (larumbe/verilog-testbench-environment-clocks      clocks-file)
    (larumbe/verilog-testbench-environment-program     program-file)
    (larumbe/verilog-testbench-environment-defs-pkg    defs-pkg-file)
    (larumbe/verilog-testbench-environment-classes-pkg classes-pkg-file)
    (larumbe/verilog-testbench-environment-top         top-file dut-file clocks-file)))


;;;; Case
(defun larumbe/verilog-case-template ()
  "Fetched and modified from `verilog-state-machine-add-case-fold' for sync FSMs"
  (interactive)
  (let (param-read)
    (insert "case (" (read-string "Expression: ") ")") (progn (electric-verilog-terminate-line) nil)
    (while (not(string-equal (setq param-read (read-string "Case: ")) "")) ; Empty string ends with case addition
      (insert (concat param-read ": begin"))       (progn (electric-verilog-terminate-line) nil)
      (insert (concat "// Output statements... ")) (progn (electric-verilog-terminate-line) nil)
      (insert (concat "end"))                      (progn (electric-verilog-terminate-line) nil)
      (electric-verilog-terminate-line))
    (insert "endcase") (electric-verilog-terminate-line)))


;;;; Enum, Typedef, Struct
(defvar larumbe-verilog-enum-types '("logic" "bit" "int" "integer" "other"))

(defun larumbe/verilog-compute-vector-width ()
  "Will return [width-1:0] as a string for enum/struct templates.
If a number is set, then calculus will be automatically performed. If set to 0 or 1, then do not set a vector.
If a constant is set, then it will be set to [CONSTANT-1:0].
DANGER: If width introduced is 0, it will be assumed as a human mistake and width 1 will be computed"
  (let (width-str width-num)
    (setq width-str (read-string "Width: "))
    (setq width-num (string-to-number width-str))
    ;; Corner case if width 0 or no width is introduced (assume 1)
    (when (or (string-equal width-str "0") (string-equal width-str ""))
      (setq width-num 1))
    ;; End of corner case
    (if (not (eq width-num 0)) ; width was a number different from 0, not a constant
        (if (> width-num 1)    ; Greater than 1 (i.e. a vector with brackets)
            (progn
              (setq width-num (1- width-num))
              (setq width-str (number-to-string width-num))
              (setq width-str (concat "[" width-str ":0]")))
          (setq width-str "")) ; Width was 1, just a signal without brackets
      (setq width-str (concat "[" width-str "-1:0]"))))) ;; If width was not a number but a constant, format properly [width-1:0]


(defun larumbe/verilog-enum-typedef-template (&optional typedef)
  "Insert enum contents for [typedef] enum template"
  (let (enum-item type (width ""))
    ;; Set typedef if specified
    (when typedef
      (insert "typedef "))
    ;; Select type for enum
    (setq type (completing-read "Type: " larumbe-verilog-enum-types))
    (if (string-equal type "other")
        (setq type (read-string "Type: ")))
    ;; Select width
    (if (or (string-equal type "logic") (string-equal type "bit"))
        (setq width (larumbe/verilog-compute-vector-width))
      (setq width "")) ; If not a vector disable width field
    (insert "enum " type width " {")
    (while (not (string-equal (setq enum-item (read-string "Item: ")) "")) ; Empty string ends with item addition
      (insert enum-item ", "))
    ;; Last item
    (delete-char -2)
    (insert "} ")
    ;; Name
    (if typedef
        (insert (read-string "Type Name: ") ";") ; Typedef
      (insert (read-string "Enum Name: ") ";"))  ; Enum
    (electric-verilog-terminate-line)))


(defun larumbe/verilog-struct-typedef-template (&optional typedef union)
  "Insert enum contents for [typedef] struct template"
  (let (struct-item type (width ""))
    ;; Set typedef if specified
    (when typedef
      (insert "typedef "))
    ;; Struct Header
    (if union
        (insert "union ")
      (insert "struct "))
    (when (yes-or-no-p "Packed?")
      (insert "packed "))
    (insert "{")
    (electric-verilog-terminate-line)
    ;; Struct fields
    (while (not (string-equal (setq struct-item (read-string "Item: ")) "")) ; Empty string ends with item addition
      (setq type (read-string "Type: " "logic"))
      ;; Select width
      (if (or (string-equal type "logic") (string-equal type "bit"))
          (setq width (larumbe/verilog-compute-vector-width))
        (setq width "")) ; If not a vector disable width field
      (insert type " " width " " struct-item ";")
      (electric-verilog-terminate-line))
    (insert "} ")
    ;; Struct Name
    (if typedef
        (insert (read-string "Type Name: ") ";")   ; Typedef
      (insert (read-string "Struct Name: ") ";"))  ; Enum
    (electric-verilog-terminate-line)))


;;;; Task
(defun larumbe/verilog-task-add-port (direction read)
  "Add inputs to task template"
  (let (type width)
    ;; Select type
    (setq type (read-string "Type: " "logic"))
    ;; Select width
    (if (or (string-equal type "logic") (string-equal type "bit"))
        (setq width (larumbe/verilog-compute-vector-width))
      (setq width "")) ; If not a vector disable width field
    ;; Insert port
    (insert direction " " type " " width " " read ",")
    (electric-verilog-terminate-line)))


(defun larumbe/verilog-task-custom ()
  "Insert a task definition."
  (interactive)
  (let (in-read out-read)
    (insert "task ")
    (insert (read-string "Task name: ") " (")
    (electric-verilog-terminate-line)
    (while (not(string-equal (setq in-read (read-string "Input signal: ")) ""))
      (larumbe/verilog-task-add-port "input" in-read))
    (while (not(string-equal (setq out-read (read-string "Output signal: ")) ""))
      (larumbe/verilog-task-add-port "output" out-read))
    ;; INFO: "inout" or "ref" could be added in the future via universal-arg
    (insert ");") (electric-verilog-terminate-line)
    (save-excursion
      (electric-verilog-terminate-line)
      (insert (concat "endtask"))
      (electric-verilog-terminate-line)
      (electric-verilog-tab))
    ;; Align port declarations
    (re-search-backward "(")
    (beginning-of-line)
    (next-line)
    (verilog-pretty-declarations)
    (re-search-forward ");")
    (next-line)
    (electric-verilog-tab)))



;;;; Hydra
(defhydra hydra-verilog-template (:color blue
                                         :hint nil)
  "
RTL                          TESTBENCH                       COMMON
^^
_af_: always ff                _@_:  (posedge Clk)               _for_: for             _td_: typedef
_ac_: always comb              _in_: initial                     _ff_: function         _en_: enum
_aa_: always                   _ta_: task (1 line)               _ll_: logic signal     _te_: typedef enum
_ms_: module simple            _tk_: task template               _lv_: logic vector     _st_: struct
_md_: module w/params          _cl_: class                       _lp_: localparam       _ts_: typedef struct
_gn_: generate                 _fv_: forever                     _pm_: parameter        _un_: union
_it_: interface                _rp_: repeat                      _pc_: package          _tu_: typedef union
_mp_: modport                  _fj_: fork-join                   _bg_: begin/end        ^^
_cc_: case                     _fa_: fork-join any               _fe_: foreach          _/_: Star comment
_as_: assign                   _fn_: fork-join none              _if_: if               _B_: Block comment
_FS_: FSM sync                 _rn_: rand/constraint             _ei_: else if          _D_: Define signal
_IS_: Inst simple              _cb_: clocking block              _el_: else             _hd_: HP Header
_IP_: Inst w/params            _d_:  display                     _wh_: while            ^^
^^                             _ai_: assert immediate            _wd_: do-while^^
^^                             _ap_: assert property             ^^
^^                             _pr_: property                    ^^
^^                             _sq_: sequence                    ^^
^^                             _fl_: final                       ^^
^^                             _pg_: program                     ^^
^^                             _cg_: covergroup                  ^^
^^                             _TS_: Testbench Simple            ^^
^^                             _TE_: Testbench Environment       ^^
"
  ;;;;;;;;;
  ;; RTL ;;
  ;;;;;;;;;
  ("af"  (larumbe/hydra-yasnippet "af"))  ; always_ff
  ("ac"  (larumbe/hydra-yasnippet "ac"))  ; always_comb
  ("aa"  (larumbe/hydra-yasnippet "aa"))  ; always
  ("ms"  (larumbe/hydra-yasnippet "ms"))  ; module simple
  ("md"  (larumbe/hydra-yasnippet "md"))  ; module with parameter
  ("gn"  (larumbe/hydra-yasnippet "gn"))  ; generate
  ("it"  (larumbe/hydra-yasnippet "it"))  ; interface
  ("mp"  (larumbe/hydra-yasnippet "mp"))  ; Modport
  ("cc"  (larumbe/verilog-case-template)) ; case
  ("as"  (larumbe/hydra-yasnippet "as"))  ; assign
  ;; FSM
  ("FS"  (larumbe/verilog-state-machine-sync-custom)) ; Sync FSM
  ;; Instances from file
  ("IS"  (call-interactively 'larumbe/verilog-insert-instance-from-file))             ; Simple (no params)
  ("IP"  (call-interactively 'larumbe/verilog-insert-instance-from-file-with-params)) ; With params

  ;;;;;;;;;;;;;;;
  ;; TestBench ;;
  ;;;;;;;;;;;;;;;
  ("@"   (larumbe/hydra-yasnippet "@"))  ; Clk posedge
  ("in"  (larumbe/hydra-yasnippet "in")) ; Initial
  ("ta"  (larumbe/hydra-yasnippet "ta")) ; Task 1 line
  ("tk"  (larumbe/verilog-task-custom))  ; Task multiple ports
  ("cl"  (larumbe/hydra-yasnippet "cl")) ; Class
  ("fv"  (larumbe/hydra-yasnippet "fv")) ; Forever
  ("rp"  (larumbe/hydra-yasnippet "rp")) ; Repeat
  ("fj"  (larumbe/hydra-yasnippet "fj")) ; Fork-join
  ("fa"  (larumbe/hydra-yasnippet "fa")) ; Fork-join_any
  ("fn"  (larumbe/hydra-yasnippet "fn")) ; Fork-join_none
  ("rn"  (larumbe/hydra-yasnippet "rn")) ; Rand/Constraint
  ("cb"  (larumbe/hydra-yasnippet "cb")) ; Clocking block
  ("d"   (larumbe/hydra-yasnippet "d"))  ; Display for debug
  ("ai"  (larumbe/hydra-yasnippet "ai")) ; assert immediate
  ("ap"  (larumbe/hydra-yasnippet "ap")) ; assert property
  ("pr"  (larumbe/hydra-yasnippet "pr")) ; property
  ("sq"  (larumbe/hydra-yasnippet "sq")) ; sequence
  ("fl"  (larumbe/hydra-yasnippet "fl")) ; Final
  ("pg"  (larumbe/hydra-yasnippet "pg")) ; Program
  ("cg"  (larumbe/hydra-yasnippet "cg")) ; Covergroup
  ;; Testbench from DUT file
  ("TS"   (call-interactively 'larumbe/verilog-testbench-insert-template-simple))
  ("TE"   (call-interactively 'larumbe/verilog-testbench-environment))
  ;;  TODO: Coverage at some point?
  ;;      : More constraints, rand and randc
  ;;         - Distribution templates?

  ;;;;;;;;;;;;
  ;; Common ;;
  ;;;;;;;;;;;;
  ("for" (larumbe/hydra-yasnippet "for"))  ; For
  ("ff"  (larumbe/hydra-yasnippet "ff")) ; function
  ("ll"  (larumbe/hydra-yasnippet "ll")) ; logic signal
  ("lv"  (larumbe/hydra-yasnippet "lv")) ; logic vector
  ("lp"  (larumbe/hydra-yasnippet "lp")) ; Localparam
  ("pm"  (larumbe/hydra-yasnippet "pm")) ; Parameter
  ("pc"  (larumbe/hydra-yasnippet "pc")) ; Package
  ("bg"  (larumbe/hydra-yasnippet "bg")) ; begin/end
  ("fe"  (larumbe/hydra-yasnippet "fe")) ; Foreach
  ("if"  (larumbe/hydra-yasnippet "if"))
  ("ei"  (larumbe/hydra-yasnippet "ei")) ; Else if
  ("el"  (larumbe/hydra-yasnippet "el")) ; else
  ("wh"  (larumbe/hydra-yasnippet "wh")) ; While
  ("wd"  (larumbe/hydra-yasnippet "wd")) ; Do-while
  ("td"  (larumbe/hydra-yasnippet "td")) ; Generic typedef
  ("en"  (larumbe/verilog-enum-typedef-template nil))     ; Enum
  ("te"  (larumbe/verilog-enum-typedef-template t))       ; Typedef Enum
  ("st"  (larumbe/verilog-struct-typedef-template nil))   ; Struct
  ("ts"  (larumbe/verilog-struct-typedef-template t))     ; Typedef struct
  ("un"  (larumbe/verilog-struct-typedef-template nil t)) ; Union
  ("tu"  (larumbe/verilog-struct-typedef-template t t))   ; Typedef Union
  ("/"   (larumbe/hydra-yasnippet "/"))  ; Star comment
  ("B"   (larumbe/verilog-add-block-comment))
  ("D"   (larumbe/verilog-define-signal))
  ("hd"  (call-interactively 'larumbe/verilog-header-hp)) ; header for HP

  ;;;;;;;;;
  ;; UVM ;;
  ;;;;;;;;;
  ;; TODO: Check already existing templates
  ;; ("uc"  (larumbe/hydra-yasnippet "uvm-component"))
  ;; ("uo"  (larumbe/hydra-yasnippet "uvm-object"))

  ;;;;;;;;;;;;
  ;; Others ;;
  ;;;;;;;;;;;;
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))



;;; Imenu and instance navigating
;; INFO: There are 3 ways of creating the index-alist for Imenu mode (from simpler to more complex):
;;
;;   1 - Define `imenu-generic-expression' (categories and regexps). This is the most common and default one.
;;
;;   2 - Define `imenu-prev-index-position-function' and `imenu-extract-index-name-function'.
;;       If these variables are defined, the imenu-list creation function uses them to find the tags.
;;
;;   3 - Redefine `imenu-create-index-function' to make a custom more complex alist (e.g a tree recursively for nested classes)
;;       This is the most complex and the one used in python mode.

(defun larumbe/verilog-imenu (&optional test)
  "Custom imenu function with `imenu-list' for verilog-mode.
If inside a module, focuses on instance highlighting and checks if there is a semicolon
in instance comments that might cause issues detecting the regexp.

If inside a package, focuses on classes/methods highlighting with a custom tree build function.

If TEST is passed as an universal argument, then build Imenu with method 2 just for testing purposes (in case it could be useful in the future...)
"
  (interactive "P")
  (let ((end-keywords '("endmodule" "endpackage" "endprogram"))
        issue
        context)
    (save-excursion
      (end-of-buffer)
      (unless (re-search-backward (regexp-opt end-keywords 'symbols) nil t)
        (error "Imenu not supported for this kind of expression: %s not found" end-keywords))
      (verilog-backward-sexp)
      (setq context (thing-at-point 'symbol t))
      (when test
        (setq context "imenu-debug"))
      (message "Context: %s" context)
      (cond
       ;; Imenu method 1: Generate Imenu for modules (RTL)
       ((string= context "module")
        (setq imenu-prev-index-position-function nil)
        (setq imenu-extract-index-name-function nil)
        (setq imenu-create-index-function 'imenu-default-create-index-function)
        (setq issue (larumbe/verilog-find-semicolon-in-instance-comments))
        (imenu-list)
        (larumbe/verilog-imenu-hide-all t)
        (when issue
          (error "Imenu DANGER!: semicolon in comment instance!!")))
       ;; Imenu method 3: Generate Imenu for packages/classes (TB)
       ((or (string= context "package") (string= context "program"))
        (setq imenu-prev-index-position-function nil)
        (setq imenu-extract-index-name-function nil)
        (setq imenu-create-index-function 'verilog--imenu-index)
        (imenu-list))
       ;; Imenu method 2: Unuseful for the moment...
       ((string= context "imenu-debug")
        (setq imenu-prev-index-position-function 'larumbe/verilog-imenu-prev-index-position-function)
        (setq imenu-extract-index-name-function 'larumbe/verilog-imenu-extract-index-name)
        (setq imenu-create-index-function 'imenu-default-create-index-function)
        (imenu-list))
       ;; Default fallback
       (t
        (error "File context: %s is neither `module' for RTL, nor `package' for TB!" context))))))


;;;; Imenu method 1: Generic tree Imenu (RTL)
;; Same as modi's one
(setq larumbe/verilog-identifier-re
      (concat "\\_<\\(?:"
              "\\(?:[a-zA-Z_][a-zA-Z0-9$_]*\\)" ; simple identifier
              "\\|\\(?:\\\\[!-~]+\\)"           ; escaped identifier
              "\\)\\_>"))

;; "Modi's Regexp modified to match valid Verilog/SystemVerilog module instance declaration."
(setq larumbe/newline-or-space-optional "\\(?:[[:blank:]\n]\\)*")
(setq larumbe/newline-or-space-mandatory "\\(?:[[:blank:]\n]\\)+")
(setq larumbe/param-port-list "([^;]+?)")
(setq larumbe/verilog-module-instance-re
      (concat "^[[:blank:]]*"
              "\\(?1:" larumbe/verilog-identifier-re "\\)" ;module name (subgroup 1)
              larumbe/newline-or-space-optional ; For modi its mandatory, but thats a problem since it could be: btd#(
              ;; optional port parameters
              "\\("
              "#" larumbe/newline-or-space-optional larumbe/param-port-list
              "\\([[:blank:]]*//.*?\\)*"  ;followed by optional comments
              "[^;\\./]+?"  ;followed by 'almost anything' before instance name
              "\\)*"
              "\\(?2:" larumbe/verilog-identifier-re "\\)" ;instance name (subgroup 2)
              ;; Added by Larumbe
              "\\(\\[.*\\]\\)*"         ; SystemVerilog sometimes instantiates array of modules with brackets after instance name
              larumbe/newline-or-space-optional
              "(" ; And finally .. the opening parenthesis `(' before port list
              ;; Added by Larumbe (detect dot (port connection) after instance name parenthesis)
              larumbe/newline-or-space-optional
              ;; "[^;]+?"  ;followed by 'almost anything' before instance name -> This one requires content between brackets (instances only)
              "[^;]*?"  ;followed by 'almost anything' before instance name -> This one does not require contents necessarily between brackets (instances+interfaces)
              ")"
              larumbe/newline-or-space-optional
              ";"
              ))


;; Set imenu patterns (SystemVerilog): https://www.veripool.org/issues/1025-Verilog-mode-Integration-with-the-speedbar
;; This function extends the value of the variable present in `verilog-mode.el'
;; DANGER: Does note recognize instances when there are line-comments that end in `;'
(setq larumbe/verilog-imenu-generic-expression
      (append
       verilog-imenu-generic-expression
       `(("*Localparams*"    "^\\s-*localparam\\s-+\\([a-zA-Z0-9_.:]+\\)" 1)
         ("*Defines*"        "^\\s-*`define\\s-+\\([a-zA-Z0-9_.:]+\\)" 1)
         ("*Assigns*"        "^\\s-*assign\\s-+\\([a-zA-Z0-9_.:]+\\)" 1)
         ("*Always blocks*"  "^\\s-*always\\(_ff\\|_comb\\|_latch\\)?\\s-*\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)" 4)
         ("*Initial blocks*" "^\\s-*initial\\s-+\\(.*\\)\\(begin\\)?[ |\n]*\\(.*\\)" 3)
         ;; Instantiations for comment-erased buffer
         ("*Instances*"      ,larumbe/verilog-module-instance-re 1) ;; Use regexp index 2 if want to get instance name instead
         )
       ))

;; INFO: Issues with instance detection @ generic Imenu:
;;
;; 1 - Imenu must work on current buffer. Creates an alist of (elements . #<mark pos at buffer>)
;;     Therefore, must be executed on the buffer on which it will have the effect (cannot use with-temp-buffer in a buffer with no comments
;;     and trying to reassociate afterwards)
;;
;; 2 - Imenu just ignores comments starting at the beginning of line, not inline comments that might be within the instance regexp.
;;
;; 3 - It is not possible to work with (with-comments-hidden) since it makes comments invisible, and imenu ignores invisible characters
;;     by looking for the next non-invisible regexp, since `re-search-forward' cannot ignore invisible, just skip to the next.
;;     The problem is that instances regexp are multiline, and if an unexpected character such as comment with semicolon appears, it won't
;;     be recognized, and there wont be any chance of skip to the next. It will be missed.
;;
;; 4 - A first solution seemed to be executing `imenu' after erasing comments from current buffer and then returning it to its initial state
;;     But that would require use of `larumbe/delete-comments-from-buffer' (very slow) and `undo', with some issues programatically.
;;     That would need  to be done with `larumbe/find-verilog-module-instance-fwd' as well. The profit would not be worth the effort due to
;;     an extreme fall in performance.
;;
;; 5 - Best solution is to create a function that checks if there are problematic regexps in a verilog file, and set is as a hook every time
;;     a file is opened, or Imenu is executed.


(defun larumbe/verilog-find-semicolon-in-instance-comments ()
  "Find semicolons in instance comments to avoid missing instantiation detections with `imenu' and `larumbe/find-verilog-module-instance-fwd' functions.
Point to problematic regexp in case it is found."
  (let ((problem-re ")[, ]*\\(//\\|/\\*\\).*;") ; DANGER: Does not detect semicolon if newline within /* comment */
        (found))
    (save-excursion
      (beginning-of-buffer)
      (when (re-search-forward problem-re nil t)
        (setq found t)))
    (when found
      (beginning-of-buffer)
      (re-search-forward problem-re nil t)
      (message "Imenu DANGER!: semicolon in comment instance!!"))))


(defun larumbe/verilog-imenu-hide-all (&optional first)
  "Hides all the blocks @ Imenu-list buffer.
If optional FIRST is used, then shows first block (Verilog *instances/interfaces*)"
  (interactive)
  (if (string-equal major-mode "imenu-list-major-mode")
      (progn
        (beginning-of-buffer)
        (while (< (point) (point-max))
          (hs-hide-block)
          (next-line))
        (beginning-of-buffer)
        ;; If there is an optional argument, unfold first block
        (when first
          (hs-show-block)))
    (message "Not in imenu-list mode !!")))



;;;; Imenu method 2 (debug)
;; This method was insufficient to implement Imenu with functions/tasks within classes
;; Code still here for the coming future... One never knows...
(defun larumbe/verilog-imenu-prev-index-position-function ()
  "Function to search backwards in the buffer for Imenu alist generation."
  (verilog-beg-of-defun))

(defun larumbe/verilog-imenu-extract-index-name ()
  "Function to extract the tag."
  (verilog-forward-word)
  (verilog-forward-syntactic-ws)
  (thing-at-point 'symbol t))



;;;; Imenu method 3: Custom tree builder functions (TB)
;; Regexps fetched from `verilog-imenu-generic-expression' and adapted to match specific capture groups
(defvar larumbe/verilog-task-re "^\\s-*\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*task\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?2:[A-Za-z_][A-Za-z0-9_:]+\\)")
(defvar larumbe/verilog-function-re "^\\s-*\\(?1:\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*function\\)\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?:\\w+\\s-+\\)?\\(?:\\(?:un\\)signed\\s-+\\)?\\(?2:[A-Za-z_][A-Za-z0-9_:]+\\)")
(defvar larumbe/verilog-class-re "^\\s-*\\(?1:\\(?:\\(?:virtual\\|interface\\)\\s-+\\)?class\\)\\s-+\\(?2:[A-Za-z_][A-Za-z0-9_]+\\)")

(defun verilog-imenu-format-item-label (type name)
  "Return Imenu label for single node using TYPE and NAME."
  (let (short-type)
    (setq short-type
          (pcase type
            ("task"      "T")
            ("function"  "F")
            (_           type)))
    (format "%s (%s)" name short-type)))


(defun verilog-imenu--put-parent (type name pos tree)
  "Add the parent with TYPE, NAME and POS to TREE."
  (let* ((label
         (funcall 'verilog-imenu-format-item-label type name))
         (jump-label label))
    (if (not tree)
        (cons label pos)
      (cons label (cons (cons jump-label pos) tree)))))


(defun verilog-imenu--build-tree (&optional tree)
  "Build the imenu alist tree.
Coded to work with verification files with CLASSES and METHODS.
Adapted from `python-mode' imenu build-tree function."
  (save-restriction
    (narrow-to-region (point-min) (point))
    (let* ((pos
            (progn
              ;; finds a top-level class
              (verilog-beg-of-defun)
              ;; stops behind the indented form at EOL
              (verilog-forward-sexp)
              ;; may find an inner def-or-class
              (modi/verilog-jump-to-header-dwim nil)))
           type
           (name (when (and pos (or (looking-at larumbe/verilog-task-re)
                                    (looking-at larumbe/verilog-function-re)
                                    (looking-at larumbe/verilog-class-re)))
                   (setq type (match-string-no-properties 1))
                   (match-string-no-properties 2)))
           (label (when name
                    (funcall 'verilog-imenu-format-item-label type name))))
      (cond ((not pos)
             ;; Nothing found, probably near to bobp.
             nil)
            ((looking-at larumbe/verilog-class-re)
             ;; The current indentation points that this is a parent
             ;; node, add it to the tree and stop recursing.
             (verilog-imenu--put-parent type name pos tree))
            (t
             (verilog-imenu--build-tree
              (if (or (looking-at larumbe/verilog-task-re)
                      (looking-at larumbe/verilog-function-re))
                  (cons (cons label pos) tree)
                (cons
                 (verilog-imenu--build-tree
                  (list (cons label pos)))
                 tree))))))))


(defun verilog--imenu-index ()
  "Return tree Imenu alist for the current Verilog buffer. "
  (save-excursion
    (goto-char (point-max))
    (let ((index)
          (tree))
      (while (setq tree (verilog-imenu--build-tree))
        (setq index (cons tree index)))
      index)))



;;; Custom Functions
;; Fetched from: https://www.veripool.org/issues/724-Verilog-mode-How-to-make-word-navigation-commands-stop-at-underscores-
(defun verilog-forward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores withouth destroying verilog-mode syntax highlighting/indentation."
  (interactive "p")
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (forward-word arg))))

(defun verilog-backward-word (&optional arg)
  "Make verilog word navigation commands stop at underscores withouth destroying verilog-mode syntax highlighting/indentation."
  (interactive "p")
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (with-syntax-table table
      (backward-word arg))))

(defun larumbe/electric-verilog-tab ()
  "Wrapper of the homonym verilog function to avoid indentation issues with compiler directives after setting custom hooks.."
  (interactive)
  (let ((table (make-syntax-table verilog-mode-syntax-table)))
    (modify-syntax-entry ?` "w" table)
    (with-syntax-table table
      (electric-verilog-tab))))


;; https://emacs.stackexchange.com/questions/8032/configure-indentation-logic-to-ignore-certain-lines/8033#8033
(defun larumbe/verilog-avoid-indenting-outshine-comments (&rest args)
  "Ignore outshine comments for indentation.
Return t if the current line starts with '// *'."
  (interactive)
  (let ((match (looking-at "^[[:blank:]]*// \\*")))
    (when match (delete-horizontal-space))
    match))


(defun larumbe/find-verilog-module-instance-fwd ()
  "with-comments-hidden will make comments invisible, but that does not work with `search-forward'..."
  (interactive)
  (if (not (re-search-forward larumbe/verilog-module-instance-re nil t))
      (message "No more instances forward")
    (message "%s" (match-string 1))))


(defun larumbe/find-verilog-module-instance-bwd ()
  "with-comments-hidden will make comments invisible, but that does not work with `search-forward'..."
  (interactive)
  (if (not (re-search-backward larumbe/verilog-module-instance-re nil t))
       (message "No more instances backwards")
    (message "%s" (match-string 1))))



(defun larumbe/verilog-indent-current-module (&optional module)
  "Indent current module, the one pointed to by `which-func' (not instant)

For use programatically, an argument needs to be specified as current-module is determined by `which-func' and that takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let (current-module)
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (re-search-backward (concat "\\_<" current-module "\\_>"))
      (beginning-of-line) ; INFO: Needed to detect current instantiation and avoid the "No more instances forward" error message
      (set-mark (point))
      (larumbe/find-verilog-module-instance-fwd)
      (electric-verilog-tab))))


(defun larumbe/verilog-align-parameters-current-module (&optional module)
  "Align parenthesis PARAMETERS of current module, the one pointed to by `which-func' (not instant).
It will align parameters contained between module name and instance name.

For use programatically, an argument needs to be specified as current-module is determined by `which-func' and that takes time,
therefore not detecting the proper module but the previous one."
  (interactive)
  (let (current-module current-instance beg end)
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (if module
        (setq current-module module)
      (setq current-module modi/verilog-which-func-xtra)) ; Find module header (modi/verilog-which-func-xtra)
    (save-excursion
      (re-search-backward (concat "\\_<" current-module "\\_>"))
      (next-line 1) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward current-instance)))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Parameters aligned...")))


(defun larumbe/verilog-align-ports-current-module ()
  "Align parenthesis PORTS of current module, the one pointed to by `modi/verilog-find-module-instance'
It will only align ports, i.e., between instance name and end of instantiation."
  (interactive)
  (let (current-instance beg end)
    (setq current-instance (substring-no-properties (modi/verilog-find-module-instance)))
    (save-excursion
      (re-search-backward (concat "\\_<" current-instance "\\_>"))
      (next-line 1) ; Assumes ports start at next line from instance name
      (setq beg (point))
      (setq end (re-search-forward ");")))
    (align-regexp beg end "\\(\\s-*\\)(" 1 1 nil) ; Requires one capture group: https://stackoverflow.com/questions/14583702/align-regexp-from-emacs-lisp
    (message "Ports aligned...")))


(defun larumbe/verilog-beautify-current-module ()
  "Beautify current module (open parenthesis +indent + align)"
  (interactive)
  (save-excursion
    (larumbe/verilog-indent-current-module)
    (larumbe/verilog-align-ports-current-module)
    (larumbe/verilog-align-parameters-current-module)))


(defvar larumbe/connect-disconnect-port-re "\\.\\(?1:[a-zA-Z0-9_-]+\\)\\(?2:[[:blank:]]*\\)")
(defvar larumbe/connect-disconnect-conn-re "(\\(?3:.*\\))")
(defvar larumbe/connect-disconnect-not-found "No port detected at current line")

(defun larumbe/verilog-toggle-connect-port (force-connect)
  "Connect/disconnect port @ current line (regexp based).
If regexp detects that port is connected, then disconnect it. The other way round works the same.
If called with universal arg, `force-connect' parameter will force connection of current port, no matter it is connected/disconnected"
  (interactive "P")
  (let* ((port-regex larumbe/connect-disconnect-port-re)
         (conn-regex larumbe/connect-disconnect-conn-re)
         (line-regex (concat port-regex conn-regex))
         port conn sig
         (start (point)))
    ;; Find '.port (conn)' verilog regexp
    (beginning-of-line)
    (if (re-search-forward line-regex (point-at-eol) t)
        (progn
          (setq port (substring-no-properties (match-string 1)))
          (setq conn (substring-no-properties (match-string 3)))
          (if (or (string-equal conn "") force-connect) ; If it is disconnected or connection is forced via parameter...
              (progn ; Connect
                (setq sig (read-string (concat "Connect [" port "] to: ") conn))
                (replace-match (concat ".\\1\\2\(" sig "\)") t))
            (progn ; Else disconnect
              (replace-match (concat ".\\1\\2()") t)))
          (goto-char start)
          (next-line 1))
      (progn ; No port found
        (goto-char start)
        (message larumbe/connect-disconnect-not-found)))))


(defun larumbe/verilog-connect-ports-recursively ()
  "Ask recursively for ports to be connected until no port is found at current line"
  (interactive)
  (while (not (string-equal (larumbe/verilog-toggle-connect-port t) larumbe/connect-disconnect-not-found))))


(defun larumbe/verilog-def-logic (sig)
  "Replaces `verilog-sk-def-reg' for use within `larumbe/verilog-define-signal'"
  (let (width str)
    (split-line) ;; Keep indentation
    (setq width (larumbe/verilog-compute-vector-width))
    (setq str (concat "logic " width " " sig ";"))
    (insert str)
    (message (concat "[Line " (format "%s" (line-number-at-pos)) "]: " str))))


(defun larumbe/verilog-define-signal ()
  "INFO: Copied/modified from `verilog-mode.el' function: `verilog-sk-define-signal'.
There were some issues with this skeleton, an a function offers more flexibility.

Insert a definition of signal under point at top of module."
  (interactive "*")
  (let* ((sig-re "[a-zA-Z0-9_]*")
         (sig (buffer-substring
               (save-excursion
                 (skip-chars-backward sig-re)
                 (point))
               (save-excursion
                 (skip-chars-forward sig-re)
                 (point)))))
    (if (not (member sig verilog-keywords))
        (save-excursion
          (verilog-beg-of-defun)
          (verilog-end-of-statement)
          (verilog-forward-syntactic-ws)
          (larumbe/verilog-def-logic sig))
      (message "object at point (%s) is a keyword" sig))))



(defun larumbe/gtags-verilog-files-pwd-recursive ()
  "Generate gtags.files for current directory. Purpose is to be used with dired mode for small projects, to save the regexp"
  (interactive)
  (larumbe/directory-files-recursively-to-file (list default-directory) "gtags.files" ".[s]?v[h]?$"))


(defun larumbe/ggtags-create-verilog-tags-recursive ()
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-verilog-files-pwd-recursive)
  (ggtags-create-tags default-directory))


(defun larumbe/verilog-clean-parenthesis-blanks ()
  "Cleans blanks inside parenthesis blocks (Verilog port connections).
If region is not used, then a query replacement is performed instead.
DANGER: It may wrongly detect some `old-end' regexp matches, but seems too complex for the effort..."
  (interactive)
  (let ((old-start "([ ]+\\(.*\\))")
        (new-start "(\\1)")
        (old-end "(\\([^ ]+\\)[ ]+)")
        (new-end "(\\1)"))
    (if (use-region-p)
        (progn
          (message "Removing blanks at the beginning...")
          (replace-regexp old-start new-start nil (region-beginning) (region-end))
          (replace-regexp old-end   new-end   nil (region-beginning) (region-end)))
      (progn
        (message "Removing blanks at the end...")
        (query-replace-regexp old-start new-start nil (point-min) (point-max))
        (query-replace-regexp old-end   new-end   nil (point-min) (point-max))))))


(defun larumbe/verilog-list-directories-of-open-buffers ()
  "Base content fetched from: https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
Returns a list of directories from current verilog opened files. Useful for `verilator' flycheck include directories"
  (let (verilog-opened-dirs)
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "verilog-mode")
          (add-to-list 'verilog-opened-dirs default-directory))))
    (eval 'verilog-opened-dirs)))  ; Return list of -I directories



;;; Verilog-Perl hierarchy
(defvar larumbe-verilog-perl-buffer-name "Verilog-Perl"
  "Initial buffer name to use for the hierarchy file")

;; INFO: First preprocesses input files in a file for `include' and `define' expansion. Then extracts hierarchy from that preprocessed file.
;; Init variables for VHIER Generation to nil
(setq larumbe-verilog-perl-top-module nil)
(setq larumbe-verilog-perl-project-vhier-path nil)
(setq larumbe-verilog-perl-hier-input-files nil)
(setq larumbe-verilog-perl-hier-file nil)

(setq larumbe-verilog-perl-preprocessed-file nil)
(setq larumbe-verilog-perl-outargs nil)
(setq larumbe-verilog-perl-prep-outargs nil)

;; Projects list
;; Name of the project (+plus)
;; 1) Name of the top-module
;; 2) Input files for hierarchy elaboration
;; 3) vhier folder path (for generation and further reading)
;; 4) Output hierarchy file path


;; Retrieve VHIER project list and set variables accordingly
(defun larumbe/verilog-vhier-set-active-project ()
  (let ((vhier-project)
        (files-list))
    ;; Get Project name
    (setq vhier-project (completing-read "Select project: " (mapcar 'car larumbe-verilog-perl-projects))) ;; Read previous variable and get list of first element of each assoc list
    (setq files-list (cdr (assoc vhier-project larumbe-verilog-perl-projects)))
    ;; Set parameters accordingly
    (setq larumbe-verilog-perl-top-module         (nth 0 files-list))
    (setq larumbe-verilog-perl-hier-input-files   (nth 1 files-list))
    (setq larumbe-verilog-perl-project-vhier-path (nth 2 files-list))
    (setq larumbe-verilog-perl-hier-file          (nth 3 files-list))

    (setq larumbe-verilog-perl-preprocessed-file
          (concat
           larumbe-verilog-perl-project-vhier-path
           larumbe-verilog-perl-top-module "_pp.sv"))
    (setq larumbe-verilog-perl-outargs
          (concat
           "--cells" " "
           "--no-missing" " "
           "--missing-modules" " "
           "--top-module " larumbe-verilog-perl-top-module " "
           ))
    (setq larumbe-verilog-perl-prep-outargs
          (concat "-o " larumbe-verilog-perl-preprocessed-file))
    ))


;; Has to be done in the file with the relative include path so that it can be found (e.g. sllc_tb.sv)
(defun larumbe/verilog-vhier-preprocess-hierarchy ()
  "Preprocess hierarchy of top-level module for `includes and `defines.
Only used if hierarchy is extracted in project mode."
  (let ((processed-files (concat larumbe-verilog-perl-project-vhier-path "vhier.files"))
        (sorted-files-p nil) ; Used inside while loop to decide when every `defs_pkg' has been put at the beginning
        )
    (shell-command
     (concat "mkdir -p " larumbe-verilog-perl-project-vhier-path)) ; Create vhier folder if it did not exist
    (with-temp-buffer
      ;; (view-buffer-other-window (current-buffer))      ; INFO: Debug for `with-temp-buffer'
      ;; (clone-indirect-buffer-other-window "*debug*" t) ; INFO: Debug for `with-temp-buffer'
      (insert-file-contents larumbe-verilog-perl-hier-input-files)
      (replace-regexp "\\(.*/\\).*\.[s]?vh$" "-y \\1" nil (point-min) (point-max)) ; Replace header `include' files with -y library flag
      (larumbe/sort-regexp-at-the-beginning-of-file "_defs_pkg.sv") ;; Move every _defs_pkg.sv at the beginning
      (write-file processed-files))
    ;; Eecute preprocess command
    (shell-command
     (concat "vppreproc "
             "-f " processed-files " "
             larumbe-verilog-perl-prep-outargs))))


(defun larumbe/verilog-vhier-format-hierarchy-file ()
  "Process Verilog-Perl file prior to write it to hierarchy file.
Make an outline/outshine accessible view for use with Gtags)"
  (pop-to-buffer (get-buffer larumbe-verilog-perl-buffer-name))
  (save-excursion
    (replace-regexp "  " "*" nil (point-min) (point-max)) ; Replace blank spaces by * for outline
    (replace-regexp "*\\([a-zA-Z0-9_-]\\)" "* \\1" nil (point-min) (point-max)) ; Add blank after asterisks
    ;; Add comments on every line for outshine detection
    (beginning-of-buffer)
    (while (> (point-max) (point))
      (insert "// ")
      (beginning-of-line)
      (forward-line))
    ;; Parse not-used/not-found modules/files
    (beginning-of-buffer)
    (re-search-forward "// \\* ") ; Find top instance
    (when (re-search-forward "// \\* " nil t) ; Find second instance to add a blank line if non-found modules exist
      (beginning-of-line)
      (open-line 2)
      (forward-line)
      (insert "// * Not found module references") ; Create level for not found
      (replace-string "// * " "// ** " nil (point) (point-max)))
    ;; Insert header to get some info of the file
    (beginning-of-buffer)
    (open-line 1)
    (insert
     (concat "// Created by Larumbe at " (format-time-string "%d-%m-%Y, %H:%M:%S") "\n"))
    (if larumbe-verilog-perl-hier-input-files
        (insert (concat "// Hierarchy extracted from files included in: " larumbe-verilog-perl-hier-input-files "\n"))
      (insert (concat "// Hierarchy extracted from `larumbe/verilog-open-dirs' variable\n")))))


(defun larumbe/verilog-vhier-from-project ()
  "Extract hierarchy of top-level module using Verilog-Perl backend"
  (interactive)
  (larumbe/verilog-vhier-set-active-project)
  (larumbe/verilog-vhier-preprocess-hierarchy)
  (shell-command
   (concat "vhier "
           larumbe-verilog-perl-outargs
           larumbe-verilog-perl-preprocessed-file)
   larumbe-verilog-perl-buffer-name)
  (larumbe/verilog-vhier-format-hierarchy-file)
  ;; Save-file and enable verilog-mode for tag navigation
  (write-file larumbe-verilog-perl-hier-file)
  (vhier-outline-mode)
  (setq buffer-read-only t))


(defun larumbe/verilog-vhier-current-file (&optional extra-files)
  "Extract hierarchy of current file module using Verilog-Perl backend.
To handle packages that require being sourced before the rest of the files, use universal argument.
Prompt for a file of with the following format:

/path/to/package/pkg1.sv
/path/to/package/pkg2.sv
"
  (interactive "P")
  (let* ((library-args (mapconcat
                        (lambda (x) (concat "-y " x))
                        larumbe/verilog-open-dirs
                        " "))
         (pkg-files (when extra-files
                      (concat "-f " (read-file-name "Pkg file:") " ")))
         (top-module (file-title))
         (cmd (concat
               "vhier "
               pkg-files
               buffer-file-name " "
               "+libext+.sv+.svh" " "
               library-args " "
               "--cells" " "
               "--no-missing" " "
               "--missing-modules" " "
               "--top-module " top-module))
         (file-path (concat (projectile-project-root) "vhier/" top-module ".v")))
    ;; Body
    (verilog-read-defines) ; Not sure if needed...
    (verilog-read-includes)
    ;; (message "%s" cmd) ;; INFO: Debug
    (shell-command cmd larumbe-verilog-perl-buffer-name)
    (larumbe/verilog-vhier-format-hierarchy-file)
    (shell-command (concat "mkdir -p " (file-name-directory file-path))) ; Ensure vhier folder is created
    (write-file file-path) ; Ensure ggtags working by writing hier file into projectile root
    (vhier-outline-mode)
    (setq buffer-read-only t)))

