;;; vhdl-navigation.el --- VHDL Navigation  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'ag)
(require 'which-func)
(require 'init-vhdl)

;;;; Navigation
(defun larumbe/find-vhdl-module-instance-fwd (&optional limit)
  "Search forward for a VHDL module/instance regexp.

LIMIT argument is included to allow the function to be used to fontify VHDL buffers."
  (interactive)
  (let ((found nil)
        (pos))
    (save-excursion
      (when (called-interactively-p 'any) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (forward-char))              ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-forward larumbe/vhdl-instance-re limit t))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p 'any)
              (setq pos (match-beginning 6))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


(defun larumbe/find-vhdl-module-instance-bwd (&optional limit)
  "Search backwards for a VHDL module/instance regexp.

LIMIT argument is included to allow the function to be used to fontify VHDL buffers."
  (interactive)
  (let ((found nil)
        (pos))
    (save-excursion
      (when (called-interactively-p 'any) ; DANGER: If applied to verilog-font-locking will break multiline font locking.
        (backward-char))             ; Needed to avoid getting stuck if point is at the beginning of the regexp while searching
      (while (and (not found)
                  (re-search-backward larumbe/vhdl-instance-re limit t))
        (unless (or (equal (face-at-point) 'font-lock-comment-face)
                    (equal (face-at-point) 'font-lock-string-face))
          (setq found t)
          (if (called-interactively-p 'any)
              (setq pos (match-beginning 6))
            (setq pos (point))))))
    (when found
      (goto-char pos))))


;;;; Jump to modules
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
  (let ((module-name)
        (module-instance-pcre)
        (regexp)
        (ag-arguments ag-arguments)) ; Save the global value of `ag-arguments'
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
    (setq ag-arguments (append ag-arguments '("--vhdl")))
    (xref-push-marker-stack)
    (ag-regexp module-instance-pcre (projectile-project-root))))



(defun larumbe/vhdl-electric-return ()
  "Wrapper for RET key to add functionality when there is an AG search buffer.
This will normally happen after calling `larumbe/vhdl-find-parent-module'"
  (interactive)
  (let* ((ag-buf "*ag search*")
         (ag-win (get-buffer-window ag-buf)))
    (if ag-win
        (delete-window ag-win)
      (vhdl-electric-return))))


(provide 'vhdl-navigation)

;;; vhdl-navigation.el ends here
