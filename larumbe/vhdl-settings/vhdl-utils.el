;;; vhdl-utils.el --- VHDL Utilities  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Gtags
(defun larumbe/gtags-vhdl-files-pwd-recursive ()
  "Generate gtags.files for VHDL files on current directory."
  (larumbe/directory-files-recursively-to-file default-directory "gtags.files" ".vhd[l]?$"))


(defun larumbe/ggtags-create-vhdl-tags-recursive ()
  "Create global GTAGS of every VHDL file in the directory."
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-vhdl-files-pwd-recursive)
  (ggtags-create-tags default-directory))


;;;; Others
(defun my-vhdl-mode-hook ()
  (set 'ac-sources '(ac-source-gtags))
  ;; Flycheck
  (setq flycheck-ghdl-include-path (larumbe/vhdl-list-directories-of-open-buffers))
  (setq flycheck-ghdl-language-standard "08")
  (setq flycheck-ghdl-work-lib vhdl-default-library) ; "xil_defaultlib"
  (setq flycheck-ghdl-workdir (concat (projectile-project-root) "library/" vhdl-default-library)) ; Used @ axi_if_converter
  (setq flycheck-ghdl-ieee-library "synopsys"))


;; https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
(defun larumbe/vhdl-list-directories-of-open-buffers ()
  "Return a list of directories from current VHDL open files.
Used for `ghdl' linter flycheck include directories among other things."
  (let ((vhdl-opened-dirs nil))
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "vhdl-mode")
          (setq vhdl-opened-dirs (push default-directory vhdl-opened-dirs)))))
    vhdl-opened-dirs))


(provide 'vhdl-utils)

;;; vhdl-utils.el ends here
