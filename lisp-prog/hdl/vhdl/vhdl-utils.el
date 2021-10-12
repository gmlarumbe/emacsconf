;;; vhdl-utils.el --- VHDL Utilities  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'ggtags)
(require 'auto-complete)


;;;; Variables
(defvar larumbe/vhdl-entity-re "^\\s-*\\(entity\\)\\s-+\\(\\(\\w\\|\\s_\\)+\\)")
(defvar larumbe/vhdl-blank-opt-re "[[:blank:]\n]*")
(defvar larumbe/vhdl-blank-mand-re "[[:blank:]\n]+")
(defvar larumbe/vhdl-identifier-re "[a-zA-Z_][a-zA-Z0-9_-]*")
(defvar larumbe/vhdl-instance-re
  (concat "^\\s-*\\(?1:" larumbe/vhdl-identifier-re "\\)\\s-*:" larumbe/vhdl-blank-opt-re ; Instance TAG
          "\\(?2:\\(?3:component\\s-+\\|configuration\\s-+\\|\\(?4:entity\\s-+\\(?5:" larumbe/vhdl-identifier-re "\\)\.\\)\\)\\)?"
          "\\(?6:" larumbe/vhdl-identifier-re "\\)" larumbe/vhdl-blank-opt-re ; Module name
          "\\(--[^\n]*" larumbe/vhdl-blank-mand-re "\\)*\\(generic\\|port\\)\\s-+map\\>"))


;;;; Gtags
(defun larumbe/ggtags-create-vhdl-tags-recursive ()
  "Create global GTAGS of every VHDL file in the directory."
  (interactive)
  (let ((vhdl-file-re "\\.vhd[l]?$"))
    (larumbe/gtags-filelist-create vhdl-file-re)
    (larumbe/gtags-create-tags-async default-directory)))



;;;; Others
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
