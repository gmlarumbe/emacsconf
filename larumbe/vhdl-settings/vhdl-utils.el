;;; vhdl-utils.el --- VHDL Utilities  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;;; Speedbar
;; TODO: Fetch last version with git submodules
;; (use-package sr-speedbar)
;; (require 'sr-speedbar)


;;;; Gtags
(defun larumbe/gtags-vhdl-files-pwd-recursive ()
  "Generate gtags.files for current directory. Purpose is to be used with dired mode for small projects, to save the regexp"
  (larumbe/directory-files-recursively-to-file default-directory "gtags.files" ".vhd[l]?$"))


(defun larumbe/ggtags-create-vhdl-tags-recursive ()
  (interactive)
  (shell-command "touch GTAGS")
  (larumbe/gtags-vhdl-files-pwd-recursive)
  (ggtags-create-tags default-directory))


;;;; Others
(defun larumbe/vhdl-list-directories-of-open-buffers ()
  "Base content fetched from: https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
Returns a list of directories from current VHDL opened files. Useful for `ghdl' linter flycheck include directories"
  (let (vhdl-opened-dirs)
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "vhdl-mode")
          (add-to-list 'vhdl-opened-dirs default-directory))))
    (eval 'vhdl-opened-dirs)))


(provide 'vhdl-utils)

;;; vhdl-utils.el ends here
