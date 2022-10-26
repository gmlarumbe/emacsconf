;;; Utils

;;;; Others
;; https://emacs.stackexchange.com/questions/16874/list-all-buffers-with-specific-mode (3rd answer)
(defun vhdl-ext-list-directories-of-open-buffers ()
  "Return a list of directories from current VHDL open files.
Used for `ghdl' linter flycheck include directories among other things."
  (let ((vhdl-opened-dirs nil))
    (dolist ($buf (buffer-list (current-buffer)))
      (with-current-buffer $buf
        (when (string-equal major-mode "vhdl-mode")
          (setq vhdl-opened-dirs (push default-directory vhdl-opened-dirs)))))
    vhdl-opened-dirs))


;; TODO: This one shouldn't be needed anymore...
(defun vhdl-ext-electric-return ()
  "Wrapper for RET key to add functionality when there is an AG search buffer.
This will normally happen after calling `vhdl-ext-find-parent-module'"
  (interactive)
  (let* ((ag-buf "*ag search*")
         (ag-win (get-buffer-window ag-buf)))
    (if ag-win
        (delete-window ag-win)
      (vhdl-electric-return))))

;; Keys
;; ("<return>" . larumbe/vhdl-electric-return)
;; ("RET"      . larumbe/vhdl-electric-return)


