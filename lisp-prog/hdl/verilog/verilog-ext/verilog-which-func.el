;;; verilog-which-func.el --- Verilog which func  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'which-func)
;; (require 'verilog-rx)
(require 'verilog-navigation)


(defvar-local verilog-ext-which-func-xtra nil
  "Variable to hold extra information for `which-func' to show in the
mode-line. For instance, if point is under \"module top\", `which-func' would
show \"top\" but also show extra information that it's a \"module\".")


;; TODO: Seems it's not used!
(defun hdl-ext-which-func-current ()
  ""
  (gethash (get-buffer-window) which-func-table))
;; End of TODO


(defun verilog-ext-which-func-find-instance ()
  ""
  (let (instance-point instance-type instance-name)
    (save-excursion
      (when (verilog-ext-instance-at-point)
        (setq instance-point (point))
        (setq instance-type (match-string-no-properties 1))
        (setq instance-name (match-string-no-properties 2))))
    (list instance-point instance-type instance-name)))


(defun verilog-ext-which-func-find-token ()
  ""
  (let (token-point token-type token-name)
    (save-excursion
      (when (verilog-ext-find-token-bwd)
        (setq token-point (point))
        (setq token-type (match-string-no-properties 1))
        ;; Similar to `verilog-ext-find-task-function-class-bwd'. TODO: Could be refactored?
        (if (or (looking-at verilog-ext-function-re)
                (looking-at verilog-ext-task-re)
                (looking-at verilog-ext-class-re)
                (looking-at verilog-ext-top-re))
            (setq token-name (match-string-no-properties 2))
          (setq token-name (buffer-substring-no-properties (point) (point-at-eol))))))
    (list token-point token-type token-name)))



(defun verilog-ext-which-func-maybe-shorten-token (token-type)
  ""
  (cond ((string= "module"      token-type) "mod")
        ((string= "interface"   token-type) "itf")
        ((string= "program"     token-type) "pgrm")
        ((string= "package"     token-type) "pkg")
        ((string= "class"       token-type) "cls")
        ((string= "function"    token-type) "fun")
        ((string= "task"        token-type) "task")
        ;; The rest already show the whole line
        (t "")))


(defun verilog-ext-which-func-set-instance (instance-type instance-name)
  ""
  (setq verilog-ext-which-func-xtra instance-name)
  instance-type)


(defun verilog-ext-which-func-set-token (token-type token-name)
  ""
  (setq verilog-ext-which-func-xtra (verilog-ext-which-func-maybe-shorten-token token-type))
  token-name)


(defun verilog-ext-which-func-decide (instance-data token-data)
  ""
  (let ((instance-point (nth 0 instance-data))
        (instance-type  (nth 1 instance-data))
        (instance-name  (nth 2 instance-data))
        (token-point (nth 0 token-data))
        (token-type  (nth 1 token-data))
        (token-name  (nth 2 token-data)))
    (cond (;; Instance found
           (and instance-point (not token-point))
           (verilog-ext-which-func-set-instance instance-type instance-name))
          ;; Token found
          ((and (not instance-point) token-point)
           (verilog-ext-which-func-set-token token-type token-name))
          ;; Both found: select closest one
          ((and instance-point token-point)
           (if (> instance-point token-point) ; which-func searches backwards, closest is the one with highest point value
               (verilog-ext-which-func-set-instance instance-type instance-name)
             (verilog-ext-which-func-set-token token-type token-name))))))



(defun verilog-ext-which-func-function ()
  ""
  (let ((instance-data (verilog-ext-which-func-find-instance))
        (token-data    (verilog-ext-which-func-find-token)))
    (verilog-ext-which-func-decide instance-data token-data)))


(defun verilog-ext-which-func ()
  (setq-local which-func-functions '(verilog-ext-which-func-function)))


(defun verilog-ext-which-func-update-format ()
  (setq-local which-func-format
              `("["
                (:propertize which-func-current
                 face (which-func :weight bold)
                 mouse-face mode-line-highlight)
                ":"
                (:propertize verilog-ext-which-func-xtra
                 face which-func
                 mouse-face mode-line-highlight)
                "]")))

;;;;; Setup
;; TODO: Do a minor-mode that adds/removes the hooks?
;; TODO: Enable when this thing of tokens gets fixed again
;; (add-hook 'verilog-mode-hook #'verilog-ext-which-func)
;; (add-hook 'verilog-mode-hook #'verilog-ext-which-func-update-format)



(provide 'verilog-which-func)

;;; verilog-which-func.el ends here
