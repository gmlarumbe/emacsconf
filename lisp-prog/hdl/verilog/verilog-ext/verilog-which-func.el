;;; verilog-which-func.el --- Verilog which func  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defvar-local verilog-ext-which-func-xtra nil
  "Variable to hold extra information for `which-func' to show in the
mode-line. For instance, if point is under \"module top\", `which-func' would
show \"top\" but also show extra information that it's a \"module\".")


(defun verilog-ext-which-func-function ()
  ""
  (let (instance-type instance-name token-name token-full point-instance point-token token2-type token2-name)
    (save-excursion
      (when (verilog-ext-find-module-instance-bwd)
        (setq instance-type (match-string-no-properties 1))
        (setq instance-name (match-string-no-properties 2))
        (setq point-instance (point))))
    (save-excursion
      (when (verilog-ext-find-task-function-class-bwd)
        (setq token2-type (match-string-no-properties 1))
        (setq token2-name (match-string-no-properties 2))))
    ;; (save-excursion
    ;;   (when (and (verilog-ext-find-token-bwd)
    ;;              (not (string= (match-string-no-properties 1) "task"))
    ;;              (not (string= (match-string-no-properties 1) "function")))
    ;;     (setq point-token (point))
    ;;     (setq token-name (match-string-no-properties 1))
    ;;     (setq token-full (buffer-substring-no-properties point-token (point-at-eol)))))
    (cond (;; Instance found
           (and point-instance (not point-token))
           (setq verilog-ext-which-func-xtra instance-name)
           instance-type)
          ;; Token found
          ((and (not point-instance) point-token)
           (setq verilog-ext-which-func-xtra (cond
                                              ;; ((string= "class"     token-name) "class")
                                              ((string= "clocking"  token-name) "clk")
                                              ((string= "`define"   token-name) "macro")
                                              ((string= "group"     token-name) "group")
                                              ((string= "module"    token-name) "mod")
                                              ((string= "interface" token-name) "if")
                                              ((string= "package"   token-name) "pkg")
                                              ((string= "sequence"  token-name) "seq")
                                              (t (substring token-name 0 4))))
           token-full)
          ;; Closest one
          ;; TODO: Refactor previous choice of string= and use also here
          ;; TODO: Use a more generic way of finding what comes after the token and use it here
          ((and point-instance point-token)
           (if (> point-instance point-token)
               (progn
                 (setq verilog-ext-which-func-xtra instance-name)
                 instance-type)
             (setq verilog-ext-which-func-xtra )
             token-name)))))


;; TODO: Needs to be executed manually, dunno why it doesn't get loaded
(defun verilog-ext-which-func ()
  (setq-local which-func-functions '(verilog-ext-which-func-function)))


;; TODO: Still add some function to
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
(add-hook 'verilog-mode-hook #'verilog-ext-which-func)
(add-hook 'verilog-mode-hook #'verilog-ext-which-func-update-format)



(provide 'verilog-which-func)

;;; verilog-which-func.el ends here
