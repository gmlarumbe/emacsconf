;;; verilog-which-func.el --- Verilog which func  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defvar-local modi/verilog-which-func-xtra nil
  "Variable to hold extra information for `which-func' to show in the
mode-line. For instance, if point is under \"module top\", `which-func' would
show \"top\" but also show extra information that it's a \"module\".")


(defun modi/verilog-which-func ()
  (setq-local which-func-functions '(modi/verilog-find-module-instance
                                     modi/verilog-get-header))
  (which-function-mode))

(defun modi/verilog-update-which-func-format ()
  (let ((modi/verilog-which-func-echo-help
         (concat "mouse-1/scroll up: jump to header UP" "\n"
                 "mouse-3/scroll-down: jump to header DOWN")))

    (setq-local which-func-keymap
                (let ((map (make-sparse-keymap)))
                  ;; left click on mode line
                  (define-key map [mode-line mouse-1] #'modi/verilog-jump-to-header-dwim)
                  ;; scroll up action while mouse on mode line
                  (define-key map [mode-line mouse-4] #'modi/verilog-jump-to-header-dwim)
                  ;; middle click on mode line
                  (define-key map [mode-line mouse-2] #'modi/verilog-jump-to-header-dwim-fwd)
                  ;; scroll down action while mouse on mode line
                  (define-key map [mode-line mouse-5] #'modi/verilog-jump-to-header-dwim-fwd)
                  map))

    (if modi/verilog-which-func-xtra
        (setq-local which-func-format
                    `("["
                      (:propertize which-func-current
                       local-map ,which-func-keymap
                       face (font-lock-keyword-face :weight bold)
                       mouse-face mode-line-highlight
                       help-echo ,modi/verilog-which-func-echo-help)
                      ":"
                      (:propertize modi/verilog-which-func-xtra
                       local-map ,which-func-keymap
                       face font-lock-keyword-face
                       mouse-face mode-line-highlight
                       help-echo ,modi/verilog-which-func-echo-help)
                      "]"))
      (setq-local which-func-format
                  `("["
                    (:propertize which-func-current
                     local-map ,which-func-keymap
                     face font-lock-keyword-face
                     mouse-face mode-line-highlight
                     help-echo ,modi/verilog-which-func-echo-help)
                    "]")))))


(defun larumbe/verilog-update-which-func-format ()
  "Same as `modi/verilog-update-which-func-format'.
Modify `which-func' face color and set a slightly different format from modi's."
  (let ((modi/verilog-which-func-echo-help
         (concat "mouse-1/scroll up: jump to header UP" "\n"
                 "mouse-3/scroll-down: jump to header DOWN")))

    (setq-local which-func-keymap
                (let ((map (make-sparse-keymap)))
                  ;; left click on mode line
                  (define-key map [mode-line mouse-1] #'modi/verilog-jump-to-header-dwim)
                  ;; scroll up action while mouse on mode line
                  (define-key map [mode-line mouse-4] #'modi/verilog-jump-to-header-dwim)
                  ;; middle click on mode line
                  (define-key map [mode-line mouse-2] #'modi/verilog-jump-to-header-dwim-fwd)
                  ;; scroll down action while mouse on mode line
                  (define-key map [mode-line mouse-5] #'modi/verilog-jump-to-header-dwim-fwd)
                  map))

    ;; Customised by Larumbe to keep `which-func' face and a slightly different format
    (if modi/verilog-which-func-xtra
        (setq-local which-func-format
                    `("["
                      (:propertize modi/verilog-which-func-xtra
                       local-map ,which-func-keymap
                       face (which-func :weight bold)
                       mouse-face mode-line-highlight
                       help-echo ,modi/verilog-which-func-echo-help)
                      ":"
                      (:propertize which-func-current
                       local-map ,which-func-keymap
                       face which-func
                       mouse-face mode-line-highlightp
                       help-echo ,modi/verilog-which-func-echo-help)
                      "]"))
      (setq-local which-func-format
                  `("["
                    (:propertize which-func-current
                     local-map ,which-func-keymap
                     face which-func
                     mouse-face mode-line-highlight
                     help-echo ,modi/verilog-which-func-echo-help)
                    "]")))))


;;;;; Setup
(advice-add 'modi/verilog-update-which-func-format :override #'larumbe/verilog-update-which-func-format)
(add-hook 'verilog-mode-hook #'modi/verilog-which-func)



(provide 'verilog-which-func)

;;; verilog-which-func.el ends here
