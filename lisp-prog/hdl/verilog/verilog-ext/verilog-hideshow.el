;;; verilog-hideshow.el --- Verilog Hideshow  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(require 'hideshow)
(require 'verilog-mode)


(defconst verilog-ext-hs-block-start-keywords-re
  (eval-when-compile
    (verilog-regexp-words
     '("begin"
       "fork"
       "clocking"
       "function"
       "covergroup"
       "property"
       "task"
       "generate"))))

(defconst verilog-ext-hs-block-end-keywords-re
  (eval-when-compile
    (verilog-regexp-words
     '("end"
       "join" "join_any" "join_none"
       "endclocking"
       "endfunction"
       "endgroup"
       "endproperty"
       "endtask"
       "endgenerate"))))

;; Config
(add-to-list 'hs-special-modes-alist `(verilog-mode ,verilog-ext-hs-block-start-keywords-re
                                                    ,verilog-ext-hs-block-end-keywords-re
                                                    nil
                                                    verilog-forward-sexp-function))



(provide 'verilog-hideshow)

;;; verilog-hideshow.el ends here
