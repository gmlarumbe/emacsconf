;;; verilog-hideshow.el --- Verilog Hideshow  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defvar larumbe/verilog-hs-block-start-keywords
  '("begin"
    "fork"
    "clocking"
    "function"
    "covergroup"
    "property"
    "task"
    "generate"))

(defvar larumbe/verilog-hs-block-end-keywords
  '("end"
    "join" "join_any" "join_none"
    "endclocking"
    "endfunction"
    "endgroup"
    "endproperty"
    "endtask"
    "endgenerate"))

(defvar larumbe/verilog-hs-block-end-keywords-re (regexp-opt larumbe/verilog-hs-block-start-keywords 'symbols))
(defvar larumbe/verilog-hs-block-end-keywords-re (regexp-opt larumbe/verilog-hs-block-end-keywords   'symbols))
(add-to-list 'hs-special-modes-alist `(verilog-mode ,larumbe/verilog-hs-block-end-keywords-re
                                                    ,larumbe/verilog-hs-block-end-keywords-re
                                                    nil
                                                    verilog-forward-sexp-function))



(provide 'verilog-hideshow)

;;; verilog-hideshow.el ends here
