;;; Present in verilog-ext not in vhdl-ext
;;;; Not very time consuming
;;;; A bit more time consuming
;; TODO: Hierarchy extraction and navigation
;;;; Probably won't do
;; TODO: Find definitions and references
;; TODO: Auto-completion with dot and scope completion

;;  All of these require some type of project/workspace analysis
;;  Could reuse what's already existing in vhdl-mode?

;;;; Others
;;; Hierarchy with GHDL
;; Check page 11/11: http://www.dossmatik.de/ghdl/ghdl_unisim_eng.pdf
;; Compile
ghdl -c src/core_fsm/rtl/core_fsm.vhd src/core_fsm/tb/tb_core_fsm.vhd
;; Run without 'running and display tree (similar to vhier)
;; See how to process it and show it with hierarchy
ghdl -r tb_core_fsm --no-run --disp-tree=inst
