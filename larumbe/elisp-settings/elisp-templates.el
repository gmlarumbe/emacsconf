;;; elisp-templates.el --- Elisp Templates  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(defhydra hydra-elisp (:color blue
                              :hint  nil)
  "
    EMACS LISP

_da_  : defalias        _lam_ : lambda           _rsf_ : re-search-forward          _s=_  : string=
_dc_  : defconst        _let_ : let              _rsb_ : re-search-backward         _tap_ : thing-at-point
_def_ : defun           _la_  : looking-at       _se_  : save-excursion             _up_  : use-package
_dv_  : defvar          _mc_  : mapc             _sf_  : search-forward             _ul_  : unless
_dl_  : dolist          _ms_  : message          _sb_  : search-backward            _wh_  : when
_er_  : error           _px_  : point-max        _sq_  : setq
_f_   : format          _pn_  : point-min        _ss_  : split-string
_is_  : insert          _rq_  : require          _sm_  : string-match
_ie_  : if-else
"
  ("da"  (larumbe/hydra-yasnippet "da"))  ; defalias
  ("dc"  (larumbe/hydra-yasnippet "dc"))  ; defconst
  ("def" (larumbe/hydra-yasnippet "def")) ; defun
  ("dv"  (larumbe/hydra-yasnippet "dv"))  ; defvar
  ("dl"  (larumbe/hydra-yasnippet "dl"))  ; dolist
  ("er"  (larumbe/hydra-yasnippet "er"))  ; error
  ("f"   (larumbe/hydra-yasnippet "f"))   ; format
  ("is"  (larumbe/hydra-yasnippet "is"))  ; insert
  ("ie"  (larumbe/hydra-yasnippet "ie"))  ; if-else
  ("lam" (larumbe/hydra-yasnippet "lam")) ; lambda
  ("let" (larumbe/hydra-yasnippet "let")) ; let
  ("la"  (larumbe/hydra-yasnippet "la"))  ; looking-at
  ("mc"  (larumbe/hydra-yasnippet "mc"))  ; mapc
  ("ms"  (larumbe/hydra-yasnippet "ms"))  ; message
  ("px"  (larumbe/hydra-yasnippet "px"))  ; point-max
  ("pn"  (larumbe/hydra-yasnippet "pn"))  ; point-min
  ("rq"  (larumbe/hydra-yasnippet "rq"))  ; require
  ("rsf" (larumbe/hydra-yasnippet "rsf")) ; re-search-forward
  ("rsb" (larumbe/hydra-yasnippet "rsb")) ; re-search-backward
  ("se"  (larumbe/hydra-yasnippet "se"))  ; save-excursion
  ("sf"  (larumbe/hydra-yasnippet "sf"))  ; search-forward
  ("sb"  (larumbe/hydra-yasnippet "sb"))  ; search-backward
  ("sq"  (larumbe/hydra-yasnippet "sq"))  ; setq
  ("ss"  (larumbe/hydra-yasnippet "ss"))  ; split-string
  ("sm"  (larumbe/hydra-yasnippet "sm"))  ; string-match
  ("s="  (larumbe/hydra-yasnippet "s="))  ; string=
  ("tap" (larumbe/hydra-yasnippet "tap")) ; thing-at-point
  ("up"  (larumbe/hydra-yasnippet "up"))  ; use-package
  ("ul"  (larumbe/hydra-yasnippet "ul"))  ; unless
  ("wh"  (larumbe/hydra-yasnippet "wh"))  ; when
  ;; quitting and stopping
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))
;; Thanks to Kaushal Modi



(defhydra hydra-edebug (:color amaranth
                               :hint  nil)
  "
    EDEBUG MODE
^^_<SPC>_ step             ^^_f_ forward sexp         _b_reakpoint set                previous _r_esult      _w_here                    ^^_d_ebug backtrace
^^_n_ext                   ^^goto _h_ere              _u_nset breakpoint              _e_val expression      bounce _p_oint             _q_ top level (_Q_ nonstop)
_g_o (_G_ nonstop)         ^^_I_nstrument callee      next _B_reakpoint               _E_val list            _v_iew outside             ^^_a_bort recursive edit
_t_race (_T_ fast)         step _i_n/_o_ut            _x_ conditional breakpoint      eval _l_ast sexp       toggle save _W_indows      ^^_S_top
_c_ontinue (_C_ fast)      ^^^^                       _X_ global breakpoint
"
  ("<SPC>" edebug-step-mode)
  ("n"     edebug-next-mode)
  ("g"     edebug-go-mode)
  ("G"     edebug-Go-nonstop-mode)
  ("t"     edebug-trace-mode)
  ("T"     edebug-Trace-fast-mode)
  ("c"     edebug-continue-mode)
  ("C"     edebug-Continue-fast-mode)

  ("f"     edebug-forward-sexp)
  ("h"     edebug-goto-here)
  ("I"     edebug-instrument-callee)
  ("i"     edebug-step-in)
  ("o"     edebug-step-out)

  ;; breakpoints
  ("b"     edebug-set-breakpoint)
  ("u"     edebug-unset-breakpoint)
  ("B"     edebug-next-breakpoint)
  ("x"     edebug-set-conditional-breakpoint)
  ("X"     edebug-set-global-break-condition)

  ;; evaluation
  ("r"     edebug-previous-result)
  ("e"     edebug-eval-expression)
  ("l"     edebug-eval-last-sexp)
  ("E"     edebug-visit-eval-list)

  ;; views
  ("w"     edebug-where)
  ("p"     edebug-bounce-point)
  ("v"     edebug-view-outside) ; maybe obsolete??
  ("P"     edebug-view-outside) ; same as v
  ("W"     edebug-toggle-save-windows)

  ("d"     edebug-backtrace)

  ;; quitting and stopping
  ("q"     top-level :color blue)
  ("Q"     edebug-top-level-nonstop :color blue)
  ("a"     abort-recursive-edit :color blue)
  ("S"     edebug-stop :color blue))



(provide 'elisp-templates)

;;; elisp-templates.el ends here
