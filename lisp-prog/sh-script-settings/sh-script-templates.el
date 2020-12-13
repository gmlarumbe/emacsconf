;;; sh-script-templates.el --- Shell Script Templates  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(defhydra hydra-sh (:color blue :hint nil) "
for si_m_ple           _i_f            _p_rintf            _a_rgs
fo_r_ c-style          if-e_l_se       printf _d_ebug      _b_ang
_u_ntil                _c_ase          _e_cho              safe ba_n_g
_w_hile                _f_unction
while inde_x_ed        _+_ add
^^                     _s_elect
"
  ("r"   (larumbe/hydra-yasnippet "forc"))
  ("m"   (larumbe/hydra-yasnippet "for"))
  ("u"   (larumbe/hydra-yasnippet "until"))
  ("w"   (larumbe/hydra-yasnippet "while"))
  ("f"   (larumbe/hydra-yasnippet "f"))
  ("p"   (larumbe/hydra-yasnippet "pr"))
  ("e"   (larumbe/hydra-yasnippet "e"))
  ("d"   (larumbe/hydra-yasnippet "pd"))
  ("a"   (larumbe/hydra-yasnippet "args"))
  ("b"   (larumbe/hydra-yasnippet "!"))
  ("n"   (larumbe/hydra-yasnippet "s!"))
  ("x"   (sh-indexed-loop))
  ("i"   (larumbe/hydra-yasnippet "if"))
  ("l"   (sh-if)) ;;  if - elif - else
  ("c"   (sh-case))
  ("+"   (call-interactively #'sh-add))
  ("s"   (sh-select))
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))


(provide 'sh-script-templates)

;;; sh-script-templates.el ends here
