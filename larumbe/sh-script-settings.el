;;; sh-script-settings.el --- Shell Script  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

(use-package sh-script
  :ensure nil
  :bind (:map sh-mode-map
              ("C-c C-j" . sh-switch-to-process-buffer)
              ("C-c C-k" . sh-send-line-or-region-and-step)
              ("C-c C-p" . larumbe/sh-send-line-or-region-and-step-ansi)
              ("C-c C-t" . hydra-sh-template/body))
  :hook ((sh-mode . my-sh-mode-hook))
  :config
  (defun my-sh-mode-hook ()
    (set 'ac-sources '(ac-source-gtags ac-source-symbols)))

  (defhydra hydra-sh-template (:color blue :hint nil) "
for si_m_ple           _i_f            _p_rintf            _a_rgs
fo_r_ c-style          if-e_l_se       printf _d_ebug      _b_ang
_u_ntil                _c_ase          _e_cho              safe ba_n_g
_w_hile                _f_unction
while inde_x_ed        _+_ add
^^                     _s_elect
^^
^^
^^
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

  (defun larumbe/sh-send-line-or-region-and-step-ansi ()
    "Same as `sh-send-line-or-region-and-step' but for *ansi-term* process"
    (interactive)
    (let (from to end)
      (if (use-region-p)
          (setq from (region-beginning)
                to (region-end)
                end to)
        (setq from (line-beginning-position)
              to (line-end-position)
              end (1+ to)))
      (comint-send-string (get-buffer-process "*ansi-term*")
                          (concat (buffer-substring-no-properties from to) "\n"))
      (goto-char end)))

  (defun sh-switch-to-process-buffer ()
    (interactive)
    (pop-to-buffer (process-buffer (get-process "shell")) t)))


(provide 'sh-script-settings)

;;; sh-script-settings.el ends here
