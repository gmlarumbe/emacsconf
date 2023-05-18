;;; init-polymode.el --- Polymode Modes  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Repo: https://github.com/polymode/polymode
;;
;; Doc: https://polymode.github.io/defining-polymodes/
;;
;; INFO: There is always one host mode, but there could be one or more inner modes.

;; Basic info about Inner Modes:
;;
;;  - If there is only one inner mode, specified in advance, use `define-innermode' and :mode '<inner-mode-name>
;;
;;  - If there could be more than one inner mode, it needs to be detected on the fly and `define-auto-innermode'
;;  has to be used instead:
;;    1) Instead of :mode, the :mode-matcher keyword is used in this macro to detect the proper major mode
;;      - This :mode-matcher could be a regexp, (cons regexp match-num) or a function return a string with
;;        the name of the major mode of the chunk
;;
;;  - The key args :head-matcher and :tail-matcher seem always mandatory for both macros and have to be:
;;    1) A regular expression matching the beginning/end for the innermode
;;    2) A (cons regexp match-num)
;;    NOTE: This cannot be a function, or at least a tried with functions returning strings and point positions
;;    and it didn't work!
;;
;;; Code:


(use-package polymode
  :commands (larumbe/yaml-shell-toggle)
  :hook (poly-nxml-mode . larumbe/poly-nxml-mode-hook)
  :config
;;;; nXML + Perl
  (define-hostmode poly-nxml-hostmode
    :mode 'nxml-mode)

  (define-innermode poly-nxml-perl-innermode
    :mode 'perl-mode
    :head-matcher "%"
    :tail-matcher "\n"
    :head-mode 'host
    :tail-mode 'host)

  (define-polymode poly-nxml-mode
    :hostmode 'poly-nxml-hostmode
    :innermodes '(poly-nxml-perl-innermode))

  (defun larumbe/poly-nxml-mode-hook ()
    "nXML + Perl Hook."
    (interactive)
    (rng-validate-mode -1)) ; Do not parse Perl preprocessor headers in XML files


;;;; Conf + Perl
  (define-hostmode poly-conf-hostmode
    :mode 'conf-mode)

  (define-innermode poly-conf-perl-innermode
    :mode 'perl-mode
    :head-matcher "%"
    :tail-matcher "\n"
    :head-mode 'host
    :tail-mode 'host)

  (define-polymode poly-conf-perl-mode
    :hostmode 'poly-conf-hostmode
    :innermodes '(poly-conf-perl-innermode))


;;;; Conf + C
  (define-hostmode poly-conf-c-hostmode
    :mode 'conf-mode)

  (define-innermode poly-conf-c-innermode
    :mode 'c-mode
    :head-matcher (cons "\\(?1:\\)#\\(if\\|else\\|endif\\|elsif\\|include\\|ITERATE\\)" 1) ; Capture group 1 is a hack to also include the #(word) inside the C mode
    :tail-matcher "\n"
    :head-mode 'host
    :tail-mode 'host)

  (define-polymode poly-conf-c-mode
    :hostmode 'poly-conf-c-hostmode
    :innermodes '(poly-conf-c-innermode))

;;;; YAML + Shell
  ;; `poly-yaml-hostmode' already defined in polymode-base.el

  ;; INFO: tail-matcher requires some hacking in this case since there is no specific
  ;; regexp to match the end for `sh-mode'. Any YAML tag of the form "- name: " or "name:"
  ;; different than "shell:" is used to match the end of the shell code.
  (define-innermode poly-yaml-shell-innermode
    :mode 'sh-mode
    :head-matcher "^\s*-\s*shell\s*:\\(\s*|\s*\n\\)?"
    :tail-matcher (cons "^\s*-?\s*\\(?1:\\(?2:shell\\)\\|\\(?3:[_-a-zA-Z0-9]+\\)\\)\s*:" 3)
    :head-mode 'host
    :tail-mode 'host)

  (define-polymode poly-yaml-shell-mode
    :hostmode 'poly-yaml-hostmode
    :innermodes '(poly-yaml-shell-innermode))

  (defun larumbe/yaml-shell-toggle ()
    "Toggle between `yaml-mode' and `poly-yaml-shell-mode'"
    (interactive)
    (unless (or (string= major-mode "yaml-mode")
                poly-yaml-shell-mode)
      (error "Cannot call `larumbe/yaml-shell-toggle' in this major-mode!"))
    (if poly-yaml-shell-mode
        (progn
          (yaml-mode)
          (font-lock-fontify-buffer)
          (message "Switched to `yaml-mode'"))
      (poly-yaml-shell-mode 1)
      (font-lock-fontify-buffer)
      (message "Switched to `poly-yaml-shell-mode'"))))


(provide 'init-polymode)

;;; init-polymode.el ends here
