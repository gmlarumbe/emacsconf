;;; init-ivy.el --- Ivy/Counsel/Swiper  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package ivy
  :diminish
  :bind (("C-x b" . ivy-switch-buffer)
         ("M-s o" . ivy-occur))
  :config
  (setq ivy-use-virtual-buffers t)      ; Add recent files and bookmarks to the ivy-switch-buffer
  ;; (setq ivy-count-format "%d/%d ")      ; Displays the current and total number in the collection in the prompt
  (setq enable-recursive-minibuffers t) ; Allow minibuffer commands while in the minibuffer.
  ;; Do not break compatibility with Helm for switching buffers
  (if (equal larumbe/completion-framework 'ivy)
      (progn
        (ivy-mode 1)
        (use-package ivy-rich
          :demand
          :config
          (ivy-rich-mode 1)))
    ;; Else (using helm)
    (ivy-mode -1))

  ;; (setq ivy-extra-directories nil)

  ;; https://github.com/abo-abo/swiper/issues/1068
  (defun ivy-with-thing-at-point (cmd)
    (let ((ivy-initial-inputs-alist
           (list
            (cons cmd (thing-at-point 'symbol)))))
      (funcall cmd)))

  (defun ivy-with-thing-at-point-search-symbol (cmd)
    (let ((ivy-initial-inputs-alist
           (list
            (cons cmd (concat "\\_<" (thing-at-point 'symbol) "\\_>")))))
      (funcall cmd)))

  ;; Swiper multiple cursors
  (add-to-list 'mc/cmds-to-run-once 'swiper-mc)

  ;; Dependencies
  (use-package ivy-hydra))





(when (equal larumbe/completion-framework 'ivy)
  (use-package swiper
    :bind (:map swiper-map
           ("C-r"   . swiper-isearch-C-r)
           ("C-w"   . ivy-yank-word)
           )
    :bind (("C-s"   . swiper)
           ("M-s ." . swiper-symbol-at-point))
    :config
    ;; enable this if you want `swiper' to use it
    (setq search-default-mode #'case-fold-search)

    (defun swiper-symbol-at-point ()
      (interactive)
      (if (thing-at-point 'symbol)
          (ivy-with-thing-at-point-search-symbol 'swiper)
        (call-interactively #'swiper))))


  (use-package counsel
    :bind (("M-x"     . counsel-M-x)
           ("C-x C-f" . counsel-find-file)
           ("C-x r b" . counsel-bookmark)
           ;; ("M-g a"   . counsel-ag)
           ("M-g a"   . counsel-ag-thing-at-point)
           ;; ("M-g r"   . counsel-rg)
           ("M-g r"   . counsel-rg-thing-at-point)
           ("M-I"     . counsel-imenu)
           ("C-x c /" . counsel-file-jump)
           ("C-x c p" . counsel-list-processes)
           ("C-#"     . counsel-outline)
           ;;  ; Emulate Helm, TODO: Do it at counsel map, not global
           )
    :bind (:map counsel-find-file-map
           ("C-l" . counsel-up-directory))
    :config
    (defun counsel-ag-thing-at-point ()
      (interactive)
      (ivy-with-thing-at-point 'counsel-ag))

    (defun counsel-rg-thing-at-point ()
      (interactive)
      (ivy-with-thing-at-point 'counsel-rg))
    )

  (use-package ivy-youtube
    :bind (("C-x c y" . ivy-youtube))))



(provide 'init-ivy)

;;; init-ivy.el ends here
