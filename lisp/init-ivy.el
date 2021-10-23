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
      (ivy-mode 1)
    (ivy-mode -1))
  ;; Dependencies
  (use-package ivy-hydra))


(when (equal larumbe/completion-framework 'ivy)
  (use-package ivy-youtube
    :bind (("C-x c y" . ivy-youtube)))

  (use-package swiper
    :bind (:map swiper-map
           ("C-r"   . swiper-isearch-C-r)
           ("C-w"   . ivy-yank-word)
           )
    :bind (("C-s"   . swiper)
           ("M-s ." . swiper-isearch-thing-at-point))
    :config
    ;; enable this if you want `swiper' to use it
    (setq search-default-mode #'case-fold-search)
    )


  ;; INFO: Gave it a try at 10/2021 but it seemed I still was in love with Helm
  (use-package counsel
    :bind (("M-x"     . counsel-M-x)
           ("C-x C-f" . counsel-find-file)
           ("C-x r b" . counsel-bookmark)
           ("M-g a"   . counsel-ag)
           ("M-g r"   . counsel-rg)
           ("M-I"     . counsel-imenu)
           ("C-x c /" . counsel-file-jump)
           ("C-x c p" . counsel-list-processes)
           ("C-#"     . counsel-outline)
           )))



(provide 'init-ivy)

;;; init-ivy.el ends here
