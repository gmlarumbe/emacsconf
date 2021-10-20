;;; init-ivy.el --- Ivy/Counsel/Swiper  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


(use-package ivy
  :diminish
  :bind (("C-x b" . ivy-switch-buffer))
  :config
  (setq ivy-use-virtual-buffers t)
  (setq enable-recursive-minibuffers t)
  (ivy-mode -1) ; Do not break compatibility with Helm
  (use-package ivy-hydra))


;; INFO: Gave it a try at 10/2021 but it seemed I still was in love with Helm
;; Left it here to be enabled conditionally via these 2 variables in case
;; some day i want to play around again.
(defvar larumbe/force-use-counsel nil "Override usage of Helm with Ivy/Counsel")
(defvar larumbe/force-use-swiper nil  "Override usage of Isearch with Swiper")


(when larumbe/force-use-swiper
  (use-package swiper
    :bind (("C-s" . swiper))
    :config
    ;; enable this if you want `swiper' to use it
    (setq search-default-mode #'char-fold-to-regexp)))


(when larumbe/force-use-counsel
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
           ("M-s o"   . ivy-occur))
    :bind (:map minibuffer-local-map
           ("C-r" . counsel-minibuffer-history))))



(provide 'init-ivy)

;;; init-ivy.el ends here
