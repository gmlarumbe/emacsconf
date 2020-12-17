;;; init-package.el --- Package Init settings  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:


;;; Package management setup for use-package
(require 'package)
(setq package-enable-at-startup nil)
(add-to-list 'package-archives '("melpa"        . "http://melpa.org/packages/"))
(add-to-list 'package-archives '("melpa-stable" . "http://stable.melpa.org/packages/"))
(add-to-list 'package-archives '("gnu"          . "http://elpa.gnu.org/packages/"))
(package-initialize)

(unless (package-installed-p 'use-package)
  (package-refresh-contents)
  (package-install 'use-package))

;; use-package.el is no longer needed at runtime
;; This means you should put the following at the top of your Emacs, to further reduce load time:
(eval-when-compile
  (require 'use-package))
(setq use-package-always-ensure t) ; Force download if not available.
(setq use-package-always-defer t)  ; Force deferring of every package for proper loading after `load-path' updating
;; INFO: For local packages, set:
;;  :ensure nil - to avoid downloading the package. If deferred, rely on load-path set properly, otherwise :demand it.


(use-package auto-package-update
  :config
  (setq auto-package-update-delete-old-versions t)
  (setq auto-package-update-hide-results t)
  (auto-package-update-maybe))

(use-package gnu-elpa-keyring-update)    ; Update elpa keys to avoid signature issues
(use-package quelpa-use-package :demand) ; Allow for :quelpa keyword with `use-package'


(provide 'init-package)

;;; init-package.el ends here
