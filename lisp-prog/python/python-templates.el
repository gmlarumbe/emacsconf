;;; python-templates.el --- Python Templates  -*- lexical-binding: t -*-
;;; Commentary:
;;; Code:

;;;; Hydra
(defhydra larumbe/python-hydra (:color blue
                                :hint nil)
  ("c"  (python-skeleton-class)  "class"  :column "Skel")
  ("d"  (python-skeleton-def)    "def")
  ("f"  (python-skeleton-for)    "for")
  ("i"  (python-skeleton-if)     "if")
  ("m"  (python-skeleton-import) "import")
  ("t"  (python-skeleton-try)    "try")
  ("w"  (python-skeleton-while)  "while")
  ;;;;;;;;;;
  ;; Exit ;;
  ;;;;;;;;;;
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue))


(provide 'python-templates)

;;; python-templates.el ends here
