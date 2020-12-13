;;; docbook-mode.el --- Docbook Mode  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Basic Larumbe's minor mode for XML Docbook editing
;;
;; INFO: It seems there are already some Docbook modes...
;;  Check them and verify how this glues with the rest.
;;
;;; Code:

;;; Description

(defvar larumbe/docbook-xsl-program "xsltproc")
(defvar larumbe/docbook-fo-program "fop")


(define-derived-mode docbook-mode nxml-mode "Docbook"
  "Docbook minor mode."
  (define-key docbook-mode-map (kbd "C-c C-p") #'larumbe/docbook-to-pdf-current-buffer)
  (define-key docbook-mode-map (kbd "C-c C-t") #'hydra-nxml-docbook-template/body))


;; https://stackoverflow.com/questions/2615002/how-to-generate-pdf-from-docbook-5-0/2651158
(defun larumbe/docbook-to-pdf ()
  "Render XML Docbook file to PDF"
  (interactive)
  (let (xml-file pdf-out fo-file cmd)
    (setq xml-file (read-file-name "Docbook file: "))
    (if (string-equal (file-name-extension xml-file) "xml") ; File must be a xml
        (progn
          (setq pdf-out (concat (file-name-sans-extension (file-name-nondirectory xml-file)) ".pdf"))
          (setq fo-file (concat (file-name-sans-extension (file-name-nondirectory xml-file)) ".fo"))
          (setq cmd
                (concat
                 larumbe/docbook-xsl-program " "
                 "-xinclude "
                 larumbe/docbook-xsl-stylesheet " "
                 xml-file " > " fo-file " "
                 "&& "
                 larumbe/docbook-fo-program " -fo " fo-file " -pdf " pdf-out))
          (shell-command "ln -s images/* .") ;; Create symlinks to all images to get them rendered (assumed to be contained within a 'images' folder)
          (shell-command cmd "*Docbook2PDF*")
          (shell-command "find . -lname 'images/*' -delete") ;; Remove all the symbolic links to images once file has been rendered to PDF
          )
      (message "File isn't .xml!!"))))


(defun larumbe/docbook-to-pdf-current-buffer (&optional no-preview)
  "Render current buffer XML Docbook file to PDF.
If Universal Argument is provided, then do not preview file"
  (interactive "P")
  (let (xml-file pdf-out fo-file cmd docbuf-pdf docbuf-okular)
    (setq docbuf-pdf "*Docbook2PDF*")
    (setq docbuf-okular "*DocbookOkular*")
    (setq xml-file (file-name-nondirectory buffer-file-name))
    (if (string-equal (file-name-extension xml-file) "xml") ; File must be a xml
        (progn
          (setq pdf-out (concat (file-name-sans-extension (file-name-nondirectory xml-file)) ".pdf"))
          (setq fo-file (concat (file-name-sans-extension (file-name-nondirectory xml-file)) ".fo"))
          (setq cmd
                (concat
                 larumbe/docbook-xsl-program " "
                 "-xinclude "
                 larumbe/docbook-xsl-stylesheet " "
                 xml-file " > " fo-file " "
                 "&& "
                 larumbe/docbook-fo-program " -fo " fo-file " -pdf " pdf-out))
          (message (concat "Rendering " xml-file "..."))
          (shell-command "ln -sf images/* .") ;; Create symlinks to all images to get them rendered (assumed to be contained within a 'images' folder)
          (shell-command cmd docbuf-pdf)
          (shell-command (concat "rm " fo-file))
          (shell-command "find . -lname 'images/*' -delete") ;; Remove all the symbolic links to images once file has been rendered to PDF
          (unless no-preview
            (start-process-shell-command docbuf-okular docbuf-okular (concat "okular " pdf-out))))
      (message "File isn't .xml!!"))))


(defun larumbe/nxml-docbook-bold-region ()
  "Get region bold"
  (interactive)
  (let (beg end)
    (if (use-region-p)
        (progn
          (setq beg (region-beginning))
          (setq end (region-end))
          (save-excursion
            (goto-char end)
            (insert "</emphasis>"))
          (goto-char beg)
          (insert "<emphasis role=\"bold\">"))
      (message "No region selected motherfucker!"))))


(defun larumbe/nxml-docbook-italic-region ()
  "Get region bold"
  (interactive)
  (let (beg end)
    (if (use-region-p)
        (progn
          (setq beg (region-beginning))
          (setq end (region-end))
          (save-excursion
            (goto-char end)
            (insert "</emphasis>"))
          (goto-char beg)
          (insert "<emphasis role=\"italic\">"))
      (message "No region selected motherfucker!"))))


(defhydra hydra-nxml-docbook-template (:color blue
                                              :hint nil)
  "
_p_aragraph     _b_old           itemized_L_ist   _r_egisters
_s_ection       _i_talic         _l_istitem
_t_itle         _B_oldRegion
_c_hapter       _I_talicRegion
"
  ;; ("p"   (larumbe/hydra-yasnippet "para")) ; Leaves a line between tag and text
  ("p"   (larumbe/hydra-yasnippet "parahp")) ; Right after the tag
  ("s"   (larumbe/hydra-yasnippet "section"))
  ("t"   (larumbe/hydra-yasnippet "title"))
  ("c"   (larumbe/hydra-yasnippet "chapter"))
  ("b"   (larumbe/hydra-yasnippet "bold"))
  ("i"   (larumbe/hydra-yasnippet "italic"))
  ("B"   (larumbe/nxml-docbook-bold-region))
  ("I"   (larumbe/nxml-docbook-italic-region))
  ("r"   (larumbe/hydra-yasnippet "registers"))
  ("L"   (larumbe/hydra-yasnippet "itemizedlist"))
  ("l"   (larumbe/hydra-yasnippet "listitem"))
  ("q"   nil nil :color blue)
  ("C-g" nil nil :color blue)
  )


(provide 'docbook-mode)


(provide 'docbook-mode)

;;; docbook-mode.el ends here
