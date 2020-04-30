;; INFO: For a new config template, check: `exwm-config-default'
;;   /home/gonz/.emacs.d/elpa/exwm-0.22.1/exwm-config.el:26
;;
;; Fetched from:
;; https://github.com/ch11ng/exwm/wiki/Configuration-Example

;;; Larumbe's summary
;;  Precedence's hierarchy from top to bottom would be the following:
;;
;;  - Global keybindings: aka `exwm-input-set-key' affects char and line mode buffers (text and *EXWM*)
;;  - (`global-set-key') would only affect text buffers
;;  - Local keybindings: aka `exwm-input-prefix-keys' frees keys used in line-mode EXWM buffers (would be the same as in text bufers)
;;  - Simulation keys: aka `exwm-input-set-simulation-keys' are sent to line-mode EXWM buffers and remap keys.
;;
;;    - Therefore, an EXWM buffer in `char-mode' would only respond to keys in `exwm-input-set-key'.
;;
;;    - An EWWM buffer in `line-mode' would only respond to keys that are NOT in `exwm-input-prefix-keys'
;;      and would change the ones included in `exwm-input-set-simulation-keys'


;;; Basic config
;; Load EXWM
(use-package exwm)
(require 'exwm-config)

;; Set the initial number of workspaces.
(setq exwm-workspace-number 2)


;;; Buffer naming
;; All buffers created in EXWM mode are named "*EXWM*". You may want to change
;; it in `exwm-update-class-hook' and `exwm-update-title-hook', which are run
;; when a new window class name or title is available. Here's some advice on
;; this subject:
;; + Always use `exwm-workspace-rename-buffer` to avoid naming conflict.
;; + Only renaming buffer in one hook and avoid it in the other. There's no
;;   guarantee on the order in which they are run.
;; + For applications with multiple windows (e.g. GIMP), the class names of all
;;   windows are probably the same. Using window titles for them makes more
;;   sense.
;; + Some application change its title frequently (e.g. browser, terminal).
;;   Its class name may be more suitable for such case.
;; In the following example, we use class names for all windows expect for
;; Java applications and GIMP.
(add-hook 'exwm-update-class-hook
          (lambda ()
            (unless (or (string-prefix-p "sun-awt-X11-" exwm-instance-name)
                        (string= "gimp" exwm-instance-name))
              (exwm-workspace-rename-buffer exwm-class-name))))
(add-hook 'exwm-update-title-hook
          (lambda ()
            (when (or (not exwm-instance-name)
                      (string-prefix-p "sun-awt-X11-" exwm-instance-name)
                      (string= "gimp" exwm-instance-name))
              (exwm-workspace-rename-buffer exwm-title))))


;;; Global KeyBindings
;; `exwm-input-set-key' allows you to set a global key binding (available in
;; any case). Following are a few examples.
;; + We always need a way to go back to line-mode from char-mode
(exwm-input-set-key (kbd "s-r") #'exwm-reset)
;; + Bind a key to switch workspace interactively
(exwm-input-set-key (kbd "s-w") #'exwm-workspace-switch)
;; + Bind "s-0" to "s-9" to switch to the corresponding workspace.
(dotimes (i 10)
  (exwm-input-set-key (kbd (format "s-%d" i))
                      `(lambda ()
                         (interactive)
                         (exwm-workspace-switch-create ,i))))
;; + Application launcher ('M-&' also works if the output buffer does not
;;   bother you). Note that there is no need for processes to be created by
;;   Emacs.
(exwm-input-set-key (kbd "s-j")
                    (lambda (command)
                      (interactive (list (read-shell-command "$ ")))
                      (start-process-shell-command command nil command)))

;; + 'slock' is a simple X display locker provided by suckless tools.
(exwm-input-set-key (kbd "s-<f2>")
                    (lambda () (interactive) (start-process "" nil "slock")))

;; Shortcuts created by Larumbe for convenience
;; Firefox Shortcut
(exwm-input-set-key (kbd "s-k")
                    (lambda ()
                      (interactive)
                      (start-process-shell-command "" nil "firefox")))



;;;; Window/Frame movement/navigation
(defvar larumbe/shrink-window-horizontally-delta   15)
(defvar larumbe/shrink-window-vertically-delta      5)

(exwm-input-set-key (kbd "C-}")   #'larumbe/shrink-window-horizontally)
(exwm-input-set-key (kbd "C-{")   #'larumbe/enlarge-window-horizontally)
(exwm-input-set-key (kbd "C-M-{") #'larumbe/shrink-window-vertically)
(exwm-input-set-key (kbd "C-M-}") #'larumbe/enlarge-window-vertically)

(exwm-input-set-key (kbd "M-o")   #'other-window) ; Suggested by Mastering-Emacs author (Replaces Enriched faces: https://www.gnu.org/software/emacs/manual/html_node/emacs/Enriched-Faces.html)
(exwm-input-set-key (kbd "M-O")   #'other-frame)  ; replaces 'negative-argument
(exwm-input-set-key (kbd "M-'")   #'larumbe/kill-current-buffer)


;;;; Line-mode global keybindings
;;;;; Text Editing
(global-set-key (kbd "C-M-<up>") #'move-lines-up)
(global-set-key (kbd "C-M-<down>") #'move-lines-down)
(global-set-key (kbd "C-x d") #'duplicate-line) ; Replaces Dired (C-x C-j works better)
(global-set-key (kbd "C-w") #'whole-line-or-region-kill-region)
(global-set-key (kbd "M-w") #'larumbe/copy-region-or-symbol-at-point) ; Overrides `kill-ring-save'
(global-set-key (kbd "C-M-<backspace>") #'xah-delete-backward-char-or-bracket-text)

(global-set-key (kbd "<C-return>") #'completion-at-point)
(global-set-key (kbd "<S-return>") #'auto-complete)
(global-set-key (kbd "<C-M-return>") #'yas-expand)          ; Outline-minor mode replaces this yas keybinding
(global-set-key [remap dabbrev-expand] #'hippie-expand)

(global-set-key (kbd "C-\\")  #'highlight-symbol-at-point)
(global-set-key (kbd "C-'")  #'unhighlight-regexp)

(global-set-key (kbd "C-<f12>") #'auto-fill-mode)           ;  Auto-fill mode
(global-set-key [f12] #'toggle-truncate-lines)              ;  Truncate lines


;;;;; Navigation
(global-set-key (kbd "M-x") #'helm-M-x)
(global-set-key (kbd "C-x C-f") #'helm-find-files)
(global-set-key (kbd "C-x r b") #'helm-filtered-bookmarks)
;; IDO mode compatibility with Helm:
;;    - To do so, M-x customize-group RET helm-mode RET and then:
;;    - Check Helm Completing Read Handlers Alist:
;;    - Find all the 'ido' occurences (now are set to switch-to-buffer and find-alternate-file)

(global-set-key (kbd "M-s o") #'helm-occur)
(global-set-key (kbd "M-g a") #'helm-do-grep-ag) ; Avoid `C-x c' prefix
(global-set-key (kbd "C-#")  #'helm-navi-headings)
(global-set-key (kbd "M-#")  #'helm-navi)
(global-set-key (kbd "C-x C-j") #'dired-jump)

(global-set-key (kbd "M-I") #'helm-imenu)
(global-set-key (kbd "M-i") #'imenu-list)

(global-set-key (kbd "C-z") #'larumbe/pop-to-previous-mark) ; Unmaps suspending frame
(global-set-key (kbd "C-x C-z") #'larumbe/pop-to-previous-mark) ; Unmaps suspending frame

(global-set-key (kbd "C-x C-/") #'larumbe/pwd-to-kill-ring)
(global-set-key (kbd "C-x C-,") #'revert-buffer) ; Bind to `larumbe/revert-buffer-no-confirm' to avoid asking


;;;;; Version Control
(global-set-key (kbd "C-x g") #'magit-status)
(global-set-key (kbd "C-x M-g") #'magit-dispatch)
(global-set-key (kbd "C-x j") '(lambda ()
                                 (interactive)
                                 (svn-status default-directory)
                                 (setq truncate-lines t))) ; Setting a hook for `svn-status-mode' did not seem to work
(global-set-key (kbd "C-x t") #'larumbe/repohome-magit-status)
(global-set-key (kbd "C-x y") #'larumbe/repohome-reset-git-args)


;;;;; Compilation
;; M-n and M-p are already overwritten at mode-line.el. This mapping allows to step through errors in a non-compilation buffer
(global-set-key (kbd "M-n") #'next-error)
(global-set-key (kbd "M-p") #'previous-error)
(global-set-key [f5] #'compile)
(global-set-key (kbd "C-*") #'show-custom-compilation-buffers)


;;;;; Misc
(global-set-key (kbd "C-,") #'larumbe/ansi-term)
(global-set-key (kbd "C-.") '(lambda ()
                               (interactive)
                               (ansi-term "/bin/bash")))
(global-set-key (kbd "<print>")  #'screenshot-take)
(global-set-key (kbd "C-x C-h") #'larumbe/helm-help-major-mode)
(global-set-key (kbd "C-x l") #'larumbe/org-show-todos-agenda)
(global-set-key (kbd "C-c / y") #'helm-youtube)             ; Analogous to google-this mode keybindings



;;; Local KeyBindings
;; The following example demonstrates how to set a key binding only available
;; in line mode. It's simply done by first push the prefix key to
;; `exwm-input-prefix-keys' and then add the key sequence to `exwm-mode-map'.
;; The example shorten 'C-c q' to 'C-q'.
(push ?\C-q exwm-input-prefix-keys)
(define-key exwm-mode-map [?\C-q] #'exwm-input-send-next-key)
;; Avoids use of following keys inside an  *EXWM* buffer in line-mode
;; Macro defining
(push 'f3 exwm-input-prefix-keys)
(push 'f4 exwm-input-prefix-keys)
;; Ansi-term
(push '?\C-, exwm-input-prefix-keys)
(push '?\C-. exwm-input-prefix-keys)
;; Screenshot
(push '\print exwm-input-prefix-keys)
;; Various functions (copy sim from cee)
(push 'f9 exwm-input-prefix-keys)


;;; Common Simulation Key-Bindings
;; The following example demonstrates how to use simulation keys to mimic the
;; behavior of Emacs. The argument to `exwm-input-set-simulation-keys' is a
;; list of cons cells (SRC . DEST), where SRC is the key sequence you press and
;; DEST is what EXWM actually sends to application. Note that SRC must be a key
;; sequence (of type vector or string), while DEST can also be a single key.
(exwm-input-set-simulation-keys
 '(
   ;; Own keys
    ([?\C-g] . escape)
    ;; movement
    ([?\C-b] . left)
    ([?\M-b] . C-left)
    ([?\C-f] . right)
    ([?\M-f] . C-right)
    ([?\C-p] . up)
    ([?\C-n] . down)
    ([?\M-<] . home)
    ([?\M->] . end)
    ([?\C-a] . home)
    ([?\C-e] . end)
    ([?\M-v] . prior)
    ([?\C-v] . next)
    ([?\C-d] . delete)
    ([?\C-k] . (S-end delete))
    ;; cut/paste.
    ;; ([?\C-w] . ?\C-x)
    ([?\M-w] . ?\C-c)
    ([?\C-y] . ?\C-v)
    ;; search
    ([?\C-s] . ?\C-f)
    ))


;;; Firefox Local Key-Bindings
;; Local Key-bindings
;; (add-hook 'exwm-manage-finish-hook
;;           (lambda ()
;;             (when (and exwm-class-name
;;                        (string= exwm-class-name "firefox"))
;;               ;; (setq-local exwm-input-prefix-keys '(?\C-c))
;;                  )))
;; Simulation keys
(add-hook 'exwm-manage-finish-hook
          (lambda ()
            (when (and exwm-class-name
                       (string= exwm-class-name "Firefox"))
              (exwm-input-set-local-simulation-keys
               '(
                 ;; Own keys
                 ([?\C-g] . escape)
                 ;; movement
                 ([?\C-b] . left)
                 ([?\M-b] . C-left)
                 ([?\C-f] . right)
                 ([?\M-f] . C-right)
                 ([?\C-p] . up)
                 ([?\C-n] . down)
                 ([?\M-<] . home)
                 ([?\M->] . end)
                 ([?\C-a] . home)
                 ([?\C-e] . end)
                 ([?\M-v] . prior)
                 ([?\C-v] . next)
                 ([?\C-d] . delete)
                 ([?\C-k] . (S-end ?\C-x)) ; It kills, not simply deletes
                 ;; cut/paste.
                 ;; ([?\C-w] . ?\C-x)
                 ([?\M-w] . ?\C-c)
                 ([?\C-y] . ?\C-v)
                 ;; search
                 ([?\C-\M-s] . ?\C-F)      ; Find
                 ([?\C-\M-r] . ?\C-F)      ; Find
                 ([?\C-s]    . ?\C-G)      ; Find Next (forward search)
                 ([?\C-r]    . (S-f3))     ; Find Previous (backwards search)
                 ;; TABs navigation
                 ([?\C-\M-l] . (C-next))   ;
                 ([?\C-\M-h] . (C-prior))  ;
                 ;; Deleting words
                 ([?\M-d] . (S-C-right delete))
                 ;; ([?\M-\d] . (S-C-left delete))  ;; INFO: Could no make it work (not even with binary value, with backspace, with delete...): Note (http://ergoemacs.org/emacs/keystroke_rep.html)
                 ;; Key-Scripting -> With '-' and between parenthesis they will be pressed in that order "simultaneously"
                 ([?\C-j]  . tab)
                 ([?\C-\;] . (S-tab))
                 )))))



;;; Okular Local Key-Bindings
;; Local Key-bindings
;; (add-hook 'exwm-manage-finish-hook
;;           (lambda ()
;;             (when (and exwm-class-name
;;                        (string= exwm-class-name "Okular"))
;;               ;; (setq-local exwm-input-prefix-keys '(?\C-c))
;;                  )))
;; Simulation keys
(add-hook 'exwm-manage-finish-hook
          (lambda ()
            (when (and exwm-class-name
                       (or
                        (string= exwm-class-name "Okular") ; DebianVM
                        (string= exwm-class-name "okular") ; Kali
                        ))
              (exwm-input-set-local-simulation-keys
               '(
                 ([?\C-g] . escape)
                 ;; movement
                 ([?\C-b] . left)
                 ([?\M-b] . C-left)
                 ([?\C-f] . right)
                 ([?\M-f] . C-right)
                 ([?\C-p] . up)
                 ([?\C-n] . down)
                 ([?\M-<] . home)
                 ([?\M->] . end)
                 ;; ([?\C-a] . home)
                 ;; ([?\C-e] . end)
                 ([?\M-v] . prior)
                 ([?\C-v] . next)
                 ([?\C-d] . delete)
                 ([?\C-k] . (S-end delete))
                 ;; cut/paste.
                 ([?\C-w] . ?\C-x)
                 ([?\M-w] . ?\C-c)
                 ([?\C-y] . ?\C-v)
                 ;; search (manually assigned at Okular)
                 ([?\C-s] . ?\C-')      ; Forward
                 ([?\C-r] . ?\C-\\)      ; Backward
                 )))))



;;; Vivado Local Key-Bindings
;; Local Key-bindings
;; (add-hook 'exwm-manage-finish-hook
;;           (lambda ()
;;             (when (and exwm-class-name
;;                        (string= exwm-class-name "Vivado"))
;;               ;; (setq-local exwm-input-prefix-keys '(?\C-c))
;;                  )))
;; Simulation keys
(add-hook 'exwm-manage-finish-hook
          (lambda ()
            (when (and exwm-class-name
                       (string= exwm-class-name "Vivado"))
              (exwm-input-set-local-simulation-keys
               '(
                 ;; movement
                 ([?\C-b] . left)
                 ([?\M-b] . C-left)
                 ([?\C-f] . right)
                 ([?\M-f] . C-right)
                 ([?\C-p] . up)
                 ([?\C-n] . down)
                 ([?\C-a] . home)
                 ([?\C-e] . end)
                 ([?\M-v] . prior)
                 ([?\C-v] . next)
                 ([?\C-d] . delete)
                 ([?\C-k] . (S-end delete))
                 ;; cut/paste.
                 ([?\C-w] . ?\C-x)
                 ([?\M-w] . ?\C-c)
                 ([?\C-y] . ?\C-v)
                 ;; ([?\C-s] . ?\C-f)      ; Forward -> Avoid it since C-s should be better saving than searching (use C-r instead)
                 ([?\C-r] . ?\C-f)      ; Backward
                 ;; Undo
                 ([?\C-\/] . ?\C-z)
                 )))))



;;; Gtkwave Local Key-Bindings
;; ;; Local Key-bindings
;; (add-hook 'exwm-manage-finish-hook
;;           (lambda ()
;;             (when (and exwm-class-name
;;                        (string= exwm-class-name "Gtkwave"))
;;               ;; (setq-local exwm-input-prefix-keys '(?\C-c))
;;                  )))
;; Simulation keys
(add-hook 'exwm-manage-finish-hook
          (lambda ()
            (when (and exwm-class-name
                       (string= exwm-class-name "Gtkwave"))
              (exwm-input-set-local-simulation-keys
               '(
                 ;; Own keys
                 ([?\C-g] . escape)
                 ;; movement
                 ([?\C-b] . left)
                 ([?\M-b] . C-left)
                 ([?\C-f] . right)
                 ([?\M-f] . C-right)
                 ([?\C-p] . up)
                 ([?\C-n] . down)
                 ([?\M-<] . home)
                 ([?\M->] . end)
                 ([?\C-a] . home)
                 ([?\C-e] . end)
                 ([?\M-v] . prior)
                 ([?\C-v] . next)
                 ([?\C-d] . delete)
                 ;; ([?\C-k] . (S-end ?\C-x)) ; It kills, not simply deletes
                 ;; cut/paste.
                 ;; ([?\C-w] . ?\C-x)
                 ([?\M-w] . ?\C-c)
                 ([?\C-y] . ?\C-v)
                 ;; search
                 ;; ([?\C-\M-s] . ?\C-F)      ; Find
                 ;; ([?\C-\M-r] . ?\C-F)      ; Find
                 ;; ([?\C-s]    . ?\C-G)      ; Find Next (forward search)
                 ;; ([?\C-r]    . (S-f3))     ; Find Previous (backwards search)
                 )))))



;;; Novas Local Key-Bindings
;; ;; Local Key-bindings
;; (add-hook 'exwm-manage-finish-hook
;;           (lambda ()
;;             (when (and exwm-class-name
;;                        (string= exwm-class-name "Novas"))
;;               ;; (setq-local exwm-input-prefix-keys '(?\C-c))
;;                  )))
;; Simulation keys
(add-hook 'exwm-manage-finish-hook
          (lambda ()
            (when (and exwm-class-name
                       (string= exwm-class-name "Novas"))
              (exwm-input-set-local-simulation-keys
               '(
                 ;; Own keys
                 ([?\C-g] . escape)
                 ;; movement
                 ([?\C-b] . left)
                 ([?\M-b] . C-left)
                 ([?\C-f] . right)
                 ([?\M-f] . C-right)
                 ([?\C-p] . up)
                 ([?\C-n] . down)
                 ([?\M-<] . home)
                 ([?\M->] . end)
                 ([?\C-a] . home)
                 ([?\C-e] . end)
                 ([?\M-v] . prior)
                 ([?\C-v] . next)
                 ([?\C-d] . delete)
                 ;; ([?\C-k] . (S-end ?\C-x)) ; It kills, not simply deletes
                 ;; cut/paste.
                 ;; ([?\C-w] . ?\C-x)
                 ([?\M-w] . ?\C-c)
                 ([?\C-y] . ?\C-v)
                 ;; search
                 ;; ([?\C-\M-s] . ?\C-F)      ; Find
                 ;; ([?\C-\M-r] . ?\C-F)      ; Find
                 ;; ([?\C-s]    . ?\C-G)      ; Find Next (forward search)
                 ;; ([?\C-r]    . (S-f3))     ; Find Previous (backwards search)
                 )))))



;;; Other Options
;; You can hide the minibuffer and echo area when they're not used, by
;; uncommenting the following line
;; (setq exwm-workspace-minibuffer-position 'bottom)

;; You can hide the mode-line of floating X windows by uncommenting the
;; following lines
;; (add-hook 'exwm-floating-setup-hook #'exwm-layout-hide-mode-line)
;; (add-hook 'exwm-floating-exit-hook #'exwm-layout-show-mode-line)


;;; Unused features
;; Compositing manager
;; (require 'exwm-cm)
;; Make all Emacs frames opaque.
;; (setq window-system-default-frame-alist '((x . ((alpha . 100)))))
;; Assign everything else a 80% opacity.
;; (setq exwm-cm-opacity 80)
;; (exwm-cm-enable)

;; System tray
;; (require 'exwm-systemtray)
;; (exwm-systemtray-enable)


;;; Workspace/Layout settings
;; Note: EXWM only shows X windows belonging to the current workspace by default.
;; You may alter this behavior by assigning exwm-workspace-show-all-buffers a non-nil value.
(setq exwm-workspace-show-all-buffers t)
;; Also, you might want to set exwm-layout-show-all-buffers to t to allow automatically moving X
;; windows from inactive workspaces by switching to their associated buffers.
(setq exwm-layout-show-all-buffers t)
