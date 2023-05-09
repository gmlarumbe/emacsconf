;;; init-exwm.el --- EXWM  -*- lexical-binding: t -*-
;;; Commentary:
;; INFO: For a new config template, check: `exwm-config-default'
;;   ~/.emacs.d/elpa/exwm-0.24/exwm-config.el:26
;;
;; Fetched from:
;; https://github.com/ch11ng/exwm/wiki/Configuration-Example
;;
;;;; Larumbe's summary
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
;;
;;
;;;; Buffer naming
;; All buffers created in EXWM mode are named "*EXWM*".  You may want to change
;; it in `exwm-update-class-hook' and `exwm-update-title-hook', which are run
;; when a new window class name or title is available.  Here's some advice on
;; this subject:
;; + Always use `exwm-workspace-rename-buffer` to avoid naming conflict.
;; + Only renaming buffer in one hook and avoid it in the other.  There's no
;;   guarantee on the order in which they are run.
;; + For applications with multiple windows (e.g.  GIMP), the class names of all
;;   windows are probably the same.  Using window titles for them makes more
;;   sense.
;; + Some application change its title frequently (e.g.  browser, terminal).
;;   Its class name may be more suitable for such case.
;;
;;  Check `larumbe/exwm-set-buffer-naming' example
;;
;;;; Some combinations not-used anymore
;;
;; ([?\C-\;] . (S-tab))

;;; Code:


(use-package exwm
  :demand)


;;;; Variables
;;;;; Common
;; Avoids use of following keys inside an  *EXWM* buffer in line-mode
(defvar larumbe/exwm-common-input-prefix-keys
  '(?\C-q  ; Free `exwm-input-send-next-key'
    f3    ; Macro defining
    f4
    ?\C-, ; Ansi-term
    ?\C-.
    (kbd "C-;") ; `switch-to-buffer'
    f9))  ; Other various functions


(defvar larumbe/exwm-common-input-simulation-keys
  '(([?\C-g] . escape)
    ([?\C-m] . return)
    ([?\C-j] . return)
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
    ([?\C-w] . ?\C-x)
    ([?\M-w] . ?\C-c)
    ([?\C-y] . ?\C-v)
    ;; search
    ([?\C-s] . ?\C-f)))

;;;;; Programs
;; Structure of this extensible variable:
;; Association list, cars are the name of the program and cdrs are a list with the following elements:
;;  1) EXWM class names: name given to the EXWM buffer. Needed to assign the sim keys to the proper buffer
;;  2) Prefix keys
;;  3) Simulation keys
(defvar larumbe/exwm-programs
  '(("Firefox" .
     (("Firefox" "firefox" "Firefox-esr" "Tor Browser")
      (f8 f7)
      (([?\C-w]     . ?\C-w)         ; Keep value for window closing
       ([?\C-k]     . (S-end ?\C-x)) ; It kills, not simply deletes
       ;; search
       ([?\C-\M-s]  . ?\C-F)         ; Find
       ([?\C-\M-r]  . ?\C-F)         ; Find
       ([?\C-s]     . ?\C-G)         ; Find Next (forward search)
       ([?\C-r]     . (S-f3))        ; Find Previous (backwards search)
       ;; TABs navigation
       ([?\C-\M-l]  . (C-next))
       ([?\C-\M-h]  . (C-prior))
       ;; Deleting words
       ([?\M-d]     . (S-C-right delete))
       ;; ([?\M-\d] . (S-C-left delete))  ; INFO: Could not make it work (not even with binary value, with backspace, with delete...): Note (http://ergoemacs.org/emacs/keystroke_rep.html)
       ;; \d stands for backspace, and the command "(global-set-key [?\M-\d] #'newline)" actually works, so it's an EXWM thing...
       ;; Key-Scripting -> With '-' and between parenthesis they will be pressed in that order "simultaneously"
       ;; Toggle link/page view
       ([?\C-l]     . f6))
      ))

    ("Okular" .
     (("Okular" "okular")
      nil
      (;; Keep original values
       ([?\C-a] . ?\C-a)    ; Select all
       ([?\C-e] . ?\C-e)
       ;; search (manually assigned at Okular)
       ([?\C-s] . ?\C-')    ; Forward
       ([?\C-r] . ?\C-\\))  ; Backward
      ))

    ("Libreoffice" .
     (("Soffice")
      nil
      (;; Undo
       ([?\C-\/] . ?\C-z)
       )
      ))

    ("Vivado" .
     (("Vivado")
      nil
      (;; Keep original values
       ([?\M-<] . ?\M-<) ; Don't remember well why these two...
       ([?\M->] . ?\M->)
       ([?\C-s] . ?\C-s) ; Forward -> Avoid it since C-s should be better saving than searching (use C-r instead)
       ;; Search
       ([?\C-r] . ?\C-f)
       ;; Undo
       ([?\C-\/] . ?\C-z))
      ))

    ("Gtkwave" .
     (("Gtkwave")
      nil
      (;; Keep original values
       ([?\C-k] . ?\C-k)
       ([?\C-w] . ?\C-w)
       ([?\C-s] . ?\C-s) ; Forward -> Avoid it since C-s should be better saving than searching (use C-r instead)
       ([?\C-r] . ?\C-r)
       ;; Selection/highlight
       ([?\C-a] . ?\C-a))
      ))

    ("Novas" .
     (("Novas")
      nil
      (;; Keep original values
       ([?\C-k] . ?\C-k)
       ([?\C-w] . ?\C-w)
       ([?\C-s] . ?\C-s) ; Forward -> Avoid it since C-s should be better saving than searching (use C-r instead)
       ([?\C-r] . ?\C-r)
       ;; Selection/highlight
       ([?\C-a] . ?\C-a))
      ))

    ("Diamond" .
     (("Pnmain")
      nil
      (;; Keep original values
       ([?\C-k] . ?\C-k)
       ([?\C-w] . ?\C-w)
       ([?\C-s] . ?\C-s) ; Forward -> Avoid it since C-s should be better saving than searching (use C-r instead)
       ([?\C-r] . ?\C-r)
       ;; Selection/highlight
       ([?\C-a] . ?\C-a))
      ))

    ("ModelSim" .
     (("Vsim")
      nil
      (;; Save
       ([?\M-s] . ?\C-s)
       ;; Selection/highlight
       ([?\M-a] . ?\C-a)
       ;; Grouping
       ([?\M-g] . ?\C-g)
       ;; Send waves
       ([?\M-e] . ?\C-w)
       )
      ))

    ;; INFO: Waves in ModelSim require the 'no-common-keybindings 4th argument in the alist.
    ;; This is because the movement keybindings (C-f, C-b, C-M-f, etc...) were bound to a tcl
    ;; command inside ModelSim. This TCL command was something like:
    ;;  .vcop Action scrollleft %X %Y
    ;; Assigning a simulation key made the %X %Y args be 0 0. These are the mouse coordinates,
    ;; and if 0 0 the tcl command would have no effect at all. Therefore, it was needed to map
    ;; these inside ModelSim to their respective keys and avoid mapping to simulation keys.
    ;; The rest that do not use the .vcop with coordinates commands can be mapped to simulation
    ;; keys without problem (e.g. C-v M-v etc)
    ("ModelSim-waves" .
     (("WindowObj")
      nil
      (;; Keep original values
       ([?\C-g] . escape)
       ([?\C-m] . return)
       ([?\C-j] . return)
       ([?\M-v] . prior)
       ([?\C-v] . next)
       ([?\C-d] . delete)
       ([?\C-k] . (S-end delete))
       ;; cut/paste.
       ([?\C-w] . ?\C-x)
       ([?\M-w] . ?\C-c)
       ([?\C-y] . ?\C-y)
       ;; Search (rebound to M-f inside Modelsim, since C-f was rebound in waves to <right> key)
       ([?\C-s] . ?\M-f)
       ;; Save
       ([?\M-s] . ?\C-s)
       ;; Selection/highlight
       ([?\M-a] . ?\C-a)
       ;; Grouping
       ([?\M-g] . ?\C-g)
       )
      'no-common-keybidings
      ))
    ))



;;;; Functions
(defun larumbe/exwm-set-buffer-naming ()
  "Set EXWM buffer naming depending on class/title."
  (interactive)
  (add-hook 'exwm-update-class-hook (lambda ()
                                      (exwm-workspace-rename-buffer exwm-class-name)))
  (add-hook 'exwm-update-title-hook (lambda ()
                                      (when (not exwm-instance-name)
                                        (exwm-workspace-rename-buffer exwm-title)))))


(defun larumbe/exwm-set-keybindings ()
  "Set EXWM keybindings."
  ;; Global keybindings
  (exwm-input-set-key (kbd "C-q") #'exwm-input-send-next-key)
  (exwm-input-set-key (kbd "s-r") #'exwm-reset)
  (exwm-input-set-key (kbd "s-w") #'exwm-workspace-switch)
  ;; + Bind "s-0" to "s-9" to switch to the corresponding workspace.
  (dotimes (i 10)
    (exwm-input-set-key (kbd (format "s-%d" i))
                        `(lambda ()
                           (interactive)
                           (exwm-workspace-switch-create ,i))))
  ;; Processes
  (exwm-input-set-key (kbd "s-j") #'larumbe/exwm-launch)
  (exwm-input-set-key (kbd "s-k") #'larumbe/exwm-launch-firefox)
  (exwm-input-set-key (kbd "s-;") #'async-shell-command)
  ;; TODO: Rewrite at some point
  (exwm-input-set-key (kbd "s-o") #'treesit-explore-mode)
  (exwm-input-set-key (kbd "s-i") #'verilog-ts-mode)
  (exwm-input-set-key (kbd "s-I") #'verilog-mode)
  (exwm-input-set-key (kbd "s-u") #'vhdl-ts-mode)
  (exwm-input-set-key (kbd "s-h") #'verilog-ext-hierarchy-current-module)
  (exwm-input-set-key (kbd "C-M-<tab>") #'completion-at-point)
  (exwm-input-set-key (kbd "C-.") #'treesit-explore-mode)
  (exwm-input-set-key (kbd "C-M-]") #'verilog-ts-mode)
  ;; LSP testing
  (exwm-input-set-key (kbd "C-C C-,") #'larumbe/lsp-toggle)
  (exwm-input-set-key (kbd "C-C C-.") #'larumbe/eglot-toggle)
  (exwm-input-set-key (kbd "C-C C-/") #'larumbe/lsp-vhdl-set)
  (exwm-input-set-key (kbd "C-C C-;") #'larumbe/lsp-verilog-set)
  ;; End of TODO
  ;; Window/Frame movement/navigation
  (exwm-input-set-key (kbd "C-;")   #'ivy-switch-buffer)
  (exwm-input-set-key (kbd "C-M-<backspace>") #'backward-kill-sexp)
  (exwm-input-set-key (kbd "M-o")   #'other-window) ; Replaces enriched faces
  (exwm-input-set-key (kbd "M-O")   #'other-frame)  ; Replaces 'negative argument
  (exwm-input-set-key (kbd "C-}")   #'larumbe/shrink-window-horizontally)
  (exwm-input-set-key (kbd "C-{")   #'larumbe/enlarge-window-horizontally)
  (exwm-input-set-key (kbd "C-M-{") #'larumbe/shrink-window-vertically)
  (exwm-input-set-key (kbd "C-M-}") #'larumbe/enlarge-window-vertically)
  (exwm-input-set-key (kbd "M-'")   #'larumbe/kill-current-buffer)
  ;; Misc
  (exwm-input-set-key (kbd "s-SPC") #'larumbe/toggle-keyboard-layout))



(defun larumbe/exwm-set-layout ()
  "Set layout of EXWM."
  ;; Note: EXWM only shows X windows belonging to the current workspace by default.
  ;; You may alter this behavior by assigning exwm-workspace-show-all-buffers a non-nil value.
  (setq exwm-workspace-show-all-buffers t)
  ;; Also, you might want to set exwm-layout-show-all-buffers to t to allow automatically moving X
  ;; windows from inactive workspaces by switching to their associated buffers.
  (setq exwm-layout-show-all-buffers t))


(defun larumbe/exwm-set-keys-hook ()
  "Set local-simulation-keys and input-prefix-keys for EXWM buffers.

Simulation keys add and maybe override the common default
simulation keys `larumbe/exwm-common-input-simulation-keys'.

Prefix keys add to the prefix keys `exwm-input-prefix-keys',
set previously through pushes.

These keys are meant to be set everytime an EXWM buffer is created."
  (let ((programs-params (mapcar #'cdr larumbe/exwm-programs))
        class-names-list simulation-keys prefix-keys no-common-keybindings)
    (catch 'sim-keys-set ; If keys are set for a buffer, break the dolist loop
      (dolist (params programs-params)
        (setq class-names-list      (nth 0 params))
        (setq prefix-keys           (nth 1 params))
        (setq simulation-keys       (nth 2 params))
        (setq no-common-keybindings (nth 3 params))
        (when (and exwm-class-name
                   (member exwm-class-name class-names-list))
          (setq prefix-keys (append exwm-input-prefix-keys prefix-keys))
          (setq-local exwm-input-prefix-keys prefix-keys)
          (unless no-common-keybindings
            (setq simulation-keys (append larumbe/exwm-common-input-simulation-keys simulation-keys)))
          (exwm-input-set-local-simulation-keys simulation-keys)
          (throw 'sim-keys-set nil))))))


(defun larumbe/exwm-setup ()
  "Setup EXWM at startup."
  (larumbe/exwm-set-buffer-naming)
  (larumbe/exwm-set-keybindings)
  (dolist (key larumbe/exwm-common-input-prefix-keys)
    (push key exwm-input-prefix-keys))
  (larumbe/exwm-set-layout)
  (add-hook 'exwm-manage-finish-hook #'larumbe/exwm-set-keys-hook))


(defun larumbe/exwm-launch (&optional program buffer)
  "Launch PROGRAM on a *EXWM* buffer.
PROGRAM must be a string with a binary in the PATH, or
with a full path in case it is not added.

If universal argument or second argument BUFFER is non-nil,
show stdout in BUFFER and pop to this window (for debug mainly)."
  (interactive)
  (unless program
    (setq program (string-trim-right (read-shell-command "$ "))))
  (unless (executable-find program)
    (error "Could not find '%s' in $PATH!!" program))
  (when current-prefix-arg
    (setq buffer (concat "*" program "*")))
  (start-process-shell-command "" buffer program)
  (when buffer
    (pop-to-buffer buffer)))


(defun larumbe/exwm-launch-firefox ()
  "Launch Firefox.
If it is already running, set to current window.
It there is universal argument, open new instance of Firefox."
  (interactive)
  (let* ((ff-class-names (nth 1 (assoc "Firefox" larumbe/exwm-programs)))
         (bufs           (mapcar 'get-buffer ff-class-names))
         (bufs-active    (seq-remove (lambda (elt) (eq elt nil)) bufs))
         (buf-selected   (car bufs-active))) ; Select the first non-nil buffer of Firefox class-names buffers
    (if buf-selected
        (if current-prefix-arg
            (larumbe/exwm-launch "firefox")
          (switch-to-buffer buf-selected))
      (larumbe/exwm-launch "firefox"))))


;;;; xrandr
;; INFO: Command to be set if exwm-randr is enabled in a specific machine
(defvar larumbe/exwm-randr-resolution-command nil)


;;;; Setup
;; Enable on every machine to provide the window keybindings.
;; If EXWM is not enabled, `exwm-input-set-key' works as a `global-set-key'
(larumbe/exwm-setup)



(provide 'init-exwm)

;;; init-exwm.el ends here
