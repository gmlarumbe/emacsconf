;;; init-env.el --- Emacs Environment Variables Functions  -*- lexical-binding: t -*-
;;; Commentary:
;;
;; Inspiration came from: https://emacs.stackexchange.com/questions/6104/reload-environment-variables
;;
;; Needs to work in conjunction with an update script that provides environment variables to the Emacs server
;; through a emacsclient call that evaluates `larumbe/update-env' (many thanks to Håkon Hægland)
;;
;; TODO: Still need to know how to handle aliases and imported functions
;; aliases: $ alias
;; functions: $ declare -f
;;
;; INFO: The thing with BASH_FUNC and modules below has to do with following issue:
;; https://github.com/drush-ops/drush/issues/2065
;; Check 'dirkd' comments below
;; Modules will export a function as a multiline environment variable
;; (could be one-line but it is done like that with export -f in /p/lfp/common/asic_tools/Modules/3.2.10/init/bash:11
;; More info about functions in shell variables: https://unix.stackexchange.com/questions/233091/bash-functions-in-shell-variables
;;
;; Plus `exec-path-from-shell' was not useful for what I wanted to do in batch
;;
;;; Code:

(defvar larumbe/env-var-re "^\\(.*?\\)=\\(.*\\)")
(defvar larumbe/env-fun-re "^\\(BASH_FUNC_\\)[a-z]+()=\\(.*\\)")

(defvar larumbe/current-environment nil)


(defun larumbe/env-to-alist (env)
  "docstring"
  (let ((var-re larumbe/env-var-re)
        (fun-re larumbe/env-fun-re)
        (var)
        (value)
        (env-alist))
    (dolist (pair env)
      (when (and (string-match var-re pair)
                 (not (string-match fun-re pair)))
        (setq var   (match-string 1 pair))
        (setq value (match-string 2 pair))
        (push (cons var value) env-alist)))
    env-alist))


(defun larumbe/env-set-from-alist (alist)
  "docstring"
  (mapcar (lambda (pair)
            (setenv (car pair) (cdr pair)))
          alist))


(defun larumbe/env-get-current ()
  "docstring"
  (let ((cur-env (split-string (shell-command-to-string "printenv") "\n")))
    (setq larumbe/current-environment (larumbe/env-to-alist cur-env))))


(defun larumbe/env-get-initial ()
  "docstring"
  (larumbe/env-to-alist initial-environment))


(defun larumbe/env-set-initial ()
  "docstring"
  (interactive)
  (let ((env-to-unset (seq-difference
                       (mapcar 'car (larumbe/env-get-current))
                       (mapcar 'car (larumbe/env-get-initial)))))
    ;; Clear environment variables that were not present at startup
    (dolist (elm env-to-unset)
      (setenv elm)) ; `setenv' second argument set to nil to clear
    ;; Set startup env variables to their initial values
    (larumbe/env-set-from-alist (larumbe/env-get-initial))))


(defun larumbe/env-update-from-subshell (fn)
  "To be used from outside of Emacs to update inner Emacs."
  (let* ((env-str (with-temp-buffer
                    (insert-file-contents fn)
                    (buffer-string)))
         (env-list (split-string env-str "\n"))
         (env-alist (larumbe/env-to-alist env-list)))
    (larumbe/env-set-from-alist env-alist)))



(provide 'init-env)

;;; init-env.el ends here
