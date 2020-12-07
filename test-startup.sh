#!/bin/sh -e

# Copyright (c) 2006-2018, Steve Purcell
# All rights reserved.

echo "Attempting startup..."
${EMACS:=emacs} -nw --batch \
                --eval '(let ((debug-on-error t)
                              (user-emacs-directory (expand-file-name "~/.emacs.d/"))
                              (user-init-file (expand-file-name "larumbe/init.el")))
                           (load-file user-init-file)
                           (run-hooks (quote after-init-hook)))'
echo "Startup successful"
