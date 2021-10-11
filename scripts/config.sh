#!/bin/bash

mkdir -p ${HOME}/.emacs.d

echo "Create .elisp home dir..."
ln -s ${PWD}/.elisp ${HOME}/.elisp

if [ -d ".elisp_private" ]; then
    echo "Create .elisp_private home dir..."
    ln -s ${PWD}/.elisp_private ${HOME}/.elisp_private
fi

echo "Link to emacs init folder..."
ln -s ${PWD}/.elisp/lisp/init.el ${HOME}/.emacs.d/init.el
ln -s ${PWD}/.elisp/lisp/early-init.el ${HOME}/.emacs.d/early-init.el

# INFO: Uncomment if using git submodules
# git -C .elisp submodule update --init --recursive --jobs 8
