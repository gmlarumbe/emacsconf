#!/bin/bash

mkdir -p ${HOME}/.emacs.d

echo "Create .elisp home dir..."
ln -s .elisp ~/.elisp

if [ -d ".elisp_private" ]; then
    echo "Create .elisp_private home dir..."
    ln -s .elisp_private ~/.elisp_private
fi

echo "Link to emacs init folder..."
ln -s .elisp/lisp/init.el ${HOME}/.emacs.d/init.el

cd .elisp
git submodule update --init --recursive --jobs 4
