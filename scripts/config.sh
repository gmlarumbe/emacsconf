#!/bin/bash

# Rename repos
# CUR_DIR=$PWD

mkdir -p ${HOME}/.emacs.d

ln -s $PWD ~/.elisp
ln -s larumbe/init.el ${HOME}/.emacs.d/init.el


# mv ${CUR_DIR} ${HOME}/.elisp
# mv ~/emacsconf_priv ~/.elisp_private

# Create symlinks inside .emacs.d
# ln -sf ${HOME}/.elisp/larumbe/init.el ${HOME}/.emacs.d/init.el