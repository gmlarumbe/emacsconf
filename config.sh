#!/bin/bash

# Rename repos
mv ~/emacsconf ~/.elisp
mv ~/emacsconf_priv ~/.elisp_private

# Create symlinks inside .emacs.d
ln -sf ~/.elisp_private ~/.emacs.d/.elisp_private
ln -sf ~/.elisp/larumbe/init.el ~/.emacs.d/init.el
