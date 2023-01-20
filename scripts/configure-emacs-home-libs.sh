#!/bin/bash

# Guidelines on how to build Emacs using $HOME lib versions.
#
# This could be necessary when versions different than the system ones are required
# or when these are not even installed in a system without root privileges.

PREFIX=$HOME/bin/emacs-29
LIBJANSSON_PATH=${HOME}/bin/jansson-2.14
LIBGCCJIT_PATH=${HOME}/bin/gcc-12.1.0
LIBTREESITTER_PATH=${HOME}/bin/tree-sitter-0.20

# Some basic checks
[[ -f "./configure" ]] || { echo "Not in proper directory for ./configure"; exit 1; }
[[ -d "$PREFIX" ]] || { echo "Prefix directory $PREFIX does not exist"; exit 1; }

[[ -d "$LIBJANSSON_PATH" ]] || { echo "libjansson directory missing"; exit 1; }
[[ -d "$LIBGCCJIT_PATH" ]] || { echo "libgccjit directory missing"; exit 1; }
[[ -d "$LIBTREESITTER_PATH" ]] || { echo "libtree-sitter directory missing"; exit 1; }

[[ -L "$LIBJANSSON_PATH/lib/libjansson.so" ]] || { echo "libjansson.so missing"; exit 1; }
[[ -L "$LIBGCCJIT_PATH/lib/libgccjit.so" ]] || { echo "libgccjit.so missing"; exit 1; }
[[ -L "$LIBTREESITTER_PATH/lib/libtree-sitter.so" ]] || { echo "libtree-sitter.so missing"; exit 1; }


# Initial return code
RC=0
# Initial values
LDFLAGS=
CPPFLAGS=
LIBS=


# Set up libjansson to have native JSON parsing support, for LSP and eglot
#  - This is needed if system does not have an updated version of libjansson and ./configure does not detect it
JSON_LIBS="-L${LIBJANSSON_PATH}/lib"
JSON_CFLAGS="-I${LIBJANSSON_PATH}/include"
LDFLAGS+="-L${LIBJANSSON_PATH}/lib"
CPPFLAGS="-I${LIBJANSSON_PATH}/include"
LIBS+="-ljansson"


# Set up libgccjit for native compilation
# - NOTE: No need to update LIBS here since using --with-native-compilation will ensure libgccjit is found
LDFLAGS+=" -L${LIBGCCJIT_PATH}/lib"
CPPFLAGS+=" -I${LIBGCCJIT_PATH}/include"


# Set up libtree-sitter
TREE_SITTER_CFLAGS="-I${LIBTREESITTER_PATH}/include"
TREE_SITTER_LIBS="-L${LIBTREESITTER_PATH}/lib"
LDFLAGS+=" -L${LIBTREESITTER_PATH}/lib"
CPPFLAGS+=" -I${LIBTREESITTER_PATH}/include"
LIBS+=" -ltree-sitter"


# Export variables for ./configure
echo "JSON_LIBS=$JSON_LIBS"
echo "JSON_CFLAGS=$JSON_CFLAGS"
echo "LDFLAGS=$LDFLAGS"
echo "CPPFLAGS=$CPPFLAGS"
echo "LIBS=$LIBS"
export JSON_CFLAGS JSON_LIBS LDFLAGS CPPFLAGS LIBS TREE_SITTER_CFLAGS TREE_SITTER_LIBS


# ./configure will run basic programs to make sure that these libraries are available
export LD_LIBRARY_PATH=$LIBJANSSON_PATH/lib:$LIBTREESITTER_PATH/lib:$LIBGCCJIT_PATH/lib


# Configure command
set -o pipefail # Save exit code of tee piped command (https://stackoverflow.com/questions/6871859/piping-command-output-to-tee-but-also-save-exit-code-of-command)
LOG_FILE=configure.log
echo ""
./configure --prefix=$PREFIX --with-gif=ifavailable --with-native-compilation --with-json --with-tree-sitter | tee $LOG_FILE
RC=$?

# DANGER: Check visually if these 3 packages are available. Following code somehow hanged the shell...
# Check if it was successfully setup
# if [ $RC -eq 0 ]; then
#     [[ $(grep "Does Emacs use -ljansson" $LOG_FILE | awk '{ print $(NF)}') == "yes" ]] || { echo "ERROR with libjansson"; RC=1; }
#     [[ $(grep "Does Emacs use -ltree-sitter "$LOG_FILE | awk '{ print $(NF)}') == "yes" ]] || { echo "ERROR with tree-sitter"; RC=1; }
#     [[ $(grep "Does Emacs have native lisp compiler" $LOG_FILE | awk '{ print $(NF)}') == "yes" ]] || { echo "ERROR with native compiler"; RC=1; }
#     return $RC
# fi


