[![Build Status](https://github.com/gmlarumbe/emacsconf/workflows/CI/badge.svg)](https://github.com/gmlarumbe/emacsconf/actions)


## Overview

My Emacs configuration file.

Main focus on **SystemVerilog**, **VHDL**, **scripting** and **compilation** for elaboration/synthesis/simulations.

## How-To ##

  * Root config file is **init.el**. Symbolic links at *~/.emacs.d/init.el* and *~/.emacs.d/early-init.el* are required for configuration to be loaded. This file loads configuration from other files in a modular way.

  * [EXWM](https://github.com/ch11ng/exwm) is set as the default configuration display manager. If you want to use it read the [documentation](https://github.com/ch11ng/exwm/wiki) and customize *exwm-config.el* with the proper **xrandr** resolution of your screen. Besides, other display managers might be disabled first and **.xinitrc** file should look similar to the following:

      ```shell
    # Disable access control
    xhost +SI:localuser:$USER
    # Keyboard repeat rate
    xset r rate 200 60
    # Keyboard layout
    setxkbmap us
    # Switch Caps/Ctrl
    setxkbmap -option "ctrl:swapcaps"
    # Disable bell for terminal
    xset b off
    # Start Emacs
    exec dbus-launch --exit-with-session emacs
      ```

  * NOTE: This configuration is intended to be shared among different machines and expects a machine-specific configuration to be placed at "~/.elisp_private/". Here you can enable/disable EXWM and some other machine-dependent settings.


## Folder structure ##

  * **lisp**: core files of the configuration.

  * **lisp_prog**: programming languages related files.

  * **scripts**: auxiliary files for CI.


