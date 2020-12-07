[![Build Status](https://github.com/gmlarumbe/emacsconf/workflows/CI/badge.svg)](https://github.com/gmlarumbe/emacsconf/actions)


## Overview

My Emacs configuration file.

Main focus on **Verilog/SystemVerilog** HDL, **scripting** and **compilation** for elaboration/synthesis/simulations.

## How-To ##

  * Root config file is **init.el**. A symbolic link from *~/.emacs.d/init.el* is required for configuration to be loaded. This file loads configuration from other files in a modular way.

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


  * This config also makes extensive use of use-package, helm, ido, navi, outshine, ggtags or yasnippet among others. Check their corresponding user guides for more info.


## Folder structure ##

  * **larumbe** includes the core files of the configuration.
    * **config-basic.el:** basic emacs configuration and built-in modes setup.
    * **packages-config.el**: use-package MELPA packages setup for a portable and compact config.
    * **custom-functions.el**: global and mode-specific customized functions.
    * **macros.el**: insert-kbd-macro and elmacro recorded functions/macros.
    * **compilation-settings.el**: compilation-mode setup with additional regexp parsing for external programs (e.g. vivado, irun, scons...)
    * **programming-settings.el**: global setup for prog-mode derived modes and specific mode keybindings.
    * **exwm-config.el**: global keybindings and exwm input/simulation keys config.
    * **machine-config.el**: specific content to current machine (not included in the repo).

  * **download** includes elisp files found on the Internet and not available at MELPA.

  * **snippets** includes additional yasnippet snippets, some of them found on the internet and some of them customized.


