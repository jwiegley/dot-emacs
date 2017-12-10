emacs-makefile-runner
=====================

http://danamlund.dk/emacs/make-runner.html

Searches for Makefile and fetches targets

An easy method of running Makefiles. The function searches current and
parent directories for a Makefile, fetches targets, and asks the user
which of the targets to run.

Save makefile-runner.el to your load path and add the following to
your .emacs file:

    (require 'makefile-runner)

You can add a keybinding to run the function, for example:

    (global-set-key (kbd "F11") 'makefile-runner)
