# dired-du

[![Build Status](https://api.travis-ci.org/calancha/dired-du.svg?branch=master)](https://travis-ci.org/calancha/dired-du)

## Display the recursive size of directories in Dired

This file defines a minor mode **dired-du-mode** to show
the recursive size of directories in Dired buffers.
If *du* program is available, then the directory sizes are
obtained with it.  Otherwise, the directory sizes are obtained
with Lisp.  The former is much faster.
For directories where the user doesn't have read permission,
the recursive size is not obtained.

Once this mode is enabled, every new Dired buffer displays
recursive dir sizes.

To enable the mode at start up:

1. Store the file in a directory within *load-path*.
2. Add the following into .emacs file:

```(add-hook 'dired-mode-hook #'dired-du-mode)```

Note that obtaining the recursive size of all the directories
in a Dired buffer might be very slow: it may significantly delay
the time to display a new Dired buffer.
Instead of enabling *dired-du-mode* by default in all Dired buffers
you might prefer to use this mode as an interfaz to
the *du* program: you can enable it in the current Dired buffer,
and disable it once you have finished checking the used space.

## Number of marked files and their size

In adition, this library adds a command, **dired-du-count-sizes**,
to count the number of marked files and how much space
they use; the command accepts a particular character mark
i.e., '*' or all kind of marks i.e, any character other than ?\s.

