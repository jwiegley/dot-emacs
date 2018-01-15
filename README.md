# Magit-Popup

This package implements a generic interface for toggling switches
and setting options and then invoking an Emacs command which does
something with these arguments.  The prototypical use is for the
command to call an external process, passing on the arguments as
command line arguments.  But this is only one of many possible
uses (though the one this library is optimized for).

Magit still used Magit-Popup but is going to be switch to a cleaner
and more flexible implementation, once that has been written.  Even
after that Magit-Popup will remain available and receive bug fixes,
so that third-party packages can continue to use it.

- [Magit-Popup User Manual](https://magit.vc/manual/magit-popup)
- [Finally replace magit-popup with a more capable implementation](https://github.com/magit/magit/issues/2957)
