# Minimap

This file is an implementation of a minimap sidebar, i.e., a
smaller display of the current buffer on the left side.  It
highlights the currently shown region and updates its position
automatically.  You can navigate in the minibar by dragging the
active region with the mouse, which will scroll the corresponding
edit buffer.  Additionally, you can overlay information from the
tags gathered by CEDET's semantic analyzer.

Simply use M-x minimap-mode to toggle activation of the minimap.
Use 'M-x customize-group RET minimap RET' to adapt minimap to your
needs.

### Before you make a pull request:

This package is part of GNU ELPA, so anyone making a non-trivial
change needs a signed copyright assignment with the FSF for GNU Emacs.
