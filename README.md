smartscan-mode
==============

Quickly jumps between other symbols found at point in Emacs.

How it works
------------

Smart Scan will try to infer the symbol your point is on and let you jump to other, identical, symbols 
elsewhere in your current buffer with a single key stroke. The advantage over isearch is its unintrusiveness; 
there are no menus, prompts or other UI elements that require your attention.

Installation
============
```
(package-install 'smartscan)
```
Enable minor mode
```
(smartscan-mode 1)
```
or with `M-x smartscan-mode`.

Usage
=====
`M-n` and `M-p` move between symbols and type `M-'` to replace all symbols in the buffer matching the one under point, and `C-u M-'` to replace symbols in your current defun only (as used by `narrow-to-defun`.)

For more information on how to use Smart Scan and how to master movement in Emacs, read my article on [Effective Editing I: Movement](http://www.masteringemacs.org/articles/2011/01/14/effective-editing-movement/).
