<b>NOTE</b>:  This package is obsolete as of v24.  Use the built-in option
`switch-to-buffer-preserve-window-point` instead.

Emacs conveniently allows one to work on different parts of the same buffer
at the same time, but the rules governing buffer display are, for some
people's editing habits, less than ideal.  Suppose for example that one is
editing two parts of buffer <i>buf</i> in windows <i>win-1</i> and
<i>win-2</i>, switches briefly to another buffer in <i>win-2</i>, then
returns to editing <i>buf</i> in <i>win-2</i>.  This latter window will now
display the same part of <i>buf</i> as <i>win-1</i>, rather than the portion
that one was just recently editing in it.  The package `per-window-point`
creates persistent values of `window-point` and `window-start`, so that in
cases like that just described <i>win-2</i> will return to its previous
position in <i>buf</i>.

In some cases, as when another Lisp program wants to move point in a buffer
and then display that buffer in a window, it makes sense for Per-Window-Point
not to position point in that window.  (For example, when looking up a
function definition via `describe-function`, point is moved to the function
definition before the library that defines the function is displayed; we then
don't want to move point away from the definition when the library is
displayed.)  The package is reasonably intelligent in identifying situations
in which it should defer to other Lisp programs.  It also provides several
hooks so that the user can define other types of exception.

Installation and Usage
======================

To install, place the package file in your load path and put `(require 'per-window-point)` in your .emacs.  To toggle Per-Window-Point on and off, use the command `pwp-mode`.

Three variables provide control over whether pwp-mode should reposition a buffer that has been displayed before in a window:

1. `pwp-no-reposition-names`:  If a buffer name is an element of this list, then Per-Window-Point will not position it. The default value is nil.
2. `pwp-no-reposition-regexps`:  If a buffer name matches one of the regular expressions in this list,  Per-Window-Point will not position it.  The default value is `("^\\*.+\\*$")`.
3. `pwp-reposition-tests`:  A list of functions.  When a buffer is displayed in a window, Per-Window-Point calls each function in this list with two arguments, the buffer and the window in question.  If any function returns nil, Per-Window-Point does not reposition.  The default value is nil.

A Note on v24
=============

The buffer display routines were substantially rewritten for v24, and this
package hasn't been fully tested with with that version.
