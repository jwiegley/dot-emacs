fn.el -- Concise anonymous functions for Emacs Lisp.
-----

__fn.el__ provides macros for writing concise and readable anonymous functions.

[![MELPA](https://melpa.org/packages/fn-badge.svg)](https://melpa.org/#/fn)
[![MELPA Stable](https://stable.melpa.org/packages/fn-badge.svg)](https://stable.melpa.org/#/fn)

------------------------------------------------------------

## Installation

* Install from [melpa](http://melpa.org/#/) using `M-x list-packages`.
* Or, place `fn.el` in any directory on your `load-path` and execute:

    (require 'fn)

------------------------------------------------------------

## API

* [fn](#fn-rest-body) `(&rest body)`
* [fn:](#fn-rest-body) `(&rest body)`

### fn `(&rest BODY)`

Return a function defined by BODY.

Intended for inline use where concision is desired.  If creating a function to
bind as a function value, use `lambda` or `-lambda`.

The definition BODY may use anaphoric parameters to refer to the arguments. For
a single-argument function, `<>` can be used. For a multiple-argument function,
use `<1>` to refer to the first argument, `<2>` to refer to the second, and so on
up to `<9>`. The parameter `<rest>` refers to a list containing the (n+1)st and
later arguments, where `<n>` is the highest numerical parameter supplied.

If applied to a literal, creates a constant function, or equivalently, a thunk
(since it can be called with any number of arguments).

    (-map (fn (* <> <>)) (number-sequence 0 10))
    ;; (0 1 4 9 16 25 36 49 64 81 100)

    (-map (fn (/ (-sum <>)
                (length <>)))
          '((3.0 4.0 5.0 5.0 10.0)
            (1.5 2.5 2.0)
            (1 5)))
    ;; (5.4 2.0 3)
    ;; find average of each list

    (-filter (fn (zerop (mod <> 3)))
            (number-sequence 1 10))
    ;; (3 6 9)

    (funcall (fn 7))
    ;; 7

    (funcall (fn (-map #'list <rest>)) 1 2 3 4)
    ;; ((1) (2) (3) (4))
    
### fn: `(&rest BODY)`

Return a function defined by (BODY).

Intended for inline use where concision is desired.  If creating a function to
bind as a function value, use `lambda` or `-lambda`.

Identical to `fn` except that BODY is automatically parenthesized.

The definition BODY may use the anaphoric parameter `<>` for the sole argument,
or `<1>` ... `<9>` to refer to multiple positional arguments. The parameter
`<rest>` refers to a list containing the (n+1)st and later arguments, where `<n>` is
the highest numerical parameter supplied.

    (-map (fn: * <> <>) (number-sequence 0 10))
    ;; (0 1 4 9 16 25 36 49 64 81 100)

    (-filter (fn: > <> 0)
            '(-5 2 0 0 3 -1 0 4))
    ;; (2 3 4)
