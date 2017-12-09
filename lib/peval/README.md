# Partial Evaluator for Emacs Lisp [![Build Status](https://travis-ci.org/Wilfred/peval.svg?branch=master)](https://travis-ci.org/Wilfred/peval) [![Coverage Status](https://coveralls.io/repos/github/Wilfred/peval/badge.svg?branch=master)](https://coveralls.io/github/Wilfred/peval?branch=master)

Partially evaluate elisp forms. Handy for debugging, and [inspired by
a discussion on Reddit](https://www.reddit.com/r/emacs/comments/60tl6o/tips_on_reading_dense_emacs_lisp_code/dfa92hg/) and
[this talk on Program Slicing](https://www.youtube.com/watch?v=dSqLt8BgbRQ).

## Fundamental Limitations

* Assumes lexical scope.

* Assumes that if a macro call site does not contain a symbol, than
  that symbol is not modified (TODO: example).
  
* (No plan to implement) recursive functions.

## Current limitations

* Some special forms are not implemented.

* Loops are not implemented and their effects are ignored.

* Does not macro expand forms to see if we can simplify them entirely.

* Does not simplify known s-expressions in macro arguments that are
  known to be evaluated.

* Does not properly print simplified values that are now lists.

* Mutation `(push 1 foo)` is not handled correctly.

* Mutation does not currently cause preservation of let
  forms. E.g. `(let ((x 1)) (fn1 x)` can be `(fn1 1)` (numbers are
  value types), but `(let ((x '(1))) (fn1 x) (fn2 x))` cannot be
  `(progn (fn1 '(1)) (fn2 '(1)))`.

* (Fundamental?) Does not handle aliasing of values.
