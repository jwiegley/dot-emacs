[![Build Status](https://secure.travis-ci.org/rolandwalker/anaphora.png?branch=master)](http://travis-ci.org/rolandwalker/anaphora)

Overview
========

Anaphoric expressions for Emacs Lisp, providing implicit temporary variables.

Quickstart
----------

```lisp
(require 'anaphora)
 
(awhen (big-long-calculation)
  (foo it)      ; `it` is provided as
  (bar it))     ; a temporary variable
 
;; anonymous function to compute factorial using `self`
(alambda (x) (if (= x 0) 1 (* x (self (1- x)))))
```

anaphora
--------

Anaphoric expressions implicitly create one or more temporary
variables which can be referred to during the expression.  This
technique can improve clarity in certain cases.  It also enables
recursion for anonymous functions.

To use anaphora, place the anaphora.el library somewhere
Emacs can find it, and add the following to your ~/.emacs file:

```lisp
(require 'anaphora)
```

The following macros are made available

	aand
	ablock
	acase
	acond
	aecase
	aetypecase
	aif
	alambda
	alet
	aprog1
	aprog2
	atypecase
	awhen
	awhile
	a+
	a-
	a*
	a/

The following macros are experimental, especially the last one

	anaphoric-set
	anaphoric-setq
	anaphoric-setf-experimental

See Also
--------

* [http://en.wikipedia.org/wiki/On_Lisp](http://en.wikipedia.org/wiki/On_Lisp)
* [http://en.wikipedia.org/wiki/Anaphoric_macro](http://en.wikipedia.org/wiki/Anaphoric_macro)

Notes
-----

Partially based on examples from the book "On Lisp", by Paul Graham.

When this library is loaded, the provided anaphoric forms are
registered as keywords in font-lock. This may be disabled via
customize.

Compatibility and Requirements
------------------------------

	GNU Emacs version 24.3-devel     : yes, except macros marked experimental
	GNU Emacs version 24.1 & 24.2    : yes
	GNU Emacs version 23.3           : yes
	GNU Emacs version 22.3           : yes
	GNU Emacs version 21.x and lower : unknown

No external dependencies
