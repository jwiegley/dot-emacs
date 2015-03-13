[![Build Status](https://secure.travis-ci.org/rolandwalker/persistent-soft.png?branch=master)](http://travis-ci.org/rolandwalker/persistent-soft)

Overview
========

Persistent storage for Emacs, returning nil on failure.

Quickstart
----------

```lisp
(require 'persistent-soft)
(persistent-soft-store 'hundred 100 "mydatastore")
(persistent-soft-fetch 'hundred "mydatastore")    ; 100
(persistent-soft-fetch 'thousand "mydatastore")   ; nil
 
;; quit and restart Emacs
 
(persistent-soft-fetch 'hundred "mydatastore")    ; 100
```

Explanation
-----------

This is a wrapper around [pcache.el](http://github.com/sigma/pcache), providing "soft" fetch and
store routines which never throw an error, but instead return
nil on failure.

There is no end-user interface for this library.  It is only
useful from other Lisp code.

The following functions are provided:

	persistent-soft-store
	persistent-soft-fetch
	persistent-soft-exists-p
	persistent-soft-flush
	persistent-soft-location-readable
	persistent-soft-location-destroy

To use persistent-soft, place the persistent-soft.el library
somewhere Emacs can find it, and add the following to your
~/.emacs file:

```lisp
(require 'persistent-soft)
```

See Also
--------

M-x customize-group RET persistent-soft RET

Notes
-----

Using [pcache](http://github.com/sigma/pcache) with a more recent version of [CEDET](http://cedet.sourceforge.net/) gives

	Unsafe call to `eieio-persistent-read'.
	eieio-persistent-read: Wrong type argument: class-p, nil

This library provides something of a workaround.

Bugs
----

Persistent-soft is a wrapper around pcache which is a wrapper
around eieio.  Therefore, persistent-soft should probably be
rewritten to use eieio directly or recast as a patch to pcache.

Compatibility and Requirements
------------------------------

	GNU Emacs version 24.3-devel     : yes, at the time of writing
	GNU Emacs version 24.1 & 24.2    : yes
	GNU Emacs version 23.3           : yes
	GNU Emacs version 22.3 and lower : no

Uses if present: [pcache.el](http://github.com/sigma/pcache) (all operations are noops when
not present)
