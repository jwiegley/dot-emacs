[![Build Status](https://secure.travis-ci.org/rolandwalker/list-utils.png?branch=master)](http://travis-ci.org/rolandwalker/list-utils)

# Overview

List-manipulation utility functions for Emacs.

 * [Quickstart](#quickstart)
 * [Explanation](#explanation)
 * [Notes](#notes)
 * [Compatibility and Requirements](#compatibility-and-requirements)

## Quickstart

```elisp
(require 'list-utils)
 
(list-utils-flatten '(1 2 (3 4 (5 6 7))))
;; '(1 2 3 4 5 6 7)
 
(list-utils-depth '(1 2 (3 4 (5 6 7))))
;; 3
 
(let ((cyclic-list '(1 2 3 4 5 6 7)))
  (nconc cyclic-list (cdr cyclic-list))
  (list-utils-make-linear-inplace cyclic-list))
;; '(1 2 3 4 5 6 7)
 
(list-utils-cyclic-p '(1 2 3))
;; nil
 
(list-utils-plist-del '(:one 1 :two 2 :three 3) :two)
;; '(:one 1 :three 3)
```

## Explanation

List-utils is a collection of functions for list manipulation.
This library has no user-level interface; it is only useful
for programming in Emacs Lisp.

Notable functionality includes

 * `list-utils-flatten`, a robust list-flattener which handles
    cyclic lists, non-nil-terminated lists, and preserves nils
    when they are found as list elements.

 * `tconc`, a simple data structure for efficiently appending
    to a list

The following functions are provided:

	make-tconc
	tconc-p
	tconc-list
	tconc
	list-utils-cons-cell-p
	list-utils-cyclic-length
	list-utils-improper-p
	list-utils-make-proper-copy
	list-utils-make-proper-inplace
	list-utils-make-improper-copy
	list-utils-make-improper-inplace
	list-utils-linear-p
	list-utils-linear-subseq
	list-utils-cyclic-p
	list-utils-cyclic-subseq
	list-utils-make-linear-copy
	list-utils-make-linear-inplace
	list-utils-safe-length
	list-utils-safe-equal
	list-utils-depth
	list-utils-flat-length
	list-utils-flatten
	list-utils-alist-or-flat-length
	list-utils-alist-flatten
	list-utils-insert-before
	list-utils-insert-after
	list-utils-insert-before-pos
	list-utils-insert-after-pos
	list-utils-and
	list-utils-not
	list-utils-xor
	list-utils-uniq
	list-utils-dupes
	list-utils-singlets
	list-utils-partition-dupes
	list-utils-plist-reverse
	list-utils-plist-del

To use list-utils, place the `list-utils.el` library somewhere
Emacs can find it, and add the following to your `~/.emacs` file:

```elisp
(require 'list-utils)
```

## Notes

This library includes an implementation of the classic Lisp
`tconc` which is outside the `list-utils-` namespace.

## Compatibility and Requirements

	GNU Emacs version 25.1-devel     : not tested
	GNU Emacs version 24.5           : not tested
	GNU Emacs version 24.4           : yes
	GNU Emacs version 24.3           : yes
	GNU Emacs version 23.3           : yes
	GNU Emacs version 22.2           : yes, with some limitations
	GNU Emacs version 21.x and lower : unknown

No external dependencies
