[![MELPA](https://melpa.org/packages/diminish-badge.svg)](https://melpa.org/#/diminish)
[![MELPA Stable](http://stable.melpa.org/packages/diminish-badge.svg)](http://stable.melpa.org/#/diminish)

# diminish.el

Introduction
============

> When we diminish a mode, we are saying we want it to continue doing its
> work for us, but we no longer want to be reminded of it.  It becomes a
> night worker, like a janitor; it becomes an invisible man; it remains a
> component, perhaps an important one, sometimes an indispensable one, of
> the mechanism that maintains the day-people's world, but its place in
> their thoughts is diminished, usually to nothing.  As we grow old we
> diminish more and more such thoughts, such people, usually to nothing.
>  -- Will Mengarini

This package implements hiding or abbreviation of the mode line displays
(lighters) of minor-modes.

Quick start
===========

```emacs-lisp
(require 'diminish)
;; Hide jiggle-mode lighter from mode line
(diminish 'jiggle-mode)
;; Replace abbrev-mode lighter with "Abv"
(diminish 'abbrev-mode "Abv")
```

John Wiegley's
[use-package](https://github.com/jwiegley/use-package#diminishing-and-delighting-minor-modes)
macro also has support for diminish.el.

Acknowledgments
===============

diminish.el was created by Will Mengarini on 19th of February 1998 and is now
maintained by [Martin Yrjölä](https://github.com/myrjola).
