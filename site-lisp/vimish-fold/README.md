# Vimish Fold

[![License GPL 3](https://img.shields.io/badge/license-GPL_3-green.svg)](http://www.gnu.org/licenses/gpl-3.0.txt)
[![MELPA](https://melpa.org/packages/vimish-fold-badge.svg)](https://melpa.org/#/vimish-fold)
[![Build Status](https://travis-ci.org/mrkkrp/vimish-fold.svg?branch=master)](https://travis-ci.org/mrkkrp/vimish-fold)

![Vimish Fold](https://raw.githubusercontent.com/mrkkrp/vimish-fold/gh-pages/vimish-fold.png)

This is a package to perform text folding like in Vim. It has the following
features:

* folding of active regions;

* good visual feedback: it's obvious which part of text is folded;

* persistence by default: when you kill a buffer your folds don't disappear;

* persistence scales well, you can work on hundreds of files with lots of
  folds without adverse effects;

* it does not break indentation;

* folds can be toggled from folded state to unfolded and back very easily;

* quick navigation between existing folds;

* you can use mouse to unfold folds (good for beginners and not only for
  them);

* for fans of the `avy` package: you can use `avy` to fold text with minimal
  number of key strokes!

## Installation

If you would like to install the package manually, download or clone it and
put on Emacs' `load-path`, then you can require it in your init file like
this:

```emacs-lisp
(require 'vimish-fold)
```

It's available via MELPA, so you can just <kbd>M-x package-install RET
vimish-fold RET</kbd>.

## Usage

First of all, create global key bindings for most important functions:

* `vimish-fold` creates folds;
* `vimish-fold-delete` deletes folds.

When point is inside of a fold you can toggle it with <kbd>C-`</kbd>, so
usually you don't need to bind toggling functions.

Minimal code creating the keybindings might look like this:

```emacs-lisp
(global-set-key (kbd "<menu> v f") #'vimish-fold)
(global-set-key (kbd "<menu> v v") #'vimish-fold-delete)
```

Of course you can choose different key bindings.

Other functions that constitute API of the package:

* `vimish-fold-unfold`
* `vimish-fold-unfold-all`
* `vimish-fold-refold`
* `vimish-fold-refold-all`
* `vimish-fold-delete-all`
* `vimish-fold-toggle`
* `vimish-fold-toggle-all`
* `vimish-fold-avy` (requires `avy` package)

To get persistent folds you need to enable a minor mode provided by the
package. You can turn `vimish-fold-mode` selectively for modes where you
want to have persistent folding, or simply activate it everywhere:

```emacs-lisp
(vimish-fold-global-mode 1)
```

## Customization

There are a number of customization options that are available via <kbd>M-x
customize-group vimish-fold</kbd>. Everything is carefully documented, as
always.

## License

This work is based on Magnar Sveen's `fold-this` package to some extent, so
I think I should include him as an author, thanks Magnar!

Copyright © 2015–2017 Mark Karpov<br>
Copyright © 2012–2013 Magnar Sveen

Distributed under GNU GPL, version 3.
