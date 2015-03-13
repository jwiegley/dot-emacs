[![Build Status](https://secure.travis-ci.org/rolandwalker/button-lock.png?branch=master)](http://travis-ci.org/rolandwalker/button-lock)

# Overview

Mouseable text in Emacs.

![wiki-nav example](https://raw.githubusercontent.com/rolandwalker/button-lock/master/wiki_nav_example.png)

Modern people using modern Emacs usually look at screens marked up with
font-lock (aka syntax highlighting).  Sometimes modern people even use a
mouse.

This package provides

 * *button-lock:* a programmer-friendly library for making text mouseable

 * *wiki-nav:* a user-friendly library for making text mouseable

Because these packages are based on font-lock, they are efficient.

 * [Quickstart](#quickstart)
 * [button-lock](#button-lock)
 * [wiki-nav](#wiki-nav)
 * [Advanced usage](#advanced-usage)
 * [Prior Art](#prior-art)
 * [Other Libraries Built on Button-lock](#other-libraries-built-on-button-lock)
 * [Compatibility and Requirements](#compatibility-and-requirements)

## Quickstart

```elisp
(require 'wiki-nav)
 
(global-wiki-nav-mode 1)
 
;; Sprinkle double-bracketed [[links]] in your code comments
```

## button-lock

Button-lock uses font-lock to make text clickable.  In Emacs-speak: it
creates font-lock keywords which have mouse bindings added to their
text properties.

Button-lock has a simple interface that works like this

```elisp
(button-lock-set-button "http://google.com" 'browse-url-at-mouse)
```

However, button-lock does not create any buttons by default.  You must write
some Lisp code to make it do anything.

For much more information, see [the source for button-lock.el](https://github.com/rolandwalker/button-lock/blob/master/button-lock.el)
and the docstring for `button-lock-set-button` (<kbd>C-h</kbd> <kbd>f</kbd> <kbd>button-lock-set-button</kbd>).

## wiki-nav

Wiki-nav is a user-friendly high-level interface to button-lock.  It
provides a minor mode which recognizes [[wiki-style]] double-bracketed
navigation links in any type of file.  Wiki-nav links permit the user
to jump between sections, between files, or open external URLs.

Example usage:

1. Put `button-lock.el` and `wiki-nav.el` on your Emacs `load-path`
   directory.  If you've never heard of a `load-path` directory, create a
   new directory named `~/.emacs.d/lisp`, and add this code to your
   `~/.emacs` file:

	```elisp
	(add-to-list 'load-path (expand-file-name "~/.emacs.d/lisp"))
	```

2. Add the following to your `~/.emacs` file

	```elisp
	(require 'wiki-nav)
	(global-wiki-nav-mode 1)
	```

3. Sprinkle double-bracketed

		[[links]]

   in your files.  That's it.  There's more functionality, but simple `[[links]]`
   may be all you need.  When you click on `[[links]]`, the point jumps forward
   in the buffer to the next matching wiki-nav link.

## Advanced usage

Bracketed links may contain external URLs:

		[[http://google.com]]

Or they may use various internally-recognized URI schemes:

 * `visit:` navigates to another file

		[[visit:/etc/hosts]]

		[[visit:/path/to/another/file:NameOfLink]]

 * `func:` navigates to the definition of a function

		[[func:main]]

 * `line:` navigates to a line number

		[[line:12]]

 * `visit:` may be combined with other schemes:

		[[visit:/path/to/another/file.c:func:main]]

		[[visit:/etc/hosts:line:5]]

Path names and similar strings are subjected to URI-style unescaping before
lookup.  To link to a filename which contains a colon, substitute "%3A" for
the colon character.

For much more information, see [the source for wiki-nav.el](https://github.com/rolandwalker/button-lock/blob/master/wiki-nav.el)
and the docstring for `wiki-nav-mode` (<kbd>C-h</kbd> <kbd>f</kbd> <kbd>wiki-nav-mode</kbd>).

## Prior Art

The following packages provide functionality that is similar to button-lock
or wiki-nav:

hi-lock  
David M. Koppelman <koppel@ece.lsu.edu>

buttons.el  
Miles Bader <miles@gnu.org>

linkd  
<http://dto.github.com/notebook/linkd.html>  
David O'Toole <dto@gnu.org>

org-mode  
<http://orgmode.org>  
Carsten Dominik &lt;carsten at orgmode dot org&gt;

## Other Libraries Built on Button-lock

[Fixmee-mode](http://github.com/rolandwalker/fixmee)

## Compatibility and Requirements

	GNU Emacs version 24.5-devel     : not tested
	GNU Emacs version 24.4           : yes
	GNU Emacs version 24.3           : yes
	GNU Emacs version 23.3           : yes
	GNU Emacs version 22.2           : yes, with some limitations
	GNU Emacs version 21.x and lower : unknown

Uses if present: [nav-flash.el](http://github.com/rolandwalker/nav-flash), [back-button.el](http://github.com/rolandwalker/back-button)
