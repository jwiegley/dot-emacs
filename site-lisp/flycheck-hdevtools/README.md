flycheck-hdevtools
==================

*NOTICE: This package is currently unmaintained, and may or may not work*

This library provides a [flycheck][] checker for Haskell source code
using [hdevtools][].

`hdevtools` is a syntax and type checker which caches information in persistent
background daemons, and thus checks faster than plain GHC.

Installation
------------

You'll need Emacs 24 for `flycheck`, so the recommended way to get
`flycheck-hdevtools` is as a package from the [MELPA][melpa]
repository. The version of `haskell-hdevtools` there will always be
up-to-date.

If you insist on doing things the hard way, first ensure `flycheck` is
installed, then download this code and add the directory to your Emacs
`load-path`.

Then, in your `init.el`:

```lisp
(eval-after-load 'flycheck
  '(require 'flycheck-hdevtools))
```

Make sure that the `hdevtools` binary is present on Emacs' `exec-path`, or
customize `flycheck-haskell-hdevtools-executable` to point to the `hdevtools`
binary.

Usage
-----

When `flycheck` is enabled (e.g. with `global-flycheck-mode`), Haskell
buffers will be automatically checked using this checker.

License
-------

This program is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with
this program.  If not, see http://www.gnu.org/licenses/.

See
[COPYING](https://github.com/flycheck/flycheck-hdevtools/blob/master/COPYING)
for details.

About
-----

`flycheck-hdevtools` is code originally submitted to `flycheck` by
[Steve Purcell](https://github.com/purcell).

<hr>

Author links:

[![](http://api.coderwall.com/purcell/endorsecount.png)](http://coderwall.com/purcell)

[![](http://www.linkedin.com/img/webpromo/btn_liprofile_blue_80x15.png)](http://uk.linkedin.com/in/stevepurcell)

[Steve Purcell's blog](http://www.sanityinc.com/) // [@sanityinc on Twitter](https://twitter.com/sanityinc)

[flycheck]: https://github.com/flycheck/flycheck
[tags]: https://github.com/flycheck/flycheck-hdevtools/tags
[hdevtools]: https://github.com/hdevtools/hdevtools
[melpa]: http://melpa.org
