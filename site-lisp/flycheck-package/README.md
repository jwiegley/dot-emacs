[![Melpa Status](http://melpa.org/packages/flycheck-package-badge.svg)](http://melpa.org/#/flycheck-package)
[![Melpa Stable Status](http://stable.melpa.org/packages/flycheck-package-badge.svg)](http://stable.melpa.org/#/flycheck-package)
<a href="https://www.patreon.com/sanityinc"><img alt="Support me" src="https://img.shields.io/badge/Support%20Me-%F0%9F%92%97-ff69b4.svg"></a>

flycheck-package
===============

This library provides a [flycheck][] checker for the metadata in Emacs
Lisp files which are intended to be packages.  That metadata includes the
package description, its dependencies and more.  The checks are
performed by the
separate [package-lint](https://github.com/purcell/package-lint)
library.

Currently these checks are only activated if a `Package-Requires` or
`Package-Version` header is present in the file, and checks center on
the validity of the data in that header.

Installation
------------

You'll need Emacs 24 for `flycheck`, so the recommended way to get
`flycheck-package` is as a package from the [MELPA][melpa]
repository. The version of `flycheck-package` there will always be
up-to-date. There are also packages in [MELPA Stable][melpa-stable], which
track the [latest numbered tag][tags].

If you insist on doing things the hard way, first ensure `flycheck`
and `package-lint` are installed, then download this code and add the
directory to your Emacs `load-path`.

Then, in your `init.el`:

```lisp
(eval-after-load 'flycheck
  '(flycheck-package-setup))
```

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
[COPYING](https://github.com/purcell/flycheck-package/blob/master/COPYING)
for details.

Credits
-------

`flycheck-package` was written by
[Steve Purcell](https://github.com/purcell) with significant
contributions from [Fanael Linithien](https://github.com/Fanael).

<hr>

Author links:

[![](http://api.coderwall.com/purcell/endorsecount.png)](http://coderwall.com/purcell)

[![](http://www.linkedin.com/img/webpromo/btn_liprofile_blue_80x15.png)](http://uk.linkedin.com/in/stevepurcell)

[Steve Purcell's blog](http://www.sanityinc.com/) // [@sanityinc on Twitter](https://twitter.com/sanityinc)

[flycheck]: https://github.com/flycheck/flycheck
[tags]: https://github.com/purcell/flycheck-package/tags
[ledger]: https://ledger-cli.org/
[melpa-stable]: http://stable.melpa.org
[melpa]: http://melpa.org
