## js3-mode ##

A chimeric fork of js-mode (included with emacs 24) and [js2-mode](https://github.com/mooz/js2-mode/) that supports comma-first style and other quirks.

The goal of this project was to get a javascript mode working that supports [npm style](https://docs.npmjs.com/misc/coding-style), but it turns out this mode is compatible with other styles as well.

Notably, js3-mode does not support js2-mode's bounce-indent, though it does support several popular indentation styles.

Documentation is on the [wiki](https://github.com/thomblake/js3-mode/wiki/).

## Credits ##

Created by [Thom Blake](https://github.com/thomblake).

For more credits, see https://github.com/thomblake/js3-mode/wiki/Credits

## Installation ##

js3.el should be placed in your emacs include path. You'll need to byte-compile js3-mode before using it - in emacs, `M-x byte-compile-file RET <path-to-js3.el> RET`.  Or on the command line: `emacs --batch -f batch-byte-compile js3.el` If you want, js3-mode can be configured using `M-x customize-group RET js3-mode RET`.

For more details, see https://github.com/thomblake/js3-mode/wiki/Installation

## Notes ##

Right now, all commits are the 'current development build' - so far, nothing that feels like a sufficiently stable release exists.  Several features persist from the software this is based on that may or may not be removed in the near future.

If your JS is in error, the indentation might look wrong.  I tend to regard this as a feature.

I use the default settings, plus the following which are turned off by default for historical reasons: (note that they might be annoying if js3-mode doesn't *quite* line up where you want it to)

```elisp
 '(js3-auto-indent-p t)         ; it's nice for commas to right themselves.
 '(js3-enter-indents-newline t) ; don't need to push tab before typing
 '(js3-indent-on-enter-key t)   ; fix indenting before moving on
```

I expect that there are still some bugs; if you see any, **please report them**. Feel free to **file issue reports on github** for things like "it indented like [code block] but I want it to be [code block]".

Remember - if you start a line with `(`, `[`, `+`, or `-`, strongly consider preceding it with a semicolon (`;`).

## License ##

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License as
published by the Free Software Foundation; either version 3 of
the License, or (at your option) any later version.

This program is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied
warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see http://www.gnu.org/licenses/.
