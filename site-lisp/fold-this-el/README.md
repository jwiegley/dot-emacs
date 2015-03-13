# fold-this.el

Just fold the active region, please.

## How it works

The command `fold-this` visually replaces the current region with `...`.
If you move point into the ellipsis and press enter or `C-g` it is unfolded.

You can unfold everything with `fold-this-unfold-all`.

You can fold all instances of the text in the region with `fold-this-all`.

## Installation

It is available on [marmalade](http://marmalade-repo.org/) and [Melpa](http://melpa.milkbox.net/):

    M-x package-install fold-this

Or just dump it in your load path somewhere and `(require 'fold-this)`

## Setup

I won't presume to know which keys you want these functions bound to,
so you'll have to set that up for yourself. Here's some example code,
which incidentally is what I use:

```cl
(global-set-key (kbd "C-c C-f") 'fold-this-all)
(global-set-key (kbd "C-c C-F") 'fold-this)
(global-set-key (kbd "C-c M-f") 'fold-this-unfold-all)
```

## License

Copyright (C) 2012 Magnar Sveen

Author: Magnar Sveen <magnars@gmail.com>
Keywords: convenience

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
