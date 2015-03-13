# smart-forward.el

smart-forward gives you semantic navigation, building on
[expand-region](https://github.com/magnars/expand-region.el). It is most easily
explained by example:

    function test() {
      return "semantic navigation";
    }

With point at the start of the quotes,

 * `smart-forward` would go to the end of the quotes
 * `smart-backward` would go to the start of `return`, then to the `{`.
 * `smart-up` would go to the `{`
 * `smart-down` would go to the `}`

With point at the start of `function`,

 * `smart-forward` would go to the `}`

With point at the start of `{`,

 * `smart-forward` would go to the `}`
 * `smart-backward` would go to the start of `function`

I use M-up/down/left/right arrows for this.

## Installation

Start by installing
[expand-region](https://github.com/magnars/expand-region.el).

    (require 'smart-forward)
    (global-set-key (kbd "M-<up>") 'smart-up)
    (global-set-key (kbd "M-<down>") 'smart-down)
    (global-set-key (kbd "M-<left>") 'smart-backward)
    (global-set-key (kbd "M-<right>") 'smart-forward)

## Contribute

smart-forward is a thin wrapper around expand-region. Most fixes to
smart-forward belong there.

## License

Copyright (C) 2011 Magnar Sveen

Author: Magnar Sveen <magnars@gmail.com>
Keywords: marking region

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
