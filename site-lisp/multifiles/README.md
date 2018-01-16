# multifiles.el

An initial attempt at "multifiles" as defined
[here](http://www.reddit.com/r/emacs/comments/10gc9u/can_i_have_multiple_parts_of_buffers_in_one_super/).

## Setup

    (require 'multifiles)

## Usage

Bind a key to `mf/mirror-region-in-multifile`, let's say `C-!`. Now
mark a part of the buffer and press it. A new \*multifile\* buffer pops
up. Mark some other part of another file, and press `C-!` again. This
is added to the \*multifile\*.

You can now edit the \*multifile\* buffer, and watch the original files change.
Or you can edit the original files and watch the \*multifile\* buffer change.

Saving the \*multifile\* buffer will save all the original files.

**Warning** This API and functionality is highly volatile.

## License

Copyright (C) 2011 Magnar Sveen

Author: Magnar Sveen <magnars@gmail.com>
Keywords: multiple files

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
