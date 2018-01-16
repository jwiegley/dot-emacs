# multifiles.el

An initial attempt at "multifiles" as defined
[here](http://www.reddit.com/r/emacs/comments/10gc9u/can_i_have_multiple_parts_of_buffers_in_one_super/).

## Setup

    (require 'multifiles)

## Usage

Bind a key to `mf/mirror-region-lines-in-multifile`, let's say `C-!`. Now
mark a part of the buffer and press it. A new \*multifile\* buffer pops
up. Mark some other part of another file, and press `C-!` again. This
is added to the \*multifile\*.

You can now edit the \*multifile\* buffer, and watch the original files change.
Or you can edit the original files and watch the \*multifile\* buffer change.

Saving in the \*multifile\* buffer saves all the original files.
