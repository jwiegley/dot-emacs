# string-edit.el [![Build Status](https://secure.travis-ci.org/magnars/string-edit.el.png)](http://travis-ci.org/magnars/string-edit.el)

Avoid escape nightmares by editing strings in a separate buffer.

## Installation

I highly recommended installing string-edit through elpa.

It's available on [marmalade](http://marmalade-repo.org/) and
[melpa](http://melpa.milkbox.net/):

    M-x package-install string-edit

You can also install the dependencies on your own, and just dump
string-edit in your path somewhere:

 - <a href="https://github.com/magnars/dash.el">dash.el</a>

## Usage

Call `string-edit-at-point` when inside a string. A new buffer pops
up with unescaped content, letting you edit it directly.

Then press `C-c C-c` to re-escape the content and insert into the
string, or `C-c C-k` to abort.

[![asciicast](https://asciinema.org/a/3040.png)](https://asciinema.org/a/3040)

### JavaScript and HTML

I made this package to edit html templates in javascript code. So it
works a little special there:

 - newlines in the content resolves into multiple concatenated strings.
 - if the content starts with a `<`, html-mode is enabled in the popup buffer.

## Todo

 - string interpolation (handle with intangible overlays?)
 - what's the difference between a newline and a `\n` in an emacs lisp multiline string?
 - setting major-mode for the popup buffer
 - changing major-mode when inside the popup buffer clears all local
   vars, breaking the functionality - any way around that?

## Contribute

Yes, please do. :-)

All changes must be accompanied by feature tests, or I might break it later.
They are written in [Ecukes](http://ecukes.info), a Cucumber for Emacs.

You'll find the repo at:

    https://github.com/magnars/string-edit.el

To fetch the test dependencies, install
[cask](https://github.com/rejeep/cask.el) if you haven't already,
then:

    $ cd /path/to/string-edit
    $ cask

Run the tests with:

    $ ./run-tests.sh

## License

Copyright (C) 2013 Magnar Sveen

Author: Magnar Sveen <magnars@gmail.com>

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
