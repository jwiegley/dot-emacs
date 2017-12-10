# What is Origami?

A text folding minor mode for Emacs.

With this minor mode enabled, you can collapse and expand regions of
text.

The actual buffer contents are never changed in any way. This works by
using overlays to affect how the buffer is presented. This also means
that all of your usual editing commands should work with folded
regions. For example killing and yanking folded text works as you
would expect.

There are many commands provided to make expanding and collapsing text
convenient.

# What does it look like?

![origami](http://www.gregsexton.org/images/origami-screen.png)

# How do I install it?

The easiest way is to just use MELPA. For manual installation:

Firstly, origami requires the following dependencies:

* https://github.com/magnars/dash.el
* https://github.com/magnars/s.el

You should install these anyway, they make working with elisp much
more comfortable.

Drop this package somewhere on your load-path or

    (add-to-list 'load-path (expand-file-name "/path/to/origami.el/"))

Then

    (require 'origami)

In a buffer run `M-x origami-mode`, and start experimenting with any
of the supplied origami interactive functions. I recommend binding
these to keys of your choice in the `origami-mode-map`.

There is also `global-origami-mode` if you just want to enable origami
everywhere. For any major-mode that doesn't have explicit support,
origami will use the indentation of the buffer to determine folds.

Origami has been tested on Emacs 24.3, 24.4 and 24.5.

# What can it do?

Origami works by parsing the buffer to determine a fold structure.

The following commands are supplied to move between and manipulate
folds. Those in bold are particularly useful. Many primitives are
provided so that you may compose your own custom functions.

<table>
  <tr>
    <td>origami-open-node</td>
    <td>Open a fold node.</td>
  </tr>

  <tr>
    <td>origami-open-node-recursively</td>
    <td>Open a fold node and all of its children.</td>
  </tr>

  <tr>
    <td>origami-show-node</td>
    <td>Like origami-open-node but also opens parent fold nodes recursively so as to ensure the position where point is is visible.</td>
  </tr>

  <tr>
    <td>origami-close-node</td>
    <td>Close a fold node.</td>
  </tr>

  <tr>
    <td>origami-close-node-recursively</td>
    <td>Close a fold node and all of its children.</td>
  </tr>

  <tr>
    <td>origami-toggle-node</td>
    <td>Toggle open or closed a fold node.</td>
  </tr>

  <tr>
    <td>origami-forward-toggle-node</td>
    <td>Search forward on this line for a node and toggle it open or closed. This makes toggling nodes much more convenient.</td>
  </tr>

  <tr>
    <td><strong>origami-recursively-toggle-node</strong></td>
    <td>Acts like org-mode header collapsing. Cycle a fold between open, recursively open, closed.</td>
  </tr>

  <tr>
    <td>origami-open-all-nodes</td>
    <td>Open every fold in the buffer.</td>
  </tr>

  <tr>
    <td>origami-close-all-nodes</td>
    <td>Close every fold in the buffer.</td>
  </tr>

  <tr>
    <td>origami-toggle-all-nodes</td>
    <td>Toggle open/closed every fold node in the buffer.</td>
  </tr>

  <tr>
    <td><strong>origami-show-only-node</strong></td>
    <td>Close everything but the folds necessary to see the point. Very useful for concentrating on an area of code.</td>
  </tr>

  <tr>
    <td>origami-previous-fold</td>
    <td>Move to the previous fold.</td>
  </tr>

  <tr>
    <td>origami-next-fold</td>
    <td>Move to the end of the next fold.</td>
  </tr>

  <tr>
    <td>origami-forward-fold</td>
    <td>Move to the start of the next fold.</td>
  </tr>

  <tr>
    <td>origami-forward-fold-same-level</td>
    <td>Move to the start of the next fold that is a sibling of the current fold.</td>
  </tr>

  <tr>
    <td>origami-backward-fold-same-level</td>
    <td>Move to the start of the previous fold that is a sibling of the current fold.</td>
  </tr>

  <tr>
    <td><strong>origami-undo</strong></td>
    <td>Undo the last folding operation.</td>
  </tr>

  <tr>
    <td><strong>origami-redo</strong></td>
    <td>Redo the last undone folding operation.</td>
  </tr>

  <tr>
    <td>origami-reset</td>
    <td>Remove all folds from the buffer and reset all origami state. Useful if origami messes up!</td>
  </tr>
</table>

# Does it support my favourite major-mode?

To some degree, yes. Currently out of the box support is provided for:

* C
* C++
* Clojure
* Go
* Java
* Javascript
* PHP
* Perl
* Python
* elisp

Anything not in this list will be folded using indentation. This works
surprisingly well for most major-modes and is great for folding text.

It should be trivial to add support for any language that uses braces
to delimit blocks. Just add to `origami-parser-alist` something like:
`(mode-name . origami-c-style-parser)`. Adding support for another
lisp dialect should be almost as simple. You can also easily define a
parser for anything with start and end delimiters (similar to braces).
Use the `origami-markers-parser` function for this. There's an example
defined for triple-braces in `origami-parser-alist`.

I'm happy to work on parsers for other languages if interest is
expressed. Cut an issue and I'll see what I can do.

You can write your own parser too. An origami parser is a function
that takes a 'create function' and returns a function taking the
string to be parsed. The returned function should return a list of
fold nodes. Fold nodes are created using the passed-in create
function. Here is an example that creates a single fold node:

     (defun my-amazing-parser (create)
       (lambda (content)
         (list (funcall create beginning-of-the-fold-node-point-position ; inclusive
                               end-of-the-fold-node-point-position ; exclusive
                               offset  ; this allows you to show some of the start of the folded text
                               child-nodes))))

While I work on writing better documentation for parsing, I suggest
starting by looking at the current parsers in origami-parsers.el to
see how they work.

# Can I override the folding parser for an individual file?

You most certainly can. Just add a buffer-local variable that
references a key in `origami-parser-alist`. Something like:

    ;; -*- origami-fold-style: triple-braces -*-

This will add fold-marker support to that file.

# How is this different from [yafolding](https://github.com/zenozeng/yafolding.el)?

I wasn't aware of yafolding before writing this. It looks like origami
provides a richer set of functions for manipulating folds. It is also
smarter about folding for the supported modes - yafolding uses
indentation as a folding heuristic.

# How is this different from [hideshow](http://www.emacswiki.org/HideShow)?

Again, origami provides a much richer set of functions for
manipulating folds. I looked at extending hideshow but gave up when I
realised it kept all of its state in the buffer overlays. This makes
it quite difficult to write some of the more complex fold
manipulations.

Origami maintains a data structure representing the folds and provides
a rich library of functions for manipulating it. This makes adding new
folding operations easy.

# How is this different from [folding.el](http://www.emacswiki.org/emacs/folding.el)?

Folding.el uses markers in the buffer to annotate folds. Origami also
supports this and more.

# How is this different from folding implemented by a specific mode?

It's general purpose and concentrates only on providing a great
folding solution. You need only write a parser for origami to get all
of its fold-manipulating features for free.
