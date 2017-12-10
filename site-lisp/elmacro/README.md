[![MELPA](http://melpa.org/packages/elmacro-badge.svg)](http://melpa.org/#/elmacro)
[![MELPA Stable](http://stable.melpa.org/packages/elmacro-badge.svg)](http://stable.melpa.org/#/elmacro)

# elmacro

Shows keyboard macros or latest interactive commands as emacs lisp.

## Examples

### upcase-last-word

Say you have the following text:

    violets are blue
    roses are red

With the cursor somewhere on the first line. Press the following keys:

<kbd>F3 C-e M-b M-u C-a C-n F4</kbd>

Then doing <kbd>M-x elmacro-show-last-macro upcase-last-word RET</kbd> produces a buffer with:

``` emacs-lisp
(defun upcase-last-word ()
  (interactive)
  (move-end-of-line 1)
  (backward-word 1)
  (upcase-word 1)
  (move-beginning-of-line 1)
  (next-line 1 1))
```

You can now do <kbd>M-x eval-buffer</kbd> followed by <kbd>M-x upcase-last-word</kbd>
or call it from your emacs lisp code.

## Table of Contents

* [Installation](#installation)
* [Commands](#commands)
  * [elmacro-show-last-macro](#elmacro-show-last-macro)
  * [elmacro-show-last-commands](#elmacro-show-last-commands)
  * [elmacro-clear-recorded-commands](#elmacro-clear-recorded-commands)
* [Customization](#customization)
  * [elmacro-processors](#elmacro-processors)
  * [elmacro-show-last-commands-default](#elmacro-show-last-commands-default)
  * [elmacro-additional-recorded-functions](#elmacro-additional-recorded-functions)
  * [elmacro-unwanted-commands-regexps](#elmacro-unwanted-commands-regexps)
  * [elmacro-special-objects](#elmacro-special-objects)
  * [elmacro-debug](#elmacro-debug)
* [Processors](#processors)
  * [elmacro-processor-filter-unwanted](#elmacro-processor-filter-unwanted)
  * [elmacro-processor-prettify-inserts](#elmacro-processor-prettify-inserts)
  * [elmacro-processor-concatenate-inserts](#elmacro-processor-concatenate-inserts)
  * [elmacro-processor-handle-special-objects](#elmacro-processor-handle-special-objects)
* [FAQ](#faq)
  * [org-mode, smartparens, etc](#org-mode-smartparens-etc)
  * [Mouse events](#mouse-events)
* [Contributions welcome!](#contributions-welcome)

## Installation

The recommended way to install elmacro is through [MELPA](https://github.com/milkypostman/melpa).

Otherwise, simply add `elmacro.el` to your load-path and then `(require 'elmacro)`.

To enable elmacro, do <kbd>M-x elmacro-mode</kbd> or enable it from your config file like this:

``` emacs-lisp
(elmacro-mode)
```

## Commands

### elmacro-show-last-macro

<kbd>M-x elmacro-show-last-macro</kbd> shows your latest macro as emacs lisp.

In order to use this, you must firt record a
[keyboard macro](https://www.gnu.org/software/emacs/manual/html_node/emacs/Keyboard-Macros.html).
Then, when you do <kbd>M-x elmacro-show-last-macro</kbd> it will ask
you for a defun name and show the latest macro as emacs lisp.

### elmacro-show-last-commands

<kbd>M-x elmacro-show-last-commands</kbd> shows your latest emacs activity as emacs lisp.

This is basically a better version of `kmacro-edit-lossage`.

The default number of commands shown is modifiable in variable
[elmacro-show-last-commands-default](#elmacro-show-last-commands-default).

You can also modify this number by using a numeric prefix argument or
by using the universal argument, in which case it’ll ask for how many
in the minibuffer.

### elmacro-clear-recorded-commands

Clears the list of recorded commands.

## Customization

### elmacro-processors

_Default value:_ `(elmacro-processor-filter-unwanted elmacro-processor-prettify-inserts elmacro-processor-concatenate-inserts elmacro-processor-handle-special-objects)`

List of [processors](#processors) functions used to improve code listing.

Each function is passed the list of commands meant to be displayed and
is expected to return a modified list of commands.

### elmacro-show-last-commands-default

_Default value:_ `30`

Number of commands shown by default in [elmacro-show-last-commands](#elmacro-show-last-commands).

### elmacro-additional-recorded-functions

_Default value:_ `(copy-file copy-directory rename-file delete-file make-directory)`

List of non-interactive functions that you also want to be recorded.

For example, `dired-copy-file` (`C` key in dired)
doesn't reads its arguments as an interactive specification, and
thus the file name is never stored.

### elmacro-unwanted-commands-regexps

_Default value:_ `("^(ido.*)$" "^(smex)$")`

Regexps used to filter unwanted commands.

### elmacro-special-objects

_Default value:_

``` emacs-lisp
'(("#<frame [^0]+\\(0x[0-9a-f]+\\)>" ",(elmacro-get-frame \"\\1\")")
  ("#<window \\([0-9]+\\)[^>]+>"     ",(elmacro-get-window \\1)")
  ("#<buffer \\([^>]+\\)>"           ",(get-buffer \"\\1\")"))
```

List of `(regexp replacement)` for special objects.

This will be used as arguments for `replace-regexp-in-string`.

### elmacro-debug

_Default value:_ `nil`

Set to true to turn debugging in buffer `* elmacro debug *`.

## Processors

The way elmacro processes commands can be modified using *processors*.

A processor is an emacs lisp function that takes a list the commands
meant to be displayed and is expected to return a modified list of
commands.

For example, a simple processor that filters anything you insert in a buffer:

``` emacs-lisp
(defun filter-insert-processor (commands)
  (--remove (eq 'insert (car it)) commands))
```

### elmacro-processor-filter-unwanted

Remove unwanted commands using [elmacro-unwanted-commands-regexps](#elmacro-unwanted-commands-regexps).

### elmacro-processor-prettify-inserts

Transform all occurences of `self-insert-command` into `insert`.
This filter should be not be enabled with packages that
advice `self-insert-command`, see the [FAQ](#org-mode-smartparens-etc) for more information.

Before:

``` emacs-lisp
(setq last-command-event 97)
(self-insert-command 1)
(setq last-command-event 98)
(self-insert-command 1)
(setq last-command-event 99)
(self-insert-command 3)
```

After:

``` emacs-lisp
(insert "a")
(insert "b")
(insert "ccc")
```

### elmacro-processor-concatenate-inserts

Concatenate multiple text insertion together.

Before:

``` emacs-lisp
(insert "a")
(insert "b")
(insert "c")
```

After:

``` emacs-lisp
(insert "abc")
```

### elmacro-processor-handle-special-objects

Turn special objects into usable objects using [elmacro-special-objects](#elmacro-special-objects).

## FAQ

### org-mode, smartparens, etc

Normally `elmacro` works reasonably well with these, but if you want to ensure the most accurate experience you should
disable the [elmacro-processor-prettify-inserts](#elmacro-processor-prettify-inserts) processor (see [elmacro-processors](#elmacro-processors)).

This is necessary because these packages usually advice `self-insert-command`, and by transforming
it into an `insert` the advice does not run and we miss functionnality.

### Mouse events

A nice addition to normal macros is that mouse events (clicks / scroll)
are also recorded and elmacro can figure which emacs window / frame was the target.

For example, by default clicking in a window will generate code like:

``` emacs-lisp
(mouse-set-point '(mouse-1 (#<window 75 on foo.el> 913 (90 . 286) 185432429 nil 913 (10 . 15) nil (90 . 1) (9 . 19))))
```

We see that the `<#window 75 on foo.el>` part is not very useful.
Thanks to the processor [elmacro-processor-handle-special-objects](#elmacro-processor-handle-special-objects), the following code is generated
instead (`elmacro-get-window` is a helper that returns the correct emacs window object):

``` emacs-lisp
(mouse-set-point `(mouse-1 (,(elmacro-get-window 75) 913 (90 . 286) 185432429 nil 913 (10 . 15) nil (90 . 1) (9 . 19))))
```

## Contributions welcome!

Either as suggestions or as pull requests by opening tickets on the
[issue tracker](https://github.com/Silex/elmacro/issues).
