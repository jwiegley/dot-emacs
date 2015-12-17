# Helm Dash [![Build Status](https://api.travis-ci.org/areina/helm-dash.png?branch=master)](http://travis-ci.org/areina/helm-dash) [![Coverage Status](https://img.shields.io/coveralls/areina/helm-dash.svg)](https://coveralls.io/r/areina/helm-dash?branch=master)

## What's it

This package uses [Dash](http://www.kapeli.com/dash) docsets inside
emacs to browse documentation. Here's an
[article](http://puntoblogspot.blogspot.com.es/2014/01/ann-helm-dash-documentation-browser-for.html)
explaining the basic usage of it.

It doesn't require Dash app.

![](https://raw.github.com/areina/helm-dash/master/misc/helm-dash.gif)

## What's not

If you're looking for dash.el, the list library, please go to
[dash.el](http://www.github.com/magnars/dash.el)


## Requirements

- [helm](https://github.com/emacs-helm/helm)
- sqlite3

## Installation

It's available on [MELPA](https://melpa.org).

Now, it's possible to choose between install the stable or development version
of helm-dash. [Here](https://github.com/milkypostman/melpa#stable-packages)
there is an explanation about stable packages and MELPA and
[here](https://github.com/areina/helm-dash/tags) a list of our tags.

`m-x package-install helm-dash RET`


## Installing docsets

Helm-dash uses the same docsets as [Dash](http://www.kapeli.com/dash).
You can install them with `m-x helm-dash-install-docset` for the
official docsets or `m-x helm-dash-install-user-docset` for user
contributed docsets (experimental).

To install a docset from a file in your drive you can use `m-x
helm-dash-install-docset-from-file'.

## Usage

`m-x helm-dash RET` will run helm with your active docsets
loaded. Typing substrings of what you search will find-as-you-type.

- The search starts from 3 chars.
- Install new docsets with m-x helm-dash-install-docset
- After installing a new docset, add the name of the docset to
  `helm-dash-common-docsets' or in 'helm-dash-docsets' (which is ment
  to be buffer local)

`m-x helm-dash-at-point RET` is like helm-dash, but it will prefill
the search input with the symbol at point.

The command `helm-dash-reset-connections` will clear the connections
to all sqlite db's. Use it in case of errors when adding new docsets.
The next call to `helm-dash` will recreate them.

## Variables to customize

`helm-dash-docsets-path` is the prefix for your docsets. Defaults to ~/.docset

`helm-dash-min-length` tells helm-dash from which length to start
searching. Defaults to 3.

`helm-dash-browser-func` is a function to encapsulate the way to browse
Dash' docsets. Defaults to browse-url. For example, if you want to use eww to
browse your docsets, you can do: `(setq helm-dash-browser-func 'eww)`.

When `helm-dash-enable-debugging` is non-nil stderr from sqlite queries is
captured and displayed in a buffer. The default value is `t`. Setting this
to `nil` may speed up queries on some machines (capturing stderr requires
the creation and deletion of a temporary file for each query).


## Sets of Docsets

### Common docsets

`helm-dash-common-docsets' is a list that should contain the docsets
to be active always. In all buffers.

### Buffer local docsets

Different subsets of docsets can be activated depending on the
buffer. For the moment (it may change in the future) we decided it's a
plain local variable you should setup for every different
filetype. This way you can also do fancier things like project-wise
docsets sets.

``` elisp
(defun go-doc ()
  (interactive)
  (setq-local helm-dash-docsets '("Go")))

(add-hook 'go-mode-hook 'go-doc)
```

### Only one docset

To narrow the search to just one docset, type its name in the
beginning of the search followed by a space. If the docset contains
spaces, no problemo, we handle it :D.

## FAQ

- Does it work in osX?

sqlite queries. Provisionally, we're executing shell-commands directly. Our
idea is come back to use [esqlite](http://www.github.com/mhayashi1120/Emacs-esqlite)
when some issues will be fixed.

helm-dash has been tested only in linux.  We've been notified that it
doesn't work in Mac, so we ask for elisp hackers who own something
that runs Mac OSX if they could take a look at it.

Hints: It looks like something with 'end of line' differences. The
suspicious are
[esqlite](http://www.github.com/mhayashi1120/Emacs-esqlite) (which
helm-dash requires) or
[pcsv](http://www.github.com/mhayashi1120/Emacs-pcsv) (which esqlite
requires)

- I'm using mac osx and pages open but not in the correct anchor

[bug on **mac osx**'s browse-url](https://github.com/areina/helm-dash/issues/36)
which can't open urls with #. If you find this issue, and want to
debug, great, otherwise, you can use eww or w3 or w3m which will work
just fine

- I get nil for every search I do

make sure you don't have sqlite3 .mode column but .mode list (the default). check your .sqliterc

- When selecting an item in helm-dash, no browser lookup occurs with firefox >= 38.0.and emacs >= 24.4

try:
```
(setq browse-url-browser-function 'browse-url-generic
      browse-url-generic-program "/path/to/firefox")
(setq helm-dash-browser-func 'browse-url-generic)
```


## Contribution

We ♥ feedback, issues or pull requests. Feel free to contribute in helm-dash.

We're trying to add tests to the project, if you send a PR please consider add
new or update the existing ones.

Install [Cask](https://github.com/cask/cask) if you haven't already, then:

    $ cd /path/to/helm-dash
    $ cask

Run all tests with:

    $ make


## Authors

- Toni Reina <areina0@gmail.com>
- Raimon Grau <raimonster@gmail.com>
