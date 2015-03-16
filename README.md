# bug-reference-github

Automatically set `bug-reference-url-format` and enable
`bug-reference-prog-mode` buffers from Github repositories.

What it does is: 

1. If `bug-reference-url-format` is not set and this appears to be
    part of a git working copy (we can locate a .git/config).

2. Find the git remote repository (run `git ls-remote --get-url`).

3. If the remote matches github.com set `bug-reference-url-format` to
    the correct Github issue URL (we set it buffer locally).

4. Enable `bug-reference-prog-mode`.

## Installation and usage

The easiest way to install bug-reference-github is probably to install
it via the ELPA archive at
[Marmalade](http://marmalade-repo.org/packages/bug-reference-github) or
[MELPA](http://melpa.milkbox.net/#/bug-reference-github).

ELPA (package.el) is part of Emacs 24. For Emacs 23 see
[Marmalade](http://marmalade-repo.org) for installation instructions.

If you don't install via ELPA make sure that bug-reference-github.el is in
your load-path and require the library

    (add-to-list 'load-path "~/.emacs.d/path/to/bug-reference-github")
    (require 'bug-reference-github)

Then, to use `bug-reference-github` in every opened file:

    (add-hook 'find-file-hook 'bug-reference-github-set-url-format)

Alternatively, you can use `prog-mode-hook`:

    (add-hook 'prog-mode-hook 'bug-reference-github-set-url-format)

## Requirements

bug-reference-github depends on bug-reference.el which is part of
Emacs 23 and greater.

## Development of bug-reference-github

bug-reference-github.el is developed at
[GitHub](https://github.com/arnested/bug-reference-github).  Feature
requests, ideas, bug reports, and pull request are more that welcome!
