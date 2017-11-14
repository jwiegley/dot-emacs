# ace-link

**GNU Emacs package for selecting a link to jump to**

## What and why

Currently, to jump to a link in an `Info-mode` or `help-mode` or `woman-mode` or `org-mode` or `eww-mode` or `compilation-mode` or `goto-address-mode` buffer, you can tab through the links to select the one you want.  This is an O(N) operation, where the N is the amount of links.  This package turns this into an O(1) operation, or at least O(log(N)) if you manage to squeeze thousands of links in one screen.  It does so by assigning a letter to each link using [avy](https://github.com/abo-abo/avy).

## Install
Either clone from here or install from [MELPA](http://melpa.milkbox.net/) (recommended).

## Setup

Put this in your `~/.emacs`:

    (ace-link-setup-default)

This will bind <kbd>o</kbd> to:

- `ace-link-info` in `Info-mode`
- `ace-link-help` in `help-mode`
- `ace-link-woman` in `woman-mode`
- `ace-link-eww` in `eww-mode`
- `ace-link-compilation` in `compilation-mode`
- `ace-link-custom` in `custom-mode-map`

This shortcut is usually unbound and is very close to <kbd>l</kbd> which is the
default shortcut to go back.

To bind `ace-link-org`, you can use something like this:

    (define-key org-mode-map (kbd "M-o") 'ace-link-org)

To bind `ace-link-gnus`, you can use something like this:

    (define-key gnus-summary-mode-map (kbd "M-o") 'ace-link-gnus)
    (define-key gnus-article-mode-map (kbd "M-o") 'ace-link-gnus)

If you use `ert`, `ace-link-help` also works on `ert` results:

    (require 'ert)
    (define-key ert-results-mode-map "o" 'ace-link-help)

To bind 'ace-link-addr' in all modes (useful when using `goto-address-mode` or `goto-address-prog-mode`):

    (global-set-key (kbd "M-o") 'ace-link-addr)

## Usage

Just press <kbd>o</kbd> when you're in `Info-mode` or `help-mode` or
`woman-mode` or `eww-mode` or `compilation-mode`.

Here's a screencast of browsing Info using `ace-link-info`:

![gif][screencast-1]

[screencast-1]: https://raw.githubusercontent.com/abo-abo/ace-link/gh-pages/screencast-1.gif
