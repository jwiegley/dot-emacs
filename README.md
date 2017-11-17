[![Melpa Status](http://melpa.org/packages/highlight-numbers-badge.svg)](http://melpa.org/#/highlight-numbers)
[![Melpa Stable Status](http://stable.melpa.org/packages/highlight-numbers-badge.svg)](http://stable.melpa.org/#/highlight-numbers)

# highlight-numbers

`highlight-numbers` is an Emacs minor mode that highlights numeric literals
in source code.

## Usage

To turn it on:

    M-x highlight-numbers-mode

To turn it on automatically for `foo-mode`:

    (add-hook 'foo-mode-hook 'highlight-numbers-mode)

To turn it on for most programming modes:

    (add-hook 'prog-mode-hook 'highlight-numbers-mode)

## Customization

The face used for highlighting is `highlight-numbers-number`. By default it
inherits from `font-lock-constant-face`.

Regular expressions used to match the numeric literals are stored in
`highlight-numbers-modelist`.

## Installation

The package is available in [MELPA](http://melpa.org/), so if you
have MELPA in `package-archives`, all you need is

    M-x package-install RET highlight-numbers RET

If you don't, open `highlight-numbers.el` and issue

    M-x package-install-from-buffer
