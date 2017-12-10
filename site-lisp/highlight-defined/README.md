[![Melpa Status](http://melpa.org/packages/highlight-defined-badge.svg)](http://melpa.org/#/highlight-defined)
[![Melpa Stable Status](http://stable.melpa.org/packages/highlight-defined-badge.svg)](http://stable.melpa.org/#/highlight-defined)

# highlight-defined

`highlight-defined` is an Emacs minor mode that highlights defined
Emacs Lisp symbols in source code.

Currently it recognizes Lisp function, built-in function, macro, face
and variable names.

## Installation

The package is available in [MELPA](http://melpa.org/).

If you have MELPA in `package-archives`, use

    M-x package-install RET highlight-defined RET

If you don't, open `highlight-defined.el` in Emacs and call
`package-install-from-buffer`.

## Usage

To turn it on:

    M-x highlight-defined-mode

To turn it on automatically:

    (add-hook 'emacs-lisp-mode-hook 'highlight-defined-mode)

## Customization

Change the following faces:
 * `highlight-defined-function-name-face`
 * `highlight-defined-builtin-function-name-face`
 * `highlight-defined-special-form-name-face`
 * `highlight-defined-macro-name-face`
 * `highlight-defined-variable-name-face`
 * `highlight-defined-face-name-face`
