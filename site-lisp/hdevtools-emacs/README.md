# About

[hdevtools](https://github.com/bennofs/hdevtools) is a program for rapidly syntax checking/compiling Haskell files, typically used with [flycheck-hdevtools](https://github.com/flycheck/flycheck-hdevtools). This package provides an emacs interface for hdevtools's type-checking functionality.

# Installation

If you have Emacs >= 24, you can install `hdevtools-emacs` via the package `hdevtools` in [MELPA](http://melpa.milkbox.net/).

To install manually, just put `hdevtools.el` somewhere on your `load-path`; using `(require 'hdevtools)` is not necessary, but you can do it if you want.

hdevtools-emacs doesn't export any key bindings by default; you can do something like

     (add-hook 'haskell-mode-hook
               (lambda () (define-key haskell-mode-map (kbd "C-c .")
                            'hdevtools/show-type-info)))
