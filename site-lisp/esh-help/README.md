# esh-help.el

[![MELPA](http://melpa-stable.milkbox.net/packages/esh-help-badge.svg)](http://melpa-stable.milkbox.net/#/esh-help)
[![MELPA](http://melpa.milkbox.net/packages/esh-help-badge.svg)](http://melpa.milkbox.net/#/esh-help)

This library adds the following help functions and support for Eshell:
* run-help function inspired by Zsh
* eldoc support

You can install it by using `package-install` via [MELPA](http://melpa.milkbox.net/).

To use this package, add these lines to your `.emacs` file:
```elisp
    (require 'esh-help)
    (setup-esh-help-eldoc)  ;; To use eldoc in Eshell
```
And by using `M-x eldoc-mode` in Eshell, you can see help strings
for the pointed command in minibuffer.
And by using `M-x esh-help-run-help`, you can see full help string
for the command.
