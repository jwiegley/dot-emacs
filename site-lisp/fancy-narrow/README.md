fancy-narrow [![Donate](https://www.paypalobjects.com/en_US/i/btn/btn_donate_LG.gif)](https://www.paypal.com/cgi-bin/webscr?cmd=_s-xclick&hosted_button_id=B9GT37MB4Y64E)
============

Emacs package to immitate [`narrow-to-region`](http://bruce-connor.github.io/emacs-online-documentation/Fun%2Fnarrow-to-region.html) with more eye-candy.

![Narrowed google-this](https://raw.github.com/Bruce-Connor/fancy-narrow/master/narrowed-google-this.png)

Unlike [`narrow-to-region`](http://bruce-connor.github.io/emacs-online-documentation/Fun%2Fnarrow-to-region.html), which completely hides text outside the narrowed region, this package simply deemphasizes the text, makes it readonly, and makes it unreachable. This leads to a much more natural feeling, where the region stays static (instead of being brutally moved to a blank slate) and is clearly highlighted with respect to the rest of the buffer.

### Installation ###

The easiest way is to install from Melpa.

    M-x package-install fancy-narrow

You can also download this file, open it in emacs, and use `M-x package-install-from-buffer`.

### Usage ###

1. Simply call `fancy-narrow-to-region` to see it in action. To widen the
region again afterwards use `fancy-widen`.

2. If you activate the minor mode (`fancy-narrow-mode`), then the
   standard narrowing keys (`C-x n n`, `C-x n w`, etc) will make use of fancy-narrow.

### Customization ###

To customise the face used to deemphasize unreachable text, customise `fancy-narrow-blocked-face`. 

*Note this is designed for user interaction. For using within lisp code, the standard [`narrow-to-region`](http://bruce-connor.github.io/emacs-online-documentation/Fun%2Fnarrow-to-region.html) is preferable, because the fancy version is susceptible to [`inhibit-read-only`](http://bruce-connor.github.io/emacs-online-documentation/Var/inhibit-read-only.html) and some corner cases.*
