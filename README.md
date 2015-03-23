# Company quickhelp

## What is?

One of the things I missed the most when moving from
[auto-complete](https://github.com/auto-complete/auto-complete) to
[company](https://github.com/company-mode) was the documentation
popups that would appear when idling on a completion candidate.  This
package remedies that situation.

[auto-complete](https://github.com/auto-complete/auto-complete) uses
[popup-el](https://github.com/auto-complete/popup-el) to do its thing
and this results in quite a few glitches.  This package uses the much
better [pos-tip](http://www.emacswiki.org/emacs/PosTip) to display the
popups.  I recommend installing `pos-tip` using [MELPA](www.melpa.org)
which fetches the version of `pos-tip` which is located
[here](https://github.com/pitkali/pos-tip/blob/master/pos-tip.el).
This version contains a few bugfixes not included in the original on
[EmacsWiki](http://www.emacswiki.org).

## Installation

I highly recommend installing `company-quickhelp` through `package.el`.

It's available on [MELPA](http://melpa.org/):

    M-x package-install company-quickhelp

## Usage

To activate `company-quickhelp` add the following to your `init.el`:

```elisp
(company-quickhelp-mode 1)
```

You can adjust the time it takes for the documentation to pop up by
changing `company-quickhelp-delay`.

## Customizing

If you hit `M-x customize-group <RET> company-quickhelp <RET>` you'll
find a few variables you can diddle.

## Is it any good?

Yes!

![company-quickhelp](company-quickhelp.png)
