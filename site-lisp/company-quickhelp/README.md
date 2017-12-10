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

### What isn't

Since this library relies on `pos-tip`, and I prefer libraries that do
one thing well, `company-quickhelp` will never be extended with
optional terminal support.

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

If you don't want the help popup to appear automatically, but prefer
it to the popup help buffer provided by
[company](https://github.com/company-mode), you can set
`company-quickhelp-delay` to `nil` and manually trigger the popup with
`M-h`.

## Customizing

If you hit `M-x customize-group <RET> company-quickhelp <RET>` you'll
find a few variables you can diddle.
For instance, you can change the help popup text background and foreground colors.

You might also want to put this in your `init.el`:

```el
(eval-after-load 'company
  '(define-key company-active-map (kbd "C-c h") #'company-quickhelp-manual-begin))
```

This gives you a key to manually trigger the help popup, but only when
company is doing its thing.

## Developer corner

By default, `company-quickhelp` displays the contents of the buffer returned by a `doc-buffer` backend call.  To override this default, backends should respond to the `quickhelp-string` command with a string to display instead of the contents of `doc-buffer`.

## Is it any good?

Yes!

![company-quickhelp](company-quickhelp.png)
