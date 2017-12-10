# Emacs mode for typographical editing

typo.el includes two modes, `typo-mode` and `typo-global-mode`.

`typo-mode` is a buffer-specific minor mode that will change a number
of normal keys to make them insert typographically useful unicode
characters. Some of those keys can be used repeatedly to cycle through
variations. This includes in particular quotation marks and dashes.

`typo-global-mode` introduces a global minor mode which adds the
`C-c 8` prefix to complement Emacs’ default `C-x 8` prefix map.

See the documentation of `typo-mode` and `typo-global-mode` for
further details.

## Quotation Marks

> “He said, ‘leave me alone,’ and closed the door.”

All quotation marks in this sentence were added by hitting the " key
exactly once each. typo.el guessed the correct glyphs to use from
context. If it gets it wrong, you can just repeat hitting the " key
until you get the quotation mark you wanted.

`M-x typo-change-language` lets you change which quotation marks to
use in a single buffer. To change globally, add
`(setq-default typo-language <language>)` to your initialization
files. This is also configurable, in case you want to add your own.

## Dashes and Dots

The hyphen key will insert a default hyphen-minus glyph. On repeated
use, though, it will cycle through the en-dash, em-dash, and a number
of other dash-like glyphs available in Unicode. This means that typing
two dashes inserts an en-dash and typing three dashes inserts an
em-dash, as would be expected. The name of the currently inserted dash
is shown in the minibuffer.

The full stop key will self-insert as usual. When three dots are
inserted in a row, though, they are replaced by a horizontal ellipsis
glyph.

## Other Keys

Tick and backtick keys insert the appropriate quotation mark as well.
The less-than and greater-than signs cycle insert the default glyphs
on first use, but cycle through double and single guillemets on
repeated use.

## Prefix Map

In addition to the above, typo-global-mode also provides a
globally-accessible key map under the `C-c 8` prefix (akin to Emacs’
default `C-x 8` prefix map) to insert various Unicode characters.

In particular, `C-c 8 SPC` will insert a no-break space. Continued use
of SPC after this will cycle through half a dozen different space
types available in Unicode.

Check the mode’s documentation for more details.

## Download and Installation

Download `typo.el` and put it somewhere in your load-path.

Add the following to your .emacs:

```Lisp
(typo-global-mode 1)
(add-hook 'text-mode-hook 'typo-mode)
```

## Ligatures

Unicode supports ligatures (ff, fi, fl, ffi, ffl). This is nice, but
quite a lot of fonts lack support for this. Also, it could be argued
that ligatures should happen as part of the display process, not in
the document. Use ZERO WIDTH NON-JOINER (C-c 8 SPC SPC SPC) to prevent
two characters from being merged like this.

Until fonts widely support ligatures, typo.el will not support
them.
