# erc-image.el #

Show inlined images (png/jpg/gif/svg) in erc buffers.

## Usage

```lisp
(require 'erc-image)
(add-to-list 'erc-modules 'image)
(erc-update-modules)
```

Or `(require 'erc-image)` and  `M-x customize-option erc-modules RET`

This plugin subscribes to hooks `erc-insert-modify-hook` and
`erc-send-modify-hook` to download and show images.


## Credits

* [Raimon Grau](https://github.com/kidd)
* [David Vazquez](https://github.com/davazp)
* [Jon de Andres](https://github.com/jondeandres)
* [Michael Markert](https://github.com/cofi)