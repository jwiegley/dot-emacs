lsp-haskell
===========

[![MELPA](https://melpa.org/packages/lsp-haskell-badge.svg)](https://melpa.org/#/lsp-haskell)

An Emacs Lisp library for interacting with
a [haskell-ide-engine](https://github.com/haskell/haskell-ide-engine/)
server using Microsoft's
[Language Server Protocol](https://github.com/Microsoft/language-server-protocol/).

The library is designed to integrate with existing Emacs IDE frameworks
(completion-at-point, xref (beginning with Emacs 25.1), flycheck, haskell-mode, intero, etc).


*This package is still under development, and is not recommended for daily use.*
## Installation

Clone this repository and https://github.com/emacs-lsp/lsp-mode to suitable paths, and add
```emacs-lisp
(add-to-list 'load-path "<path to lsp-haskell>")
(add-to-list 'load-path "<path to lsp-mode>")
(require 'lsp-haskell)
(require 'lsp-mode)
(add-to-list 'haskell-mode-hook #'lsp-haskell-enable)
```
to your .emacs.

It needs the HIE server in your path, so

```bash
git clone https://github.com/haskell/haskell-ide-engine
cd haskell-ide-engine
stack install
```

