# HaRe : The Haskell Refactorer

[![Available on Hackage][badge-hackage]][hackage]
[![License BSD3][badge-license]][license]
[![Build Status][badge-travis]][travis]

[badge-travis]: https://travis-ci.org/alanz/HaRe.png?branch=master
[travis]: https://travis-ci.org/alanz/HaRe
[badge-hackage]: https://img.shields.io/hackage/v/HaRe.svg?dummy
[hackage]: https://hackage.haskell.org/package/HaRe
[badge-license]: https://img.shields.io/badge/license-BSD3-green.svg?dummy
[license]: https://github.com/alanz/HaRe/blob/master/LICENSE

Note: The current version (0.7.2.8) does not install with GHC 7.8.x

## Roadmap

The token management utilities [haskell-token-utils](https://github.com/alanz/haskell-token-utils)
are too brittle, and will not be updated for GHC 7.8.x and beyond.

There are substantial changes coming in GHC 7.10, which will form the
basis of the new token management, based on
[ghc-exactprint](https://github.com/alanz/ghc-exactprint)

For coming changes in GHC 7.10, see

  * https://ghc.haskell.org/trac/ghc/wiki/GhcApi
  * https://ghc.haskell.org/trac/ghc/wiki/GhcAstAnnotations

## Getting Started

    cabal install HaRe

Check that it works from the command line

    $ ghc-hare --version
    0.7.2.x

Running the bare command lists available refactorings and their parameters

### Emacs integration

Currently only emacs integration is offered. Add the following to your
~/.emacs using the load-path entry that matches the installation on
your machine.

    (add-to-list 'load-path
        "~/.cabal/share/HaRe-0.7.2.2/elisp")
    (add-to-list 'load-path
        "~/.cabal/share/i386-linux-ghc-7.6.3/HaRe-0.7.2.2/elisp")
    (require 'hare)
    (autoload 'hare-init "hare" nil t)

Add an intializer hook to the ghc-mode command

    (add-hook 'haskell-mode-hook (lambda () (ghc-init) (hare-init)))

Alternatively, if using haskell-mode, and initializing via a function

    ;; Haskell main editing mode key bindings.
    (defun haskell-hook ()

      ;(lambda nil (ghc-init))
      (ghc-init)
      (hare-init)
      ...
    )

If this is done correctly, there should be an additional `Refactorer`
menu entry when opening a haskell file. The refactorings can be
initiated via the menu, or using the keyboard shortcuts displayed in
the menu.

The installation can be fine-tuned using

    M-x customize-variable

on

    hare-search-paths
    ghc-hare-command


Each refactoring will first ask for any information it requires, e.g.
a new name if renaming, and then attempt the refactoring. If any
precondition is not met this will be reported and the refactoring will
abort.

If it succeeds, you will be given the option to look at an ediff
session to see what changes would be made, and each file can be
individually accepted or declined.

If the refactoring is commited, the original file is renamed to have a
suffix containing the current timestamp.

E.g., after renaming in Foo.hs, there will be two files

    Foo.hs
    Foo.hs.2013-08-22T19:32:31+0200

This allows a sequence of refactorings to be undone manually if
required. In theory.


## Development & Support

Join in at `#haskell-refactorer` on freenode.

### Developing in sandbox with haskell-token-utils locally

    cabal clean
    cabal sandbox init
    # Next line assumes haskell-token-utils checked out at same level
    cabal sandbox add-source ../haskell-token-utils/
    cabal install --dependencies-only

### Running test suite

To run the test suite do:

    cabal configure --enable-tests && cabal build && cabal test

See <http://hspec.github.com/> for details on hspec

see <http://travis-ci.org/#alanz/HaRe> for continuous build results

## Resources

  * [GHC chapter](http://aosabook.org/en/ghc.html) of
    [AOSA](http://aosabook.org "Architecture of Open Source
    Applications") (if only for the diagram of GHC phases and data structures)
  * [GHC 7.6.3 API docs](http://www.haskell.org/ghc/docs/7.6.3/html/libraries/ghc-7.6.3/GHC.html)
  * [GHC 7.4.2 API docs](http://www.haskell.org/ghc/docs/7.4.2/html/libraries/ghc-7.4.2/GHC.html)
  * [Monoids: Theme and Variations](http://www.cis.upenn.edu/~byorgey/pub/monoid-pearl.pdf) 
    The background to how the dual tree data structure used for token
    output works

## Coding style

Contributors: please try to follow https://github.com/tibbe/haskell-style-guide
Note:A consistent coding layout style is more important than what specific on is used.

## Contributors

 * Simon Thompson
 * Christopher Brown
 * Huiqing Li
 * Alan Zimmerman

Please put a pull request for this list if you are missing.

## Logo

<img src="https://rawgithub.com/alanz/HaRe/master/HaReLogo.svg"
width="400" height="300" />

The logo was designed by Christi du Toit,
<http://www.behance.net/christidutoit>

