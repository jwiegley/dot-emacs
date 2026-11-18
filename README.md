# dot-emacs

My .emacs file and other personal Emacs goodies.

On Clio, this checkout lives at `~/.config/emacs`. Home Manager owns only
the `nix-packages` and `nix-packages.el` leaves there, not the checkout.
The Makefile still synchronizes `init.org` from `~/org/init.org`; edit that
source before rebuilding `init.el`.

Only configuration lives in this checkout. What Emacs writes while it runs
goes to one of three places, by what it is: data (saved choices, tokens,
tree-sitter grammars) under `$XDG_DATA_HOME/emacs`, state (histories,
recent files, sessions, backups) under `$XDG_STATE_HOME/emacs`, and caches
under `$XDG_CACHE_HOME/emacs`. `lisp/user-paths.el` defines the three roots
and `early-init.el` loads it first. Run `make check-litter` to see whether
anything has crept back.

I keep my Emacs file in literate Org mode, so that it's easier to organize and
also document how things are to be used, since there are enough packages that
I often forget. You can view that document here:

https://github.com/jwiegley/dot-emacs/blob/master/init.org

NOTE: I no longer use git-subtree or submodules for most dependencies.
Instead, packages are built and managed using Nix and Nix overlays:
https://github.com/jwiegley/nix-config/blob/master/overlays/10-emacs.nix

The sole exception is `lisp/llm-setup`, which remains a development submodule.
