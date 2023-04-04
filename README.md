# dot-emacs

My .emacs.el file and other personal Emacs goodies.

I keep my Emacs file in literate Org mode, so that it's easier to organize and
also document how things are to be used, since there are enough packages that
I often forget. You can view that document here:

https://github.com/jwiegley/dot-emacs/blob/master/emacs.org

NOTE: I no longer use git-subtree and submodules to track dependencies.
Instead, everything is built and managed using Nix and Nix overlays:
https://github.com/jwiegley/nix-config/blob/master/overlays/10-emacs.nix
