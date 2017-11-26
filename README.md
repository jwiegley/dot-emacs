# dot-emacs
My .emacs.el file and other personal Emacs goodies

I've switched to using git-subtree to include the dependencies that I rely on,
both because I had so many of them that it was impossible to make sure that
`clone --recursive` always worked, and because I want to preserve the exact
version that my configuration was built against, no matter what may happen
upstream. It also makes it easier for others to clone this setup in its
entirety, even if some of the other repositories should go down.
