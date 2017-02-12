<a href="screenshots.md"><img align="right" src="https://github.com/vermiculus/magithub/raw/master/images/status.png" width="50%" alt="Overview -- the status buffer"/></a>

# Magithub

[![MELPA Status](http://melpa.milkbox.net/packages/magithub-badge.svg)](http://melpa.milkbox.net/#/magithub)
[![MELPA Stable Status](http://melpa-stable.milkbox.net/packages/magithub-badge.svg)](http://melpa-stable.milkbox.net/#/magithub)
[![Build Status](https://travis-ci.org/vermiculus/magithub.svg?branch=master)](https://travis-ci.org/vermiculus/magithub)
[![Gitter](https://badges.gitter.im/vermiculus/magithub.svg)](https://gitter.im/vermiculus/magithub?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

Magithub is a collection of interfaces to GitHub.

Integrated into [Magit][magit] workflows, Magithub allows very easy,
very basic GitHub repository management.  Supported actions from the
status buffer include:

 - `H H` opens the current repo in the browser
 - `H c` pushes brand-new local repositories up to GitHub
 - `H f` creates forks of existing repositories
 - `H p` submits pull requests upstream
 - `H i` creates issues
 - `RET` on an issue open that issue in GitHub
 - `RET` on the CI header takes you to your CI dashboard

Happy hacking!

## Installation

The package can be installed from MELPA.  Otherwise, simply place
`magithub.el` in your `load-path` and `(require 'magithub)`.  Use the
function `magithub-feature-autoinject` to add full Magit workflow
integration.

If you use [use-package][gh-use-package], you should instead use:

```elisp
(use-package magithub
  :after magit
  :config (magithub-feature-autoinject t))
```

For now, Magithub requires the `hub` utility to work -- before trying
to use Magithub, follow the installation instructions
at [hub.github.com][hub].  To force `hub` to authenticate, you can use
`hub browse` in a terminal (inside a GitHub repo).

## Support

I'm gainfully and happily employed with a company that frowns on
moonlighting, so unfortunately I can't accept any donations myself.
Instead, [please direct any and all support to Magit itself][magit-donate]!

## Note

There used to be another `magithub`: [nex3/magithub][old-magithub].
It's long-since unsupported and apparently has many issues
(see [nex3/magithub#11][old-magithub-11]
and [nex3/magithub#13][old-magithub-13]) and
was [removed from MELPA][melpa-1126] some years ago.  If you have it
installed or configured, you may wish to remove/archive that
configuration to avoid name-clash issues.  Given that the package has
been defunct for over three years and is likely abandoned, the present
package's name will not be changing.

[magit]: //www.github.com/magit/magit
[magit-donate]: https://magit.vc/donate
[hub]: //hub.github.com
[gh-use-package]: //github.com/jwiegley/use-package
[old-magithub]: //github.com/nex3/magithub
[old-magithub-11]: //github.com/nex3/magithub/issues/11
[old-magithub-13]: //github.com/nex3/magithub/issues/13
[melpa-1126]: //github.com/melpa/melpa/issues/1126
