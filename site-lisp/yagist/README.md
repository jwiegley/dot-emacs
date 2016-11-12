yagist.el -- Yet Another Emacs integration for gist.github.com
==============================================================

Install
=======

    $ cd ~/.emacs.d/vendor
    $ git clone git://github.com/mhayashi1120/yagist.el.git

In your emacs config:

```lisp
(add-to-list 'load-path "~/.emacs.d/vendor/yagist.el")
(require 'yagist)
```

If you want to save encrypted token to ~/.gitconfig install elisp from following url.
And set a variable:

https://github.com/mhayashi1120/Emacs-kaesar/raw/master/kaesar.el

```lisp
(setq yagist-encrypt-risky-config t)
```

Functions
=========

    M-x yagist-list - Lists your gists in a new buffer. Use arrow keys
    to browse, RET to open one in the other buffer.

    M-x yagist-region - Copies Gist URL into the kill ring.
    With a prefix argument, makes a private gist.

    M-x yagist-region-private - Explicitly create a private gist.

    M-x yagist-buffer - Copies Gist URL into the kill ring.
    With a prefix argument, makes a private gist.

    M-x yagist-buffer-private - Explicitly create a private gist.

    M-x yagist-region-or-buffer - Post either the current region, or if mark
    is not set, the current buffer as a new paste at gist.github.com .
    Copies the URL into the kill ring.
    With a prefix argument, makes a private paste.

    M-x yagist-region-or-buffer-private - Explicitly create a gist from the
    region or buffer.

    M-x yagist-minor-mode - Automated POST current buffer contents to gist
	after saving.

    M-x yagist-global-minor-mode - Open the file that under gist repository
    automatically activate `yagist-minor-mode'.

Config
======

Set `yagist-view-gist` to non-nil if you want to view your Gist using
 `browse-url` after it is created.

### OAuth authentication

Get the `Personal API Access Token` from:

https://github.com/settings/applications

Save the token to your ~/.gitconfig :

    $ git config --global github.oauth-token ***************************

Or put following to your .emacs:

```lisp
(setq yagist-github-token "******************************")
```

### Other customizations

     M-x customize-group (yagist)

Meta
====

* Code: `git clone git://github.com/mhayashi1120/yagist.el.git`
* Home: <https://github.com/mhayashi1120/yagist.el>
* Bugs: <https://github.com/mhayashi1120/yagist.el/issues>
* Hosting: melpa
