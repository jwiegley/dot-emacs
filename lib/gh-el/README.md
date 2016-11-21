[![Build Status](https://travis-ci.org/sigma/gh.el.png?branch=master)](https://travis-ci.org/sigma/gh.el)
[![Coverage Status](https://coveralls.io/repos/github/sigma/gh.el/badge.svg?branch=master)](https://coveralls.io/github/sigma/gh.el?branch=master)

This is a (very early) GitHub client library for Emacs.

This library also allows implementation of the various authentication schemes (password, OAuth).

Implementation is heavily based on EIEIO so that various components can be replaced easily.

Current state:
* basic API v3 handler

* functional password- and oauth-based authentication

* low-level APIs

  * gist (used in separate project http://github.com/defunkt/gist.el )

  * orgs

  * issues

  * pull requests (used in separate project http://github.com/sigma/magit-gh-pulls )

  * repositories

* support for local caching
