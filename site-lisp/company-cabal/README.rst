================================
 company-cabal |travis| |melpa|
================================

`Company-mode`_ completion back-end for haskell-cabal-mode.

Installation
============

Depends
-------
* cl-lib
* `company-mode`_

Setup from MELPA_
-----------------
1. Install from `MELPA`_::

     M-x package-install RET company-cabal RET


2. Add ``company-cabal`` to ``company-backends`` after loading `company-mode`_.

   .. code:: emacs-lisp

     (add-to-list 'company-backends 'company-cabal)


Setup from Git
--------------
1. Install from Git::

     git clone https://github.com/iquiw/company-cabal.git

2. Add ``company-cabal`` to ``company-backends`` after loading `company-mode`_.

   .. code:: emacs-lisp

     (add-to-list 'load-path "/path/to/company-cabal")
     (add-to-list 'company-backends 'company-cabal)


Feature
=======
* Field name completion

  | If field name starts with uppercase character, the completion result is capitalized (e.g. "Cabal-Version").
  | Otherwise, the completion result contains lowercase characters only (e.g. "cabal-version").

* Section name completion

* Some field value completion

  * build-depends (``ghc-pkg list``)
  * build-type
  * default-extensions, extensions, other-extensions
    (``ghc --supported-extensions``)
  * ghc-options, ghc-prof-options, ghc-shared-options
    (``ghc --show-options`` if ghc version >= 7.8)
  * hs-source-dirs (current directories)
  * type


Note
====
* No support for brace layout


License
=======
Licensed under GPL 3+ license.

.. _company-mode: http://company-mode.github.io/
.. _MELPA: http://melpa.milkbox.net/
.. |travis| image:: https://api.travis-ci.org/iquiw/company-cabal.svg?branch=master
            :target: https://travis-ci.org/iquiw/company-cabal
.. |melpa| image:: http://melpa.org/packages/company-cabal-badge.svg
           :target: http://melpa.org/#/company-cabal
