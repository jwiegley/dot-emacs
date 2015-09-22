===================================
 HYAI |travis| |coveralls| |melpa|
===================================

Overview
========
Hyai is an indentation minor mode for Haskell, written from scratch.
It supports only one style that basically follows Johan Tibell's `Style Guide`_.

Installation
============

Setup from MELPA_
-----------------
1. Install from `MELPA`_::

     M-x package-install RET hyai RET

2. Add ``hyai-mode`` to ``haskell-mode-hook``

   .. code:: emacs-lisp

      (add-hook 'haskell-mode-hook #'hyai-mode)

Setup from GitHub
-----------------
1. Install from GitHub::

     git clone https://github.com/iquiw/hyai.git

2. Add ``hyai-mode`` to ``haskell-mode-hook``

   .. code:: emacs-lisp

      (add-to-list 'load-path "/path/to/hyai")
      (require 'hyai)
      (add-hook 'haskell-mode-hook #'hyai-mode)

Status
======

Supported Style
---------------
* Basic Indentation and ``where``
* Data Declarations
* List Declarations
* Hanging Lambdas (partial)
* Export Lists
* If-then-else clauses (partial)
* Case expressions
* Top-Level Definitions

License
=======
Licensed under the GPL 3+ license.

.. _Style Guide: https://github.com/tibbe/haskell-style-guide
.. _MELPA: http://melpa.org/
.. |travis| image:: https://travis-ci.org/iquiw/hyai.svg?branch=master
            :target: https://travis-ci.org/iquiw/hyai
.. |coveralls| image:: https://coveralls.io/repos/iquiw/hyai/badge.svg?branch=master&service=github
               :target: https://coveralls.io/github/iquiw/hyai?branch=master
.. |melpa| image:: http://melpa.org/packages/hyai-badge.svg
           :target: http://melpa.org/#/hyai
