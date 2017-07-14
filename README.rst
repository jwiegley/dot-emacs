==============================
 Company GHC |travis| |melpa|
==============================

.. contents:: Table of Contents
.. sectnum::

Overview
========

| `Company-mode`_ completion back-end for `haskell-mode`_ via `ghc-mod`_.
| It runs when the major mode is derived from `haskell-mode`_.

Installation
============

Depends
-------
* cl-lib
* `company-mode`_
* `ghc-mod`_

  In order to make company-ghc work, ``ghc-comp-init`` needs to be called once.
  It is called by ``ghc-init``, so if you follow `ghc-mod manual`_, there is nothing else to do about it.
  Otherwise (if you don't want to call ``ghc-init``), ensure ``ghc-comp-init`` is called before using company-ghc.

Optional Dependency
-------------------
* `hoogle`_ command and its database (``hoogle data``) for doc-buffer support and hoogle search completion.

Setup from MELPA_
-----------------
1. Install from `MELPA`_

   | :kbd:`M-x package-install RET company-ghc RET`

2. Add ``company-ghc`` to ``company-backends`` after loading `company-mode`_ and `ghc-mod`_

   .. code:: emacs-lisp

     (add-to-list 'company-backends 'company-ghc)

Setup from Git
--------------
1. Install from Git::

     git clone https://github.com/iquiw/company-ghc.git

2. Add ``company-ghc`` to ``company-backends`` after loading `company-mode`_ and `ghc-mod`_

   .. code:: emacs-lisp

     (add-to-list 'load-path "/path/to/company-ghc")
     (add-to-list 'company-backends 'company-ghc)


Feature
=======

Completion
----------
The following completions are available.

1. Pragma names. (``ghc-pragma-names``)

   .. image:: images/pragma.png
      :alt: Completion for pragma

2. Language extensions. (``ghc-language-extensions``)

   .. image:: images/language.png
      :alt: Completion for language extensions

3. GHC option flags. (``ghc-options-flags``)

   .. image:: images/option.png
      :alt: Completion for GHC options

4. Import module names. (``ghc-modules-names``)

   .. image:: images/module.png
      :alt: Completion for import modules

5. Variables and functions in import spec. (``ghc-module-keyword``)

   .. image:: images/impspec.png
      :alt: Completion for import specs

6. Qualified imported keywords.

   .. image:: images/qualified.png
      :alt: Completion for qualified imported keywords

7. Keywords from imported modules.

   .. image:: images/keyword.png
      :alt: Completion for keywords of imported modules

Show type info in minibuffer
----------------------------
* Type info of completion candidate is displayed in minibuffer,
  given by ``ghc-modi browse -d``.

  Only when ``ghc-modi browse -d`` does not provide type info,
  ``company-ghc-show-info`` (``t``, ``oneline`` or ``nomodule``) is used to
  determine how type info given by ``ghc-modi info`` is displayed.

  Default value of ``company-ghc-show-info`` is nil since when ``ghc-modi info`` is called,
  ghc-mod pops up error if the current buffer contains error.

  .. image:: images/showinfo.png
     :alt: Show info in minibuffer (``nomodule``)

Show module name as annotation
------------------------------
* Module name is displayed as completion annotation
  if ``company-ghc-show-module`` is non-nil (default) as in the above images.

Display Hoogle document as doc-buffer
-------------------------------------
* If `hoogle`_ is installed and its database is prepared,
  then pressing :kbd:`<f1>` displays hoogle searched documentation in the doc-buffer.

  .. image:: images/doc-buffer.png
     :alt: Display documentation in docbuffer

Locate source
-------------
* When a function in the local project is selected as completion candidate,
  pressing :kbd:`C-w` (``company-show-location``) shows its source.
  It uses information from ``ghc-mod info``, and works only when ``company-ghc-show-info`` is non-nil.

Special completion command
--------------------------
1. In-module completion (:kbd:`M-x company-ghc-complete-in-module`)

   It takes a module name in minibuffer, and provides candidates from keywords defined in the specified module.
   You can use this as an alternative to ``:browse`` command of GHCi.

   .. image:: images/in-module.png
      :alt: In-module completion

2. Hoogle search completion (:kbd:`M-x company-ghc-complete-by-hoogle`)

   It takes a query text in minibuffer, and provide candidates from `hoogle`_ search results.
   For example, candidates is like the following if the query is ``(a -> b) -> (f a -> f b)``.

   .. image:: images/hoogle-search.png
      :alt: Hoogle search completion

   If you want to get more search results at a time, increase the value of ``company-ghc-hoogle-search-limit`` (default 20).

Note
====
* Currently, company-ghc treats all symbols as completion prefix unless it starts from line beginning.
  This means other back-ends after company-ghc have no chance to provide completion candidates in haskell-mode.

  As of now, if you want to use other back-ends with company-ghc, use grouped back-end like below.

  .. code:: emacs-lisp

     (add-to-list 'company-backends '(company-ghc :with company-dabbrev-code))

* company-ghc add automatic scan module function to local ``after-save-hook``.
  It might cause serious problem if there is a bug in it.
  If you have any trouble at save, turn off autoscan by :kbd:`M-x company-ghc-turn-off-autoscan`.

  If customized variable ``company-ghc-autoscan`` is nil,
  autoscan won't be added to local ``after-save-hook``.

  If scan module is not performed in the buffer, completion by company-ghc does not work properly.
  scan module can be invoked by :kbd:`M-x company-ghc-scan-modules`.

* company-ghc does not try to browse keywords in a module if the module failed
  to be browsed once.

  If you want company-ghc to browse failed modules again,
  use :kbd:`M-x company-ghc-clear-failed-cache`.

  To make all modules browsed again, use :kbd:`M-x company-ghc-clear-all-cache`.


Diagnostic
==========
There are some cases that completion by company-ghc does not work.
If there is something wrong, run :kbd:`M-x company-ghc-diagnose`,
which shows diagnostic info like the following::

   * company-ghc backend found: company-ghc
   * automatic scan module is enabled
   * ghc-boot process has been done
   
   Module                                  Alias               Candidates
   -------------------------------------------------------------------------------
   Data.Maybe                              -                        12
   Data.Map                                M                        111
   Data.Attoparsec.ByteString.Char8        -                        76
   Control.Applicative                     -                        22
   Prelude                                 -                        212

The first item shows if ``company-ghc`` is added to ``company-backends`` or not.

The second item shows if company-ghc auto scan is enabled or not.

The third item shows if ``ghc-boot`` has been processed properly.

The table shows rows of imported module in the current buffer,
its qualified import alias and number of candidates in the module.

If ``company-ghc-autoscan`` is non-nil but company-ghc auto scan is disabled,
it is possibly initialization step of ``company-ghc`` is not performed by some reason.
Check company-ghc configuration. For workaround, run :kbd:`M-x company-ghc-turn-on-autoscan` manually.

If ``ghc-boot`` process has not been done or failed to run,
check ghc-mod configuration (Ref. `ghc-mod manual`_) or whether ``ghc-mod boot`` command from shell or command prompt succeeds in the project directory.

If some module is not in the table, it is possibly bug of company-ghc.

Number of candidates is nil initially, and gets filled when completion for the corresponding module is performed.
If number of candidates is 0 or nil after completion, it might be problem related to ``ghc-mod``.
Try again with setting ``ghc-debug`` to ``t`` and see if there is any error in ``*GHC Debug*`` buffer.


License
=======
Licensed under the GPL 3+ license.

.. _company-mode: https://company-mode.github.io/
.. _haskell-mode: https://github.com/haskell/haskell-mode
.. _ghc-mod: http://www.mew.org/~kazu/proj/ghc-mod/en/
.. _ghc-mod manual: http://www.mew.org/~kazu/proj/ghc-mod/en/preparation.html
.. _haskell-docs: https://github.com/chrisdone/haskell-docs
.. _hoogle: https://hackage.haskell.org/package/hoogle
.. _MELPA: https://melpa.org/
.. |travis| image:: https://api.travis-ci.org/iquiw/company-ghc.svg?branch=master
            :target: https://travis-ci.org/iquiw/company-ghc
.. |melpa| image:: https://melpa.org/packages/company-ghc-badge.svg
           :target: https://melpa.org/#/company-ghc
