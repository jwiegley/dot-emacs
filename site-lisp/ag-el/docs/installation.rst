Installation
============

Operating System
----------------

ag.el currently works on Linux, Mac and Windows. Patches or bug
reports for other platforms are welcome.

Emacs
-----

We currently support Emacs 23.4 or above, patches for other emacsen
are also welcome.

Ag
---

You will need the ``ag`` binary. See
`the installation instructions <https://github.com/ggreer/the_silver_searcher#installation>`_
on ag's GitHub repo. A
`precompiled Windows binary is also available <http://blog.kowalczyk.info/software/the-silver-searcher-for-windows.html>`_.

Ag.el
-----

Afterwards, you can install ag.el from `MELPA
<http://melpa.milkbox.net/>`_ (the recommended approach).

Functions are autoloaded, so ``(require 'ag)`` is unnecessary.

If you want to install it manually, add the following to your
.emacs.d::

    (add-to-list 'load-path "/path/to/ag.el")
    (require 'ag)


