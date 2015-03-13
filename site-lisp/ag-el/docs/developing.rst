Developing ag.el
================

Contributing to ag.el is just a matter of editing the ag.el file and
sending a pull request on GitHub.

Using flycheck (optional)
-------------------------

If you're using flycheck, you can configure it to check ag.el.

First, you will need to install `Cask <http://cask.readthedocs.org/en/latest/>`_.
You can then install the ag.el dependencies::

    $ cask install

Flycheck will now check ag.el, including arguments of functions in
included libraries.
