Extensions
============

Using with Projectile
---------------------

`Projectile <https://github.com/bbatsov/projectile>`_ supports ag.el. If
you have Projectile installed, ``C-c p s s`` runs ``ag-regexp`` on your project.

Customising the project root
----------------------------

By default, ``ag-project`` and ``ag-project-regexp`` use the root of the
VCS repo as the directory to search in. You can override this by
setting or customising ``ag-project-root-function``.

Editing the results inline
--------------------------

`wgrep <https://github.com/mhayashi1120/Emacs-wgrep>`_ has support for
ag.el. If you install wgrep-ag
(`available on MELPA <http://melpa.milkbox.net/?#/wgrep-ag>`_), you can
simply run ``wgrep-change-to-wgrep-mode`` and edit the ``*ag*``
buffer. Press ``C-x C-s`` when you're done to make the changes to
buffers.

Writing Your Own
----------------

You can use ``ag``, ``ag-project`` and so on from an elisp
function. ``ag/FOO`` functions are private and are more likely to
change. Please file a bug if you find a use for internal functions
that you can't do otherwise.

