eyebrowse
=========

.. image:: https://raw.github.com/wasamasa/eyebrowse/master/img/eyebrows.gif

About
-----

``eyebrowse`` is a global minor mode for Emacs that allows you to
manage your window configurations in a simple manner, just like tiling
window managers like i3wm with their workspaces do.  It displays their
current state in the modeline by default.  The behaviour is modeled
after `ranger <http://ranger.nongnu.org/>`_, a file manager written in
Python.

Screenshot
----------

.. image:: https://raw.github.com/wasamasa/eyebrowse/master/img/scrot.png

See the lighter and the modeline indicator at the right side of the
bottom modeline?  That's what you get to see after enabling eyebrowse.

Installation
------------

Install via ``package.el`` from the `Marmalade
<https://marmalade-repo.org/>`_ or `MELPA (stable)
<http://melpa.org/>`_ repository by setting them up if you haven't
already and executing ``M-x package-install RET eyebrowse RET``.

Quick Tutorial
--------------

Use ``M-x eyebrowse-mode`` to enable ``eyebrowse`` interactively.  If
you want to enable it automatically on startup, add ``(eyebrowse-mode
t)`` to your init file (either ``~/.emacs`` or
``~/.emacs.d/init.el``).

You start with your current window config on slot 1.  Once you hit
``C-c C-w 2``, you will see the modeline indicator appearing and
showing slot 1 and 2 with slot 2 slightly emphasized.  Slot 1 has been
saved automatically for you and contains your last window config.  Do
something meaningful like a window split, then hit ``C-c C-w 1``.  The
window config on slot 2 is saved and the window config from slot 1 is
loaded.  Try switching back and forth between them with ``C-c C-w '``
to get a feeling for how subsequent window manipulations are handled.

To make keeping track of workspaces easier, a tagging feature was
added.  Use ``C-c C-w ,`` to set a tag for the current window config,
it will both appear in the modeline indicator and when using ``M-x
eyebrowse-switch-to-window-config``.  Setting the tag to an empty
value will undo this change.

Key bindings
------------

The default key bindings are:

============== ================================
Key bind       Function
============== ================================
``C-c C-w <``  Switch to previous window config
``C-c C-w >``  Switch to next window config
``C-c C-w '``  Switch to last window config
``C-c C-w "``  Close current window config
``C-c C-w ,``  Rename current window config
``C-c C-w 0``  Switch to window config ``0``
\...           ...
``C-c C-w 9``  Switch to window config ``9``
============== ================================

Further Customization
---------------------

Use ``M-x customize-group RET eyebrowse`` for a list of customizable
options.  The more interesting ones would be
``eyebrowse-wrap-around`` and ``eyebrowse-switch-back-and-forth``
which affect both wrap around and lazier switching.  It is also
possible to change the behaviour of creation of new workspaces by
customizing ``eyebrowse-new-workspace``.  By default the last one is
simply cloned, setting it to ``t`` will start out with as empty of a
slate as possible (by just displaying a single window with the scratch
buffer in it).

The prefix for each binding defaults to ``C-c C-w``, but you can change
it to something else by customizing ``eyebrowse-keymap-prefix``.  If
you want to change it in your init file, insert the customization
before enabling ``eyebrowse-mode``.

If you're not happy with the default keybindings, a riskier set can be
enabled additionally either by executing ``M-:
(eyebrowse-setup-opinionated-keys)`` interactively or inserting
``(eyebrowse-setup-opinionated-keys)`` in your init file.  If the
function detects the `evil <https://bitbucket.org/lyro/evil/wiki/Home>`_ package, it
will enable extra key bindings for it as well.

The extra key bindings are:

=============== ================================
Key bind        Function
=============== ================================
``C-<``, ``gT`` Switch to previous window config
``C->``, ``gt`` Switch to next window config
``C-'``, ``zx`` Switch to last window config
``C-"``, ``gc`` Close current window config
``M-0``         Switch to window config ``0``
\...            ...
``M-9``         Switch to window config ``9``
=============== ================================

Internals
---------

This mode basically wraps what ``C-x r w`` and ``C-x r j`` would do,
but takes care of automatically saving and loading to a separate data
structure for you and does it in a slightly different manner (see
``window-state-put`` and ``window-state-get`` for more details) to
allow for features like persistency in combination with `desktop.el
<https://www.gnu.org/software/emacs/manual/html_node/emacs/Saving-Emacs-Sessions.html#Saving-Emacs-Sessions>`_.

Notes
-----

The ``window-state-put`` and ``window-state-get`` functions do not
save all window parameters.  If you use features like side windows
that store the window parameters ``window-side`` and ``window-slot``,
you will need to customize ``window-persistent-parameters`` for them
to be saved as well:

.. code:: elisp

    (add-to-list 'window-persistent-parameters '(window-side . writable))
    (add-to-list 'window-persistent-parameters '(window-slot . writable))

See `#52 <https://github.com/wasamasa/eyebrowse/issues/52>`_ for
further discussion.

Contributing
------------

If you find bugs, have suggestions or any other problems, feel free to
report an issue on the issue tracker or hit me up on IRC, I'm always on
``#emacs``.  Patches are welcome, too, just fork, work on a separate
branch and open a pull request with it.

Alternatives
------------

The two most popular window configuration packages are `elscreen
<https://github.com/shosti/elscreen>`_ and `escreen
<https://github.com/emacsmirror/escreen>`_.  Both are fairly old and
have their share of bugs.  The closest package I've found so far to
eyebrowse with workspace-specific buffers would be `perspective
<https://github.com/nex3/perspective-el>`_.  `wconf
<https://github.com/ilohmar/wconf>`_ is a minimal alternative with
half the lines of code (and features).  To have fancy features such
as morphing, try `workgroups <https://github.com/tlh/workgroups.el>`_
or `workgroups2 <https://github.com/pashinin/workgroups2>`_.

Name
----

Actually, I wanted to name this mode "eyebrows" for no real reason,
but then a silly typo happened.  The typo stuck.  So did the new name.
