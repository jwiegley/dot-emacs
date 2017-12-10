====================================
 Kill & Mark Things Easily in Emacs
====================================
 
.. image:: https://travis-ci.org/leoliu/easy-kill.svg?branch=master
   :target: https://travis-ci.org/leoliu/easy-kill
   :align: right
   :alt: Travis CI build status

Provide commands ``easy-kill`` and ``easy-mark`` to let users kill or
mark things easily.

Comments, bug reports and patches are highly appreciated.

easy-kill
~~~~~~~~~

``easy-kill`` is a drop-in replacement for ``kill-ring-save``. To Use:
::

   (global-set-key [remap kill-ring-save] 'easy-kill)

After this configuration, ``M-w`` serves as both a command and a
prefix key for other commands. ``M-w`` alone saves in the order of
active region, url, email and finally current line (See
``easy-kill-try-things``). As a prefix key:

#. ``M-w w``: save word at point
#. ``M-w s``: save sexp at point
#. ``M-w l``: save list at point (enclosing sexp)
#. ``M-w d``: save defun at point
#. ``M-w D``: save current defun name
#. ``M-w f``: save file at point
#. ``M-w b``: save ``buffer-file-name`` or ``default-directory``.
   ``-`` changes the kill to the directory name, ``+`` to full name
   and ``0`` to basename.

The following keys modify the selection:

#. ``@``: append selection to previous kill and exit. For example,
   ``M-w d @`` will append current function to last kill.
#. ``C-w``: kill selection and exit
#. ``+``, ``-`` and ``1..9``: expand/shrink selection
#. ``0`` shrink the selection to the initial size i.e. before any
   expansion
#. ``C-SPC``: turn selection into an active region
#. ``C-g``: abort
#. ``?``: help

For example, ``M-w w`` saves current word, repeat ``w`` to expand the
kill to include the next word. ``5`` to include the next 5 words etc.
The other commands also follow this pattern.

``+``/``-`` does expanding/shrinking according to the thing selected.
So for ``word`` the expansion is word-wise, for ``line`` line-wise,
for ``list`` or ``sexp``, list-wise.

``list-wise`` expanding/shrinking work well in lispy modes (elisp,
Common Lisp, Scheme, Clojure etc.), smie-based modes (Prolog, SML,
Modula2, Shell, Ruby, Octave, CSS, SQL etc.), Org mode, Nxml mode and
Js2 mode.

To copy the enclosing list in lispy modes, I used to do a lot of
``C-M-u C-M-SPC M-w``. Now the key sequence is replaced by ``M-w l``
(save list at point) as shown in `screenshot
<http://i.imgur.com/8TNgPly.png>`_:

.. figure:: http://i.imgur.com/8TNgPly.png
   :target: http://i.imgur.com/8TNgPly.png
   :alt: ``M-w l``

easy-mark
~~~~~~~~~

``easy-mark`` is similar to ``easy-kill`` but marks the region
immediately. It can be a handy replacement for ``mark-sexp`` allowing
``+``/``-`` to do list-wise expanding/shrinking and marks the whole
sexp even when in the middle of one. ::

   (global-set-key [remap mark-sexp] 'easy-mark)

Install
~~~~~~~

``easy-kill`` is part of GNU ELPA and is also available on `MELPA
<https://melpa.org/#/easy-kill>`_.

Extensions
~~~~~~~~~~

New things can be defined by following package ``thingatpt.el``'s
convention, or by defining new functions named like
``easy-kill-on-THING-NAME``. See ``easy-kill-on-buffer-file-name`` and
``easy-kill-on-url`` for examples.

NEWS
~~~~

0.9.4
+++++

#. New user variable ``easy-kill-unhighlight-key``.
#. key ``D`` selects current defun name.

0.9.3
+++++

#. Key ``?`` in ``easy-kill`` or ``easy-mark`` prints help info.
#. ``M-w l`` can select the enclosing string.
#. ``easy-mark`` learns exchanging point & mark.
#. Key ``0`` now sets the selection to its initial size before any
   expansion.
#. ``M-w l``, ``M-w s`` and list-wise ``+/-`` now work in Org mode.

0.9.2
+++++

#. ``-`` can move pass the first selection.
#. ``+``/``-`` on ``sexp`` no longer change ``thing`` to ``list``
#. Mouse over the selection now shows description.
#. Echo js2 node name.
#. Append now uses sensible separator (customisable via
   ``easy-kill-alist``).
#. The format of easy-kill-alist has changed. The old ``(CHAR .
   THING)`` format is still supported but may be removed in future.

Bugs
~~~~

https://github.com/leoliu/easy-kill/issues
