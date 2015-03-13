Configuration
==============

Highlighting results
--------------------

ag.el supports highlighting results for ag 0.14 or later. Previous
versions of ag don't support the ``--color-match`` argument.

If your version of ag is recent enough, you can add highlighting by
adding the following to your Emacs configuration::

    (setq ag-highlight-search t)

Path to the ag executable
-------------------------

ag.el assumes that the ag executable is in one of the directories on
``exec-path``. Generally, this is sufficient.

However, you may find that you can run ag in a terminal but ag.el
isn't finding the ag executable. This is common on Mac OS X. You'll
need to update ``exec-path`` to match your terminal. The best way to do
this is to install
`exec-path-from-shell <https://github.com/purcell/exec-path-from-shell>`_
(available on MELPA).

Alternatively, you can do this yourself by putting the following code
in your Emacs configuration::

    (defun set-exec-path-from-shell-PATH ()
      "Set up Emacs' `exec-path' and PATH environment variable to match that used by the user's shell.

    This is particularly useful under Mac OSX, where GUI apps are not started from a shell."
      (interactive)
      (let ((path-from-shell (replace-regexp-in-string "[ \t\n]*$" "" (shell-command-to-string "$SHELL --login -i -c 'echo $PATH'"))))
        (setenv "PATH" path-from-shell)
        (setq exec-path (split-string path-from-shell path-separator))))

    (set-exec-path-from-shell-PATH)

Finally, as a last resort, you can specify the path to ag
explicitly. This might be the case if:

- you are are in an environment where, for whatever reason, you
  can't easily change the path to include ag
- you are on windows, where the executable name ends in ``.exe``.
- you have multiple versions of ag or want to use some other
  executable that works the same as ag.

To change the ag executable used::

    (setq ag-executable "C:/Wherever/I/Installed/Ag/ag.exe")

Visiting the results
--------------------

By default, ag.el will open results in a different window in the
frame, so the results buffer is still visible. You can override this
so the results buffer is hidden and the selected result is shown in
its place::

    (setq ag-reuse-window 't)

Overriding the arguments passed to ag
-------------------------------------

ag.el provides a customisable variable ``ag-arguments``.

For temporary changes to arguments, the search commands will prompt
you for arguments if you call them with a prefix argument. For
example, ``C-u M-x ag``.

Hooks
-----

ag.el provides ``ag-mode-hook`` which is run when you start a search.

Multiple search buffers
-----------------------

Ag.el provides the interactive commands for closing old search
buffers:

* ``ag-kill-buffers``
* ``ag-kill-other-buffers``

Alternatively, you can make ag.el reuse the same ``*ag*`` buffer for all
your searches::

    (setq ag-reuse-buffers 't)
