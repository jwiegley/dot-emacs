Changelog
=========

Previous Versions
-----------------

master
~~~~~~

Replaced calls to ``ido-completing-read`` with
``completing-read``. This allows helm users to use helm completion. To
continue using ido for completion, please install
ido-ubiquitous-mode. This only affects ``ag-files`` and
``ag-project-files``.

Fixed an issue where pressing ``k`` would kill the search results
buffer, even if ``evil-mode`` was active. ``k`` now only kills the
results buffer if you're not using evil.

0.45
~~~~

Fixed another case where ``ag-dired*`` commands ignored ``ag-executable``.

Fixed an issue with ``ag-dired`` where inputs would be quoted twice.

Added ``ag-ignore-list`` which allows you specify patterns to ignore.

Fixed a crash with ``ag-files`` when using a built-in file type.

0.44
~~~~

Fixed a bug with ``ag-dired*`` commands where it ignored
``ag-executable``.

Improved alignment of the output from ``ag-dired*`` commands.

``ag-dired*`` commands now call ``dired-before-readin-hook`` and
``dired-after-readin-hook`` where appropriate.

Fixed a bug with path name escaping in ``ag-dired*`` commands.

Fixed a bug with calling ag on Windows such that you can't jump to
results from the results buffer (you just get 'No Error Here').

Minor docs improvements.

0.43
~~~~

When calling ag with a prefix argument, we now place the point after
the last argument in the minibuffer. See
`#48 <https://github.com/Wilfred/ag.el/issues/48>`_.

Minor docstring improvements.

0.42
~~~~

When passing a prefix argument, ag.el now presents you with the whole
command so you can edit any part, as a string. See
`#38 <https://github.com/Wilfred/ag.el/issues/38>`_.

Documentation and docstring improvements, mostly around clarifying
what regular expression syntax ag.el expects.

0.41
~~~~

Added a setting ``ag-executable`` which allows you to override the name
or path of the ag executable.

Added support for Emacs 23.4.

Buffers created by ag.el are now always named ``*ag: FOO*``.

``ag-dired`` now respects the value of ``ag-reuse-buffers``.

0.40
~~~~

``ag-project-regexp`` now defaults to the escaped value at point, as an
escaped regular expression. For example, if point is at ``foo-bar``,
then the suggested search regexp is ``foo\-bar``.

``ag-regexp-project-at-point`` is now just an obsolete alias for ``ag-project-regexp``.

0.39
~~~~

The commands ``ag``, ``ag-files``, ``ag-regexp``, ``ag-project``,
``ag-project-files`` and ``ag-project-regexp`` can now take a prefix
argument. For example, ``C-u M-x ag``. If given a prefix argument, you
are also prompted for the flags to pass ag itself.

0.38
~~~~

``ag-dired`` and ``ag-project-dired`` should now work on Mac OS X
(previously we assumed xargs supported GNU extensions).

0.37
~~~~

Added ``ag-dired`` and ``ag-project-dired`` to search for files matching a
pattern.

0.36
~~~~

Fixed a bug in ``ag-regexp`` and ``ag-project-regexp`` due to an internal
API change (``ag/search`` now uses keyword arguments).

0.35
~~~~

Added the ``ag-files`` and ``ag-project-files`` commands.

Note that the *internal API changed* in this release: ``ag/search`` now
takes ``regexp`` as a keyword argument instead of a positional
argument. I'm not aware of any external packages depending on this, so
I'm not incrementing the major version.

0.34
~~~~

Specifying the path as an argument to ag, allowing ag.el to do
searches on Windows.

0.33
~~~~

Fixed a bug with ag.el not searching if ``shell-command-switch`` had
been modified by the user.

0.32
~~~~

Adding ``ag-project-root-function`` which allows users to override how
ag.el finds the root of a project.

0.31
~~~~

Ag.el faces (which are ``ag-match-face`` and ``ag-hit-face``x) are defined
with ``defface``, so you can use ``customize-face`` on them.

0.30
~~~~

Improved quoting of arguments passed to ag.

0.29
~~~~

Added customisable variable ``ag-reuse-window``. If set to ``t`` (defaults
to ``nil``) then selecting a search result hides the results buffer and
shows the match, rather than using a different window in the frame.

0.28
~~~~

``-project`` functions now handle the case of multiple nested VCS
repositories. Ag.el now takes the most deepest subdirectory, so if
``/foo/bar`` is a subversion repo that contains a git repo
``/foo/bar/baz``, ag.el will search ``/foo/bar/baz``.

0.27
~~~~

Ag.el autopopulates the minibuffer with the text at point, or the
active selection. If this text was read-only, the minibuffer text
would also be read-only. It's now always possible to edit the text in
the minibuffer.

0.26
~~~~

Fixed a crash when refreshing a search buffer by pressing ``g``.

0.25
~~~~

Added commands ``ag-kill-buffers`` and ``ag-kill-other-buffers`` to
close old search result buffers. Also added a customisable variable
``ag-reuse-buffers`` so users can optionally stop ag.el creating
multiple buffers.

0.24
~~~~

Search results buffers now take the form `*ag text:something
dir:~/some/path*`, so new searches will create new buffers.

0.23
~~~~

ag.el now detects the project root for Mercurial repositories in the
``ag-project*`` commands.

0.22
~~~~

The keys ``n`` and ``p`` now move between matches, similar to the
behaviour of dired.

0.21
~~~~

Added a new face ``ag-hit-face`` to distinguish from ``ag-match-face``.

0.20
~~~~

Fixed ``next-error`` and ``previous-error`` not working with ag.el (broken
in v0.18).

0.19
~~~~

``ag`` now has a default search term of the symbol at point.

0.18
~~~~

Search results are now highlighted as information, rather than
errors. The ag output is now more consistent with grep.el.

0.17
~~~~

The interactive functions provided by ag.el are now autoloaded.

0.16
~~~~

Removed the unused variable ``ag-last-buffer``

0.15
~~~~

Fixed ``ag-project`` and ``ag-project-regexp`` not working in buffers that
aren't associated with a specific file, such as dired and magit buffers.

0.14
~~~~

The compilation mode regexp is now more accurate, so you should no
longer get 'compilation-next-error: No error here' when trying to open
a file in the results list.

0.13
~~~~

Current stable ag (0.13.1) doesn't support ``--color-match``, ag.el now
only highlights when ``ag-highlight-search`` is non-nil (the default is nil).

If you're upgrading ag.el and your ag version is 0.14 or higher, you
need to explicitly enable highlighting::

    (setq ag-highlight-search t)
