Usage
=====

Running a search
----------------

You will now have the following interactive commands available for performing
searches:

* ``ag``
* ``ag-files``
* ``ag-regexp``
* ``ag-project``
* ``ag-project-files``
* ``ag-project-regexp``

``*-project`` commands automatically choose the directory to search,
automatically detecting git, Subversion and Mercurial project roots.

``*-regexp`` commands allow you to specify a PCRE pattern for your
search term.

``*-files`` commands allow you to specify a PCRE pattern for file names
to search in. By default, ag searches in all files. Note that in both
cases, ag ignores files that are ignored by your VCS (e.g. things
mentioned in .gitignore).

The results buffer
------------------

In the search results buffer, you can move between results by pressing
``n`` and ``p``, and you can visit the file by pressing ``<return>`` or
clicking.

You can run the search again by pressing ``g``, close the buffer with ``q``, or kill the buffer with ``k``.

You can activate ``next-error-follow-minor-mode`` with ``C-c C-f``. With
this minor mode enabled, moving in the results buffer will make Emacs
automatically display the search result at point.

If you've [configured wgrep](#editing-the-results-inline) you can use
``C-c C-p`` to make the buffer writable and edit the results inline.

Of course, ``C-h m`` inside a results buffer will show all the
keybindings available to you.

Search for file names
---------------------

``ag`` supports an option ``-g`` that lets you to list file names matching
PCRE patterns. It is analogical to ``find``, but comes with all the nice
features of ``ag`` such as automatically ignoring all the vcs files. You
can search for files matching a pattern using functions

* ``ag-dired``
* ``ag-dired-regexp``
* ``ag-project-dired``
* ``ag-project-dired-regexp``

The results are presented as a ``dired-mode`` buffer. The analogical
interface to ``find`` in emacs is ``find-dired``.
