=========================================================
 Emacs frontend to GNU Global source code tagging system
=========================================================

This package is part of `GNU ELPA <http://elpa.gnu.org>`_ (``M-x
list-packages``) and is also available on `MELPA
<http://melpa.milkbox.net/#/ggtags>`_.

The goal is to make working with GNU Global in Emacs as effortlessly
and intuitively as possible and to integrate tightly with standard
emacs packages. ``ggtags.el`` is tested in emacs 24.1, 24.2, 24.3,
24.4 and trunk. Patches, feature requests and bug reports are welcome.
Thanks.

Features
~~~~~~~~

#. Build on ``compile.el`` for asynchronicity and its large
   feature-set.
#. Automatically update Global's tag files when needed with tuning for
   large source trees.
#. Intuitive navigation among multiple matches with mode-line display
   of current match, total matches and exit status.
#. Read tag with completion.
#. Show definition at point.
#. Jump to #include files.
#. Support search history and saving a search to register/bookmark.
#. Query replace.
#. Manage Global's environment variables on a per-project basis.
#. Highlight (definition) tag at point.
#. Abbreviated display of file names.
#. Support all Global search backends: ``grep``, ``idutils`` etc.
#. Support `exuberant ctags <http://ctags.sourceforge.net/>`_ backend.
#. Support all Global's output formats: ``grep``, ``ctags-x``,
   ``cscope`` etc.
#. Support projects on remote hosts (e.g. via ``tramp``).
#. Support eldoc.
#. Search ``GTAGSLIBPATH`` for references and symbols.

Screenshot
~~~~~~~~~~

.. figure:: http://i.imgur.com/wx8ZPGe.png
   :width: 500px
   :target: http://i.imgur.com/wx8ZPGe.png
   :alt: ggtags.png

Why GNU Global
~~~~~~~~~~~~~~

The opengrok project composed a feature comparison `table
<https://github.com/OpenGrok/OpenGrok/wiki/Comparison-with-Similar-Tools>`_
between a few tools.

Install Global and plugins
~~~~~~~~~~~~~~~~~~~~~~~~~~

1. Compile and install Global with ``exuberant-ctags``
   ::

     ./configure --prefix=<PREFIX> --with-exuberant-ctags=/usr/local/bin/ctags
     make && make install

   The executable ``ctags`` is unfortunately named because ``emacs`` also
   includes a command of the same name. So make sure it is from
   http://ctags.sourceforge.net. See ``plugin-factory/README`` in GNU
   Global source for further information.

2. Install ``pygments`` plugin

   The ``pygments`` plugin has been included in ``global`` since
   version ``6.3.2``. ``pip install pygments`` is the only step
   required. Note the plugin is not activated by the default
   ``gtags.conf`` or ``.globalrc``. See
   ``global/plugin-factory/PLUGIN_HOWTO.pygments`` for details.

   The following instructions are for older ``global``.
   ::

     pip install pygments
     git clone https://github.com/yoshizow/global-pygments-plugin.git
     cd global-pygments-plugin/
     sh reconf.sh
     ./configure --prefix=<PREFIX> --with-exuberant-ctags=/usr/local/bin/ctags
     make && make install
     cp sample.globalrc $HOME/.globalrc

   Make sure the value of ``<PREFIX>`` agree with step 1.

Config
~~~~~~

Global with ``exuberant-ctags`` and ``pygments`` plugins can support
dozens of programming languages. For example, to enable
``ggtags-mode`` for C/C++/Java modes::

    (add-hook 'c-mode-common-hook
              (lambda ()
                (when (derived-mode-p 'c-mode 'c++-mode 'java-mode)
                  (ggtags-mode 1))))

Also see https://github.com/leoliu/ggtags/wiki for more examples.

Usage
~~~~~

Open any file in a project and type ``M-x ggtags-mode``. Use ``M-.``
(``ggtags-find-tag-dwim``) to find the tag at point. If the project
has not been indexed (i.e. no ``GTAGS`` file exists), ``ggtags`` will
ask for the project root directory and index it recursively.
Alternatively one can invoke ``ggtags-create-tags`` to index a
directory. The mode line will display the directory name next to the
buffer name. If point is at a valid definition tag, it is underlined.

``ggtags`` is similar to the standard ``etags`` package. For example
these keys ``M-.``, ``M-,``, ``M-*`` and ``C-M-.`` should work as
expected in ``ggtags-mode``.

The following search commands are available:

ggtags-find-tag-dwim

   Find a tag by context.

   If point is at a definition tag, find references, and vice versa.
   If point is at a line that matches ``ggtags-include-pattern``, find
   the include file instead.

   To force finding a definition tag, call it with a prefix (``C-u``).

ggtags-find-tag-mouse

   Like ``ggtags-find-tag-dwim`` but suitable for binding to mouse
   events.

ggtags-find-definition

   Find definition tags. With ``C-u`` ask for the tag name with
   completion.

ggtags-find-reference

   Find reference tags. With ``C-u`` ask for the tag name with completion.

ggtags-find-other-symbol

   Find tags that have no definitions. With ``C-u`` ask for the tag
   name with completion.

ggtags-find-tag-regexp

   Find definition tags matching a regexp. By default it lists all
   matching tags in the project. With ``C-u`` restrict the lists to a
   directory of choice.

ggtags-idutils-query

   Use idutils to find matches.

ggtags-grep

   Grep for lines matching a regexp. This is usually the slowest.

ggtags-find-file

   Find a file from all the files indexed by ``gtags``.

ggtags-query-replace

   Do a query replace in all files found in a search.

Handling multiple matches
+++++++++++++++++++++++++

When a search finds multiple matches, a buffer named
``*ggtags-global*`` is popped up and ``ggtags-navigation-mode`` is
turned on to facilitate locating the right match.
``ggtags-navigation-mode`` makes a few commands in the
``*ggtags-global*`` buffer globally accessible:

``M-n``

   Move to the next match.

``M-p``

   Move to the previous match.

``M-}``

   Move to next file.

``M-{``

   Move to previous file.

``M-=``

   Move to the file where navigation session starts.

``M-<``

   Move to the first match.

``M->``

   Move to the last match.

``C-M-s`` or ``M-s s``

   Use ``isearch`` to find the match.

``RET``

   Found the right match so exit navigation mode. Resumable by ``M-,``
   (``tags-loop-continue``).

``M-*``

   Abort and go back to the location where the search was started.

Miscellaneous commands
++++++++++++++++++++++

Commands are avaiable from the ``Ggtags`` menu in ``ggtags-mode``.

ggtags-prev-mark

   Move to the previously (older) visited location. Unlike ``M-*``
   this doesn't delete the location from the tag ring.

ggtags-next-mark

   Move to the next (newer) visited location.

ggtags-view-tag-history

   Pop to a buffer listing all visited locations from newest to
   oldest. The buffer is a next error buffer and works with standard
   commands ``next-error`` and ``previous-error``. In addition ``TAB``
   and ``S-TAB`` move to next/prev entry, and ``RET`` visits the
   location. ``M-n`` and ``M-p`` move to and display the next/previous
   entry.

ggtags-view-search-history

   View or re-run past searches as kept in
   ``ggtags-global-search-history``.

ggtags-kill-file-buffers

   Kill all file-visiting buffers of current project.

ggtags-toggle-project-read-only

   Toggle opening files in ``read-only`` mode. Handy if the main
   purpose of source navigation is to read code.

ggtags-visit-project-root

   Open the project root directory in ``dired``.

ggtags-delete-tags

   Delete the GTAGS, GRTAGS, GPATH and ID files of current project.

ggtags-explain-tags

  Explain how each file is indexed in current project.

ggtags-browse-file-as-hypertext

   Use ``htags`` to generate HTML of the source tree. This allows
   browsing the porject in a browser with cross-references.

Integration with other packages
+++++++++++++++++++++++++++++++

* eldoc

  ``Eldoc`` support is set up by default on emacs 24.4+. For older
  versions set, for example, in the desired major mode:

  ::

     (setq-local eldoc-documentation-function #'ggtags-eldoc-function)

* imenu

  Emacs major modes usually have excellent support for ``imenu`` so
  this is not enabled by default. To use:
  ::

    (setq-local imenu-create-index-function #'ggtags-build-imenu-index)

* hippie-exp
  ::

     (setq-local hippie-expand-try-functions-list
                 (cons 'ggtags-try-complete-tag hippie-expand-try-functions-list))

* company

  ``company`` can use ``ggtags`` as completion source via
  ``company-capf`` which is enabled by default.

* helm

  If ``helm-mode`` is enabled ``ggtags`` will use it for completion if
  ``ggtags-completing-read-function`` is nil.

NEWS
~~~~

(devel) 0.8.10
++++++++++++++

#. Tags update on save is configurable by ``ggtags-update-on-save``.
#. New command ``ggtags-explain-tags`` to explain how each file is
   indexed in current project. Global 6.4+ required.

[2015-01-16 Fri] 0.8.9
++++++++++++++++++++++

#. ``ggtags-visit-project-root`` can visit past projects.
#. ``eldoc`` support enabled for emacs 24.4+.

[2014-12-03 Wed] 0.8.8
++++++++++++++++++++++

#. Command ``ggtags-update-tags`` now runs in the background for large
   projects (per ``ggtags-oversize-limit``) without blocking emacs.

[2014-11-10 Mon] 0.8.7
++++++++++++++++++++++

#. New navigation command ``ggtags-navigation-start-file``.
#. New variable ``ggtags-use-sqlite3`` to enable sqlite3 storage.

[2014-09-12 Fri] 0.8.6
++++++++++++++++++++++

#. ``ggtags-show-definition`` shows definition with font locking.

[2014-06-22 Sun] 0.8.5
++++++++++++++++++++++

#. New command ``ggtags-find-tag-mouse`` for mouse support.
#. New command ``ggtags-find-definition``.
#. Variable ``ggtags-completing-read-function`` restored.
#. ``ggtags-navigation-isearch-forward`` can also be invoked using
   ``M-s s``.
#. Command ``ggtags-global-rerun-search`` renamed to
   ``ggtags-view-search-history``.
#. The output buffer from ``ggtags-view-search-history`` looks
   cleaner.
#. Search history items can be re-arranged with ``C-k`` and ``C-y``.

[2014-05-06 Tue] 0.8.4
++++++++++++++++++++++

#. ``M-.`` (``ggtags-find-tag-dwim``) is smarter on new files.
#. Always update tags for current file on save.
#. Can continue search ``GTAGSLIBPATH`` if search turns up 0 matches.
   Customisable via ``ggtags-global-search-libpath-for-reference``.

[2014-04-12 Sat] 0.8.3
++++++++++++++++++++++

#. Tweak mode-line ligter in ``ggtags-navigation-mode``.

[2014-04-05 Sat] 0.8.2
++++++++++++++++++++++

#. Default ``ggtags-auto-jump-to-match`` to ``history``.
#. Add eldoc support; see ``ggtags-eldoc-function``.
#. Improved support for tramp.

[2014-03-30 Sun] 0.8.1
++++++++++++++++++++++

#. Improve ``ggtags-view-tag-history`` and tag history navigation.
#. New customsable variable ``ggtags-global-use-color``.
#. Automatically jump to match from location stored in search history.
   See ``ggtags-auto-jump-to-match``.
#. Rename ``ggtags-supress-navigation-keys`` to
   ``ggtags-enable-navigation-keys`` with a better way to suppress
   navigation key bindings in some buffers including
   ``*ggtags-global*`` buffer.

[2014-03-24 Mon] 0.8.0
++++++++++++++++++++++

#. Record search history and re-run past searches.
#. Bookmark or save search to register.
#. New command ``ggtags-show-definition``.
#. Project name on mode line.
#. Automatically use ``.globalrc`` or ``gtags.conf`` file at project
   root.
#. Better completion based on tag types.
#. Use colored output to get column number for jumping to tag.
#. Improve detection of stale GTAGS file based on file modification
   time.
#. New customisable variables ``ggtags-executable-directory``,
   ``ggtags-global-always-update``, ``ggtags-mode-sticky`` and
   ``ggtags-supress-navigation-keys``.
#. Other bug fixes.

Bugs
~~~~

https://github.com/leoliu/ggtags/issues
