=====================================
 Emacs Syntax Highlighting for LaTeX
=====================================

This programs processes TeX source files, adding syntax-highlighting to the
contents of specially-delimited environments and macros.  For example,
``esh2tex`` transforms this block:

.. code:: latex

   %% ESH: c
   \begin{verbatim}
     int main() { return 0; }
   \end{verbatim}

into something like that:

.. code:: latex

   \begin{ESHBlock}
   \-  \color{8CC4FF}{int} \color{FCE94F}{main}() \{ \color{B4FA70}{return} 0; \}
   \end{ESHBlock}

Curious? Check out our `demo PDF`_ and give it a try! Plus, since ESH works with
special comments, your documents remain compatible with plain LaTeX (for more on
this see `Collaborating with authors who do not use ESH`_ below).

.. _demo PDF: https://github.com/cpitclaudel/esh/raw/master/example/reference.pdf


Setup
=====

**Dependencies:** Emacs > 24.2; XeLaTeX (best) or pdfLaTeX; Cask (optional)

**Setup:** Clone the repository somewhere, and add ``<wherever>/bin`` to your
path (alternatively, just call ``<wherever>/bin/esh2tex`` explicitly).  This
program is tested only on GNU/Linux; it has been reported to work on macOS as
well, and to some limited extent on Windows (see `Windows support`_ below).

**Sanity check:** Running ``make`` in the ``example`` directory of the Git repo
should produce a (partially) syntax-highlighted ``example.pdf``.


Quickstart
==========

Create a new file ``minimal.tex`` and write the following:

.. code:: latex

   \documentclass{minimal}
   %% ESH-preamble-here

   \begin{document}
     %% ESH: c
     \begin{verbatim}
     int main() { return 0; }
     \end{verbatim}
   \end{document}

Process with ``esh2tex minimal.tex``, then compile with ``pdflatex
minimal.esh.tex`` or ``xelatex minimal.esh.tex``. Run ``make`` in the
``example/`` directory of the Git repository for a more advanced example.

For larger documents, run ``esh2tex --init`` in a new directory to create a
ready-to-use ESH setup.


Usage
=====

::

  # Create a ready-to-use ESH setup in the current directory
  esh2tex --init

  # Process one or more tex files with embedded code blocks
  esh2tex [<options>...] [<input>.tex...]

  # Process one or more standalone source code listings
  esh2tex --standalone [<options>...] [<input>.py|c|cpp|...]


``<input>.tex`` should be an UTF-8 encoded text file; output goes to
``<input>.esh.tex``. ``--init`` is special; see `Options`_.  ``<input>`` may
also be an arbitrary source file; see ``--standalone``.


In ``<input>``, you may indicate source blocks like this:

.. code:: latex

   %% ESH: <lang>
   \begin{...}
     ...
   \end{...}

``<lang>-mode`` should be the name of an Emacs major mode (in fact, any function
will do, as long as it ends in ``mode``); the name of the environment (``...``)
does not matter.

Additionally, ``<input>`` should load ESH's preamble before ``\begin{document}``.
For simple documents, adding the following special comment to your preamble is
enough (``esh2tex`` will replace it by appropriate set-up code)::

    %% ESH-preamble-here

``esh2tex`` does not load your personal Emacs configuration (though see
``--no-Q``); instead, it looks for a file named ``esh-init.el`` in the current
directory, one of its parents, or ``~/.emacs.d/``.  You can use that file to
chose a different color theme, load extra packages (see `Installing extra
packages`_), and teach ESH about inline macros (see `Inline syntax
highlighting`_).


Options
=======

* ``--usage``, ``--help``

  Show this help.

* ``--init``

  Don't process input files; instead, create a fairly complete ESH setup in the
  current folder, including an basic ``main.tex`` and simple ``Makefile``.

* ``--standalone``

  Treat <input> as a standalone source file: don't look for special ``%% ESH``
  comments, highlight the entire file, and save output to ``<input>.esh.tex``.
  This is convenient for longer source code listings, or if your collaborators
  don't use ESH (see `Collaborating with authors who do not use ESH`_ below).

* ``--persist``

  Leave server running after processing ``<input>.tex``.

* ``--kill-server``

  Kill previously-started instances of the ESH server.  (You usually do not need
  to run this explicitly, since the server resets automatically when you edit
  your ESH configuration).

* ``--stdout``

  Write to stdout, instead of writing to ``<input>.esh.tex``.

* ``--no-cask``

  Normally, when the current directory contains a Cask file and the cask binary
  is in your path, ESH uses ``cask exec emacs`` instead of ``emacs`` to start
  the syntax-highlighting daemon.  With this option, ESH will stick to using
  the plain ``emacs``.

* ``--no-Q``

  Load your full Emacs configuration instead of the ``esh-init.el`` file.  Use
  this option with caution; there are subtle differences between ESH and a
  regular Emacs that can prevent your Emacs configuration from loading properly.
  In general, it's much better to extract just what you need from your
  ``.emacs`` and put it in an ``esh-init.el``, as described below.

* ``--write-preamble``

  Write ``esh-preamble.tex`` to current directory.  This option does not require
  specifying an input file.

* ``--precompute-verbs-map``

  Instead of producing a highlighted version of ``<input>``, produce an auxiliary
  file storing only highlighting information and redefinitions of ``\verb``-like
  commands. See `Precomputed verb maps`_ below.

* ``--debug-on-error``

  Print stack traces for errors.


Notes
=====


* Starting a server can be slow if your configuration file is large.  Use
  ``--persist`` to leave a server running after the first run and reuse it on
  subsequent runs.


Tips and suggestions
====================

All the following tricks, and more, are demonstrated in the
``example/example.tex`` file of the Git repository.

Loading a different theme
-------------------------

To load a different theme, include the following line in your ``esh-init.el``:

.. code:: emacs-lisp

   (load-theme '<theme-name> t) ;; tango, dichromacy, leuven, adwaita...

Inline syntax highlighting
--------------------------

In addition to code blocks, ESH can highlight inline macros.  Since LaTeX
doesn't have inline comments, though, you need to define your own wrappers.
Start by adding the following to your ``esh-init.el``:

.. code:: emacs-lisp

   (esh-latex-add-inline-verb "\\python" 'python-mode)
   (esh-latex-add-inline-verb "\\cpp" 'c++-mode)

These lines teach ESH about two new inline code delimiters, ``\python`` and
``\cpp``.  This lets you use ``\python|yield 1|`` or ``\cpp/*p++ |= *q++/`` in
the body of your documents, and have them syntax-highlighted by ``esh2tex`` in
``python-mode`` and ``c++-mode`` respectively.

If you want the document to remain compatible with plain LaTeX, you can trick
LaTeX into thinking that ``\python`` and ``\cpp`` are aliases of ``\verb``:

.. code:: latex

   \def\python{\verb} % To remain compatible with plain LaTeX
   \def\cpp{\verb}

Using prettification
--------------------

Emacs can render operators using unicode symbols, displaying ``→`` instead of
``->``, for example.  This feature is called ``prettify-symbols-mode``.

To enable it in ESH, add the following to your ``esh-init.el``:

.. code:: emacs-lisp

   (add-hook '<mode>-hook #'prettify-symbols-mode) ;; lisp-mode, perl-mode...

``XeLaTeX`` and ``LuaLaTeX`` are generally better at handling Unicode, but if
you are stuck with ``pdfLaTeX`` we have a workaround (see the `pdfLaTeX tips`_
section).

With ``XeLaTeX`` and ``LuaLaTeX``, you'll probably want to redefine the
``\ESHFallbackFont`` command, too (see below); something like this:

.. code:: latex

   \usepackage{fontspec}
   \newfontfamily{\Symbola}{Symbola}
   \renewcommand{\ESHFallbackFontFamily}{\Symbola}

Inline blocks
-------------

By default, ESH blocks work in vertical mode: they start a new paragraph, and
add vertical space before and after themselves.  If you include them in a
horizontal box, such as a math formula or a subfloat, LaTeX will complain
(``something is wrong -- maybe a missing \item?``).  Think of the difference
between ``\begin{align}`` and ``\begin{aligned}``.

To get a horizontal-mode "inline" block, use the following syntax::

   %% ESHInlineBlock: <lang>
   \begin{...}
     ...
   \end{...}

Installing extra packages
-------------------------

If the languages that you want to highlight are not supported by Emacs out of
the box, use `Cask <https://github.com/cask/cask>`_ to install the corresponding
packages locally.  This is much cleaner and more stable than loading your full
Emacs configuration (in short, ``Cask`` is to Emacs Lisp what ``VirtualEnv`` is
to Python).

The repo's ``example/`` directory uses a Cask file to manage external
dependencies.

Customizing the output
----------------------

All customizations should be placed **after** the ``%% ESH-preamble-here`` line
(or the explicit ``\input{esh-preamble}``).

Changing fonts:

.. code:: latex

   \usepackage{fontspec}

   ;; Use a roman font for code blocks
   \renewcommand{\ESHBlockFontFamily}{\textrm}

   ;; Use Ubuntu Mono for inline code
   \newfontfamily{\UbuntuMono}[Mapping=tex-ansi]{Ubuntu Mono}
   \renewcommand{\ESHInlineFontFamily}{\UbuntuMono}

   ;; Use Symbola for special characters
   \newfontfamily{\Symbola}{Symbola}
   \renewcommand{\ESHFallbackFontFamily}{\Symbola}

Customizing spacing:

.. code:: latex

   ;; Leave two blank lines before and after each code block
   \setlength{\ESHSkip}{2\baselineskip}

Overriding the ``ESHBlock`` environment:

.. code:: latex

   \renewenvironment{ESHBlock}{...}{...}

All these tricks, and more, are demonstrated in the ``example/example.tex``
subfolder of the repository.

Processing standalone source files
----------------------------------

ESH processes the input as a LaTeX source file containing code blocks to
highlight.  To process a plain source file, use the ``--standalone`` option::

    esh2tex --standalone main.py

This is very useful to collaborate with authors who do not use ESH.

Collaborating with authors who do not use ESH
---------------------------------------------

ESH documents can be compiled using plain ``xelatex`` or ``pdflatex``, but then
they won't be highlighted, and there might be small spacing differences.  To
collaborate with non-ESH users, you can instead use the following setup:

* In your main document, replace the ``%% ESH-preamble-here`` line with
  ``\input{esh-preamble}`` and run ``esh2tex --write-preamble`` to save a local
  copy of ESH's preamble.  Make sure to share this file with your collaborators
  (check it in your repository, for example).

* Do not use special ``% ESH`` comments; instead, save your code snippets as
  individual files in a separate ``listings`` directory.  In your document,
  replace code blocks::

     %% ESH: c
     \begin{verbatim}
     int main() {...}
     \end{verbatim}

  by ``\ESHInputBlock``\s::

     \ESHInputBlock{listings/main.c}

  or, if the block appears in a horizontal context (inside of a math formula,
  for example)::

     \ESHInputInlineBlock[t]{listings/main.c}

  (the optional argument indicates the vertical alignment to use -- one of
  ``t``, ``c``, or ``b``)

* Use ESH to highlight your source files::

    esh2tex --standalone listings/main.c

  (this command produces ``listings/main.c.esh.tex``)

* For inline code snippets, use one of the following two approaches:

  + Extract the code to external files, process them with ``--standalone``, and
    use ``\ESHInputInline{snippet.c}`` to include them.  This approach is very
    stable, but cumbersome for small snippets.

  + Use a precomputed verbs map.  Keep your inline snippets as usual in your
    file, make sure that it compiles with the regular ``esh2tex``, then run
    ``esh2tex --precompute-verbs-map <your-file>.tex`` and ``\input`` the
    resulting ``<your-file>.esh-pv.tex``.  See `Precomputed verb maps`_ below
    for more info.

As long as you share the highlighted source files and the ESH preamble with your
co-authors, they won't need to run ESH themselves.

Precomputed verb maps
~~~~~~~~~~~~~~~~~~~~~

The ``--precompute-verbs-map`` flag instructs ESH to generate a table mapping
each inline code snippet in your original LaTeX file to its highlighted
counterpart.  This table is saved under the name ``<your-file>.esh-pv.tex``.
``esh-preamble.tex`` includes the required machinery to manipulate these
mappings, and the generated ``.esh-pv.tex`` file redefines each of your inline
macros to perform the appropriate lookups (ESH learns about your inline macros
from the declarations in your ``esh-init.el``).

This works very well as long as your inline snippets are at the top level of
your file.  If they appear as arguments to another macro, things get tricky
(remember that you can't have ``\verb`` as an argument to a macro, for
catcode-related reasons).  In a nutshell, if you use an inline snippet inside
the argument of another macro, the snippet must contain neither unbalanced
braces nor ``%`` or ``#`` signs (the former will yield "File ended while
scanning use of ...", and the latter an "Illegal parameter number in definition
of \reserved@a." error).  To work around this, you can either use an external
file processed with ``--standalone``, or use ``ESHSavedVerb`` and ``ESHUseVerb``
in conjunction with ``--precompute-verb-map``::

  \begin{ESHSavedVerb}{yuck-yuck}
    \cverb|You can write anything here: %, #, and {{{|
  \end{ESHSavedVerb}

  Here's a reference to the saved verb: \footnote{\ESHUseVerb{yuck-yuck}}

Using ``esh2tex`` with ``org-mode``
-----------------------------------

See `README.org-mode.rst <README.org-mode.rst>`_.

pdfLaTeX tips
-------------

pdfLaTeX is bad at Unicode, but ESH can use its built-in table of (Unicode →
LaTeX command) mappings to substitute unicode characters before pdfLaTeX can see
them and get confused.  For this to work, just add the following to your
``esh-init.el``::

   (setq-default esh-substitute-unicode-symbols t)

If you want to add your own mappings, use the following examples::

    (esh-latex-add-unicode-substitution "∷" "\\ensuremath{::}")
    (esh-latex-add-unicode-substitution "‽" "!\!?")

Some symbols require extra packages, like ``MnSymbol``.

Fixing font issues
------------------

If you're having font issues, try switching to XeLaTeX or LuaLaTeX.  ESH wraps
each non-ASCII character in an ``\ESHSpecialChar{}`` command, which internally
uses ``\ESHFallbackFont`` (by default, this is an alias of ``\ESHFontFamily``).
You may want to redefine that to a font with good Unicode coverage:

.. code:: latex

   \usepackage{fontspec}
   \newfontfamily{\XITSMath}{XITS Math}
   \renewcommand{\ESHFallbackFontFamily}{\XITSMath}

Using a different version of Emacs
----------------------------------

If the Emacs in your path isn't the right one, you can use the ``EMACS``
environment variable to let ESH know about the right one::

  EMACS=/Applications/Emacs.app/Contents/MacOS/Emacs esh2tex your-file.tex

Windows support
---------------

ESH works on Windows, with the following limitations:

* Emacs 25 is required.
* ``--persist`` is not supported.

Debugging
---------

If you run into issues, try getting the example (in the ``example`` folder of
the repository) to work.  If you can't get the example to work, please open
a GitHub issue.

For more advanced debugging, you can load the ``esh`` package into Emacs, and
use ``M-x esh2tex-current-buffer`` on your TeX file.
