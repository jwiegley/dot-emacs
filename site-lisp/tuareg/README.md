[![MELPA](https://melpa.org/packages/tuareg-badge.svg)](https://melpa.org/#/tuareg)
[![LGPL v2](https://img.shields.io/badge/licence-lgpl2-blue.svg)](COPYING)
[![Build Status](https://travis-ci.org/ocaml/tuareg.svg?branch=master)](https://travis-ci.org/ocaml/tuareg)

Tuareg: an Emacs OCaml mode
===========================

This archive contains files to help editing [OCaml](http://ocaml.org/)
code, to highlight important parts of the code, to run an OCaml
toplevel, and to run the OCaml debugger within Emacs.

Contents
--------

`README.md`      — This file.  
`HISTORY`        — Differences with previous versions.  
`tuareg.el`      — A major mode for editing OCaml code in Emacs.  
`ocamldebug.el`  — To run the OCaml debugger under Emacs.  
`sample.ml`      — Sample file to check the indentation engine.

Install
-------

The easier way to install Tuareg is though
[`opam`](http://opam.ocaml.org/):

    opam install tuareg

and follow the instructions given at the end of the `opam`
installation.

There are versions of Tuareg in [Melpa](https://melpa.org/) and
in [Marmalade](https://marmalade-repo.org/) but they may be older.

If you want to install from the Git checkout, just add to your
[Init File][]the line:

    (load "path-to-git-checkout-dir/tuareg-site-file")

If you want to byte compile the files, issue `make elc`.  If you do
this in Darwin, make sure that the version of Emacs displayed at the
end of `make elc` is the sole that you use (the `.elc` files may not
be compatible with other versions of Emacs installed on your system).


Usage & Configuration
---------------------

The Tuareg major mode is triggered by visiting a file with extension
`.ml`, `.mli`, `.mly`, `.mll`, and `.mlp` or manually by
<kbd>M-x tuareg-mode</kbd>.

Start the OCaml toplevel with <kbd>M-x run-ocaml</kbd>.  You can evaluate a
phrase in your buffer by typing <kbd>C-c C-e</kbd> when the cursor is on it (it
will start the OCaml toplevel if needed).

Run the OCaml debugger with <kbd>M-x ocamldebug FILE</kbd>.


Customization
-------------

- By default, Tuareg will align the arguments of functions as follows:

        function_name arg1
                      arg2

  If you prefer that arguments on the second line be indented w.r.t.
  the function name, put `(setq tuareg-indent-align-with-first-arg nil)`
  in your [Init File][].  This may be convenient if you use
  the following style:

        function_name (fun x ->
            do_something
          )
          arg2

  In both cases, if there are no argument on the line following the
  function name, the indentation will be:

        function_name
          arg1
          arg2

- To make easier to distinguish pattern-match cases containing several
  patterns, sub-patterns are slightly indented as in

        match x with
        | A
          | B -> ...
        | C -> ...

  If you prefer all pipes to be aligned as

        match x with
        | A
        | B -> ...
        | C -> ...

  use `(setq tuareg-match-patterns-aligned t)`.

- Emacs ≥ 24.4 turned on [electric-indent-mode][] mode by default.  If
  you do not like it, call `(electric-indent-mode 0)` in
  `tuareg-mode-hook`.

  [electric-indent-mode]: https://www.gnu.org/software/emacs/manual/html_node/emacs/Indent-Convenience.html

- You can turn on and off the rendering of certain sequences of
  characters as symbols (such as `∔` and `∧` instead of `+.`and `&&`),
  use `prettify-symbols-mode` or use the check box in the _Tuareg
  Options_ menu.  To enable it by default when you start Tuareg, add
  the following to your [Init File][]:

        (add-hook 'tuareg-mode-hook
                  (lambda()
                    (when (functionp 'prettify-symbols-mode)
                      (prettify-symbols-mode))))

  If you want more symbols to be prettified (such as `->` being
  displayed as `→`) at the expense of modifying the indentation in
  incompatible ways with those not using that option, add `(setq
  tuareg-prettify-symbols-full t)` to your [Init File][].

Thanks to the work of Stefan Monnier, a new indentation engine based on
[SMIE](https://www.gnu.org/software/emacs/manual/html_node/elisp/SMIE.html)
was written.  This changes the indentation somewhat w.r.t. the
previous versions of `tuareg`.  If you do not want that, you can use
the _old_ indentation engine by adding `(setq tuareg-use-smie nil)` to
your [Init File][].  It is discouraged however as the older
indentation engine will _not_ be updated (unless a PR is submitted)
and will eventually be removed.


The standard Emacs customization tool can be used to configure Tuareg
options.  It is available from the Options menu and Tuareg's Customize
sub-menu.  Note that, at the moment, both customization options
pertaining to the SMIE indentation mode and the old one are present.

You may also customize the appearance of OCaml code by twiddling the
variables listed at the start of tuareg.el (preferably using
`tuareg-mode-hook`, you should not patch the file directly).
You should then add to your configuration file something like:

    (add-hook 'tuareg-mode-hook
      (lambda () ... ; your customization code ))

For example:

    (add-hook 'tuareg-mode-hook
              ;; Turn on auto-fill minor mode.
              (lambda () (auto-fill-mode 1)))

See [dot-emacs.el](dot-emacs.el) for some examples.

[Init File]: https://www.gnu.org/software/emacs/manual/html_node/emacs/Init-File.html


Features, Known Bugs
--------------------

Cf. online help.

Thanks
------

Ian Zimmerman for the previous mode, compilation interface and
debugger enhancement.

Jacques Garrigue enhanced Zimmerman's mode along with an adaptation
to OCaml (and Labl) syntax. Although this work was performed
independently, his useful test file and comments were of great help.

Michel Quercia for excellent suggestions, patches, and helpful
emacs-lisp contributions (full, ready-to-work implementations, I
should say), especially for Tuareg interactive mode, and browser
capacities.

Denis Barthou, Pierre Boulet, Jean-Christophe Filliatre and Rémi
Vanicat for intensive testing, useful suggestions, and help.

Ralf Treinen for maintaining the Debian GNU/Linux package.

Every people who sent me bug reports, suggestions, comments and
patches. Nothing would have improved since version 0.9.2 without
their help. Special thanks to Eli Barzilay, Josh Berdine, Christian
Boos, Carsten Clasohm, Yann Coscoy, Prakash Countcham, Alvarado
Cuihtlauac, Erwan David, Gilles Défourneaux, Philippe Esperet,
Gilles Falcon, Tim Freeman, Alain Frisch, Christian Lindig, Claude
Marché, Charles Martin, Dave Mason, Stefan Monnier, Toby Moth,
Jean-Yves Moyen, Alex Ott, Christopher Quinn, Ohad Rodeh, Rauli
Ruohonen, Hendrik Tews, Christophe Troestler, Joseph Sudish, Mattias
Waldau and John Whitley.

Tuareg mode have been maintained by Albert Cohen until version 1.45.

Jane Street took over maintenance based on Albert Cohen's version 1.46
(later retracted by him), and released its first version as 2.0.

Reporting
---------

The official Tuareg home page is located at:
<https://github.com/ocaml/tuareg>.

Bug reports & patches: use the tracker:
<https://github.com/ocaml/tuareg/issues>.
