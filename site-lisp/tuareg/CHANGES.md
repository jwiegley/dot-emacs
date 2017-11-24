2.1.0 2017-11-10
----------------

* Let <kbd>M-q</kbd> reformat strings (and use only SMIE).
* Do not indent an expression after `;;` (issue #106).
* New face `tuareg-font-double-colon-face` to highlight `;;`.
* For `type … and …`, left-align `and` with `type`.
* Fix indentation of some GADT type definitions.
* Use `prettify-symbols-mode` to turn `+.` into `∔`,… and add a menu
  entry to toggle it.
* Properly indent `type 'a foo = 'a bla = …` (issue #98).
* Properly indent (issue #7):

        module … with module X = Z
                  and type t := C.t

* Support `let exception E in expr` (issue #102).
* Improved highlighting of `val` and `module` in first class module
  expressions.
* Warn if a file inside a `_build` is edited and propose to switch.
* Add a custom face `tuareg-font-lock-label-face` for labels.
* Add option `tuareg-match-patterns-aligned` to allow to choose
  between the two styles:

        function          v.s.        function
        | A                           | A
          | B -> ...                  | B -> ...
        | C -> ...                    | C -> ... "

* Highlight attributes and extension nodes.
* Disable by default and improve the compilation advice—see the new
  variable `tuareg-opam-insinuate` (issue #97).
* New keybinding <kbd>C-cC-w</kbd> and function `tuareg-opam-update-env`
  to update the environment to an opam switch (offering completion).
* Improved highlighting of quoted strings `{|…|}` (issue #89).
* Move after `;;` when evaluating a phrase in the toploop (issue #96).

* ocamldebug:
  - Add support for `completion-at-point`.
  - Highlight the right location even in presence of non-ascii chars
	(issue #80).
  - Make possible to pass argument to ocamldebug (say, paths with `-I`).
  - Make possible to pass argument to the program being debugged (issue #66).
  - Warn if SMIE is disabled.

* New modes `tuareg-jbuild` and `tuareg-opam` with syntax
  highlighting, indentation, and skeletons.

2.0.10
------

* New indentation config var for SMIE: tuareg-indent-align-with-first-arg.
* Many indentation improvements.
* Fixed point jumping in ocamldebug completion (by Darius Foo).
* Improved (var: t) syntax highlighting.
* Color all predefined exceptions with font-lock-builtin-face
* Syntax highlight cppo preprocessor directives.

2.0.9
-----

* Do not activate Tuareg for .mll and .mly files.
* Toplevel prompt is readonly.
* Font-lock code completely rewritten (avoids several hangs).  New faces
  `tuareg-font-lock-module-face', `tuareg-font-lock-constructor-face',
  and `tuareg-font-lock-line-number-face'.
* Non-closed comment does not cause M-q to hang.
* New variables `caml-types-build-dirs' and `caml-types-annot-dir' for
  a more versatile specification of .annot files.  (Submitted back to
  caml-mode.)
* Fix toplevel highlighting of output and errors.
