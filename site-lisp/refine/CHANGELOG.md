# v0.4

* Added support for editing values in vectors.
* Fixed an issue where `:foo` was formatted as `':foo`.
* Fixed several issues where we showed the global value of a variable,
  instead of its buffer-local value.
* Refine buffers now include a button to take you back to the relevant
  buffer.
* Fixed a crash on inserting values into a `defcustom` a type of
  `'sexp`, such as `mode-line-format`.
* Variable descriptions now inform you if the variable has
  buffer-local bindings.

# v0.3

* Fixed an issue with cycling custom boolean variables.
* Fixed several crashes on reordering list elements.
* When prompting for a variable, refine now defaults the variable at
  point.
* Refine buffers now include links to help and the definition of
  variables.

# v0.2

* Improved pretty-printing of strings.
* For `defcustom` variables which are just lists of symbols, refine
  now offers those values with completion.
* Fixed a crash on variables that are set to strings.
* Fixed an issue inserting values into an empty list.
* Fixed various issues with viewing values set to symbols.
* Fixed an issue with viewing values set to numbers.
* Added the ability to cycle values or list elements within custom
  variables.

# v0.1

Initial relase
