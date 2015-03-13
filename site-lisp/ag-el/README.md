# ag.el

[![MELPA](http://melpa.org/packages/ag-badge.svg)](http://melpa.org/#/ag)
[![MELPA Stable](http://stable.melpa.org/packages/ag-badge.svg)](http://stable.melpa.org/#/ag)

Ag.el allows you to search using `ag` from inside Emacs. You can
filter by file type, edit results inline, or find files.

Ag.el tries very hard to be Do-What-I-Mean, and will make intelligent
suggestions about what to search and which directories to search in.

Documentation: http://agel.readthedocs.org/en/latest/index.html

Bugs: https://github.com/Wilfred/ag.el/issues

![screenshot](ag_el_screenshot.png)

## Alternatives

* There's an ag plugin for helm: https://github.com/syohex/emacs-helm-ag

## Todo

* Remove `*-at-point` commands in favour of always defaulting to the
  symbol at point.
* Add aliases for the old command names to ensure backward
  compatibility.
