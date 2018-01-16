# Syntax based indentation for SQL files for GNU Emacs

[![Build Status](https://travis-ci.org/alex-hhh/emacs-sql-indent.svg?branch=master)](https://travis-ci.org/alex-hhh/emacs-sql-indent)

sql-indent.el is a GNU Emacs minor mode which adds support for syntax-based
indentation when editing SQL code: TAB indents the current line based on the
syntax of the SQL code on previous lines.  This works like the indentation for
C and C++ code.

The package also defines align rules so that the `align` function works for
SQL statements, see `sqlind-align-rules` for which rules are defined.  This
can be used to align multiple lines around equal signs or "as" statements,
like this.

`sqlind-minor-mode` together with the align rules can assist in writing tidy
SQL code or formatting existing SQL code.  The indentation rules are
customizable and they can be adapted to match your coding style.

See the [manual](./sql-indent.org) for more details.

# Installation

You can install a released version of this package
from [GNU ELPA](http://elpa.gnu.org/packages/sql-indent.html), by running the
following commands in Emacs:

    M-x package-install RET sql-indent RET

To install sql-indent from this repository, open the file `sql-indent.el` in
Emacs and type:

    M-x package-install-from-buffer RET

The syntax-based indentation of SQL code can be turned ON/OFF at any time by
enabling or disabling `sqlind-minor-mode`:

    M-x sqlind-minor-mode RET

To enable syntax-based indentation for every SQL buffer, you can add
`sqlind-minor-mode` to `sql-mode-hook`.  First, bring up the customization
buffer using the command:

    M-x customize-variable RET sql-mode-hook RET
    
Than, click on the "INS" button to add a new entry and put "sqlind-minor-mode"
in the text field.

