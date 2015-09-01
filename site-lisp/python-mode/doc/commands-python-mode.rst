Python-mode commands

====================

py-guess-pdb-path
-----------------
If py-pdb-path isn't set, find location of pdb.py. 

highlight-indentation-on
------------------------
Make sure `highlight-indentation' is on. 

highlight-indentation-off
-------------------------
Make sure `highlight-indentation' is off. 

highlight-indentation
---------------------
Toggle highlight indentation.
Optional argument INDENT-WIDTH specifies which indentation
level (spaces only) should be highlighted, if omitted
indent-width will be guessed from current major-mode

run-python-internal
-------------------
Run an inferior Internal Python process.
Input and output via buffer named after
`python-shell-internal-buffer-name' and what
`python-shell-internal-get-process-name' returns.  This new kind
of shell is intended to be used for generic communication related
to defined configurations.  The main difference with global or
dedicated shells is that these ones are attached to a
configuration, not a buffer.  This means that can be used for
example to retrieve the sys.path and other stuff, without messing
with user shells.  Runs the hook
`inferior-python-mode-hook' (after the `comint-mode-hook' is
run).  (Type C-h m in the process buffer for a list
of commands.)

python-shell-send-string
------------------------
Send STRING to inferior Python PROCESS.
When `py-verbose-p' and MSG is non-nil messages the first line of STRING.

python-shell-send-region
------------------------
Send the region delimited by START and END to inferior Python process.

python-shell-send-buffer
------------------------
Send the entire buffer to inferior Python process.

python-shell-send-defun
-----------------------
Send the current defun to inferior Python process.
When argument ARG is non-nil sends the innermost defun.

python-shell-send-file
----------------------
Send FILE-NAME to inferior Python PROCESS.
If TEMP-FILE-NAME is passed then that file is used for processing
instead, while internally the shell will continue to use
FILE-NAME.

python-shell-switch-to-shell
----------------------------
Switch to inferior Python process buffer.

python-shell-completion-complete-at-point
-----------------------------------------
Perform completion at point in inferior Python process.

python-shell-completion-complete-or-indent
------------------------------------------
Complete or indent depending on the context.
If content before pointer is all whitespace indent.  If not try
to complete.

py-count-lines
--------------
Count lines in accessible part until current line.

See http://debbugs.gnu.org/cgi/bugreport.cgi?bug=7115

run-python
----------
Run an inferior Python process, input and output via buffer *Python*.

CMD is the Python command to run.  NOSHOW non-nil means don't
show the buffer automatically.

Interactively, a prefix arg means to prompt for the initial
Python command line (default is `python-command').

A new process is started if one isn't running attached to
`python-buffer', or if called from Lisp with non-nil arg NEW.
Otherwise, if a process is already running in `python-buffer',
switch to that buffer.

This command runs the hook `inferior-python-mode-hook' after
running `comint-mode-hook'.  Type C-h m in the
process buffer for a list of commands.

By default, Emacs inhibits the loading of Python modules from the
current working directory, for security reasons.  To disable this
behavior, change `python-remove-cwd-from-path' to nil.

python-send-region
------------------
Send the region to the inferior Python process.

python-send-string
------------------
Evaluate STRING in inferior Python process.

python-send-buffer
------------------
Send the current buffer to the inferior Python process.

python-send-defun
-----------------
Send the current defun (class or method) to the inferior Python process.

python-switch-to-python
-----------------------
Switch to the Python process buffer, maybe starting new process.
With prefix arg, position cursor at end of buffer.

python-send-region-and-go
-------------------------
Send the region to the inferior Python process.
Then switch to the process buffer.

python-load-file
----------------
Load a Python file FILE-NAME into the inferior Python process.
If the file has extension `.py' import or reload it as a module.
Treating it as a module keeps the global namespace clean, provides
function location information for debugging, and supports users of
module-qualified names.

python-set-proc
---------------
Set the default value of `python-buffer' to correspond to this buffer.
If the current buffer has a local value of `python-buffer', set the
default (global) value to that.  The associated Python process is
the one that gets input from M-x python-send-region et al when used
in a buffer that doesn't have a local value of `python-buffer'.

python-fill-paragraph
---------------------
`fill-paragraph-function' handling multi-line strings and possibly comments.
If any of the current line is in or at the end of a multi-line string,
fill the string or the paragraph of it that point is in, preserving
the string's indentation.

python-shift-left
-----------------
Shift lines in region COUNT (the prefix arg) columns to the left.
COUNT defaults to `py-indent-offset'.  If region isn't active, just shift
current line.  The region shifted includes the lines in which START and
END lie.  It is an error if any lines in the region are indented less than
COUNT columns.

python-shift-right
------------------
Shift lines in region COUNT (the prefix arg) columns to the right.
COUNT defaults to `py-indent-offset'.  If region isn't active, just shift
current line.  The region shifted includes the lines in which START and
END lie.

python-mark-block
-----------------
Mark the block around point.
Uses `python-beginning-of-block', `python-end-of-block'.

python-find-imports
-------------------
Find top-level imports, updating `python-imports'.

python-find-function
--------------------
Find source of definition of function NAME.
Interactively, prompt for name.

py-insert-default-shebang
-------------------------
Insert in buffer shebang of installed default Python. 

py-electric-comment
-------------------
Insert a comment. If starting a comment, indent accordingly.

If a numeric argument ARG is provided, that many colons are inserted
non-electrically.
With C-u "#" electric behavior is inhibited inside a string or comment.

py-electric-colon
-----------------
Insert a colon and indent accordingly.

If a numeric argument ARG is provided, that many colons are inserted
non-electrically.

Electric behavior is inhibited inside a string or
comment or by universal prefix C-u.
Default is nil, controlled by `py-electric-colon-active-p'

py-electric-backspace
---------------------
Delete preceding character or level of indentation.

With ARG do that ARG times.
Returns column reached. 

py-electric-delete
------------------
Delete following character or levels of whitespace.

With ARG do that ARG times. 

py-indent-line-outmost
----------------------
Indent the current line to the outmost reasonable indent.

With optional C-u an indent with length `py-indent-offset' is inserted unconditionally 

py-indent-line
--------------
Indent the current line according to Python rules.

When called interactivly with C-u, ignore dedenting rules for block closing statements
(e.g. return, raise, break, continue, pass)

An optional C-u followed by a numeric argument neither 1 nor 4 will switch off `py-smart-indentation' for this execution. This permits to correct allowed but unwanted indents.
Similar to `toggle-py-smart-indentation' resp. `py-smart-indentation-off' followed by TAB.

This function is normally used by `indent-line-function' resp.
TAB.
Returns current indentation 

py-newline-and-indent
---------------------
Add a newline and indent to outmost reasonable indent.
When indent is set back manually, this is honoured in following lines. 

py-newline-and-dedent
---------------------
Add a newline and indent to one level below current.
Returns column. 

toggle-force-local-shell
------------------------
If locally indicated Python shell should be taken and
enforced upon sessions execute commands.

Toggles boolean `py-force-local-shell-p' along with `py-force-py-shell-name-p'
Returns value of `toggle-force-local-shell' switched to.

When on, kind of an option 'follow', local shell sets `py-shell-name', enforces its use afterwards.

See also commands
`py-force-local-shell-on'
`py-force-local-shell-off'
 

py-force-local-shell-on
-----------------------
Make sure, `py-py-force-local-shell-p' is on.

Returns value of `py-force-local-shell-p'.

Kind of an option 'follow', local shell sets `py-shell-name', enforces its use afterwards 

py-force-local-shell-off
------------------------
Restore `py-shell-name' default value and `behaviour'. 

toggle-force-py-shell-name-p
----------------------------
If customized default `py-shell-name' should be enforced upon execution.

If `py-force-py-shell-name-p' should be on or off.
Returns value of `py-force-py-shell-name-p' switched to.

See also commands
force-py-shell-name-p-on
force-py-shell-name-p-off

Caveat: Completion might not work that way.


force-py-shell-name-p-on
------------------------
Switches `py-force-py-shell-name-p' on.

Customized default `py-shell-name' will be enforced upon execution.
Returns value of `py-force-py-shell-name-p'.

Caveat: Completion might not work that way.


force-py-shell-name-p-off
-------------------------
Make sure, `py-force-py-shell-name-p' is off.

Function to use by executes will be guessed from environment.
Returns value of `py-force-py-shell-name-p'. 

py-toggle-indent-tabs-mode
--------------------------
Toggle `indent-tabs-mode'.

Returns value of `indent-tabs-mode' switched to. 

py-indent-tabs-mode
-------------------
With positive ARG switch `indent-tabs-mode' on.

With negative ARG switch `indent-tabs-mode' off.
Returns value of `indent-tabs-mode' switched to. 

py-indent-tabs-mode-on
----------------------
Switch `indent-tabs-mode' on. 

py-indent-tabs-mode-off
-----------------------
Switch `indent-tabs-mode' on. 

py-guess-indent-offset
----------------------
Guess a value for, and change, `py-indent-offset'.

By default, make a buffer-local copy of `py-indent-offset' with the
new value.
With optional argument GLOBAL change the global value of `py-indent-offset'.

Indent might be guessed savely only from beginning of a block.
Returns `py-indent-offset'

py-narrow-to-defun
------------------
Make text outside current def or class invisible.

The defun visible is the one that contains point or follows point. 

py-shift-left
-------------
Dedent region according to `py-indent-offset' by COUNT times.

If no region is active, current line is dedented.
Returns indentation reached. 

py-shift-right
--------------
Indent region according to `py-indent-offset' by COUNT times.

If no region is active, current line is indented.
Returns indentation reached. 

py-shift-paragraph-right
------------------------
Indent paragraph by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-paragraph-left
-----------------------
Dedent paragraph by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-block-right
--------------------
Indent block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-block-left
-------------------
Dedent block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-clause-right
---------------------
Indent clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-clause-left
--------------------
Dedent clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-def-right
------------------
Indent def by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-def-left
-----------------
Dedent def by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-class-right
--------------------
Indent class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-class-left
-------------------
Dedent class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-line-right
-------------------
Indent line by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-line-left
------------------
Dedent line by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-statement-right
------------------------
Indent statement by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-shift-statement-left
-----------------------
Dedent statement by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached. 

py-indent-and-forward
---------------------
Indent current line according to mode, move one line forward. 

py-indent-region
----------------
Reindent a region of Python code.

With optional INDENT-OFFSET specify a different value than `py-indent-offset' at place.

Guesses the outmost reasonable indent
Returns and keeps relative position 

py-beginning-of-paragraph-position
----------------------------------
Returns beginning of paragraph position. 

py-end-of-paragraph-position
----------------------------
Returns end of paragraph position. 

py-beginning-of-block-position
------------------------------
Returns beginning of block position. 

py-end-of-block-position
------------------------
Returns end of block position. 

py-beginning-of-clause-position
-------------------------------
Returns beginning of clause position. 

py-end-of-clause-position
-------------------------
Returns end of clause position. 

py-beginning-of-block-or-clause-position
----------------------------------------
Returns beginning of block-or-clause position. 

py-end-of-block-or-clause-position
----------------------------------
Returns end of block-or-clause position. 

py-beginning-of-def-position
----------------------------
Returns beginning of def position. 

py-end-of-def-position
----------------------
Returns end of def position. 

py-beginning-of-class-position
------------------------------
Returns beginning of class position. 

py-end-of-class-position
------------------------
Returns end of class position. 

py-beginning-of-def-or-class-position
-------------------------------------
Returns beginning of def-or-class position. 

py-end-of-def-or-class-position
-------------------------------
Returns end of def-or-class position. 

py-beginning-of-line-position
-----------------------------
Returns beginning of line position. 

py-end-of-line-position
-----------------------
Returns end of line position. 

py-beginning-of-statement-position
----------------------------------
Returns beginning of statement position. 

py-end-of-statement-position
----------------------------
Returns end of statement position. 

py-beginning-of-expression-position
-----------------------------------
Returns beginning of expression position. 

py-end-of-expression-position
-----------------------------
Returns end of expression position. 

py-beginning-of-partial-expression-position
-------------------------------------------
Returns beginning of partial-expression position. 

py-end-of-partial-expression-position
-------------------------------------
Returns end of partial-expression position. 

py-bounds-of-statement
----------------------
Returns bounds of statement at point.

With optional POSITION, a number, report bounds of statement at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-block
------------------
Returns bounds of block at point.

With optional POSITION, a number, report bounds of block at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-clause
-------------------
Returns bounds of clause at point.

With optional POSITION, a number, report bounds of clause at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-block-or-clause
----------------------------
Returns bounds of block-or-clause at point.

With optional POSITION, a number, report bounds of block-or-clause at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-def
----------------
Returns bounds of def at point.

With optional POSITION, a number, report bounds of def at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-class
------------------
Returns bounds of class at point.

With optional POSITION, a number, report bounds of class at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-region
-------------------
Returns bounds of region at point.

Returns a list, whose car is beg, cdr - end.

py-bounds-of-buffer
-------------------
Returns bounds of buffer at point.

With optional POSITION, a number, report bounds of buffer at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-expression
-----------------------
Returns bounds of expression at point.

With optional POSITION, a number, report bounds of expression at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-partial-expression
-------------------------------
Returns bounds of partial-expression at point.

With optional POSITION, a number, report bounds of partial-expression at POSITION.
Returns a list, whose car is beg, cdr - end.

py-bounds-of-declarations
-------------------------
Bounds of consecutive multitude of assigments resp. statements around point.

Indented same level, which don't open blocks.
Typically declarations resp. initialisations of variables following
a class or function definition.
See also py-bounds-of-statements 

py-beginning-of-declarations
----------------------------
Got to the beginning of assigments resp. statements in current level which don't open blocks.


py-end-of-declarations
----------------------
Got to the end of assigments resp. statements in current level which don't open blocks. 

py-declarations
---------------
Copy and mark assigments resp. statements in current level which don't open blocks or start with a keyword.

See also `py-statements', which is more general, taking also simple statements starting with a keyword. 

py-kill-declarations
--------------------
Delete variables declared in current level.

Store deleted variables in kill-ring 

py-bounds-of-statements
-----------------------
Bounds of consecutive multitude of statements around point.

Indented same level, which don't open blocks. 

py-beginning-of-statements
--------------------------
Got to the beginning of statements in current level which don't open blocks. 

py-end-of-statements
--------------------
Got to the end of statements in current level which don't open blocks. 

py-statements
-------------
Copy and mark simple statements in current level which don't open blocks.

More general than py-declarations, which would stop at keywords like a print-statement. 

py-kill-statements
------------------
Delete statements declared in current level.

Store deleted statements in kill-ring 

py-comment-region
-----------------
Like `comment-region' but uses double hash (`#') comment starter.

py-fill-paragraph
-----------------
Like M-q, but handle Python comments and strings.

If any of the current line is a comment, fill the comment or the
paragraph of it that point is in, preserving the comment's indentation
and initial `#'s.
If point is inside a string, narrow to that string and fill.


py-insert-super
---------------
Insert a function "super()" from current environment.

As example given in Python v3.1 documentation » The Python Standard Library »

class C(B):
    def method(self, arg):
        super().method(arg) # This does the same thing as:
                               # super(C, self).method(arg)

Returns the string inserted. 

py-nesting-level
----------------
Accepts the output of `parse-partial-sexp'. 

py-compute-indentation
----------------------
Compute Python indentation.

When HONOR-BLOCK-CLOSE-P is non-nil, statements such as `return',
`raise', `break', `continue', and `pass' force one level of dedenting.

py-continuation-offset
----------------------
With numeric ARG different from 1 py-continuation-offset is set to that value; returns py-continuation-offset. 

py-indentation-of-statement
---------------------------
Returns the indenation of the statement at point. 

py-list-beginning-position
--------------------------
Return lists beginning position, nil if not inside.

Optional ARG indicates a start-position for `parse-partial-sexp'.

py-end-of-list-position
-----------------------
Return end position, nil if not inside.

Optional ARG indicates a start-position for `parse-partial-sexp'.

py-in-triplequoted-string-p
---------------------------
Returns character address of start tqs-string, nil if not inside. 

py-in-string-p
--------------
Returns character address of start of string, nil if not inside. 

py-in-statement-p
-----------------
Returns list of beginning and end-position if inside.

Result is useful for booleans too: (when (py-in-statement-p)...)
will work.


py-statement-opens-block-p
--------------------------
Return position if the current statement opens a block
in stricter or wider sense.

For stricter sense specify regexp. 

py-statement-opens-clause-p
---------------------------
Return position if the current statement opens block or clause. 

py-statement-opens-block-or-clause-p
------------------------------------
Return position if the current statement opens block or clause. 

py-statement-opens-class-p
--------------------------
Return `t' if the statement opens a functions or class definition, nil otherwise. 

py-statement-opens-def-p
------------------------
Return `t' if the statement opens a functions or class definition, nil otherwise. 

py-statement-opens-def-or-class-p
---------------------------------
Return `t' if the statement opens a functions or class definition, nil otherwise. 

py-current-defun
----------------
Go to the outermost method or class definition in current scope.

Python value for `add-log-current-defun-function'.
This tells add-log.el how to find the current function/method/variable.
Returns name of class or methods definition, if found, nil otherwise.

See customizable variables `py-current-defun-show' and `py-current-defun-delay'.

py-sort-imports
---------------
Sort multiline imports.

Put point inside the parentheses of a multiline import and hit
M-x py-sort-imports to sort the imports lexicographically

py-which-function
-----------------
Return the name of the function or class, if curser is in, return nil otherwise. 

py-beginning-of-block
---------------------
Returns beginning of block if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-block
---------------
Go to the end of block.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-clause
----------------------
Returns beginning of clause if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-clause
----------------
Go to the end of clause.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-block-or-clause
-------------------------------
Returns beginning of block-or-clause if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-block-or-clause
-------------------------
Go to the end of block-or-clause.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-def
-------------------
Returns beginning of def if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-def
-------------
Go to the end of def.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-class
---------------------
Returns beginning of class if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-class
---------------
Go to the end of class.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-def-or-class
----------------------------
Returns beginning of def-or-class if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-def-or-class
----------------------
Go to the end of def-or-class.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-if-block
------------------------
Returns beginning of if-block if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-if-block
------------------
Go to the end of if-block.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-try-block
-------------------------
Returns beginning of try-block if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-try-block
-------------------
Go to the end of try-block.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-minor-block
---------------------------
Returns beginning of minor-block if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-end-of-minor-block
---------------------
Go to the end of minor-block.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html

py-beginning-of-expression
--------------------------
Go to the beginning of a compound python expression.

A a compound python expression might be concatenated by "." operator, thus composed by minor python expressions.

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes.


py-end-of-expression
--------------------
Go to the end of a compound python expression.

A a compound python expression might be concatenated by "." operator, thus composed by minor python expressions.

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference

Operators however are left aside resp. limit py-expression designed for edit-purposes. 

py-beginning-of-partial-expression
----------------------------------
Go to the beginning of a minor python expression.

"." operators delimit a minor expression on their level.
Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes. 

py-end-of-partial-expression
----------------------------
Go to the end of a minor python expression.

"." operators delimit a minor expression on their level.
Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes. 

py-beginning-of-line
--------------------
Go to beginning-of-line, return position.

If already at beginning-of-line and not at BOB, go to beginning of previous line. 

py-end-of-line
--------------
Go to end-of-line, return position.

If already at end-of-line and not at EOB, go to end of next line. 

py-beginning-of-statement
-------------------------
Go to the initial line of a simple statement.

For beginning of compound statement use py-beginning-of-block.
For beginning of clause py-beginning-of-clause.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html


py-end-of-statement
-------------------
Go to the last char of current statement.

To go just beyond the final line of the current statement, use `py-down-statement-lc'. 

py-goto-statement-below
-----------------------
Goto beginning of next statement. 

py-mark-paragraph
-----------------
Mark paragraph at point.

Returns beginning and end positions of marked area, a cons. 

py-mark-block
-------------
Mark block at point.

Returns beginning and end positions of marked area, a cons. 

py-mark-clause
--------------
Mark clause at point.

Returns beginning and end positions of marked area, a cons. 

py-mark-block-or-clause
-----------------------
Mark block-or-clause at point.

Returns beginning and end positions of marked area, a cons. 

py-mark-def
-----------
Mark def at point.

With M-x universal argument or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons. 

py-mark-class
-------------
Mark class at point.

With M-x universal argument or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons. 

py-mark-def-or-class
--------------------
Mark def-or-class at point.

With M-x universal argument or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons. 

py-mark-line
------------
Mark line at point.

Returns beginning and end positions of marked area, a cons. 

py-mark-statement
-----------------
Mark statement at point.

Returns beginning and end positions of marked area, a cons. 

py-mark-expression
------------------
Mark expression at point.

Returns beginning and end positions of marked area, a cons. 

py-mark-partial-expression
--------------------------
Mark partial-expression at point.

Returns beginning and end positions of marked area, a cons. 

py-beginning-of-decorator
-------------------------
Go to the beginning of a decorator.

Returns position if succesful 

py-end-of-decorator
-------------------
Go to the end of a decorator.

Returns position if succesful 

py-copy-expression
------------------
Mark expression at point.

Returns beginning and end positions of marked area, a cons. 

py-copy-partial-expression
--------------------------
Mark partial-expression at point.

Returns beginning and end positions of marked area, a cons.

"." operators delimit a partial-expression expression on it's level, that's the difference to compound expressions.

Given the function below, `py-partial-expression'
called at pipe symbol would copy and return:

def usage():
    print """Usage: %s
    ....""" % (
        os.path.basename(sys.argv[0]))
------------|-------------------------
==> path

        os.path.basename(sys.argv[0]))
------------------|-------------------
==> basename(sys.argv[0]))

        os.path.basename(sys.argv[0]))
--------------------------|-----------
==> sys

        os.path.basename(sys.argv[0]))
------------------------------|-------
==> argv[0]

while `py-expression' would copy and return

(
        os.path.basename(sys.argv[0]))

;;;;;

Also for existing commands a shorthand is defined:

(defalias 'py-statement 'py-copy-statement)

py-copy-statement
-----------------
Mark statement at point.

Returns beginning and end positions of marked area, a cons. 

py-copy-block
-------------
Mark block at point.

Returns beginning and end positions of marked area, a cons. 

py-copy-block-or-clause
-----------------------
Mark block-or-clause at point.

Returns beginning and end positions of marked area, a cons. 

py-copy-def
-----------
Mark def at point.

With universal argument or `py-mark-decorators' set to `t' decorators are copied too.
Returns beginning and end positions of marked area, a cons.

py-copy-def-or-class
--------------------
Mark def-or-class at point.

With universal argument or `py-mark-decorators' set to `t' decorators are copied too.
Returns beginning and end positions of marked area, a cons.

py-copy-class
-------------
Mark class at point.

With universal argument or `py-mark-decorators' set to `t' decorators are copied too.
Returns beginning and end positions of marked area, a cons.

py-copy-clause
--------------
Mark clause at point.
  Returns beginning and end positions of marked area, a cons. 

py-kill-expression
------------------
Delete expression at point.
  Stores data in kill ring. Might be yanked back using `C-y'. 

py-kill-partial-expression
--------------------------
Delete partial-expression at point.
  Stores data in kill ring. Might be yanked back using `C-y'.

"." operators delimit a partial-expression expression on it's level, that's the difference to compound expressions.

py-kill-statement
-----------------
Delete statement at point.

Stores data in kill ring. Might be yanked back using `C-y'. 

py-kill-block
-------------
Delete block at point.

Stores data in kill ring. Might be yanked back using `C-y'. 

py-kill-block-or-clause
-----------------------
Delete block-or-clause at point.

Stores data in kill ring. Might be yanked back using `C-y'. 

py-kill-def-or-class
--------------------
Delete def-or-class at point.

Stores data in kill ring. Might be yanked back using `C-y'. 

py-kill-class
-------------
Delete class at point.

Stores data in kill ring. Might be yanked back using `C-y'. 

py-kill-def
-----------
Delete def at point.

Stores data in kill ring. Might be yanked back using `C-y'. 

py-kill-clause
--------------
Delete clause at point.

Stores data in kill ring. Might be yanked back using `C-y'. 

py-forward-line
---------------
Goes to end of line after forward move.

Travels right-margin comments. 

py-go-to-beginning-of-comment
-----------------------------
Go to the beginning of current line's comment, if any.

From a programm use `py-beginning-of-comment' instead 

py-leave-comment-or-string-backward
-----------------------------------
If inside a comment or string, leave it backward. 

py-beginning-of-list-pps
------------------------
Go to the beginning of a list.
Optional ARG indicates a start-position for `parse-partial-sexp'.
Return beginning position, nil if not inside.

py-down-block-lc
----------------
Goto beginning of line following end of block.

Returns position reached, if successful, nil otherwise.

"-lc" stands for "left-corner" - a complementary command travelling left, whilst `py-end-of-block' stops at right corner.

See also `py-down-block': down from current definition to next beginning of block below. 

py-down-clause-lc
-----------------
Goto beginning of line following end of clause.

Returns position reached, if successful, nil otherwise.

"-lc" stands for "left-corner" - a complementary command travelling left, whilst `py-end-of-clause' stops at right corner.

See also `py-down-clause': down from current definition to next beginning of clause below. 

py-down-def-lc
--------------
Goto beginning of line following end of def.

Returns position reached, if successful, nil otherwise.

"-lc" stands for "left-corner" - a complementary command travelling left, whilst `py-end-of-def' stops at right corner.

See also `py-down-def': down from current definition to next beginning of def below. 

py-down-class-lc
----------------
Goto beginning of line following end of class.

Returns position reached, if successful, nil otherwise.

"-lc" stands for "left-corner" - a complementary command travelling left, whilst `py-end-of-class' stops at right corner.

See also `py-down-class': down from current definition to next beginning of class below. 

py-down-statement-lc
--------------------
Goto beginning of line following end of statement.

Returns position reached, if successful, nil otherwise.

"-lc" stands for "left-corner" - a complementary command travelling left, whilst `py-end-of-statement' stops at right corner.

See also `py-down-statement': down from current definition to next beginning of statement below. 

py-down-statement
-----------------
Go to the beginning of next statement below in buffer.

Returns indentation if statement found, nil otherwise. 

py-down-block
-------------
Go to the beginning of next block below in buffer.

Returns indentation if block found, nil otherwise. 

py-down-clause
--------------
Go to the beginning of next clause below in buffer.

Returns indentation if clause found, nil otherwise. 

py-down-block-or-clause
-----------------------
Go to the beginning of next block-or-clause below in buffer.

Returns indentation if block-or-clause found, nil otherwise. 

py-down-def
-----------
Go to the beginning of next def below in buffer.

Returns indentation if def found, nil otherwise. 

py-down-class
-------------
Go to the beginning of next class below in buffer.

Returns indentation if class found, nil otherwise. 

py-down-def-or-class
--------------------
Go to the beginning of next def-or-class below in buffer.

Returns indentation if def-or-class found, nil otherwise. 

py-forward-into-nomenclature
----------------------------
Move forward to end of a nomenclature section or word.

With C-u (programmatically, optional argument ARG), do it that many times.

A `nomenclature' is a fancy way of saying AWordWithMixedCaseNotUnderscores.

py-backward-into-nomenclature
-----------------------------
Move backward to beginning of a nomenclature section or word.

With optional ARG, move that many times.  If ARG is negative, move
forward.

A `nomenclature' is a fancy way of saying AWordWithMixedCaseNotUnderscores.

match-paren
-----------
Go to the matching brace, bracket or parenthesis if on its counterpart.

Otherwise insert the character, the key is assigned to, here `%'.
With universal arg  insert a `%'. 

py-toggle-execute-keep-temporary-file-p
---------------------------------------
Toggle py-execute-keep-temporary-file-p 

py-guess-default-python
-----------------------
Defaults to "python", if guessing didn't succeed. 

py-set-shell-completion-environment
-----------------------------------
Sets `...-completion-command-string' and `py-complete-function'. 

py-set-ipython-completion-command-string
----------------------------------------
Set and return `ipython-completion-command-string'. 

py-shell-dedicated
------------------
Start an interactive Python interpreter in another window.

With optional C-u user is prompted by
`py-choose-shell' for command and options to pass to the Python
interpreter.


py-shell
--------
Start an interactive Python interpreter in another window.

Interactively, C-u 4 prompts for a buffer.
C-u 2 prompts for `py-python-command-args'.
If `default-directory' is a remote file name, it is also prompted
to change if called with a prefix arg.

Returns py-shell's buffer-name.
Optional string PYSHELLNAME overrides default `py-shell-name'.
Optional symbol SWITCH ('switch/'noswitch) precedes `py-switch-buffers-on-execute-p'
When SEPCHAR is given, `py-shell' must not detect the file-separator.
BUFFER allows specifying a name, the Python process is connected to
When DONE is `t', `py-shell-manage-windows' is omitted


python
------
Start an Python interpreter.

Optional C-u prompts for options to pass to the Python interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. 

ipython
-------
Start an IPython interpreter.

Optional C-u prompts for options to pass to the IPython interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. 

python3
-------
Start an Python3 interpreter.

Optional C-u prompts for options to pass to the Python3 interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. 

python2
-------
Start an Python2 interpreter.

Optional C-u prompts for options to pass to the Python2 interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. 

python2\.7
----------
Start an Python2.7 interpreter.

Optional C-u prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. 

jython
------
Start an Jython interpreter.

Optional C-u prompts for options to pass to the Jython interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. 

python3\.2
----------
Start an Python3.2 interpreter.

Optional C-u prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. 

python-dedicated
----------------
Start an unique Python interpreter in another window.

Optional C-u prompts for options to pass to the Python interpreter. See `py-python-command-args'.

ipython-dedicated
-----------------
Start an unique IPython interpreter in another window.

Optional C-u prompts for options to pass to the IPython interpreter. See `py-python-command-args'.

python3-dedicated
-----------------
Start an unique Python3 interpreter in another window.

Optional C-u prompts for options to pass to the Python3 interpreter. See `py-python-command-args'.

python2-dedicated
-----------------
Start an unique Python2 interpreter in another window.

Optional C-u prompts for options to pass to the Python2 interpreter. See `py-python-command-args'.

python2\.7-dedicated
--------------------
Start an unique Python2.7 interpreter in another window.

Optional C-u prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'.

jython-dedicated
----------------
Start an unique Jython interpreter in another window.

Optional C-u prompts for options to pass to the Jython interpreter. See `py-python-command-args'.

python3\.2-dedicated
--------------------
Start an unique Python3.2 interpreter in another window.

Optional C-u prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'.

python-switch
-------------
Switch to Python interpreter in another window.

Optional C-u prompts for options to pass to the Python interpreter. See `py-python-command-args'.

ipython-switch
--------------
Switch to IPython interpreter in another window.

Optional C-u prompts for options to pass to the IPython interpreter. See `py-python-command-args'.

python3-switch
--------------
Switch to Python3 interpreter in another window.

Optional C-u prompts for options to pass to the Python3 interpreter. See `py-python-command-args'.

python2-switch
--------------
Switch to Python2 interpreter in another window.

Optional C-u prompts for options to pass to the Python2 interpreter. See `py-python-command-args'.

python2\.7-switch
-----------------
Switch to Python2.7 interpreter in another window.

Optional C-u prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'.

jython-switch
-------------
Switch to Jython interpreter in another window.

Optional C-u prompts for options to pass to the Jython interpreter. See `py-python-command-args'.

python3\.2-switch
-----------------
Switch to Python3.2 interpreter in another window.

Optional C-u prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'.

python-no-switch
----------------
Open an Python interpreter in another window, but do not switch to it.

Optional C-u prompts for options to pass to the Python interpreter. See `py-python-command-args'.

ipython-no-switch
-----------------
Open an IPython interpreter in another window, but do not switch to it.

Optional C-u prompts for options to pass to the IPython interpreter. See `py-python-command-args'.

python3-no-switch
-----------------
Open an Python3 interpreter in another window, but do not switch to it.

Optional C-u prompts for options to pass to the Python3 interpreter. See `py-python-command-args'.

python2-no-switch
-----------------
Open an Python2 interpreter in another window, but do not switch to it.

Optional C-u prompts for options to pass to the Python2 interpreter. See `py-python-command-args'.

python2\.7-no-switch
--------------------
Open an Python2.7 interpreter in another window, but do not switch to it.

Optional C-u prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'.

jython-no-switch
----------------
Open an Jython interpreter in another window, but do not switch to it.

Optional C-u prompts for options to pass to the Jython interpreter. See `py-python-command-args'.

python3\.2-no-switch
--------------------
Open an Python3.2 interpreter in another window, but do not switch to it.

Optional C-u prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'.

python-switch-dedicated
-----------------------
Switch to an unique Python interpreter in another window.

Optional C-u prompts for options to pass to the Python interpreter. See `py-python-command-args'.

ipython-switch-dedicated
------------------------
Switch to an unique IPython interpreter in another window.

Optional C-u prompts for options to pass to the IPython interpreter. See `py-python-command-args'.

python3-switch-dedicated
------------------------
Switch to an unique Python3 interpreter in another window.

Optional C-u prompts for options to pass to the Python3 interpreter. See `py-python-command-args'.

python2-switch-dedicated
------------------------
Switch to an unique Python2 interpreter in another window.

Optional C-u prompts for options to pass to the Python2 interpreter. See `py-python-command-args'.

python2\.7-switch-dedicated
---------------------------
Switch to an unique Python2.7 interpreter in another window.

Optional C-u prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'.

jython-switch-dedicated
-----------------------
Switch to an unique Jython interpreter in another window.

Optional C-u prompts for options to pass to the Jython interpreter. See `py-python-command-args'.

python3\.2-switch-dedicated
---------------------------
Switch to an unique Python3.2 interpreter in another window.

Optional C-u prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'.

py-which-execute-file-command
-----------------------------
Return the command appropriate to Python version.

Per default it's "(format "execfile(r'%s') # PYTHON-MODE\n" filename)" for Python 2 series.

py-execute-region-no-switch
---------------------------
Send the region to a Python interpreter.

Ignores setting of `py-switch-buffers-on-execute-p', buffer with region stays current.
 

py-execute-region-switch
------------------------
Send the region to a Python interpreter.

Ignores setting of `py-switch-buffers-on-execute-p', output-buffer will being switched to.


py-execute-region
-----------------
Send the region to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)


py-execute-region-default
-------------------------
Send the region to the systems default Python interpreter.
See also `py-execute-region'. 

py-execute-region-dedicated
---------------------------
Get the region processed by an unique Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument. 

py-execute-region-default-dedicated
-----------------------------------
Send the region to an unique shell of systems default Python. 

py-execute-string
-----------------
Send the argument STRING to a Python interpreter.

See also `py-execute-region'. 

py-execute-string-dedicated
---------------------------
Send the argument STRING to an unique Python interpreter.

See also `py-execute-region'. 

py-fetch-py-master-file
-----------------------
Lookup if a `py-master-file' is specified.

See also doku of variable `py-master-file' 

py-execute-import-or-reload
---------------------------
Import the current buffer's file in a Python interpreter.

If the file has already been imported, then do reload instead to get
the latest version.

If the file's name does not end in ".py", then do execfile instead.

If the current buffer is not visiting a file, do `py-execute-buffer'
instead.

If the file local variable `py-master-file' is non-nil, import or
reload the named file instead of the buffer's file.  The file may be
saved based on the value of `py-execute-import-or-reload-save-p'.

See also `M-x py-execute-region'.

This may be preferable to `M-x py-execute-buffer' because:

 - Definitions stay in their module rather than appearing at top
   level, where they would clutter the global namespace and not affect
   uses of qualified names (MODULE.NAME).

 - The Python debugger gets line number information about the functions.

py-execute-buffer-dedicated
---------------------------
Send the contents of the buffer to a unique Python interpreter.

If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.

If a clipping restriction is in effect, only the accessible portion of the buffer is sent. A trailing newline will be supplied if needed.

With M-x univeral-argument user is prompted to specify another then default shell.
See also `M-x py-execute-region'. 

py-execute-buffer-switch
------------------------
Send the contents of the buffer to a Python interpreter and switches to output.

If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.
If there is a *Python* process buffer, it is used.
If a clipping restriction is in effect, only the accessible portion of the buffer is sent. A trailing newline will be supplied if needed.

With M-x univeral-argument user is prompted to specify another then default shell.
See also `M-x py-execute-region'. 

py-execute-buffer-dedicated-switch
----------------------------------
Send the contents of the buffer to an unique Python interpreter.

Ignores setting of `py-switch-buffers-on-execute-p'.
If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.

If a clipping restriction is in effect, only the accessible portion of the buffer is sent. A trailing newline will be supplied if needed.

With M-x univeral-argument user is prompted to specify another then default shell.
See also `M-x py-execute-region'. 

py-execute-buffer
-----------------
Send the contents of the buffer to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch) 

py-execute-buffer-no-switch
---------------------------
Send the contents of the buffer to a Python interpreter but don't switch to output.

If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.
If there is a *Python* process buffer, it is used.
If a clipping restriction is in effect, only the accessible portion of the buffer is sent. A trailing newline will be supplied if needed.

With M-x univeral-argument user is prompted to specify another then default shell.
See also `M-x py-execute-region'. 

py-execute-defun
----------------
Send the current defun (class or method) to the inferior Python process.

py-process-file
---------------
Process "python filename".

Optional OUTPUT-BUFFER and ERROR-BUFFER might be given. 

py-exec-execfile-region
-----------------------
Execute the region in a Python interpreter. 

py-exec-execfile
----------------
Process "python filename",
Optional OUTPUT-BUFFER and ERROR-BUFFER might be given.')


py-execute-statement
--------------------
Send statement at point to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)

py-execute-block
----------------
Send block at point to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)

py-execute-block-or-clause
--------------------------
Send block-or-clause at point to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)

py-execute-def
--------------
Send def at point to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)

py-execute-class
----------------
Send class at point to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)

py-execute-def-or-class
-----------------------
Send def-or-class at point to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)

py-execute-expression
---------------------
Send expression at point to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)

py-execute-partial-expression
-----------------------------
Send partial-expression at point to a Python interpreter.

When called with M-x univeral-argument, execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with M-x univeral-argument followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)

py-execute-line
---------------
Send current line from beginning of indent to Python interpreter. 

py-execute-file
---------------
When called interactively, user is prompted for filename. 

py-down-exception
-----------------
Go to the next line down in the traceback.

With M-x univeral-argument (programmatically, optional argument
BOTTOM), jump to the bottom (innermost) exception in the exception
stack.

py-up-exception
---------------
Go to the previous line up in the traceback.

With C-u (programmatically, optional argument TOP)
jump to the top (outermost) exception in the exception stack.

py-output-buffer-filter
-----------------------
Clear output buffer from py-shell-input prompt etc. 

py-send-string
--------------
Evaluate STRING in inferior Python process.

py-pdbtrack-toggle-stack-tracking
---------------------------------
Set variable `py-pdbtrack-do-tracking-p'. 

turn-on-pdbtrack
----------------


turn-off-pdbtrack
-----------------


py-fetch-docu
-------------
Lookup in current buffer for the doku for the symbol at point.

Useful for newly defined symbol, not known to python yet. 

py-find-imports
---------------
Find top-level imports, updating `python-imports'.

py-eldoc-function
-----------------
Print help on symbol at point. 

py-describe-symbol
------------------
Print help on symbol at point.

Optional C-u used for debugging, will prevent deletion of temp file. 

py-describe-mode
----------------
Dump long form of `python-mode' docs.

py-find-function
----------------
Find source of definition of function NAME.

Interactively, prompt for name.

py-update-imports
-----------------
Returns `python-imports'.

Imports done are displayed in message buffer. 

py-indent-forward-line
----------------------
Indent and move one line forward to next indentation.
Returns column of line reached.

If `py-kill-empty-line' is non-nil, delete an empty line.
When closing a form, use py-close-block et al, which will move and indent likewise.
With M-x universal argument just indent.


py-dedent-forward-line
----------------------
Dedent line and move one line forward. 

py-dedent
---------
Dedent line according to `py-indent-offset'.

With arg, do it that many times.
If point is between indent levels, dedent to next level.
Return indentation reached, if dedent done, nil otherwise.

Affected by `py-dedent-keep-relative-column'. 

py-close-def
------------
Set indent level to that of beginning of function definition.

If final line isn't empty and `py-close-block-provides-newline' non-nil, insert a newline. 

py-close-class
--------------
Set indent level to that of beginning of class definition.

If final line isn't empty and `py-close-block-provides-newline' non-nil, insert a newline. 

py-close-clause
---------------
Set indent level to that of beginning of clause definition.

If final line isn't empty and `py-close-block-provides-newline' non-nil, insert a newline. 

py-close-block
--------------
Set indent level to that of beginning of block definition.

If final line isn't empty and `py-close-block-provides-newline' non-nil, insert a newline. 

py-class-at-point
-----------------
Return class definition as string.

With interactive call, send it to the message buffer too. 

py-line-at-point
----------------
Return line as string.
  With interactive call, send it to the message buffer too. 

py-looking-at-keywords-p
------------------------
If looking at a python keyword. Returns t or nil. 

py-match-paren-mode
-------------------
py-match-paren-mode nil oder t

py-match-paren
--------------
Goto to the opening or closing of block before or after point.

With arg, do it that many times.
 Closes unclosed block if jumping from beginning. 

py-printform-insert
-------------------
Inserts a print statement out of current `(car kill-ring)' by default, inserts ARG instead if delivered. 

py-documentation
----------------
Launch PyDOC on the Word at Point

eva
---
Put "eval(...)" forms around strings at point. 

pst-here
--------
Kill previous "pdb.set_trace()" and insert it at point. 

py-line-to-printform-python2
----------------------------
Transforms the item on current in a print statement. 

py-switch-imenu-index-function
------------------------------
For development only. Good old renamed `py-imenu-create-index'-function hangs with medium size files already. Working `py-imenu-create-index-new' is active by default.

Switch between classic index machine `py-imenu-create-index'-function and new `py-imenu-create-index-new'.

The former may provide a more detailed report, thus delivering two different index-machines is considered. 

py-choose-shell-by-path
-----------------------
Select Python executable according to version desplayed in path, current buffer-file is selected from.

Returns versioned string, nil if nothing appropriate found 

py-choose-shell-by-shebang
--------------------------
Choose shell by looking at #! on the first line.

Returns the specified Python resp. Jython shell command name. 

py-which-python
---------------
Returns version of Python of current environment, a number. 

py-python-current-environment
-----------------------------
Returns path of current Python installation. 

py-switch-shell
---------------
Toggles between the interpreter customized in `py-shell-toggle-1' resp. `py-shell-toggle-2'. Was hard-coded CPython and Jython in earlier versions, now starts with Python2 and Python3 by default.

ARG might be a python-version string to set to.

C-u `py-toggle-shell' prompts to specify a reachable Python command.
C-u followed by numerical arg 2 or 3, `py-toggle-shell' opens a respective Python shell.
C-u followed by numerical arg 5 opens a Jython shell.

Should you need more shells to select, extend this command by adding inside the first cond:

                    ((eq NUMBER (prefix-numeric-value arg))
                     "MY-PATH-TO-SHELL")


py-choose-shell
---------------
Return an appropriate executable as a string.

Returns nil, if no executable found.

This does the following:
 - look for an interpreter with `py-choose-shell-by-shebang'
 - examine imports using `py-choose-shell-by-import'
 - look if Path/To/File indicates a Python version
 - if not successful, return default value of `py-shell-name'

When interactivly called, messages the shell name, Emacs would in the given circtumstances.

With C-u 4 is called `py-switch-shell' see docu there.


py-toggle-smart-indentation
---------------------------
If `py-smart-indentation' should be on or off.

Returns value of `py-smart-indentation' switched to. 

py-smart-indentation-on
-----------------------
Make sure, `py-smart-indentation' is on.

Returns value of `py-smart-indentation'. 

py-smart-indentation-off
------------------------
Make sure, `py-smart-indentation' is off.

Returns value of `py-smart-indentation'. 

py-toggle-split-windows-on-execute
----------------------------------
If `py-split-windows-on-execute-p' should be on or off.

  Returns value of `py-split-windows-on-execute-p' switched to. 

py-split-windows-on-execute-on
------------------------------
Make sure, `py-split-windows-on-execute-p' is on.

Returns value of `py-split-windows-on-execute-p'. 

py-split-windows-on-execute-off
-------------------------------
Make sure, `py-split-windows-on-execute-p' is off.

Returns value of `py-split-windows-on-execute-p'. 

clear-flymake-allowed-file-name-masks
-------------------------------------
Remove entries with SUFFIX from `flymake-allowed-file-name-masks'.

Default is "\.py\'" 

pylint-flymake-mode
-------------------
Toggle `pylint' `flymake-mode'. 

pyflakes-flymake-mode
---------------------
Toggle `pyflakes' `flymake-mode'. 

pychecker-flymake-mode
----------------------
Toggle `pychecker' `flymake-mode'. 

pep8-flymake-mode
-----------------
Toggle `pep8' `flymake-mode'. 

pyflakespep8-flymake-mode
-------------------------
Toggle `pyflakespep8' `flymake-mode'.

Joint call to pyflakes and pep8 as proposed by

Keegan Carruthers-Smith



py-toggle-shell-switch-buffers-on-execute
-----------------------------------------
If `py-switch-buffers-on-execute-p' should be on or off.

  Returns value of `py-switch-buffers-on-execute-p' switched to. 

py-shell-switch-buffers-on-execute-on
-------------------------------------
Make sure, `py-switch-buffers-on-execute-p' is on.

Returns value of `py-switch-buffers-on-execute-p'. 

py-shell-switch-buffers-on-execute-off
--------------------------------------
Make sure, `py-switch-buffers-on-execute-p' is off.

Returns value of `py-switch-buffers-on-execute-p'. 

py-install-directory-check
--------------------------
Do some sanity check for `py-install-directory'.

Returns `t' if successful. 

py-load-pymacs
--------------
Load Pymacs as delivered with python-mode.el.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.ca

py-guess-py-install-directory
-----------------------------
Takes value of user directory aka $HOME
if `(locate-library "python-mode")' is not succesful. 

py-set-load-path
----------------
Include needed subdirs of python-mode directory. 

py-def-or-class-beginning-position
----------------------------------
Returns beginning position of function or class definition. 

py-def-or-class-end-position
----------------------------
Returns end position of function or class definition. 

py-statement-beginning-position
-------------------------------
Returns beginning position of statement. 

py-statement-end-position
-------------------------
Returns end position of statement. 

py-current-indentation
----------------------
Returns beginning position of code in line. 

py-python-version
-----------------
Returns versions number of a Python EXECUTABLE, string.

If no EXECUTABLE given, `py-shell-name' is used.
Interactively output of `--version' is displayed. 

py-version
----------
Echo the current version of `python-mode' in the minibuffer.

py-install-search-local
-----------------------


py-install-local-shells
-----------------------
Builds Python-shell commands from executable found in LOCAL.

If LOCAL is empty, shell-command `find' searches beneath current directory.
Eval resulting buffer to install it, see customizable `py-extensions'. 

py-send-region
--------------
Send the region to the inferior Python process.

py-send-buffer
--------------
Send the current buffer to the inferior Python process.

py-switch-to-python
-------------------
Switch to the Python process buffer, maybe starting new process.

With prefix arg, position cursor at end of buffer.

py-send-region-and-go
---------------------
Send the region to the inferior Python process.

Then switch to the process buffer.

py-load-file
------------
Load a Python file FILE-NAME into the inferior Python process.

If the file has extension `.py' import or reload it as a module.
Treating it as a module keeps the global namespace clean, provides
function location information for debugging, and supports users of
module-qualified names.

py-set-proc
-----------
Set the default value of `python-buffer' to correspond to this buffer.

If the current buffer has a local value of `python-buffer', set the
default (global) value to that.  The associated Python process is
the one that gets input from M-x py-send-region et al when used
in a buffer that doesn't have a local value of `python-buffer'.

py-completion-at-point
----------------------
An alternative completion, similar the way python.el does it. 

py-script-complete
------------------


py-python-script-complete
-------------------------
Complete word before point, if any. Otherwise insert TAB. 

py-python2-shell-complete
-------------------------


py-python3-shell-complete
-------------------------
Complete word before point, if any. Otherwise insert TAB. 

py-shell-complete
-----------------
Complete word before point, if any. Otherwise insert TAB. 

ipython-complete
----------------
Complete the python symbol before point.

If no completion available, insert a TAB.
Returns the completed symbol, a string, if successful, nil otherwise.

Bug: if no IPython-shell is running, fails first time due to header returned, which messes up the result. Please repeat once then. 

ipython-complete-py-shell-name
------------------------------
Complete the python symbol before point.

If no completion available, insert a TAB.
Returns the completed symbol, a string, if successful, nil otherwise.

Bug: if no IPython-shell is running, fails first time due to header returned, which messes up the result. Please repeat once then. 

py-pep8-run
-----------
*Run pep8, check formatting (default on the file currently visited).


py-pep8-help
------------
Display pep8 command line help messages. 

py-pylint-run
-------------
*Run pylint (default on the file currently visited).

For help see M-x pylint-help resp. M-x pylint-long-help.
Home-page: http://www.logilab.org/project/pylint 

py-pylint-help
--------------
Display Pylint command line help messages.

Let's have this until more Emacs-like help is prepared 

py-pylint-doku
--------------
Display Pylint Documentation.

Calls `pylint --full-documentation'

py-pyflakes-run
---------------
*Run pyflakes (default on the file currently visited).

For help see M-x pyflakes-help resp. M-x pyflakes-long-help.
Home-page: http://www.logilab.org/project/pyflakes 

py-pyflakes-help
----------------
Display Pyflakes command line help messages.

Let's have this until more Emacs-like help is prepared 

py-pyflakespep8-run
-------------------
*Run pyflakespep8, check formatting (default on the file currently visited).


py-pyflakespep8-help
--------------------
Display pyflakespep8 command line help messages. 

py-pychecker-run
----------------
*Run pychecker (default on the file currently visited).

virtualenv-current
------------------
barfs the current activated virtualenv

virtualenv-activate
-------------------
Activate the virtualenv located in DIR

virtualenv-deactivate
---------------------
Deactivate the current virtual enviroment

virtualenv-workon
-----------------
Issue a virtualenvwrapper-like virtualenv-workon command

py-toggle-local-default-use
---------------------------


py-execute-statement-python
---------------------------
Send statement at point to Python interpreter. 

py-execute-statement-python-switch
----------------------------------
Send statement at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-statement-python-noswitch
------------------------------------
Send statement at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-statement-python-dedicated
-------------------------------------
Send statement at point to Python unique interpreter. 

py-execute-statement-python-dedicated-switch
--------------------------------------------
Send statement at point to Python unique interpreter and switch to result. 

py-execute-statement-ipython
----------------------------
Send statement at point to IPython interpreter. 

py-execute-statement-ipython-switch
-----------------------------------
Send statement at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-statement-ipython-noswitch
-------------------------------------
Send statement at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-statement-ipython-dedicated
--------------------------------------
Send statement at point to IPython unique interpreter. 

py-execute-statement-ipython-dedicated-switch
---------------------------------------------
Send statement at point to IPython unique interpreter and switch to result. 

py-execute-statement-python3
----------------------------
Send statement at point to Python3 interpreter. 

py-execute-statement-python3-switch
-----------------------------------
Send statement at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-statement-python3-noswitch
-------------------------------------
Send statement at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-statement-python3-dedicated
--------------------------------------
Send statement at point to Python3 unique interpreter. 

py-execute-statement-python3-dedicated-switch
---------------------------------------------
Send statement at point to Python3 unique interpreter and switch to result. 

py-execute-statement-python2
----------------------------
Send statement at point to Python2 interpreter. 

py-execute-statement-python2-switch
-----------------------------------
Send statement at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-statement-python2-noswitch
-------------------------------------
Send statement at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-statement-python2-dedicated
--------------------------------------
Send statement at point to Python2 unique interpreter. 

py-execute-statement-python2-dedicated-switch
---------------------------------------------
Send statement at point to Python2 unique interpreter and switch to result. 

py-execute-statement-python2\.7
-------------------------------
Send statement at point to Python2.7 interpreter. 

py-execute-statement-python2\.7-switch
--------------------------------------
Send statement at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-statement-python2\.7-noswitch
----------------------------------------
Send statement at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-statement-python2\.7-dedicated
-----------------------------------------
Send statement at point to Python2.7 unique interpreter. 

py-execute-statement-python2\.7-dedicated-switch
------------------------------------------------
Send statement at point to Python2.7 unique interpreter and switch to result. 

py-execute-statement-jython
---------------------------
Send statement at point to Jython interpreter. 

py-execute-statement-jython-switch
----------------------------------
Send statement at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-statement-jython-noswitch
------------------------------------
Send statement at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-statement-jython-dedicated
-------------------------------------
Send statement at point to Jython unique interpreter. 

py-execute-statement-jython-dedicated-switch
--------------------------------------------
Send statement at point to Jython unique interpreter and switch to result. 

py-execute-statement-python3\.2
-------------------------------
Send statement at point to Python3.2 interpreter. 

py-execute-statement-python3\.2-switch
--------------------------------------
Send statement at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-statement-python3\.2-noswitch
----------------------------------------
Send statement at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-statement-python3\.2-dedicated
-----------------------------------------
Send statement at point to Python3.2 unique interpreter. 

py-execute-statement-python3\.2-dedicated-switch
------------------------------------------------
Send statement at point to Python3.2 unique interpreter and switch to result. 

py-execute-block-python
-----------------------
Send block at point to Python interpreter. 

py-execute-block-python-switch
------------------------------
Send block at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-python-noswitch
--------------------------------
Send block at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-python-dedicated
---------------------------------
Send block at point to Python unique interpreter. 

py-execute-block-python-dedicated-switch
----------------------------------------
Send block at point to Python unique interpreter and switch to result. 

py-execute-block-ipython
------------------------
Send block at point to IPython interpreter. 

py-execute-block-ipython-switch
-------------------------------
Send block at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-ipython-noswitch
---------------------------------
Send block at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-ipython-dedicated
----------------------------------
Send block at point to IPython unique interpreter. 

py-execute-block-ipython-dedicated-switch
-----------------------------------------
Send block at point to IPython unique interpreter and switch to result. 

py-execute-block-python3
------------------------
Send block at point to Python3 interpreter. 

py-execute-block-python3-switch
-------------------------------
Send block at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-python3-noswitch
---------------------------------
Send block at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-python3-dedicated
----------------------------------
Send block at point to Python3 unique interpreter. 

py-execute-block-python3-dedicated-switch
-----------------------------------------
Send block at point to Python3 unique interpreter and switch to result. 

py-execute-block-python2
------------------------
Send block at point to Python2 interpreter. 

py-execute-block-python2-switch
-------------------------------
Send block at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-python2-noswitch
---------------------------------
Send block at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-python2-dedicated
----------------------------------
Send block at point to Python2 unique interpreter. 

py-execute-block-python2-dedicated-switch
-----------------------------------------
Send block at point to Python2 unique interpreter and switch to result. 

py-execute-block-python2\.7
---------------------------
Send block at point to Python2.7 interpreter. 

py-execute-block-python2\.7-switch
----------------------------------
Send block at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-python2\.7-noswitch
------------------------------------
Send block at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-python2\.7-dedicated
-------------------------------------
Send block at point to Python2.7 unique interpreter. 

py-execute-block-python2\.7-dedicated-switch
--------------------------------------------
Send block at point to Python2.7 unique interpreter and switch to result. 

py-execute-block-jython
-----------------------
Send block at point to Jython interpreter. 

py-execute-block-jython-switch
------------------------------
Send block at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-jython-noswitch
--------------------------------
Send block at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-jython-dedicated
---------------------------------
Send block at point to Jython unique interpreter. 

py-execute-block-jython-dedicated-switch
----------------------------------------
Send block at point to Jython unique interpreter and switch to result. 

py-execute-block-python3\.2
---------------------------
Send block at point to Python3.2 interpreter. 

py-execute-block-python3\.2-switch
----------------------------------
Send block at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-python3\.2-noswitch
------------------------------------
Send block at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-python3\.2-dedicated
-------------------------------------
Send block at point to Python3.2 unique interpreter. 

py-execute-block-python3\.2-dedicated-switch
--------------------------------------------
Send block at point to Python3.2 unique interpreter and switch to result. 

py-execute-clause-python
------------------------
Send clause at point to Python interpreter. 

py-execute-clause-python-switch
-------------------------------
Send clause at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-clause-python-noswitch
---------------------------------
Send clause at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-clause-python-dedicated
----------------------------------
Send clause at point to Python unique interpreter. 

py-execute-clause-python-dedicated-switch
-----------------------------------------
Send clause at point to Python unique interpreter and switch to result. 

py-execute-clause-ipython
-------------------------
Send clause at point to IPython interpreter. 

py-execute-clause-ipython-switch
--------------------------------
Send clause at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-clause-ipython-noswitch
----------------------------------
Send clause at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-clause-ipython-dedicated
-----------------------------------
Send clause at point to IPython unique interpreter. 

py-execute-clause-ipython-dedicated-switch
------------------------------------------
Send clause at point to IPython unique interpreter and switch to result. 

py-execute-clause-python3
-------------------------
Send clause at point to Python3 interpreter. 

py-execute-clause-python3-switch
--------------------------------
Send clause at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-clause-python3-noswitch
----------------------------------
Send clause at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-clause-python3-dedicated
-----------------------------------
Send clause at point to Python3 unique interpreter. 

py-execute-clause-python3-dedicated-switch
------------------------------------------
Send clause at point to Python3 unique interpreter and switch to result. 

py-execute-clause-python2
-------------------------
Send clause at point to Python2 interpreter. 

py-execute-clause-python2-switch
--------------------------------
Send clause at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-clause-python2-noswitch
----------------------------------
Send clause at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-clause-python2-dedicated
-----------------------------------
Send clause at point to Python2 unique interpreter. 

py-execute-clause-python2-dedicated-switch
------------------------------------------
Send clause at point to Python2 unique interpreter and switch to result. 

py-execute-clause-python2\.7
----------------------------
Send clause at point to Python2.7 interpreter. 

py-execute-clause-python2\.7-switch
-----------------------------------
Send clause at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-clause-python2\.7-noswitch
-------------------------------------
Send clause at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-clause-python2\.7-dedicated
--------------------------------------
Send clause at point to Python2.7 unique interpreter. 

py-execute-clause-python2\.7-dedicated-switch
---------------------------------------------
Send clause at point to Python2.7 unique interpreter and switch to result. 

py-execute-clause-jython
------------------------
Send clause at point to Jython interpreter. 

py-execute-clause-jython-switch
-------------------------------
Send clause at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-clause-jython-noswitch
---------------------------------
Send clause at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-clause-jython-dedicated
----------------------------------
Send clause at point to Jython unique interpreter. 

py-execute-clause-jython-dedicated-switch
-----------------------------------------
Send clause at point to Jython unique interpreter and switch to result. 

py-execute-clause-python3\.2
----------------------------
Send clause at point to Python3.2 interpreter. 

py-execute-clause-python3\.2-switch
-----------------------------------
Send clause at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-clause-python3\.2-noswitch
-------------------------------------
Send clause at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-clause-python3\.2-dedicated
--------------------------------------
Send clause at point to Python3.2 unique interpreter. 

py-execute-clause-python3\.2-dedicated-switch
---------------------------------------------
Send clause at point to Python3.2 unique interpreter and switch to result. 

py-execute-block-or-clause-python
---------------------------------
Send block-or-clause at point to Python interpreter. 

py-execute-block-or-clause-python-switch
----------------------------------------
Send block-or-clause at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-or-clause-python-noswitch
------------------------------------------
Send block-or-clause at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-or-clause-python-dedicated
-------------------------------------------
Send block-or-clause at point to Python unique interpreter. 

py-execute-block-or-clause-python-dedicated-switch
--------------------------------------------------
Send block-or-clause at point to Python unique interpreter and switch to result. 

py-execute-block-or-clause-ipython
----------------------------------
Send block-or-clause at point to IPython interpreter. 

py-execute-block-or-clause-ipython-switch
-----------------------------------------
Send block-or-clause at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-or-clause-ipython-noswitch
-------------------------------------------
Send block-or-clause at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-or-clause-ipython-dedicated
--------------------------------------------
Send block-or-clause at point to IPython unique interpreter. 

py-execute-block-or-clause-ipython-dedicated-switch
---------------------------------------------------
Send block-or-clause at point to IPython unique interpreter and switch to result. 

py-execute-block-or-clause-python3
----------------------------------
Send block-or-clause at point to Python3 interpreter. 

py-execute-block-or-clause-python3-switch
-----------------------------------------
Send block-or-clause at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-or-clause-python3-noswitch
-------------------------------------------
Send block-or-clause at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-or-clause-python3-dedicated
--------------------------------------------
Send block-or-clause at point to Python3 unique interpreter. 

py-execute-block-or-clause-python3-dedicated-switch
---------------------------------------------------
Send block-or-clause at point to Python3 unique interpreter and switch to result. 

py-execute-block-or-clause-python2
----------------------------------
Send block-or-clause at point to Python2 interpreter. 

py-execute-block-or-clause-python2-switch
-----------------------------------------
Send block-or-clause at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-or-clause-python2-noswitch
-------------------------------------------
Send block-or-clause at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-or-clause-python2-dedicated
--------------------------------------------
Send block-or-clause at point to Python2 unique interpreter. 

py-execute-block-or-clause-python2-dedicated-switch
---------------------------------------------------
Send block-or-clause at point to Python2 unique interpreter and switch to result. 

py-execute-block-or-clause-python2\.7
-------------------------------------
Send block-or-clause at point to Python2.7 interpreter. 

py-execute-block-or-clause-python2\.7-switch
--------------------------------------------
Send block-or-clause at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-or-clause-python2\.7-noswitch
----------------------------------------------
Send block-or-clause at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-or-clause-python2\.7-dedicated
-----------------------------------------------
Send block-or-clause at point to Python2.7 unique interpreter. 

py-execute-block-or-clause-python2\.7-dedicated-switch
------------------------------------------------------
Send block-or-clause at point to Python2.7 unique interpreter and switch to result. 

py-execute-block-or-clause-jython
---------------------------------
Send block-or-clause at point to Jython interpreter. 

py-execute-block-or-clause-jython-switch
----------------------------------------
Send block-or-clause at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-or-clause-jython-noswitch
------------------------------------------
Send block-or-clause at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-or-clause-jython-dedicated
-------------------------------------------
Send block-or-clause at point to Jython unique interpreter. 

py-execute-block-or-clause-jython-dedicated-switch
--------------------------------------------------
Send block-or-clause at point to Jython unique interpreter and switch to result. 

py-execute-block-or-clause-python3\.2
-------------------------------------
Send block-or-clause at point to Python3.2 interpreter. 

py-execute-block-or-clause-python3\.2-switch
--------------------------------------------
Send block-or-clause at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-block-or-clause-python3\.2-noswitch
----------------------------------------------
Send block-or-clause at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-block-or-clause-python3\.2-dedicated
-----------------------------------------------
Send block-or-clause at point to Python3.2 unique interpreter. 

py-execute-block-or-clause-python3\.2-dedicated-switch
------------------------------------------------------
Send block-or-clause at point to Python3.2 unique interpreter and switch to result. 

py-execute-def-python
---------------------
Send def at point to Python interpreter. 

py-execute-def-python-switch
----------------------------
Send def at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-def-python-noswitch
------------------------------
Send def at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-def-python-dedicated
-------------------------------
Send def at point to Python unique interpreter. 

py-execute-def-python-dedicated-switch
--------------------------------------
Send def at point to Python unique interpreter and switch to result. 

py-execute-def-ipython
----------------------
Send def at point to IPython interpreter. 

py-execute-def-ipython-switch
-----------------------------
Send def at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-def-ipython-noswitch
-------------------------------
Send def at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-def-ipython-dedicated
--------------------------------
Send def at point to IPython unique interpreter. 

py-execute-def-ipython-dedicated-switch
---------------------------------------
Send def at point to IPython unique interpreter and switch to result. 

py-execute-def-python3
----------------------
Send def at point to Python3 interpreter. 

py-execute-def-python3-switch
-----------------------------
Send def at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-def-python3-noswitch
-------------------------------
Send def at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-def-python3-dedicated
--------------------------------
Send def at point to Python3 unique interpreter. 

py-execute-def-python3-dedicated-switch
---------------------------------------
Send def at point to Python3 unique interpreter and switch to result. 

py-execute-def-python2
----------------------
Send def at point to Python2 interpreter. 

py-execute-def-python2-switch
-----------------------------
Send def at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-def-python2-noswitch
-------------------------------
Send def at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-def-python2-dedicated
--------------------------------
Send def at point to Python2 unique interpreter. 

py-execute-def-python2-dedicated-switch
---------------------------------------
Send def at point to Python2 unique interpreter and switch to result. 

py-execute-def-python2\.7
-------------------------
Send def at point to Python2.7 interpreter. 

py-execute-def-python2\.7-switch
--------------------------------
Send def at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-def-python2\.7-noswitch
----------------------------------
Send def at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-def-python2\.7-dedicated
-----------------------------------
Send def at point to Python2.7 unique interpreter. 

py-execute-def-python2\.7-dedicated-switch
------------------------------------------
Send def at point to Python2.7 unique interpreter and switch to result. 

py-execute-def-jython
---------------------
Send def at point to Jython interpreter. 

py-execute-def-jython-switch
----------------------------
Send def at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-def-jython-noswitch
------------------------------
Send def at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-def-jython-dedicated
-------------------------------
Send def at point to Jython unique interpreter. 

py-execute-def-jython-dedicated-switch
--------------------------------------
Send def at point to Jython unique interpreter and switch to result. 

py-execute-def-python3\.2
-------------------------
Send def at point to Python3.2 interpreter. 

py-execute-def-python3\.2-switch
--------------------------------
Send def at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-def-python3\.2-noswitch
----------------------------------
Send def at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-def-python3\.2-dedicated
-----------------------------------
Send def at point to Python3.2 unique interpreter. 

py-execute-def-python3\.2-dedicated-switch
------------------------------------------
Send def at point to Python3.2 unique interpreter and switch to result. 

py-execute-class-python
-----------------------
Send class at point to Python interpreter. 

py-execute-class-python-switch
------------------------------
Send class at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-class-python-noswitch
--------------------------------
Send class at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-class-python-dedicated
---------------------------------
Send class at point to Python unique interpreter. 

py-execute-class-python-dedicated-switch
----------------------------------------
Send class at point to Python unique interpreter and switch to result. 

py-execute-class-ipython
------------------------
Send class at point to IPython interpreter. 

py-execute-class-ipython-switch
-------------------------------
Send class at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-class-ipython-noswitch
---------------------------------
Send class at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-class-ipython-dedicated
----------------------------------
Send class at point to IPython unique interpreter. 

py-execute-class-ipython-dedicated-switch
-----------------------------------------
Send class at point to IPython unique interpreter and switch to result. 

py-execute-class-python3
------------------------
Send class at point to Python3 interpreter. 

py-execute-class-python3-switch
-------------------------------
Send class at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-class-python3-noswitch
---------------------------------
Send class at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-class-python3-dedicated
----------------------------------
Send class at point to Python3 unique interpreter. 

py-execute-class-python3-dedicated-switch
-----------------------------------------
Send class at point to Python3 unique interpreter and switch to result. 

py-execute-class-python2
------------------------
Send class at point to Python2 interpreter. 

py-execute-class-python2-switch
-------------------------------
Send class at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-class-python2-noswitch
---------------------------------
Send class at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-class-python2-dedicated
----------------------------------
Send class at point to Python2 unique interpreter. 

py-execute-class-python2-dedicated-switch
-----------------------------------------
Send class at point to Python2 unique interpreter and switch to result. 

py-execute-class-python2\.7
---------------------------
Send class at point to Python2.7 interpreter. 

py-execute-class-python2\.7-switch
----------------------------------
Send class at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-class-python2\.7-noswitch
------------------------------------
Send class at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-class-python2\.7-dedicated
-------------------------------------
Send class at point to Python2.7 unique interpreter. 

py-execute-class-python2\.7-dedicated-switch
--------------------------------------------
Send class at point to Python2.7 unique interpreter and switch to result. 

py-execute-class-jython
-----------------------
Send class at point to Jython interpreter. 

py-execute-class-jython-switch
------------------------------
Send class at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-class-jython-noswitch
--------------------------------
Send class at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-class-jython-dedicated
---------------------------------
Send class at point to Jython unique interpreter. 

py-execute-class-jython-dedicated-switch
----------------------------------------
Send class at point to Jython unique interpreter and switch to result. 

py-execute-class-python3\.2
---------------------------
Send class at point to Python3.2 interpreter. 

py-execute-class-python3\.2-switch
----------------------------------
Send class at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-class-python3\.2-noswitch
------------------------------------
Send class at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-class-python3\.2-dedicated
-------------------------------------
Send class at point to Python3.2 unique interpreter. 

py-execute-class-python3\.2-dedicated-switch
--------------------------------------------
Send class at point to Python3.2 unique interpreter and switch to result. 

py-execute-region-python
------------------------
Send region at point to Python interpreter. 

py-execute-region-python-switch
-------------------------------
Send region at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-region-python-noswitch
---------------------------------
Send region at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-region-python-dedicated
----------------------------------
Send region at point to Python unique interpreter. 

py-execute-region-python-dedicated-switch
-----------------------------------------
Send region at point to Python unique interpreter and switch to result. 

py-execute-region-ipython
-------------------------
Send region at point to IPython interpreter. 

py-execute-region-ipython-switch
--------------------------------
Send region at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-region-ipython-noswitch
----------------------------------
Send region at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-region-ipython-dedicated
-----------------------------------
Send region at point to IPython unique interpreter. 

py-execute-region-ipython-dedicated-switch
------------------------------------------
Send region at point to IPython unique interpreter and switch to result. 

py-execute-region-python3
-------------------------
Send region at point to Python3 interpreter. 

py-execute-region-python3-switch
--------------------------------
Send region at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-region-python3-noswitch
----------------------------------
Send region at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-region-python3-dedicated
-----------------------------------
Send region at point to Python3 unique interpreter. 

py-execute-region-python3-dedicated-switch
------------------------------------------
Send region at point to Python3 unique interpreter and switch to result. 

py-execute-region-python2
-------------------------
Send region at point to Python2 interpreter. 

py-execute-region-python2-switch
--------------------------------
Send region at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-region-python2-noswitch
----------------------------------
Send region at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-region-python2-dedicated
-----------------------------------
Send region at point to Python2 unique interpreter. 

py-execute-region-python2-dedicated-switch
------------------------------------------
Send region at point to Python2 unique interpreter and switch to result. 

py-execute-region-python2\.7
----------------------------
Send region at point to Python2.7 interpreter. 

py-execute-region-python2\.7-switch
-----------------------------------
Send region at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-region-python2\.7-noswitch
-------------------------------------
Send region at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-region-python2\.7-dedicated
--------------------------------------
Send region at point to Python2.7 unique interpreter. 

py-execute-region-python2\.7-dedicated-switch
---------------------------------------------
Send region at point to Python2.7 unique interpreter and switch to result. 

py-execute-region-jython
------------------------
Send region at point to Jython interpreter. 

py-execute-region-jython-switch
-------------------------------
Send region at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-region-jython-noswitch
---------------------------------
Send region at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-region-jython-dedicated
----------------------------------
Send region at point to Jython unique interpreter. 

py-execute-region-jython-dedicated-switch
-----------------------------------------
Send region at point to Jython unique interpreter and switch to result. 

py-execute-region-python3\.2
----------------------------
Send region at point to Python3.2 interpreter. 

py-execute-region-python3\.2-switch
-----------------------------------
Send region at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-region-python3\.2-noswitch
-------------------------------------
Send region at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-region-python3\.2-dedicated
--------------------------------------
Send region at point to Python3.2 unique interpreter. 

py-execute-region-python3\.2-dedicated-switch
---------------------------------------------
Send region at point to Python3.2 unique interpreter and switch to result. 

py-execute-buffer-python
------------------------
Send buffer at point to Python interpreter. 

py-execute-buffer-python-switch
-------------------------------
Send buffer at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-buffer-python-noswitch
---------------------------------
Send buffer at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-buffer-python-dedicated
----------------------------------
Send buffer at point to Python unique interpreter. 

py-execute-buffer-python-dedicated-switch
-----------------------------------------
Send buffer at point to Python unique interpreter and switch to result. 

py-execute-buffer-ipython
-------------------------
Send buffer at point to IPython interpreter. 

py-execute-buffer-ipython-switch
--------------------------------
Send buffer at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-buffer-ipython-noswitch
----------------------------------
Send buffer at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-buffer-ipython-dedicated
-----------------------------------
Send buffer at point to IPython unique interpreter. 

py-execute-buffer-ipython-dedicated-switch
------------------------------------------
Send buffer at point to IPython unique interpreter and switch to result. 

py-execute-buffer-python3
-------------------------
Send buffer at point to Python3 interpreter. 

py-execute-buffer-python3-switch
--------------------------------
Send buffer at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-buffer-python3-noswitch
----------------------------------
Send buffer at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-buffer-python3-dedicated
-----------------------------------
Send buffer at point to Python3 unique interpreter. 

py-execute-buffer-python3-dedicated-switch
------------------------------------------
Send buffer at point to Python3 unique interpreter and switch to result. 

py-execute-buffer-python2
-------------------------
Send buffer at point to Python2 interpreter. 

py-execute-buffer-python2-switch
--------------------------------
Send buffer at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-buffer-python2-noswitch
----------------------------------
Send buffer at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-buffer-python2-dedicated
-----------------------------------
Send buffer at point to Python2 unique interpreter. 

py-execute-buffer-python2-dedicated-switch
------------------------------------------
Send buffer at point to Python2 unique interpreter and switch to result. 

py-execute-buffer-python2\.7
----------------------------
Send buffer at point to Python2.7 interpreter. 

py-execute-buffer-python2\.7-switch
-----------------------------------
Send buffer at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-buffer-python2\.7-noswitch
-------------------------------------
Send buffer at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-buffer-python2\.7-dedicated
--------------------------------------
Send buffer at point to Python2.7 unique interpreter. 

py-execute-buffer-python2\.7-dedicated-switch
---------------------------------------------
Send buffer at point to Python2.7 unique interpreter and switch to result. 

py-execute-buffer-jython
------------------------
Send buffer at point to Jython interpreter. 

py-execute-buffer-jython-switch
-------------------------------
Send buffer at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-buffer-jython-noswitch
---------------------------------
Send buffer at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-buffer-jython-dedicated
----------------------------------
Send buffer at point to Jython unique interpreter. 

py-execute-buffer-jython-dedicated-switch
-----------------------------------------
Send buffer at point to Jython unique interpreter and switch to result. 

py-execute-buffer-python3\.2
----------------------------
Send buffer at point to Python3.2 interpreter. 

py-execute-buffer-python3\.2-switch
-----------------------------------
Send buffer at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-buffer-python3\.2-noswitch
-------------------------------------
Send buffer at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-buffer-python3\.2-dedicated
--------------------------------------
Send buffer at point to Python3.2 unique interpreter. 

py-execute-buffer-python3\.2-dedicated-switch
---------------------------------------------
Send buffer at point to Python3.2 unique interpreter and switch to result. 

py-execute-expression-python
----------------------------
Send expression at point to Python interpreter. 

py-execute-expression-python-switch
-----------------------------------
Send expression at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-expression-python-noswitch
-------------------------------------
Send expression at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-expression-python-dedicated
--------------------------------------
Send expression at point to Python unique interpreter. 

py-execute-expression-python-dedicated-switch
---------------------------------------------
Send expression at point to Python unique interpreter and switch to result. 

py-execute-expression-ipython
-----------------------------
Send expression at point to IPython interpreter. 

py-execute-expression-ipython-switch
------------------------------------
Send expression at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-expression-ipython-noswitch
--------------------------------------
Send expression at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-expression-ipython-dedicated
---------------------------------------
Send expression at point to IPython unique interpreter. 

py-execute-expression-ipython-dedicated-switch
----------------------------------------------
Send expression at point to IPython unique interpreter and switch to result. 

py-execute-expression-python3
-----------------------------
Send expression at point to Python3 interpreter. 

py-execute-expression-python3-switch
------------------------------------
Send expression at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-expression-python3-noswitch
--------------------------------------
Send expression at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-expression-python3-dedicated
---------------------------------------
Send expression at point to Python3 unique interpreter. 

py-execute-expression-python3-dedicated-switch
----------------------------------------------
Send expression at point to Python3 unique interpreter and switch to result. 

py-execute-expression-python2
-----------------------------
Send expression at point to Python2 interpreter. 

py-execute-expression-python2-switch
------------------------------------
Send expression at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-expression-python2-noswitch
--------------------------------------
Send expression at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-expression-python2-dedicated
---------------------------------------
Send expression at point to Python2 unique interpreter. 

py-execute-expression-python2-dedicated-switch
----------------------------------------------
Send expression at point to Python2 unique interpreter and switch to result. 

py-execute-expression-python2\.7
--------------------------------
Send expression at point to Python2.7 interpreter. 

py-execute-expression-python2\.7-switch
---------------------------------------
Send expression at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-expression-python2\.7-noswitch
-----------------------------------------
Send expression at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-expression-python2\.7-dedicated
------------------------------------------
Send expression at point to Python2.7 unique interpreter. 

py-execute-expression-python2\.7-dedicated-switch
-------------------------------------------------
Send expression at point to Python2.7 unique interpreter and switch to result. 

py-execute-expression-jython
----------------------------
Send expression at point to Jython interpreter. 

py-execute-expression-jython-switch
-----------------------------------
Send expression at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-expression-jython-noswitch
-------------------------------------
Send expression at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-expression-jython-dedicated
--------------------------------------
Send expression at point to Jython unique interpreter. 

py-execute-expression-jython-dedicated-switch
---------------------------------------------
Send expression at point to Jython unique interpreter and switch to result. 

py-execute-expression-python3\.2
--------------------------------
Send expression at point to Python3.2 interpreter. 

py-execute-expression-python3\.2-switch
---------------------------------------
Send expression at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-expression-python3\.2-noswitch
-----------------------------------------
Send expression at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-expression-python3\.2-dedicated
------------------------------------------
Send expression at point to Python3.2 unique interpreter. 

py-execute-expression-python3\.2-dedicated-switch
-------------------------------------------------
Send expression at point to Python3.2 unique interpreter and switch to result. 

py-execute-partial-expression-python
------------------------------------
Send partial-expression at point to Python interpreter. 

py-execute-partial-expression-python-switch
-------------------------------------------
Send partial-expression at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-partial-expression-python-noswitch
---------------------------------------------
Send partial-expression at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-partial-expression-python-dedicated
----------------------------------------------
Send partial-expression at point to Python unique interpreter. 

py-execute-partial-expression-python-dedicated-switch
-----------------------------------------------------
Send partial-expression at point to Python unique interpreter and switch to result. 

py-execute-partial-expression-ipython
-------------------------------------
Send partial-expression at point to IPython interpreter. 

py-execute-partial-expression-ipython-switch
--------------------------------------------
Send partial-expression at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-partial-expression-ipython-noswitch
----------------------------------------------
Send partial-expression at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-partial-expression-ipython-dedicated
-----------------------------------------------
Send partial-expression at point to IPython unique interpreter. 

py-execute-partial-expression-ipython-dedicated-switch
------------------------------------------------------
Send partial-expression at point to IPython unique interpreter and switch to result. 

py-execute-partial-expression-python3
-------------------------------------
Send partial-expression at point to Python3 interpreter. 

py-execute-partial-expression-python3-switch
--------------------------------------------
Send partial-expression at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-partial-expression-python3-noswitch
----------------------------------------------
Send partial-expression at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-partial-expression-python3-dedicated
-----------------------------------------------
Send partial-expression at point to Python3 unique interpreter. 

py-execute-partial-expression-python3-dedicated-switch
------------------------------------------------------
Send partial-expression at point to Python3 unique interpreter and switch to result. 

py-execute-partial-expression-python2
-------------------------------------
Send partial-expression at point to Python2 interpreter. 

py-execute-partial-expression-python2-switch
--------------------------------------------
Send partial-expression at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-partial-expression-python2-noswitch
----------------------------------------------
Send partial-expression at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-partial-expression-python2-dedicated
-----------------------------------------------
Send partial-expression at point to Python2 unique interpreter. 

py-execute-partial-expression-python2-dedicated-switch
------------------------------------------------------
Send partial-expression at point to Python2 unique interpreter and switch to result. 

py-execute-partial-expression-python2\.7
----------------------------------------
Send partial-expression at point to Python2.7 interpreter. 

py-execute-partial-expression-python2\.7-switch
-----------------------------------------------
Send partial-expression at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-partial-expression-python2\.7-noswitch
-------------------------------------------------
Send partial-expression at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-partial-expression-python2\.7-dedicated
--------------------------------------------------
Send partial-expression at point to Python2.7 unique interpreter. 

py-execute-partial-expression-python2\.7-dedicated-switch
---------------------------------------------------------
Send partial-expression at point to Python2.7 unique interpreter and switch to result. 

py-execute-partial-expression-jython
------------------------------------
Send partial-expression at point to Jython interpreter. 

py-execute-partial-expression-jython-switch
-------------------------------------------
Send partial-expression at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-partial-expression-jython-noswitch
---------------------------------------------
Send partial-expression at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-partial-expression-jython-dedicated
----------------------------------------------
Send partial-expression at point to Jython unique interpreter. 

py-execute-partial-expression-jython-dedicated-switch
-----------------------------------------------------
Send partial-expression at point to Jython unique interpreter and switch to result. 

py-execute-partial-expression-python3\.2
----------------------------------------
Send partial-expression at point to Python3.2 interpreter. 

py-execute-partial-expression-python3\.2-switch
-----------------------------------------------
Send partial-expression at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-partial-expression-python3\.2-noswitch
-------------------------------------------------
Send partial-expression at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-partial-expression-python3\.2-dedicated
--------------------------------------------------
Send partial-expression at point to Python3.2 unique interpreter. 

py-execute-partial-expression-python3\.2-dedicated-switch
---------------------------------------------------------
Send partial-expression at point to Python3.2 unique interpreter and switch to result. 

py-execute-line-python
----------------------
Send line at point to Python interpreter. 

py-execute-line-python-switch
-----------------------------
Send line at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-line-python-noswitch
-------------------------------
Send line at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-line-python-dedicated
--------------------------------
Send line at point to Python unique interpreter. 

py-execute-line-python-dedicated-switch
---------------------------------------
Send line at point to Python unique interpreter and switch to result. 

py-execute-line-ipython
-----------------------
Send line at point to IPython interpreter. 

py-execute-line-ipython-switch
------------------------------
Send line at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-line-ipython-noswitch
--------------------------------
Send line at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-line-ipython-dedicated
---------------------------------
Send line at point to IPython unique interpreter. 

py-execute-line-ipython-dedicated-switch
----------------------------------------
Send line at point to IPython unique interpreter and switch to result. 

py-execute-line-python3
-----------------------
Send line at point to Python3 interpreter. 

py-execute-line-python3-switch
------------------------------
Send line at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-line-python3-noswitch
--------------------------------
Send line at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-line-python3-dedicated
---------------------------------
Send line at point to Python3 unique interpreter. 

py-execute-line-python3-dedicated-switch
----------------------------------------
Send line at point to Python3 unique interpreter and switch to result. 

py-execute-line-python2
-----------------------
Send line at point to Python2 interpreter. 

py-execute-line-python2-switch
------------------------------
Send line at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-line-python2-noswitch
--------------------------------
Send line at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-line-python2-dedicated
---------------------------------
Send line at point to Python2 unique interpreter. 

py-execute-line-python2-dedicated-switch
----------------------------------------
Send line at point to Python2 unique interpreter and switch to result. 

py-execute-line-python2\.7
--------------------------
Send line at point to Python2.7 interpreter. 

py-execute-line-python2\.7-switch
---------------------------------
Send line at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-line-python2\.7-noswitch
-----------------------------------
Send line at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-line-python2\.7-dedicated
------------------------------------
Send line at point to Python2.7 unique interpreter. 

py-execute-line-python2\.7-dedicated-switch
-------------------------------------------
Send line at point to Python2.7 unique interpreter and switch to result. 

py-execute-line-jython
----------------------
Send line at point to Jython interpreter. 

py-execute-line-jython-switch
-----------------------------
Send line at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-line-jython-noswitch
-------------------------------
Send line at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-line-jython-dedicated
--------------------------------
Send line at point to Jython unique interpreter. 

py-execute-line-jython-dedicated-switch
---------------------------------------
Send line at point to Jython unique interpreter and switch to result. 

py-execute-line-python3\.2
--------------------------
Send line at point to Python3.2 interpreter. 

py-execute-line-python3\.2-switch
---------------------------------
Send line at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. 

py-execute-line-python3\.2-noswitch
-----------------------------------
Send line at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' 

py-execute-line-python3\.2-dedicated
------------------------------------
Send line at point to Python3.2 unique interpreter. 

py-execute-line-python3\.2-dedicated-switch
-------------------------------------------
Send line at point to Python3.2 unique interpreter and switch to result. 

