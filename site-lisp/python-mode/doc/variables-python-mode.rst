Variables

====================

py-install-directory
--------------------
Directory where python-mode.el and it’s subdirectories should be installed. Needed for completion and other environment stuff only. 

py-pythonpath
-------------
Define $PYTHONPATH here, if needed.

Emacs doesn’t read .bashrc

python-mode-modeline-display
----------------------------
String to display in Emacs modeline 

py-extensions
-------------
File where extensions to python-mode.el should be installed. Used by virtualenv support. 

info-lookup-mode
----------------
Which Python documentation should be queried.

Make sure it’s accessible from Emacs by M-x info RET ...
See INSTALL-INFO-FILES for help. 

py-fast-process-p
-----------------
Use ‘py-fast-process’.

Commands prefixed "py-fast-..." suitable for large output

See: large output makes Emacs freeze, lp:1253907

Results arrive in output buffer, which is not in comint-mode

py-comment-auto-fill-p
----------------------
When non-nil, fill comments.

Defaut is nil

py-sexp-use-expression-p
------------------------
If non-nil, C-M-s call py-forward-expression.

Respective C-M-b will call py-backward-expression
Default is t

py-session-p
------------
If commands would use an existing process.

If nil, a maybe existing process at py-buffer-name would be killed and re-started

See also ‘py-dedicated-process-p’


py-max-help-buffer-p
--------------------
If "*Python-Help*"-buffer should appear as the only visible.

Default is nil. In help-buffer, "q" will close it.  

py-highlight-error-source-p
---------------------------
When py-execute-... commands raise an error, respective code in source-buffer will be highlighted. Default is nil.

M-x ‘py-remove-overlays-at-point’ removes that highlighting.
 

py-set-pager-cat-p
------------------
If the shell environment variable $PAGER should set to ‘cat’.

If ‘t’, use ‘C-c C-r’ to jump to beginning of output. Then scroll normally.

Avoids lp:783828, "Terminal not fully functional", for help(’COMMAND’) in python-shell

When non-nil, imports module ‘os’ 

py-empty-line-closes-p
----------------------
When non-nil, dedent after empty line following block

if True:
    print("Part of the if-statement")

print("Not part of the if-statement")

Default is nil

If non-nil, a C-j from empty line dedents.

py-prompt-on-changed-p
----------------------
When called interactively, ask for save before a changed buffer is sent to interpreter.

Default is ‘t’

py-dedicated-process-p
----------------------
If commands executing code use a dedicated shell.

Default is nil

When non-nil and ‘py-session-p’, an existing dedicated process is re-used instead of default - which allows executing stuff in parallel.


py-store-result-p
-----------------
When non-nil, put resulting string of ‘py-execute-...’ into kill-ring, so it might be yanked.

Default is nil

py--execute-use-temp-file-p
---------------------------
Assume execution at a remote machine.

 where write-access is not given. 

py-electric-close-active-p
--------------------------
Close completion buffer when it’s sure, it’s no longer needed, i.e. when inserting a space.

Works around a bug in ‘choose-completion’.
Default is ‘nil’

py-update-gud-pdb-history-p
---------------------------
If pdb should provide suggestions WRT file to check and py-pdb-path.

Default is t
See lp:963253


py-pdb-executable
-----------------
Indicate PATH/TO/pdb.

Default is nil
See lp:963253


py-hide-show-minor-mode-p
-------------------------
If hide-show minor-mode should be on, default is nil. 

py-load-skeletons-p
-------------------
If skeleton definitions should be loaded, default is nil.

If non-nil and abbrev-mode on, block-skeletons will inserted.
Pressing "if<SPACE>" for example will prompt for the if-condition.


py-if-name-main-permission-p
----------------------------
Allow execution of code inside blocks started
by "if __name__== ’__main__’:".

Default is non-nil

py-use-font-lock-doc-face-p
---------------------------
If documention string inside of def or class get ‘font-lock-doc-face’.

‘font-lock-doc-face’ inherits ‘font-lock-string-face’.
Call M-x ‘customize-face’ in order to have a visible effect. 

py-empty-comment-line-separates-paragraph-p
-------------------------------------------
Consider paragraph start/end lines with nothing inside but comment sign.

Default is  non-nil

py-indent-honors-inline-comment
-------------------------------
If non-nil, indents to column of inlined comment start.
Default is nil. 

py-auto-fill-mode
-----------------
If python-mode should set fill-column

according values in ‘py-comment-fill-column’ and ‘py-docstring-fill-column’.
Default is  nil

py-error-markup-delay
---------------------
Seconds error’s are highlighted in exception buffer. 

py-fast-completion-delay
------------------------
Used by py--fast-send-string-intern. 

py-new-shell-delay
------------------
If a new comint buffer is connected to Python, commands like completion might need some delay. 

py-autofill-timer-delay
-----------------------
Delay when idle before functions ajusting  ‘py-docstring-fill-column’ resp. ‘py-comment-fill-column’ are called. 

py-docstring-fill-column
------------------------
Value of ‘fill-column’ to use when filling a docstring.
Any non-integer value means do not use a different value of
‘fill-column’ when filling docstrings.

py-comment-fill-column
----------------------
Value of ‘fill-column’ to use when filling a comment.
Any non-integer value means do not use a different value of
‘fill-column’ when filling docstrings.

py-fontify-shell-buffer-p
-------------------------
If code in Python shell should be highlighted as in script buffer.

Default is nil.

If ‘t’, related vars like ‘comment-start’ will be set too.
Seems convenient when playing with stuff in IPython shell
Might not be TRT when a lot of output arrives 

py-modeline-display-full-path-p
-------------------------------
If the full PATH/TO/PYTHON should be displayed in shell modeline.

Default is nil. Note: when ‘py-shell-name’ is specified with path, it’s shown as an acronym in buffer-name already. 

py-modeline-acronym-display-home-p
----------------------------------
If the modeline acronym should contain chars indicating the home-directory.

Default is nil 

py-timer-close-completions-p
----------------------------
If ‘py-timer-close-completion-buffer’ should run, default is non-nil. 

py-smart-operator-mode-p
------------------------
If python-mode calls ‘smart-operator-mode-on’

Default is nil. 

py-autopair-mode
----------------
If python-mode calls (autopair-mode-on)

Default is nil
Load ‘autopair-mode’ written by Joao Tavora <joaotavora [at] gmail.com>
URL: http://autopair.googlecode.com 

py-indent-no-completion-p
-------------------------
If completion function should insert a TAB when no completion found.

Default is ‘nil’

py-company-pycomplete-p
-----------------------
Load company-pycomplete stuff. Default is  nil

py-auto-complete-p
------------------
Run python-mode’s built-in auto-completion via py-complete-function. Default is  nil

py-tab-shifts-region-p
----------------------
If ‘t’, TAB will indent/cycle the region, not just the current line.

Default is  nil
See also ‘py-tab-indents-region-p’

py-tab-indents-region-p
-----------------------
When ‘t’ and first TAB doesn’t shift, indent-region is called.

Default is  nil
See also ‘py-tab-shifts-region-p’

py-block-comment-prefix-p
-------------------------
If py-comment inserts py-block-comment-prefix.

Default is t

py-org-cycle-p
--------------
When non-nil, command ‘org-cycle’ is available at shift-TAB, <backtab>

Default is nil. 

py-set-complete-keymap-p
------------------------
If ‘py-complete-initialize’, which sets up enviroment for Pymacs based py-complete, should load it’s keys into ‘python-mode-map’

Default is nil.
See also resp. edit ‘py-complete-set-keymap’ 

py-outline-minor-mode-p
-----------------------
If outline minor-mode should be on, default is ‘t’. 

py-guess-py-install-directory-p
-------------------------------
If in cases, ‘py-install-directory’ isn’t set,  ‘py-set-load-path’should guess it from ‘buffer-file-name’. 

py-load-pymacs-p
----------------
If Pymacs related stuff should be loaded.

Default is nil.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.ca

py-verbose-p
------------
If functions should report results.

Default is nil. 

py-sexp-function
----------------
When set, it’s value is called instead of ‘forward-sexp’, ‘backward-sexp’

Default is nil. 

py-close-provides-newline
-------------------------
If a newline is inserted, when line after block isn’t empty. Default is non-nil.

When non-nil, ‘py-end-of-def’ and related will work faster

py-dedent-keep-relative-column
------------------------------
If point should follow dedent or kind of electric move to end of line. Default is t - keep relative position. 

py-indent-honors-multiline-listing
----------------------------------
If ‘t’, indents to 1+ column of opening delimiter. If ‘nil’, indent adds one level to the beginning of statement. Default is ‘nil’. 

py-indent-paren-spanned-multilines-p
------------------------------------
If non-nil, indents elements of list a value of ‘py-indent-offset’ to first element:

def foo():
    if (foo &&
            baz):
        bar()

Default lines up with first element:

def foo():
    if (foo &&
        baz):
        bar()

Default is ‘t’

py-closing-list-dedents-bos
---------------------------
When non-nil, indent list’s closing delimiter like start-column.

It will be lined up under the first character of
 the line that starts the multi-line construct, as in:

my_list = [
    1, 2, 3,
    4, 5, 6,
]

result = some_function_that_takes_arguments(
    ’a’, ’b’, ’c’,
    ’d’, ’e’, ’f’,
)

Default is nil, i.e.

my_list = [
    1, 2, 3,
    4, 5, 6,
    ]
result = some_function_that_takes_arguments(
    ’a’, ’b’, ’c’,
    ’d’, ’e’, ’f’,
    )

Examples from PEP8

py-imenu-max-items
------------------
Python-mode specific ‘imenu-max-items’

py-closing-list-space
---------------------
Number of chars, closing parenthesis outdent from opening, default is 1 

py-max-specpdl-size
-------------------
Heuristic exit. Limiting number of recursive calls by py-forward-statement and related functions. Default is max-specpdl-size.

This threshold is just an approximation. It might set far higher maybe.

See lp:1235375. In case code is not to navigate due to errors, ‘which-function-mode’ and others might make Emacs hang. Rather exit than. 

py-closing-list-keeps-space
---------------------------
If non-nil, closing parenthesis dedents onto column of opening plus ‘py-closing-list-space’, default is nil 

py-electric-kill-backward-p
---------------------------
Affects ‘py-electric-backspace’. Default is nil.

If behind a delimited form of braces, brackets or parentheses,
backspace will kill it’s contents

With when cursor after
my_string[0:1]
--------------^

==>

my_string[]
----------^

In result cursor is insided emptied delimited form.

py-electric-colon-active-p
--------------------------
‘py-electric-colon’ feature.  Default is ‘nil’. See lp:837065 for discussions.

See also ‘py-electric-colon-bobl-only’ 

py-electric-colon-bobl-only
---------------------------
When inserting a colon, do not indent lines unless at beginning of block

See lp:1207405 resp. ‘py-electric-colon-active-p’ 

py-electric-yank-active-p
-------------------------
 When non-nil, ‘yank’ will be followed by an ‘indent-according-to-mode’.

Default is nil

py-electric-colon-greedy-p
--------------------------
If py-electric-colon should indent to the outmost reasonable level.

If nil, default, it will not move from at any reasonable level. 

py-electric-colon-newline-and-indent-p
--------------------------------------
If non-nil, ‘py-electric-colon’ will call ‘newline-and-indent’.  Default is ‘nil’. 

py-electric-comment-p
---------------------
If "#" should call ‘py-electric-comment’. Default is ‘nil’. 

py-electric-comment-add-space-p
-------------------------------
If py-electric-comment should add a space.  Default is ‘nil’. 

py-mark-decorators
------------------
If py-mark-def-or-class functions should mark decorators too. Default is ‘nil’. 

py-defun-use-top-level-p
------------------------
When non-nil, keys C-M-a, C-M-e address top-level form.

Default is nil.

Beginning- end-of-defun forms use
commands ‘py-beginning-of-top-level’, ‘py-end-of-top-level’

mark-defun marks top-level form at point etc.

py-tab-indent
-------------
Non-nil means TAB in Python mode calls ‘py-indent-line’.

py-return-key
-------------
Which command <return> should call. 

py-complete-function
--------------------
When set, enforces function todo completion, default is ‘py-fast-complete’.

Might not affect IPython, as ‘py-shell-complete’ is the only known working here.
Normally python-mode knows best which function to use. 

py-encoding-string
------------------
Default string specifying encoding of a Python file. 

py-shebang-startstring
----------------------
Detecting the shell in head of file. 

py-flake8-command
-----------------
Which command to call flake8.

If empty, python-mode will guess some 

py-flake8-command-args
----------------------
Arguments used by flake8.

Default is the empty string. 

py-message-executing-temporary-file
-----------------------------------
If execute functions using a temporary file should message it. Default is ‘t’.

Messaging increments the prompt counter of IPython shell. 

py-execute-no-temp-p
--------------------
Seems Emacs-24.3 provided a way executing stuff without temporary files. 

py-lhs-inbound-indent
---------------------
When line starts a multiline-assignment: How many colums indent should be more than opening bracket, brace or parenthesis. 

py-continuation-offset
----------------------
Additional amount of offset to give for some continuation lines.
Continuation lines are those that immediately follow a backslash
terminated line. 

py-indent-tabs-mode
-------------------
Python-mode starts ‘indent-tabs-mode’ with the value specified here, default is nil. 

py-smart-indentation
--------------------
Should ‘python-mode’ try to automagically set some indentation variables?
When this variable is non-nil, two things happen when a buffer is set
to ‘python-mode’:

 1. ‘py-indent-offset’ is guessed from existing code in the buffer.
 Only guessed values between 2 and 8 are considered.  If a valid
 guess can’t be made (perhaps because you are visiting a new
 file), then the value in ‘py-indent-offset’ is used.

 2. ‘tab-width’ is setq to ‘py-indent-offset’ if not equal
 already. ‘indent-tabs-mode’ inserts one tab one
 indentation level, otherwise spaces are used.

 Note that both these settings occur *after* ‘python-mode-hook’ is run,
 so if you want to defeat the automagic configuration, you must also
 set ‘py-smart-indentation’ to nil in your ‘python-mode-hook’.

py-block-comment-prefix
-----------------------
String used by M-x comment-region to comment out a block of code.
This should follow the convention for non-indenting comment lines so
that the indentation commands won’t get confused (i.e., the string
should be of the form ‘#x...’ where ‘x’ is not a blank or a tab, and
 ‘...’ is arbitrary).  However, this string should not end in whitespace.

py-indent-offset
----------------
Amount of offset per level of indentation.
 ‘M-x py-guess-indent-offset’ can usually guess a good value when
you’re editing someone else’s Python code.

py-backslashed-lines-indent-offset
----------------------------------
Amount of offset per level of indentation of backslashed.
No semantic indent,  which diff to ‘py-indent-offset’ indicates 

py-pdb-path
-----------
Where to find pdb.py. Edit this according to your system.

If you ignore the location ‘M-x py-guess-pdb-path’ might display it.

py-indent-comments
------------------
When t, comment lines are indented. 

py-uncomment-indents-p
----------------------
When non-nil, after uncomment indent lines. 

py-separator-char
-----------------
Values set by defcustom only will not be seen in batch-mode. 

py-custom-temp-directory
------------------------
If set, will take precedence over guessed values from ‘py-temp-directory’. Default is the empty string. 

py-beep-if-tab-change
---------------------
Ring the bell if ‘tab-width’ is changed.
If a comment of the form

                           	# vi:set tabsize=<number>:

is found before the first code line when the file is entered, and the
current value of (the general Emacs variable) ‘tab-width’ does not
equal <number>, ‘tab-width’ is set to <number>, a message saying so is
displayed in the echo area, and if ‘py-beep-if-tab-change’ is non-nil
the Emacs bell is also rung as a warning.

py-jump-on-exception
--------------------
Jump to innermost exception frame in Python output buffer.
When this variable is non-nil and an exception occurs when running
Python code synchronously in a subprocess, jump immediately to the
source code of the innermost traceback frame.

py-ask-about-save
-----------------
If not nil, ask about which buffers to save before executing some code.
Otherwise, all modified buffers are saved without asking.

py-delete-function
------------------
Function called by ‘py-electric-delete’ when deleting forwards.

py-pdbtrack-do-tracking-p
-------------------------
Controls whether the pdbtrack feature is enabled or not.
When non-nil, pdbtrack is enabled in all comint-based buffers,
e.g. shell buffers and the *Python* buffer.  When using pdb to debug a
Python program, pdbtrack notices the pdb prompt and displays the
source file and line that the program is stopped at, much the same way
as gud-mode does for debugging C programs with gdb.

py-pdbtrack-filename-mapping
----------------------------
Supports mapping file paths when opening file buffers in pdbtrack.
When non-nil this is an alist mapping paths in the Python interpreter
to paths in Emacs.

py-pdbtrack-minor-mode-string
-----------------------------
String to use in the minor mode list when pdbtrack is enabled.

py-import-check-point-max
-------------------------
Maximum number of characters to search for a Java-ish import statement.
When ‘python-mode’ tries to calculate the shell to use (either a
CPython or a Jython shell), it looks at the so-called ‘shebang’ line
                           -- i.e. #! line.  If that’s not available, it looks at some of the
file heading imports to see if they look Java-like.

py-jython-packages
------------------
Imported packages that imply ‘jython-mode’.

py-current-defun-show
---------------------
If ‘py-current-defun’ should jump to the definition, highlight it while waiting PY-WHICH-FUNC-DELAY seconds, before returning to previous position.

Default is ‘t’.

py-current-defun-delay
----------------------
When called interactively, ‘py-current-defun’ should wait PY-WHICH-FUNC-DELAY seconds at the definition name found, before returning to previous position. 

py--delete-temp-file-delay
--------------------------
Used by ‘py--delete-temp-file’

py-python-send-delay
--------------------
Seconds to wait for output, used by ‘py--send-...’ functions.

See also py-ipython-send-delay

py-ipython-send-delay
---------------------
Seconds to wait for output, used by ‘py--send-...’ functions.

See also py-python-send-delay

py-master-file
--------------
If non-nil, M-x py-execute-buffer executes the named
master file instead of the buffer’s file.  If the file name has a
relative path, the value of variable ‘default-directory’ for the
buffer is prepended to come up with a file name.

Beside you may set this variable in the file’s local
variable section, e.g.:

                           # Local Variables:
                           # py-master-file: "master.py"
                           # End:

                           

py-pychecker-command
--------------------
Shell command used to run Pychecker.

py-pychecker-command-args
-------------------------
String arguments to be passed to pychecker.

py-pyflakes-command
-------------------
Shell command used to run Pyflakes.

py-pyflakes-command-args
------------------------
String arguments to be passed to pyflakes.

Default is ""

py-pep8-command
---------------
Shell command used to run pep8.

py-pep8-command-args
--------------------
String arguments to be passed to pylint.

Default is "" 

py-pyflakespep8-command
-----------------------
Shell command used to run ‘pyflakespep8’.

py-pyflakespep8-command-args
----------------------------
string arguments to be passed to pyflakespep8.

Default is "" 

py-pylint-command
-----------------
Shell command used to run Pylint.

py-pylint-command-args
----------------------
String arguments to be passed to pylint.

Default is "--errors-only" 

py-shell-input-prompt-1-regexp
------------------------------
A regular expression to match the input prompt of the shell.

py-shell-input-prompt-2-regexp
------------------------------
A regular expression to match the input prompt of the shell after the
first line of input.

py-shell-prompt-read-only
-------------------------
If non-nil, the python prompt is read only.  Setting this
variable will only effect new shells.

py-honor-IPYTHONDIR-p
---------------------
When non-nil ipython-history file is constructed by $IPYTHONDIR
followed by "/history". Default is nil.

Otherwise value of py-ipython-history is used. 

py-ipython-history
------------------
ipython-history default file. Used when py-honor-IPYTHONDIR-p is nil (default) 

py-honor-PYTHONHISTORY-p
------------------------
When non-nil python-history file is set by $PYTHONHISTORY
Default is nil.

Otherwise value of py-python-history is used. 

py-python-history
-----------------
python-history default file. Used when py-honor-PYTHONHISTORY-p is nil (default) 

py-switch-buffers-on-execute-p
------------------------------
When non-nil switch to the Python output buffer.

If ‘py-keep-windows-configuration’ is t, this will take precedence over setting here. 

py-split-window-on-execute
--------------------------
When non-nil split windows.

Default is just-two - when code is send to interpreter, split screen into source-code buffer and current py-shell result.

Other buffer will be hidden that way.

When set to ‘t’, python-mode tries to reuse existing windows and will split only if needed.

With ’always, results will displayed in a new window.

Both ‘t’ and ‘always’ is experimental still.

For the moment: If a multitude of python-shells/buffers should be
visible, open them manually and set ‘py-keep-windows-configuration’ to ‘t’.

See also ‘py-keep-windows-configuration’


py-split-window-on-execute-threshold
------------------------------------
Maximal number of displayed windows.

Honored, when ‘py-split-window-on-execute’ is ‘t’, i.e. "reuse".
Don’t split when max number of displayed windows is reached. 

py-split-windows-on-execute-function
------------------------------------
How window should get splitted to display results of py-execute-... functions. 

py-shell-fontify-style
----------------------
Fontify current input resp. output in Python shell. Default is nil.

INPUT will leave output unfontified.
ALL keeps output fontified.

At any case only current input gets fontified.


py-hide-show-keywords
---------------------
Keywords composing visible heads. 

py-hide-show-hide-docstrings
----------------------------
Controls if doc strings can be hidden by hide-show

py-hide-comments-when-hiding-all
--------------------------------
Hide the comments too when you do an ‘hs-hide-all’.

py-outline-mode-keywords
------------------------
Keywords composing visible heads. 

python-mode-hook
----------------
Hook run after entering python-mode-modeline-display mode.
No problems result if this variable is not bound.
‘add-hook’ automatically binds it.  (This is true for all hook variables.)

py-shell-name
-------------
A PATH/TO/EXECUTABLE or default value ‘py-shell’ may look for, if no shell is specified by command.

On Windows default is C:/Python27/python
--there is no garantee it exists, please check your system--

Else python

py-python-command
-----------------
Make sure, the directory where python.exe resides in in the PATH-variable.

Windows: If needed, edit in "Advanced System Settings/Environment Variables" Commonly "C:\\Python27\\python.exe"
With Anaconda for example the following works here:
"C:\\Users\\My-User-Name\\Anaconda\\Scripts\\python.exe"

Else /usr/bin/python

py-python-command-args
----------------------
String arguments to be used when starting a Python shell.

py-python2-command
------------------
Make sure, the directory where python.exe resides in in the PATH-variable.

Windows: If needed, edit in "Advanced System Settings/Environment Variables" Commonly "C:\\Python27\\python.exe"
With Anaconda for example the following works here:
"C:\\Users\\My-User-Name\\Anaconda\\Scripts\\python.exe"

Else /usr/bin/python

py-python2-command-args
-----------------------
String arguments to be used when starting a Python shell.

py-python3-command
------------------
A PATH/TO/EXECUTABLE or default value ‘py-shell’ may look for, if
  no shell is specified by command.

On Windows see C:/Python3/python.exe
--there is no garantee it exists, please check your system--

At GNU systems see /usr/bin/python3

py-python3-command-args
-----------------------
String arguments to be used when starting a Python3 shell.

py-ipython-command
------------------
A PATH/TO/EXECUTABLE or default value ‘M-x IPython RET’ may look for, if no IPython-shell is specified by command.

On Windows default is "C:\\Python27\\python.exe"
While with Anaconda for example the following works here:
"C:\\Users\\My-User-Name\\Anaconda\\Scripts\\ipython.exe"

Else /usr/bin/ipython

py-ipython-command-args
-----------------------
String arguments to be used when starting a Python shell.
At Windows make sure ipython-script.py is PATH. Also setting PATH/TO/SCRIPT here should work, for example;
C:\Python27\Scripts\ipython-script.py
With Anaconda the following is known to work:
"C:\\Users\\My-User-Name\\Anaconda\\Scripts\\ipython-script-py"


py-jython-command
-----------------
A PATH/TO/EXECUTABLE or default value ‘M-x Jython RET’ may look for, if no Jython-shell is specified by command.

Not known to work at windows
Default /usr/bin/jython

py-jython-command-args
----------------------
String arguments to be used when starting a Python shell.

py-shell-toggle-1
-----------------
A PATH/TO/EXECUTABLE or default value used by ‘py-toggle-shell’. 

py-shell-toggle-2
-----------------
A PATH/TO/EXECUTABLE or default value used by ‘py-toggle-shell’. 

py--imenu-create-index-p
------------------------
Non-nil means Python mode creates and displays an index menu of functions and global variables. 

py-match-paren-mode
-------------------
Non-nil means, cursor will jump to beginning or end of a block.
This vice versa, to beginning first.
Sets ‘py-match-paren-key’ in python-mode-map.
Customize ‘py-match-paren-key’ which key to use. 

py-match-paren-key
------------------
String used by M-x comment-region to comment out a block of code.
This should follow the convention for non-indenting comment lines so
that the indentation commands won’t get confused (i.e., the string
should be of the form ‘#x...’ where ‘x’ is not a blank or a tab, and
                               ‘...’ is arbitrary).  However, this string should not end in whitespace.

py-kill-empty-line
------------------
If t, py-indent-forward-line kills empty lines. 

py-imenu-show-method-args-p
---------------------------
Controls echoing of arguments of functions & methods in the Imenu buffer.
When non-nil, arguments are printed.

py-use-local-default
--------------------
If ‘t’, py-shell will use ‘py-shell-local-path’ instead
of default Python.

Making switch between several virtualenv’s easier,
                               ‘python-mode’ should deliver an installer, so named-shells pointing to virtualenv’s will be available. 

py-edit-only-p
--------------
When ‘t’ ‘python-mode’ will not take resort nor check for installed Python executables. Default is nil.

See bug report at launchpad, lp:944093. 

py-force-py-shell-name-p
------------------------
When ‘t’, execution with kind of Python specified in ‘py-shell-name’ is enforced, possibly shebang doesn’t take precedence. 

python-mode-v5-behavior-p
-------------------------
Execute region through ‘shell-command-on-region’ as
v5 did it - lp:990079. This might fail with certain chars - see UnicodeEncodeError lp:550661

py-trailing-whitespace-smart-delete-p
-------------------------------------
Default is nil. When t, python-mode calls
    (add-hook ’before-save-hook ’delete-trailing-whitespace nil ’local)

Also commands may delete trailing whitespace by the way.
When editing other peoples code, this may produce a larger diff than expected 

py-newline-delete-trailing-whitespace-p
---------------------------------------
Delete trailing whitespace maybe left by ‘py-newline-and-indent’.

Default is ‘t’. See lp:1100892 

py--warn-tmp-files-left-p
-------------------------
Messages a warning, when ‘py-temp-directory’ contains files susceptible being left by previous Python-mode sessions. See also lp:987534 

py-complete-ac-sources
----------------------
List of auto-complete sources assigned to ‘ac-sources’ in ‘py-complete-initialize’.

Default is known to work an Ubuntu 14.10 - having python-
mode, pymacs and auto-complete-el, with the following minimal
emacs initialization:

(require ’pymacs)
(require ’auto-complete-config)
(ac-config-default)



py-remove-cwd-from-path
-----------------------
Whether to allow loading of Python modules from the current directory.
If this is non-nil, Emacs removes ’’ from sys.path when starting
a Python process.  This is the default, for security
reasons, as it is easy for the Python process to be started
without the user’s realization (e.g. to perform completion).

py-shell-local-path
-------------------
If ‘py-use-local-default’ is non-nil, ‘py-shell’ will use EXECUTABLE indicated here incl. path. 

py-python-edit-version
----------------------
When not empty, fontify according to Python version specified.

Default is the empty string, a useful value "python3" maybe.

When empty, version is guessed via ‘py-choose-shell’. 

py-ipython-execute-delay
------------------------
Delay needed by execute functions when no IPython shell is running. 

py--imenu-create-index-function
-------------------------------
Switch between ‘py--imenu-create-index-new’, which also lists modules variables,  and series 5. index-machine

py-docstring-style
------------------
Implemented styles are DJANGO, ONETWO, PEP-257, PEP-257-NN,
SYMMETRIC, and NIL.

A value of NIL won’t care about quotes
position and will treat docstrings a normal string, any other
value may result in one of the following docstring styles:

DJANGO:

    """
    Process foo, return bar.
    """

    """
    Process foo, return bar.

    If processing fails throw ProcessingError.
    """

ONETWO:

    """Process foo, return bar."""

    """
    Process foo, return bar.

    If processing fails throw ProcessingError.

    """

PEP-257:

    """Process foo, return bar."""

    """Process foo, return bar.

    If processing fails throw ProcessingError.

    """

PEP-257-NN:

    """Process foo, return bar."""

    """Process foo, return bar.

    If processing fails throw ProcessingError.
    """

SYMMETRIC:

    """Process foo, return bar."""

    """
    Process foo, return bar.

    If processing fails throw ProcessingError.
    """

py-execute-directory
--------------------
When set, stores the file’s default directory-name py-execute-... functions act upon.

Used by Python-shell for output of ‘py-execute-buffer’ and related commands. See also ‘py-use-current-dir-when-execute-p’

py-use-current-dir-when-execute-p
---------------------------------
When ‘t’, current directory is used by Python-shell for output of ‘py-execute-buffer’ and related commands.

See also ‘py-execute-directory’

py-keep-shell-dir-when-execute-p
--------------------------------
Don’t change Python shell’s current working directory when sending code.

See also ‘py-execute-directory’

py-fileless-buffer-use-default-directory-p
------------------------------------------
When ‘py-use-current-dir-when-execute-p’ is non-nil and no buffer-file exists, value of ‘default-directory’ sets current working directory of Python output shell

py-check-command
----------------
Command used to check a Python file.

py-ffap-p
---------
Select python-modes way to find file at point.

Default is nil 

py-keep-windows-configuration
-----------------------------
Takes precedence over ‘py-split-window-on-execute’ and ‘py-switch-buffers-on-execute-p’.

See lp:1239498

To suppres window-changes due to error-signaling also, set ‘py-keep-windows-configuration’ onto ’force

Default is nil 

py-shell-prompt-regexp
----------------------
Regular Expression matching top-level input prompt of python shell.
It should not contain a caret (^) at the beginning.

py-shell-prompt-output-regexp
-----------------------------
Regular Expression matching output prompt of python shell.
It should not contain a caret (^) at the beginning.

py-debug-p
----------
When non-nil, keep resp. store information useful for debugging.

Temporary files are not deleted. Other functions might implement
some logging etc. 

py-section-start
----------------
Delimit arbitrary chunks of code. 

py-section-end
--------------
Delimit arbitrary chunks of code. 

py-paragraph-re
---------------
Allow Python specific paragraph-start var

py-outdent-re-raw
-----------------


py-no-outdent-re-raw
--------------------


py-block-or-clause-re-raw
-------------------------
Matches the beginning of a compound statement or it’s clause. 

py-block-re-raw
---------------
Matches the beginning of a compound statement but not it’s clause. 

py-extended-block-or-clause-re-raw
----------------------------------
Matches the beginning of a compound statement or it’s clause. 

py-top-level-re
---------------
A form which starts at zero indent level, but is not a comment. 

py-clause-re-raw
----------------
Matches the beginning of a clause. 

py-compilation-regexp-alist
---------------------------
Fetch errors from Py-shell.
hooked into ‘compilation-error-regexp-alist’  

py-shell-unfontify-p
--------------------
Run ‘py--run-unfontify-timer’ unfontifying the shell banner-text.

Default is nil 

py-underscore-word-syntax-p
---------------------------
If underscore chars should be of syntax-class ‘word’, not of ‘symbol’.

Underscores in word-class makes ‘forward-word’ etc. travel the indentifiers. Default is ‘t’.

See bug report at launchpad, lp:940812 

