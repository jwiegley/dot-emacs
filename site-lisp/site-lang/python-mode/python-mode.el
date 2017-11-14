;;; python-mode.el --- Towards an Python-IDE in Emacs

;; Maintainer: Andreas Roehler <andreas.roehler@online.de>
;; Keywords: languages, processes, python, oop

;; Copyright (C) 1992,1993,1994  Tim Peters

;; Author: 2003-2011 https://launchpad.net/python-mode
;;         1995-2002 Barry A. Warsaw
;;         1992-1994 Tim Peters
;; Maintainer: python-mode@python.org
;; Created:    Feb 1992
;; Keywords:   python languages oop

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code

(require 'comint)
(require 'custom)
(eval-when-compile (require 'cl))
(require 'compile)
(require 'ansi-color)
(require 'cc-cmds)
(require 'shell)
(require 'rx)
(require 'flymake)

(defgroup python-mode nil
  "Support for the Python programming language, <http://www.python.org/>"
  :group 'languages
  :prefix "py-")

(defconst py-version "6.0.8")

(defvar python-local-version nil
  "Used internally. ")
(make-variable-buffer-local 'python-local-version)

(defvar py-local-command nil
  "Returns locally used executable-name. ")
(make-variable-buffer-local 'py-local-command)

(defvar py-local-versioned-command nil
  "Returns locally used executable-name including its version. ")
(make-variable-buffer-local 'py-local-versioned-command)

;;; User definable variables
(defcustom py-indent-offset 4
  "*Amount of offset per level of indentation.
`\\[py-guess-indent-offset]' can usually guess a good value when
you're editing someone else's Python code."
  :type 'integer
  :group 'python-mode)
(make-variable-buffer-local 'py-indent-offset)

(defcustom pdb-path '/usr/lib/python2.7/pdb.py
  "Where to find pdb.py. Edit this according to your system.

If you ignore the location `M-x py-guess-pdb-path' might display it.
"
  :type 'variable
  :group 'python-mode)

(defcustom py-verbose-p nil
  "If indenting functions should report reached indent level.

Default is nil. "

  :type 'boolean
  :group 'python-mode)

(defun py-guess-pdb-path ()
  "If py-pdb-path isn't set, find location of pdb.py. "
  (interactive)
  (let ((ele (split-string (shell-command-to-string "whereis python")))
        erg)
    (while (or (not erg)(string= "" erg))
      (when (and (string-match "^/" (car ele)) (not (string-match "/man" (car ele))))
        (setq erg (shell-command-to-string (concat "find " (car ele) " -type f -name \"pdb.py\""))))
      (setq ele (cdr ele)))
    (if erg
        (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      (when (interactive-p) (message "%s" "pdb.py not found, please customize `pdb-path'")))
    (concat "'" erg)))

(defcustom py-install-directory ""
  "Directory where python-mode.el and it's subdirectories should be installed. Needed for completion and other environment stuff only. "
  :type 'string
  :group 'python-mode)

(defcustom py-guess-py-install-directory-p t
  "If in cases, `py-install-directory' isn't set,  `py-set-load-path'should guess it from `buffer-file-name'. "

  :type 'boolean
  :group 'python-mode)

(defcustom py-load-pymacs-p  nil
  "If Pymacs as delivered with python-mode.el shall be loaded.
Default is nil.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.ca"

  :type 'boolean
  :group 'python-mode)

(defcustom py-report-position-p nil
  "If functions moving point like `py-forward-into-nomenclature' should report reached position.

Default is nil. "

  :type 'boolean
  :group 'python-mode)

(defcustom py-extensions "py-extensions.el"
  "File where extensions to python-mode.el should be installed. Used by virtualenv support. "

  :type 'string
  :group 'python-mode)

(defcustom py-hide-show-minor-mode-p nil
  "If hide-show minor-mode should be on, default is nil. "

  :type 'boolean
  :group 'python-mode)

(defcustom py-org-cycle-p nil
  "When non-nil, command `org-cycle' is available at shift-TAB, <backtab>

Default is nil. "

  :type 'boolean
  :group 'python-mode)

(defcustom ipython-complete-use-separate-shell-p t

  "If `ipython-complete' should use a separate shell. Thus prompt-counter is not incremented by completion. "
  :type 'boolean :group 'python-mode)

(defcustom py-outline-minor-mode-p t
  "If outline minor-mode should be on, default is `t'. "

  :type 'boolean
  :group 'python-mode)

(defcustom py-outline-mode-keywords
  '("class"    "def"    "elif"    "else"    "except"
    "for"      "if"     "while"   "finally" "try"
    "with")
  "Keywords composing visible heads. "
  :type '(repeat string)
  :group 'python-mode)

(defcustom py-start-run-py-shell t
  "If `python-mode' should start a python-shell, `py-shell'. Default is `t'. "

  :type 'boolean
  :group 'python-mode)

(defcustom py-start-run-ipython-shell t
  "If `python-mode' should start an ipython-shell. Default is `t'.

A running ipython-shell presently is needed by `ipython-complete', otherwise first try will fail. "

  :type 'boolean
  :group 'python-mode)

;; vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv
(defcustom py-close-provides-newline t
  "If a newline is inserted, when line after block isn't empty. Default is non-nil. "
  :type 'boolean
  :group 'python-mode)
(make-variable-buffer-local 'py-close-provides-newline)

(defcustom py-dedent-keep-relative-column t
  "If point should follow dedent or kind of electric move to end of line. Default is t - keep relative position. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-indent-honors-multiline-listing nil
  "If `t', indents to 1+ column of opening delimiter. If `nil', indent adds one level to the beginning of statement. Default is `nil'. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-indent-honors-inline-comment nil
  "If non-nil, indents to column of inlined comment start.
Default is nil. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-closing-list-dedents-bos nil
  "If non-nil, closing parentesis dedents onto column of statement, otherwise keeps additional `py-indent-offset', default is nil "
  :type 'boolean
  :group 'python-mode)

(defcustom py-electric-colon-active-p nil
  "`py-electric-colon' feature.  Default is `nil'. See lp:837065 for discussions. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-electric-comment-p t
  "If \"#\" should call `py-electric-comment'. Default is `t'. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-electric-comment-add-space-p nil
  "If py-electric-comment should add a space.  Default is `nil'. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-mark-decorators nil
  "If py-mark-def-or-class functions should mark decorators too. Default is `nil'. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-tab-indent t
  "*Non-nil means TAB in Python mode calls `py-indent-line'."
  :type 'boolean
  :group 'python-mode)

(defcustom py-complete-function 'nil
  "When set, enforces function todo completion, default is nil.

Normally python-mode, resp. inferior-python-mode know best which functin to use. "
  :type '(choice
          (const :tag "default" nil)
          (const :tag "py-completion-at-point" py-completion-at-point)
          (const :tag "Pymacs based py-complete" py-complete)
          (const :tag "py-shell-complete" py-shell-complete)
          (const :tag "IPython's ipython-complete" ipython-complete)
          )
  :group 'python-mode)

(defcustom ipython-complete-function 'ipython-complete
  "Function used for completion in IPython shell buffers.

Minor bug: `ipython-complete' raises the prompt counter when completion done

Richard Everson commented:

    I don't know how to stop IPython from incrementing the prompt
    counter, but using py-completion-at-point just hangs emacs for
    me. If I start with a new IPython shell, then

    In [1]: import sys

    In [2]: sys.pa

    then M-x py-completion-at-point, hoping to complete to sys.path, Emacs
    hangs.  Escaping out of it shows that the \*Python\* buffer has the
    contents:

    >>> Traceback (most recent call last):
      File \"<stdin>\", line 1, in <module>
    NameError: name 'nil' is not defined
    >>> =
    [ ... ]

    On the other hand, IPython's interaction and completion itself is pretty
    impressive (for versions greater than 0.10 at least): it inserts the
    correct indentation for for, if, etc and it will show completions even
    within a loop.  Here's an example from a terminal shell:

    In [1]:

    In [1]: for i in range(3):
       ...:     print i, sys.p<------------ Pressed tab here; indentation inser=
    ted automatically
    sys.path                 sys.path_importer_cache  sys.prefix
    sys.path_hooks           sys.platform             sys.py3kwarning
       ...:     print i, sys.path<------------ Pressed tab again
    sys.path                 sys.path_hooks           sys.path_importer_cache
"
  :type '(choice (const :tag "py-completion-at-point" py-completion-at-point)
                 (const :tag "py-shell-complete" py-shell-complete)
		 (const :tag "Pymacs based py-complete" py-complete)
                 (const :tag "IPython's ipython-complete" ipython-complete))
  :group 'python-mode)
(make-variable-buffer-local 'ipython-complete-function)

(defcustom py-encoding-string " # -*- coding: utf-8 -*-"
  "Default string specifying encoding of a Python file. "
  :type 'string
  :group 'python-mode)

(defvar py-encoding-string-re "^[ \t]*#[ \t]*-\\*-[ \t]*coding:.+-\\*-"
  "Matches encoding string of a Python file. ")

(defvar symbol-definition-start-re)
(setq symbol-definition-start-re "^[ \t]*(\\(defun\\|defvar\\|defcustom\\)")
(defcustom py-shebang-startstring "#! /bin/env"
  "Detecting the shell in head of file. "
  :type 'string
  :group 'python-mode)

(defvar py-shebang-regexp "#![ \t]?\\([^ \t\n]+\\)[ \t]?\\([iptj]+ython[^ \t\n]*\\)"
  "Detecting the shell in head of file. ")

(defcustom py-python-command-args '("-i")
  "*List of string arguments to be used when starting a Python shell."
  :type '(repeat string)
  :group 'python-mode)
(make-variable-buffer-local 'py-python-command-args)

(set-default 'py-python-command-args  '("-i"))

(make-obsolete-variable 'py-jpython-command-args 'py-jython-command-args nil)
(defcustom py-jython-command-args '("-i")
  "*List of string arguments to be used when starting a Jython shell."
  :type '(repeat string)
  :group 'python-mode
  :tag "Jython Command Args")

(defcustom py-cleanup-temporary t
  "If temporary buffers and files used by functions executing region should be deleted afterwards. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-lhs-inbound-indent 1
  "When line starts a multiline-assignment: How many colums indent should be more than opening bracket, brace or parenthesis. "
  :type 'integer
  :group 'python-mode)
(make-variable-buffer-local 'py-lhs-inbound-indent)

(defcustom py-rhs-inbound-indent 1
  "When inside a multiline-assignment: How many colums indent should be more than opening bracket, brace or parenthesis. "
  :type 'integer
  :group 'python-mode)
(make-variable-buffer-local 'py-rhs-inbound-indent)

(defcustom py-continuation-offset 2
  "*Additional amount of offset to give for some continuation lines.
Continuation lines are those that immediately follow a backslash
terminated line. "
  :type 'integer
  :group 'python-mode)

(defcustom py-indent-tabs-mode nil
  "Python-mode starts `indent-tabs-mode' with the value specified here, default is nil. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-smart-indentation t
  "*Should `python-mode' try to automagically set some indentation variables?
When this variable is non-nil, two things happen when a buffer is set
to `python-mode':

    1. `py-indent-offset' is guessed from existing code in the buffer.
       Only guessed values between 2 and 8 are considered.  If a valid
       guess can't be made (perhaps because you are visiting a new
       file), then the value in `py-indent-offset' is used.

    2. `indent-tabs-mode' is turned off if `py-indent-offset' does not
       equal `tab-width' (`indent-tabs-mode' is never turned on by
       Python mode).  This means that for newly written code, tabs are
       only inserted in indentation if one tab is one indentation
       level, otherwise only spaces are used.

Note that both these settings occur *after* `python-mode-hook' is run,
so if you want to defeat the automagic configuration, you must also
set `py-smart-indentation' to nil in your `python-mode-hook'."
  :type 'boolean
  :group 'python-mode)
(make-variable-buffer-local 'py-smart-indentation)

(defcustom py-align-multiline-strings-p t
  "*Flag describing how multi-line triple quoted strings are aligned.
When this flag is non-nil, continuation lines are lined up under the
preceding line's indentation.  When this flag is nil, continuation
lines are aligned to column zero."
  :type '(choice (const :tag "Align under preceding line" t)
                 (const :tag "Align to column zero" nil))
  :group 'python-mode)

(defcustom py-block-comment-prefix "##"
  "*String used by \\[comment-region] to comment out a block of code.
This should follow the convention for non-indenting comment lines so
that the indentation commands won't get confused (i.e., the string
should be of the form `#x...' where `x' is not a blank or a tab, and
`...' is arbitrary).  However, this string should not end in whitespace."
  :type 'string
  :group 'python-mode)

(defcustom py-indent-comments t
  "When t, comment lines are indented. "
  :type 'boolean
  :group 'python-mode)

(defvar py-separator-char 47
  "Values set by defcustom only will not be seen in batch-mode. ")

(defcustom py-separator-char 47
  "The character, which separates the system file-path components.

Precedes guessing when not empty, returned by function `py-separator-char'. "
  :type 'character
  :group 'python-mode)

(defcustom py-custom-temp-directory ""
  "If set, will take precedence over guessed values from `py-temp-directory'. Default is the empty string.

When set, make sure the directory exists. "
  :type 'string
  :group 'python-mode)

(defvar py-temp-directory
  (let ((ok '(lambda (x)
               (and x
                    (setq x (expand-file-name x)) ; always true
                    (file-directory-p x)
                    (file-writable-p x)
                    x)))
        erg)
    (or
     (and (not (string= "" py-custom-temp-directory))
          (if (funcall ok py-custom-temp-directory)
              (setq erg (expand-file-name py-custom-temp-directory))
            (if (file-directory-p (expand-file-name py-custom-temp-directory))
                (error "py-custom-temp-directory set but not writable")
              (error "py-custom-temp-directory not an existing directory"))))
     (and (funcall ok (getenv "TMPDIR"))
          (setq erg (getenv "TMPDIR")))
     (and (funcall ok (getenv "TEMP/TMP"))
          (setq erg (getenv "TEMP/TMP")))
     (and (funcall ok "/usr/tmp")
          (setq erg "/usr/tmp"))
     (and (funcall ok "/tmp")
          (setq erg "/tmp"))
     (and (funcall ok "/var/tmp")
          (setq erg "/var/tmp"))
     (and (eq system-type 'darwin)
          (funcall ok "/var/folders")
          (setq erg "/var/folders"))
     (and (or (eq system-type 'ms-dos)(eq system-type 'windows-nt))
          (funcall ok (concat "c:" (py-separator-char) "Users"))
          (setq erg (concat "c:" (py-separator-char) "Users")))
     ;; (funcall ok ".")
     (error
      "Couldn't find a usable temp directory -- set `py-temp-directory'"))
    (when erg (setq py-temp-directory erg)))
  "*Directory used for temporary files created by a *Python* process.
By default, guesses the first directory from this list that exists and that you
can write into: the value (if any) of the environment variable TMPDIR,
/usr/tmp, /tmp, /var/tmp, or the current directory.

`py-custom-temp-directory' will take precedence when setq ")

(defcustom py-beep-if-tab-change t
  "*Ring the bell if `tab-width' is changed.
If a comment of the form

  \t# vi:set tabsize=<number>:

is found before the first code line when the file is entered, and the
current value of (the general Emacs variable) `tab-width' does not
equal <number>, `tab-width' is set to <number>, a message saying so is
displayed in the echo area, and if `py-beep-if-tab-change' is non-nil
the Emacs bell is also rung as a warning."
  :type 'boolean
  :group 'python-mode)

(defcustom py-jump-on-exception t
  "*Jump to innermost exception frame in *Python Output* buffer.
When this variable is non-nil and an exception occurs when running
Python code synchronously in a subprocess, jump immediately to the
source code of the innermost traceback frame."
  :type 'boolean
  :group 'python-mode)

(defcustom py-ask-about-save t
  "If not nil, ask about which buffers to save before executing some code.
Otherwise, all modified buffers are saved without asking."
  :type 'boolean
  :group 'python-mode)

(defcustom py-backspace-function 'backward-delete-char-untabify
  "*Function called by `py-electric-backspace' when deleting backwards."
  :type 'function
  :group 'python-mode)

(defcustom py-delete-function 'delete-char
  "*Function called by `py-electric-delete' when deleting forwards."
  :type 'function
  :group 'python-mode)

(defcustom py-pdbtrack-do-tracking-p t
  "*Controls whether the pdbtrack feature is enabled or not.
When non-nil, pdbtrack is enabled in all comint-based buffers,
e.g. shell buffers and the *Python* buffer.  When using pdb to debug a
Python program, pdbtrack notices the pdb prompt and displays the
source file and line that the program is stopped at, much the same way
as gud-mode does for debugging C programs with gdb."
  :type 'boolean
  :group 'python-mode)
(make-variable-buffer-local 'py-pdbtrack-do-tracking-p)

(defcustom py-pdbtrack-filename-mapping nil
  "Supports mapping file paths when opening file buffers in pdbtrack.
When non-nil this is an alist mapping paths in the Python interpreter
to paths in Emacs."
  :type 'alist
  :group 'python-mode)

(defcustom py-pdbtrack-minor-mode-string " PDB"
  "*String to use in the minor mode list when pdbtrack is enabled."
  :type 'string
  :group 'python-mode)

(defcustom py-import-check-point-max
  20000
  "Maximum number of characters to search for a Java-ish import statement.
When `python-mode' tries to calculate the shell to use (either a
CPython or a Jython shell), it looks at the so-called `shebang' line
-- i.e. #! line.  If that's not available, it looks at some of the
file heading imports to see if they look Java-like."
  :type 'integer
  :group 'python-mode)

(defcustom py-jython-packages
  '("java" "javax")
  "Imported packages that imply `jython-mode'."
  :type '(repeat string)
  :group 'python-mode)
(make-obsolete-variable 'py-jpython-packages 'py-jython-packages nil)

(defcustom py-current-defun-show  t
  "If `py-current-defun' should jump to the definition, highlight it while waiting PY-WHICH-FUNC-DELAY seconds, before returning to previous position.

Default is `t'."

  :type 'boolean
  :group 'python-mode)

(defcustom py-current-defun-delay  2
  "When called interactively, `py-current-defun' should wait PY-WHICH-FUNC-DELAY seconds at the definition name found, before returning to previous position. "

  :type 'number
  :group 'python-mode)

(defcustom py-send-receive-delay  5
  "Seconds to wait for output, used by `python-send-receive'. "

  :type 'number
  :group 'python-mode)

(defvar py-exec-command nil
  "Mode commands will set this. ")
(make-variable-buffer-local 'py-exec-command)

(defvar py-exec-string-command nil
  "Mode commands will set this. ")
(make-variable-buffer-local 'py-exec-string-command)

(defvar py-which-bufname "Python")
(make-variable-buffer-local 'py-which-bufname)

(defcustom py-master-file nil
  "If non-nil, \\[py-execute-buffer] executes the named
master file instead of the buffer's file.  If the file name has a
relative path, the value of variable `default-directory' for the
buffer is prepended to come up with a file name.

Beside you may set this variable in the file's local
variable section, e.g.:

    # Local Variables:
    # py-master-file: \"master.py\"
    # End:

"
  :type 'string
  :group 'python-mode)
(make-variable-buffer-local 'py-master-file)

(defvar py-pychecker-history nil)
(defcustom py-pychecker-command "pychecker"
  "*Shell command used to run Pychecker."
  :type 'string
  :group 'python-mode
  :tag "Pychecker Command")

(defcustom py-pychecker-command-args '("--stdlib")
  "*List of string arguments to be passed to pychecker."
  :type '(repeat string)
  :group 'python-mode
  :tag "Pychecker Command Args")

(defvar py-pep8-history nil)
(defcustom py-pep8-command "pep8"
  "*Shell command used to run pep8."
  :type 'string
  :group 'python-mode
  :tag "PEP 8 Command")

(defcustom py-pep8-command-args '("")
  "*List of string arguments to be passed to pep8.

Default is \"\" "
  :type '(repeat string)
  :group 'python-mode
  :tag "PEP 8 Command Args")


(defvar py-pyflakespep8-history nil)
(defcustom py-pyflakespep8-command (concat py-install-directory "pyflakespep8.py")
  "*Shell command used to run `pyflakespep8'."
  :type 'string
  :group 'python-mode
  :tag "Pyflakespep8 Command")

(defcustom py-pyflakespep8-command-args '("")
  "*List of string arguments to be passed to pyflakespep8.

Default is \"\" "
  :type '(repeat string)
  :group 'python-mode
  :tag "Pyflakes-pep8 Command Args")

(defvar py-pyflakes-history nil)
(defcustom py-pyflakes-command "pyflakes"
  "*Shell command used to run Pyflakes."
  :type 'string
  :group 'python-mode
  :tag "Pyflakes Command")

(defcustom py-pyflakes-command-args '("")
  "*List of string arguments to be passed to pyflakes.

Default is \"\" "
  :type '(repeat string)
  :group 'python-mode
  :tag "Pyflakes Command Args")

(defcustom py-pep8-command-args '("")
  "*List of string arguments to be passed to pylint.

Default is \"\" "
  :type '(repeat string)
  :group 'python-mode
  :tag "PEP 8 Command Args")

(defvar py-pylint-history nil)
(defcustom py-pylint-command "pylint"
  "*Shell command used to run Pylint."
  :type 'string
  :group 'python-mode
  :tag "Pylint Command")

(defcustom py-pylint-command-args '("--errors-only")
  "*List of string arguments to be passed to pylint.

Default is \"--errors-only\" "
  :type '(repeat string)
  :group 'python-mode
  :tag "Pylint Command Args")

(defvar py-shell-alist
  '(("jython" . 'jython)
    ("python" . 'cpython))
  "*Alist of interpreters and python shells. Used by `py-choose-shell'
to select the appropriate python interpreter mode for a file.")

(defcustom py-shell-input-prompt-1-regexp "^>>> "
  "*A regular expression to match the input prompt of the shell."
  :type 'string
  :group 'python-mode)

(defcustom py-shell-input-prompt-2-regexp "^[.][.][.] "
  "*A regular expression to match the input prompt of the shell after the
  first line of input."
  :type 'string
  :group 'python-mode)

(defcustom py-shell-switch-buffers-on-execute-p t
  "When non-nil switch to the new Python shell. "

  :type 'boolean
  :group 'python-mode)

(defcustom py-switch-buffers-on-execute-p nil
  "When non-nil switch to the Python output buffer. "

  :type 'boolean
  :group 'python-mode)

(defcustom py-split-windows-on-execute-p t
  "When non-nil split windows. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-split-windows-on-execute-function 'split-window-vertically
  "How window should get splitted to display results of py-execute-... functions. "
  :type '(choice (const :tag "split-window-vertically" split-window-vertically)
		 (const :tag "split-window-horizontally" split-window-horizontally)
                 )
  :group 'python-mode)
(make-variable-buffer-local 'py-split-windows-on-execute-function)

(defcustom py-hide-show-keywords
  '("class"    "def"    "elif"    "else"    "except"
    "for"      "if"     "while"   "finally" "try"
    "with")
  "Keywords composing visible heads.
Also used by (minor-)outline-mode "
  :type '(repeat string)
  :group 'python-mode)

(defcustom py-hide-show-hide-docstrings t
  "*Controls if doc strings can be hidden by hide-show"
  :type 'boolean
  :group 'python-mode)

(defcustom python-mode-hook nil
  "Hook run when entering Python mode."
  :group 'python-mode
  :type 'hook)

(defcustom py-imenu-create-index-p nil
  "Non-nil means Python mode creates and displays an index menu of functions and global variables. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-shell-name "python"
  "A PATH/TO/EXECUTABLE or default value `py-shell' may look for, if no shell is specified by command. "
  :type 'string
  :group 'python-mode)
(make-variable-buffer-local 'py-shell-name)

(defcustom py-shell-toggle-1 py-shell-name
  "A PATH/TO/EXECUTABLE or default value used by `py-toggle-shell'. "
  :type 'string
  :group 'python-mode)
(make-variable-buffer-local 'py-shell-toggle-1)

(defcustom py-shell-toggle-2 "python3"
  "A PATH/TO/EXECUTABLE or default value used by `py-toggle-shell'. "
  :type 'string
  :group 'python-mode)
(make-variable-buffer-local 'py-shell-toggle-2)

(defcustom py-source-modes '(python-mode jython-mode)
  "Used to determine if a buffer contains Python source code.

If a file is loaded into a buffer that is in one of these major modes, it is considered Python source by `py-load-file', which uses the
value to determine defaults."
  :type '(repeat function)
  :group 'python-mode)

(defcustom py-shell-prompt-alist
  '(("ipython" . "^In \\[[0-9]+\\]: *")
    (t . "^>>> "))
  "Alist of Python input prompts.
Each element has the form (PROGRAM . REGEXP), where PROGRAM is
the value of `py-shell-name' for the python process and
REGEXP is a regular expression matching the Python prompt.
PROGRAM can also be t, which specifies the default when no other
element matches `py-shell-name'."
  :type 'string
  :group 'python-mode)

(defcustom py-shell-continuation-prompt-alist
  '(("ipython" . "^   [.][.][.]+: *")
    (t . "^[.][.][.] "))
  "Alist of Python continued-line prompts.
Each element has the form (PROGRAM . REGEXP), where PROGRAM is
the value of `py-shell-name' for the python process and
REGEXP is a regular expression matching the Python prompt for
continued lines.
PROGRAM can also be t, which specifies the default when no other
element matches `py-shell-name'."
  :type 'string
  :group 'python-mode)

;; ipython.el
(defvar ipython-de-input-prompt-regexp "\\(?:
In \\[[0-9]+\\]: *.*
----+> \\(.*
\\)[\n]?\\)\\|\\(?:
In \\[[0-9]+\\]: *\\(.*
\\)\\)\\|^[ ]\\{3\\}[.]\\{3,\\}: *\\(.*
\\)"
  "A regular expression to match the IPython input prompt and the python
command after it. The first match group is for a command that is rewritten,
the second for a 'normal' command, and the third for a multiline command.")

(defvar ipython-de-output-prompt-regexp "^Out\\[[0-9]+\\]: "
  "A regular expression to match the output prompt of IPython.")

(defcustom py-match-paren-mode nil
  "*Non-nil means, cursor will jump to beginning or end of a block.
This vice versa, to beginning first.
Sets `py-match-paren-key' in python-mode-map.
Customize `py-match-paren-key' which key to use. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-match-paren-key "%"
  "*String used by \\[comment-region] to comment out a block of code.
This should follow the convention for non-indenting comment lines so
that the indentation commands won't get confused (i.e., the string
should be of the form `#x...' where `x' is not a blank or a tab, and
`...' is arbitrary).  However, this string should not end in whitespace."
  :type 'string
  :group 'python-mode)

(defcustom py-kill-empty-line t
  "*If t, py-indent-forward-line kills empty lines. "
  :type 'boolean
  :group 'python-mode)

(defcustom py-remove-cwd-from-path t
  "Whether to allow loading of Python modules from the current directory.
If this is non-nil, Emacs removes '' from sys.path when starting
an inferior Python process.  This is the default, for security
reasons, as it is easy for the Python process to be started
without the user's realization (e.g. to perform completion)."
  :type 'boolean
  :group 'python-mode)

(defcustom py-imenu-show-method-args-p nil
  "*Controls echoing of arguments of functions & methods in the Imenu buffer.
When non-nil, arguments are printed."
  :type 'boolean
  :group 'python-mode)

(defcustom python-default-interpreter 'cpython
  "*Which Python interpreter is used by default.
The value for this variable can be either `cpython' or `jpython'.

When the value is `cpython', the variables `python-python-command' and
`python-python-command-args' are consulted to determine the interpreter
and arguments to use.

When the value is `jpython', the variables `python-jpython-command' and
`python-jpython-command-args' are consulted to determine the interpreter
and arguments to use.

Note that this variable is consulted only the first time that a Python
mode buffer is visited during an Emacs session.  After that, use
\\[py-toggle-shell] to change the interpreter shell."
  :type '(choice (const :tag "Python (a.k.a. CPython)" cpython)
		 (const :tag "JPython" jpython))
  :group 'python-mode)

(defcustom python-python-command-args '("-i")
  "*List of string arguments to be used when starting a Python shell."
  :type '(repeat string)
  :group 'python-mode)

(defcustom python-jython-command-args '("-i")
  "*List of string arguments to be used when starting a Jython shell."
  :type '(repeat string)
  :group 'python-mode
  :tag "JPython Command Args")

(defcustom python-pdbtrack-do-tracking-p t
  "*Controls whether the pdbtrack feature is enabled or not.

When non-nil, pdbtrack is enabled in all comint-based buffers,
e.g. shell interaction buffers and the *Python* buffer.

When using pdb to debug a Python program, pdbtrack notices the
pdb prompt and presents the line in the source file where the
program is stopped in a pop-up buffer.  It's similar to what
gud-mode does for debugging C programs with gdb, but without
having to restart the program."
  :type 'boolean
  :group 'python-mode)
(make-variable-buffer-local 'python-pdbtrack-do-tracking-p)

(defcustom python-pdbtrack-minor-mode-string " PDB"
  "*Minor-mode sign to be displayed when pdbtrack is active."
  :type 'string
  :group 'python-mode)

(defcustom python-shell-prompt-alist
  '(("ipython" . "^In \\[[0-9]+\\]: *")
    (t . "^>>> "))
  "Alist of Python input prompts.
Each element has the form (PROGRAM . REGEXP), where PROGRAM is
the value of `python-python-command' for the python process and
REGEXP is a regular expression matching the Python prompt.
PROGRAM can also be t, which specifies the default when no other
element matches `python-python-command'."
  :type 'string
  :group 'python-mode)

(defcustom python-shell-continuation-prompt-alist
  '(("ipython" . "^   [.][.][.]+: *")
    (t . "^[.][.][.] "))
  "Alist of Python continued-line prompts.
Each element has the form (PROGRAM . REGEXP), where PROGRAM is
the value of `python-python-command' for the python process and
REGEXP is a regular expression matching the Python prompt for
continued lines.
PROGRAM can also be t, which specifies the default when no other
element matches `python-python-command'."
  :type 'string
  :group 'python-mode)

(defcustom python-python-command "python"
  "Shell command to run Python interpreter.
Any arguments can't contain whitespace."
  :group 'python-mode
  :type 'string)

(defcustom python-jython-command "jython"
  "Shell command to run Jython interpreter.
Any arguments can't contain whitespace."
  :group 'python-mode
  :type 'string)

(defcustom py-history-filter-regexp "\\`\\s-*\\S-?\\S-?\\s-*\\'"
  "Input matching this regexp is not saved on the history list.
Default ignores all inputs of 0, 1, or 2 non-blank characters."
  :type 'regexp
  :group 'python-mode)

(defcustom python-remove-cwd-from-path t
  "Whether to allow loading of Python modules from the current directory.
If this is non-nil, Emacs removes '' from sys.path when starting
an inferior Python process.  This is the default, for security
reasons, as it is easy for the Python process to be started
without the user's realization (e.g. to perform completion)."
  :type 'boolean
  :group 'python-mode
  :version "23.3")

(defcustom python-source-modes '(python-mode jython-mode)
  "Used to determine if a buffer contains Python source code.

If a file is loaded into a buffer that is in one of these major modes, it is considered Python source by `py-load-file', which uses the
value to determine defaults."
  :type '(repeat function)
  :group 'python-mode)

(defcustom python-jython-packages '("java" "javax" "org" "com")
  "Packages implying `jython-mode'.
If these are imported near the beginning of the buffer, `python-mode'
actually punts to `jython-mode'."
  :type '(repeat string)
  :group 'python-mode)

(defface py-number-face
  '((t (:inherit default)))
  ;; '((t (:inherit 'font-lock-variable-name-face)))
  "Highlight numbers. "
  :group 'python-mode)
(defvar py-number-face 'py-number-face)

(defface py-XXX-tag-face
  '((t (:inherit font-lock-string-face)))
  "XXX\\|TODO\\|FIXME "
  :group 'python-mode)
(defvar py-XXX-tag-face 'py-XXX-tag-face)

;; ;; Face for None, True, False, self, and Ellipsis
(defface py-pseudo-keyword-face
  '((t (:inherit font-lock-keyword-face)))
  "Face for pseudo keywords in Python mode, like self, True, False, Ellipsis."
  :group 'python-mode)
(defvar py-pseudo-keyword-face 'py-pseudo-keyword-face)

(defface py-variable-name-face
  '((t (:inherit default)))
  ;; '((t (:inherit 'font-lock-variable-name-face)))
  "Face method decorators."
  :group 'python-mode)
(defvar py-variable-name-face 'py-variable-name-face)

;; PEP 318 decorators
(defface py-decorators-face
  '((t (:inherit font-lock-keyword-face)))
  "Face method decorators."
  :group 'python-mode)
(defvar py-decorators-face 'py-decorators-face)

;; Face for builtins
(defface py-builtins-face
  '((t (:inherit font-lock-builtin-face)))
  "Face for builtins like TypeError, object, open, and exec."
  :group 'python-mode)
(defvar py-builtins-face 'py-builtins-face)

(defface py-class-name-face
  '((t (:inherit font-lock-type-face)))
  "Face for classes."
  :group 'python-mode)
(defvar py-class-name-face 'py-class-name-face)

;; XXX, TODO, and FIXME comments and such
(defface py-exception-name-face
  '((t (:inherit font-lock-builtin-face)))
  "."
  :group 'python-mode)
(defvar py-exception-name-face 'py-exception-name-face)

(defcustom py-use-local-default nil
  "If `t', py-shell will use `py-shell-local-path' instead
  of default Python.

Making switch between several virtualenv's easier,
 `python-mode' should deliver an installer, so named-shells pointing to virtualenv's will be available. "
  :type 'boolean
  :group 'python-mode)

;; (defcustom python-load-extended-executes-p  t
;;   "If commands from `python-extended-executes.el' should be loaded.
;;
;; Default is `t'.
;; Provides commands executing buffers code at different conditions, thus avoids customization of `py-shell-name', `py-switch-buffers-on-execute-p'. "
;;
;;   :type 'boolean
;;   :group 'python-mode)

(defcustom py-shell-local-path ""
  "If `py-use-local-default' is non-nil, `py-shell' will use EXECUTABLE indicated here incl. path. "

  :type 'string
  :group 'python-mode)

;;; highlight-indentation.el --- Function for highlighting indentation
;; Original Author: Anton Johansson <anton.johansson@gmail.com> - http://antonj.se
;; Created: Dec 15 23:42:04 2010
;; URL: https://github.com/antonj/Highlight-Indentation-for-Emacs

(defcustom highlight-indentation  nil
  "If level of indentation should be displayed at start.
Toggle buffer local status via `M-x highlight-indentation' during session. "

  :type 'boolean
  :group 'python-mode)
(make-variable-buffer-local 'highlight-indentation)

(defvar highlight-indent-active nil)
(make-variable-buffer-local 'highlight-indent-active)

(defface highlight-indent-face
  '((((class color) (background dark))
     (:background "grey33"))
    (((class color) (background light))
     (:background "grey")))
  "Basic face for highlighting indentation guides.")

(defvar highlight-indent-offset 4)
(setq-default highlight-indent-offset 4)

(defvar ruby-indent-level nil)
(defvar nxml-child-indent nil)

(defun highlight-indentation-on ()
  "Make sure `highlight-indentation' is on. "
  (interactive)
  (set (make-local-variable 'highlight-indent-active) nil)
  (highlight-indentation)
  (when (called-interactively-p 'any)
    (message "highlight-indentation ON")))

(defun highlight-indentation-off ()
  "Make sure `highlight-indentation' is off. "
  (interactive)
  (set (make-local-variable 'highlight-indent-active) t)
  (highlight-indentation)
  (when (called-interactively-p 'any)
    (message "highlight-indentation OFF")))

(defun highlight-indentation (&optional indent-width)
  "Toggle highlight indentation.
Optional argument INDENT-WIDTH specifies which indentation
level (spaces only) should be highlighted, if omitted
indent-width will be guessed from current major-mode"
  (interactive "P")
  (let ((re (format "\\( \\) \\{%s\\}" (- highlight-indent-offset 1))))
    (if (not highlight-indent-active)
        (progn ;; Toggle on
          (set (make-local-variable 'highlight-indent-offset)
               (if indent-width
                   indent-width
                 ;; Set indentation offset according to major mode
                 (cond ((eq major-mode 'python-mode)
                        (if (boundp 'python-indent)
                            python-indent
                          py-indent-offset))
                       ((eq major-mode 'ruby-mode)
                        ruby-indent-level)
                       ((eq major-mode 'nxml-mode)
                        nxml-child-indent)
                       ((local-variable-p 'c-basic-offset)
                        c-basic-offset)
                       (t
                        (default-value 'highlight-indent-offset)))))
          (set (make-local-variable 'highlight-indent-active) t)
          (if (featurep 'xemacs)
              (font-lock-add-keywords nil `((,re (1 'paren-face-match))))
            (font-lock-add-keywords nil `((,re (1 'highlight-indent-face)))))
          (message (format "highlight-indentation with indent-width %s"
                           highlight-indent-offset)))
      ;; Toggle off
      (set (make-local-variable 'highlight-indent-active) nil)
      (if (featurep 'xemacs)
          (font-lock-remove-keywords nil `((,re (1 'paren-face-match))))
        (font-lock-remove-keywords nil `((,re (1 'highlight-indent-face)))))
      (message "highlight-indentation OFF"))
    (font-lock-fontify-buffer)))

(defcustom py-underscore-word-syntax-p t
  "If underscore chars should be of syntax-class `word', not of `symbol'.

Underscores in word-class makes `forward-word' etc. travel the indentifiers. Default is `t'.

See bug report at launchpad, lp:940812 "
  :type 'boolean
  :group 'python-mode)

(defcustom py-edit-only-p nil
  "When `t' `python-mode' will not take resort nor check for installed Python executables. Default is nil.

See bug report at launchpad, lp:944093. "
  :type 'boolean
  :group 'python-mode)

(defvar py-force-local-shell-p nil
  "Used internally, see `toggle-force-local-shell'. ")

(defcustom py-force-py-shell-name-p nil
  "When `t', execution with kind of Python specified in `py-shell-name' is enforced, possibly shebang doesn't take precedence. "

  :type 'boolean
  :group 'python-mode)

(defvar python-mode-v5-behavior nil)
(defcustom python-mode-v5-behavior-p nil
  "Execute region through `shell-command-on-region' as
v5 did it - lp:990079. This might fail with certain chars - see UnicodeEncodeError lp:550661"

  :type 'boolean
  :group 'python-mode)

(defcustom py-ipython-execute-delay 0.3
  "Delay needed by execute functions when no IPython shell is running. "
  :type 'float
  :group 'python-mode)

;;; Derived Python's flying circus support for Emacs
;;  Employed for completion in Python3 shells
;; Copyright (C) 2010, 2011 Free Software Foundation, Inc.

;; Original author: Fabián E. Gallina <fabian@anue.biz>
;; URL: https://github.com/fgallina/python.el

(defcustom python-shell-buffer-name "Python"
  "Default buffer name for Python interpreter."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-shell-interpreter "python"
  "Default Python interpreter for shell."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-shell-internal-buffer-name "Python Internal"
  "Default buffer name for the Internal Python interpreter."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-shell-interpreter-args "-i"
  "Default arguments for the Python interpreter."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-shell-prompt-regexp ">>> "
  "Regular Expression matching top\-level input prompt of python shell.
It should not contain a caret (^) at the beginning."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-shell-prompt-block-regexp "[.][.][.] "
  "Regular Expression matching block input prompt of python shell.
It should not contain a caret (^) at the beginning."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-shell-prompt-output-regexp ""
  "Regular Expression matching output prompt of python shell.
It should not contain a caret (^) at the beginning."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-shell-prompt-pdb-regexp "[(<]*[Ii]?[Pp]db[>)]+ "
  "Regular Expression matching pdb input prompt of python shell.
It should not contain a caret (^) at the beginning."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-shell-send-setup-max-wait 5
  "Seconds to wait for process output before code setup.
If output is received before the especified time then control is
returned in that moment and not after waiting."
  :type 'integer
  :group 'python
  :safe 'integerp)

(defcustom python-shell-process-environment nil
  "List of environment variables for Python shell.
This variable follows the same rules as `process-environment'
since it merges with it before the process creation routines are
called.  When this variable is nil, the Python shell is run with
the default `process-environment'."
  :type '(repeat string)
  :group 'python
  :safe 'listp)

(defcustom python-shell-extra-pythonpaths nil
  "List of extra pythonpaths for Python shell.
The values of this variable are added to the existing value of
PYTHONPATH in the `process-environment' variable."
  :type '(repeat string)
  :group 'python
  :safe 'listp)

(defcustom python-shell-exec-path nil
  "List of path to search for binaries.
This variable follows the same rules as `exec-path' since it
merges with it before the process creation routines are called.
When this variable is nil, the Python shell is run with the
default `exec-path'."
  :type '(repeat string)
  :group 'python
  :safe 'listp)

(defcustom python-shell-virtualenv-path nil
  "Path to virtualenv root.
This variable, when set to a string, makes the values stored in
`python-shell-process-environment' and `python-shell-exec-path'
to be modified properly so shells are started with the specified
virtualenv."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-ffap-setup-code
  "def __FFAP_get_module_path(module):
    try:
        import os
        path = __import__(module).__file__
        if path[-4:] == '.pyc' and os.path.exists(path[0:-1]):
            path = path[:-1]
        return path
    except:
        return ''"
  "Python code to get a module path."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-ffap-string-code
  "__FFAP_get_module_path('''%s''')\n"
  "Python code used to get a string with the path of a module."
  :type 'string
  :group 'python
  :safe 'stringp)

(defvar python--prompt-regexp nil)

(defvar python-command python-python-command
  "Actual command used to run Python.
May be `python-python-command' or `python-jython-command', possibly
modified by the user.  Additional arguments are added when the command
is used by `run-python' et al.")

(defvar python-buffer nil
  "*The current Python process buffer.

Commands that send text from source buffers to Python processes have
to choose a process to send to.  This is determined by buffer-local
value of `python-buffer'.  If its value in the current buffer,
i.e. both any local value and the default one, is nil, `run-python'
and commands that send to the Python process will start a new process.

Whenever \\[run-python] starts a new process, it resets the default
value of `python-buffer' to be the new process's buffer and sets the
buffer-local value similarly if the current buffer is in Python mode
or Inferior Python mode, so that source buffer stays associated with a
specific sub-process.

Use \\[py-set-proc] to set the default value from a buffer with a
local value.")
(make-variable-buffer-local 'python-buffer)

(defun python-ffap-module-path (module)
  "Function for `ffap-alist' to return path for MODULE."
  (let ((process (or
                  (and (eq major-mode 'inferior-python-mode)
                       (get-buffer-process (current-buffer)))
                  (python-shell-get-process))))
    (if (not process)
        nil
      (let ((module-file
             (python-shell-send-string-no-output
              (format python-ffap-string-code module) process)))
        (when module-file
          (substring-no-properties module-file 1 -1))))))

(eval-after-load "ffap"
  '(progn
     (push '(python-mode . python-ffap-module-path) ffap-alist)
     (push '(inferior-python-mode . python-ffap-module-path) ffap-alist)))

(defcustom python-shell-setup-codes '(python-shell-completion-setup-code
                                      python-ffap-setup-code
                                      python-eldoc-setup-code)
  "List of code run by `python-shell-send-setup-codes'."
  :type '(repeat symbol)
  :group 'python
  :safe 'listp)

(defcustom python-shell-compilation-regexp-alist
  `((,(rx line-start (1+ (any " \t")) "File \""
	  (group (1+ (not (any "\"<")))) ; avoid `<stdin>' &c
	  "\", line " (group (1+ digit)))
     1 2)
    (,(rx " in file " (group (1+ not-newline)) " on line "
	  (group (1+ digit)))
     1 2)
    (,(rx line-start "> " (group (1+ (not (any "(\"<"))))
	  "(" (group (1+ digit)) ")" (1+ (not (any "("))) "()")
     1 2))
  "`compilation-error-regexp-alist' for inferior Python."
  :type '(alist string)
  :group 'python)

(defvar python-mode-syntax-table nil
  "Syntax table for Python files.")

(setq python-mode-syntax-table
      (let ((table (make-syntax-table)))
        ;; Give punctuation syntax to ASCII that normally has symbol
        ;; syntax or has word syntax and isn't a letter.
        (let ((symbol (string-to-syntax "_"))
              (sst (standard-syntax-table)))
          (dotimes (i 128)
            (unless (= i ?_)
              (if (equal symbol (aref sst i))
                  (modify-syntax-entry i "." table)))))
        (modify-syntax-entry ?$ "." table)
        (modify-syntax-entry ?% "." table)
        ;; exceptions
        (modify-syntax-entry ?# "<" table)
        (modify-syntax-entry ?\n ">" table)
        (modify-syntax-entry ?' "\"" table)
        (modify-syntax-entry ?` "$" table)
        (when py-underscore-word-syntax-p
          (modify-syntax-entry ?_ "w" table))
        table))

(defconst python-dotty-syntax-table
  (let ((table (make-syntax-table)))
    (set-char-table-parent table python-mode-syntax-table)
    (modify-syntax-entry ?. "_" table)
    table)
  "Syntax table giving `.' symbol syntax.
Otherwise inherits from `python-mode-syntax-table'.")
(defvar outline-heading-end-regexp)
(defvar eldoc-documentation-function)

;; Stolen from org-mode
(defun python-util-clone-local-variables (from-buffer &optional regexp)
  "Clone local variables from FROM-BUFFER.
Optional argument REGEXP selects variables to clone and defaults
to \"^python-\"."
  (mapc
   (lambda (pair)
     (and (symbolp (car pair))
          (string-match (or regexp "^python-")
                        (symbol-name (car pair)))
	  (set (make-local-variable (car pair))
	       (cdr pair))))
   (buffer-local-variables from-buffer)))

(defun python-shell-send-setup-code ()
  "Send all setup code for shell.
This function takes the list of setup code to send from the
`python-shell-setup-codes' list."
  (let (
        ;; (msg "Sent %s")
        (process (get-buffer-process (current-buffer))))
    (accept-process-output process python-shell-send-setup-max-wait)
    (dolist (code python-shell-setup-codes)
      (when code
        ;; (when py-verbose-p (message (format msg code)))
        (python-shell-send-string-no-output
         (symbol-value code) process)))))

(add-hook 'inferior-python-mode-hook
          #'python-shell-send-setup-code)

(defun python-shell-get-process-name (dedicated)
  "Calculate the appropiate process name for inferior Python process.
If DEDICATED is t and the variable `buffer-file-name' is non-nil
returns a string with the form
`python-shell-buffer-name'[variable `buffer-file-name'] else
returns the value of `python-shell-buffer-name'.  After
calculating the process name adds the buffer name for the process
in the `same-window-buffer-names' list."
  (let ((process-name
         (if (and dedicated
                  buffer-file-name)
             (format "%s[%s]" python-shell-buffer-name buffer-file-name)
           (format "%s" python-shell-buffer-name))))
    (add-to-list 'same-window-buffer-names (purecopy
                                            (format "*%s*" process-name)))
    process-name))

(defun python-shell-internal-get-process-name ()
  "Calculate the appropiate process name for Internal Python process.
The name is calculated from `python-shell-global-buffer-name' and
a hash of all relevant global shell settings in order to ensure
uniqueness for different types of configurations."
  (format "%s [%s]"
          python-shell-internal-buffer-name
          (md5
           (concat
            (python-shell-parse-command)
            python-shell-prompt-regexp
            python-shell-prompt-block-regexp
            python-shell-prompt-output-regexp
            (mapconcat #'symbol-value python-shell-setup-codes "")
            (mapconcat #'identity python-shell-process-environment "")
            (mapconcat #'identity python-shell-extra-pythonpaths "")
            (mapconcat #'identity python-shell-exec-path "")
            (or python-shell-virtualenv-path "")
            (mapconcat #'identity python-shell-exec-path "")))))

(defun python-shell-parse-command ()
  "Calculate the string used to execute the inferior Python process."
  (format "%s %s" python-shell-interpreter python-shell-interpreter-args))

(defun python-shell-calculate-process-environment ()
  "Calculate process environment given `python-shell-virtualenv-path'."
  (let ((process-environment (append
                              python-shell-process-environment
                              process-environment nil))
        (virtualenv (if python-shell-virtualenv-path
                        (directory-file-name python-shell-virtualenv-path)
                      nil)))
    (when python-shell-extra-pythonpaths
      (setenv "PYTHONPATH"
              (format "%s%s%s"
                      (mapconcat 'identity
                                 python-shell-extra-pythonpaths
                                 path-separator)
                      path-separator
                      (or (getenv "PYTHONPATH") ""))))
    (if (not virtualenv)
        process-environment
      (setenv "PYTHONHOME" nil)
      (setenv "PATH" (format "%s/bin%s%s"
                             virtualenv path-separator
                             (or (getenv "PATH") "")))
      (setenv "VIRTUAL_ENV" virtualenv))
    process-environment))

(defun python-shell-calculate-exec-path ()
  "Calculate exec path given `python-shell-virtualenv-path'."
  (let ((path (append python-shell-exec-path
                      exec-path nil)))
    (if (not python-shell-virtualenv-path)
        path
      (cons (format "%s/bin"
                    (directory-file-name python-shell-virtualenv-path))
            path))))

(defcustom python-shell-send-setup-max-wait 5
  "Seconds to wait for process output before code setup.
If output is received before the especified time then control is
returned in that moment and not after waiting."
  :type 'integer
  :group 'python
  :safe 'integerp)

(defun python-shell-make-comint (cmd proc-name &optional pop)
  "Create a python shell comint buffer.
CMD is the python command to be executed and PROC-NAME is the
process name the comint buffer will get.  After the comint buffer
is created the `inferior-python-mode' is activated.  If POP is
non-nil the buffer is shown."
  (save-excursion
    (let* ((proc-buffer-name (format "*%s*" proc-name))
           (process-environment (python-shell-calculate-process-environment))
           (exec-path (python-shell-calculate-exec-path)))
      (when (not (comint-check-proc proc-buffer-name))
        (let* ((cmdlist (split-string-and-unquote cmd))
               (buffer (apply 'make-comint proc-name (car cmdlist) nil
                              (cdr cmdlist)))
               (current-buffer (current-buffer)))
          (with-current-buffer buffer
            (inferior-python-mode)
            (python-util-clone-local-variables current-buffer))))
      (when pop
        (pop-to-buffer proc-buffer-name))
      proc-buffer-name)))

(defcustom python-shell-completion-setup-code
  "try:
    import readline
except ImportError:
    def __COMPLETER_all_completions(text): []
else:
    import rlcompleter
    readline.set_completer(rlcompleter.Completer().complete)
    def __COMPLETER_all_completions(text):
        import sys
        completions = []
        try:
            i = 0
            while True:
                res = readline.get_completer()(text, i)
                if not res: break
                i += 1
                completions.append(res)
        except NameError:
            pass
        return completions"
  "Code used to setup completion in inferior Python processes."
  :type 'string
  :group 'python-mode
  :safe 'stringp)

(defcustom python-shell-completion-string-code
  "';'.join(__COMPLETER_all_completions('''%s'''))\n"
  "Python code used to get a string of completions separated by semicolons."
  :type 'string
  :group 'python-mode
  :safe 'stringp)

(defcustom python-shell-module-completion-string-code ""
  "Python code used to get completions separated by semicolons for imports.

For IPython v0.11, add the following line to
`python-shell-completion-setup-code':

from IPython.core.completerlib import module_completion

and use the following as the value of this variable:

';'.join(module_completion('''%s'''))\n"
  :type 'string
  :group 'python-mode
  :safe 'stringp)

(defvar python-completion-original-window-configuration nil)

(defun run-python-internal ()
  "Run an inferior Internal Python process.
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
run).  \(Type \\[describe-mode] in the process buffer for a list
of commands.)"
  (interactive)
  (set-process-query-on-exit-flag
   (get-buffer-process
    (python-shell-make-comint
     (python-shell-parse-command)
     (python-shell-internal-get-process-name))) nil))

(defun python-shell-get-process ()
  "Get inferior Python process for current buffer and return it."
  (let* ((dedicated-proc-name (python-shell-get-process-name t))
         (dedicated-proc-buffer-name (format "*%s*" dedicated-proc-name))
         (global-proc-name  (python-shell-get-process-name nil))
         (global-proc-buffer-name (format "*%s*" global-proc-name))
         (dedicated-running (comint-check-proc dedicated-proc-buffer-name))
         (global-running (comint-check-proc global-proc-buffer-name)))
    ;; Always prefer dedicated
    (get-buffer-process (or (and dedicated-running dedicated-proc-buffer-name)
                            (and global-running global-proc-buffer-name)))))

(defun python-shell-get-or-create-process ()
  "Get or create an inferior Python process for current buffer and return it."
  (let* ((old-buffer (current-buffer))
         (dedicated-proc-name (python-shell-get-process-name t))
         (dedicated-proc-buffer-name (format "*%s*" dedicated-proc-name))
         (global-proc-name  (python-shell-get-process-name nil))
         (global-proc-buffer-name (format "*%s*" global-proc-name))
         (dedicated-running (comint-check-proc dedicated-proc-buffer-name))
         (global-running (comint-check-proc global-proc-buffer-name))
         (current-prefix-arg 4))
    (when (and (not dedicated-running) (not global-running))
      (if (call-interactively 'run-python)
          (setq dedicated-running t)
        (setq global-running t)))
    ;; Always prefer dedicated
    (switch-to-buffer old-buffer)
    (get-buffer-process (if dedicated-running
                            dedicated-proc-buffer-name
                          global-proc-buffer-name))))

(defun python-shell-internal-get-or-create-process ()
  "Get or create an inferior Internal Python process."
  (let* ((proc-name (python-shell-internal-get-process-name))
         (proc-buffer-name (format "*%s*" proc-name)))
    (run-python-internal)
    (get-buffer-process proc-buffer-name)))

(defun python-shell-send-string (string &optional process msg)
  "Send STRING to inferior Python PROCESS.
When `py-verbose-p' and MSG is non-nil messages the first line of STRING."
  (interactive "sPython command: ")
  (let ((process (or process (python-shell-get-or-create-process)))
        (lines (split-string string "\n" t)))
    ;; (when (and py-verbose-p msg)
    ;; (message (format "Sent: %s..." (nth 0 lines)))
    ;; )
    (if (> (length lines) 1)
        (let* ((temp-file-name (make-temp-file "py"))
               (file-name (or (buffer-file-name) temp-file-name)))
          (with-temp-file temp-file-name
            (insert string)
            (delete-trailing-whitespace))
          (python-shell-send-file file-name process temp-file-name))
      (comint-send-string process string)
      (when (or (not (string-match "\n$" string))
                (string-match "\n[ \t].*\n?$" string))
        (comint-send-string process "\n")))))

(defun python-shell-send-string-no-output (string &optional process msg)
  "Send STRING to PROCESS and inhibit output.
When MSG is non-nil messages the first line of STRING.  Return
the output."
  (let* ((output-buffer)
         (process (or process (python-shell-get-or-create-process)))
         (comint-preoutput-filter-functions
          (append comint-preoutput-filter-functions
                  '(ansi-color-filter-apply
                    (lambda (string)
                      (setq output-buffer (concat output-buffer string))
                      "")))))
    (python-shell-send-string string process msg)
    (accept-process-output process)
    (replace-regexp-in-string
     (if (> (length python-shell-prompt-output-regexp) 0)
         (format "\n*%s$\\|^%s\\|\n$"
                 python-shell-prompt-regexp
                 (or python-shell-prompt-output-regexp ""))
       (format "\n*$\\|^%s\\|\n$"
               python-shell-prompt-regexp))
     "" output-buffer)))

(defun python-shell-internal-send-string (string)
  "Send STRING to the Internal Python interpreter.
Returns the output.  See `python-shell-send-string-no-output'."
  (python-shell-send-string-no-output
   ;; Makes this function compatible with the old
   ;; python-send-receive. (At least for CEDET).
   (replace-regexp-in-string "_emacs_out +" "" string)
   (python-shell-internal-get-or-create-process) nil))

(defun python-shell-send-region (start end)
  "Send the region delimited by START and END to inferior Python process."
  (interactive "r")
  (let ((deactivate-mark nil))
    (python-shell-send-string (buffer-substring start end) nil t)))

(defun python-shell-send-buffer ()
  "Send the entire buffer to inferior Python process."
  (interactive)
  (save-restriction
    (widen)
    (python-shell-send-region (point-min) (point-max))))

(defun python-shell-send-defun (arg)
  "Send the current defun to inferior Python process.
When argument ARG is non-nil sends the innermost defun."
  (interactive "P")
  (save-excursion
    (python-shell-send-region
     (progn
       (or (python-beginning-of-defun-function)
           (progn (beginning-of-line) (point-marker))))
     (progn
       (or (python-end-of-defun-function)
           (progn (end-of-line) (point-marker)))))))

(defun python-shell-send-file (file-name &optional process temp-file-name)
  "Send FILE-NAME to inferior Python PROCESS.
If TEMP-FILE-NAME is passed then that file is used for processing
instead, while internally the shell will continue to use
FILE-NAME."
  (interactive "fFile to send: ")
  (let* ((process (or process (python-shell-get-or-create-process)))
         (temp-file-name (when temp-file-name
                           (expand-file-name temp-file-name)))
         (file-name (or (expand-file-name file-name) temp-file-name)))
    (when (not file-name)
      (error "If FILE-NAME is nil then TEMP-FILE-NAME must be non-nil"))
    (python-shell-send-string
     (format
      (concat "__pyfile = open('''%s''');"
              "exec(compile(__pyfile.read(), '''%s''', 'exec'));"
              "__pyfile.close()")
      (or temp-file-name file-name) file-name)
     process)))

(defun python-shell-switch-to-shell ()
  "Switch to inferior Python process buffer."
  (interactive)
  (pop-to-buffer (process-buffer (python-shell-get-or-create-process)) t))

(defcustom python-pdbtrack-stacktrace-info-regexp
  "^> \\([^\"(<]+\\)(\\([0-9]+\\))\\([?a-zA-Z0-9_<>]+\\)()"
  "Regular Expression matching stacktrace information.
Used to extract the current line and module being inspected."
  :type 'string
  :group 'python
  :safe 'stringp)

;;; Eldoc

(defcustom python-eldoc-setup-code
  "def __PYDOC_get_help(obj):
    try:
        import inspect
        if hasattr(obj, 'startswith'):
            obj = eval(obj, globals())
        doc = inspect.getdoc(obj)
        if not doc and callable(obj):
            target = None
            if inspect.isclass(obj) and hasattr(obj, '__init__'):
                target = obj.__init__
                objtype = 'class'
            else:
                target = obj
                objtype = 'def'
            if target:
                args = inspect.formatargspec(
                    *inspect.getargspec(target)
                )
                name = obj.__name__
                doc = '{objtype} {name}{args}'.format(
                    objtype=objtype, name=name, args=args
                )
        else:
            doc = doc.splitlines()[0]
    except:
        doc = ''
    try:
        exec('print doc')
    except SyntaxError:
        print(doc)"
  "Python code to setup documentation retrieval."
  :type 'string
  :group 'python
  :safe 'stringp)

(defcustom python-eldoc-string-code
  "__PYDOC_get_help('''%s''')\n"
  "Python code used to get a string with the documentation of an object."
  :type 'string
  :group 'python
  :safe 'stringp)

;;; Pdb
(defvar python-pdbtrack-tracked-buffer nil
  "Variable containing the value of the current tracked buffer.
Never set this variable directly, use
`python-pdbtrack-set-tracked-buffer' instead.")
(make-variable-buffer-local 'python-pdbtrack-tracked-buffer)

(defvar python-pdbtrack-buffers-to-kill nil
  "List of buffers to be deleted after tracking finishes.")
(make-variable-buffer-local 'python-pdbtrack-buffers-to-kill)

(defun python-pdbtrack-set-tracked-buffer (file-name)
  "Set the buffer for FILE-NAME as the tracked buffer.
Internally it uses the `python-pdbtrack-tracked-buffer' variable.
Returns the tracked buffer."
  (let ((file-buffer (get-file-buffer file-name)))
    (if file-buffer
        (setq python-pdbtrack-tracked-buffer file-buffer)
      (setq file-buffer (find-file-noselect file-name))
      (when (not (member file-buffer python-pdbtrack-buffers-to-kill))
        (add-to-list 'python-pdbtrack-buffers-to-kill file-buffer)))
    file-buffer))

(defun python-pdbtrack-comint-output-filter-function (output)
  "Move overlay arrow to current pdb line in tracked buffer.
Argument OUTPUT is a string with the output from the comint process."
  (when (not (string= output ""))
    (let* ((full-output (ansi-color-filter-apply
                         (buffer-substring comint-last-input-end (point-max))))
           (line-number)
           (file-name
            (with-temp-buffer
              (insert full-output)
              (goto-char (point-min))
              ;; OK, this sucked but now it became a cool hack. The
              ;; stacktrace information normally is on the first line
              ;; but in some cases (like when doing a step-in) it is
              ;; on the second.
              (when (or (looking-at python-pdbtrack-stacktrace-info-regexp)
                        (and (forward-line)
                             (looking-at python-pdbtrack-stacktrace-info-regexp)))
                (setq line-number (string-to-number
                                   (match-string-no-properties 2)))
                (match-string-no-properties 1)))))
      (if (and file-name line-number)
          (let* ((tracked-buffer (python-pdbtrack-set-tracked-buffer file-name))
                 (shell-buffer (current-buffer))
                 (tracked-buffer-window (get-buffer-window tracked-buffer))
                 (tracked-buffer-line-pos))
            (with-current-buffer tracked-buffer
              (set (make-local-variable 'overlay-arrow-string) "=>")
              (set (make-local-variable 'overlay-arrow-position) (make-marker))
              (setq tracked-buffer-line-pos (progn
                                              (goto-char (point-min))
                                              (forward-line (1- line-number))
                                              (point-marker)))
              (when tracked-buffer-window
                (set-window-point
                 tracked-buffer-window tracked-buffer-line-pos))
              (set-marker overlay-arrow-position tracked-buffer-line-pos))
            (pop-to-buffer tracked-buffer)
            (switch-to-buffer-other-window shell-buffer))
        (when python-pdbtrack-tracked-buffer
          (with-current-buffer python-pdbtrack-tracked-buffer
            (set-marker overlay-arrow-position nil))
          (mapc #'(lambda (buffer)
                    (ignore-errors (kill-buffer buffer)))
                python-pdbtrack-buffers-to-kill)
          (setq python-pdbtrack-tracked-buffer nil
                python-pdbtrack-buffers-to-kill nil)))))
  output)

;;;

(defun python-shell-completion--get-completions (input process completion-code)
  "Retrieve available completions for INPUT using PROCESS.
Argument COMPLETION-CODE is the python code used to get
completions on the current context."
  (with-current-buffer (process-buffer process)
    (let ((completions
           (python-shell-send-string-no-output
            (format completion-code input) process)))
      (when (> (length completions) 2)
        (split-string completions "^'\\|^\"\\|;\\|'$\\|\"$" t)))))

(defun python-shell-completion--do-completion-at-point (process line input)
  "Do completion at point for PROCESS."
  (with-syntax-table python-dotty-syntax-table
    (let* ((code
	    (if line
                (concat line  python-shell-module-completion-string-code)
              python-shell-module-completion-string-code))
	   (completions
            (python-shell-completion--get-completions
             input process code))
	   (completion (when completions
			 (try-completion input completions))))
      (cond ((eq completion t)
	     (if (eq this-command last-command)
		 (when python-completion-original-window-configuration
		   (set-window-configuration
		    python-completion-original-window-configuration)))
	     (setq python-completion-original-window-configuration nil)
	     nil)
	    ((null completion)
	     (message "Can't find completion for \"%s\"" input)
	     (ding)
             nil)
            ((not (string= input completion))
             (progn (delete-char (- (length input)))
                    (insert completion)
                    ;; minibuffer.el expects a list, a bug IMO
                    t))
            (t
             (unless python-completion-original-window-configuration
               (setq python-completion-original-window-configuration
                     (current-window-configuration)))
             (with-output-to-temp-buffer "*Python Completions*"
               (display-completion-list
                (all-completions input completions)))
             nil)))))

(defun python-shell-completion-complete-at-point ()
  "Perform completion at point in inferior Python process."
  (interactive)
  (and comint-last-prompt-overlay
       (> (point-marker) (overlay-end comint-last-prompt-overlay))
       (python-shell-completion--do-completion-at-point
	(get-buffer-process (current-buffer))(buffer-substring-no-properties beg end) word)))

(defun python-shell-completion-complete-or-indent ()
  "Complete or indent depending on the context.
If content before pointer is all whitespace indent.  If not try
to complete."
  (interactive)
  (if (string-match "^[[:space:]]*$"
                    (buffer-substring (comint-line-beginning-position)
                                      (point-marker)))
      (indent-for-tab-command)
    (comint-dynamic-complete)))

;;; NO USER DEFINABLE VARIABLES BEYOND THIS POINT
(defvar ipython-version nil)

(defvar python-command "python"
  "Used by `py-completion-at-point', derived from python.el" )

(defvaralias 'python-python-command-args 'py-python-command-args)
(defvaralias 'py-python-command 'py-shell-name)
(defvaralias 'py-jpython-command 'py-shell-name)
(defvaralias 'py-jython-command 'py-shell-name)
(defvaralias 'py-default-interpreter 'py-shell-name)
;; (defvaralias 'python-command 'py-shell-name)

(defvar py-shell-template "
\(defun NAME (&optional argprompt)
  \"Start an DOCNAME interpreter in another window.

With optional \\\\[universal-argument] user is prompted
for options to pass to the DOCNAME interpreter. \"
  (interactive \"P\")
  (let\* ((py-shell-name \"FULLNAME\"))
    (py-set-shell-completion-environment)
    (py-shell argprompt)
    (when (interactive-p) (switch-to-buffer (current-buffer))
          (goto-char (point-max)))))
")

(setq py-shell-template "
\(defun NAME (&optional argprompt)
  \"Start an DOCNAME interpreter in another window.

With optional \\\\[universal-argument] user is prompted
for options to pass to the DOCNAME interpreter. \"
  (interactive \"P\")
  (let\* ((py-shell-name \"FULLNAME\"))
    (py-set-shell-completion-environment)
    (py-shell argprompt)
    (when (interactive-p) (switch-to-buffer (current-buffer))
          (goto-char (point-max)))))
")

(defvar view-return-to-alist)
(defvar python-imports)			; forward declaration

(defvar py-execute-directory nil
  "Stores the file's directory-name py-execute-... functions act upon. ")

(defvar py-prev-dir/file nil
  "Caches (directory . file) pair used in the last `py-load-file' command.
Used for determining the default in the next one.")

(defvar py-exception-buffer nil)

(defvar py-output-buffer "*Python Output*")
(make-variable-buffer-local 'py-output-buffer)

(defvar py-execute-keep-temporary-file-p nil
  "For tests only. Excute functions delete temporary files default. ")

(defvar py-expression-skip-regexp "^ =:#\t\r\n\f"
  "py-expression assumes chars indicated possible composing a py-expression, skip it. ")
;; (setq py-expression-skip-regexp "^ =:#\t\r\n\f")

(defvar py-expression-looking-regexp "[^ =:#\t\r\n\f)]"
  "py-expression assumes chars indicated possible composing a py-expression, when looking-at or -back. ")
;; (setq py-expression-looking-regexp "[^ =:#\t\r\n\f)]")

(defvar py-not-expression-regexp "[ .=:#\t\r\n\f)]"
  "py-expression assumes chars indicated probably will not compose a py-expression. ")
;; (setq py-not-expression-regexp "[ .=:#\t\r\n\f)]")

(defvar py-partial-expression-skip-regexp "^ .()[]{}=:#\t\r\n\f"
  "py-partial-expression assumes chars indicated possible composing a py-partial-expression, skip it. ")
;; (setq py-partial-expression-skip-regexp "^ .(){}=:#\t\r\n\f")

(defvar py-partial-expression-forward-regexp "^ .)}=:#\t\r\n\f"
  "py-partial-expression assumes chars indicated possible composing a py-partial-expression, skip it. ")

(defvar py-partial-expression-backward-regexp "^ .({=:#\t\r\n\f"
  "py-partial-expression assumes chars indicated possible composing a py-partial-expression, skip it. ")

(defvar py-not-partial-expression-skip-regexp " \\.=:#\t\r\n\f"
  "py-partial-expression assumes chars indicated may not compose a py-partial-expression, skip it. ")

(defvar py-partial-expression-looking-regexp "[^ .=:#\t\r\n\f]"
  "py-partial-expression assumes chars indicated possible composing a py-partial-expression, when looking-at or -back. ")
;; (setq py-partial-expression-looking-regexp "[^ .=:#\t\r\n\f)]")

(defvar py-not-partial-expression-regexp "[ .=:#\t\r\n\f)]"
  "py-partial-expression assumes chars indicated probably will not compose a py-partial-expression. ")
;; (setq py-not-partial-expression-regexp "[ .=:#\t\r\n\f)]")

(defvar py-line-number-offset 0
  "When an exception occurs as a result of py-execute-region, a
subsequent py-up-exception needs the line number where the region
started, in order to jump to the correct file line.  This variable is
set in py-execute-region and used in py-jump-to-exception.")

(defvar match-paren-no-use-syntax-pps nil)

(defsubst py-keep-region-active ()
  "Keep the region active in XEmacs."
  ;; Ignore byte-compiler warnings you might see.  Also note that
  ;; FSF's Emacs does it differently; its policy doesn't require us
  ;; to take explicit action.
  (and (boundp 'zmacs-region-stays)
       (setq zmacs-region-stays t)))

;; Constants
(defconst py-blank-or-comment-re "[ \t]*\\($\\|#\\)"
  "Regular expression matching a blank or comment line.")

(defconst py-block-closing-keywords-re
  "[ \t]*\\<\\(return\\|raise\\|break\\|continue\\|pass\\)\\_>[ \n\t]"
  "Matches the beginning of a class, method or compound statement. ")

(defconst py-finally-re
  "[ \t]*\\_<finally\\_>[: \n\t]"
  "Regular expression matching keyword which closes a try-block. ")

(defconst py-except-re
  "[ \t]*\\_<except\\_>[: \n\t]"
  "Regular expression matching keyword which composes a try-block. ")

(defconst py-else-re
  "[ \t]*\\_<else\\_>[: \n\t]"
  "Regular expression matching keyword which closes a for- if- or try-block. ")

(defconst py-return-re
  ".*:?[ \t]*\\_<\\(return\\)\\_>[ \n\t]"
  "Regular expression matching keyword which typically closes a function. ")

(defconst py-no-outdent-re "\\(try:\\|except\\(\\s +.*\\)?:\\|while\\s +.*:\\|for\\s +.*:\\|if\\s +.*:\\|elif\\s +.*:\\)\\([ 	]*\\_<\\(return\\|raise\\|break\\|continue\\|pass\\)\\_>[ 	\n]\\)")

;; (defconst py-no-outdent-re
;;   (concat
;;    "\\("
;;    (mapconcat 'identity
;;               (list "try:"
;;                     "except\\(\\s +.*\\)?:"
;;                     "while\\s +.*:"
;;                     "for\\s +.*:"
;;                     "if\\s +.*:"
;;                     "elif\\s +.*:"
;;                     (concat py-block-closing-keywords-re "[ \t\n]"))
;;               "\\|")
;;    "\\)")
;;   "Regular expression matching lines not to dedent after.")

(defvar py-traceback-line-re
  "^IPython\\|^In \\[[0-9]+\\]: *\\|^>>>\\|^[^ \t>]+>[^0-9]+\\([0-9]+\\)\\|^[ \t]+File \"\\([^\"]+\\)\", line \\([0-9]+\\)"
  "Regular expression that describes tracebacks.
Inludes Python shell-prompt in order to stop further searches. ")

(defconst py-assignment-re "\\<\\w+\\>[ \t]*\\(=\\|+=\\|*=\\|%=\\|&=\\|^=\\|<<=\\|-=\\|/=\\|**=\\||=\\|>>=\\|//=\\)"
  "If looking at the beginning of an assignment. ")

(defconst py-block-re "[ \t]*\\_<\\(class\\|def\\|for\\|if\\|try\\|while\\|with\\)\\_>[: \n\t]"
  "Matches the beginning of a compound statement. ")

(defconst py-minor-block-re "[ \t]*\\_<\\(for\\|if\\|try\\)\\_>[: \n\t]"
  "Matches the beginning of an `for', `if' or `try' block. ")

(defconst py-try-block-re "[ \t]*\\_<try\\_>[: \n\t]"
  "Matches the beginning of an `if' or `try' block. ")

(defconst py-class-re "[ \t]*\\_<\\(class\\)\\_>[ \n\t]"
  "Matches the beginning of a class definition. ")

(defconst py-def-or-class-re "[ \t]*\\_<\\(def\\|class\\)\\_>[ \n\t]"
  "Matches the beginning of a class- or functions definition. ")

(defconst py-def-re "[ \t]*\\_<\\(def\\)\\_>[ \n\t]"
  "Matches the beginning of a functions definition. ")

(defconst py-block-or-clause-re "[ \t]*\\_<\\(if\\|else\\|elif\\|while\\|for\\|def\\|class\\|try\\|except\\|finally\\|with\\)\\_>[: \n\t]"
  "Matches the beginning of a compound statement or it's clause. ")

(defconst py-clause-re "[ \t]*\\_<\\(else\\|elif\\|except\\|finally\\)\\_>[: \n\t]"
  "Matches the beginning of a compound statement's clause. ")

(defconst py-elif-re "[ \t]*\\_<\\elif\\_>[: \n\t]"
  "Matches the beginning of a compound if-statement's clause exclusively. ")

(defconst py-try-clause-re "[ \t]*\\_<\\(except\\|else\\|finally\\)\\_>[: \n\t]"
  "Matches the beginning of a compound try-statement's clause. ")

(defconst py-if-re "[ \t]*\\_<if\\_>[ \n\t]"
  "Matches the beginning of a compound statement saying `if'. ")

(defconst py-try-re "[ \t]*\\_<try\\_>[: \n\t]"
  "Matches the beginning of a compound statement saying `try'. " )

;;; Macro definitions
(defmacro py-in-string-or-comment-p ()
  "Returns beginning position if inside a string or comment, nil otherwise. "
  `(or (nth 8 (syntax-ppss))
       (when (or (looking-at "\"")(looking-at "[ \t]*#[ \t]*"))
         (match-beginning 0))))

(defmacro empty-line-p ()
  "Returns t if cursor is at an line with nothing but whitespace-characters, nil otherwise."
  (interactive "p")
  `(save-excursion
     (progn
       (beginning-of-line)
       (looking-at "\\s-*$"))))

(defmacro py-escaped ()
  "Return t if char is preceded by an odd number of backslashes. "
  `(save-excursion
     (< 0 (% (abs (skip-chars-backward "\\\\")) 2))))

(defmacro py-preceding-line-backslashed-p ()
  "Return t if preceding line is a backslashed continuation line. "
  `(save-excursion
     (beginning-of-line)
     (skip-chars-backward " \t\r\n\f")
     (and (eq (char-before (point)) ?\\ )
          (py-escaped))))

(defmacro py-current-line-backslashed-p ()
  "Return t if current line is a backslashed continuation line. "
  `(save-excursion
     (end-of-line)
     (skip-chars-backward " \t\r\n\f")
     (and (eq (char-before (point)) ?\\ )
          (py-escaped))))

(defmacro py-continuation-line-p ()
  "Return t iff current line is a continuation line."
  `(save-excursion
     (beginning-of-line)
     (or (py-preceding-line-backslashed-p)
         (< 0 (nth 0 (syntax-ppss))))))

(defun py-count-lines (&optional start end)
  "Count lines in accessible part until current line.

See http://debbugs.gnu.org/cgi/bugreport.cgi?bug=7115"
  (interactive)
  (save-excursion
    (let ((count 0)
          (orig (point)))
      (goto-char (point-min))
      (while (and (< (point) orig)(not (eobp)) (skip-chars-forward "^\n" orig))
        (setq count (1+ count))
        (unless (or (not (< (point) orig)) (eobp)) (forward-char 1)
                (setq count (+ count (abs (skip-chars-forward "\n" orig))))))
      (when (bolp) (setq count (1+ count)))
      (when (interactive-p) (message "%s" count))
      count)))

(defmacro python-rx (&rest regexps)
  "Python mode specialized rx macro which supports common python named REGEXPS."
  (let ((rx-constituents (append python-rx-constituents rx-constituents)))
    (cond ((null regexps)
           (error "No regexp"))
          ((cdr regexps)
           (rx-to-string `(and ,@regexps) t))
          (t
           (rx-to-string (car regexps) t)))))

;;;
;; GNU's syntax-ppss-context
(unless (functionp 'syntax-ppss-context)
  (defsubst syntax-ppss-context (ppss)
    (cond
     ((nth 3 ppss) 'string)
     ((nth 4 ppss) 'comment)
     (t nil))))

;; Skip's XE workaround
(unless (fboundp 'string-to-syntax)
  (defun string-to-syntax (s)
    (cond
     ((equal s "|") '(15))
     ((equal s "_") '(3))
     (t (error "Unhandled string: %s" s)))))

;;; GNU python.el stuff

(defun py-history-input-filter (str)
  "`comint-input-filter' function for inferior Python.
Don't save anything for STR matching `py-history-filter-regexp'."
  (not (string-match py-history-filter-regexp str)))

;; Fixme: Loses with quoted whitespace.
(defun python-args-to-list (string)
  (let ((where (string-match "[ \t]" string)))
    (cond ((null where) (list string))
          ((not (= where 0))
           (cons (substring string 0 where)
                 (python-args-to-list (substring string (+ 1 where)))))
          (t (let ((pos (string-match "[^ \t]" string)))
               (if pos (python-args-to-list (substring string pos))))))))

(defvar python-preoutput-result nil
  "Data from last `_emacs_out' line seen by the preoutput filter.")

(defvar python-preoutput-continuation nil
  "If non-nil, funcall this when `python-preoutput-filter' sees `_emacs_ok'.")

(defvar python-preoutput-leftover nil)
(defvar python-preoutput-skip-next-prompt nil)

;; Using this stops us getting lines in the buffer like
;; >>> ... ... >>>
;; Also look for (and delete) an `_emacs_ok' string and call
;; `python-preoutput-continuation' if we get it.
(defun python-preoutput-filter (s)
  "`comint-preoutput-filter-functions' function: ignore prompts not at bol."
  (when python-preoutput-leftover
    (setq s (concat python-preoutput-leftover s))
    (setq python-preoutput-leftover nil))
  (let ((start 0)
        (res ""))
    ;; First process whole lines.
    (while (string-match "\n" s start)
      (let ((line (substring s start (setq start (match-end 0)))))
        ;; Skip prompt if needed.
        (when (and python-preoutput-skip-next-prompt
                   (string-match comint-prompt-regexp line))
          (setq python-preoutput-skip-next-prompt nil)
          (setq line (substring line (match-end 0))))
        ;; Recognize special _emacs_out lines.
        (if (and (string-match "\\`_emacs_out \\(.*\\)\n\\'" line)
                 (local-variable-p 'python-preoutput-result))
            (progn
              (setq python-preoutput-result (match-string 1 line))
              (set (make-local-variable 'python-preoutput-skip-next-prompt) t))
          (setq res (concat res line)))))
    ;; Then process the remaining partial line.
    (unless (zerop start) (setq s (substring s start)))
    (cond ((and (string-match comint-prompt-regexp s)
                ;; Drop this prompt if it follows an _emacs_out...
                (or python-preoutput-skip-next-prompt
                    ;; ... or if it's not gonna be inserted at BOL.
                    ;; Maybe we could be more selective here.
                    (if (zerop (length res))
                        (not (bolp))
                      (string-match ".\\'" res))))
           ;; The need for this seems to be system-dependent:
           ;; What is this all about, exactly?  --Stef
           ;; (if (and (eq ?. (aref s 0)))
           ;;     (accept-process-output (get-buffer-process (current-buffer)) 1))
           (setq python-preoutput-skip-next-prompt nil)
           res)
          ((let ((end (min (length "_emacs_out ") (length s))))
             (eq t (compare-strings s nil end "_emacs_out " nil end)))
           ;; The leftover string is a prefix of _emacs_out so we don't know
           ;; yet whether it's an _emacs_out or something else: wait until we
           ;; get more output so we can resolve this ambiguity.
           (set (make-local-variable 'python-preoutput-leftover) s)
           res)
          (t (concat res s)))))

(defvar python-version-checked nil)
(defun python-check-version (cmd)
  "Check that CMD runs a suitable version of Python."
  ;; Fixme:  Check on Jython.
  (unless (or python-version-checked
              (equal 0 (string-match (regexp-quote python-python-command)
                                     cmd)))
    (unless (shell-command-to-string cmd)
      (error "Can't run Python command `%s'" cmd))
    (let* ((res (shell-command-to-string
                 (concat cmd
                         " -c \"from sys import version_info;\
print version_info >= (2, 2) and version_info < (3, 0)\""))))
      (unless (string-match "True" res)
        (error "Only Python versions >= 2.2 and < 3.0 are supported")))
    (setq python-version-checked t)))

(defun run-python (&optional cmd noshow new)
  "Run an inferior Python process, input and output via buffer *Python*.

CMD is the Python command to run.  NOSHOW non-nil means don't
show the buffer automatically.

Interactively, a prefix arg means to prompt for the initial
Python command line (default is `python-command').

A new process is started if one isn't running attached to
`python-buffer', or if called from Lisp with non-nil arg NEW.
Otherwise, if a process is already running in `python-buffer',
switch to that buffer.

This command runs the hook `inferior-python-mode-hook' after
running `comint-mode-hook'.  Type \\[describe-mode] in the
process buffer for a list of commands.

By default, Emacs inhibits the loading of Python modules from the
current working directory, for security reasons.  To disable this
behavior, change `python-remove-cwd-from-path' to nil."
  (interactive (if current-prefix-arg
                   (list (read-string "Run Python: " python-command) nil t)
                 (list python-command)))
  (require 'ansi-color) ; for ipython
  (unless cmd (setq cmd python-command))
  (setq python-command cmd)
  ;; Fixme: Consider making `python-buffer' buffer-local as a buffer
  ;; (not a name) in Python buffers from which `run-python' &c is
  ;; invoked.  Would support multiple processes better.
  (when (or new (not (comint-check-proc python-buffer)))
    (with-current-buffer
        (let* ((cmdlist
                (append (python-args-to-list cmd) '("-i")
                        (if python-remove-cwd-from-path
                            '("-c" "import sys; sys.path.remove('')"))))
               (path (getenv "PYTHONPATH"))
               (process-environment	; to import emacs.py
                (cons (concat "PYTHONPATH="
                              (if path (concat path path-separator))
                              data-directory)
                      process-environment))
               ;; If we use a pipe, unicode characters are not printed
               ;; correctly (Bug#5794) and IPython does not work at
               ;; all (Bug#5390).
               ;; (process-connection-type t))
               )
          (apply 'make-comint-in-buffer "Python"
                 (generate-new-buffer "*Python*")
                 (car cmdlist) nil (cdr cmdlist)))
      (setq-default python-buffer (current-buffer))
      (setq python-buffer (current-buffer))
      (accept-process-output (get-buffer-process python-buffer) 5)
      (inferior-python-mode)
      ;; Load function definitions we need.
      ;; Before the preoutput function was used, this was done via -c in
      ;; cmdlist, but that loses the banner and doesn't run the startup
      ;; file.  The code might be inline here, but there's enough that it
      ;; seems worth putting in a separate file, and it's probably cleaner
      ;; to put it in a module.
      ;; Ensure we're at a prompt before doing anything else.
      (py-send-string "import emacs")
      ;; The following line was meant to ensure that we're at a prompt
      ;; before doing anything else.  However, this can cause Emacs to
      ;; hang waiting for a response, if that Python function fails
      ;; (i.e. raises an exception).
      ;; (python-send-receive "print '_emacs_out ()'")
      ))
  (if (derived-mode-p 'python-mode)
      (setq python-buffer (default-value 'python-buffer))) ; buffer-local
  ;; Without this, help output goes into the inferior python buffer if
  ;; the process isn't already running.
  (sit-for 1 t)        ;Should we use accept-process-output instead?  --Stef
  (unless noshow (pop-to-buffer python-buffer t)))

(defun python-send-command (command)
  "Like `python-send-string' but resets `compilation-shell-minor-mode'."
  (when (python-check-comint-prompt)
    (with-current-buffer (process-buffer (py-proc))
      (goto-char (point-max))
      (compilation-forget-errors)
      (py-send-string command)
      (setq compilation-last-buffer (current-buffer)))))

(defun python-send-region (start end)
  "Send the region to the inferior Python process."
  ;; The region is evaluated from a temporary file.  This avoids
  ;; problems with blank lines, which have different semantics
  ;; interactively and in files.  It also saves the inferior process
  ;; buffer filling up with interpreter prompts.  We need a Python
  ;; function to remove the temporary file when it has been evaluated
  ;; (though we could probably do it in Lisp with a Comint output
  ;; filter).  This function also catches exceptions and truncates
  ;; tracebacks not to mention the frame of the function itself.
  ;;
  ;; The `compilation-shell-minor-mode' parsing takes care of relating
  ;; the reference to the temporary file to the source.
  ;;
  ;; Fixme: Write a `coding' header to the temp file if the region is
  ;; non-ASCII.
  (interactive "r")
  (let* ((f (make-temp-file "py"))
         (command
          ;; IPython puts the FakeModule module into __main__ so
          ;; emacs.eexecfile becomes useless.
          (if (or (string-match "[iI][pP]ython[^[:alpha:]]*$" (py-choose-shell))
                  (string-match "[pP]ython3[[:alnum:]:]*$" (py-choose-shell)))
              (format "execfile %S" f)
            (format "emacs.eexecfile(%S)" f)))
         (orig-start (copy-marker start)))
    (when (save-excursion
            (goto-char start)
            (/= 0 (current-indentation))) ; need dummy block
      (save-excursion
        (goto-char orig-start)
        ;; Wrong if we had indented code at buffer start.
        (set-marker orig-start (line-beginning-position 0)))
      (write-region "if True:\n" nil f nil 'nomsg))
    (write-region start end f t 'nomsg)
    (python-send-command command)
    (with-current-buffer (process-buffer (py-proc))
      ;; Tell compile.el to redirect error locations in file `f' to
      ;; positions past marker `orig-start'.  It has to be done *after*
      ;; `python-send-command''s call to `compilation-forget-errors'.
      (compilation-fake-loc orig-start f))))

(defun python-send-string (string)
  "Evaluate STRING in inferior Python process."
  (interactive "sPython command: ")
  (comint-send-string (py-proc) string)
  (unless (string-match "\n\\'" string)
    ;; Make sure the text is properly LF-terminated.
    (comint-send-string (py-proc) "\n"))
  (when (string-match "\n[ \t].*\n?\\'" string)
    ;; If the string contains a final indented line, add a second newline so
    ;; as to make sure we terminate the multiline instruction.
    (comint-send-string (py-proc) "\n")))

(defun python-send-buffer ()
  "Send the current buffer to the inferior Python process."
  (interactive)
  (python-send-region (point-min) (point-max)))

;; Fixme: Try to define the function or class within the relevant
;; module, not just at top level.
(defun python-send-defun ()
  "Send the current defun (class or method) to the inferior Python process."
  (interactive)
  (save-excursion (python-send-region (progn (beginning-of-defun) (point))
                                      (progn (end-of-defun) (point)))))

(defun python-switch-to-python (eob-p)
  "Switch to the Python process buffer, maybe starting new process.
With prefix arg, position cursor at end of buffer."
  (interactive "P")
  (pop-to-buffer (process-buffer (py-proc)) t) ;Runs python if needed.
  (when eob-p
    (push-mark)
    (goto-char (point-max))))

(defun python-send-region-and-go (start end)
  "Send the region to the inferior Python process.
Then switch to the process buffer."
  (interactive "r")
  (python-send-region start end)
  (python-switch-to-python t))

(defvar python-prev-dir/file nil
  "Caches (directory . file) pair used in the last `python-load-file' command.
Used for determining the default in the next one.")

(defun python-load-file (file-name)
  "Load a Python file FILE-NAME into the inferior Python process.
If the file has extension `.py' import or reload it as a module.
Treating it as a module keeps the global namespace clean, provides
function location information for debugging, and supports users of
module-qualified names."
  (interactive (comint-get-source "Load Python file: " python-prev-dir/file
                                  python-source-modes
                                  t))	; because execfile needs exact name
  (comint-check-source file-name)     ; Check to see if buffer needs saving.
  (setq python-prev-dir/file (cons (file-name-directory file-name)
                                   (file-name-nondirectory file-name)))
  (with-current-buffer (process-buffer (py-proc)) ;Runs python if needed.
    ;; Fixme: I'm not convinced by this logic from python-mode.el.
    (python-send-command
     (if (string-match "\\.py\\'" file-name)
         (let ((module (file-name-sans-extension
                        (file-name-nondirectory file-name))))
           (format "emacs.eimport(%S,%S)"
                   module (file-name-directory file-name)))
       (format "execfile(%S)" file-name)))
    (message "%s loaded" file-name)))

(defun py-proc ()
  "Return the current Python process.

See variable `python-buffer'.  Starts a new process if necessary."
  ;; Fixme: Maybe should look for another active process if there
  ;; isn't one for `python-buffer'.
  (unless (comint-check-proc python-buffer)
    (run-python nil t))
  (get-buffer-process (if (derived-mode-p 'inferior-python-mode)
                          (current-buffer)
                        python-buffer)))

(defun python-set-proc ()
  "Set the default value of `python-buffer' to correspond to this buffer.
If the current buffer has a local value of `python-buffer', set the
default (global) value to that.  The associated Python process is
the one that gets input from \\[python-send-region] et al when used
in a buffer that doesn't have a local value of `python-buffer'."
  (interactive)
  (if (local-variable-p 'python-buffer)
      (setq-default python-buffer python-buffer)
    (error "No local value of `python-buffer'")))

;; Fixme: Should this actually be used instead of info-look, i.e. be
;; bound to C-h S?  [Probably not, since info-look may work in cases
;; where this doesn't.]
;; (defun python-describe-symbol (symbol)
;;   "Get help on SYMBOL using `help'.
;; Interactively, prompt for symbol.
;;
;; Symbol may be anything recognized by the interpreter's `help'
;; command -- e.g. `CALLS' -- not just variables in scope in the
;; interpreter.  This only works for Python version 2.2 or newer
;; since earlier interpreters don't support `help'.
;;
;; In some cases where this doesn't find documentation, \\[info-lookup-symbol]
;; will."
;;   ;; Note that we do this in the inferior process, not a separate one, to
;;   ;; ensure the environment is appropriate.
;;   (interactive
;;    (let ((symbol (with-syntax-table python-dotty-syntax-table
;; 		   (current-word)))
;; 	 (enable-recursive-minibuffers t))
;;      (list (read-string (if symbol
;; 			    (format "Describe symbol (default %s): " symbol)
;; 			  "Describe symbol: ")
;; 			nil nil symbol))))
;;   (if (equal symbol "") (error "No symbol"))
;;   ;; Ensure we have a suitable help buffer.
;;   ;; Fixme: Maybe process `Related help topics' a la help xrefs and
;;   ;; allow C-c C-f in help buffer.
;;   (let ((temp-buffer-show-hook		; avoid xref stuff
;; 	 (lambda ()
;; 	   (toggle-read-only 1)
;; 	   (setq view-return-to-alist
;; 		 (list (cons (selected-window) help-return-method))))))
;;     (with-output-to-temp-buffer (help-buffer)
;;       (with-current-buffer standard-output
;;  	;; Fixme: Is this actually useful?
;; 	(help-setup-xref (list 'python-describe-symbol symbol)
;; 			 (called-interactively-p 'interactive))
;; 	(set (make-local-variable 'comint-redirect-subvert-readonly) t)
;; 	(help-print-return-message))))
;;   (comint-redirect-send-command-to-process (format "emacs.ehelp(%S, %s)"
;; 						   symbol python-imports)
;;                                            "*Help*" (py-proc) nil nil))

(add-to-list 'debug-ignored-errors "^No symbol")

(defun python-send-receive (string)
  "Send STRING to inferior Python (if any) and return result.
The result is what follows `_emacs_out' in the output.
This is a no-op if `python-check-comint-prompt' returns nil."
  (py-send-string string)
  (let ((proc (py-proc)))
    (with-current-buffer (process-buffer proc)
      (when (python-check-comint-prompt proc)
        (set (make-local-variable 'python-preoutput-result) nil)
        (while (progn
                 (accept-process-output proc 5)
                 (null python-preoutput-result)))
        (prog1 python-preoutput-result
          (kill-local-variable 'python-preoutput-result))))))

(defun python-check-comint-prompt (&optional proc)
  "Return non-nil if and only if there's a normal prompt in the inferior buffer.
If there isn't, it's probably not appropriate to send input to return Eldoc
information etc.  If PROC is non-nil, check the buffer for that process."
  (with-current-buffer (process-buffer (or proc (py-proc)))
    (save-excursion
      (save-match-data
        (re-search-backward (concat python--prompt-regexp " *\\=")
                            nil t)))))

;; Fixme:  Is there anything reasonable we can do with random methods?
;; (Currently only works with functions.)
(defun python-eldoc-function ()
  "`eldoc-documentation-function' for Python.
Only works when point is in a function name, not its arg list, for
instance.  Assumes an inferior Python is running."
  (let ((symbol (with-syntax-table python-dotty-syntax-table
                  (current-word))))
    ;; This is run from timers, so inhibit-quit tends to be set.
    (with-local-quit
      ;; First try the symbol we're on.
      (or (and symbol
               (python-send-receive (format "emacs.eargs(%S, %s)"
                                            symbol python-imports)))
          ;; Try moving to symbol before enclosing parens.
          (let ((s (syntax-ppss)))
            (unless (zerop (car s))
              (when (eq ?\( (char-after (nth 1 s)))
                (save-excursion
                  (goto-char (nth 1 s))
                  (skip-syntax-backward "-")
                  (let ((point (point)))
                    (skip-chars-backward "a-zA-Z._")
                    (if (< (point) point)
                        (python-send-receive
                         (format "emacs.eargs(%S, %s)"
                                 (buffer-substring-no-properties (point) point)
                                 python-imports))))))))))))

;;; Info-look functionality.

(declare-function info-lookup-maybe-add-help "info-look" (&rest arg))

(defun python-after-info-look ()
  "Set up info-look for Python.
Used with `eval-after-load'."
  (let* ((version (let ((s (shell-command-to-string (concat py-shell-name
                                                            " -V"))))
                    (string-match "^Python \\([0-9]+\\.[0-9.]+\\_>\\)" s)
                    (match-string 1 s)))
         ;; Whether info files have a Python version suffix, e.g. in Debian.
         (versioned
          (with-temp-buffer
            (with-no-warnings (Info-mode))
            (condition-case ()
                ;; Don't use `info' because it would pop-up a *info* buffer.
                (with-no-warnings
                  (Info-goto-node (format "(python%s-lib)Miscellaneous Index"
                                          version))
                  t)
              (error nil)))))
    (info-lookup-maybe-add-help
     :mode 'python-mode
     :regexp "[[:alnum:]_]+"
     :doc-spec
     ;; Fixme: Can this reasonably be made specific to indices with
     ;; different rules?  Is the order of indices optimal?
     ;; (Miscellaneous in -ref first prefers lookup of keywords, for
     ;; instance.)
     (if versioned
         ;; The empty prefix just gets us highlighted terms.
         `((,(concat "(python" version "-ref)Miscellaneous Index") nil "")
           (,(concat "(python" version "-ref)Module Index" nil ""))
           (,(concat "(python" version "-ref)Function-Method-Variable Index"
                     nil ""))
           (,(concat "(python" version "-ref)Class-Exception-Object Index"
                     nil ""))
           (,(concat "(python" version "-lib)Module Index" nil ""))
           (,(concat "(python" version "-lib)Class-Exception-Object Index"
                     nil ""))
           (,(concat "(python" version "-lib)Function-Method-Variable Index"
                     nil ""))
           (,(concat "(python" version "-lib)Miscellaneous Index" nil "")))
       '(("(python-ref)Miscellaneous Index" nil "")
         ("(python-ref)Module Index" nil "")
         ("(python-ref)Function-Method-Variable Index" nil "")
         ("(python-ref)Class-Exception-Object Index" nil "")
         ("(python-lib)Module Index" nil "")
         ("(python-lib)Class-Exception-Object Index" nil "")
         ("(python-lib)Function-Method-Variable Index" nil "")
         ("(python-lib)Miscellaneous Index" nil ""))))))
(eval-after-load "info-look" '(python-after-info-look))

;;;; Miscellany.

;; Called from `python-mode', this causes a recursive call of the
;; mode.  See logic there to break out of the recursion.
(defun python-maybe-jython ()
  "Invoke `jython-mode' if the buffer appears to contain Jython code.
The criterion is either a match for `jython-mode' via
`interpreter-mode-alist' or an import of a module from the list
`python-jython-packages'."
  ;; The logic is taken from python-mode.el.
  (save-excursion
    (save-restriction
      (widen)
      (goto-char (point-min))
      (let ((interpreter (if (looking-at auto-mode-interpreter-regexp)
                             (match-string 2))))
        (if (and interpreter (eq 'jython-mode
                                 (cdr (assoc (file-name-nondirectory
                                              interpreter)
                                             interpreter-mode-alist))))
            (jython-mode)
          (if (catch 'done
                (while (re-search-forward
                        (rx bol (or "import" "from") (1+ space)
                            (group (1+ (not (any " \t\n.")))))
                        (+ (point-min) 10000) ; Probably not worth customizing.
                        t)
                  (if (member (match-string 1) python-jython-packages)
                      (throw 'done t))))
              (jython-mode)))))))

(defun python-fill-paragraph (&optional justify)
  "`fill-paragraph-function' handling multi-line strings and possibly comments.
If any of the current line is in or at the end of a multi-line string,
fill the string or the paragraph of it that point is in, preserving
the string's indentation."
  (interactive "P")
  (or (fill-comment-paragraph justify)
      (save-excursion
        (end-of-line)
        (let* ((syntax (syntax-ppss))
               (orig (point))
               start end)
          (cond ((nth 4 syntax)	; comment.   fixme: loses with trailing one
                 (let (fill-paragraph-function)
                   (fill-paragraph justify)))
                ;; The `paragraph-start' and `paragraph-separate'
                ;; variables don't allow us to delimit the last
                ;; paragraph in a multi-line string properly, so narrow
                ;; to the string and then fill around (the end of) the
                ;; current line.
                ((eq t (nth 3 syntax))	; in fenced string
                 (goto-char (nth 8 syntax)) ; string start
                 (setq start (line-beginning-position))
                 (setq end (condition-case () ; for unbalanced quotes
                               (progn (forward-sexp)
                                      (- (point) 3))
                             (error (point-max)))))
                ((re-search-backward "\\s|\\s-*\\=" nil t) ; end of fenced string
                 (forward-char)
                 (setq end (point))
                 (condition-case ()
                     (progn (backward-sexp)
                            (setq start (line-beginning-position)))
                   (error nil))))
          (when end
            (save-restriction
              (narrow-to-region start end)
              (goto-char orig)
              ;; Avoid losing leading and trailing newlines in doc
              ;; strings written like:
              ;;   """
              ;;   ...
              ;;   """
              (let ((paragraph-separate
                     ;; Note that the string could be part of an
                     ;; expression, so it can have preceding and
                     ;; trailing non-whitespace.
                     (concat
                      (rx (or
                           ;; Opening triple quote without following text.
                           (and (* nonl)
                                (group (syntax string-delimiter))
                                (repeat 2 (backref 1))
                                ;; Fixme:  Not sure about including
                                ;; trailing whitespace.
                                (* (any " \t"))
                                eol)
                           ;; Closing trailing quote without preceding text.
                           (and (group (any ?\" ?')) (backref 2)
                                (syntax string-delimiter))))
                      "\\(?:" paragraph-separate "\\)"))
                    fill-paragraph-function)
                (fill-paragraph justify))))))) t)

(defun python-shift-left (start end &optional count)
  "Shift lines in region COUNT (the prefix arg) columns to the left.
COUNT defaults to `py-indent-offset'.  If region isn't active, just shift
current line.  The region shifted includes the lines in which START and
END lie.  It is an error if any lines in the region are indented less than
COUNT columns."
  (interactive
   (if mark-active
       (list (region-beginning) (region-end) current-prefix-arg)
     (list (line-beginning-position) (line-end-position) current-prefix-arg)))
  (if count
      (setq count (prefix-numeric-value count))
    (setq count py-indent-offset))
  (when (> count 0)
    (save-excursion
      (goto-char start)
      (while (< (point) end)
        (if (and (< (current-indentation) count)
                 (not (looking-at "[ \t]*$")))
            (error "Can't shift all lines enough"))
        (forward-line))
      (indent-rigidly start end (- count)))))

(add-to-list 'debug-ignored-errors "^Can't shift all lines enough")

(defun python-shift-right (start end &optional count)
  "Shift lines in region COUNT (the prefix arg) columns to the right.
COUNT defaults to `py-indent-offset'.  If region isn't active, just shift
current line.  The region shifted includes the lines in which START and
END lie."
  (interactive
   (if mark-active
       (list (region-beginning) (region-end) current-prefix-arg)
     (list (line-beginning-position) (line-end-position) current-prefix-arg)))
  (if count
      (setq count (prefix-numeric-value count))
    (setq count py-indent-offset))
  (indent-rigidly start end count))

(defun python-outline-level ()
  "`outline-level' function for Python mode.
The level is the number of `py-indent-offset' steps of indentation
of current line."
  (1+ (/ (current-indentation) py-indent-offset)))

;; Fixme: Consider top-level assignments, imports, &c.
(defun python-current-defun (&optional length-limit)
  "`add-log-current-defun-function' for Python."
  (save-excursion
    ;; Move up the tree of nested `class' and `def' blocks until we
    ;; get to zero indentation, accumulating the defined names.
    (let ((accum)
          (length -1))
      (catch 'done
        (while (or (null length-limit)
                   (null (cdr accum))
                   (< length length-limit))
          (let ((started-from (point)))
            (python-beginning-of-block)
            (end-of-line)
            (beginning-of-defun)
            (when (= (point) started-from)
              (throw 'done nil)))
          (when (looking-at (rx (0+ space) (or "def" "class") (1+ space)
                                (group (1+ (or word (syntax symbol))))))
            (push (match-string 1) accum)
            (setq length (+ length 1 (length (car accum)))))
          (when (= (current-indentation) 0)
            (throw 'done nil))))
      (when accum
	(when (and length-limit (> length length-limit))
	  (setcar accum ".."))
	(mapconcat 'identity accum ".")))))

(defun python-mark-block ()
  "Mark the block around point.
Uses `python-beginning-of-block', `python-end-of-block'."
  (interactive)
  (push-mark)
  (python-beginning-of-block)
  (push-mark (point) nil t)
  (python-end-of-block)
  (exchange-point-and-mark))

;; Fixme:  Provide a find-function-like command to find source of a
;; definition (separate from BicycleRepairMan).  Complicated by
;; finding the right qualified name.

;;;; Completion.

;; http://lists.gnu.org/archive/html/bug-gnu-emacs/2008-01/msg00076.html
(defvar python-imports "None"
  "String of top-level import statements updated by `python-find-imports'.")
(make-variable-buffer-local 'python-imports)

;; Fixme: Should font-lock try to run this when it deals with an import?
;; Maybe not a good idea if it gets run multiple times when the
;; statement is being edited, and is more likely to end up with
;; something syntactically incorrect.
;; However, what we should do is to trundle up the block tree from point
;; to extract imports that appear to be in scope, and add those.
(defun python-find-imports ()
  "Find top-level imports, updating `python-imports'."
  (interactive)
  (save-excursion
    (let (lines)
      (goto-char (point-min))
      (while (re-search-forward "^import\\_>\\|^from\\_>" nil t)
        (unless (syntax-ppss-context (syntax-ppss))
          (let ((start (line-beginning-position)))
            ;; Skip over continued lines.
            (while (and (eq ?\\ (char-before (line-end-position)))
                        (= 0 (forward-line 1)))
              t)
            (push (buffer-substring start (line-beginning-position 2))
                  lines))))
      (setq python-imports
            (if lines
                (apply #'concat
                       ;; This is probably best left out since you're unlikely to need the
                       ;; doc for a function in the buffer and the import will lose if the
                       ;; Python sub-process' working directory isn't the same as the
                       ;; buffer's.
                       ;; 			 (if buffer-file-name
                       ;; 			     (concat
                       ;; 			      "import "
                       ;; 			      (file-name-sans-extension
                       ;; 			       (file-name-nondirectory buffer-file-name))))
                       (nreverse lines))
              "None"))
      (when lines
        (set-text-properties 0 (length python-imports) nil python-imports)
        ;; The output ends up in the wrong place if the string we
        ;; send contains newlines (from the imports).
        (setq python-imports
              (replace-regexp-in-string "\n" "\\n"
                                        (format "%S" python-imports) t t))))))

(defun python-completion-at-point ()
  (let ((end (point))
	(start (save-excursion
		 (and (re-search-backward
		       (rx (or buffer-start (regexp "[^[:alnum:]._]"))
			   (group (1+ (regexp "[[:alnum:]._]"))) point)
		       nil t)
		      (match-beginning 1)))))
    (when start
      (list start end
            (completion-table-dynamic 'python-symbol-completions)))))

;;; FFAP support

(defun python-module-path (module)
  "Function for `ffap-alist' to return path to MODULE."
  (python-send-receive (format "emacs.modpath (%S)" module)))

(eval-after-load "ffap"
  '(push '(python-mode . python-module-path) ffap-alist))

;;;; Find-function support

;; Fixme: key binding?

(defun python-find-function (name)
  "Find source of definition of function NAME.
Interactively, prompt for name."
  (interactive
   (let ((symbol (with-syntax-table python-dotty-syntax-table
		   (current-word)))
	 (enable-recursive-minibuffers t))
     (list (read-string (if symbol
			    (format "Find location of (default %s): " symbol)
			  "Find location of: ")
			nil nil symbol))))
  (unless python-imports
    (error "Not called from buffer visiting Python file"))
  (let* ((loc (python-send-receive (format "emacs.location_of (%S, %s)"
					   name python-imports)))
	 (loc (car (read-from-string loc)))
	 (file (car loc))
	 (line (cdr loc)))
    (unless file (error "Don't know where `%s' is defined" name))
    (pop-to-buffer (find-file-noselect file))
    (when (integerp line)
      (goto-char (point-min))
      (forward-line (1- line)))))

;;;
(defvar py-mode-syntax-table nil)
(setq py-mode-syntax-table
      (let ((table (make-syntax-table))
            (tablelookup (if (featurep 'xemacs)
                             'get-char-table
                           'aref)))
        ;; Give punctuation syntax to ASCII that normally has symbol
        ;; syntax or has word syntax and isn't a letter.
        (if (featurep 'xemacs)
            (setq table (standard-syntax-table))
          (let ((symbol (string-to-syntax "_"))
                ;; (symbol (string-to-syntax "_"))
                (sst (standard-syntax-table)))
            (dotimes (i 128)
              (unless (= i ?_)
                (if (equal symbol (funcall tablelookup sst i))
                    (modify-syntax-entry i "." table))))))
        (modify-syntax-entry ?$ "." table)
        (modify-syntax-entry ?% "." table)
        ;; exceptions
        (modify-syntax-entry ?# "<" table)
        (modify-syntax-entry ?\n ">" table)
        (modify-syntax-entry ?' "\"" table)
        (modify-syntax-entry ?` "$" table)
        (modify-syntax-entry ?\_ "w" table)
        table))

(defvar py-help-mode-syntax-table
  (let ((st (make-syntax-table py-mode-syntax-table)))
    ;; Don't get confused by apostrophes in the process's output (e.g. if
    ;; you execute "help(os)").
    (modify-syntax-entry ?\' "." st)
    ;; Maybe we should do the same for double quotes?
    (modify-syntax-entry ?\" "." st)
    st))

(defconst py-space-backslash-table
  (let ((table (copy-syntax-table py-mode-syntax-table)))
    (modify-syntax-entry ?\\ " " table)
    table)
  "`py-mode-syntax-table' with backslash given whitespace syntax.")

;; have to bind py-file-queue before installing the kill-emacs-hook
(defvar py-file-queue nil
  "Queue of Python temp files awaiting execution.
Currently-active file is at the head of the list.")

(defvar python-mode-abbrev-table nil)
(define-abbrev-table 'python-mode-abbrev-table ())

(defvar inferior-python-mode-abbrev-table nil
  "Not in use.")
(define-abbrev-table 'inferior-python-mode-abbrev-table ())

;; pdbtrack constants
(defconst py-pdbtrack-stack-entry-regexp
  (concat ".*\\("py-shell-input-prompt-1-regexp">\\|>\\) *\\(.*\\)(\\([0-9]+\\))\\([?a-zA-Z0-9_<>()]+\\)()")
  "Regular expression pdbtrack uses to find a stack trace entry.")

;; ipython.el
;; Recognize the ipython pdb, whose prompt is 'ipdb>' or  'ipydb>'
;;instead of '(Pdb)'
(defvar py-pdbtrack-input-prompt)
(setq py-pdbtrack-input-prompt "^[(<]*[Ii]?[Pp]y?db[>)]+ ")
(defvar py-pydbtrack-input-prompt)
(setq py-pydbtrack-input-prompt "^[(]*ipydb[>)]+ ")

;; pydb-328837.diff
;; (defconst py-pydbtrack-stack-entry-regexp
;;   "^(\\([-a-zA-Z0-9_/.]*\\):\\([0-9]+\\)):[ \t]?\\(.*\n\\)"
;;   "Regular expression pdbtrack uses to find a stack trace entry for pydb.
;;
;; The debugger outputs program-location lines that look like this:
;;    (/usr/bin/zonetab2pot.py:15): makePOT")

(defconst py-pdbtrack-marker-regexp-file-group 2
  "Group position in gud-pydb-marker-regexp that matches the file name.")

(defconst py-pdbtrack-marker-regexp-line-group 3
  "Group position in gud-pydb-marker-regexp that matches the line number.")

(defconst py-pdbtrack-marker-regexp-funcname-group 4
  "Group position in gud-pydb-marker-regexp that matches the function name.")

(defconst py-pdbtrack-track-range 10000
  "Max number of characters from end of buffer to search for stack entry.")

(defvar py-pdbtrack-is-tracking-p nil)

;;; Bindings
(add-to-list 'auto-mode-alist (cons (purecopy "\\.py\\'")  'python-mode))
(add-to-list 'interpreter-mode-alist (cons (purecopy "python") 'python-mode))
(add-to-list 'interpreter-mode-alist (cons (purecopy "jython") 'jython-mode))
(add-to-list 'same-window-buffer-names (purecopy "*Python*"))

(defconst python-font-lock-syntactic-keywords
  ;; Make outer chars of matching triple-quote sequences into generic
  ;; string delimiters.  Fixme: Is there a better way?
  ;; First avoid a sequence preceded by an odd number of backslashes.
  `((,(concat "\\(?:^\\|[^\\]\\(?:\\\\.\\)*\\)" ;Prefix.
              "\\(?:\\('\\)\\('\\)\\('\\)\\|\\(?1:\"\\)\\(?2:\"\\)\\(?3:\"\\)\\)")
     (1 (python-quote-syntax 1) nil lax)
     (2 (python-quote-syntax 2))
     (3 (python-quote-syntax 3)))
    ;; This doesn't really help.
    ;;     (,(rx (and ?\\ (group ?\n))) (1 " "))
    ))

(defun python-quote-syntax (n)
  "Put `syntax-table' property correctly on triple quote.
Used for syntactic keywords.  N is the match number (1, 2 or 3)."
  ;; Given a triple quote, we have to check the context to know
  ;; whether this is an opening or closing triple or whether it's
  ;; quoted anyhow, and should be ignored.  (For that we need to do
  ;; the same job as `syntax-ppss' to be correct and it seems to be OK
  ;; to use it here despite initial worries.)  We also have to sort
  ;; out a possible prefix -- well, we don't _have_ to, but I think it
  ;; should be treated as part of the string.

  ;; Test cases:
  ;;  ur"""ar""" x='"' # """
  ;; x = ''' """ ' a
  ;; '''
  ;; x '"""' x """ \"""" x
  (save-excursion
    (goto-char (match-beginning 0))
    (cond
     ;; Consider property for the last char if in a fenced string.
     ((= n 3)
      (let* ((font-lock-syntactic-keywords nil)
	     (syntax (syntax-ppss)))
	(when (eq t (nth 3 syntax))	; after unclosed fence
	  (goto-char (nth 8 syntax))	; fence position
	  ;; (skip-chars-forward "uUrR")	; skip any prefix
	  ;; Is it a matching sequence?
	  (if (eq (char-after) (char-after (match-beginning 2)))
	      (eval-when-compile (string-to-syntax "|"))))))
     ;; Consider property for initial char, accounting for prefixes.
     ((or (and (= n 2)			; leading quote (not prefix)
	       (not (match-end 1)))     ; prefix is null
	  (and (= n 1)			; prefix
	       (match-end 1)))          ; non-empty
      (let ((font-lock-syntactic-keywords nil))
	(unless (eq 'string (syntax-ppss-context (syntax-ppss)))
	  (eval-when-compile (string-to-syntax "|")))))
     ;; Otherwise (we're in a non-matching string) the property is
     ;; nil, which is OK.
     )))


;;; Keymap and syntax

(defvar py-shell-map nil
  "Keymap used in *Python* shell buffers.")

;; used by py-completion-at-point, the way of python.el
(defvar python-shell-map
  (let ((map (copy-keymap comint-mode-map)))
    (define-key map [tab]   'py-shell-complete)
    (define-key map "\C-c-" 'py-up-exception)
    (define-key map "\C-c=" 'py-down-exception)
    map)
  "Keymap used in *Python* shell buffers.")

;;; Intern
(defun py-point (position)
  "Returns the value of point at certain commonly referenced POSITIONs.
POSITION can be one of the following symbols:

  bol -- beginning of line
  eol -- end of line
  bod -- beginning of def or class
  eod -- end of def or class
  bob -- beginning of buffer
  eob -- end of buffer
  boi -- back to indentation
  bos -- beginning of statement

This function does not modify point or mark."
  (let (erg)
    (save-excursion
      (setq erg
            (progn
              (cond
               ((eq position 'bol) (beginning-of-line))
               ((eq position 'eol) (end-of-line))
               ((eq position 'bod) (py-beginning-of-def-or-class))
               ((eq position 'eod) (py-end-of-def-or-class))
               ;; Kind of funny, I know, but useful for py-up-exception.
               ((eq position 'bob) (goto-char (point-min)))
               ((eq position 'eob) (goto-char (point-max)))
               ((eq position 'boi) (back-to-indentation))
               ((eq position 'bos) (py-beginning-of-statement))
               (t (error "Unknown buffer position requested: %s" position))) (point))))
    erg))


;;; Python specialized rx

(eval-when-compile
  (defconst python-rx-constituents
    (list
     `(block-start          . ,(rx symbol-start
                                   (or "def" "class" "if" "elif" "else" "try"
                                       "except" "finally" "for" "while" "with")
                                   symbol-end))
     `(decorator            . ,(rx line-start (* space) ?@ (any letter ?_)
                                   (* (any word ?_))))
     `(defun                . ,(rx symbol-start (or "def" "class") symbol-end))
     `(symbol-name          . ,(rx (any letter ?_) (* (any word ?_))))
     `(open-paren           . ,(rx (or "{" "[" "(")))
     `(close-paren          . ,(rx (or "}" "]" ")")))
     `(simple-operator      . ,(rx (any ?+ ?- ?/ ?& ?^ ?~ ?| ?* ?< ?> ?= ?%)))
     `(not-simple-operator  . ,(rx (not (any ?+ ?- ?/ ?& ?^ ?~ ?| ?* ?< ?> ?= ?%))))
     `(operator             . ,(rx (or "+" "-" "/" "&" "^" "~" "|" "*" "<" ">"
                                       "=" "%" "**" "//" "<<" ">>" "<=" "!="
                                       "==" ">=" "is" "not")))
     `(assignment-operator  . ,(rx (or "=" "+=" "-=" "*=" "/=" "//=" "%=" "**="
                                       ">>=" "<<=" "&=" "^=" "|="))))
    "Additional Python specific sexps for `python-rx'"))


;;; Font-lock and syntax
(defun python-info-ppss-context (type &optional syntax-ppss)
  "Return non-nil if point is on TYPE using SYNTAX-PPSS.
TYPE can be 'comment, 'string or 'paren.  It returns the start
character address of the specified TYPE."
  (let ((ppss (or syntax-ppss (syntax-ppss))))
    (cond ((eq type 'comment)
           (and (nth 4 ppss)
                (nth 8 ppss)))
          ((eq type 'string)
           (nth 8 ppss))
          ((eq type 'paren)
           (nth 1 ppss))
          (t nil))))

(defvar python-font-lock-keywords nil
  "Additional expressions to highlight in Python mode.")

(setq python-font-lock-keywords
      ;; Keywords
      `(,(rx symbol-start
             (or "and" "del" "from" "not" "while" "as" "elif" "global" "or" "with"
                 "assert" "else" "if" "pass" "yield" "break" "import"
                 "print" "exec" "in" "continue" "finally" "is"
                 "return" "def" "for" "lambda" "try")
             symbol-end)
        ;; functions
        (,(rx symbol-start "def" (1+ space) (group (1+ (or word ?_))))
         (1 font-lock-function-name-face))
        ;; classes
        (,(rx symbol-start (group "class") (1+ space) (group (1+ (or word ?_))))
         (1 font-lock-keyword-face) (2 py-class-name-face))
        (,(rx symbol-start
              (or "raise" "except")
              symbol-end) . py-exception-name-face)
        ;; already pseudo-keyword
        ;; (,(rx symbol-start
        ;;       (or "None" "True" "False" "__debug__" "NotImplemented")
        ;;       symbol-end) . font-lock-constant-face)
        (,(rx symbol-start
              (or "cls" "self" "cls" "Ellipsis" "True" "False" "None"  "__debug__" "NotImplemented")
              symbol-end) . py-pseudo-keyword-face)
        ;; Decorators.
        (,(rx line-start (* (any " \t")) (group "@" (1+ (or word ?_))
                                                (0+ "." (1+ (or word ?_)))))
         (1 py-decorators-face))
        ;; '("\\_<raise[ \t]+\\([a-zA-Z_]+[a-zA-Z0-9_.]*\\)" 1 py-exception-name-face)
        ;; '("[ \t]*\\(_\\{0,2\\}[a-zA-Z][a-zA-Z_0-9.]+_\\{0,2\\}\\) *\\(+\\|-\\|*\\|*\\*\\|/\\|//\\|&\\|%\\||\\|\\^\\|>>\\|<<\\)? ?=[^=\n]"
        ;; Builtin Exceptions
        (,(rx symbol-start
              (or "ArithmeticError" "AssertionError" "AttributeError"
                  "BaseException" "BufferError" "BytesWarning" "DeprecationWarning"
                  "EOFError" "EnvironmentError" "Exception" "FloatingPointError"
                  "FutureWarning" "GeneratorExit" "IOError" "ImportError"
                  "ImportWarning" "IndentationError" "IndexError" "KeyError"
                  "KeyboardInterrupt" "LookupError" "MemoryError" "NameError"
                  "NotImplementedError" "OSError" "OverflowError"
                  "PendingDeprecationWarning" "ReferenceError" "RuntimeError"
                  "RuntimeWarning" "StandardError" "StopIteration" "SyntaxError"
                  "SyntaxWarning" "SystemError" "SystemExit" "TabError" "TypeError"
                  "UnboundLocalError" "UnicodeDecodeError" "UnicodeEncodeError"
                  "UnicodeError" "UnicodeTranslateError" "UnicodeWarning"
                  "UserWarning" "ValueError" "Warning" "ZeroDivisionError")
              symbol-end) . py-exception-name-face)
        ;; (,(rx (or space line-start) symbol-start "range
        ;; Builtins
        (,(rx (or space line-start) symbol-start
              (or "_" "__doc__" "__import__" "__name__" "__package__" "abs" "all"
                  "any" "apply" "basestring" "bin" "bool" "buffer" "bytearray"
                  "bytes" "callable" "chr" "classmethod" "cmp" "coerce" "compile"
                  "complex" "delattr" "dict" "dir" "divmod" "enumerate" "eval"
                  "execfile" "file" "filter" "float" "format" "frozenset"
                  "getattr" "globals" "hasattr" "hash" "help" "hex" "id" "input"
                  "int" "intern" "isinstance" "issubclass" "iter" "len" "list"
                  "locals" "long" "map" "max" "min" "next" "object" "oct" "open"
                  "ord" "pow" "print" "property" "range" "raw_input" "reduce"
                  "reload" "repr" "reversed" "round" "set" "setattr" "slice"
                  "sorted" "staticmethod" "str" "sum" "super" "tuple" "type"
                  "unichr" "unicode" "vars" "xrange" "zip")
              symbol-end) . py-builtins-face)
        ;; '("[ \t]*\\(_\\{0,2\\}[a-zA-Z][a-zA-Z_0-9.]+_\\{0,2\\}\\) *\\(+\\|-\\|*\\|*\\*\\|/\\|//\\|&\\|%\\||\\|\\^\\|>>\\|<<\\)? ?=[^=\n]"
        ;; 1 py-variable-name-face)
        (,(python-rx line-start (* (any " \t"))(group (** 0 2 "_") word (0+ (or word ?_))(** 0 2 "_"))(* (any " \t")) assignment-operator)
         1 py-variable-name-face)
        ;; asignations
        ;; support for a = b = c = 5
        (,(lambda (limit)
            (let ((re (python-rx (group (+ (any word ?. ?_)))
                                 (? ?\[ (+ (not (any ?\]))) ?\]) (* space)
                                 assignment-operator)))
              (when (re-search-forward re limit t)
                (while (and (python-info-ppss-context 'paren)
                            (re-search-forward re limit t)))
                (if (and (not (python-info-ppss-context 'paren))
                         (not (equal (char-after (point-marker)) ?=)))
                    t
                  (set-match-data nil)))))
         (1 py-variable-name-face nil nil))
        ;; support for a, b, c = (1, 2, 3)
        (,(lambda (limit)
            (let ((re (python-rx (group (+ (any word ?. ?_))) (* space)
                                 (* ?, (* space) (+ (any word ?. ?_)) (* space))
                                 ?, (* space) (+ (any word ?. ?_)) (* space)
                                 assignment-operator)))
              (when (and (re-search-forward re limit t)
                         (goto-char (nth 3 (match-data))))
                (while (and (python-info-ppss-context 'paren)
                            (re-search-forward re limit t))
                  (goto-char (nth 3 (match-data))))
                (if (not (python-info-ppss-context 'paren))
                    t
                  (set-match-data nil)))))
         (1 py-variable-name-face nil nil))
        ;; (,(rx (or space line-start) symbol-start "range" symbol-end) . py-builtins-face)
        ;; Numbers
        (,(rx symbol-start (or (1+ digit) (1+ hex-digit)) symbol-end) . py-number-face)))

(defconst py-font-lock-syntactic-keywords
  '(("[^\\]\\\\\\(?:\\\\\\\\\\)*\\(\\s\"\\)\\1\\(\\1\\)"
     (2
      (7)))
    ("\\([RUBrub]?\\)[Rr]?\\(\\s\"\\)\\2\\(\\2\\)"
     (1
      (py-quote-syntax 1))
     (2
      (py-quote-syntax 2))
     (3
      (py-quote-syntax 3)))))

(defun py-quote-syntax (n)
  "Put `syntax-table' property correctly on triple quote.
Used for syntactic keywords.  N is the match number (1, 2 or 3)."
  ;; Given a triple quote, we have to check the context to know
  ;; whether this is an opening or closing triple or whether it's
  ;; quoted anyhow, and should be ignored.  (For that we need to do
  ;; the same job as `syntax-ppss' to be correct and it seems to be OK
  ;; to use it here despite initial worries.) We also have to sort
  ;; out a possible prefix -- well, we don't _have_ to, but I think it
  ;; should be treated as part of the string.
  ;; Test cases:
  ;;  ur"""ar""" x='"' # """
  ;; x = ''' """ ' a
  ;; '''
  ;; x '"""' x """ \"""" x
  (save-excursion
    (goto-char (match-beginning 0))
    (cond
     ;; Consider property for the last char if in a fenced string.
     ((= n 3)
      (let* ((font-lock-syntactic-keywords nil)
             (syntax (if (featurep 'xemacs)
                         (parse-partial-sexp (point-min) (point))
                       (syntax-ppss))))
        (when (eq t (nth 3 syntax))     ; after unclosed fence
          (goto-char (nth 8 syntax))    ; fence position
          (skip-chars-forward "uUrRbB") ; skip any prefix
          ;; Is it a matching sequence?
          (if (eq (char-after) (char-after (match-beginning 2)))
              (eval-when-compile (string-to-syntax "|"))))))
     ;; Consider property for initial char, accounting for prefixes.
     ((or (and (= n 2)                  ; leading quote (not prefix)
               (= (match-beginning 1) (match-end 1))) ; prefix is null
          (and (= n 1)                  ; prefix
               (/= (match-beginning 1) (match-end 1)))) ; non-empty
      (let ((font-lock-syntactic-keywords nil))
        (unless (eq 'string (syntax-ppss-context (if (featurep 'xemacs)
                                                     (parse-partial-sexp (point-min) (point))
                                                   (syntax-ppss))))
          ;; (eval-when-compile (string-to-syntax "|"))
          (eval-when-compile (string-to-syntax "|")))))
     ;; Otherwise (we're in a non-matching string) the property is
     ;; nil, which is OK.
     )))

(defconst python-dotty-syntax-table
  (let ((table (make-syntax-table)))
    (set-char-table-parent table py-mode-syntax-table)
    (modify-syntax-entry ?. "_" table)
    table)
  "Syntax table giving `.' symbol syntax.
Otherwise inherits from `py-mode-syntax-table'.")

;; An auxiliary syntax table which places underscore and dot in the
;; symbol class for simplicity
(defvar py-dotted-expression-syntax-table nil
  "Syntax table used to identify Python dotted expressions.")
(when (not py-dotted-expression-syntax-table)
  (setq py-dotted-expression-syntax-table
        (copy-syntax-table py-mode-syntax-table))
  (modify-syntax-entry ?_ "_" py-dotted-expression-syntax-table)
  (modify-syntax-entry ?. "_" py-dotted-expression-syntax-table))

;; credits to python.el
(defun py-beg-of-defun-function ()
  (set (make-local-variable 'beginning-of-defun-function)
       'py-beginning-of-def-or-class))

(defun py-end-of-defun-function ()
  (set (make-local-variable 'end-of-defun-function) 'py-end-of-def-or-class))

(make-obsolete-variable 'jpython-mode-hook 'jython-mode-hook nil)
(defvar jython-mode-hook nil
  "*Hook called by `jython-mode'. `jython-mode' also calls
`python-mode-hook'.")

(defvar py-shell-hook nil
  "*Hook called by `py-shell'.")

;; In previous version of python-mode.el, the hook was incorrectly
;; called py-mode-hook, and was not defvar'd.  Deprecate its use.
(and (fboundp 'make-obsolete-variable)
     (make-obsolete-variable 'py-mode-hook 'python-mode-hook nil))

(defvar py-keywords "\\_<\\(ArithmeticError\\|AssertionError\\|AttributeError\\|BaseException\\|BufferError\\|BytesWarning\\|DeprecationWarning\\|EOFError\\|Ellipsis\\|EnvironmentError\\|Exception\\|False\\|FloatingPointError\\|FutureWarning\\|GeneratorExit\\|IOError\\|ImportError\\|ImportWarning\\|IndentationError\\|IndexError\\|KeyError\\|KeyboardInterrupt\\|LookupError\\|MemoryError\\|NameError\\|NoneNotImplementedError\\|NotImplemented\\|OSError\\|OverflowError\\|PendingDeprecationWarning\\|ReferenceError\\|RuntimeError\\|RuntimeWarning\\|StandardError\\|StopIteration\\|SyntaxError\\|SyntaxWarning\\|SystemError\\|SystemExit\\|TabError\\|True\\|TypeError\\|UnboundLocalError\\|UnicodeDecodeError\\|UnicodeEncodeError\\|UnicodeError\\|UnicodeTranslateError\\|UnicodeWarning\\|UserWarning\\|ValueError\\|Warning\\|ZeroDivisionError\\|__debug__\\|__import__\\|__name__\\|abs\\|all\\|and\\|any\\|apply\\|as\\|assert\\|basestring\\|bin\\|bool\\|break\\|buffer\\|bytearray\\|callable\\|chr\\|class\\|classmethod\\|cmp\\|coerce\\|compile\\|complex\\|continue\\|copyright\\|credits\\|def\\|del\\|delattr\\|dict\\|dir\\|divmod\\|elif\\|else\\|enumerate\\|eval\\|except\\|exec\\|execfile\\|exit\\|file\\|filter\\|float\\|for\\|format\\|from\\|getattr\\|global\\|globals\\|hasattr\\|hash\\|help\\|hex\\|id\\|if\\|import\\|in\\|input\\|int\\|intern\\|is\\|isinstance\\|issubclass\\|iter\\|lambda\\|len\\|license\\|list\\|locals\\|long\\|map\\|max\\|memoryview\\|min\\|next\\|not\\|object\\|oct\\|open\\|or\\|ord\\|pass\\|pow\\|print\\|property\\|quit\\|raise\\|range\\|raw_input\\|reduce\\|reload\\|repr\\|return\\|round\\|set\\|setattr\\|slice\\|sorted\\|staticmethod\\|str\\|sum\\|super\\|tuple\\|type\\|unichr\\|unicode\\|vars\\|while\\|with\\|xrange\\|yield\\|zip\\|\\)\\_>"
  "Contents like py-fond-lock-keyword")

(defun py-insert-default-shebang ()
  "Insert in buffer shebang of installed default Python. "
  (interactive "*")
  (let* ((erg (if py-edit-only-p
                  py-shell-name
                (executable-find py-shell-name)))
         (sheb (concat "#! " erg)))
    (insert sheb)))

(defun py-electric-comment (arg)
  "Insert a comment. If starting a comment, indent accordingly.

If a numeric argument ARG is provided, that many colons are inserted
non-electrically.
With \\[universal-argument] \"#\" electric behavior is inhibited inside a string or comment."
  (interactive "*P")
  (if (and py-indent-comments py-electric-comment-p)
      (if (ignore-errors (eq 4 (car-safe arg)))
          (insert "#")
        (when (and (eq last-command 'py-electric-comment) (looking-back " "))
          (forward-char -1))
        (if (interactive-p) (self-insert-command (prefix-numeric-value arg))
          (insert "#"))
        (let ((orig (copy-marker (point)))
              (indent (py-compute-indentation)))
          (unless
              ;; (or
              (eq (current-indentation) indent)
            ;; (looking-back "#[ \t]*"))
            (goto-char orig)
            (beginning-of-line)
            (delete-horizontal-space)
            (indent-to indent)
            (goto-char orig))
          (when py-electric-comment-add-space-p
            (unless (looking-at "[ \t]")
              (insert " "))))
        (setq last-command this-command))
    (self-insert-command (prefix-numeric-value arg))))

(defun py-electric-colon (arg)
  "Insert a colon and indent accordingly.

If a numeric argument ARG is provided, that many colons are inserted
non-electrically.

Electric behavior is inhibited inside a string or
comment or by universal prefix C-u.
Default is nil, controlled by `py-electric-colon-active-p'"
  (interactive "*P")
  (cond ((not py-electric-colon-active-p)
         (self-insert-command (prefix-numeric-value arg)))
        ((eq 4 (prefix-numeric-value arg))
         (self-insert-command 1))
        (t (self-insert-command (prefix-numeric-value arg))
           (unless (py-in-string-or-comment-p)
             (let ((orig (copy-marker (point)))
                   (indent (py-compute-indentation)))
               (unless (or (eq (current-indentation) indent)
                           (and (py-top-level-form-p)(< (current-indentation) indent)))
                 (beginning-of-line)
                 (delete-horizontal-space)
                 (indent-to indent))
               (goto-char orig))))))

(defun py-top-level-form-p ()
  "Return non-nil, if line starts with a top level definition.

Used by `py-electric-colon', which will not indent than. "
  (let (erg)
    (save-excursion
      (beginning-of-line)
      (setq erg (or (looking-at py-class-re)
                    (looking-at py-def-re))))
    erg))


;; Electric deletion
(defun py-electric-backspace (&optional arg)
  "Delete preceding character or level of indentation.

With ARG do that ARG times.
Returns column reached. "
  (interactive "*p")
  (let ((arg (or arg 1))
        erg)
    (dotimes (i arg)
      (if (looking-back "^[ \t]+")
          (let* ((remains (% (current-column) py-indent-offset)))
            (if (< 0 remains)
                (delete-char (- remains))
              (indent-line-to (- (current-indentation) py-indent-offset))))
        (delete-char (- 1))))
    (setq erg (current-column))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-electric-delete (&optional arg)
  "Delete following character or levels of whitespace.

With ARG do that ARG times. "
  (interactive "*p")
  (let ((arg (or arg 1)))
    (dotimes (i arg)
      (if (and (or (bolp)(looking-back "^[ \t]+")) (looking-at "[ \t]+"))
          (let* ((remains (% (+ (current-column) (- (match-end 0)(match-beginning 0))) py-indent-offset)))
            (if (< 0 remains)
                (delete-char remains)
              (delete-char py-indent-offset)))
        (delete-char 1)))))

;; (defun py-electric-delete (arg)
;;   "Delete preceding or following character or levels of whitespace.
;;
;; The behavior of this function depends on the variable
;; `delete-key-deletes-forward'.  If this variable is nil (or does not
;; exist, as in older Emacsen and non-XEmacs versions), then this
;; function behaves identically to \\[c-electric-backspace].
;;
;; If `delete-key-deletes-forward' is non-nil and is supported in your
;; Emacs, then deletion occurs in the forward direction, by calling the
;; function in `py-delete-function'.
;;
;; \\[universal-argument] (programmatically, argument ARG) specifies the
;; number of characters to delete (default is 1)."
;;   (interactive "*p")
;;   (if (or (and (fboundp 'delete-forward-p) ;XEmacs 21
;;                (delete-forward-p))
;;           (and (boundp 'delete-key-deletes-forward) ;XEmacs 20
;;                delete-key-deletes-forward))
;;       (funcall py-delete-function arg)
;;     (py-electric-backspace arg)))

;; required for pending-del and delsel modes
(put 'py-electric-colon 'delete-selection t) ;delsel
(put 'py-electric-colon 'pending-delete t) ;pending-del
(put 'py-electric-backspace 'delete-selection 'supersede) ;delsel
(put 'py-electric-backspace 'pending-delete 'supersede) ;pending-del
(put 'py-electric-delete 'delete-selection 'supersede) ;delsel
(put 'py-electric-delete 'pending-delete 'supersede) ;pending-del


(defun py-indent-line-outmost (&optional arg)
  "Indent the current line to the outmost reasonable indent.

With optional \\[universal-argument] an indent with length `py-indent-offset' is inserted unconditionally "
  (interactive "*P")
  (let* ((need (py-compute-indentation (point)))
         (cui (current-indentation))
         (cuc (current-column)))
    (cond ((eq 4 (prefix-numeric-value arg))
           (insert (make-string py-indent-offset ?\ )))
          (t
           (if (and (eq need cui)(not (eq cuc cui)))
               (back-to-indentation)
             (beginning-of-line)
             (delete-horizontal-space)
             (indent-to need))))))

(defvar py-indent-line-indent nil
  "Used internal by `py-indent-line'")

(defun py-indent-line-intern ()
  ;; (when (prefix-numeric-value arg) (message "%s" (prefix-numeric-value arg)))
  (unless (eq this-command last-command)(setq py-indent-line-indent (py-compute-indentation)))
  (if py-tab-indent
      (cond ((eq py-indent-line-indent cui)
             (when (eq this-command last-command)
               (beginning-of-line)
               (delete-horizontal-space)
               (if (<= (line-beginning-position) (+ (point) (- col cui)))
                   (forward-char (- col cui))
                 (beginning-of-line))))
            ((< cui py-indent-line-indent)
             (if (eq this-command last-command)
                 (progn
                   (beginning-of-line)
                   (delete-horizontal-space)
                   (indent-to (+ (* (/ cui py-indent-offset) py-indent-offset) py-indent-offset))
                   (forward-char (- col cui)))
               (beginning-of-line)
               (delete-horizontal-space)
               (indent-to py-indent-line-indent)
               (forward-char (- col cui))))
            (t (beginning-of-line)
               (delete-horizontal-space)
               (indent-to py-indent-line-indent)
               (if (<= (line-beginning-position) (+ (point) (- col cui)))
                   (forward-char (- col cui))
                 (beginning-of-line))))
    (insert-tab)))

(defun py-indent-line (&optional arg)
  "Indent the current line according to Python rules.

When called interactivly with \\[universal-argument], ignore dedenting rules for block closing statements
\(e.g. return, raise, break, continue, pass)

An optional \\[universal-argument] followed by a numeric argument neither 1 nor 4 will switch off `py-smart-indentation' for this execution. This permits to correct allowed but unwanted indents.
Similar to `toggle-py-smart-indentation' resp. `py-smart-indentation-off' followed by TAB.

This function is normally used by `indent-line-function' resp.
\\[indent-for-tab-command].
Returns current indentation "
  (interactive "P")
  (let ((cui (current-indentation))
        (col (current-column))
        (psi py-smart-indentation))
    (if (interactive-p)
        (progn
          (setq py-indent-line-indent (py-compute-indentation))
          (cond ((eq 4 (prefix-numeric-value arg))
                 (beginning-of-line)
                 (delete-horizontal-space)
                 (indent-to (+ py-indent-line-indent py-indent-offset)))
                ((not (eq 1 (prefix-numeric-value arg)))
                 (py-smart-indentation-off)
                 (py-indent-line-intern)
                 (setq py-smart-indentation psi))
                (t (indent-to py-indent-line-indent))))
      (py-indent-line-intern)))
  (when (and (interactive-p) py-verbose-p)(message "%s" (current-indentation)))
  (current-indentation))

(defun py-newline-and-indent ()
  "Add a newline and indent to outmost reasonable indent.
When indent is set back manually, this is honoured in following lines. "
  (interactive "*")
  (let ((ci (current-indentation))
        erg)
    (if (< ci (current-column))         ; if point beyond indentation
        (progn
          (newline)
          (setq erg (indent-to-column (py-compute-indentation))))
      (beginning-of-line)
      (insert-char ?\n 1)
      (insert (make-string (setq erg (py-compute-indentation)) ?\ ))
      ;; (move-to-column erg)
      (when (looking-at "\\([ \t]+\\)") (delete-region (match-beginning 1) (match-end 1))))
    (when (and (looking-at "[ \t]+")
               (nth 1 (if (featurep 'xemacs)
                          (parse-partial-sexp (point-min) (point))
                        (syntax-ppss))))
      (delete-region (match-beginning 0) (match-end 0)))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defalias 'py-newline-and-close-block 'py-newline-and-dedent)
(defun py-newline-and-dedent ()
  "Add a newline and indent to one level below current.
Returns column. "
  (interactive "*")
  (let ((cui (current-indentation))
        erg)
    (newline)
    (when (< 0 cui)
      (setq erg (- (py-compute-indentation) py-indent-offset))
      (indent-to-column erg))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun toggle-force-local-shell (&optional arg)
  "If locally indicated Python shell should be taken and
enforced upon sessions execute commands.

Toggles boolean `py-force-local-shell-p' along with `py-force-py-shell-name-p'
Returns value of `toggle-force-local-shell' switched to.

When on, kind of an option 'follow', local shell sets `py-shell-name', enforces its use afterwards.

See also commands
`py-force-local-shell-on'
`py-force-local-shell-off'
 "
  (interactive (list arg))
  (let ((arg (or arg (if py-force-local-shell-p -1 1))))
    (if (< 0 arg)
        (progn
          (setq py-shell-name (or py-local-command (py-choose-shell)))
          (setq py-force-local-shell-p t))
      (setq py-shell-name (default-value 'py-shell-name))
      (setq py-force-local-shell-p nil))
    (when (or py-verbose-p (interactive-p))
      (if py-force-local-shell-p
          (message "Enforce %s"  py-shell-name)
        (message "py-shell-name default restored to: %s" py-shell-name))))
  py-shell-name)

(defun py-force-local-shell-on ()
  "Make sure, `py-py-force-local-shell-p' is on.

Returns value of `py-force-local-shell-p'.

Kind of an option 'follow', local shell sets `py-shell-name', enforces its use afterwards "
  (interactive)
  (let* ((erg (toggle-force-local-shell 1)))
    (when (or py-verbose-p (interactive-p))
      (message "Enforce %s" py-shell-name))))

(defun py-force-local-shell-off ()
  "Restore `py-shell-name' default value and `behaviour'. "
  (interactive)
  (let* ((erg (toggle-force-local-shell 1)))
    (when (or py-verbose-p (interactive-p))
      (message "py-shell-name default restored to: %s" py-shell-name)
      (message "Enforce %s" py-shell-name))))

;; toggle-force-py-shell-name-p forms
(defun toggle-force-py-shell-name-p (&optional arg)
  "If customized default `py-shell-name' should be enforced upon execution.

If `py-force-py-shell-name-p' should be on or off.
Returns value of `py-force-py-shell-name-p' switched to.

See also commands
force-py-shell-name-p-on
force-py-shell-name-p-off

Caveat: Completion might not work that way.
"
  (interactive "p")
  (let ((arg (or arg (if py-force-py-shell-name-p -1 1))))
    (if (< 0 arg)
        (setq py-force-py-shell-name-p t)
      (setq py-force-py-shell-name-p nil))
    (when (or py-verbose-p (interactive-p)) (message "py-force-py-shell-name-p: %s" py-force-py-shell-name-p))
    py-force-py-shell-name-p))

(defun force-py-shell-name-p-on (&optional arg)
  "Switches `py-force-py-shell-name-p' on.

Customized default `py-shell-name' will be enforced upon execution.
Returns value of `py-force-py-shell-name-p'.

Caveat: Completion might not work that way.
"
  (interactive "p")
  (let ((arg (or arg 1)))
    (toggle-force-py-shell-name-p arg))
  (when (or py-verbose-p (interactive-p)) (message "py-force-py-shell-name-p: %s" py-force-py-shell-name-p))
  py-force-py-shell-name-p)

(defun force-py-shell-name-p-off ()
  "Make sure, `py-force-py-shell-name-p' is off.

Function to use by executes will be guessed from environment.
Returns value of `py-force-py-shell-name-p'. "
  (interactive)
  (toggle-force-py-shell-name-p -1)
  (when (or py-verbose-p (interactive-p)) (message "py-force-py-shell-name-p: %s" py-force-py-shell-name-p))
  py-force-py-shell-name-p)

(defun py-toggle-indent-tabs-mode ()
  "Toggle `indent-tabs-mode'.

Returns value of `indent-tabs-mode' switched to. "
  (interactive)
  (when
      (setq indent-tabs-mode (not indent-tabs-mode))
    (setq tab-width py-indent-offset))
  (when (and py-verbose-p (interactive-p)) (message "indent-tabs-mode %s  py-indent-offset %s" indent-tabs-mode py-indent-offset))
  indent-tabs-mode)

(defun py-indent-tabs-mode (arg &optional iact)
  "With positive ARG switch `indent-tabs-mode' on.

With negative ARG switch `indent-tabs-mode' off.
Returns value of `indent-tabs-mode' switched to. "
  (interactive "p")
  (if (< 0 arg)
      (progn
        (setq indent-tabs-mode t)
        (setq tab-width py-indent-offset))
    (setq indent-tabs-mode nil))
  (when (and py-verbose-p (or iact (interactive-p))) (message "indent-tabs-mode %s   py-indent-offset %s" indent-tabs-mode py-indent-offset))
  indent-tabs-mode)

(defun py-indent-tabs-mode-on (arg)
  "Switch `indent-tabs-mode' on. "
  (interactive "p")
  (indent-tabs-mode (abs arg)(interactive-p)))

(defun py-indent-tabs-mode-off (arg)
  "Switch `indent-tabs-mode' on. "
  (interactive "p")
  (indent-tabs-mode (- (abs arg))(interactive-p)))

;;; Guess indent offset
(defun py-guessed-sanity-check (guessed)
  (and (>= guessed 2)(<= guessed 8)(eq 0 (% guessed 2))))

(defun py-guess-indent-offset (&optional global orig origline)
  "Guess a value for, and change, `py-indent-offset'.

By default, make a buffer-local copy of `py-indent-offset' with the
new value.
With optional argument GLOBAL change the global value of `py-indent-offset'.

Indent might be guessed savely only from beginning of a block.
Returns `py-indent-offset'"
  (interactive "P")
  (save-excursion
    (let* ((orig (or orig (point)))
           (origline (or origline (py-count-lines)))
           (firstindent
            (if (eq origline (py-count-lines))
                (progn (py-beginning-of-statement)
                       (if (eq origline (py-count-lines))
                           (progn (py-beginning-of-statement)(current-column)) (current-column)))))
           (erg (when firstindent
                  (py-beginning-of-block)
                  (if
                      (< (current-column) firstindent)
                      (current-column)
                    (progn (goto-char orig)
                           ;; need a block-start
                           (when
                               (setq firstindent (progn (py-beginning-of-block)(current-indentation)))
                             (when (eq origline (py-count-lines))
                               (setq firstindent (progn (py-beginning-of-block)(current-indentation))))
                             (when (ignore-errors (< firstindent (py-down-statement)))
                               (current-indentation)))))))
           (guessed (when erg (abs (- firstindent erg)))))
      (if (and guessed (py-guessed-sanity-check guessed))
          (setq py-indent-offset guessed)
        (setq py-indent-offset (default-value 'py-indent-offset)))
      (funcall (if global 'kill-local-variable 'make-local-variable)
               'py-indent-offset)
      (when (and py-verbose-p (interactive-p))
        (message "%s value of py-indent-offset:  %d"
                 (if global "Global" "Local")
                 py-indent-offset))
      py-indent-offset)))

;;;
(defun py-comment-indent-function ()
  "Python version of `comment-indent-function'."
  ;; This is required when filladapt is turned off.  Without it, when
  ;; filladapt is not used, comments which start in column zero
  ;; cascade one character to the right
  (save-excursion
    (beginning-of-line)
    (let ((eol (line-end-position)))
      (and comment-start-skip
           (re-search-forward comment-start-skip eol t)
           (setq eol (match-beginning 0)))
      (goto-char eol)
      (skip-chars-backward " \t")
      (max comment-column (+ (current-column) (if (bolp) 0 1))))))

(defun py-narrow-to-defun ()
  "Make text outside current def or class invisible.

The defun visible is the one that contains point or follows point. "
  (interactive "P")
  (save-excursion
    (widen)
    (py-end-of-def-or-class)
    (let ((end (point)))
      (py-beginning-of-def-or-class)
      (narrow-to-region (point) end))))

;; make general form below work also in these cases
(defalias 'py-beginning-of-paragraph 'backward-paragraph)
(defalias 'py-end-of-paragraph 'forward-paragraph)

;;; Shifting
(defalias 'py-shift-region-left 'py-shift-left)
(defun py-shift-left (&optional count start end)
  "Dedent region according to `py-indent-offset' by COUNT times.

If no region is active, current line is dedented.
Returns indentation reached. "
  (interactive "p")
  (let ((erg (py-shift-intern (- count) start end)))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defalias 'py-shift-region-right 'py-shift-right)
(defun py-shift-right (&optional count beg end)
  "Indent region according to `py-indent-offset' by COUNT times.

If no region is active, current line is indented.
Returns indentation reached. "
  (interactive "p")
  (let ((erg (py-shift-intern count beg end)))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-intern (count &optional start end)
  (save-excursion
    (let* ((inhibit-point-motion-hooks t)
           deactivate-mark
           (beg (cond (start)
                      ((region-active-p)
                       (save-excursion
                         (goto-char
                          (region-beginning))))
                      (t (line-beginning-position))))
           (end (cond (end)
                      ((region-active-p)
                       (save-excursion
                         (goto-char
                          (region-end))))
                      (t (line-end-position))))
           (orig end))
      (setq beg (copy-marker beg))
      (setq end (copy-marker end))
      ;; lp:962227
      ;; (dotimes (i (abs count))
      (if (< 0 count)
          (indent-rigidly beg end py-indent-offset)
        (indent-rigidly beg end (- py-indent-offset)))
      ;; )
      (push-mark beg t)
      (goto-char end)
      (skip-chars-backward " \t\r\n\f"))
    (py-indentation-of-statement)))

(defun py-shift-forms-base (form arg &optional beg end)
  (let* ((begform (intern-soft (concat "py-beginning-of-" form)))
         (endform (intern-soft (concat "py-end-of-" form)))
         (orig (copy-marker (point)))
         (beg (cond (beg)
                    ((region-active-p)
                     (save-excursion
                       (goto-char (region-beginning))
                       (line-beginning-position)))
                    (t (save-excursion
                         (funcall begform)
                         (line-beginning-position)))))
         (end (cond (end)
                    ((region-active-p)
                     (region-end))
                    (t (funcall endform))))
         (erg (py-shift-intern arg beg end)))
    (goto-char orig)
    erg))

(defun py-shift-paragraph-right (&optional arg)
  "Indent paragraph by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "paragraph" (or arg py-indent-offset))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-paragraph-left (&optional arg)
  "Dedent paragraph by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "paragraph" (- (or arg py-indent-offset)))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-block-right (&optional arg)
  "Indent block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "block" (or arg py-indent-offset))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-block-left (&optional arg)
  "Dedent block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "block" (- (or arg py-indent-offset)))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-clause-right (&optional arg)
  "Indent clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "clause" (or arg py-indent-offset))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-clause-left (&optional arg)
  "Dedent clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "clause" (- (or arg py-indent-offset)))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-def-right (&optional arg)
  "Indent def by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "def" (or arg py-indent-offset))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-def-left (&optional arg)
  "Dedent def by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "def" (- (or arg py-indent-offset)))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-class-right (&optional arg)
  "Indent class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "class" (or arg py-indent-offset))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-class-left (&optional arg)
  "Dedent class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "class" (- (or arg py-indent-offset)))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-line-right (&optional arg)
  "Indent line by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "line" (or arg py-indent-offset))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-line-left (&optional arg)
  "Dedent line by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "line" (- (or arg py-indent-offset)))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-statement-right (&optional arg)
  "Indent statement by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "statement" (or arg py-indent-offset))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-statement-left (&optional arg)
  "Dedent statement by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py-shift-forms-base "statement" (- (or arg py-indent-offset)))))
    (when (and (interactive-p) py-verbose-p) (message "%s" erg))
    erg))

(defun py-indent-and-forward ()
  "Indent current line according to mode, move one line forward. "
  (interactive "*")
  (indent-according-to-mode)
  (if (eobp)
      (newline-and-indent)
    (forward-line 1))
  (back-to-indentation))

(defun py-indent-region (start end &optional indent-offset)
  "Reindent a region of Python code.

With optional INDENT-OFFSET specify a different value than `py-indent-offset' at place.

Guesses the outmost reasonable indent
Returns and keeps relative position "
  (interactive "*r\nP")
  (let ((orig (copy-marker (point)))
        (beg start)
        (end (copy-marker end))
        (py-indent-offset (prefix-numeric-value
                           (or indent-offset py-indent-offset))))
    (goto-char beg)
    (while (< (line-end-position) end)
      (py-indent-and-forward))
    (unless (empty-line-p) (py-indent-line))
    (goto-char orig)))

;;; Positions
(defun py-beginning-of-paragraph-position ()
  "Returns beginning of paragraph position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-paragraph)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-paragraph-position ()
  "Returns end of paragraph position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-paragraph)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-block-position ()
  "Returns beginning of block position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-block)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-block-position ()
  "Returns end of block position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-block)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-clause-position ()
  "Returns beginning of clause position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-clause)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-clause-position ()
  "Returns end of clause position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-clause)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-block-or-clause-position ()
  "Returns beginning of block-or-clause position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-block-or-clause)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-block-or-clause-position ()
  "Returns end of block-or-clause position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-block-or-clause)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-def-position ()
  "Returns beginning of def position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-def)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-def-position ()
  "Returns end of def position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-def)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-class-position ()
  "Returns beginning of class position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-class)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-class-position ()
  "Returns end of class position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-class)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-def-or-class-position ()
  "Returns beginning of def-or-class position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-def-or-class)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-def-or-class-position ()
  "Returns end of def-or-class position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-def-or-class)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-line-position ()
  "Returns beginning of line position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-line)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-line-position ()
  "Returns end of line position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-line)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-statement-position ()
  "Returns beginning of statement position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-statement)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-statement-position ()
  "Returns end of statement position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-statement)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-expression-position ()
  "Returns beginning of expression position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-expression)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-expression-position ()
  "Returns end of expression position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-expression)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-partial-expression-position ()
  "Returns beginning of partial-expression position. "
  (interactive)
  (save-excursion
    (let ((erg (py-beginning-of-partial-expression)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-end-of-partial-expression-position ()
  "Returns end of partial-expression position. "
  (interactive)
  (save-excursion
    (let ((erg (py-end-of-partial-expression)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

;;; Bounds
(defun py-bounds-of-statement (&optional position)
  "Returns bounds of statement at point.

With optional POSITION, a number, report bounds of statement at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-statement-position))
            (end (py-end-of-statement-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-bounds-of-block (&optional position)
  "Returns bounds of block at point.

With optional POSITION, a number, report bounds of block at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-block-position))
            (end (py-end-of-block-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-bounds-of-clause (&optional position)
  "Returns bounds of clause at point.

With optional POSITION, a number, report bounds of clause at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-clause-position))
            (end (py-end-of-clause-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-bounds-of-block-or-clause (&optional position)
  "Returns bounds of block-or-clause at point.

With optional POSITION, a number, report bounds of block-or-clause at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-block-or-clause-position))
            (end (py-end-of-block-or-clause-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-bounds-of-def (&optional position)
  "Returns bounds of def at point.

With optional POSITION, a number, report bounds of def at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-def-position))
            (end (py-end-of-def-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-bounds-of-class (&optional position)
  "Returns bounds of class at point.

With optional POSITION, a number, report bounds of class at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-class-position))
            (end (py-end-of-class-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-bounds-of-region ()
  "Returns bounds of region at point.

Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (let ((beg (region-beginning))
            (end (region-end)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-beginning-of-buffer-position ()
  (point-min))

(defun py-end-of-buffer-position ()
  (point-max))

(defun py-bounds-of-buffer (&optional position)
  "Returns bounds of buffer at point.

With optional POSITION, a number, report bounds of buffer at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-buffer-position))
            (end (py-end-of-buffer-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-bounds-of-expression (&optional position)
  "Returns bounds of expression at point.

With optional POSITION, a number, report bounds of expression at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-expression-position))
            (end (py-end-of-expression-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

(defun py-bounds-of-partial-expression (&optional position)
  "Returns bounds of partial-expression at point.

With optional POSITION, a number, report bounds of partial-expression at POSITION.
Returns a list, whose car is beg, cdr - end."
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (when position (goto-char position))
      (let ((beg (py-beginning-of-partial-expression-position))
            (end (py-end-of-partial-expression-position)))
        (if (and beg end)
            (when (and py-verbose-p (interactive-p)) (message "%s" (list beg end)))
          (list beg end))))))

;;; Declarations
(defun py-bounds-of-declarations ()
  "Bounds of consecutive multitude of assigments resp. statements around point.

Indented same level, which don't open blocks.
Typically declarations resp. initialisations of variables following
a class or function definition.
See also py-bounds-of-statements "
  (interactive)
  (let* ((orig-indent (progn
                        (back-to-indentation)
                        (unless (py-beginning-of-statement-p)
                          (py-beginning-of-statement))
                        (unless (py-beginning-of-block-p)
                          (current-indentation))))
         (orig (point))
         last beg end)
    (when orig-indent
      (setq beg (line-beginning-position))
      ;; look upward first
      (while (and
              (progn
                (unless (py-beginning-of-statement-p)
                  (py-beginning-of-statement))
                (line-beginning-position))
              (py-beginning-of-statement)
              (not (py-beginning-of-block-p))
              (eq (current-indentation) orig-indent))
        (setq beg (line-beginning-position)))
      (goto-char orig)
      (while (and (setq last (line-end-position))
                  (setq end (py-down-statement))
                  (not (py-beginning-of-block-p))
                  (eq (py-indentation-of-statement) orig-indent)))
      (setq end last)
      (goto-char beg)
      (if (and beg end)
          (progn
            (when (and py-verbose-p (interactive-p)) (message "%s %s" beg end))
            (cons beg end))
        (when (and py-verbose-p (interactive-p)) (message "%s" nil))
        nil))))

(defalias 'py-backward-declarations 'py-beginning-of-declarations)
(defun py-beginning-of-declarations ()
  "Got to the beginning of assigments resp. statements in current level which don't open blocks.
"
  (interactive)
  (let* ((bounds (py-bounds-of-declarations))
         (erg (car bounds)))
    (when erg (goto-char erg))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defalias 'py-forward-of-declarations 'py-end-of-declarations)
(defun py-end-of-declarations ()
  "Got to the end of assigments resp. statements in current level which don't open blocks. "
  (interactive)
  (let* ((bounds (py-bounds-of-declarations))
         (erg (cdr bounds)))
    (when erg (goto-char erg))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defalias 'py-copy-declarations 'py-declarations)
(defun py-declarations ()
  "Copy and mark assigments resp. statements in current level which don't open blocks or start with a keyword.

See also `py-statements', which is more general, taking also simple statements starting with a keyword. "
  (interactive)
  (let* ((bounds (py-bounds-of-declarations))
         (beg (car bounds))
         (end (cdr bounds)))
    (when (and beg end)
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (kill-new (buffer-substring-no-properties beg end))
      (exchange-point-and-mark))))

(defun py-kill-declarations ()
  "Delete variables declared in current level.

Store deleted variables in kill-ring "
  (interactive "*")
  (let* ((bounds (py-bounds-of-declarations))
         (beg (car bounds))
         (end (cdr bounds)))
    (when (and beg end)
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (kill-new (buffer-substring-no-properties beg end))
      (delete-region beg end))))

;;; Statements
(defun py-bounds-of-statements ()
  "Bounds of consecutive multitude of statements around point.

Indented same level, which don't open blocks. "
  (interactive)
  (let* ((orig-indent (progn
                        (back-to-indentation)
                        (unless (py-beginning-of-statement-p)
                          (py-beginning-of-statement))
                        (unless (py-beginning-of-block-p)
                          (current-indentation))))
         (orig (point))
         last beg end)
    (when orig-indent
      (setq beg (point))
      (while (and (setq last beg)
                  (setq beg
                        (when (py-beginning-of-statement)
                          (line-beginning-position)))
                  (not (py-in-string-p))
                  (not (py-beginning-of-block-p))
                  (eq (current-indentation) orig-indent)))
      (setq beg last)
      (goto-char orig)
      (setq end (line-end-position))
      (while (and (setq last (line-end-position))
                  (setq end (py-down-statement))
                  (not (py-beginning-of-block-p))
                  ;; (not (looking-at py-keywords))
                  ;; (not (looking-at "pdb\."))
                  (not (py-in-string-p))
                  (eq (py-indentation-of-statement) orig-indent)))
      (setq end last)
      (goto-char orig)
      (if (and beg end)
          (progn
            (when (and py-verbose-p (interactive-p)) (message "%s %s" beg end))
            (cons beg end))
        (when (and py-verbose-p (interactive-p)) (message "%s" nil))
        nil))))

(defalias 'py-backward-statements 'py-beginning-of-statements)
(defun py-beginning-of-statements ()
  "Got to the beginning of statements in current level which don't open blocks. "
  (interactive)
  (let* ((bounds (py-bounds-of-statements))
         (erg (car bounds)))
    (when erg (goto-char erg))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defalias 'py-forward-of-statements 'py-end-of-statements)
(defun py-end-of-statements ()
  "Got to the end of statements in current level which don't open blocks. "
  (interactive)
  (let* ((bounds (py-bounds-of-statements))
         (erg (cdr bounds)))
    (when erg (goto-char erg))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defalias 'py-copy-statements 'py-statements)
(defun py-statements ()
  "Copy and mark simple statements in current level which don't open blocks.

More general than py-declarations, which would stop at keywords like a print-statement. "
  (interactive)
  (let* ((bounds (py-bounds-of-statements))
         (beg (car bounds))
         (end (cdr bounds)))
    (when (and beg end)
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (kill-new (buffer-substring-no-properties beg end))
      (exchange-point-and-mark))))

(defun py-kill-statements ()
  "Delete statements declared in current level.

Store deleted statements in kill-ring "
  (interactive "*")
  (let* ((bounds (py-bounds-of-statements))
         (beg (car bounds))
         (end (cdr bounds)))
    (when (and beg end)
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (kill-new (buffer-substring-no-properties beg end))
      (delete-region beg end))))

;;; Comments, Filling
(defun py-comment-region (beg end &optional arg)
  "Like `comment-region' but uses double hash (`#') comment starter."
  (interactive "r\nP")
  (let ((comment-start py-block-comment-prefix))
    (comment-region beg end arg)))

(defun py-join-words-wrapping (words separator line-prefix line-length)
  (let ((lines ())
        (current-line line-prefix))
    (while words
      (let* ((word (car words))
             (maybe-line (concat current-line word separator)))
        (if (> (length maybe-line) line-length)
            (setq lines (cons (substring current-line 0 -1) lines)
                  current-line (concat line-prefix word separator " "))
          (setq current-line (concat maybe-line " "))))
      (setq words (cdr words)))
    (setq lines (cons (substring
                       current-line 0 (- 0 (length separator) 1)) lines))
    (mapconcat 'identity (nreverse lines) "\n")))

(defun py-fill-comment (&optional justify)
  "Fill the comment paragraph at point"
  (let (;; Non-nil if the current line contains a comment.
        has-comment

        ;; If has-comment, the appropriate fill-prefix for the comment.
        comment-fill-prefix)

    ;; Figure out what kind of comment we are looking at.
    (save-excursion
      (beginning-of-line)
      (cond
       ;; A line with nothing but a comment on it?
       ((looking-at "[ \t]*#[# \t]*")
        (setq has-comment t
              comment-fill-prefix (buffer-substring (match-beginning 0)
                                                    (match-end 0))))

       ;; A line with some code, followed by a comment? Remember that the hash
       ;; which starts the comment shouldn't be part of a string or character.
       ((progn
          (while (not (looking-at "#\\|$"))
            (skip-chars-forward "^#\n\"'\\")
            (cond
             ((eq (char-after (point)) ?\\) (forward-char 2))
             ((memq (char-after (point)) '(?\" ?')) (forward-sexp 1))))
          (looking-at "#+[\t ]*"))
        (setq has-comment t)
        (setq comment-fill-prefix
              (concat (make-string (current-column) ? )
                      (buffer-substring (match-beginning 0) (match-end 0)))))))

    (if (not has-comment)
        (fill-paragraph justify)

      ;; Narrow to include only the comment, and then fill the region.
      (save-restriction
        (narrow-to-region

         ;; Find the first line we should include in the region to fill.
         (save-excursion
           (while (and (zerop (forward-line -1))
                       (looking-at "^[ \t]*#")))

           ;; We may have gone to far.  Go forward again.
           (or (looking-at "^[ \t]*#")
               (forward-line 1))
           (point))

         ;; Find the beginning of the first line past the region to fill.
         (save-excursion
           (while (progn (forward-line 1)
                         (looking-at "^[ \t]*#")))
           (point)))

        ;; Lines with only hashes on them can be paragraph boundaries.
        (let ((paragraph-start (concat paragraph-start "\\|[ \t#]*$"))
              (paragraph-separate (concat paragraph-separate "\\|[ \t#]*$"))
              (fill-prefix comment-fill-prefix))
          ;;(message "paragraph-start %S paragraph-separate %S"
          ;;paragraph-start paragraph-separate)
          (fill-paragraph justify))))
    t))

(defun py-fix-this-indent (indent)
  (unless (and (eq (current-indentation) (current-column))
               (eq (current-column) indent))
    (beginning-of-line)
    (indent-to-column indent)
    (delete-region
     (point)
     (progn (skip-chars-forward " \t") (point)))))

(defun py-fill-string (start &optional justify)
  "Fill the paragraph around (point) in the string starting at start"
  ;; basic strategy: narrow to the string and call the default
  ;; implementation
  (let (;; the start of the string's contents
        string-start
        ;; the end of the string's contents
        string-end
        ;; length of the string's delimiter
        delim-length
        ;; The string delimiter
        delim)

    (save-excursion
      (goto-char start)
      (if (looking-at "\\([urbURB]*\\(?:'''\\|\"\"\"\\|'\\|\"\\)\\)\\\\?\n?")
          (setq string-start (match-end 0)
                delim-length (- (match-end 1) (match-beginning 1))
                delim (buffer-substring-no-properties (match-beginning 1)
                                                      (match-end 1)))
        (error "The parameter start is not the beginning of a python string"))

      ;; if the string is the first token on a line and doesn't start with
      ;; a newline, fill as if the string starts at the beginning of the
      ;; line. this helps with one line docstrings
      (save-excursion
        (beginning-of-line)
        (and (/= (char-before string-start) ?\n)
             (looking-at (concat "[ \t]*" delim))
             (setq string-start (point))))

      ;; move until after end of string, then the end of the string's contents
      ;; is delim-length characters before that
      (forward-sexp)
      (setq string-end (- (point) delim-length)))

    ;; Narrow to the string's contents and fill the current paragraph
    (save-restriction
      (narrow-to-region string-start string-end)
      (let ((ends-with-newline (= (char-before (point-max)) ?\n)))
        (fill-paragraph justify)
        (if (and (not ends-with-newline)
                 (= (char-before (point-max)) ?\n))
            ;; the default fill-paragraph implementation has inserted a
            ;; newline at the end. Remove it again.
            (save-excursion
              (goto-char (point-max))
              (delete-char -1)))))

    ;; return t to indicate that we've done our work
    t))

(defun py-fill-paragraph (&optional justify)
  "Like \\[fill-paragraph], but handle Python comments and strings.

If any of the current line is a comment, fill the comment or the
paragraph of it that point is in, preserving the comment's indentation
and initial `#'s.
If point is inside a string, narrow to that string and fill.
"
  (interactive "P")
  (save-excursion
    (save-restriction
      (widen)
      (let ((pps
             (if (featurep 'xemacs)
                 (parse-partial-sexp (point-min) (point))
               (syntax-ppss))))
        (cond
         ;; inside a comment
         ((nth 4 pps)
          (py-fill-comment justify))
         ;; only whitespace before the comment start
         ((save-excursion (beginning-of-line) (looking-at "[ \t]*#"))
          (py-fill-comment justify))
         ;; inside a string
         ((nth 3 pps)
          (py-fill-string (nth 8 pps)))
         ;; opening quote of a string
         ((progn (save-excursion (forward-char 1)(nth 3 pps)))
          (save-excursion
            (forward-char 1)
            (py-fill-string (nth 8 pps)))))))))

(defun py-insert-super ()
  "Insert a function \"super()\" from current environment.

As example given in Python v3.1 documentation » The Python Standard Library »

class C(B):
    def method(self, arg):
        super().method(arg) # This does the same thing as:
                               # super(C, self).method(arg)

Returns the string inserted. "
  (interactive "*")
  (let* ((orig (point))
         (funcname (progn
                     (py-beginning-of-def)
                     (when (looking-at (concat py-def-re " *\\([^(]+\\) *(\\(?:[^),]*\\),? *\\([^)]*\\))"))
                       (match-string-no-properties 2))))
         (args (match-string-no-properties 3))
         (ver (py-which-python))
         classname erg)
    (if (< ver 3)
        (progn
          (py-beginning-of-class)
          (when (looking-at (concat py-class-re " *\\([^( ]+\\)"))
            (setq classname (match-string-no-properties 2)))
          (goto-char orig)
          (setq erg (concat "super(" classname ", self)." funcname "(" args ")"))
          ;; super(C, self).method(arg)"
          (insert erg))
      (goto-char orig)
      (setq erg (concat "super()." funcname "(" args ")"))
      (insert erg))
    erg))

(defun py-nesting-level (&optional pps)
  "Accepts the output of `parse-partial-sexp'. "
  (interactive)
  (let* ((pps (or (ignore-errors (nth 0 pps))
                  (if (featurep 'xemacs)
                      (parse-partial-sexp (point-min) (point))
                    (syntax-ppss))))
         (erg (nth 0 pps)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defalias 'py-count-indentation 'py-compute-indentation)
(defun py-compute-indentation (&optional orig origline closing line inside repeat)
  "Compute Python indentation.

When HONOR-BLOCK-CLOSE-P is non-nil, statements such as `return',
`raise', `break', `continue', and `pass' force one level of dedenting."
  (interactive "P")
  (save-excursion
    (save-restriction
      (widen)
      (let* ((orig (or orig (point)))
             (origline (or origline (py-count-lines)))
             ;; closing indicates: when started, looked
             ;; at a single closing parenthesis
             (closing closing)
             ;; line: moved already a line backward
             (line line)
             (pps (syntax-ppss))
             ;; in a recursive call already
             (repeat repeat)
             ;; inside: started inside a list
             (inside inside)
             erg indent this-line)
        (unless repeat (setq inside (nth 1 pps))
                (setq repeat t))
        (setq indent
              (cond
               ((and (bobp)
                     (eq origline (py-count-lines)))
                (current-indentation))
               ((and (bobp)(py-statement-opens-block-p))
                (+ (if py-smart-indentation (py-guess-indent-offset nil orig origline) py-indent-offset) (current-indentation)))
               ((and (bobp)(not (py-statement-opens-block-p)))
                (current-indentation))
               ;; (py-in-triplequoted-string-p)
               ((and (nth 3 pps)(nth 8 pps))
                (if (eq origline (py-count-lines))
                    (progn
                      (forward-line -1)
                      (end-of-line)
                      (skip-chars-backward " \t\r\n\f")
                      (if (ignore-errors (< (nth 2 (syntax-ppss)) (line-beginning-position)))
                          (current-indentation)
                        (ignore-errors (goto-char (nth 2 pps)))
                        (py-line-backward-maybe)
                        (back-to-indentation)
                        (py-compute-indentation orig origline closing line inside repeat)))
                  (current-indentation)))
               ((and (looking-at "\"\"\"\\|'''")(not (bobp)))
                (py-beginning-of-statement)
                (py-compute-indentation orig origline closing line inside repeat))
               ;; comments
               ((nth 8 pps)
                (if (eq origline (py-count-lines))
                    (progn
                      (goto-char (nth 8 pps))
                      (py-line-backward-maybe)
                      (skip-chars-backward " \t")
                      (py-compute-indentation orig origline closing line inside repeat))
                  (goto-char (nth 8 pps))
                  (if (and line (or py-indent-honors-inline-comment (looking-back "^[ \t]*")))
                      (current-column)
                    (forward-char -1)
                    (py-compute-indentation orig origline closing line inside repeat))))
               ((and (looking-at "[ \t]*#") (looking-back "^[ \t]*")(not py-indent-comments)(eq origline (py-count-lines)))
                0)
               ((and (looking-at "[ \t]*#") (looking-back "^[ \t]*")(not (eq (line-beginning-position) (point-min))))
                (forward-line -1)
                (end-of-line)
                (setq line t)
                (py-compute-indentation orig origline closing line inside repeat))
               ;; lists
               ((nth 1 pps)
                (cond ((and inside (not line))
                       (when (and (eq (point) orig) (looking-at "[ \t]*\\()\\)[ \t]*$"))
                         (setq closing (match-beginning 0)))
                       (save-excursion
                         (goto-char (nth 1 pps))
                         (setq this-line (py-count-lines))
                         (cond
                          ((< 0 (- origline this-line))
                           (if (< 1 (- origline this-line))
                               (if closing
                                   (if py-closing-list-dedents-bos
                                       (current-indentation)
                                     (+ (current-indentation) py-indent-offset))
                                 (py-fetch-previous-indent orig))
                             (cond ((looking-at "\\s([ \t]*$")
                                    (if
                                        (progn
                                          (save-excursion
                                            (back-to-indentation)
                                            (looking-at py-block-or-clause-re)))
                                        (progn
                                          (back-to-indentation)
                                          (+ (current-column) (* 2 py-indent-offset)))
                                      (back-to-indentation)
                                      (+ (current-column) py-indent-offset)))
                                   ((looking-at "\\s([ \t]*\\([^ \t]+.*\\)$")
                                    (goto-char (match-beginning 1))
                                    (current-column))
                                   (t (+ (current-column) (* (nth 0 pps)))))))
                          (t (back-to-indentation)
                             (py-beginning-of-statement)
                             (py-compute-indentation orig origline closing line inside repeat)))))
                      ((and (not inside) line)
                       (py-beginning-of-statement)
                       (py-compute-indentation orig origline closing line inside repeat))
                      ((not inside)
                       (progn (goto-char (+ py-lhs-inbound-indent (nth 1 pps)))
                              (when (looking-at "[ \t]+")
                                (goto-char (match-end 0)))
                              (current-column)))
                      (t
                       (goto-char (nth 1 pps))
                       (py-compute-indentation orig origline closing line inside repeat))))
               ((py-preceding-line-backslashed-p)
                (progn
                  (py-beginning-of-statement)
                  (setq this-line (py-count-lines))
                  (if (< 1 (- origline this-line))
                      (py-fetch-previous-indent orig)
                    (if (looking-at "from +\\([^ \t\n]+\\) +import")
                        5
                      (+ (current-indentation) py-continuation-offset)))))
               ((looking-at py-no-outdent-re)
                (if (eq (py-count-lines) origline)
                    (progn
                      (back-to-indentation)
                      (py-line-backward-maybe)
                      (py-compute-indentation orig origline closing line inside repeat))
                  (current-indentation)))
               ((and (looking-at py-block-closing-keywords-re)(eq (py-count-lines) origline))
                (py-beginning-of-block-or-clause)
                (+
                 (if py-smart-indentation (py-guess-indent-offset nil orig origline) py-indent-offset)
                 ;; py-indent-offset
                 (current-indentation)))
               ((looking-at py-block-closing-keywords-re)
                (py-beginning-of-block-or-clause (current-indentation))
                (current-indentation))
               ((and (looking-at py-elif-re) (eq (py-count-lines) origline))
                (py-line-backward-maybe)
                (car (py-clause-lookup-keyword py-elif-re -1 nil orig origline)))
               ((and (looking-at py-clause-re)(eq origline (py-count-lines)))
                (cond ((looking-at py-finally-re)
                       (car (py-clause-lookup-keyword py-finally-re -1 nil orig origline)))
                      ((looking-at py-except-re)
                       (car (py-clause-lookup-keyword py-except-re -1 nil orig origline)))
                      ((looking-at py-else-re)
                       ;; (car (py-clause-lookup-keyword py-else-re -1 (current-indentation))))
                       (car (py-clause-lookup-keyword py-else-re -1 nil orig origline)))
                      ((looking-at py-elif-re)
                       (car (py-clause-lookup-keyword py-elif-re -1 nil orig origline)))
                      ;; maybe at if, try, with
                      (t (car (py-clause-lookup-keyword py-block-or-clause-re -1 nil orig origline)))))
               ((looking-at py-block-or-clause-re)
                (cond ((eq origline (py-count-lines))
                       (py-line-backward-maybe)
                       (py-compute-indentation orig origline closing line inside t))
                      (t (+ (if py-smart-indentation (py-guess-indent-offset nil orig origline) py-indent-offset)(current-indentation)))))
               ((looking-at py-block-closing-keywords-re)
                (py-beginning-of-block)
                (current-indentation))
               ((and (< (current-indentation) (current-column)))
                (back-to-indentation)
                (unless line
                  (setq inside (nth 1 (syntax-ppss))))
                (py-compute-indentation orig origline closing line inside repeat))
               ((not (py-beginning-of-statement-p))
                (if (bobp)
                    (current-column)
                  (if (eq (point) orig)
                      (progn
                        (py-line-backward-maybe)
                        (py-compute-indentation orig origline closing line inside repeat))
                    (py-beginning-of-statement)
                    (py-compute-indentation orig origline closing line inside repeat))))
               ((py-statement-opens-block-p)
                (if (< (py-count-lines) origline)
                    (+ (if py-smart-indentation (py-guess-indent-offset nil orig origline) py-indent-offset) (current-indentation))
                  (py-compute-indentation orig origline closing line inside t)))
               ((and (< (py-count-lines) origline)(looking-at py-assignment-re))
                (current-indentation))
               ((looking-at py-assignment-re)
                (py-beginning-of-statement)
                (py-compute-indentation orig origline closing line inside repeat))
               ((and (eq origline (py-count-lines))
                     (save-excursion (and (setq erg (py-go-to-keyword py-block-or-clause-re))
                                          (ignore-errors (< orig (py-end-of-block-or-clause))))))
                (+ (car erg) (if py-smart-indentation (py-guess-indent-offset nil orig origline) py-indent-offset)))
               ((and (eq origline (py-count-lines))
                     (py-beginning-of-statement-p))
                (py-beginning-of-statement)
                (py-compute-indentation orig origline closing line inside repeat))
               (t (current-indentation))))
        (when (and py-verbose-p (interactive-p)) (message "%s" indent))
        indent))))

(defun py-line-backward-maybe ()
  (skip-chars-backward " \t\f" (line-beginning-position))
  (when (< 0 (abs (skip-chars-backward " \t\r\n\f")))
    (setq line t)))

(defun py-fetch-previous-indent (orig)
  "Report the preceding indent. "
  (save-excursion
    (goto-char orig)
    (forward-line -1)
    (end-of-line)
    (skip-chars-backward " \t\r\n\f")
    (current-indentation)))

(defun py-continuation-offset (&optional arg)
  "With numeric ARG different from 1 py-continuation-offset is set to that value; returns py-continuation-offset. "
  (interactive "p")
  (let ((erg (if (eq 1 arg)
                 py-continuation-offset
               (when (numberp arg)
                 (prog1
                     arg
                   (setq py-continuation-offset arg))))))
    (when (and py-verbose-p (interactive-p)) (message "%s" py-continuation-offset))
    py-continuation-offset))

(defalias 'pios 'py-indentation-of-statement)
(defalias 'ios 'py-indentation-of-statement)
(defun py-indentation-of-statement ()
  "Returns the indenation of the statement at point. "
  (interactive)
  (let ((erg (save-excursion
               (back-to-indentation)
               (or (py-beginning-of-statement-p)
                   (py-beginning-of-statement))
               (current-indentation))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defalias 'py-in-list-p 'py-list-beginning-position)
(defun py-list-beginning-position (&optional start)
  "Return lists beginning position, nil if not inside.

Optional ARG indicates a start-position for `parse-partial-sexp'."
  (interactive)
  (let* ((ppstart (or start (point-min)))
         (erg (nth 1 (syntax-ppss))))
    (when (interactive-p) (message "%s" erg))
    erg))

(defun py-end-of-list-position (&optional arg)
  "Return end position, nil if not inside.

Optional ARG indicates a start-position for `parse-partial-sexp'."
  (interactive)
  (let* ((ppstart (or arg (point-min)))
         (erg (syntax-ppss))
         (beg (nth 1 erg))
         end)
    (when beg
      (save-excursion
        (goto-char beg)
        (forward-list 1)
        (setq end (point))))
    (when (and py-verbose-p (interactive-p)) (message "%s" end))
    end))

(defun py-in-comment-p ()
  "Return the beginning of current line's comment, if inside. "
  (save-restriction
    (widen)
    (let* ((pps (syntax-ppss))
           (erg (when (nth 4 pps) (nth 8 pps))))
      (unless erg
        (when (looking-at (concat "^[ \t]*" comment-start-skip))
          (setq erg (point))))
      erg)))

(defun py-in-triplequoted-string-p ()
  "Returns character address of start tqs-string, nil if not inside. "
  (interactive)
  (let* ((pps (syntax-ppss))
         (erg (when (and (nth 3 pps) (nth 8 pps))(nth 2 pps))))
    (save-excursion
      (unless erg (setq erg
                        (progn
                          (when (looking-at "\"\"\"\\|''''")
                            (goto-char (match-end 0))
                            (setq pps (syntax-ppss))
                            (when (and (nth 3 pps) (nth 8 pps)) (nth 2 pps)))))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-in-string-p ()
  "Returns character address of start of string, nil if not inside. "
  (interactive)
  (let* ((pps (syntax-ppss))
         (erg (when (nth 3 pps) (nth 8 pps))))
    (save-excursion
      (unless erg (setq erg
                        (progn
                          (when (looking-at "\"\\|'")
                            (forward-char 1)
                            (setq pps (syntax-ppss))
                            (when (nth 3 pps) (nth 8 pps)))))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-in-statement-p ()
  "Returns list of beginning and end-position if inside.

Result is useful for booleans too: (when (py-in-statement-p)...)
will work.
"
  (interactive)
  (let ((orig (point))
        beg end erg)
    (save-excursion
      (setq end (py-end-of-statement))
      (setq beg (py-beginning-of-statement))
      (when (and (<= beg orig)(<= orig end))
        (setq erg (cons beg end))
        (when (and py-verbose-p (interactive-p)) (message "%s" erg))
        erg))))

;;; Beginning-of- p
(defun py-beginning-of-line-p ()
  "Returns position, if cursor is at the beginning of a line, nil otherwise. "
  (when (bolp)(point)))

(defun py-beginning-of-buffer-p ()
  "Returns position, if cursor is at the beginning of buffer, nil otherwise. "
  (when (bobp)(point)))

(defun py-beginning-of-paragraph-p ()
  "Returns position, if cursor is at the beginning of a paragraph, nil otherwise. "
  (let ((orig (point))
        erg)
    (if (and (bolp) (looking-at paragraph-separate))
        (setq erg (point))
      (save-excursion
        (py-end-of-paragraph)
        (py-beginning-of-paragraph)
        (when (eq orig (point))
          (setq erg orig)))
      erg)))

(defun py-beginning-of-statement-p ()
  "Returns position, if cursor is at the beginning of a statement, nil otherwise. "
  (let ((orig (point))
        erg)
    (save-excursion
      (py-end-of-statement)
      (py-beginning-of-statement)
      (when (eq orig (point))
        (setq erg orig))
      erg)))

(defun py-beginning-of-expression-p ()
  "Returns position, if cursor is at the beginning of a expression, nil otherwise. "
  (let ((orig (point))
        erg)
    (save-excursion
      (py-end-of-expression)
      (py-beginning-of-expression)
      (when (eq orig (point))
        (setq erg orig))
      erg)))

(defun py-beginning-of-partial-expression-p ()
  "Returns position, if cursor is at the beginning of a partial-expression, nil otherwise. "
  (let ((orig (point))
        erg)
    (save-excursion
      (py-end-of-partial-expression)
      (py-beginning-of-partial-expression)
      (when (eq orig (point))
        (setq erg orig))
      erg)))

(defun py-beginning-of-block-p ()
  "Returns position, if cursor is at the beginning of a block, nil otherwise. "
  (when (and (looking-at py-block-re)
             (not (py-in-string-or-comment-p)))
    (point)))

(defun py-beginning-of-clause-p ()
  "Returns position, if cursor is at the beginning of a clause, nil otherwise. "
  (when (and (looking-at py-clause-re)
             (not (py-in-string-or-comment-p)))
    (point)))

(defun py-beginning-of-block-or-clause-p ()
  "Returns position, if cursor is at the beginning of a block-or-clause, nil otherwise. "
  (when (and (looking-at py-block-or-clause-re)
             (not (py-in-string-or-comment-p)))
    (point)))

(defun py-beginning-of-def-p ()
  "Returns position, if cursor is at the beginning of a def, nil otherwise. "
  (when (and (looking-at py-def-re)
             (not (py-in-string-or-comment-p)))
    (point)))

(defun py-beginning-of-class-p ()
  "Returns position, if cursor is at the beginning of a class, nil otherwise. "
  (when (and (looking-at py-class-re)
             (not (py-in-string-or-comment-p)))
    (point)))

(defun py-beginning-of-def-or-class-p ()
  "Returns position, if cursor is at the beginning of a def-or-class, nil otherwise. "
  (when (and (looking-at py-def-or-class-re)
             (not (py-in-string-or-comment-p)))
    (point)))

;;; Opens- p
(defun py-statement-opens-block-p (&optional regexp)
  "Return position if the current statement opens a block
in stricter or wider sense.

For stricter sense specify regexp. "
  (interactive)
  (let* ((regexp (or regexp py-block-re))
         (erg (py-statement-opens-base regexp)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-statement-opens-base (regexp)
  (let ((orig (point))
        erg)
    (save-excursion
      (back-to-indentation)
      (py-end-of-statement)
      (py-beginning-of-statement)
      (when (and
             (looking-back "^[ \t]*") (<= (line-beginning-position)(point))(looking-at regexp))
        (setq erg (point))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-statement-opens-clause-p ()
  "Return position if the current statement opens block or clause. "
  (interactive)
  (py-statement-opens-base py-clause-re))

(defun py-statement-opens-block-or-clause-p ()
  "Return position if the current statement opens block or clause. "
  (interactive)
  (py-statement-opens-base py-block-or-clause-re))

(defun py-statement-opens-class-p ()
  "Return `t' if the statement opens a functions or class definition, nil otherwise. "
  (interactive)
  (py-statement-opens-base py-class-re))

(defun py-statement-opens-def-p ()
  "Return `t' if the statement opens a functions or class definition, nil otherwise. "
  (interactive)
  (py-statement-opens-base py-def-re))

(defun py-statement-opens-def-or-class-p ()
  "Return `t' if the statement opens a functions or class definition, nil otherwise. "
  (interactive)
  (py-statement-opens-base py-def-or-class-re))

(defun py-statement-closes-block-p ()
  "Return t iff the current statement closes a block.
I.e., if the line starts with `return', `raise', `break', `continue',
and `pass'.  This doesn't catch embedded statements."
  (let ((here (point)))
    (unless (py-beginning-of-statement-p) (py-beginning-of-statement))
    (prog1
        (looking-at py-block-closing-keywords-re)
      (goto-char here))))

(defun py-end-base (regexp &optional orig)
  "Used internal by functions going to the end forms. "
  (let ((orig (or orig (point)))
        (erg (if (py-statement-opens-block-p regexp)
                 (point)
               (py-go-to-keyword regexp)
               (when (py-statement-opens-block-p regexp)
                 (point))))
        ind)
    (if erg
        (progn
          (setq ind (+ py-indent-offset (current-indentation)))
          (py-end-of-statement)
          (forward-line 1)
          (setq erg (py-travel-current-indent ind)))
      (py-look-downward-for-beginning regexp)
      (unless (eobp)(py-end-base regexp orig)))
    (if (< orig (point))
        (setq erg (point))
      (setq erg (py-look-downward-for-beginning regexp))
      (when erg (py-end-base regexp orig)))
    erg))

(defun py-look-downward-for-beginning (regexp)
  "When above any beginning of FORM, search downward. "
  (let ((erg (re-search-forward regexp nil (quote move) 1)))
    (if (and erg (not (py-in-string-or-comment-p))
             (not (py-in-list-p)))
        erg
      (unless (eobp)
        (py-look-downward-for-beginning regexp)))))

(defun py-current-defun (&optional iact)
  "Go to the outermost method or class definition in current scope.

Python value for `add-log-current-defun-function'.
This tells add-log.el how to find the current function/method/variable.
Returns name of class or methods definition, if found, nil otherwise.

See customizable variables `py-current-defun-show' and `py-current-defun-delay'."
  (interactive "p")
  (save-restriction
    (widen)
    (save-excursion
      (let ((erg (when (py-beginning-of-def-or-class)
                   (forward-word 1)
                   (skip-chars-forward " \t")
                   (prin1-to-string (symbol-at-point)))))
        (when (and erg py-current-defun-show (push-mark (point) t t) (skip-chars-forward "^ (")
                   (exchange-point-and-mark)
                   (sit-for py-current-defun-delay)))
        (when iact (message (prin1-to-string erg)))
        erg))))

(defun py-outdent-p ()
  "Returns non-nil if the current line should dedent one level."
  (save-excursion
    (and (progn (back-to-indentation)
                (looking-at py-clause-re))
         ;; short circuit infloop on illegal construct
         (not (bobp))
         (progn (forward-line -1)
                (py-beginning-of-statement)
                (back-to-indentation)
                (when (looking-at py-blank-or-comment-re)
                  (backward-to-indentation 1))
                (not (looking-at py-no-outdent-re))))))

(defun py-sort-imports ()
  "Sort multiline imports.

Put point inside the parentheses of a multiline import and hit
\\[py-sort-imports] to sort the imports lexicographically"
  (interactive)
  (save-excursion
    (let ((open-paren (save-excursion (progn (up-list -1) (point))))
          (close-paren (save-excursion (progn (up-list 1) (point))))
          sorted-imports)
      (goto-char (1+ open-paren))
      (skip-chars-forward " \n\t")
      (setq sorted-imports
            (sort
             (delete-dups
              (split-string (buffer-substring
                             (point)
                             (save-excursion (goto-char (1- close-paren))
                                             (skip-chars-backward " \n\t")
                                             (point)))
                            ", *\\(\n *\\)?"))
             ;; XXX Should this sort case insensitively?
             'string-lessp))
      ;; Remove empty strings.
      (delete-region open-paren close-paren)
      (goto-char open-paren)
      (insert "(\n")
      (insert (py-join-words-wrapping (remove "" sorted-imports) "," "    " 78))
      (insert ")"))))

(defun py-in-literal (&optional lim)
  "Return non-nil if point is in a Python literal (a comment or string).
Optional argument LIM indicates the beginning of the containing form,
i.e. the limit on how far back to scan."
  (let* ((lim (or lim (point-min)))
         (state (syntax-ppss)))
    (cond
     ((nth 3 state) 'string)
     ((nth 4 state) 'comment))))

(defun py-which-function ()
  "Return the name of the function or class, if curser is in, return nil otherwise. "
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (let ((orig (point))
            (erg (if (and (looking-at (concat py-def-or-class-re " +\\([^(]+\\)(.+")) (not (py-in-string-or-comment-p)))
                     (match-string-no-properties 2)
                   (progn
                     (py-beginning-of-def-or-class)
                     (when (looking-at (concat py-def-or-class-re " +\\([^(]+\\)(.+"))
                       (match-string-no-properties 2))))))
        (if (and erg (< orig (py-end-of-def-or-class)))
            (when (and py-verbose-p (interactive-p)) (message "%s" erg))
          (setq erg nil)
          (when (and py-verbose-p (interactive-p)) (message "%s" "Not inside a function or class"))
          erg)))))

(defconst py-help-address "python-mode@python.org"
  "List dealing with usage and developing python-mode.

Also accepts submission of bug reports, whilst a ticket at
http://launchpad.net/python-mode
is preferable for that. ")

;;; Beg-end forms
(defun py-beginning-of-block (&optional indent)
  "Returns beginning of block if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-block-re indent)))))
    erg))

(defun py-end-of-block ()
  "Go to the end of block.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let* ((orig (point))
         (erg (py-end-base py-block-re orig)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-beginning-of-clause (&optional indent)
  "Returns beginning of clause if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-clause-re indent)))))
    erg))

(defun py-end-of-clause ()
  "Go to the end of clause.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let* ((orig (point))
         (erg (py-end-base py-clause-re orig)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-beginning-of-block-or-clause (&optional indent)
  "Returns beginning of block-or-clause if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-block-or-clause-re indent)))))
    erg))

(defun py-end-of-block-or-clause ()
  "Go to the end of block-or-clause.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let* ((orig (point))
         (erg (py-end-base py-block-or-clause-re orig)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-beginning-of-def (&optional indent)
  "Returns beginning of def if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-def-re indent)))))
    erg))

(defun py-end-of-def ()
  "Go to the end of def.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let* ((orig (point))
         (erg (py-end-base py-def-re orig)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-beginning-of-class (&optional indent)
  "Returns beginning of class if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-class-re indent)))))
    erg))

(defun py-end-of-class ()
  "Go to the end of class.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let* ((orig (point))
         (erg (py-end-base py-class-re orig)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-beginning-of-def-or-class (&optional indent)
  "Returns beginning of def-or-class if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-def-or-class-re indent)))))
    erg))

(defun py-end-of-def-or-class ()
  "Go to the end of def-or-class.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (save-restriction
    (widen)
    (let* ((orig (point))
           (pps (syntax-ppss))
           ;; (origline (py-count-lines))
           (erg (if (and (not (nth 8 pps)) (looking-at py-def-or-class-re))
                    (point)
                  (py-go-to-keyword py-def-or-class-re)
                  (when (and (not (nth 8 pps)) (looking-at py-def-or-class-re)) (point))))
           ind)
      (if erg
          (progn
            (setq ind
                  (+ (if py-smart-indentation
                         (save-excursion
                           (goto-char orig)
                           ;; (setq origline (py-count-lines))
                           (py-end-of-statement)
                           (py-end-of-statement)
                           ;; (when (eq origline (py-count-lines)) (py-end-of-statement))
                           (py-guess-indent-offset nil (point)))
                       py-indent-offset)
                     (current-indentation)))
            (py-end-of-statement)
            (forward-line 1)
            (setq erg (py-travel-current-indent ind)))
        (py-look-downward-for-beginning py-def-or-class-re)
        (unless (eobp)
          ;; (py-end-base py-def-or-class-re orig)
          (progn
            (setq ind
                  (+ (if py-smart-indentation
                         (save-excursion
                           (goto-char orig)
                           ;; (setq origline (py-count-lines))
                           (py-end-of-statement)
                           (py-end-of-statement)
                           ;; (when (eq origline (py-count-lines)) (py-end-of-statement))
                           (py-guess-indent-offset nil (point)))
                       py-indent-offset)
                     (current-indentation)))
            (py-end-of-statement)
            (forward-line 1)
            (setq erg (py-travel-current-indent ind)))
          ))
      (if (< orig (point))
          (setq erg (point))
        (setq erg (py-look-downward-for-beginning py-def-or-class-re))
        (when erg
          (progn
            (setq ind (+ py-indent-offset (current-indentation)))
            (py-end-of-statement)
            (forward-line 1)
            (setq erg (py-travel-current-indent ind)))
          ;; (py-end-base py-def-or-class-re orig)
          ))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-beginning-of-if-block (&optional indent)
  "Returns beginning of if-block if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-if-re indent)))))
    erg))

(defun py-end-of-if-block ()
  "Go to the end of if-block.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let* ((orig (point))
         (erg (py-end-base py-if-re orig)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-beginning-of-try-block (&optional indent)
  "Returns beginning of try-block if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-try-block-re indent)))))
    erg))

(defun py-end-of-try-block ()
  "Go to the end of try-block.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let* ((orig (point))
         (erg (py-end-base py-try-block-re orig)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-beginning-of-minor-block (&optional indent)
  "Returns beginning of minor-block if successful, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let ((erg (ignore-errors (cdr (py-go-to-keyword py-minor-block-re indent)))))
    erg))

(defun py-end-of-minor-block ()
  "Go to the end of minor-block.

Returns position reached, if any, nil otherwise.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html"
  (interactive)
  (let* ((orig (point))
         (erg (py-end-base py-minor-block-re orig)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

;; Buffer
(defun py-beginning-of-buffer ()
  "Go to beginning-of-buffer, return position. "
  (let ((erg (unless (bobp)
               (goto-char (point-min)))))
    erg))

(defun py-end-of-buffer ()
  "Go to end-of-buffer, return position.

If already at end-of-buffer and not at EOB, go to end of next line. "
  (let ((erg (unless (eobp)
               (goto-char (point-max)))))
    erg))

(defalias 'py-forward-block 'py-end-of-block)
(defalias 'py-forward-block-or-clause 'py-end-of-block-or-clause)
(defalias 'py-forward-class 'py-end-of-class)
(defalias 'py-forward-clause 'py-end-of-clause)
(defalias 'end-of-def-or-class 'py-end-of-def-or-class)
(defalias 'py-forward-def-or-class 'py-end-of-def-or-class)
(defalias 'py-previous-block 'py-beginning-of-block)
(defalias 'py-goto-block-up 'py-beginning-of-block)
(defalias 'py-backward-block 'py-beginning-of-block)
(defalias 'py-previous-block-or-clause 'py-beginning-of-block-or-clause)
(defalias 'py-goto-block-or-clause-up 'py-beginning-of-block-or-clause)
(defalias 'py-backward-block-or-clause 'py-beginning-of-block-or-clause)
(defalias 'beginning-of-class 'py-beginning-of-class)
(defalias 'py-backward-class 'py-beginning-of-class)
(defalias 'py-previous-class 'py-beginning-of-class)
(defalias 'py-previous-clause 'py-beginning-of-clause)
(defalias 'py-goto-clause-up 'py-beginning-of-clause)
(defalias 'py-backward-clause 'py-beginning-of-clause)
(defalias 'py-backward-def-or-class 'py-beginning-of-def-or-class)
(defalias 'py-previous-def-or-class 'py-beginning-of-def-or-class)

;;; Expression
(defalias 'py-backward-expression 'py-beginning-of-expression)
(defun py-beginning-of-expression (&optional orig origline done erg)
  "Go to the beginning of a compound python expression.

A a compound python expression might be concatenated by \".\" operator, thus composed by minor python expressions.

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes.
"
  (interactive)
  (save-restriction
    (widen)
    (unless (bobp)
      (when (looking-at "\\(=\\|:\\|+\\|-\\|*\\|/\\|//\\|&\\|%\\||\\|\^\\|>>\\|<<\\)")
        (goto-char (1- (match-beginning 0)))
        (skip-chars-backward " \t\r\n\f")
        (forward-char -1))
      (when (looking-back "[\])}]")
        (forward-char -1))
      (let ((orig (or orig (point)))
            (cui (current-indentation))
            (origline (or origline (py-count-lines)))
            (pps (if (featurep 'xemacs)
                     (parse-partial-sexp (point-min) (point))
                   (syntax-ppss)))
            (done done)
            (erg erg))
        (cond
         ;; if in string
         ((and (nth 3 pps)(nth 8 pps)
               (goto-char (nth 8 pps)))
          (unless (looking-back "\\(=\\|:\\|+\\|-\\|*\\|/\\|//\\|&\\|%\\||\\|\^\\|>>\\|<<\\)[ \t]*")
            (goto-char (nth 2 pps))
            (setq erg (point))
            (setq done t))
          (py-beginning-of-expression orig origline done erg))
         ;; comments left, as strings are done
         ((nth 8 pps)
          (goto-char (1- (nth 8 pps)))
          (py-beginning-of-expression orig origline done erg))
         ((and (looking-at "[ \t]*#") (looking-back "^[ \t]*"))
          (forward-line -1)
          (unless (bobp)
            (end-of-line)
            (py-beginning-of-expression orig origline done erg)))
         ;; character address of start of innermost containing list; nil if none.
         ((nth 1 pps)
          (goto-char (nth 1 pps))
          (when
              (not (looking-back "[ \t]+"))
            (when (< 0 (abs (skip-chars-backward py-expression-skip-regexp)))
              (setq erg (point))
              (setq done t)))
          (py-beginning-of-expression orig origline done erg))
         ;; inside expression
         ((and (eq (point) orig) (not (bobp)) (looking-back py-expression-looking-regexp))
          (skip-chars-backward py-expression-skip-regexp)
          (setq erg (point))
          (setq done t)
          (py-beginning-of-expression orig origline done erg))
         ((looking-at py-expression-looking-regexp)
          (setq erg (point)))
         (t (unless (and (looking-at "[ \t]*#") (looking-back "^[ \t]*"))
              (setq erg (point)))))
        (when (and py-verbose-p (interactive-p)) (message "%s" erg))
        erg))))

(defun py-end-of-expression (&optional orig origline done)
  "Go to the end of a compound python expression.

A a compound python expression might be concatenated by \".\" operator, thus composed by minor python expressions.

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference

Operators however are left aside resp. limit py-expression designed for edit-purposes. "
  (interactive)
  (save-restriction
    (widen)
    (unless (eobp)
      (let*
          ((orig (or orig (point)))
           (origline (or origline (py-count-lines)))
           (pps (if (featurep 'xemacs)
                    (parse-partial-sexp (point-min) (point))
                  (syntax-ppss)))
           (done done)
           erg
           ;; use by scan-lists
           parse-sexp-ignore-comments)
        (cond
         ((and (empty-line-p)(not done)(not (eobp)))
          (while
              (and (empty-line-p)(not done)(not (eobp)))
            (forward-line 1))
          (py-end-of-expression orig origline done))
         ;; inside string
         ((py-in-string-p)
          (when (looking-at "\"\"\"\\|'''\\|\"\\|'")
            (goto-char (match-end 0))
            (setq done t))
          ;; (re-search-forward "[^\\]\"\"\"\\|[^\\]'''\\|[^\\]\"\\|[^\\]'" nil (quote move) 1)
          (while
              (nth 3
                   (if (featurep 'xemacs)
                       (parse-partial-sexp (point-min) (point))
                     (syntax-ppss)))
            (setq done t)
            (forward-char 1))
          (py-end-of-expression orig origline done))
         ;; in comment
         ((nth 4 pps)
          (forward-line 1)
          (py-end-of-expression orig origline done))
         ((and (looking-at "[ \t]*#")(looking-back "^[ \t]*")(not done))
          (while (and (looking-at "[ \t]*#") (forward-line 1)(not (eobp))
                      (beginning-of-line)))
          (end-of-line)
          ;;          (setq done t)
          (skip-chars-backward " \t\r\n\f")
          (py-end-of-expression orig origline done))
         ;; start of innermost containing list; nil if none.
         ((nth 1 pps)
          (goto-char (nth 1 pps))
          (let ((parse-sexp-ignore-comments t))
            (forward-list)
            (py-end-of-expression orig origline done)))
         ((and (not done)(looking-at py-not-expression-regexp)(not (eobp)))
          (skip-chars-forward py-not-expression-regexp)
          (py-end-of-expression orig origline done))
         ((and (not done)(looking-at py-expression-skip-regexp)(not (eobp)))
          (skip-chars-forward py-not-expression-regexp)
          (forward-char -1)
          (py-end-of-expression orig origline done))
         ((and (looking-at py-expression-looking-regexp)(not (eobp)))
          (forward-char 1)
          (setq done (< 0 (skip-chars-forward py-expression-skip-regexp)))
          (when done (forward-char -1))
          (setq done t)
          (py-end-of-expression orig origline done)))
        (unless (eq (point) orig)
          (setq erg (point)))
        (when (and py-verbose-p (interactive-p)) (message "%s" erg))
        erg))))

;;; Partial- or Minor Expression
(defalias 'py-backward-partial-expression 'py-beginning-of-partial-expression)
(defun py-beginning-of-partial-expression (&optional orig origline done erg)
  "Go to the beginning of a minor python expression.

\".\" operators delimit a minor expression on their level.
Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes. "
  (interactive)
  (save-restriction
    (widen)
    (unless (bobp)
      (when (looking-at "\\(=\\|:\\|+\\|-\\|*\\|/\\|//\\|&\\|%\\||\\|\^\\|>>\\|<<\\)")
        (goto-char (1- (match-beginning 0)))
        (skip-chars-backward " \t\r\n\f")
        (forward-char -1))
      (let ((orig (or orig (point)))
            (cui (current-indentation))
            (origline (or origline (py-count-lines)))
            (pps (if (featurep 'xemacs)
                     (parse-partial-sexp (point-min) (point))
                   (syntax-ppss)))
            (done done)
            (erg erg))
        (cond
         ;; if in string
         ((and (nth 3 pps)(nth 8 pps)
               (save-excursion
                 (ignore-errors
                   (goto-char (nth 2 pps)))))
          (goto-char (nth 2 pps))
          (setq erg (point))
          (setq done t)
          (py-beginning-of-partial-expression orig origline done erg))
         ((nth 8 pps)
          (goto-char (1- (nth 8 pps)))
          (setq erg (point))
          (py-beginning-of-partial-expression orig origline done erg))
         ((and (looking-at "[ \t]*#") (looking-back "^[ \t]*"))
          (forward-line -1)
          (unless (bobp)
            (end-of-line)
            (setq erg (point))
            (setq done t)
            (py-beginning-of-partial-expression orig origline done erg)))
         ((nth 1 pps)
          (skip-chars-backward py-partial-expression-backward-regexp)
          (setq erg (point)))
         ((and (eq (point) orig) (not (bobp)) (looking-back py-partial-expression-looking-regexp))
          (forward-char -1)
          (when (< 0 (abs (skip-chars-backward py-partial-expression-skip-regexp)))
            (setq erg (point))
            (setq done t))
          (py-beginning-of-partial-expression orig origline done erg))
         ((looking-at py-partial-expression-looking-regexp)
          (setq erg (point)))
         (t (unless (and (looking-at "[ \t]*#") (looking-back "^[ \t]*"))(setq erg (point)))))
        (when (and py-verbose-p (interactive-p)) (message "%s" erg))
        erg))))

(defalias 'py-forward-partial-expression 'py-end-of-partial-expression)
(defun py-end-of-partial-expression (&optional orig origline done)
  "Go to the end of a minor python expression.

\".\" operators delimit a minor expression on their level.
Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes. "
  (interactive)
  (save-restriction
    (widen)
    (unless (eobp)
      (let*
          ((orig (or orig (point)))
           (origline (or origline (py-count-lines)))
           (pps (if (featurep 'xemacs)
                    (parse-partial-sexp (point-min) (point))
                  (syntax-ppss)))
           (done done)
           erg
           ;; use by scan-lists
           parse-sexp-ignore-comments)
        (cond
         ((and (empty-line-p)(not done)(not (eobp)))
          (while
              (and (empty-line-p)(not done)(not (eobp)))
            (forward-line 1))
          (py-end-of-partial-expression orig origline done))
         ;; inside string
         ((nth 3 pps)
          (when (looking-at "\"\"\"\\|'''\\|\"\\|'")
            (goto-char (match-end 0)))
          (while
              (and (re-search-forward "[^\\]\"\"\"\\|[^\\]'''\\|[^\\]\"\\|[^\\]'" nil (quote move) 1)
                   (nth 3
                        (if (featurep 'xemacs)
                            (parse-partial-sexp (point-min) (point))
                          (syntax-ppss)))))
          (py-end-of-partial-expression orig origline done))
         ;; in comment
         ((nth 4 pps)
          (forward-line 1)
          (py-end-of-partial-expression orig origline done))
         ((and (looking-at "[ \t]*#")(looking-back "^[ \t]*")(not done))
          (while (and (looking-at "[ \t]*#") (forward-line 1)(not (eobp))
                      (beginning-of-line)))
          (end-of-line)
          ;;          (setq done t)
          (skip-chars-backward " \t\r\n\f")
          (py-end-of-partial-expression orig origline done))
         ((and (nth 1 pps) (<= orig (nth 1 pps)))
          (goto-char (nth 1 pps))(forward-list)
          (point))
         ((and (not done)(ignore-errors (<= orig (nth 2 pps))))
          (goto-char (nth 2 pps))
          (setq done t)
          (skip-chars-forward py-partial-expression-forward-regexp)
          (py-end-of-partial-expression orig origline done))
         ((and (looking-at "\\.")(< orig (point)))
          (point))
         ((and (not done)(looking-at "\\.\\|=\\|:\\|+\\|-\\|*\\|/\\|//\\|&\\|%\\||\\|\^\\|>>\\|<<\\|<\\|<=\\|>\\|>=\\|==\\|!="))
          (goto-char (match-end 0))
          (when (< 0 (skip-chars-forward " \t\r\n\f"))
            (forward-char 1))
          (skip-chars-forward py-partial-expression-forward-regexp)
          (setq done t)
          (py-end-of-partial-expression orig origline done))
         ((and (not done)(looking-at py-partial-expression-looking-regexp)(not (eobp)))
          (skip-chars-forward py-partial-expression-forward-regexp)
          (setq done t)
          (py-end-of-partial-expression orig origline done))
         ((and (not done)(looking-at py-not-partial-expression-regexp)(not (eobp)))
          (skip-chars-forward py-not-partial-expression-skip-regexp)
          (skip-chars-forward py-partial-expression-forward-regexp)
          (setq done t)
          (py-end-of-partial-expression orig origline done))
         ((and (eq (point) orig) (not (eobp)))
          (forward-char 1)
          (py-end-of-partial-expression orig origline done)))
        (unless (eq (point) orig)
          (setq erg (point)))
        (when (and py-verbose-p (interactive-p)) (message "%s" erg))
        erg))))

;;; Line
(defun py-beginning-of-line ()
  "Go to beginning-of-line, return position.

If already at beginning-of-line and not at BOB, go to beginning of previous line. "
  (interactive)
  (let ((erg (unless (bobp)
               (if (bolp)
                   (progn
                     (forward-line -1)
                     (progn (beginning-of-line)(point)))
                 (progn (beginning-of-line)(point))))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-end-of-line ()
  "Go to end-of-line, return position.

If already at end-of-line and not at EOB, go to end of next line. "
  (interactive)
  (let ((erg (unless (eobp)
               (if (eolp)
                   (progn
                     (forward-line 1)
                     (progn (end-of-line)(point)))
                 (progn (end-of-line)(point))))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

;;; Statement
(defalias 'py-backward-statement 'py-beginning-of-statement)
(defalias 'py-previous-statement 'py-beginning-of-statement)
(defalias 'py-statement-backward 'py-beginning-of-statement)
(defun py-beginning-of-statement (&optional orig done)
  "Go to the initial line of a simple statement.

For beginning of compound statement use py-beginning-of-block.
For beginning of clause py-beginning-of-clause.

Referring python program structures see for example:
http://docs.python.org/reference/compound_stmts.html
"
  (interactive)
  (unless (bobp)
    (let ((orig (or orig (point)))
          (cui (current-indentation))
          (pps (syntax-ppss))
          (done done)
          erg)
      (cond
       ((nth 8 pps)
        (goto-char (1- (nth 8 pps)))
        (setq done t)
        (py-beginning-of-statement orig done))
       ((nth 1 pps)
        (goto-char (1- (nth 1 pps)))
        (setq done t)
        (py-beginning-of-statement orig done))
       ((and (not done) (not (eq 0 (skip-chars-backward " \t\r\n\f"))))
        (setq done t)
        (py-beginning-of-statement orig done))
       ((not (eq (current-column) (current-indentation)))
        (back-to-indentation)
        (setq done t)
        (py-beginning-of-statement orig done))
       ((looking-at "[ \t]*#")
        (skip-chars-backward " \t\r\n\f")
        (setq done t)
        (py-beginning-of-statement orig done))
       ((py-continuation-line-p)
        (forward-line -1)
        (setq done t)
        (py-beginning-of-statement orig done)))
      (unless (and (looking-at "[ \t]*#") (looking-back "^[ \t]*"))
        (when (< (point) orig)(setq erg (point))))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-go-to-keyword (regexp &optional maxindent)
  "Returns a list, whose car is indentation, cdr position. "
  (let ((orig (point))
        (origline (py-count-lines))
        (maxindent maxindent)
        done erg cui)
    (while (and (not done) (not (bobp)))
      (py-beginning-of-statement)
      (when (and (looking-at regexp)(if maxindent
                                        (< (current-indentation) maxindent)t))
        (setq erg (point))
        (setq done t)))
    (when erg (setq erg (cons (current-indentation) erg)))
    erg))

;; (defmacro py-go-to-keyword (regexp &optional maxindent)
;;   "Returns a list, whose car is indentation, cdr position. "
;;   `(let ((orig (point))
;;          (origline (py-count-lines))
;;          (maxindent maxindent)
;;          done erg)
;;      (while (and (not done) (not (bobp)))
;;        (py-beginning-of-statement)
;;        (when (and (looking-at ,regexp)(if maxindent
;;                                           (< (current-indentation) maxindent)t))
;;          (setq erg (point))
;;          (setq done t)))
;;      (when erg (cons (current-indentation) erg))))

(defalias 'py-statement-forward 'py-end-of-statement)
(defalias 'py-next-statement 'py-end-of-statement)
(defalias 'py-forward-statement 'py-end-of-statement)
(defun py-end-of-statement (&optional orig done)
  "Go to the last char of current statement.

To go just beyond the final line of the current statement, use `py-down-statement-lc'. "
  (interactive)
  (unless (eobp)
    (let ((pps (syntax-ppss))
          (orig (point))
          ;; use by scan-lists
          parse-sexp-ignore-comments erg)
      (cond
       ((and (not done) (< 0 (skip-chars-forward " \t\r\n\f")))
        (end-of-line)
        (py-beginning-of-comment)
        (skip-chars-backward " \t\r\n\f" (line-beginning-position))
        (if (eq (point) orig)
            (progn
              (end-of-line)
              (forward-comment 99999)
              (py-end-of-statement orig done))
          (setq done t)
          (py-end-of-statement orig done)))
       ((nth 1 pps)
        (when (< orig (point))
          (setq orig (point)))
        (goto-char (nth 1 pps))
        (let ((parse-sexp-ignore-comments t))
          (if (ignore-errors (forward-list))
              (progn
                (when (looking-at ":[ \t]*$")
                  (forward-char 1))
                (setq done t)
                (end-of-line)
                (skip-chars-backward " \t\r\n\f")
                (py-end-of-statement orig done))
            (goto-char orig))))
       ((and (nth 8 pps)(nth 4 pps))
        (cond
         ((nth 3 pps)
          (goto-char (nth 8 pps))
          (when (looking-at "\"\"\"\\|'''")
            (goto-char (match-end 0))
            (while (and (re-search-forward (match-string-no-properties 0) nil (quote move) 1)
                        (nth 3 (syntax-ppss))))
            (setq done t)
            (end-of-line)
            (skip-chars-backward " \t\r\n\f" (line-beginning-position))
            (py-end-of-statement orig done)))
         ;; in comment
         ((nth 4 pps)
          (if (eobp)
              nil
            (setq done t)
            (forward-comment 99999)
            (end-of-line)
            (skip-chars-backward " \t\r\n\f" (line-beginning-position))
            (py-beginning-of-comment)
            (skip-chars-backward " \t\r\n\f")
            (py-end-of-statement orig done)))))
       ((and (not done) (looking-at "#"))
        ;; (skip-chars-forward "#")
        (end-of-line)
        (forward-comment 99999)
        (setq done t)
        (end-of-line)
        (skip-chars-backward " \t\r\n\f")
        (py-beginning-of-comment)
        (skip-chars-backward " \t\r\n\f")
        (py-end-of-statement orig done))
       ((py-current-line-backslashed-p)
        (skip-chars-forward " \t\r\n\f")
        (end-of-line)
        (skip-chars-backward " \t\r\n\f")
        (py-beginning-of-comment)
        (skip-chars-backward " \t\r\n\f")
        (setq done t)
        (py-end-of-statement orig done))
       ((and (not done) (eq (point) orig))
        (end-of-line)
        (skip-chars-backward " \t\r\n\f")
        (py-beginning-of-comment)
        (skip-chars-backward " \t\r\n\f")
        (setq done t)
        (py-end-of-statement orig done)))
      (unless
          (or
           (eq (point) orig)
           (eq 0 (current-column)))
        (setq erg (point)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-goto-statement-below ()
  "Goto beginning of next statement. "
  (interactive)
  (let ((orig (point))
        (erg (py-end-of-statement)))
    (py-beginning-of-statement)
    (when (< (point) orig)
      (goto-char erg)
      (py-end-of-statement)
      (py-beginning-of-statement))))

;;; Mark forms
(defun py-mark-base (form &optional py-mark-decorators)
  (let* ((begform (intern-soft (concat "py-beginning-of-" form)))
         (endform (intern-soft (concat "py-end-of-" form)))
         (begcheckform (intern-soft (concat "py-beginning-of-" form "-p")))
         (orig (point))
         beg end erg)
    (setq beg (if
                  (setq beg (funcall begcheckform))
                  beg
                (funcall begform)))
    (when py-mark-decorators
      (save-excursion
        (when (setq erg (py-beginning-of-decorator))
          (setq beg erg))))
    (setq end (funcall endform))
    (push-mark beg t t)
    (unless end (when (< beg (point))
                  (setq end (point))))
    (when (interactive-p) (message "%s %s" beg end))
    (cons beg end)))

(defun py-mark-paragraph ()
  "Mark paragraph at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let (erg)
    (setq erg (py-mark-base "paragraph"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-block ()
  "Mark block at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let (erg)
    (setq erg (py-mark-base "block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-clause ()
  "Mark clause at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let (erg)
    (setq erg (py-mark-base "clause"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-block-or-clause ()
  "Mark block-or-clause at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let (erg)
    (setq erg (py-mark-base "block-or-clause"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-def (&optional arg)
  "Mark def at point.

With \\[universal argument] or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons. "
  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        erg)
    (py-mark-base "def" py-mark-decorators)
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-class (&optional arg)
  "Mark class at point.

With \\[universal argument] or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons. "
  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        erg)
    (py-mark-base "class" py-mark-decorators)
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-def-or-class (&optional arg)
  "Mark def-or-class at point.

With \\[universal argument] or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons. "
  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        erg)
    (py-mark-base "def-or-class" py-mark-decorators)
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-line ()
  "Mark line at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let (erg)
    (setq erg (py-mark-base "line"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-statement ()
  "Mark statement at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let (erg)
    (setq erg (py-mark-base "statement"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-expression ()
  "Mark expression at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let (erg)
    (setq erg (py-mark-base "expression"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-mark-partial-expression ()
  "Mark partial-expression at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let (erg)
    (setq erg (py-mark-base "partial-expression"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

;;; Decorator
(defun py-beginning-of-decorator ()
  "Go to the beginning of a decorator.

Returns position if succesful "
  (interactive)
  (back-to-indentation)
  (while (and (not (looking-at "@\\w+"))(not (empty-line-p))(not (bobp))(forward-line -1))
    (back-to-indentation))
  (let ((erg (when (looking-at "@\\w+")(match-beginning 0))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-end-of-decorator ()
  "Go to the end of a decorator.

Returns position if succesful "
  (interactive)
  (let ((orig (point)) erg)
    (unless (looking-at "@\\w+")
      (setq erg (py-beginning-of-decorator)))
    (when erg
      (if
          (re-search-forward py-def-or-class-re nil t)
          (progn
            (back-to-indentation)
            (skip-chars-backward " \t\r\n\f")
            (py-leave-comment-or-string-backward)
            (skip-chars-backward " \t\r\n\f")
            (setq erg (point)))
        (goto-char orig)
        (end-of-line)
        (skip-chars-backward " \t\r\n\f")
        (when (ignore-errors (goto-char (py-in-list-p)))
          (forward-list))
        (when (< orig (point))
          (setq erg (point))))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

;;; Copying
(defalias 'py-expression 'py-copy-expression)
(defun py-copy-expression ()
  "Mark expression at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let ((erg (py-mark-base "expression")))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defalias 'py-partial-expression 'py-copy-partial-expression)
(defun py-copy-partial-expression ()
  "Mark partial-expression at point.

Returns beginning and end positions of marked area, a cons.

\".\" operators delimit a partial-expression expression on it's level, that's the difference to compound expressions.

Given the function below, `py-partial-expression'
called at pipe symbol would copy and return:

def usage():
    print \"\"\"Usage: %s
    ....\"\"\" % (
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

\(
        os.path.basename(sys.argv[0]))

\;;;;;

Also for existing commands a shorthand is defined:

\(defalias 'py-statement 'py-copy-statement)"

  (interactive)
  (let ((erg (py-mark-base "partial-expression")))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))))

(defalias 'py-statement 'py-copy-statement)
(defun py-copy-statement ()
  "Mark statement at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let ((erg (py-mark-base "statement")))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))))

(defalias 'py-block 'py-copy-block)
(defun py-copy-block ()
  "Mark block at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let ((erg (py-mark-base "block")))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))))

(defalias 'py-block-or-clause 'py-copy-block-or-clause)
(defun py-copy-block-or-clause ()
  "Mark block-or-clause at point.

Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let ((erg (py-mark-base "block-or-clause")))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))))

(defalias 'py-def 'py-copy-def)
(defun py-copy-def (&optional arg)
  "Mark def at point.

With universal argument or `py-mark-decorators' set to `t' decorators are copied too.
Returns beginning and end positions of marked area, a cons."

  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        (erg (py-mark-base "def" py-mark-decorators)))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))))

(defun py-copy-def-or-class (&optional arg)
  "Mark def-or-class at point.

With universal argument or `py-mark-decorators' set to `t' decorators are copied too.
Returns beginning and end positions of marked area, a cons."
  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        (erg (py-mark-base "def-or-class" py-mark-decorators)))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))))

(defalias 'py-class 'py-copy-class)
(defun py-copy-class (&optional arg)
  "Mark class at point.

With universal argument or `py-mark-decorators' set to `t' decorators are copied too.
Returns beginning and end positions of marked area, a cons."

  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        (erg (py-mark-base "class" py-mark-decorators)))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))))

(defalias 'py-clause 'py-copy-clause)
(defun py-copy-clause ()
  "Mark clause at point.
  Returns beginning and end positions of marked area, a cons. "
  (interactive)
  (let ((erg (py-mark-base "clause")))
    (kill-new (buffer-substring-no-properties (car erg) (cdr erg)))))

;;; Deleting
(defun py-kill-expression ()
  "Delete expression at point.
  Stores data in kill ring. Might be yanked back using `C-y'. "
  (interactive)
  (let ((erg (py-mark-base "expression")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-partial-expression ()
  "Delete partial-expression at point.
  Stores data in kill ring. Might be yanked back using `C-y'.

\".\" operators delimit a partial-expression expression on it's level, that's the difference to compound expressions."
  (interactive)
  (let ((erg (py-mark-base "partial-expression")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-statement ()
  "Delete statement at point.

Stores data in kill ring. Might be yanked back using `C-y'. "
  (interactive "*")
  (let ((erg (py-mark-base "statement")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-block ()
  "Delete block at point.

Stores data in kill ring. Might be yanked back using `C-y'. "
  (interactive "*")
  (let ((erg (py-mark-base "block")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-block-or-clause ()
  "Delete block-or-clause at point.

Stores data in kill ring. Might be yanked back using `C-y'. "
  (interactive "*")
  (let ((erg (py-mark-base "block-or-clause")))
    (kill-region (region-beginning) (region-end))))

(defun py-kill-def-or-class ()
  "Delete def-or-class at point.

Stores data in kill ring. Might be yanked back using `C-y'. "
  (interactive "*")
  (let ((erg (py-mark-base "def-or-class")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-class ()
  "Delete class at point.

Stores data in kill ring. Might be yanked back using `C-y'. "
  (interactive "*")
  (let ((erg (py-mark-base "class")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-def ()
  "Delete def at point.

Stores data in kill ring. Might be yanked back using `C-y'. "
  (interactive "*")
  (let ((erg (py-mark-base "def")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-clause ()
  "Delete clause at point.

Stores data in kill ring. Might be yanked back using `C-y'. "
  (interactive "*")
  (let ((erg (py-mark-base "clause")))
    (kill-region (car erg) (cdr erg))))

;;; Helper functions
(defun py-forward-line (&optional arg)
  "Goes to end of line after forward move.

Travels right-margin comments. "
  (interactive "p")
  (let ((arg (or arg 1)))
    (forward-line arg)
    (end-of-line)
    (skip-chars-backward " \t")
    (py-beginning-of-comment)
    (skip-chars-backward " \t")))

(defun py-go-to-beginning-of-comment ()
  "Go to the beginning of current line's comment, if any.

From a programm use `py-beginning-of-comment' instead "
  (interactive)
  (let ((erg (py-beginning-of-comment)))
    (when (and py-verbose-p (interactive-p))
      (message "%s" erg))))

(defun py-beginning-of-comment ()
  "Go to the beginning of current line's comment, if any. "
  (save-restriction
    (widen)
    (let ((pps
           (if (featurep 'xemacs)
               (parse-partial-sexp (line-beginning-position) (point))
             (syntax-ppss))))
      (when (nth 4 pps)
        (goto-char
         (nth 8 pps))))))

(defun py-clause-lookup-keyword (regexp arg &optional indent orig origline)
  "Returns a list, whose car is indentation, cdr position. "
  (let* ((orig (or orig (point)))
         (origline (or origline (py-count-lines)))
         (stop (if (< 0 arg)'(eobp)'(bobp)))
         (function (if (< 0 arg) 'py-end-of-statement 'py-beginning-of-statement))
         (count 1)
         (maxindent (cond (indent indent)
                          ((< (py-count-lines) origline)
                           (current-indentation))
                          (t 0)))
         (complement-re
          (cond ((or (string-match "finally" regexp)
                     (string-match "except" regexp))
                 py-try-re)
                ((string-match "elif" regexp)
                 py-if-re)
                ((string-match "else" regexp)
                 py-minor-block-re)))
         (first t)
         erg done strict)
    (while (and (not (eval stop))
                (< 0 count)
                (or done (setq erg (funcall function))))
      (setq done nil)
      (when (and first (< maxindent (current-indentation)))
        (setq maxindent (current-indentation))
        (setq first nil))
      (when (if strict
                (< (current-indentation) maxindent)
              (<= (current-indentation) maxindent))
        (unless (looking-at py-block-or-clause-re)
          (setq maxindent (current-indentation)))
        ;; (message "%s %s" count indent)
        ;; nesting
        (cond
         ((and (looking-at "\\_<finally\\>[: \n\t]")(save-match-data (string-match regexp "finally")))
          (setq indent (current-indentation))
          (while
              (and
               (not (eval stop))
               (funcall function)
               (setq done t)
               (not (and (eq indent (current-indentation)) (looking-at "try"))))))
         ;; ((and (looking-at "\\<except\\>[: \n\t]")(save-match-data (string-match "else" regexp)))
         ;;  (setq indent (current-indentation))
         ;;  (setq count (1+ count))
         ;;  (while
         ;;      (and
         ;;       (not (eval stop))
         ;;       (funcall function)
         ;;       (setq done t)
         ;;       (not (and (eq indent (current-indentation)) (looking-at "try\\|if"))))))
         ((and (looking-at "\\<else\\>[: \n\t]")(save-match-data (string-match "else" regexp)))
          (setq indent (current-indentation))
          (setq count (1+ count))
          (while
              (and
               (not (eval stop))
               (funcall function)
               (setq done t)
               (not (and (eq indent (current-indentation)) (looking-at "try\\|if"))))))
         ((and (looking-at "\\_<else\\>[: \n\t]")(save-match-data (string-match "else" regexp)))
          (setq indent (current-indentation))
          (setq count (1+ count))
          (while
              (and
               (not (eval stop))
               (funcall function)
               (setq done t)
               (not (and (eq indent (current-indentation)) (looking-at "try\\|if"))))))
         ((and (looking-at "\\_<elif\\>[ \n\t]")(save-match-data (string-match "elif" regexp)))
          (setq indent (current-indentation))
          (while
              (and
               (not (eval stop))
               (funcall function)
               (setq done t)
               ;; doesn't mean nesting yet
               (setq count (1- count))
               (not (and (eq indent (current-indentation)) (looking-at "if"))))))
         ((and (looking-at complement-re)(<= (current-indentation) maxindent))
          (setq count (1- count)))
         (t (cond ((and (string-match "except" regexp)(looking-at py-block-re))
                   (setq count (1- count)))
                  ((and (string-match "else" regexp)(looking-at "except"))
                   (current-indentation))
                  (t
                   (setq strict t)
                   ))))))
    (when erg
      (if (looking-at py-def-or-class-re)
          (setq erg (cons (+ (current-indentation) py-indent-offset) erg))
        (setq erg (cons (current-indentation) erg))))
    erg))

(defun py-leave-comment-or-string-backward (&optional pos)
  "If inside a comment or string, leave it backward. "
  (interactive)
  (let ((pps
         (if (featurep 'xemacs)
             (parse-partial-sexp (point-min) (point))
           (syntax-ppss))))
    (when (nth 8 pps)
      (goto-char (1- (nth 8 pps))))))

(defun py-beginning-of-list-pps (&optional iact last ppstart orig done)
  "Go to the beginning of a list.
Optional ARG indicates a start-position for `parse-partial-sexp'.
Return beginning position, nil if not inside."
  (interactive "p")
  (let* ((orig (or orig (point)))
         (ppstart (or ppstart (re-search-backward "^[a-zA-Z]" nil t 1) (point-min)))
         erg)
    (unless done (goto-char orig))
    (setq done t)
    (if
        (setq erg (nth 1 (if (featurep 'xemacs)
                             (parse-partial-sexp ppstart (point))
                           (syntax-ppss))))
        (progn
          (setq last erg)
          (goto-char erg)
          (py-beginning-of-list-pps iact last ppstart orig done))
      (when iact (message "%s" last))
      last)))

(when (featurep 'thing-at-point-utils)
  (defun py-beginning-of-list (&optional iact orig limit done last)
    "Go to beginning of any parentized, braced or bracketed expression in statement. "
    (interactive "p")
    (save-restriction
      (let ((orig (or orig (point)))
            (done done)
            (limit (or limit (re-search-backward "^[a-zA-Z]" nil t 1)))
            (last last))
        (unless (or done (not limit)) (narrow-to-region limit (point-max)))
        (setq done t)
        (goto-char orig)
        (let* ((pt (car-safe (ar-in-parentized-p-atpt)))
               (br (car-safe (ar-in-braced-p-atpt)))
               (bk (car-safe (ar-in-bracketed-p-atpt)))
               (erg (car (sort (delq nil (list pt br bk)) '<))))
          (if erg
              (progn
                (goto-char (1- erg))
                (setq last erg)
                (py-beginning-of-list iact (1- erg) limit done last))
            (when last
              (goto-char last))
            (when iact (message "%s" last))
            last)))))

  (defun py-end-of-list (&optional iact orig limit done last)
    "Go to end of any parentized, braced or bracketed expression in statement. "
    (interactive "p")
    (save-restriction
      (let ((orig (or orig (point)))
            (done done)
            (limit (or limit (re-search-backward "^[a-zA-Z]" nil t 1)))
            (last last))
        (unless (or done (not limit)) (narrow-to-region limit (point-max)))
        (setq done t)
        (goto-char orig)
        (let* ((pt (car-safe (ar-in-parentized-p-atpt)))
               (br (car-safe (ar-in-braced-p-atpt)))
               (bk (car-safe (ar-in-bracketed-p-atpt)))
               (erg (car (sort (delq nil (list pt br bk)) '<))))
          (if erg
              (progn
                (goto-char (1- erg))
                (setq last erg)
                (py-end-of-list iact (1- erg) limit done last))
            (when last
              (goto-char last)
              (match-paren)
              (setq last (1+ (point)))
              (when iact (message "%s" last))
              last)))))))

;;; Down
(defun py-down-block-lc ()
  "Goto beginning of line following end of block.

Returns position reached, if successful, nil otherwise.

\"-lc\" stands for \"left-corner\" - a complementary command travelling left, whilst `py-end-of-block' stops at right corner.

See also `py-down-block': down from current definition to next beginning of block below. "
  (interactive)
  (let ((erg (py-end-of-block)))
    (when erg
      (unless (eobp)
        (forward-line 1)
        (beginning-of-line)
        (setq erg (point))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-clause-lc ()
  "Goto beginning of line following end of clause.

Returns position reached, if successful, nil otherwise.

\"-lc\" stands for \"left-corner\" - a complementary command travelling left, whilst `py-end-of-clause' stops at right corner.

See also `py-down-clause': down from current definition to next beginning of clause below. "
  (interactive)
  (let ((erg (py-end-of-clause)))
    (when erg
      (unless (eobp)
        (forward-line 1)
        (beginning-of-line)
        (setq erg (point))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-def-lc ()
  "Goto beginning of line following end of def.

Returns position reached, if successful, nil otherwise.

\"-lc\" stands for \"left-corner\" - a complementary command travelling left, whilst `py-end-of-def' stops at right corner.

See also `py-down-def': down from current definition to next beginning of def below. "
  (interactive)
  (let ((erg (py-end-of-def)))
    (when erg
      (unless (eobp)
        (forward-line 1)
        (beginning-of-line)
        (setq erg (point))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-class-lc ()
  "Goto beginning of line following end of class.

Returns position reached, if successful, nil otherwise.

\"-lc\" stands for \"left-corner\" - a complementary command travelling left, whilst `py-end-of-class' stops at right corner.

See also `py-down-class': down from current definition to next beginning of class below. "
  (interactive)
  (let ((erg (py-end-of-class)))
    (when erg
      (unless (eobp)
        (forward-line 1)
        (beginning-of-line)
        (setq erg (point))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-statement-lc ()
  "Goto beginning of line following end of statement.

Returns position reached, if successful, nil otherwise.

\"-lc\" stands for \"left-corner\" - a complementary command travelling left, whilst `py-end-of-statement' stops at right corner.

See also `py-down-statement': down from current definition to next beginning of statement below. "
  (interactive)
  (let ((erg (py-end-of-statement)))
    (when erg
      (unless (eobp)
        (forward-line 1)
        (beginning-of-line)
        (setq erg (point))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-statement ()
  "Go to the beginning of next statement below in buffer.

Returns indentation if statement found, nil otherwise. "
  (interactive)
  (let* ((orig (point))
         erg)
    (if (eobp)
        (setq erg nil)
      (progn
        (when (setq erg (py-end-of-statement))
          (if (< orig (setq erg (py-beginning-of-statement-position)))
              (goto-char erg)
            (setq erg (py-end-of-statement))
            (when erg
              (py-beginning-of-statement))))
        (when erg
          (setq erg (current-column)))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-block ()
  "Go to the beginning of next block below in buffer.

Returns indentation if block found, nil otherwise. "
  (interactive)
  (let* ((orig (point))
         erg)
    (if (eobp)
        (setq erg nil)
      (while (and (re-search-forward py-block-re nil (quote move))
                  (nth 8 (if (featurep 'xemacs)
                             (parse-partial-sexp ppstart (point))
                           (syntax-ppss)))))
      (back-to-indentation)
      (when (looking-at py-block-re) (setq erg (current-indentation)))
      (when (and py-verbose-p (interactive-p)) (message "%s" erg))
      erg)))

(defun py-down-clause ()
  "Go to the beginning of next clause below in buffer.

Returns indentation if clause found, nil otherwise. "
  (interactive)
  (let* ((orig (point))
         erg)
    (if (eobp)
        (setq erg nil)
      (while (and (setq erg (py-down-statement))(not (looking-at py-clause-re)))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-block-or-clause ()
  "Go to the beginning of next block-or-clause below in buffer.

Returns indentation if block-or-clause found, nil otherwise. "
  (interactive)
  (let* ((orig (point))
         erg)
    (if (eobp)
        (setq erg nil)
      (while (and (setq erg (py-down-statement))(not (looking-at py-block-or-clause-re)))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-def ()
  "Go to the beginning of next def below in buffer.

Returns indentation if def found, nil otherwise. "
  (interactive)
  (let* ((orig (point))
         erg)
    (if (eobp)
        (setq erg nil)
      (while (and (setq erg (py-down-statement))(not (looking-at py-def-re)))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-class ()
  "Go to the beginning of next class below in buffer.

Returns indentation if class found, nil otherwise. "
  (interactive)
  (let* ((orig (point))
         erg)
    (if (eobp)
        (setq erg nil)
      (while (and (setq erg (py-down-statement))(not (looking-at py-class-re)))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-down-def-or-class ()
  "Go to the beginning of next def-or-class below in buffer.

Returns indentation if def-or-class found, nil otherwise. "
  (interactive)
  (let* ((orig (point))
         erg)
    (if (eobp)
        (setq erg nil)
      (while (and (setq erg (py-down-statement))(not (looking-at py-def-or-class-re)))))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))
;; Py-down commands end

;; ripped from cc-mode
(defun py-forward-into-nomenclature (&optional arg iact)
  "Move forward to end of a nomenclature section or word.

With \\[universal-argument] (programmatically, optional argument ARG), do it that many times.

A `nomenclature' is a fancy way of saying AWordWithMixedCaseNotUnderscores."
  (interactive "p")
  (or arg (setq arg 1))
  (let ((case-fold-search nil)
        (orig (point))
        erg)
    (if (> arg 0)
        (while (and (not (eobp)) (> arg 0))
          ;; (setq erg (re-search-forward "\\(\\W+[_[:lower:][:digit:]ß]+\\)" nil t 1))
          (cond
           ((or (not (eq 0 (skip-chars-forward "[[:blank:][:punct:]\n\r]")))
                (not (eq 0 (skip-chars-forward "_"))))
            (when (or
                   (< 1 (skip-chars-forward "[:upper:]"))
                   (not (eq 0 (skip-chars-forward "[[:lower:][:digit:]ß]")))
                   (not (eq 0 (skip-chars-forward "[[:lower:][:digit:]]"))))
              (setq arg (1- arg))))
           ((or
             (< 1 (skip-chars-forward "[:upper:]"))
             (not (eq 0 (skip-chars-forward "[[:lower:][:digit:]ß]")))
             (not (eq 0 (skip-chars-forward "[[:lower:][:digit:]]"))))
            (setq arg (1- arg)))))
      (while (and (not (bobp)) (< arg 0))
        (when (not (eq 0 (skip-chars-backward "[[:blank:][:punct:]\n\r\f_]")))

          (forward-char -1))
        (or
         (not (eq 0 (skip-chars-backward "[:upper:]")))
         (not (eq 0 (skip-chars-backward "[[:lower:][:digit:]ß]")))
         (skip-chars-backward "[[:lower:][:digit:]ß]"))
        (setq arg (1+ arg))))
    (if (< (point) orig)
        (progn
          (when (looking-back "[[:upper:]]")
            ;; (looking-back "[[:blank:]]"
            (forward-char -1))
          (if (looking-at "[[:alnum:]ß]")
              (setq erg (point))
            (setq erg nil)))
      (if (and (< orig (point)) (not (eobp)))
          (setq erg (point))
        (setq erg nil)))
    (when (and py-report-position-p (or iact (interactive-p))) (message "%s" erg))
    erg))

(defun py-backward-into-nomenclature (&optional arg)
  "Move backward to beginning of a nomenclature section or word.

With optional ARG, move that many times.  If ARG is negative, move
forward.

A `nomenclature' is a fancy way of saying AWordWithMixedCaseNotUnderscores."
  (interactive "p")
  (setq arg (or arg 1))
  (py-forward-into-nomenclature (- arg) arg))

(defalias 'py-match-paren 'match-paren)

(defun match-paren (&optional arg)
  "Go to the matching brace, bracket or parenthesis if on its counterpart.

Otherwise insert the character, the key is assigned to, here `%'.
With universal arg \C-u insert a `%'. "
  (interactive "P")
  (let ((parse-sexp-ignore-comments t))
    (if arg
        (self-insert-command (if (numberp arg) arg 1))
      (cond
       ((and (not match-paren-no-use-syntax-pps) (looking-at "\\s("))
        (forward-list 1)
        (backward-char 1))
       ((and (not match-paren-no-use-syntax-pps)(looking-at "\\s)"))
        (forward-char 1) (backward-list 1))
       ;; if match-paren-no-syntax-pps
       ((looking-at "(")
        (ar-parentized-end-atpt))
       ((looking-at ")")
        (ar-parentized-beginning-atpt))
       ((looking-at "\\\[")
        (ar-bracketed-end-atpt))
       ((looking-at "]")
        (ar-bracketed-beginning-atpt))
       ((looking-at "{")
        (ar-braced-end-atpt))
       ((looking-at "}")
        (ar-braced-beginning-atpt))
       (t (self-insert-command 1))))))

(defun py-travel-current-indent (indent)
  "Moves down until clause is closed, i.e. current indentation is reached.

Takes a list, INDENT and START position. "
  (let (last)
    (while (and (setq last (point))(not (eobp))(py-end-of-statement)
                (<= indent (progn (save-excursion (py-beginning-of-statement)(current-indentation))))))
    (when last (goto-char last))
    last))

;;; python-mode-execute.el
(defun py-toggle-execute-keep-temporary-file-p ()
  "Toggle py-execute-keep-temporary-file-p "
  (interactive)
  (setq py-execute-keep-temporary-file-p
        (not py-execute-keep-temporary-file-p))
  (when (and py-verbose-p (interactive-p)) (message "py-execute-keep-temporary-file-p: %s" py-execute-keep-temporary-file-p)))

(defun py-comint-output-filter-function (string)
  "Watch output for Python prompt and exec next file waiting in queue.
This function is appropriate for `comint-output-filter-functions'."
  ;; TBD: this should probably use split-string
  (when (and (or (string-equal string ">>> ")
		 (and (>= (length string) 5)
		      (string-equal (substring string -5) "\n>>> ")))
	     (or (setq py-shell-input-lines nil)
		 py-file-queue))
    (pop-to-buffer (current-buffer))
    (ignore-errors (delete-file (car py-file-queue)))
    (setq py-file-queue (cdr py-file-queue))
    (if py-file-queue
        (let ((pyproc (get-buffer-process (current-buffer))))
	  (py-execute-file pyproc (car py-file-queue))))))

(defun py-guess-default-python ()
  "Defaults to \"python\", if guessing didn't succeed. "
  (interactive)
  (let* ((cmd (or py-shell-name (py-choose-shell) "python"))
         (erg (if py-edit-only-p cmd (executable-find cmd))))
    (when (interactive-p)
      (if erg
          (message "%s" cmd)
        (message "%s" "Could not detect Python on your system")))))

(defmacro py-separator-char ()
  "Return the file-path separator char from current machine.

When `py-separator-char' is customized, its taken.
Returns char found. "
  `(let ((erg (cond ((characterp py-separator-char)
                     (char-to-string py-separator-char))
                    ;; epd hack
                    ((and
                      (string-match "[Ii][Pp]ython" py-shell-name)
                      (string-match "epd\\|EPD" py-shell-name))
                     (setq erg (shell-command-to-string (concat py-shell-name " -c \"import os; print(os.sep)\"")))
                     (setq erg (replace-regexp-in-string "\n" "" erg))
                     (when (string-match "^$" erg)
                       (setq erg (substring erg (string-match "^$" erg)))))
                    (t (setq erg (shell-command-to-string (concat py-shell-name " -W ignore" " -c \"import os; print(os.sep)\"")))))))
     (replace-regexp-in-string "\n" "" erg)))

(defun py-process-name (&optional name dedicated nostars sepchar)
  "Return the name of the running Python process, `get-process' willsee it. "
  (let* ((sepchar (if sepchar sepchar (py-separator-char)))
         (thisname (if name
                       (if (string-match sepchar name)
                           (substring name (progn (string-match (concat "\\(.+\\)" sepchar "\\(.+\\)$") name) (match-beginning 2)))

                         name)
                     (substring py-shell-name (or (string-match (concat sepchar ".+$") py-shell-name) 0))))
         (nname (cond (dedicated
                       (make-temp-name (concat thisname "-")))
                      ;; ((string-match "\*" (buffer-name))
                      ;; (replace-regexp-in-string "\*" "" (buffer-name)))
                      (t thisname)))
         (erg (cond ((or (string-match "ipython" nname)
                         (string-match "IPython" nname))
                     "IPython")
                    (nname))))
    (unless (or nostars (string-match "^\*" erg))(setq erg (concat "*" erg "*")))
    erg))

;; from ipython.el
(defun py-dirstack-hook ()
  ;; the following is to synchronize dir-changes
  (make-local-variable 'shell-dirstack)
  (setq shell-dirstack nil)
  (make-local-variable 'shell-last-dir)
  (setq shell-last-dir nil)
  (make-local-variable 'shell-dirtrackp)
  (setq shell-dirtrackp t)
  (add-hook 'comint-input-filter-functions 'shell-directory-tracker nil t))

(defun py-set-shell-completion-environment (&optional pyshellname)
  "Sets `...-completion-command-string' and `py-complete-function'. "
  (interactive)
  (let ((pyshellname (or pyshellname py-shell-name))
        ipython-version)
    (local-unset-key [tab])
    (cond ((string-match "ipython" pyshellname)
           (setq ipython-version (string-to-number (substring (shell-command-to-string (concat py-shell-name " -V")) 2 -1)))
           (setq ipython-completion-command-string (if (< ipython-version 11) ipython0.10-completion-command-string ipython0.11-completion-command-string))
           (define-key inferior-python-mode-map [tab] ipython-complete-function)
           (define-key python-shell-map [tab] ipython-complete-function))
          ((string-match "python3" pyshellname)
           (add-hook 'completion-at-point-functions
                     'py-shell-complete nil 'local)
           (define-key inferior-python-mode-map [tab]
             'py-shell-complete))
          (t
           (define-key inferior-python-mode-map [tab] 'py-shell-complete)))))

(defun py-set-ipython-completion-command-string (&optional pyshellname)
  "Set and return `ipython-completion-command-string'. "
  (interactive)
  (let* ((pyshellname (or pyshellname py-shell-name))
         (ipython-version
          (when (string-match "ipython" pyshellname)
            (string-to-number (substring (shell-command-to-string (concat pyshellname " -V")) 2 -1)))))
    (when ipython-version
      (setq ipython-completion-command-string (if (< ipython-version 11) ipython0.10-completion-command-string ipython0.11-completion-command-string))
      ipython-completion-command-string)))

(defalias 'py-dedicated-shell 'py-shell-dedicated)
(defun py-shell-dedicated (&optional argprompt)
  "Start an interactive Python interpreter in another window.

With optional \\[universal-argument] user is prompted by
`py-choose-shell' for command and options to pass to the Python
interpreter.
"
  (interactive "P")
  (py-shell argprompt t))

(defun py-buffer-name-prepare (name &optional sepchar dedicated)
  "Return an appropriate name to display in modeline.
SEPCHAR is the file-path separator of your system. "
  (let ((sepchar (or sepchar (py-separator-char)))
        prefix erg suffix)
    (when (string-match (regexp-quote sepchar) name)
      (setq prefix "ND"))
    (setq erg
          (cond ((string= "ipython" name)
                 (replace-regexp-in-string "ipython" "IPython" name))
                ((string= "jython" name)
                 (replace-regexp-in-string "jython" "Jython" name))
                ((string= "python" name)
                 (replace-regexp-in-string "python" "Python" name))
                ((string-match "python2" name)
                 (replace-regexp-in-string "python2" "Python2" name))
                ((string-match "python3" name)
                 (replace-regexp-in-string "python3" "Python3" name))
                (t name)))
    (when dedicated
      (setq erg (make-temp-name (concat erg "-"))))
    (cond ((and prefix (string-match "^\*" erg))
           (setq erg (replace-regexp-in-string "^\*" (concat "*" prefix " ") erg)))
          (prefix
           (setq erg (concat "*" prefix " " erg "*")))

          (t (setq erg (concat "*" erg "*"))))
    erg))

(defun py-delete-numbers-and-stars-from-string (string)
  "Delete numbering and star chars from string, return result.

Needed when file-path names are contructed from maybe numbered buffer names like \"\*Python\*<2> \""
  (replace-regexp-in-string
   "<\\([0-9]+\\)>" ""
   (replace-regexp-in-string
    "\*" ""
    string)))

(defun py-shell-manage-windows (switch py-split-windows-on-execute-p py-switch-buffers-on-execute-p oldbuf py-buffer-name)
  (delete-other-windows)
  (window-configuration-to-register 213465889)
  (cond (;; split and switch
         (unless (eq switch 'noswitch)
           (and py-split-windows-on-execute-p
                (or (eq switch 'switch)
                    py-switch-buffers-on-execute-p)))
         (unless (string-match "[Ii][Pp]ython" py-buffer-name) (delete-other-windows))
         (when (< (count-windows) 2)
           (funcall py-split-windows-on-execute-function))
         (pop-to-buffer py-buffer-name))
        ;; split, not switch
        ((and py-split-windows-on-execute-p
              (or (eq switch 'noswitch)
                  (not (eq switch 'switch))))
         (if (< (count-windows) 2)
             (progn
               (funcall py-split-windows-on-execute-function)
               (display-buffer py-buffer-name)
               ;; avoids windows flip top-down - by side-effect?
               (window-configuration-to-register 213465889))
           (window-configuration-to-register 213465889))
         (jump-to-register 213465889)
         (display-buffer oldbuf)
         (pop-to-buffer oldbuf))
        ;; no split, switch
        ((or (eq switch 'switch)
             (and (not (eq switch 'noswitch))
                  py-switch-buffers-on-execute-p))
         (pop-to-buffer py-buffer-name)
         (goto-char (point-max)))
        ;; no split, no switch
        ((or (eq switch 'noswitch)
             (not py-switch-buffers-on-execute-p))
         (set-buffer oldbuf)
         (switch-to-buffer (current-buffer)))))

(defun py-report-executable (py-buffer-name)
  (downcase (replace-regexp-in-string
             "<\\([0-9]+\\)>" ""
             (replace-regexp-in-string
              "\*" ""
              (if
                  (string-match " " py-buffer-name)
                  (substring py-buffer-name (1+ (string-match " " py-buffer-name)))
                py-buffer-name)))))

(defun py-shell (&optional argprompt dedicated pyshellname switch sepchar py-buffer-name done)
  "Start an interactive Python interpreter in another window.

Interactively, \\[universal-argument] 4 prompts for a buffer.
\\[universal-argument] 2 prompts for `py-python-command-args'.
If `default-directory' is a remote file name, it is also prompted
to change if called with a prefix arg.

Returns py-shell's buffer-name.
Optional string PYSHELLNAME overrides default `py-shell-name'.
Optional symbol SWITCH ('switch/'noswitch) precedes `py-switch-buffers-on-execute-p'
When SEPCHAR is given, `py-shell' must not detect the file-separator.
BUFFER allows specifying a name, the Python process is connected to
When DONE is `t', `py-shell-manage-windows' is omitted
"
  (interactive "P")
  (let* ((sepchar (or sepchar (py-separator-char)))
         (args py-python-command-args)
         (oldbuf (current-buffer))
         (path (getenv "PYTHONPATH"))
         ;; make python.el forms usable, to import emacs.py
         (process-environment
          (cons (concat "PYTHONPATH="
                        (if path (concat path path-separator))
                        data-directory)
                process-environment))
         ;; proc
         (py-buffer-name
          (or py-buffer-name
              (when argprompt
                (cond
                 ((eq 4 (prefix-numeric-value argprompt))
                  (setq py-buffer-name
                        (prog1
                            (read-buffer "Py-Shell buffer: "
                                         (generate-new-buffer-name (py-buffer-name-prepare (or pyshellname py-shell-name) sepchar)))
                          (if (file-remote-p default-directory)
                              ;; It must be possible to declare a local default-directory.
                              (setq default-directory
                                    (expand-file-name
                                     (read-file-name
                                      "Default directory: " default-directory default-directory
                                      t nil 'file-directory-p)))))))
                 ((and (eq 2 (prefix-numeric-value argprompt))
                       (fboundp 'split-string))
                  (setq args (split-string
                              (read-string "Py-Shell arguments: "
                                           (concat
                                            (mapconcat 'identity py-python-command-args " ") " ")))))))))
         (pyshellname (or pyshellname
                          (if (or (null py-shell-name)(string= "" py-shell-name))
                              (py-choose-shell)
                            py-shell-name)))
         ;; If we use a pipe, Unicode characters are not printed
         ;; correctly (Bug#5794) and IPython does not work at
         ;; all (Bug#5390). python.el
         (process-connection-type t)
         ;; already in py-choose-shell
         (py-use-local-default
          (if (not (string= "" py-shell-local-path))
              (expand-file-name py-shell-local-path)
            (when py-use-local-default
              (error "Abort: `py-use-local-default' is set to `t' but `py-shell-local-path' is empty. Maybe call `py-toggle-local-default-use'"))))
         (py-buffer-name-prepare (unless py-buffer-name
                                   (py-buffer-name-prepare (or pyshellname py-shell-name) sepchar dedicated)))
         (py-buffer-name (or py-buffer-name py-buffer-name-prepare))
         (executable (cond (pyshellname)
                           (py-buffer-name
                            (py-report-executable py-buffer-name)))))
    ;; done by python-mode resp. inferior-python-mode
    ;; (py-set-shell-completion-environment executable)
    (unless (comint-check-proc py-buffer-name)
      ;; comint
      (when py-buffer-name
        (set-buffer (apply 'make-comint-in-buffer executable py-buffer-name executable nil args)))
      (set (make-local-variable 'comint-prompt-regexp)
           (concat "\\("
                   (mapconcat 'identity
                              (delq nil (list py-shell-input-prompt-1-regexp py-shell-input-prompt-2-regexp ipython-de-input-prompt-regexp ipython-de-output-prompt-regexp py-pdbtrack-input-prompt py-pydbtrack-input-prompt))
                              "\\|")
                   "\\)"))
      (add-hook 'comint-output-filter-functions
                'py-comint-output-filter-function)
      (set-buffer (get-buffer-create
                   (apply 'make-comint-in-buffer executable py-buffer-name executable nil args)))
      (setq python-buffer (current-buffer))
      (accept-process-output (get-buffer-process python-buffer) 5)
      (inferior-python-mode)
      (setq comint-input-sender 'py-shell-simple-send)
      (setq comint-input-ring-file-name
            (cond ((string-match "[iI][pP]ython[[:alnum:]]*$" py-buffer-name)
                   (if (getenv "IPYTHONDIR")
                       (concat (getenv "IPYTHONDIR") "/history")
                     "~/.ipython/history"))
                  ((getenv "PYTHONHISTORY")
                   (concat (getenv "PYTHONHISTORY") "/" (py-report-executable py-buffer-name) "_history"))
                  (dedicated
                   (concat "~/." (substring py-buffer-name 0 (string-match "-" py-buffer-name)) "_history"))
                  ;; .pyhistory might be locked from outside Emacs
                  ;; (t "~/.pyhistory")
                  (t (concat "~/." (py-report-executable py-buffer-name) "_history")
                     )))
      (comint-read-input-ring t)
      (set-process-sentinel (get-buffer-process (current-buffer))
                            #'shell-write-history-on-exit)
      ;; (setq proc (get-buffer-process (current-buffer)))
      ;; pdbtrack
      (add-hook 'comint-output-filter-functions 'py-pdbtrack-track-stack-file)
      (setq py-pdbtrack-do-tracking-p t)
      ;;
      (set-syntax-table python-mode-syntax-table)
      (ansi-color-for-comint-mode-on)
      ;; (use-local-map py-shell-map)
      (use-local-map inferior-python-mode-map)
      ;; (add-hook 'py-shell-hook 'py-dirstack-hook)
      (when py-shell-hook (run-hooks 'py-shell-hook))
      (goto-char (point-max)))
    (if (and (interactive-p) py-shell-switch-buffers-on-execute-p)
        (pop-to-buffer py-buffer-name)
      (unless done (py-shell-manage-windows switch py-split-windows-on-execute-p py-switch-buffers-on-execute-p oldbuf py-buffer-name)))
    ;; (when py-verbose-p (message py-buffer-name))
    py-buffer-name))

(defalias 'iyp 'ipython)
(defalias 'ipy 'ipython)
;;; Python named shells
(defun python (&optional argprompt dedicated switch)
  "Start an Python interpreter.

Optional \\[universal-argument] prompts for options to pass to the Python interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. "
  (interactive "P")
  (py-shell argprompt dedicated "python" switch))

(defun ipython (&optional argprompt dedicated switch)
  "Start an IPython interpreter.

Optional \\[universal-argument] prompts for options to pass to the IPython interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. "
  (interactive "P")
  (py-shell argprompt dedicated "ipython" switch))

(defun python3 (&optional argprompt dedicated switch)
  "Start an Python3 interpreter.

Optional \\[universal-argument] prompts for options to pass to the Python3 interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. "
  (interactive "P")
  (py-shell argprompt dedicated "python3" switch))

(defun python2 (&optional argprompt dedicated switch)
  "Start an Python2 interpreter.

Optional \\[universal-argument] prompts for options to pass to the Python2 interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. "
  (interactive "P")
  (py-shell argprompt dedicated "python2" switch))

(defun python2.7 (&optional argprompt dedicated switch)
  "Start an Python2.7 interpreter.

Optional \\[universal-argument] prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. "
  (interactive "P")
  (py-shell argprompt dedicated "python2.7" switch))

(defun jython (&optional argprompt dedicated switch)
  "Start an Jython interpreter.

Optional \\[universal-argument] prompts for options to pass to the Jython interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. "
  (interactive "P")
  (py-shell argprompt dedicated "jython" switch))

(defun python3.2 (&optional argprompt dedicated switch)
  "Start an Python3.2 interpreter.

Optional \\[universal-argument] prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'.
   Optional DEDICATED SWITCH are provided for use from programs. "
  (interactive "P")
  (py-shell argprompt dedicated "python3.2" switch))

;; dedicated
(defun python-dedicated (&optional argprompt switch)
  "Start an unique Python interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python" switch))

(defun ipython-dedicated (&optional argprompt switch)
  "Start an unique IPython interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the IPython interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "ipython" switch))

(defun python3-dedicated (&optional argprompt switch)
  "Start an unique Python3 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python3 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python3" switch))

(defun python2-dedicated (&optional argprompt switch)
  "Start an unique Python2 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python2 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python2" switch))

(defun python2.7-dedicated (&optional argprompt switch)
  "Start an unique Python2.7 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python2.7" switch))

(defun jython-dedicated (&optional argprompt switch)
  "Start an unique Jython interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Jython interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "jython" switch))

(defun python3.2-dedicated (&optional argprompt switch)
  "Start an unique Python3.2 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python3.2" switch))

;; switch
(defun python-switch (&optional argprompt dedicated)
  "Switch to Python interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python" 'switch))

(defun ipython-switch (&optional argprompt dedicated)
  "Switch to IPython interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the IPython interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "ipython" 'switch))

(defun python3-switch (&optional argprompt dedicated)
  "Switch to Python3 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python3 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python3" 'switch))

(defun python2-switch (&optional argprompt dedicated)
  "Switch to Python2 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python2 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python2" 'switch))

(defun python2.7-switch (&optional argprompt dedicated)
  "Switch to Python2.7 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python2.7" 'switch))

(defun jython-switch (&optional argprompt dedicated)
  "Switch to Jython interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Jython interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "jython" 'switch))

(defun python3.2-switch (&optional argprompt dedicated)
  "Switch to Python3.2 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python3.2" 'switch))

(defun python-no-switch (&optional argprompt dedicated)
  "Open an Python interpreter in another window, but do not switch to it.

Optional \\[universal-argument] prompts for options to pass to the Python interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python" 'noswitch))

(defun ipython-no-switch (&optional argprompt dedicated)
  "Open an IPython interpreter in another window, but do not switch to it.

Optional \\[universal-argument] prompts for options to pass to the IPython interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "ipython" 'noswitch))

(defun python3-no-switch (&optional argprompt dedicated)
  "Open an Python3 interpreter in another window, but do not switch to it.

Optional \\[universal-argument] prompts for options to pass to the Python3 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python3" 'noswitch))

(defun python2-no-switch (&optional argprompt dedicated)
  "Open an Python2 interpreter in another window, but do not switch to it.

Optional \\[universal-argument] prompts for options to pass to the Python2 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python2" 'noswitch))

(defun python2.7-no-switch (&optional argprompt dedicated)
  "Open an Python2.7 interpreter in another window, but do not switch to it.

Optional \\[universal-argument] prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python2.7" 'noswitch))

(defun jython-no-switch (&optional argprompt dedicated)
  "Open an Jython interpreter in another window, but do not switch to it.

Optional \\[universal-argument] prompts for options to pass to the Jython interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "jython" 'noswitch))

(defun python3.2-no-switch (&optional argprompt dedicated)
  "Open an Python3.2 interpreter in another window, but do not switch to it.

Optional \\[universal-argument] prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt dedicated "python3.2" 'noswitch))

(defalias 'python-dedicated-switch 'python-switch-dedicated)
(defun python-switch-dedicated (&optional argprompt)
  "Switch to an unique Python interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python" 'switch))

(defalias 'ipython-dedicated-switch 'ipython-switch-dedicated)
(defun ipython-switch-dedicated (&optional argprompt)
  "Switch to an unique IPython interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the IPython interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "ipython" 'switch))

(defalias 'python3-dedicated-switch 'python3-switch-dedicated)
(defun python3-switch-dedicated (&optional argprompt)
  "Switch to an unique Python3 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python3 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python3" 'switch))

(defalias 'python2-dedicated-switch 'python2-switch-dedicated)
(defun python2-switch-dedicated (&optional argprompt)
  "Switch to an unique Python2 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python2 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python2" 'switch))

(defalias 'python2.7-dedicated-switch 'python2.7-switch-dedicated)
(defun python2.7-switch-dedicated (&optional argprompt)
  "Switch to an unique Python2.7 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python2.7" 'switch))

(defalias 'jython-dedicated-switch 'jython-switch-dedicated)
(defun jython-switch-dedicated (&optional argprompt)
  "Switch to an unique Jython interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Jython interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "jython" 'switch))

(defalias 'python3.2-dedicated-switch 'python3.2-switch-dedicated)
(defun python3.2-switch-dedicated (&optional argprompt)
  "Switch to an unique Python3.2 interpreter in another window.

Optional \\[universal-argument] prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'."
  (interactive "P")
  (py-set-shell-completion-environment)
  (py-shell argprompt t "python3.2" 'switch))


;;; Code execution commands
(declare-function compilation-shell-minor-mode "compile" (&optional arg))

(defun py-which-execute-file-command (filename)
  "Return the command appropriate to Python version.

Per default it's \"(format \"execfile(r'%s') # PYTHON-MODE\\n\" filename)\" for Python 2 series."
  (interactive)
  (let* ((erg (py-which-python))
         (cmd (if (< erg 3)
                  (format "execfile(r'%s') # PYTHON-MODE\n" filename)
                (format "exec(compile(open('%s').read(), '%s', 'exec')) # PYTHON-MODE\n" filename filename))))
    (when (and py-verbose-p (interactive-p)) (message "%s" (prin1-to-string cmd)))
    cmd))

(defun py-execute-region-no-switch (start end &optional shell dedicated)
  "Send the region to a Python interpreter.

Ignores setting of `py-switch-buffers-on-execute-p', buffer with region stays current.
 "
  (interactive "r\nP")
  (py-execute-base start end py-shell-name dedicated 'noswitch))

(defun py-execute-region-switch (start end &optional shell dedicated)
  "Send the region to a Python interpreter.

Ignores setting of `py-switch-buffers-on-execute-p', output-buffer will being switched to.
"
  (interactive "r\nP")
  (py-execute-base start end py-shell-name dedicated 'switch))

(defun py-execute-region (start end &optional shell dedicated switch)
  "Send the region to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)
"
  (interactive "r\nP")
  (let ((shell (cond ((and py-force-local-shell-p py-force-py-shell-name-p)
                      py-shell-name)
                     ((or py-force-py-shell-name-p (eq 4 (prefix-numeric-value shell))) (default-value 'py-shell-name))
                     ((and (numberp shell) (not (eq 1 (prefix-numeric-value shell))))
                      (read-from-minibuffer "(path-to-)shell-name: " (default-value 'py-shell-name)))
                     (t shell))))
    (py-execute-base start end shell dedicated switch)))

(defun py-execute-region-default (start end &optional dedicated)
  "Send the region to the systems default Python interpreter.
See also `py-execute-region'. "
  (interactive "r\nP")
  (py-execute-base start end (default-value 'py-shell-name) dedicated))

(defun py-execute-region-dedicated (start end &optional shell)
  "Get the region processed by an unique Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument. "
  (interactive "r\nP")
  (let ((shell (cond ((eq 4 (prefix-numeric-value shell)) (default-value 'py-shell-name))
                     ((and (numberp shell) (not (eq 1 (prefix-numeric-value shell))))
                      (read-from-minibuffer "(path-to-)shell-name: " (default-value 'py-shell-name)))
                     (t shell))))
    (py-execute-base start end shell t)))

(defalias 'py-execute-region-dedicated-default 'py-execute-region-default-dedicated)
(defun py-execute-region-default-dedicated (start end)
  "Send the region to an unique shell of systems default Python. "
  (interactive "r")
  (py-execute-base start end (default-value 'py-shell-name) t))

(defun py-execute-base (start end &optional pyshellname dedicated switch nostars sepchar)
  "Adapt the variables used in the process. "
  (let* ((oldbuf (current-buffer))
         (pyshellname (or pyshellname (py-choose-shell)))
         (py-execute-directory (or (ignore-errors (file-name-directory (buffer-file-name)))(getenv "WORKON_HOME")(getenv "HOME")))
         (strg (buffer-substring-no-properties start end))
         (sepchar (if sepchar sepchar (py-separator-char)))
         (py-buffer-name (py-buffer-name-prepare pyshellname sepchar))
         (temp (make-temp-name
                (concat (replace-regexp-in-string (regexp-quote sepchar) "-" (replace-regexp-in-string (concat "^" (regexp-quote sepchar)) "" (replace-regexp-in-string ":" "-" pyshellname))) "-")))
         (file (concat (expand-file-name py-temp-directory) sepchar (replace-regexp-in-string (regexp-quote sepchar) "-" temp) ".py"))
         (filebuf (get-buffer-create file))
         (proc (if dedicated
                   (get-buffer-process (py-shell nil dedicated pyshellname switch sepchar py-buffer-name t))
                 (or (get-buffer-process pyshellname)
                     (get-buffer-process (py-shell nil dedicated pyshellname switch sepchar py-buffer-name t)))))
         (procbuf (process-buffer proc))
         (pec (if (string-match "[pP]ython ?3" py-buffer-name)
                  (format "exec(compile(open('%s').read(), '%s', 'exec')) # PYTHON-MODE\n" file file)
                (format "execfile(r'%s') # PYTHON-MODE\n" file)))
         (wholebuf (when (boundp 'wholebuf) wholebuf))
         (comint-scroll-to-bottom-on-output t)
         erg)
    (set-buffer filebuf)
    (erase-buffer)
    (insert strg)
    (py-fix-start (point-min)(point-max))
    (py-if-needed-insert-shell (prin1-to-string proc) sepchar)
    (unless wholebuf (py-insert-coding))
    (py-insert-execute-directory)
    (cond (python-mode-v5-behavior-p

           (let ((cmd (concat pyshellname (if (string-equal py-which-bufname
                                                            "Jython")
                                              " -" " -c "))))
             (save-excursion
               (set-buffer filebuf)
               (shell-command-on-region (point-min) (point-max)
                                        cmd py-output-buffer))
             (if (not (get-buffer py-output-buffer))
                 (message "No output.")
               (setq py-exception-buffer (current-buffer))
               (let ((err-p (py-postprocess-output-buffer py-output-buffer)))
                 ;; (when py-switch-buffers-on-execute-p
                 (pop-to-buffer py-output-buffer)
                 ;; )
                 (if err-p
                     (pop-to-buffer py-exception-buffer))))))
          (t (set-buffer filebuf)
             (write-region (point-min) (point-max) file nil t nil 'ask)
             (set-buffer-modified-p 'nil)
             (kill-buffer filebuf)
             (if (file-readable-p file)
                 (progn
                   (when (string-match "ipython" (process-name proc))
                     (sit-for py-ipython-execute-delay))
                   (setq erg (py-execute-file-base proc file pec procbuf))
                   (setq py-exception-buffer (cons file (current-buffer)))
                   (py-shell-manage-windows switch py-split-windows-on-execute-p py-switch-buffers-on-execute-p oldbuf py-buffer-name)
                   (unless (string= (buffer-name (current-buffer)) (buffer-name procbuf))
                     (when py-verbose-p (message "Output buffer: %s" procbuf)))
                   (sit-for 0.1)
                   (unless py-execute-keep-temporary-file-p
                     (delete-file file)
                     (when (buffer-live-p file)
                       (kill-buffer file)))
                   erg)
               (message "%s not readable. %s" file "Do you have write permissions?"))))))

(defun py-execute-string (&optional string shell dedicated)
  "Send the argument STRING to a Python interpreter.

See also `py-execute-region'. "
  (interactive)
  (let ((string (or string (read-from-minibuffer "String: ")))
        (shell (or shell (default-value 'py-shell-name))))
    (with-temp-buffer
      (insert string)
      (py-execute-region (point-min) (point-max) shell dedicated))))

(defun py-execute-string-dedicated (&optional string shell)
  "Send the argument STRING to an unique Python interpreter.

See also `py-execute-region'. "
  (interactive)
  (let ((string (or string (read-from-minibuffer "String: ")))
        (shell (or shell (default-value 'py-shell-name))))
    (with-temp-buffer
      (insert string)
      (py-execute-region (point-min) (point-max) shell t))))

(defun py-if-needed-insert-shell (&optional name sepchar)
  (let ((erg (or name
                 (py-choose-shell-by-shebang)
                 (py-choose-shell-by-import)
                 py-shell-name))
        (sepchar (or sepchar (py-separator-char))))
    (when (string-match " " erg) (setq erg (substring erg (1+ (string-match " " erg))))
          ;; closing ">"
          (setq erg (substring erg 0 (1- (length erg)))))
    (goto-char (point-min))
    (while (empty-line-p) (delete-region (point) (1+ (line-end-position))))
    (unless (looking-at py-shebang-regexp)
      (if (string-match (concat "^" erg) "ipython")
          (progn
            (shell-command "type ipython" t)
            (switch-to-buffer (current-buffer))
            (when (looking-at "[^/\n\r]+")
              (replace-match "#! ")))
        (if (string-match (regexp-quote sepchar) erg)
            (insert (concat "#! " erg "\n\n"))
          (insert (concat py-shebang-startstring " " erg "\n\n")))))))

(defun py-insert-execute-directory ()
  (goto-char (point-min))
  (if (re-search-forward py-encoding-string-re nil (quote move))
      (progn
        (newline)
        (insert (concat "import os; os.chdir(\"" py-execute-directory "\")\n")))
    (goto-char (point-min))
    (forward-line 2)
    (newline)
    (insert (concat "import os; os.chdir(\"" py-execute-directory "\")\n"))))

(defun py-insert-coding ()
  ;; (switch-to-buffer (current-buffer))
  (goto-char (point-min))
  (unless (re-search-forward py-encoding-string-re nil t)
    (goto-char (point-min))
    (if (re-search-forward py-shebang-regexp nil t 1)
        (progn
          (newline)
          (insert (concat py-encoding-string "\n")))
      (insert (concat py-encoding-string "\n")))))

(defun py-if-needed-insert-if ()
  "Internal use by py-execute... functions.
Inserts an incentive true form \"if 1:\\n.\" "
  (let ((needs-if (/= (py-point 'bol) (py-point 'boi))))
    (when needs-if
      (insert "if 1:\n")
      (setq py-line-number-offset (- py-line-number-offset 1)))))

(defun py-fix-start (start end)
  "Internal use by py-execute... functions.
Avoid empty lines at the beginning. "
  (goto-char start)
  (let ((beg (copy-marker start)))
    (while (empty-line-p)
      (delete-region (line-beginning-position) (1+ (line-end-position))))
    (back-to-indentation)
    (unless (eq (current-indentation) 0)
      (py-shift-left (current-indentation) start end))
    (setq py-line-number-offset (count-lines 1 start))
    beg))

(defun py-fetch-py-master-file ()
  "Lookup if a `py-master-file' is specified.

See also doku of variable `py-master-file' "
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (goto-char (point-min))
      (when (re-search-forward "^ *# Local Variables:" nil (quote move) 1)
        (when
            (re-search-forward (concat "^\\( *# py-master-file: *\\)\"\\([^ \t]+\\)\" *$") nil t 1)
          (setq py-master-file (match-string-no-properties 2))))))
  (when (and py-verbose-p (interactive-p)) (message "%s" py-master-file)))

(defun py-execute-import-or-reload (&optional argprompt shell dedicated)
  "Import the current buffer's file in a Python interpreter.

If the file has already been imported, then do reload instead to get
the latest version.

If the file's name does not end in \".py\", then do execfile instead.

If the current buffer is not visiting a file, do `py-execute-buffer'
instead.

If the file local variable `py-master-file' is non-nil, import or
reload the named file instead of the buffer's file.  The file may be
saved based on the value of `py-execute-import-or-reload-save-p'.

See also `\\[py-execute-region]'.

This may be preferable to `\\[py-execute-buffer]' because:

 - Definitions stay in their module rather than appearing at top
   level, where they would clutter the global namespace and not affect
   uses of qualified names (MODULE.NAME).

 - The Python debugger gets line number information about the functions."
  (interactive "P")
  ;; Check file local variable py-master-file
  (if py-master-file
      (let* ((filename (expand-file-name py-master-file))
             (buffer (or (get-file-buffer filename)
                         (find-file-noselect filename))))
        (set-buffer buffer)))
  (let ((shell (or shell (py-choose-shell argprompt shell dedicated)))
        (file (buffer-file-name (current-buffer))))
    (if file
        (let ((proc (or
                     (ignore-errors (get-process (file-name-directory shell)))
                     (get-buffer-process (py-shell argprompt dedicated (or shell (default-value 'py-shell-name)))))))
          ;; Maybe save some buffers
          (save-some-buffers (not py-ask-about-save) nil)
          (py-execute-file-base proc file
                                (if (string-match "\\.py$" file)
                                    (let ((m (py-qualified-module-name (expand-file-name file))))
                                      (if (string-match "python2" (file-name-nondirectory shell))
                                          (format "import sys\nif sys.modules.has_key('%s'):\n reload(%s)\nelse:\n import %s\n" m m m)
                                        (format "import sys,imp\nif'%s' in sys.modules:\n imp.reload(%s)\nelse:\n import %s\n" m m m)))
                                  ;; (format "execfile(r'%s')\n" file)
                                  (py-which-execute-file-command file))))
      (py-execute-buffer py-shell-name))))

(defun py-qualified-module-name (file)
  "Find the qualified module name for filename FILE.

Basically, this goes down the directory tree as long as there are __init__.py files there."
  (let ((rec #'(lambda (d f)
		 (let* ((dir (file-name-directory d))
			(initpy (concat dir "__init__.py")))
		   (if (file-exists-p initpy)
		       (let ((d2 (directory-file-name d)))
			 (funcall rec (file-name-directory d2)
                                  (concat (file-name-nondirectory d2) "." f)))
		     f)))))
    (funcall rec (file-name-directory file)
	     (file-name-sans-extension (file-name-nondirectory file)))))

(defun py-execute-buffer-dedicated (&optional shell)
  "Send the contents of the buffer to a unique Python interpreter.

If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.

If a clipping restriction is in effect, only the accessible portion of the buffer is sent. A trailing newline will be supplied if needed.

With \\[univeral-argument] user is prompted to specify another then default shell.
See also `\\[py-execute-region]'. "
  (interactive "P")
  (py-execute-buffer-base shell t))

(defun py-execute-buffer-switch (&optional shell dedicated)
  "Send the contents of the buffer to a Python interpreter and switches to output.

If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.
If there is a *Python* process buffer, it is used.
If a clipping restriction is in effect, only the accessible portion of the buffer is sent. A trailing newline will be supplied if needed.

With \\[univeral-argument] user is prompted to specify another then default shell.
See also `\\[py-execute-region]'. "
  (interactive "P")
  (py-execute-buffer-base shell dedicated 'switch))

(defalias 'py-execute-buffer-switch-dedicated 'py-execute-buffer-dedicated-switch)
(defun py-execute-buffer-dedicated-switch (&optional shell)
  "Send the contents of the buffer to an unique Python interpreter.

Ignores setting of `py-switch-buffers-on-execute-p'.
If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.

If a clipping restriction is in effect, only the accessible portion of the buffer is sent. A trailing newline will be supplied if needed.

With \\[univeral-argument] user is prompted to specify another then default shell.
See also `\\[py-execute-region]'. "
  (interactive "P")
  (py-execute-buffer-base shell t 'switch))

(defun py-execute-buffer (&optional shell dedicated switch)
  "Send the contents of the buffer to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch) "
  (interactive "P")
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end shell dedicated switch))))

(defun py-execute-buffer-base (&optional shell dedicated switch)
  "Honor `py-master-file'. "
  (save-excursion
    (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
      (if py-master-file
          (let* ((filename (expand-file-name py-master-file))
                 (buffer (or (get-file-buffer filename)
                             (find-file-noselect filename))))
            (set-buffer buffer)))
      (py-execute-region (point-min) (point-max) shell dedicated switch))))

(defun py-execute-buffer-no-switch (&optional shell dedicated)
  "Send the contents of the buffer to a Python interpreter but don't switch to output.

If the file local variable `py-master-file' is non-nil, execute the
named file instead of the buffer's file.
If there is a *Python* process buffer, it is used.
If a clipping restriction is in effect, only the accessible portion of the buffer is sent. A trailing newline will be supplied if needed.

With \\[univeral-argument] user is prompted to specify another then default shell.
See also `\\[py-execute-region]'. "
  (interactive "P")
  (py-execute-buffer-base shell dedicated 'noswitch))

;; Fixme: Try to define the function or class within the relevant
;; module, not just at top level.
(defun py-execute-defun ()
  "Send the current defun (class or method) to the inferior Python process."
  (interactive)
  (save-excursion (py-execute-region (progn (beginning-of-defun) (point))
                                     (progn (end-of-defun) (point)))))

(defun py-process-file (filename &optional output-buffer error-buffer)
  "Process \"python filename\".

Optional OUTPUT-BUFFER and ERROR-BUFFER might be given. "
  (interactive "fDatei:")
  (let ((coding-system-for-read 'utf-8)
        (coding-system-for-write 'utf-8)
        (output-buffer (or output-buffer (make-temp-name "py-process-file-output")))
        (cmd (py-choose-shell)))
    (unless (buffer-live-p output-buffer)
      (set-buffer (get-buffer-create output-buffer)))
    (shell-command (concat cmd " " filename) output-buffer error-buffer)
    (when (interactive-p) (switch-to-buffer output-buffer))))

;;;
(defun py-exec-execfile-region (start end &optional shell)
  "Execute the region in a Python interpreter. "
  (interactive "r\nP")
  (let ((shell (if (eq 4 (prefix-numeric-value shell))
                   (read-from-minibuffer "Shell: " (default-value 'py-shell-name))
                 py-shell-name)))
    (let ((strg (buffer-substring-no-properties start end)))
      (py-exec-execfile-base strg shell (interactive-p)))))

(defun py-exec-execfile-base (strg shell iact)
  (let* ((temp (make-temp-name (concat (buffer-name) "-")))
         (file (concat (expand-file-name temp) py-temp-directory ".py"))
         (imports (py-find-imports))
         (shell shell)
         cmd header)
    (with-temp-buffer
      (insert imports)
      (insert strg)
      ;;      (py-if-needed-insert-if)
      (or shell (setq shell (py-choose-shell)))
      (py-insert-coding)
      (py-if-needed-insert-shell shell)
      (setq header (buffer-substring-no-properties (point-min) (point)))
      (switch-to-buffer (current-buffer))
      (setq cmd (py-which-execute-file-command file))
      (write-file file))
    (py-exec-execfile file cmd header (concat temp "-output"))
    (set-buffer (concat temp "-output"))
    (when iact (switch-to-buffer (current-buffer)))
    (when (file-readable-p file)
      (delete-file file))
    (when iact (message "Output goes to buffer: %s" temp))
    (concat temp "-output")))

(defun py-exec-execfile (filename cmd header &optional output-buffer error-buffer)
  "Process \"python filename\",
Optional OUTPUT-BUFFER and ERROR-BUFFER might be given.')
"
  (interactive "fDatei:")
  (let* ((coding-system-for-read 'utf-8)
         (coding-system-for-write 'utf-8)
         (exec-execfile (concat (make-temp-name (concat filename "-exec-execfile.py")))))
    (set-buffer (get-buffer-create exec-execfile))
    (insert header)
    (insert cmd)
    (write-file exec-execfile)
    (if output-buffer
        (progn
          (set-buffer (get-buffer-create output-buffer))
          (erase-buffer)
          (switch-to-buffer (current-buffer))
          (shell-command (concat "python " exec-execfile) output-buffer error-buffer))
      (with-temp-buffer
        (shell-command (concat "python " exec-execfile) output-buffer error-buffer)))))

;;; Execute forms
(defun py-execute-statement (&optional shell dedicated switch)
  "Send statement at point to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)"
  (interactive "P")
  (save-excursion
    (let ((beg (prog1
                   (or (py-beginning-of-statement-p)
                       (py-beginning-of-statement))))
          (end (py-end-of-statement)))
      (py-execute-region beg end shell dedicated switch))))

(defun py-execute-block (&optional shell dedicated switch)
  "Send block at point to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)"
  (interactive "P")
  (save-excursion
    (let ((beg (or (py-beginning-of-block-p)
                   (py-beginning-of-block)))
          (end (py-end-of-block)))
      (py-execute-region beg end shell dedicated switch))))

(defun py-execute-block-or-clause (&optional shell dedicated switch)
  "Send block-or-clause at point to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)"
  (interactive "P")
  (save-excursion
    (let ((beg (or (py-beginning-of-block-or-clause-p)
                   (py-beginning-of-block-or-clause)))
          (end (py-end-of-block-or-clause)))
      (py-execute-region beg end shell dedicated switch))))

(defun py-execute-def (&optional shell dedicated switch)
  "Send def at point to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)"
  (interactive "P")
  (save-excursion
    (let ((beg (or (py-beginning-of-def-p)
                   (py-beginning-of-def)))
          (end (py-end-of-def)))
      (py-execute-region beg end shell dedicated switch))))

(defun py-execute-class (&optional shell dedicated switch)
  "Send class at point to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)"
  (interactive "P")
  (save-excursion
    (let ((beg (or (py-beginning-of-class-p)
                   (py-beginning-of-class)))
          (end (py-end-of-class)))
      (py-execute-region beg end shell dedicated switch))))

(defun py-execute-def-or-class (&optional shell dedicated switch)
  "Send def-or-class at point to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)"
  (interactive "P")
  (save-excursion
    (let ((beg (or (py-beginning-of-def-or-class-p)
                   (py-beginning-of-def-or-class)))
          (end (py-end-of-def-or-class)))
      (py-execute-region beg end shell dedicated switch))))

(defun py-execute-expression (&optional shell dedicated switch)
  "Send expression at point to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)"
  (interactive "P")
  (save-excursion
    (let ((beg (or (py-beginning-of-expression-p)
                   (py-beginning-of-expression)))
          (end (py-end-of-expression)))
      (py-execute-region beg end shell dedicated switch))))

(defun py-execute-partial-expression (&optional shell dedicated switch)
  "Send partial-expression at point to a Python interpreter.

When called with \\[univeral-argument], execution through `default-value' of `py-shell-name' is forced.
See also `py-force-py-shell-name-p'.

When called with \\[univeral-argument] followed by a number different from 4 and 1, user is prompted to specify a shell. This might be the name of a system-wide shell or include the path to a virtual environment.

When called from a programm, it accepts a string specifying a shell which will be forced upon execute as argument.

Optional arguments DEDICATED (boolean) and SWITCH (symbols 'noswitch/'switch)"
  (interactive "P")
  (save-excursion
    (let ((beg (or (py-beginning-of-partial-expression-p)
                   (py-beginning-of-partial-expression)))
          (end (py-end-of-partial-expression)))
      (py-execute-region beg end shell dedicated switch))))

;;;
(defun py-execute-line ()
  "Send current line from beginning of indent to Python interpreter. "
  (interactive)
  (save-excursion
    (let ((beg (progn (back-to-indentation)
                      (point))))
      (py-execute-region beg (line-end-position)))))

(defun py-execute-file (&optional filename shell dedicated switch)
  "When called interactively, user is prompted for filename. "
  (interactive "fFile: ")
  (let* ((regbuf (current-buffer))
         (file (or (expand-file-name filename) (when (ignore-errors (file-readable-p (buffer-file-name))) (buffer-file-name))))
         (shell (or shell (progn (with-temp-buffer (insert-file-contents file)(py-choose-shell)))))
         (name (py-process-name shell dedicated))
         (proc (get-buffer-process (py-shell nil dedicated (or shell (downcase name)))))
         (procbuf (if dedicated
                      (buffer-name (get-buffer (current-buffer)))
                    (buffer-name (get-buffer (concat "*" name "*")))))
         (pec (if (string-match "Python3" name)
                  (format "exec(compile(open('%s').read(), '%s', 'exec')) # PYTHON-MODE\n" file file)
                (format "execfile(r'%s') # PYTHON-MODE\n" file)))
         (comint-scroll-to-bottom-on-output t))
    (if (file-readable-p file)
        (progn
          (setq erg (py-execute-file-base proc file pec))
          (setq py-exception-buffer (cons file (current-buffer)))
          (if (or (eq switch 'switch)
                  (and (not (eq switch 'noswitch)) py-switch-buffers-on-execute-p))
              (progn
                (pop-to-buffer procbuf)
                (goto-char (point-max)))
            (when (buffer-live-p regbuf) (pop-to-buffer regbuf))
            (when py-verbose-p (message "Output buffer: %s" procbuf)))
          (sit-for 0.1)
          erg)
      (message "File not readable: %s" "Do you have write permissions?"))))

(defun py-execute-file-base (proc filename &optional cmd procbuf)
  "Send to Python interpreter process PROC, in Python version 2.. \"execfile('FILENAME')\".

Make that process's buffer visible and force display.  Also make
comint believe the user typed this string so that
`kill-output-from-shell' does The Right Thing.
Returns position where output starts. "
  (let ((procbuf (or procbuf (process-buffer proc)))
        (comint-scroll-to-bottom-on-output t)
        (msg (format "## executing %s...\n" filename))
        (cmd (cond (cmd)
                   (py-exec-command)
                   (t (py-which-execute-file-command filename))))
        erg)
    (when py-verbose-p
      (unwind-protect
          (save-excursion
            (set-buffer procbuf)
            (funcall (process-filter proc) proc msg))))
    (set-buffer procbuf)
    (process-send-string proc cmd)
    (setq erg (goto-char (process-mark proc)))
    erg))

;;: Subprocess utilities and filters
(defvar py-last-exeption-buffer nil
  "Internal use only - when `py-up-exception' is called in
source-buffer, this will deliver the exception-buffer again. ")

(defun py-postprocess-output-buffer (buf)
  "Highlight exceptions found in BUF.
If an exception occurred return t, otherwise return nil.  BUF must exist."
  (let (line file bol err-p)
    (save-excursion
      (set-buffer buf)
      (goto-char (point-min))
      (while (re-search-forward py-traceback-line-re nil t)
        (setq file (match-string 1)
              line (string-to-number (match-string 2))
              bol (py-point 'bol))
        (overlay-put (make-overlay (match-beginning 0) (match-end 0))
                     'face 'highlight)))
    (when (and py-jump-on-exception line)
      (beep)
      (py-jump-to-exception file line py-line-number-offset)
      (setq err-p t))
    err-p))

(defun py-jump-to-exception (file line py-line-number-offset)
  "Jump to the Python code in FILE at LINE."
  (let ((buffer (cond ((string-equal file "<stdin>")
                       (if (consp py-exception-buffer)
                           (cdr py-exception-buffer)
                         py-exception-buffer))
                      ((and (consp py-exception-buffer)
                            (string-equal file (car py-exception-buffer)))
                       (cdr py-exception-buffer))
                      ((ignore-errors (find-file-noselect file)))
                      ;; could not figure out what file the exception
                      ;; is pointing to, so prompt for it
                      (t (find-file (read-file-name "Exception file: "
                                                    nil
                                                    file t))))))
    ;; Fiddle about with line number
    (setq line (+ py-line-number-offset line))

    (pop-to-buffer buffer)
    ;; Force Python mode
    (unless(eq major-mode 'python-mode)
      (python-mode))
    (goto-char (point-min))
    (forward-line (1- line))
    (message "Jumping to exception in file %s on line %d" file line)))

(defun py-down-exception (&optional bottom)
  "Go to the next line down in the traceback.

With \\[univeral-argument] (programmatically, optional argument
BOTTOM), jump to the bottom (innermost) exception in the exception
stack."
  (interactive "P")
  (py-find-next-exception-prepare 'down (when (eq 4 (prefix-numeric-value bottom)) "BOTTOM")))

(defun py-up-exception (&optional top)
  "Go to the previous line up in the traceback.

With \\[universal-argument] (programmatically, optional argument TOP)
jump to the top (outermost) exception in the exception stack."
  (interactive "P")
  (unless py-last-exeption-buffer (setq py-last-exeption-buffer (current-buffer)))
  (py-find-next-exception-prepare 'up (when (eq 4 (prefix-numeric-value top)) "TOP")))

(defun py-find-next-exception-prepare (direction start)
  "Setup exception regexps depending from kind of Python shell. "
  (let* ((name (get-process (substring (buffer-name (current-buffer)) 1 -1)))
         (buffer (cond (name (buffer-name (current-buffer)))
                       ((buffer-live-p (get-buffer py-output-buffer))
                        py-output-buffer)
                       (py-last-exeption-buffer (buffer-name py-last-exeption-buffer))
                       (t (error "Don't see exeption buffer")))))
    (when buffer (set-buffer (get-buffer buffer)))
    (switch-to-buffer (current-buffer))
    (if (eq direction 'up)
        (if (string= start "TOP")
            (py-find-next-exception 'bob buffer 're-search-forward "Top")
          (py-find-next-exception 'bol buffer 're-search-backward "Top"))
      (if (string= start "BOTTOM")
          (py-find-next-exception 'eob buffer 're-search-backward "Bottom")
        (py-find-next-exception 'eol buffer 're-search-forward "Bottom")))))

(defun py-find-next-exception (start buffer searchdir errwhere)
  "Find the next Python exception and jump to the code that caused it.
START is the buffer position in BUFFER from which to begin searching
for an exception.  SEARCHDIR is a function, either
`re-search-backward' or `re-search-forward' indicating the direction
to search.  ERRWHERE is used in an error message if the limit (top or
bottom) of the trackback stack is encountered."
  (let ((orig (point))
        (origline (py-count-lines))
        file line pos)
    (goto-char (py-point start))
    (if (funcall searchdir py-traceback-line-re nil t)
        (if (save-match-data (eq (py-count-lines) origline))
            (progn
              (forward-line (if (string= errwhere "Top") -1 1))
              (py-find-next-exception start buffer searchdir errwhere))
          (if (not (save-match-data (string-match "^IPython\\|^In \\[[0-9]+\\]: *\\|^>>>" (match-string-no-properties 0))))
              (progn
                (setq py-last-exeption-buffer (current-buffer))
                (if (save-match-data (string-match "File" (match-string-no-properties 0)))
                    (progn
                      (setq file (match-string-no-properties 2)
                            pos (point)
                            line (string-to-number (match-string-no-properties 3))))
                  (save-excursion
                    ;; file and line-number are in different lines
                    (setq line (string-to-number (match-string-no-properties 1))
                          pos (point)
                          file (progn
                                 (when (and (re-search-backward "\\(^IPython\\|^In \\[[0-9]+\\]: *\\|^>>>\\|^[^\t >]+\\)>?[ \t]+in[ \t]+\\([^ \t\n]+\\)" nil t 1)
                                            (not (save-match-data (string-match "<\\|^IPython\\|^In \\[[0-9]+\\]: *\\|^>>>" (match-string-no-properties 1)))))
                                   (match-string-no-properties 1))))))
                (if file
                    (when (string-match ".+\.pyc" file)
                      (setq file (substring file 0 -1)))
                  (error "%s of traceback" errwhere))
                (if (and file line)
                    (if
                        (and (string= "<stdin>" file) (eq 1 line))
                        (error "%s of traceback" errwhere)
                      (py-jump-to-exception file line py-line-number-offset))
                  (error "%s of traceback" errwhere)))
            (goto-char orig)
            (error "%s of traceback" errwhere))))))

;;; python-mode-send.el

(defun py-output-buffer-filter (&optional beg end)
  "Clear output buffer from py-shell-input prompt etc. "
  (interactive "*")
  (let ((beg (cond (beg)
                   ((region-active-p)
                    (region-beginning))
                   (t (point-min))))
        (end (cond (end (copy-marker end))
                   ((region-active-p)
                    (copy-marker (region-end)))
                   (t (copy-marker (point-max))))))
    (goto-char beg)
    (while (re-search-forward (concat "\\(" py-shell-input-prompt-1-regexp "\\|" py-shell-input-prompt-2-regexp "\\|" "^In \\[[0-9]+\\]: *" "\\)") nil (quote move) 1)
      (replace-match ""))
    (goto-char beg)))

(defun py-send-string (string)
  "Evaluate STRING in inferior Python process."
  (interactive "sPython command: ")
  (comint-send-string (py-proc) string)
  (unless (string-match "\n\\'" string)
    ;; Make sure the text is properly LF-terminated.
    (comint-send-string (py-proc) "\n"))
  (when (string-match "\n[ \t].*\n?\\'" string)
    ;; If the string contains a final indented line, add a second newline so
    ;; as to make sure we terminate the multiline instruction.
    (comint-send-string (py-proc) "\n")))

;;; python-components-pdb.el

;;; Pdbtrack

(defun py-pdbtrack-overlay-arrow (activation)
  "Activate or de arrow at beginning-of-line in current buffer."
  ;; This was derived/simplified from edebug-overlay-arrow
  (cond (activation
         (setq overlay-arrow-position (make-marker))
         (setq overlay-arrow-string "=>")
         (set-marker overlay-arrow-position (line-beginning-position) (current-buffer))
         (setq py-pdbtrack-is-tracking-p t))
        (overlay-arrow-position
         (setq overlay-arrow-position nil)
         (setq py-pdbtrack-is-tracking-p nil))))

(defun py-pdbtrack-track-stack-file (text)
  "Show the file indicated by the pdb stack entry line, in a separate window.

Activity is disabled if the buffer-local variable
`py-pdbtrack-do-tracking-p' is nil.

We depend on the pdb input prompt matching `py-pdbtrack-input-prompt'
at the beginning of the line.

If the traceback target file path is invalid, we look for the most
recently visited python-mode buffer which either has the name of the
current function \(or class) or which defines the function \(or
class).  This is to provide for remote scripts, eg, Zope's 'Script
\(Python)' - put a _copy_ of the script in a buffer named for the
script, and set to python-mode, and pdbtrack will find it.)"
  ;; Instead of trying to piece things together from partial text
  ;; (which can be almost useless depending on Emacs version), we
  ;; monitor to the point where we have the next pdb prompt, and then
  ;; check all text from comint-last-input-end to process-mark.
  ;;
  ;; Also, we're very conservative about clearing the overlay arrow,
  ;; to minimize residue.  This means, for instance, that executing
  ;; other pdb commands wipe out the highlight.  You can always do a
  ;; 'where' (aka 'w') command to reveal the overlay arrow.
  (let* ((origbuf (current-buffer))
         (currproc (get-buffer-process origbuf)))

    (if (not (and currproc py-pdbtrack-do-tracking-p))
        (py-pdbtrack-overlay-arrow nil)

      (let* ((procmark (process-mark currproc))
             (block (buffer-substring (max comint-last-input-end
                                           (- procmark
                                              py-pdbtrack-track-range))
                                      procmark))
             target target_fname target_lineno target_buffer)

        (if (not (string-match (concat py-pdbtrack-input-prompt "$") block))
            (py-pdbtrack-overlay-arrow nil)

          (setq target (py-pdbtrack-get-source-buffer block))

          (if (stringp target)
              (message "pdbtrack: %s" target)

            (setq target_lineno (car target))
            (setq target_buffer (cadr target))
            (setq target_fname (buffer-file-name target_buffer))
            (switch-to-buffer-other-window target_buffer)
            (goto-char (point-min))
            (forward-line (1- target_lineno))
            (message "pdbtrack: line %s, file %s" target_lineno target_fname)
            (py-pdbtrack-overlay-arrow t)
            (pop-to-buffer origbuf t)))))))

(defun py-pdbtrack-map-filename (filename)

  (let
      ((replacement-val (assoc-default
                         filename py-pdbtrack-filename-mapping
                         (lambda (mapkey path)
                           (string-match
                            (concat "^" (regexp-quote mapkey))
                            path)))
                        ))
    (if (not (eq replacement-val nil))
        (replace-match replacement-val 't 't filename)
      filename)))

(defun py-pdbtrack-get-source-buffer (block)
  "Return line number and buffer of code indicated by block's traceback text.

We look first to visit the file indicated in the trace.

Failing that, we look for the most recently visited python-mode buffer
with the same name or having the named function.

If we're unable find the source code we return a string describing the
problem as best as we can determine."

  (if (and (not (string-match py-pdbtrack-stack-entry-regexp block))
           ;; pydb integration still to be done
	   ;; (not (string-match py-pydbtrack-stack-entry-regexp block))
           )
      "Traceback cue not found"
    (let* ((filename (match-string
		      py-pdbtrack-marker-regexp-file-group block))
           (lineno (string-to-number (match-string
                                      py-pdbtrack-marker-regexp-line-group
                                      block)))
           (funcname (match-string py-pdbtrack-marker-regexp-funcname-group
				   block))
           funcbuffer)

      (cond ((file-exists-p filename)
             (list lineno (find-file-noselect filename)))

            ((file-exists-p (py-pdbtrack-map-filename filename))
             (list lineno (find-file-noselect (py-pdbtrack-map-filename filename))))

            ((setq funcbuffer (py-pdbtrack-grub-for-buffer funcname lineno))
             (if (string-match "/Script (Python)$" filename)
                 ;; Add in number of lines for leading '##' comments:
                 (setq lineno
                       (+ lineno
                          (save-excursion
                            (set-buffer funcbuffer)
                            (count-lines
                             (point-min)
                             (max (point-min)
                                  (string-match "^\\([^#]\\|#[^#]\\|#$\\)"
                                                (buffer-substring (point-min)
                                                                  (point-max)))))))))
             (list lineno funcbuffer))

            ((= (elt filename 0) ?\<)
             (format "(Non-file source: '%s')" filename))

            (t (format "Not found: %s(), %s" funcname filename))))))

(defun py-pdbtrack-grub-for-buffer (funcname lineno)
  "Find most recent buffer itself named or having function funcname.

We walk the buffer-list history for python-mode buffers that are
named for funcname or define a function funcname."
  (let ((buffers (buffer-list))
        buf
        got)
    (while (and buffers (not got))
      (setq buf (car buffers)
            buffers (cdr buffers))
      (if (and (save-excursion (set-buffer buf)
                               (string= major-mode "python-mode"))
               (or (string-match funcname (buffer-name buf))
                   (string-match (concat "^\\s-*\\(def\\|class\\)\\s-+"
                                         funcname "\\s-*(")
                                 (save-excursion
                                   (set-buffer buf)
                                   (buffer-substring (point-min)
                                                     (point-max))))))
          (setq got buf)))
    got))


;; pdbtrack functions
(defun py-pdbtrack-toggle-stack-tracking (arg)
  "Set variable `py-pdbtrack-do-tracking-p'. "
  (interactive "P")
  (if (not (get-buffer-process (current-buffer)))
      (error "No process associated with buffer '%s'" (current-buffer)))
  ;; missing or 0 is toggle, >0 turn on, <0 turn off
  (if (or (not arg)
          (zerop (setq arg (prefix-numeric-value arg))))
      (setq py-pdbtrack-do-tracking-p (not py-pdbtrack-do-tracking-p))
    (setq py-pdbtrack-do-tracking-p (> arg 0)))
  (message "%sabled Python's pdbtrack"
           (if py-pdbtrack-do-tracking-p "En" "Dis")))

(defun turn-on-pdbtrack ()
  (interactive)
  (py-pdbtrack-toggle-stack-tracking 1))

(defun turn-off-pdbtrack ()
  (interactive)
  (py-pdbtrack-toggle-stack-tracking 0))

;;; python-components-help.el

(defun py-fetch-docu ()
  "Lookup in current buffer for the doku for the symbol at point.

Useful for newly defined symbol, not known to python yet. "
  (interactive)
  (let* ((symb (prin1-to-string (symbol-at-point)))
         (args (py-expression))
         erg)
    (save-restriction
      (widen)
      (goto-char (point-min))
      (when (re-search-forward (concat py-def-or-class-re " *" symb) nil (quote move) 1)
        (forward-line 1)
        (when (looking-at "[ \t]*\"\"\"\\|[ \t]*'''\\|[ \t]*'[^]+\\|[ \t]*\"[^\"]+")
          (goto-char (match-end 0))
          (setq erg (buffer-substring-no-properties (match-beginning 0) (re-search-forward "\"\"\"\\|'''" nil 'move)))
          (when erg
            (set-buffer (get-buffer-create "*Python-Help*"))
            (erase-buffer)
            (when (and py-verbose-p (interactive-p)) (switch-to-buffer (current-buffer)))
            (insert erg)))))))

(defun py-find-imports ()
  "Find top-level imports, updating `python-imports'."
  (interactive)
  (let* (imports)
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward
              "^import *[A-Za-z_][A-Za-z_0-9].*\\|^from +[A-Za-z_][A-Za-z_0-9]+ +import .*" nil t)
        (setq imports
              (concat
               imports
               (buffer-substring-no-properties (match-beginning 0) (match-end 0)) ";"))))
    (when (and py-verbose-p (interactive-p)) (message "%s" imports))
    imports))

(defun py-eldoc-function ()
  "Print help on symbol at point. "
  (interactive)
  (if (unless (looking-at " ")
        (or

         (eq (get-char-property (point) 'face) 'font-lock-keyword-face)
         (eq (get-char-property (point) 'face) 'py-builtins-face)
         (eq (get-char-property (point) 'face) 'py-exception-name-face)
         (eq (get-char-property (point) 'face) 'py-class-name-face)

         ))

      (lexical-let* ((sym (prin1-to-string (symbol-at-point)))
                     (origfile (buffer-file-name))
                     (temp (make-temp-name (buffer-name)))
                     (file (concat (expand-file-name temp py-temp-directory) ".py"))
                     (cmd (py-find-imports))
                     (no-quotes (save-excursion
                                  (skip-chars-backward "A-Za-z_0-9.")
                                  (and (looking-at "[A-Za-z_0-9.]+")
                                       (string-match "\\." (match-string-no-properties 0))))))
        (setq cmd (concat "import pydoc\n"
                          cmd))
        (if no-quotes
            (setq cmd (concat cmd
                              "try: pydoc.help(" sym ")\n"))
          (setq cmd (concat cmd "try: pydoc.help('" sym "')\n")))
        (setq cmd (concat cmd
                          "except:
    print 'No help available on:', \"" sym "\""))
        (with-temp-buffer
          (insert cmd)
          (write-file file))
        (py-process-file file "*Python-Help*")
        (when (file-readable-p file)
          (delete-file file)))
    (delete-other-windows)))

(defalias 'py-help-at-point 'py-describe-symbol)
(defun py-describe-symbol (&optional arg)
  "Print help on symbol at point.

Optional \\[universal-argument] used for debugging, will prevent deletion of temp file. "
  (interactive "P")
  (let* ((orig (point))
         (beg (progn (when (and (looking-back "(")(not (looking-at "\\sw"))) (forward-char -1))  (skip-chars-backward "a-zA-Z0-9_." (line-beginning-position))(point)))
         (end (progn (skip-chars-forward "a-zA-Z0-9_." (line-end-position))(point)))
         (sym (buffer-substring-no-properties beg end))
         (origfile (buffer-file-name))
         (temp (make-temp-name (buffer-name)))
         (file (concat (expand-file-name temp py-temp-directory) ".py"))
         (cmd (py-find-imports)))
    (goto-char orig)
    (setq cmd (concat "import pydoc\n"
                      cmd))
    (setq cmd (concat cmd "pydoc.help('" sym "')\n"))
    (with-temp-buffer
      (insert cmd)
      (write-file file))
    (py-process-file file "*Python-Help*")
    (when (file-readable-p file)
      (unless (eq 4 (prefix-numeric-value arg)) (delete-file file)))))


;;; Documentation
(defun py-dump-help-string (str)
  (with-output-to-temp-buffer "*Help*"
    (let ((locals (buffer-local-variables))
          funckind funcname func funcdoc
          (start 0) mstart end
          keys)
      (while (string-match "^%\\([vc]\\):\\(.+\\)\n" str start)
        (setq mstart (match-beginning 0) end (match-end 0)
              funckind (substring str (match-beginning 1) (match-end 1))
              funcname (substring str (match-beginning 2) (match-end 2))
              func (intern funcname))
        (princ (substitute-command-keys (substring str start mstart)))
        (cond
         ((equal funckind "c")          ; command
          (setq funcdoc (documentation func)
                keys (concat
                      "Key(s): "
                      (mapconcat 'key-description
                                 (where-is-internal func python-mode-map)
                                 ", "))))
         ((equal funckind "v")          ; variable
          (setq funcdoc (documentation-property func 'variable-documentation)
                keys (if (assq func locals)
                         (concat
                          "Local/Global values: "
                          (prin1-to-string (symbol-value func))
                          " / "
                          (prin1-to-string (default-value func)))
                       (concat
                        "Value: "
                        (prin1-to-string (symbol-value func))))))
         (t                             ; unexpected
          (error "Error in py-dump-help-string, tag `%s'" funckind)))
        (princ (format "\n-> %s:\t%s\t%s\n\n"
                       (if (equal funckind "c") "Command" "Variable")
                       funcname keys))
        (princ funcdoc)
        (terpri)
        (setq start end))
      (princ (substitute-command-keys (substring str start))))
    (if (featurep 'xemacs) (print-help-return-message)
      (help-print-return-message))))

(add-hook 'python-mode-hook
          (lambda ()
            (setq indent-tabs-mode py-indent-tabs-mode)
            (set (make-local-variable 'beginning-of-defun-function) 'py-beginning-of-def-or-class)
            (set (make-local-variable 'end-of-defun-function) 'py-end-of-def-or-class)
            ;; (orgstruct-mode 1)
            ))

(defun py-describe-mode ()
  "Dump long form of `python-mode' docs."
  (interactive)
  (py-dump-help-string "Major mode for editing Python files.
Knows about Python indentation, tokens, comments and continuation lines.
Paragraphs are separated by blank lines only.

Major sections below begin with the string `@'; specific function and
variable docs begin with `->'.

@EXECUTING PYTHON CODE

\\[py-execute-import-or-reload]\timports or reloads the file in the Python interpreter
\\[py-execute-buffer]\tsends the entire buffer to the Python interpreter
\\[py-execute-region]\tsends the current region
\\[py-execute-def-or-class]\tsends the current function or class definition
\\[py-execute-string]\tsends an arbitrary string
\\[py-shell]\tstarts a Python interpreter window; this will be used by
\tsubsequent Python execution commands
%c:py-execute-import-or-reload
%c:py-execute-buffer
%c:py-execute-region
%c:py-execute-def-or-class
%c:py-execute-string
%c:py-shell

@VARIABLES

py-install-directory\twherefrom `python-mode' looks for extensions
py-indent-offset\tindentation increment
py-block-comment-prefix\tcomment string used by comment-region

py-shell-name\tshell command to invoke Python interpreter
py-temp-directory\tdirectory used for temp files (if needed)

py-beep-if-tab-change\tring the bell if tab-width is changed
%v:py-install-directory
%v:py-indent-offset
%v:py-block-comment-prefix
%v:py-shell-name
%v:py-temp-directory
%v:py-beep-if-tab-change

@KINDS OF LINES

Each physical line in the file is either a `continuation line' (the
preceding line ends with a backslash that's not part of a comment, or
the paren/bracket/brace nesting level at the start of the line is
non-zero, or both) or an `initial line' (everything else).

An initial line is in turn a `blank line' (contains nothing except
possibly blanks or tabs), a `comment line' (leftmost non-blank
character is `#'), or a `code line' (everything else).

Comment Lines

Although all comment lines are treated alike by Python, Python mode
recognizes two kinds that act differently with respect to indentation.

An `indenting comment line' is a comment line with a blank, tab or
nothing after the initial `#'.  The indentation commands (see below)
treat these exactly as if they were code lines: a line following an
indenting comment line will be indented like the comment line.  All
other comment lines (those with a non-whitespace character immediately
following the initial `#') are `non-indenting comment lines', and
their indentation is ignored by the indentation commands.

Indenting comment lines are by far the usual case, and should be used
whenever possible.  Non-indenting comment lines are useful in cases
like these:

\ta = b # a very wordy single-line comment that ends up being
\t #... continued onto another line

\tif a == b:
##\t\tprint 'panic!' # old code we've `commented out'
\t\treturn a

Since the `#...' and `##' comment lines have a non-whitespace
character following the initial `#', Python mode ignores them when
computing the proper indentation for the next line.

Continuation Lines and Statements

The `python-mode' commands generally work on statements instead of on
individual lines, where a `statement' is a comment or blank line, or a
code line and all of its following continuation lines (if any)
considered as a single logical unit.  The commands in this mode
generally (when it makes sense) automatically move to the start of the
statement containing point, even if point happens to be in the middle
of some continuation line.

@INDENTATION

Primarily for entering new code:
\t\\[indent-for-tab-command]\t indent line appropriately
\t\\[py-newline-and-indent]\t insert newline, then indent
\t\\[py-electric-backspace]\t reduce indentation, or delete single character

Primarily for reindenting existing code:
\t\\[py-guess-indent-offset]\t guess py-indent-offset from file content; change locally
\t\\[universal-argument] \\[py-guess-indent-offset]\t ditto, but change globally

\t\\[py-indent-region]\t reindent region to match its context
\t\\[py-shift-left]\t shift line or region left by py-indent-offset
\t\\[py-shift-right]\t shift line or region right by py-indent-offset

Unlike most programming languages, Python uses indentation, and only
indentation, to specify block structure.  Hence the indentation supplied
automatically by `python-mode' is just an educated guess:  only you know
the block structure you intend, so only you can supply correct
indentation.

The \\[indent-for-tab-command] and \\[py-newline-and-indent] keys try to suggest plausible indentation, based on
the indentation of preceding statements.  E.g., assuming
py-indent-offset is 4, after you enter
\tif a > 0: \\[py-newline-and-indent]
the cursor will be moved to the position of the `_' (_ is not a
character in the file, it's just used here to indicate the location of
the cursor):
\tif a > 0:
\t _
If you then enter `c = d' \\[py-newline-and-indent], the cursor will move
to
\tif a > 0:
\t c = d
\t _
`python-mode' cannot know whether that's what you intended, or whether
\tif a > 0:
\t c = d
\t_
was your intent.  In general, `python-mode' either reproduces the
indentation of the (closest code or indenting-comment) preceding
statement, or adds an extra py-indent-offset blanks if the preceding
statement has `:' as its last significant (non-whitespace and non-
comment) character.  If the suggested indentation is too much, use
\\[py-electric-backspace] to reduce it.

Continuation lines are given extra indentation.  If you don't like the
suggested indentation, change it to something you do like, and Python-
mode will strive to indent later lines of the statement in the same way.

If a line is a continuation line by virtue of being in an unclosed
paren/bracket/brace structure (`list', for short), the suggested
indentation depends on whether the current line contains the first item
in the list.  If it does, it's indented py-indent-offset columns beyond
the indentation of the line containing the open bracket.  If you don't
like that, change it by hand.  The remaining items in the list will mimic
whatever indentation you give to the first item.

If a line is a continuation line because the line preceding it ends with
a backslash, the third and following lines of the statement inherit their
indentation from the line preceding them.  The indentation of the second
line in the statement depends on the form of the first (base) line:  if
the base line is an assignment statement with anything more interesting
than the backslash following the leftmost assigning `=', the second line
is indented two columns beyond that `='.  Else it's indented to two
columns beyond the leftmost solid chunk of non-whitespace characters on
the base line.

Warning:  indent-region should not normally be used!  It calls \\[indent-for-tab-command]
repeatedly, and as explained above, \\[indent-for-tab-command] can't guess the block
structure you intend.
%c:indent-for-tab-command
%c:py-newline-and-indent
%c:py-electric-backspace

The next function may be handy when editing code you didn't write:
%c:py-guess-indent-offset

The remaining `indent' functions apply to a region of Python code.  They
assume the block structure (equals indentation, in Python) of the region
is correct, and alter the indentation in various ways while preserving
the block structure:
%c:py-indent-region
%c:py-shift-left
%c:py-shift-right

@MARKING & MANIPULATING REGIONS OF CODE

\\[py-mark-block]\t mark block of lines
\\[py-mark-def-or-class]\t mark smallest enclosing def
\\[universal-argument] \\[py-mark-def-or-class]\t mark smallest enclosing class
\\[comment-region]\t comment out region of code
\\[universal-argument] \\[comment-region]\t uncomment region of code
%c:py-mark-block
%c:py-mark-def-or-class
%c:comment-region

@MOVING POINT

\\[py-previous-statement]\t move to statement preceding point
\\[py-next-statement]\t move to statement following point
\\[py-goto-block-up]\t move up to start of current block
\\[py-beginning-of-def-or-class]\t move to start of def
\\[universal-argument] \\[py-beginning-of-def-or-class]\t move to start of class
\\[py-end-of-def-or-class]\t move to end of def
\\[universal-argument] \\[py-end-of-def-or-class]\t move to end of class

The first two move to one statement beyond the statement that contains
point.  A numeric prefix argument tells them to move that many
statements instead.  Blank lines, comment lines, and continuation lines
do not count as `statements' for these commands.  So, e.g., you can go
to the first code statement in a file by entering
\t\\[beginning-of-buffer]\t to move to the top of the file
\t\\[py-next-statement]\t to skip over initial comments and blank lines
Or do `\\[py-previous-statement]' with a huge prefix argument.
%c:py-previous-statement
%c:py-next-statement
%c:py-goto-block-up
%c:py-beginning-of-def-or-class
%c:py-end-of-def-or-class

@LITTLE-KNOWN EMACS COMMANDS PARTICULARLY USEFUL IN PYTHON MODE

`\\[indent-new-comment-line]' is handy for entering a multi-line comment.

`\\[set-selective-display]' with a `small' prefix arg is ideally suited for viewing the
overall class and def structure of a module.

`\\[back-to-indentation]' moves point to a line's first non-blank character.

`\\[indent-relative]' is handy for creating odd indentation.

@OTHER EMACS HINTS

If you don't like the default value of a variable, change its value to
whatever you do like by putting a `setq' line in your .emacs file.
E.g., to set the indentation increment to 4, put this line in your
.emacs:
\t(setq py-indent-offset 4)
To see the value of a variable, do `\\[describe-variable]' and enter the variable
name at the prompt.

When entering a key sequence like `C-c C-n', it is not necessary to
release the CONTROL key after doing the `C-c' part -- it suffices to
press the CONTROL key, press and release `c' (while still holding down
CONTROL), press and release `n' (while still holding down CONTROL), &
then release CONTROL.

Entering Python mode calls with no arguments the value of the variable
`python-mode-hook', if that value exists and is not nil; for backward
compatibility it also tries `py-mode-hook'; see the `Hooks' section of
the Elisp manual for details.

Obscure:  When python-mode is first loaded, it looks for all bindings
to newline-and-indent in the global keymap, and shadows them with
local bindings to py-newline-and-indent."))

;; (require 'info-look)
;; The info-look package does not always provide this function (it
;; appears this is the case with XEmacs 21.1)
(when (fboundp 'info-lookup-maybe-add-help)
  (info-lookup-maybe-add-help
   :mode 'python-mode
   :regexp "[a-zA-Z0-9_]+"
   :doc-spec '(("(python-lib)Module Index")
               ("(python-lib)Class-Exception-Object Index")
               ("(python-lib)Function-Method-Variable Index")
               ("(python-lib)Miscellaneous Index"))))

(defvar python-preoutput-result nil
  "Data from last `_emacs_out' line seen by the preoutput filter.")

(defun py-send-receive (string)
  "Send STRING to inferior Python (if any) and return result.

The result is what follows `_emacs_out' in the output.
This is a no-op if `python-check-comint-prompt' returns nil."
  (py-send-string string)
  (let ((proc (py-proc)))
    (with-current-buffer (process-buffer proc)
      (when (python-check-comint-prompt proc)
	(set (make-local-variable 'python-preoutput-result) nil)
        (accept-process-output proc py-send-receive-delay)
        (if (null python-preoutput-result)
            (message "No output from: %s, maybe set `py-send-receive-delay' onto a higher value " string))
	(prog1 python-preoutput-result
	  (kill-local-variable 'python-preoutput-result))))))

(defun py-find-function (name)
  "Find source of definition of function NAME.

Interactively, prompt for name."
  (interactive
   (let ((symbol (with-syntax-table py-dotted-expression-syntax-table
		   (current-word)))
	 (enable-recursive-minibuffers t))
     (list (read-string (if symbol
			    (format "Find location of (default %s): " symbol)
			  "Find location of: ")
			nil nil symbol))))
  (unless python-imports
    (error "Not called from buffer visiting Python file"))
  (let* ((loc (py-send-receive (format "emacs.location_of (%S, %s)"
                                       name python-imports)))
	 (loc (car (read-from-string loc)))
	 (file (car loc))
	 (line (cdr loc)))
    (unless file (error "Don't know where `%s' is defined" name))
    (pop-to-buffer (find-file-noselect file))
    (when (integerp line)
      (goto-char (point-min))
      (forward-line (1- line)))))

(defun py-update-imports ()
  "Returns `python-imports'.

Imports done are displayed in message buffer. "
  (interactive)
  (save-excursion
    (let ((oldbuf (current-buffer))
          (orig (point))
          erg)
      (mapc 'py-execute-string (split-string (car (read-from-string (py-find-imports))) "\n" t))
      (setq erg (car (read-from-string python-imports)))
      (set-buffer oldbuf)
      (goto-char orig)
      (when (interactive-p)
        (switch-to-buffer (current-buffer))
        (when py-verbose-p (message "%s" erg)))
      erg)))

;;; python-components-extensions.el

(defun py-indent-forward-line (&optional arg)
  "Indent and move one line forward to next indentation.
Returns column of line reached.

If `py-kill-empty-line' is non-nil, delete an empty line.
When closing a form, use py-close-block et al, which will move and indent likewise.
With \\[universal argument] just indent.
"
  (interactive "*P")
  (let ((orig (point))
        erg)
    (unless (eobp)
      (if (and (py-in-comment-p)(not py-indent-comments))
          (forward-line 1)
        (py-indent-line-outmost)
        (unless (eq 4 (prefix-numeric-value arg))
          (if (eobp) (newline)
            (progn (forward-line 1))
            (when (and py-kill-empty-line (empty-line-p) (not (looking-at "[ \t]*\n[[:alpha:]]")) (not (eobp)))
              (delete-region (line-beginning-position) (line-end-position)))))))
    (back-to-indentation)
    (when (or (eq 4 (prefix-numeric-value arg)) (< orig (point))) (setq erg (current-column)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-dedent-forward-line (&optional arg)
  "Dedent line and move one line forward. "
  (interactive "*p")
  (py-dedent arg)
  (forward-line 1)
  (end-of-line)
  (skip-chars-backward " \t\r\n\f"))

(defun py-dedent (&optional arg)
  "Dedent line according to `py-indent-offset'.

With arg, do it that many times.
If point is between indent levels, dedent to next level.
Return indentation reached, if dedent done, nil otherwise.

Affected by `py-dedent-keep-relative-column'. "
  (interactive "*p")
  (let ((orig (copy-marker (point)))
        erg)
    (dotimes (i arg)
      (let* ((cui (current-indentation))
             (remain (% cui py-indent-offset))
             (indent (* py-indent-offset (/ cui py-indent-offset))))
        (beginning-of-line)
        (fixup-whitespace)
        (if (< 0 remain)
            (indent-to-column indent)
          (indent-to-column (- cui py-indent-offset)))))
    (when (< (point) orig)
      (setq erg (current-column)))
    (if py-dedent-keep-relative-column
        (goto-char orig)
      (end-of-line)
      (skip-chars-backward " \t\r\n\f"))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-close-intern (regexp)
  "Core function, internal used only. "
  (let ((cui (ignore-errors (car (py-go-to-keyword regexp)))))
    (py-end-base regexp (point))
    (forward-line 1)
    (if py-close-provides-newline
        (unless (empty-line-p) (split-line))
      (fixup-whitespace))
    (indent-to-column cui)
    cui))

(defun py-close-def ()
  "Set indent level to that of beginning of function definition.

If final line isn't empty and `py-close-block-provides-newline' non-nil, insert a newline. "
  (interactive "*")
  (let ((erg (py-close-intern py-def-re)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-close-class ()
  "Set indent level to that of beginning of class definition.

If final line isn't empty and `py-close-block-provides-newline' non-nil, insert a newline. "
  (interactive "*")
  (let ((erg (py-close-intern py-class-re)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-close-clause ()
  "Set indent level to that of beginning of clause definition.

If final line isn't empty and `py-close-block-provides-newline' non-nil, insert a newline. "
  (interactive "*")
  (let ((erg (py-close-intern py-clause-re)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-close-block ()
  "Set indent level to that of beginning of block definition.

If final line isn't empty and `py-close-block-provides-newline' non-nil, insert a newline. "
  (interactive "*")
  (let ((erg (py-close-intern py-block-re)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-class-at-point ()
  "Return class definition as string.

With interactive call, send it to the message buffer too. "
  (interactive)
  (save-excursion
    (let* ((beg (py-beginning-of-class))
	   (end (py-end-of-class))
	   (res (when (and (numberp beg)(numberp end)(< beg end)) (buffer-substring-no-properties beg end))))
      (when (and py-verbose-p (interactive-p)) (message "%s" res))
      res)))

(defun py-line-at-point ()
  "Return line as string.
  With interactive call, send it to the message buffer too. "
  (interactive)
  (let* ((beg (line-beginning-position))
	 (end (line-end-position))
	 (res (when (and (numberp beg)(numberp end)(< beg end)) (buffer-substring-no-properties beg end))))
    (when (and py-verbose-p (interactive-p)) (message "%s" res))
    res))

(defun py-looking-at-keywords-p ()
  "If looking at a python keyword. Returns t or nil. "
  (interactive)
  (let* ((kwds1 (car (nth 1 (eval (eval (quote (car font-lock-defaults)))))))
         (kwds3 (car (nth 3 (eval (eval (quote (car font-lock-defaults)))))))
	 (res
	  (or
           (looking-at kwds1)
           (looking-at kwds3))))
    (when (and py-verbose-p (interactive-p)) (message "looking-at keywords: %s" res))
    res))

(defun py-match-paren-mode (&optional arg)
  "py-match-paren-mode nil oder t"
  (interactive "P")
  (if (or (eq 4 (prefix-numeric-value arg)) (not py-match-paren-mode))
      (setq py-match-paren-mode t)
    (setq py-match-paren-mode nil)))

(defun py-match-paren ()
  "Goto to the opening or closing of block before or after point.

With arg, do it that many times.
 Closes unclosed block if jumping from beginning. "
  (interactive)
  (let ((cuc (current-column))
	(cid (current-indentation)))
    (py-beginning-of-block-or-clause)
    (if (< cuc (current-indentation))
	(goto-char cuc)
      (back-to-indentation)
      (when (eq (point) cuc)
	(py-end-of-block)))))

;;; from string-strip.el --- Strip CHARS from STRING

;; (setq strip-chars-before  "[ \t\r\n]*")
(defcustom strip-chars-before  "[ \t\r\n]*"
  "Regexp indicating which chars shall be stripped before STRING - which is defined by `string-chars-preserve'."

  :type 'string
  :group 'convenience)

;; (setq strip-chars-after  "[ \t\r\n]*")
(defcustom strip-chars-after  "[ \t\r\n]*\\'"
  "Regexp indicating which chars shall be stripped after STRING - which is defined by `string-chars-preserve'."

  :type 'string
  :group 'convenience)

(defcustom string-chars-preserve "\\(.*?\\)"
  "Chars preserved of STRING.
`strip-chars-after' and
`strip-chars-before' indicate what class of chars to strip."
  :type 'string
  :group 'convenience)

(defun string-strip (str &optional chars-before chars-after chars-preserve)
  "Return a copy of STR, CHARS removed.
`CHARS-BEFORE' and `CHARS-AFTER' default is \"[ \t\r\n]*\",
i.e. spaces, tabs, carriage returns, newlines and newpages.
`CHARS-PRESERVE' must be a parentized expression,
it defaults to \"\\(.*?\\)\""
  (let ((s-c-b (or chars-before
                   strip-chars-before))
        (s-c-a (or chars-after
                   strip-chars-after))
        (s-c-p (or chars-preserve
                   string-chars-preserve)))
    (string-match
     (concat "\\`[" s-c-b"]*" s-c-p "[" s-c-a "]*\\'") str)
    (match-string 1 str)))

;;;

(defalias 'druck 'py-printform-insert)
(defun py-printform-insert (&optional arg)
  "Inserts a print statement out of current `(car kill-ring)' by default, inserts ARG instead if delivered. "
  (interactive "*")
  (lexical-let* ((name (string-strip (or arg (car kill-ring))))
                 (form (cond ((eq major-mode 'python-mode)
                              (concat "print \"" name ": %s \" % " name)))))
    (insert form)))

(defun py-documentation (w)
  "Launch PyDOC on the Word at Point"
  (interactive
   (list (let* ((word (thing-at-point 'word))
                (input (read-string
                        (format "pydoc entry%s: "
                                (if (not word) "" (format " (default %s)" word))))))
           (if (string= input "")
               (if (not word) (error "No pydoc args given")
                 word) ;sinon word
             input)))) ;sinon input
  (shell-command (concat py-shell-name " -c \"from pydoc import help;help(\'" w "\')\"") "*PYDOCS*")
  (view-buffer-other-window "*PYDOCS*" t 'kill-buffer-and-window))

(defun eva ()
  "Put \"eval(...)\" forms around strings at point. "
  (interactive "*")
  (skip-chars-forward " \t\r\n\f")
  (let* ((bounds (ar-bounds-of-word-atpt))
         (beg (car bounds))
         (end (cdr bounds)))
    (goto-char end)
    (insert ")")
    (goto-char beg)
    (insert "eval(")))

(defun pst-here ()
  "Kill previous \"pdb.set_trace()\" and insert it at point. "
  (interactive "*")
  (let ((orig (copy-marker (point))))
    (search-backward "pdb.set_trace()")
    (replace-match "")
    (when (empty-line-p)
      (delete-region (line-beginning-position) (line-end-position)))
    (goto-char orig)
    (insert "pdb.set_trace()")))

(defun py-line-to-printform-python2 (&optional arg)
  "Transforms the item on current in a print statement. "
  (interactive "*")
  (lexical-let* ((name (thing-at-point 'word))
                 (form (cond ((eq major-mode 'python-mode)
                              (concat "print \"" name ": %s \" % " name)))))
    (delete-region (line-beginning-position) (line-end-position))
    (insert form))
  (forward-line 1)
  (back-to-indentation))

;;; python-components-imenu.el

;; Imenu definitions
(defvar py-imenu-class-regexp
  (concat                               ; <<classes>>
   "\\("                                ;
   "^[ \t]*"                            ; newline and maybe whitespace
   "\\(class[ \t]+[a-zA-Z0-9_]+\\)"     ; class name
                                        ; possibly multiple superclasses
   "\\([ \t]*\\((\\([a-zA-Z0-9_,. \t\n]\\)*)\\)?\\)"
   "[ \t]*:"                            ; and the final :
   "\\)"                                ; >>classes<<
   )
  "Regexp for Python classes for use with the Imenu package.")

(defvar py-imenu-method-regexp
  (concat                               ; <<methods and functions>>
   "\\("                                ;
   "^[ \t]*"                            ; new line and maybe whitespace
   "\\(def[ \t]+"                       ; function definitions start with def
   "\\([a-zA-Z0-9_]+\\)"                ;   name is here
                                        ;   function arguments...
   ;;   "[ \t]*(\\([-+/a-zA-Z0-9_=,\* \t\n.()\"'#]*\\))"
   "[ \t]*(\\([^:#]*\\))"
   "\\)"                                ; end of def
   "[ \t]*:"                            ; and then the :
   "\\)"                                ; >>methods and functions<<
   )
  "Regexp for Python methods/functions for use with the Imenu package.")

(defvar py-imenu-method-no-arg-parens '(2 8)
  "Indices into groups of the Python regexp for use with Imenu.

Using these values will result in smaller Imenu lists, as arguments to
functions are not listed.

See the variable `py-imenu-show-method-args-p' for more
information.")

(defvar py-imenu-method-arg-parens '(2 7)
  "Indices into groups of the Python regexp for use with imenu.
Using these values will result in large Imenu lists, as arguments to
functions are listed.

See the variable `py-imenu-show-method-args-p' for more
information.")

;; Note that in this format, this variable can still be used with the
;; imenu--generic-function. Otherwise, there is no real reason to have
;; it.
(defvar py-imenu-generic-expression
  (cons
   (concat
    py-imenu-class-regexp
    "\\|"                               ; or...
    py-imenu-method-regexp)
   py-imenu-method-no-arg-parens)
  "Generic Python expression which may be used directly with Imenu.
Used by setting the variable `imenu-generic-expression' to this value.
Also, see the function \\[py-imenu-create-index] for a better
alternative for finding the index.")

;; These next two variables are used when searching for the Python
;; class/definitions. Just saving some time in accessing the
;; generic-python-expression, really.
(defvar py-imenu-generic-regexp nil)
(defvar py-imenu-generic-parens nil)

(defun py-switch-imenu-index-function ()
  "For development only. Good old renamed `py-imenu-create-index'-function hangs with medium size files already. Working `py-imenu-create-index-new' is active by default.

Switch between classic index machine `py-imenu-create-index'-function and new `py-imenu-create-index-new'.

The former may provide a more detailed report, thus delivering two different index-machines is considered. "
  (interactive)
  (if (eq major-mode 'python-mode)
      (progn
        (if (eq imenu-create-index-function 'py-imenu-create-index-new)
            (setq imenu-create-index-function #'py-imenu-create-index)
          (setq imenu-create-index-function #'py-imenu-create-index-new))
        (when (and py-verbose-p (interactive-p)) (message "imenu-create-index-function: %s" (prin1-to-string imenu-create-index-function))))
    (error "%s" "Only available in buffers set to python-mode")))

(defun py-imenu-create-index-function ()
  "Python interface function for the Imenu package.
Finds all Python classes and functions/methods. Calls function
\\[py-imenu-create-index-engine].  See that function for the details
of how this works."
  (setq py-imenu-generic-regexp (car py-imenu-generic-expression)
        py-imenu-generic-parens (if py-imenu-show-method-args-p
                                    py-imenu-method-arg-parens
                                  py-imenu-method-no-arg-parens))
  (goto-char (point-min))
  ;; Warning: When the buffer has no classes or functions, this will
  ;; return nil, which seems proper according to the Imenu API, but
  ;; causes an error in the XEmacs port of Imenu.  Sigh.
  (py-imenu-create-index-engine nil))

(defun py-imenu-create-index-engine (&optional start-indent)
  "Function for finding Imenu definitions in Python.

Finds all definitions (classes, methods, or functions) in a Python
file for the Imenu package.

Returns a possibly nested alist of the form

        (INDEX-NAME . INDEX-POSITION)

The second element of the alist may be an alist, producing a nested
list as in

        (INDEX-NAME . INDEX-ALIST)

This function should not be called directly, as it calls itself
recursively and requires some setup.  Rather this is the engine for
the function \\[py-imenu-create-index-function].

It works recursively by looking for all definitions at the current
indention level.  When it finds one, it adds it to the alist.  If it
finds a definition at a greater indentation level, it removes the
previous definition from the alist. In its place it adds all
definitions found at the next indentation level.  When it finds a
definition that is less indented then the current level, it returns
the alist it has created thus far.

The optional argument START-INDENT indicates the starting indentation
at which to continue looking for Python classes, methods, or
functions.  If this is not supplied, the function uses the indentation
of the first definition found."
  (let (index-alist
        sub-method-alist
        looking-p
        def-name prev-name
        cur-indent def-pos
        (class-paren (first py-imenu-generic-parens))
        (def-paren (second py-imenu-generic-parens)))
    (setq looking-p
          (re-search-forward py-imenu-generic-regexp (point-max) t))
    (while looking-p
      (save-excursion
        ;; used to set def-name to this value but generic-extract-name
        ;; is new to imenu-1.14. this way it still works with
        ;; imenu-1.11
        ;;(imenu--generic-extract-name py-imenu-generic-parens))
        (let ((cur-paren (if (match-beginning class-paren)
                             class-paren def-paren)))
          (setq def-name
                (buffer-substring-no-properties (match-beginning cur-paren)
                                                (match-end cur-paren))))
        (save-match-data
          (py-beginning-of-def-or-class))
        (beginning-of-line)
        (setq cur-indent (current-indentation)))
      ;; HACK: want to go to the next correct definition location.  We
      ;; explicitly list them here but it would be better to have them
      ;; in a list.
      (setq def-pos
            (or (match-beginning class-paren)
                (match-beginning def-paren)))
      ;; if we don't have a starting indent level, take this one
      (or start-indent
          (setq start-indent cur-indent))
      ;; if we don't have class name yet, take this one
      (or prev-name
          (setq prev-name def-name))
      ;; what level is the next definition on?  must be same, deeper
      ;; or shallower indentation
      (cond
       ;; Skip code in comments and strings
       ((py-in-literal))
       ;; at the same indent level, add it to the list...
       ((= start-indent cur-indent)
        (push (cons def-name def-pos) index-alist))
       ;; deeper indented expression, recurse
       ((< start-indent cur-indent)
        ;; the point is currently on the expression we're supposed to
        ;; start on, so go back to the last expression. The recursive
        ;; call will find this place again and add it to the correct
        ;; list
        (re-search-backward py-imenu-generic-regexp (point-min) 'move)
        (setq sub-method-alist (py-imenu-create-index-engine cur-indent))
        (if sub-method-alist
            ;; we put the last element on the index-alist on the start
            ;; of the submethod alist so the user can still get to it.
            (let ((save-elmt (pop index-alist)))
              (push (cons prev-name
                          (cons save-elmt sub-method-alist))
                    index-alist))))
       ;; found less indented expression, we're done.
       (t
        (setq looking-p nil)
        (re-search-backward py-imenu-generic-regexp (point-min) t)))
      ;; end-cond
      (setq prev-name def-name)
      (and looking-p
           (setq looking-p
                 (re-search-forward py-imenu-generic-regexp
                                    (point-max) 'move))))
    (nreverse index-alist)))

(defvar imenu-max-items)
(defun py-imenu-create-index-new-intern (&optional thisend)
  (let* ((pos (match-beginning 0))
         (name (match-string-no-properties 2))
         (classname (concat "class " name))
         (thisend (or thisend (save-match-data (py-end-of-def-or-class-position))))
         sublist)
    (while (and (re-search-forward "^[ \t]*\\(?:\\(def\\|class\\)\\)[ \t]+\\(?:\\(\\sw+\\)\\)" (or thisend end) t 1)(not (nth 8 (syntax-ppss))))
      (let* ((pos (match-beginning 0))
             (name (match-string-no-properties 2))
             (classname (concat "class " name))
             (thisend (or thisend (save-match-data (py-end-of-def-or-class-position)))))
        (if (string= "class" (match-string-no-properties 1))
            (py-imenu-create-index-new-intern (save-match-data (py-end-of-def-or-class-position)))
          (push (cons (concat " " name) pos) sublist))))
    (if classname
        (progn
          (setq sublist (nreverse sublist))
          (push (cons classname pos) sublist)
          (push (cons classname sublist) index-alist))
      (push sublist index-alist))))

(defun py-imenu-create-index-new (&optional beg end)
  "`imenu-create-index-function' for Python. "
  (set (make-local-variable 'imenu-max-items) 99)
  (let ((orig (point))
        (beg (or beg (point-min)))
        (end (or end (point-max)))
        index-alist vars thisend sublist classname)
    (goto-char beg)
    (while (and (re-search-forward "^[ \t]*\\(def\\|class\\)[ \t]+\\(\\sw+\\)" end t 1)(not (nth 8 (syntax-ppss))))
      (if (save-match-data (string= "class" (match-string-no-properties 1)))
          (progn
            (setq pos (match-beginning 0)
                  name (match-string-no-properties 2)
                  classname (concat "class " name)
                  thisend (save-match-data (py-end-of-def-or-class-position))
                  sublist '())
            (while (and (re-search-forward "^[ \t]*\\(def\\|class\\)[ \t]+\\(\\sw+\\)" (or thisend end) t 1)(not (nth 8 (syntax-ppss))))
              (let* ((pos (match-beginning 0))
                     (name (match-string-no-properties 2))
                     (classname (concat "class " name))
                     (thisend (or thisend (save-match-data (py-end-of-def-or-class-position)))))
                (if (string= "class" (match-string-no-properties 1))
                    (py-imenu-create-index-new-intern (save-match-data (py-end-of-def-or-class-position)))
                  (push (cons (concat " " name) pos) sublist))))
            (if classname
                (progn
                  (setq sublist (nreverse sublist))
                  (push (cons classname pos) sublist)
                  (push (cons classname sublist) index-alist))
              (push sublist index-alist)))

        (let ((pos (match-beginning 0))
              (name (match-string-no-properties 2)))
          (push (cons name pos) index-alist))))
    ;; Look for module variables.
    (goto-char (point-min))
    (while (re-search-forward "^\\(\\sw+\\)[ \t]*=" end t)
      (unless (nth 8 (syntax-ppss))
        (let ((pos (match-beginning 1))
              (name (match-string-no-properties 1)))
          (push (cons name pos) vars))))
    (setq index-alist (nreverse index-alist))
    (when vars
      (push (cons "Module variables"
                  (nreverse vars))
            index-alist))
    (goto-char orig)
    index-alist))

;;; python-components-completion.el
(defun python-symbol-completions (symbol)
  "Return a list of completions of the string SYMBOL from Python process.
The list is sorted.
Uses `python-imports' to load modules against which to complete."
  (when (stringp symbol)
    (let ((completions
	   (condition-case ()
	       (car (read-from-string
		     (python-send-receive
		      (format "emacs.complete(%S,%s)"
			      (substring-no-properties symbol)
			      python-imports))))
	     (error nil))))
      (sort
       ;; We can get duplicates from the above -- don't know why.
       (delete-dups completions)
       #'string<))))

(defvar py-mode-output-map nil
  "Keymap used in *Python Output* buffers.")
(if py-mode-output-map
    nil
  (setq py-mode-output-map (make-sparse-keymap))
  (define-key py-mode-output-map [button2]  'py-mouseto-exception)
  (define-key py-mode-output-map "\C-c\C-c" 'py-goto-exception)
  ;; TBD: Disable all self-inserting keys.  This is bogus, we should
  ;; really implement this as *Python Output* buffer being read-only
  (mapc #' (lambda (key)
             (define-key py-mode-output-map key
               #'(lambda () (interactive) (beep))))
           (where-is-internal 'self-insert-command)))

(setq py-shell-map
      (let ((map (copy-keymap comint-mode-map)))
        (substitute-key-definition 'complete-symbol 'completion-at-point
                                   map global-map)
        (define-key map [tab] 'py-shell-complete)
        (define-key map (kbd "RET") 'comint-send-input)
        (define-key map "\C-c-" 'py-up-exception)
        (define-key map "\C-c=" 'py-down-exception)
        map))

(defun py-choose-shell-by-path (&optional file-separator-char)
  "Select Python executable according to version desplayed in path, current buffer-file is selected from.

Returns versioned string, nil if nothing appropriate found "
  (interactive)
  (lexical-let ((path (buffer-file-name))
                (file-separator-char (or file-separator-char (py-separator-char)))
                erg)
    (when (and path file-separator-char
               (string-match (concat file-separator-char "[iI]?[pP]ython[0-9.]+" file-separator-char) path))
      (setq erg (substring path
                           (1+ (string-match (concat file-separator-char "[iI]?[pP]ython[0-9.]+" file-separator-char) path)) (1- (match-end 0)) )))
    (when (interactive-p) (message "%s" erg))
    erg))

(defun py-choose-shell-by-shebang ()
  "Choose shell by looking at #! on the first line.

Returns the specified Python resp. Jython shell command name. "
  (interactive)
  ;; look for an interpreter specified in the first line
  (let* (erg res)
    (save-excursion
      (goto-char (point-min))
      (when (looking-at py-shebang-regexp)
        (setq erg (split-string (match-string-no-properties 0) "[#! \t]"))
        (dolist (ele erg)
          (when (string-match "[ijp]+ython" ele)
            (setq res ele)))))
    (when (interactive-p) (message "%s" res))
    res))

(defun py-choose-shell-by-import ()
  "Choose CPython or Jython mode based imports.

If a file imports any packages in `py-jython-packages', within
`py-import-check-point-max' characters from the start of the file,
return `jython', otherwise return nil."
  (let (mode)
    (save-excursion
      (goto-char (point-min))
      (while (and (not mode)
                  (search-forward-regexp
                   "^\\(\\(from\\)\\|\\(import\\)\\) \\([^ \t\n.]+\\)"
                   py-import-check-point-max t))
        (setq mode (and (member (match-string 4) py-jython-packages)
                        'jython))))
    mode))

(defalias 'py-version 'py-which-python)
(defun py-which-python ()
  "Returns version of Python of current environment, a number. "
  (interactive)
  (let* ((cmd (py-choose-shell))
         (erg (shell-command-to-string (concat cmd " --version")))
         (version (when (string-match "\\([0-9]\\.[0-9]+\\)" erg)
                    (substring erg 7 (1- (length erg))))))
    (when (interactive-p)
      (if erg
          (when py-verbose-p (message "%s" erg))
        (message "%s" "Could not detect Python on your system")))
    (string-to-number version)))

(defun py-python-current-environment ()
  "Returns path of current Python installation. "
  (interactive)
  (let* ((cmd (py-choose-shell))
         (denv (shell-command-to-string (concat "type " cmd)))
         (erg (substring denv (string-match "/" denv))))
    (when (interactive-p)
      (if erg
          (when py-verbose-p (message "%s" erg))
        (message "%s" "Could not detect Python on your system")))
    erg))

(defalias 'python-toggle-shells 'py-switch-shell)
(defalias 'py-toggle-shell 'py-switch-shell)
(defun py-switch-shell (&optional arg)
  "Toggles between the interpreter customized in `py-shell-toggle-1' resp. `py-shell-toggle-2'. Was hard-coded CPython and Jython in earlier versions, now starts with Python2 and Python3 by default.

ARG might be a python-version string to set to.

\\[universal-argument] `py-toggle-shell' prompts to specify a reachable Python command.
\\[universal-argument] followed by numerical arg 2 or 3, `py-toggle-shell' opens a respective Python shell.
\\[universal-argument] followed by numerical arg 5 opens a Jython shell.

Should you need more shells to select, extend this command by adding inside the first cond:

                    ((eq NUMBER (prefix-numeric-value arg))
                     \"MY-PATH-TO-SHELL\")
"
  (interactive "P")
  (let ((name (cond ((eq 2 (prefix-numeric-value arg))
                     "python2")
                    ((eq 3 (prefix-numeric-value arg))
                     "python3")
                    ((eq 4 (prefix-numeric-value arg))
                     (string-strip
                      (read-from-minibuffer "Python Shell: " py-shell-name) "\" " "\" "
                      ))
                    ((eq 5 (prefix-numeric-value arg))
                     "jython")
                    (t (if (string-match py-shell-name
                                         py-shell-toggle-1)
                           py-shell-toggle-2
                         py-shell-toggle-1))))
        erg)
    (cond ((or (string= "ipython" name)
               (string= "IPython" name))
           (setq py-shell-name name
                 py-which-bufname "IPython"
                 msg "IPython"
                 mode-name "IPython"))
          ((string-match "python3" name)
           (setq py-shell-name name
                 py-which-bufname (py-buffer-name-prepare name)
                 msg "CPython"
                 mode-name (py-buffer-name-prepare name)))
          ((string-match "jython" name)
           (setq py-shell-name name
                 py-which-bufname (py-buffer-name-prepare name)
                 msg "Jython"
                 mode-name (py-buffer-name-prepare name)))
          ((string-match "python" name)
           (setq py-shell-name name
                 py-which-bufname (py-buffer-name-prepare name)
                 msg "CPython"
                 mode-name py-which-bufname))
          (t
           (setq py-shell-name name
                 py-which-bufname name
                 msg name
                 mode-name name)))
    ;; py-edit-only-p has no interpreter
    ;; (if py-edit-only-p
    ;; (setq erg py-shell-name)
    (setq erg (executable-find py-shell-name))
    ;;)
    (if erg
        (progn
          (force-mode-line-update)
          (when (interactive-p)
            (message "Using the %s shell, %s" msg erg))
          (setq py-output-buffer (format "*%s Output*" py-which-bufname)))
      (error (concat "Could not detect " py-shell-name " on your sys
tem")))))

(defalias 'py-which-shell 'py-choose-shell)
(defun py-choose-shell (&optional arg pyshell dedicated)
  "Return an appropriate executable as a string.

Returns nil, if no executable found.

This does the following:
 - look for an interpreter with `py-choose-shell-by-shebang'
 - examine imports using `py-choose-shell-by-import'
 - look if Path/To/File indicates a Python version
 - if not successful, return default value of `py-shell-name'

When interactivly called, messages the shell name, Emacs would in the given circtumstances.

With \\[universal-argument] 4 is called `py-switch-shell' see docu there.
"
  (interactive "P")
  (if (eq 4 (prefix-numeric-value arg))
      (py-switch-shell '(4))
    (let* ((erg (cond (py-force-py-shell-name-p
                       py-shell-name)
                      (py-use-local-default
                       (if (not (string= "" py-shell-local-path))
                           (expand-file-name py-shell-local-path)
                         (message "Abort: `py-use-local-default' is set to `t' but `py-shell-local-path' is empty. Maybe call `py-toggle-local-default-use'")))
                      ((comint-check-proc (current-buffer))
                       (process-name (get-buffer-process (current-buffer))))
                      ((py-choose-shell-by-shebang))
                      ((py-choose-shell-by-import))
                      ((py-choose-shell-by-path))
                      (py-shell-name py-shell-name)
                      (t (default-value 'py-shell-name))))
           (cmd (if py-edit-only-p erg
                  (executable-find erg))))
      (if cmd
          (when (interactive-p)
            (message "%s" cmd))
        (when (interactive-p) (message "%s" "Could not detect Python on your system. Maybe set `py-edit-only-p'?")))
      erg)))

(defalias 'toggle-py-smart-indentation 'py-toggle-smart-indentation)
(defun py-toggle-smart-indentation (&optional arg)
  "If `py-smart-indentation' should be on or off.

Returns value of `py-smart-indentation' switched to. "
  (interactive)
  (let ((arg (or arg (if py-smart-indentation -1 1))))
    (if (< 0 arg)
        (setq py-smart-indentation t)
      (setq py-smart-indentation nil)
      (setq py-indent-offset (default-value 'py-indent-offset)))
    (when (and py-verbose-p (interactive-p)) (message "py-smart-indentation: %s" py-smart-indentation))
    py-smart-indentation))

(defun py-smart-indentation-on (&optional arg)
  "Make sure, `py-smart-indentation' is on.

Returns value of `py-smart-indentation'. "
  (interactive "p")
  (let ((arg (or arg 1)))
    (toggle-py-smart-indentation arg))
  (when (interactive-p) (message "py-smart-indentation: %s" py-smart-indentation))
  py-smart-indentation)

(defun py-smart-indentation-off (&optional arg)
  "Make sure, `py-smart-indentation' is off.

Returns value of `py-smart-indentation'. "
  (interactive "p")
  (let ((arg (if arg (- arg) -1)))
    (toggle-py-smart-indentation arg))
  (when (interactive-p) (message "py-smart-indentation: %s" py-smart-indentation))
  py-smart-indentation)

;;; Split-Windows-On-Execute forms
(defalias 'toggle-py-split-windows-on-execute 'py-toggle-split-windows-on-execute)
(defun py-toggle-split-windows-on-execute (&optional arg)
  "If `py-split-windows-on-execute-p' should be on or off.

  Returns value of `py-split-windows-on-execute-p' switched to. "
  (interactive)
  (let ((arg (or arg (if py-split-windows-on-execute-p -1 1))))
    (if (< 0 arg)
        (setq py-split-windows-on-execute-p t)
      (setq py-split-windows-on-execute-p nil))
    (when (interactive-p) (message "py-split-windows-on-execute-p: %s" py-split-windows-on-execute-p))
    py-split-windows-on-execute-p))

(defun py-split-windows-on-execute-on (&optional arg)
  "Make sure, `py-split-windows-on-execute-p' is on.

Returns value of `py-split-windows-on-execute-p'. "
  (interactive "p")
  (let ((arg (or arg 1)))
    (toggle-py-split-windows-on-execute arg))
  (when (interactive-p) (message "py-split-windows-on-execute-p: %s" py-split-windows-on-execute-p))
  py-split-windows-on-execute-p)

(defun py-split-windows-on-execute-off ()
  "Make sure, `py-split-windows-on-execute-p' is off.

Returns value of `py-split-windows-on-execute-p'. "
  (interactive)
  (toggle-py-split-windows-on-execute -1)
  (when (interactive-p) (message "py-split-windows-on-execute-p: %s" py-split-windows-on-execute-p))
  py-split-windows-on-execute-p)

;;; Flymake
(defun clear-flymake-allowed-file-name-masks (&optional suffix)
  "Remove entries with SUFFIX from `flymake-allowed-file-name-masks'.

Default is \"\\.py\\'\" "
  (interactive "P")
  (let ((suffix (cond ((eq 4 (prefix-numeric-value suffix))
                       (read-from-minibuffer "Suffix: " "\\\\.py\\\\'"))
                      (suffix suffix)
                      (t "\\\\.py\\\\'")))
        (erg flymake-allowed-file-name-masks)
        (newlist '()))
    (dolist (ele flymake-allowed-file-name-masks)
      (unless
          ;; (string-match "\\\\.py\\\\'" (car ele))
          (string-match suffix (car ele))
        (add-to-list 'newlist ele t)))
    (setq flymake-allowed-file-name-masks newlist)
    (when (and py-verbose-p (interactive-p)) (message "%s" flymake-allowed-file-name-masks))
    flymake-allowed-file-name-masks))

(defun py-toggle-flymake-intern (name command)
  ;; (clear-flymake-allowed-file-name-masks)
  (unless (string-match "pyflakespep8" name)
    (unless (executable-find name)
      (when py-verbose-p (message "Don't see %s. Use `easy_install' %s? " name name))))
  (let* ((temp-file (flymake-init-create-temp-buffer-copy
                     'flymake-create-temp-inplace))
         (local-file (file-relative-name
                      temp-file
                      (file-name-directory buffer-file-name))))
    (add-to-list 'flymake-allowed-file-name-masks (car (read-from-string (concat "(\"\\.py\\'\" flymake-" name ")"))))
    (list command (list local-file))))

(defun pylint-flymake-mode ()
  "Toggle `pylint' `flymake-mode'. "
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pylint" "pylint")
    (flymake-mode)))

(defun pyflakes-flymake-mode ()
  "Toggle `pyflakes' `flymake-mode'. "
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pyflakes" "pyflakes")
    (flymake-mode)))

(defun pychecker-flymake-mode ()
  "Toggle `pychecker' `flymake-mode'. "
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pychecker" "pychecker")
    (flymake-mode)))

(defun pep8-flymake-mode ()
  "Toggle `pep8' `flymake-mode'. "
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pep8" "pep8")
    (flymake-mode)))

(defun pyflakespep8-flymake-mode ()
  "Toggle `pyflakespep8' `flymake-mode'.

Joint call to pyflakes and pep8 as proposed by

Keegan Carruthers-Smith

"
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pyflakespep8" "pyflakespep8")
    (flymake-mode)))

;;; Shell-Switch-Buffers-On-Execute forms
(defalias 'toggle-py-shell-switch-buffers-on-execute 'py-toggle-shell-switch-buffers-on-execute)
(defun py-toggle-shell-switch-buffers-on-execute (&optional arg)
  "If `py-switch-buffers-on-execute-p' should be on or off.

  Returns value of `py-switch-buffers-on-execute-p' switched to. "
  (interactive)
  (let ((arg (or arg (if py-switch-buffers-on-execute-p -1 1))))
    (if (< 0 arg)
        (setq py-switch-buffers-on-execute-p t)
      (setq py-switch-buffers-on-execute-p nil))
    (when (interactive-p) (message "py-shell-switch-buffers-on-execute: %s" py-switch-buffers-on-execute-p))
    py-switch-buffers-on-execute-p))

(defun py-shell-switch-buffers-on-execute-on (&optional arg)
  "Make sure, `py-switch-buffers-on-execute-p' is on.

Returns value of `py-switch-buffers-on-execute-p'. "
  (interactive "p")
  (let ((arg (or arg 1)))
    (toggle-py-shell-switch-buffers-on-execute arg))
  (when (interactive-p) (message "py-shell-switch-buffers-on-execute: %s" py-switch-buffers-on-execute-p))
  py-switch-buffers-on-execute-p)

(defun py-shell-switch-buffers-on-execute-off ()
  "Make sure, `py-switch-buffers-on-execute-p' is off.

Returns value of `py-switch-buffers-on-execute-p'. "
  (interactive)
  (toggle-py-shell-switch-buffers-on-execute -1)
  (when (interactive-p) (message "py-shell-switch-buffers-on-execute: %s" py-switch-buffers-on-execute-p))
  py-switch-buffers-on-execute-p)

;;;
(defvar inferior-python-mode-map
  (let ((map (make-sparse-keymap)))
    ;; This will inherit from comint-mode-map.
    (define-key map "\C-c\C-l" 'py-load-file)
    (define-key map "\C-c\C-v" 'python-check)
    ;; Note that we _can_ still use these commands which send to the
    ;; Python process even at the prompt iff we have a normal prompt,
    ;; i.e. '>>> ' and not '... '.  See the comment before
    ;; py-send-region.  Fixme: uncomment these if we address that.
    map))

(defun py-normalize-directory (directory &optional file-separator-char)
  "Make sure DIRECTORY ends with a file-path separator char.

Returns DIRECTORY"
  (let* ((file-separator-char (or file-separator-char (py-separator-char)))
         ;; (if (or (string-match "windows" (prin1-to-string system-type))
         ;; (string-match "ms-dos" (prin1-to-string system-type)))
         ;; "\\"
         ;; "\/")
         (erg (cond ((string-match (concat file-separator-char "$") directory)
                     directory)
                    ((not (string= "" directory))
                     (concat directory file-separator-char))
                    (t (when py-verbose-p (message "Warning: directory is empty"))))))
    (when (interactive-p) (message "%s" erg))
    erg))

(defun py-install-directory-check ()
  "Do some sanity check for `py-install-directory'.

Returns `t' if successful. "
  (interactive)
  (let ((erg (and (boundp 'py-install-directory) (stringp py-install-directory) (< 1 (length py-install-directory)))))
    (when (interactive-p) (message "py-install-directory-check: %s" erg))
    erg))

(defun py-load-pymacs ()
  "Load Pymacs as delivered with python-mode.el.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.ca"
  (interactive)
  (let* ((pyshell (py-choose-shell))
         (path (getenv "PYTHONPATH"))
         (py-install-directory (py-normalize-directory (or py-install-directory (py-guess-py-install-directory)) (py-separator-char)))
         (pymacs-installed-p
          (ignore-errors (string-match (expand-file-name (concat py-install-directory "Pymacs")) path))))
    ;; Python side
    (unless pymacs-installed-p
      (setenv "PYTHONPATH" (concat
                            (if path (concat path path-separator))
                            (expand-file-name py-install-directory) "Pymacs")))

    (if (py-install-directory-check)
        (progn
          (load (concat py-install-directory "pymacs.el") nil t)
          (setenv "PYMACS_PYTHON" (if (string-match "IP" pyshell)
                                      "python"
                                    pyshell))
          (autoload 'pymacs-apply "pymacs")
          (autoload 'pymacs-call "pymacs")
          (autoload 'pymacs-eval "pymacs")
          (autoload 'pymacs-exec "pymacs")
          (autoload 'pymacs-load "pymacs")
          (require 'pymacs)
          (load (concat py-install-directory "completion/pycomplete.el") nil t))
      (error "`py-install-directory' not set, see INSTALL"))))

(defun py-guess-py-install-directory ()
  "Takes value of user directory aka $HOME
if `(locate-library \"python-mode\")' is not succesful. "
  (interactive)
  (let ((erg (file-name-directory (locate-library "python-mode"))))
    (if erg
        (progn
          (setq py-install-directory erg)
          (when (and py-verbose-p (interactive-p)) (message "Setting py-install-directory to: %s" erg)))
      (setq py-install-directory (expand-file-name "~/")))
    py-install-directory ))

(defun py-set-load-path ()
  "Include needed subdirs of python-mode directory. "
  (interactive)
  (let ((py-install-directory (py-normalize-directory py-install-directory (py-separator-char))))
    (cond ((and (not (string= "" py-install-directory))(stringp py-install-directory))
           (add-to-list 'load-path (expand-file-name py-install-directory))
           (add-to-list 'load-path (concat (expand-file-name py-install-directory) "completion"))
           (add-to-list 'load-path (concat (expand-file-name py-install-directory) "test"))
           (add-to-list 'load-path (concat (expand-file-name py-install-directory) "tools")))
          ((when py-guess-py-install-directory-p
             (let ((guessed-py-install-directory (py-guess-py-install-directory)))
               (when guessed-py-install-directory
                 (add-to-list 'load-path guessed-py-install-directory)))))
          (t (error "Please set `py-install-directory', see INSTALL"))
          (when (interactive-p) (message "%s" load-path)))))

(defvar py-menu)
(defvar python-mode-map)
(setq python-mode-map
      (let ((map (make-sparse-keymap)))
        ;; electric keys
        (define-key map [(:)] 'py-electric-colon)
        (define-key map [(\#)] 'py-electric-comment)
        (define-key map [(delete)] 'py-electric-delete)
        (define-key map [(backspace)] 'py-electric-backspace)
        (define-key map [(control backspace)] 'py-hungry-delete-backwards)
        (define-key map [(control c) (delete)] 'py-hungry-delete-forward)
        (define-key map [(control c)(control a)] 'py-mark-statement)
        ;; moving point
        (define-key map [(control c)(control p)] 'py-beginning-of-statement)
        (define-key map [(control c)(control n)] 'py-end-of-statement)
        (define-key map [(control c)(control u)] 'py-beginning-of-block)
        (define-key map [(control c)(control q)] 'py-end-of-block)
        (define-key map [(control meta a)] 'py-beginning-of-def-or-class)
        (define-key map [(control meta e)] 'py-end-of-def-or-class)

        ;; (define-key map [(meta i)] 'py-indent-forward-line)
        (define-key map [(control j)] 'py-newline-and-indent)
        ;; Most Pythoneers expect RET `py-newline-and-indent'
        ;; (define-key map (kbd "RET") 'py-newline-and-dedent)
        (define-key map (kbd "RET") 'py-newline-and-indent)
        ;; (define-key map (kbd "RET") 'newline)
        (define-key map [(super backspace)] 'py-dedent)
        ;; (define-key map [(control return)] 'py-newline-and-dedent)
        ;; indentation level modifiers
        (define-key map [(control c)(control l)] 'py-shift-left)
        (define-key map [(control c)(control r)] 'py-shift-right)
        (define-key map [(control c)(<)] 'py-shift-left)
        (define-key map [(control c)(>)] 'py-shift-right)
        (define-key map [(control c)(tab)] 'py-indent-region)
        (define-key map [(control c)(:)] 'py-guess-indent-offset)
        ;; subprocess commands
        (define-key map [(control c)(control c)] 'py-execute-buffer)
        (define-key map [(control c)(control m)] 'py-execute-import-or-reload)
        (define-key map [(control c)(control s)] 'py-execute-string)
        (define-key map [(control c)(|)] 'py-execute-region)
        (define-key map [(control meta x)] 'py-execute-def-or-class)
        (define-key map [(control c)(!)] 'py-shell)
        (define-key map [(control c)(control t)] 'py-toggle-shell)
        (define-key map [(control meta h)] 'py-mark-def-or-class)
        (define-key map [(control c)(control k)] 'py-mark-block-or-clause)
        (define-key map [(control c)(.)] 'py-expression)
        ;; Miscellaneous
        (define-key map [(control c)(control d)] 'py-pdbtrack-toggle-stack-tracking)
        (define-key map [(control c)(control f)] 'py-sort-imports)
        (define-key map [(control c)(\#)] 'py-comment-region)
        (define-key map [(control c)(\?)] 'py-describe-mode)
        (define-key map [(control c)(control e)] 'py-describe-symbol)
        (define-key map [(control c)(-)] 'py-up-exception)
        (define-key map [(control c)(=)] 'py-down-exception)
        (define-key map [(control x) (n) (d)] 'py-narrow-to-defun)
        ;; information
        (define-key map [(control c)(control b)] 'py-submit-bug-report)
        (define-key map [(control c)(control v)] 'py-version)
        (define-key map [(control c)(control w)] 'py-pychecker-run)
        ;; (if (featurep 'xemacs)
        ;; (define-key map [(meta tab)] 'py-complete)
        ;; (define-key map [(meta tab)] py-complete-function)
        ;; (substitute-key-definition 'complete-symbol 'completion-at-point
        ;; map global-map)
        ;; )
        (substitute-key-definition 'complete-symbol 'completion-at-point
                                   map global-map)
        (easy-menu-define py-menu map "Python Tools"
          `("PyTools"
            :help "Python mode tools"

            ["Customize Python mode" (customize-group 'python-mode)
             :help "Open the customization buffer for Python mode"]

            "-"

            ["pychecker-run" py-pychecker-run
             :help "`py-pychecker-run'
Run pychecker"]

            ("Pylint ... "
             :help "Extendet report options
call `easy_install pylint' if not available"

             ["pylint-run" py-pylint-run
              :help "`pylint-run'
Pylint will display a number of messages as it analyzes the code,
as well as some statistics about the number of warnings and
errors found in different files - unless called with arg \"--errors-only\". The messages are classified
under various categories such as errors and warnings

Pylint checks length of lines of code, if variable names are
well-formed according to your coding standard, if declared
interfaces are truly implemented, and much more. Additionally, it
is possible to write plugins.

call `easy_install pylint' if not available
"]

             ["pylint-help" pylint-help
              :help "`pylint-help'
List extendet report options
"]
             ["pylint-flymake-mode" pylint-flymake-mode
              :help "`pylint-flymake-mode'
Toggle flymake-mode running `pylint'
"]
             )

            ("pep8 ... "
             :help "Check formatting
call `easy_install pep8' if not available"

             ["pep8-run" py-pep8-run
              :help "`py-pep8-run'
Check formatting (default on the file currently visited)
call `easy_install pep8' if not available
"]

             ["pep8-help" py-pep8-help
              :help "`py-pep8-help'
Display help for pep8 format checker)
"]

             ["pep8-flymake-mode" pep8-flymake-mode
              :help "`pep8-flymake-mode'
Toggle flymake-mode running `pep8'
"]

             )

            ("Pyflakes ... " :help "Non intrusive code
             checker call `easy_install pyflakes' if
             not available"

             ["pyflakes-run" py-pyflakes-run :help
              "`py-pyflakes-run' Run pyflakes call
              `easy_install pyflakes' if not
              available"]

             ["pyflakes-help" py-pyflakes-help :help
              "`py-pyflakes-help' Display help for
              Pyflakes "]

             ["pyflakes-flymake-mode" pyflakes-flymake-mode :help
              "`pyflakes-flymake-mode'
Toggle flymake-mode running `pyflakes' "]

             )

            ("Pyflakes-pep8 ... " :help
             "Non intrusive code checker running `pyflakes' and `pep8'
call `easy_install pyflakes' and `easy_install pep8' if basics not available"

             ["pyflakespep8-run" py-pyflakespep8-run :help
              "`py-pyflakespep8-run' Run `pyflakespep8'
call `easy_install pyflakes' if not available"]

             ["pyflakespep8-help" py-pyflakespep8-help :help
              "`py-pyflakespep8-help' Display help for
              Pyflakespep8 "]

             ["pyflakespep8-flymake-mode" pyflakespep8-flymake-mode :help
              "`pyflakespep8-flymake-mode'
Toggle flymake-mode running `pyflakespep8' "]

             )

            "-"
            ("Skeletons..."
             :help "See also templates in YASnippet")
            ["if" py-if
             :help "Inserts if-statement"]
            ["py-else" py-else
             :help "Inserts else-statement"]
            ["py-while" py-while
             :help "Inserts while-statement"]
            ["py-for" py-for
             :help "Inserts for-statement"]
            ["py-try/finally" py-try/finally
             :help "Inserts py-try/finally-statement"]
            ["py-try/except" py-try/except
             :help "Inserts py-try/except-statement"]

            "-"

            ["Import/reload file" py-execute-import-or-reload
             :help "`py-execute-import-or-reload'
Load into inferior Python session"]

            ["Debugger" pdb
             :help "`pdb'
Run pdb under GUD"]
            "-"
            ["Toggle py-smart-indentation" toggle-py-smart-indentation
             :help "See also `py-smart-indentation-on', `-off' "]

            ["Toggle indent-tabs-mode" py-toggle-indent-tabs-mode
             :help "See also `py-indent-tabs-mode-on', `-off' "]

            ["Help on symbol" py-describe-symbol
             :help "`py-describe-symbol'
Use pydoc on symbol at point"]
            ["Complete symbol" completion-at-point
             :help "`completion-at-point'
Complete (qualified) symbol before point"]
            ["Find function" py-find-function
             :help "`py-find-function'
Try to find source definition of function at point"]
            ["Update imports" py-update-imports
             :help "`py-update-imports'
Update list of top-level imports for completion"]
            "-"
            ["Pymacs apply" pymacs-apply
             :help "`pymacs-apply'
Return the result of calling a Python function FUNCTION over ARGUMENTS.
FUNCTION is a string denoting the Python function, ARGUMENTS is a list of
Lisp expressions.  Immutable Lisp constants are converted to Python
equivalents, other structures are converted into Lisp handles. "]
            ["Pymacs call" pymacs-call
             :help "`pymacs-call'
             Return the result of calling a Python function FUNCTION over ARGUMENTS.
FUNCTION is a string denoting the Python function, ARGUMENTS are separate
Lisp expressions, one per argument.  Immutable Lisp constants are converted
to Python equivalents, other structures are converted into Lisp handles. "]
            ["Pymacs eval" pymacs-eval
             :help "`pymacs-eval'
             Compile TEXT as a Python expression, and return its value."]
            ["Pymacs exec" pymacs-exec
             :help "`pymacs-exec'
             Compile and execute TEXT as a sequence of Python statements.
This functionality is experimental, and does not appear to be useful. "]
            ["Pymacs load" pymacs-load
             :help "`pymacs-load'
             Import the Python module named MODULE into Emacs.
Each function in the Python module is made available as an Emacs function.
The Lisp name of each function is the concatenation of PREFIX with
the Python name, in which underlines are replaced by dashes.  If PREFIX is
not given, it defaults to MODULE followed by a dash.
If NOERROR is not nil, do not raise error when the module is not found. "]

            ))

        ;; Menu py-execute forms
        (easy-menu-define py-menu map "Execute Python"
          `("PyExec"
            :help "Python-specific features"

            ["Execute statement" py-execute-statement
             :help "`py-execute-statement'
       Send statement at point to Python interpreter. "]

            ["Execute block" py-execute-block
             :help "`py-execute-block'
       Send block at point to Python interpreter. "]

            ["Execute block-or-clause" py-execute-block-or-clause
             :help "`py-execute-block-or-clause'
       Send block-or-clause at point to Python interpreter. "]

            ["Execute def" py-execute-def
             :help "`py-execute-def'
       Send def at point to Python interpreter. "]

            ["Execute class" py-execute-class
             :help "`py-execute-class'
       Send class at point to Python interpreter. "]

            ["Execute region" py-execute-region
             :help "`py-execute-region'
       Send region at point to Python interpreter. "]

            ["Execute buffer" py-execute-buffer
             :help "`py-execute-buffer'
       Send buffer at point to Python interpreter. "]

            ["Execute file" py-execute-file
             :help "`py-execute-file'
       Send file at point to Python interpreter. "]
            ["Execute line" py-execute-line
             :help "`py-execute-line'
       Send current line from beginning of indent to Python interpreter. "]

            ["Execute expression" py-execute-expression
             :help "`py-execute-expression'
       Send expression at point to Python interpreter. "]

            ["Execute partial-expression" py-execute-partial-expression
             :help "`py-execute-partial-expression'
       Send partial-expression at point to Python interpreter. "]

            ["Execute line" py-execute-line
             :help "`py-execute-line'
       Send line at point to Python interpreter. "]

            ;; statement
            ("Execute statement ... "
             :help "Execute statement functions"
             ["py-execute-statement-python" py-execute-statement-python
              :help "Execute statement through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-statement-ipython" py-execute-statement-ipython
              :help "Execute statement through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-statement-python3" py-execute-statement-python3
              :help "Execute statement through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-statement-python2" py-execute-statement-python2
              :help "Execute statement through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-statement-python2.7" py-execute-statement-python2.7
              :help "Execute statement through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-statement-jython" py-execute-statement-jython
              :help "Execute statement through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-statement-python3.2" py-execute-statement-python3.2
              :help "Execute statement through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-statement-python-dedicated" py-execute-statement-python-dedicated
              :help "Execute statement through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-ipython-dedicated" py-execute-statement-ipython-dedicated
              :help "Execute statement through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-python3-dedicated" py-execute-statement-python3-dedicated
              :help "Execute statement through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-python2-dedicated" py-execute-statement-python2-dedicated
              :help "Execute statement through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-python2.7-dedicated" py-execute-statement-python2.7-dedicated
              :help "Execute statement through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-jython-dedicated" py-execute-statement-jython-dedicated
              :help "Execute statement through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-python3.2-dedicated" py-execute-statement-python3.2-dedicated
              :help "Execute statement through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-statement-python-switch" py-execute-statement-python-switch
              :help "Execute statement through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-statement-ipython-switch" py-execute-statement-ipython-switch
              :help "Execute statement through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-statement-python3-switch" py-execute-statement-python3-switch
              :help "Execute statement through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-statement-python2-switch" py-execute-statement-python2-switch
              :help "Execute statement through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-statement-python2.7-switch" py-execute-statement-python2.7-switch
              :help "Execute statement through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-statement-jython-switch" py-execute-statement-jython-switch
              :help "Execute statement through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-statement-python3.2-switch" py-execute-statement-python3.2-switch
              :help "Execute statement through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-statement-python-dedicated-switch" py-execute-statement-python-dedicated-switch
              :help "Execute statement through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-ipython-dedicated-switch" py-execute-statement-ipython-dedicated-switch
              :help "Execute statement through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-python3-dedicated-switch" py-execute-statement-python3-dedicated-switch
              :help "Execute statement through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-python2-dedicated-switch" py-execute-statement-python2-dedicated-switch
              :help "Execute statement through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-python2.7-dedicated-switch" py-execute-statement-python2.7-dedicated-switch
              :help "Execute statement through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-jython-dedicated-switch" py-execute-statement-jython-dedicated-switch
              :help "Execute statement through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-statement-python3.2-dedicated-switch" py-execute-statement-python3.2-dedicated-switch
              :help "Execute statement through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )

            ;; block
            ("Execute block ... "
             :help "Execute block functions"
             ["py-execute-block-python" py-execute-block-python
              :help "Execute block through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-block-ipython" py-execute-block-ipython
              :help "Execute block through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-block-python3" py-execute-block-python3
              :help "Execute block through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-block-python2" py-execute-block-python2
              :help "Execute block through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-block-python2.7" py-execute-block-python2.7
              :help "Execute block through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-block-jython" py-execute-block-jython
              :help "Execute block through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-block-python3.2" py-execute-block-python3.2
              :help "Execute block through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-block-python-dedicated" py-execute-block-python-dedicated
              :help "Execute block through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-ipython-dedicated" py-execute-block-ipython-dedicated
              :help "Execute block through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-python3-dedicated" py-execute-block-python3-dedicated
              :help "Execute block through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-python2-dedicated" py-execute-block-python2-dedicated
              :help "Execute block through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-python2.7-dedicated" py-execute-block-python2.7-dedicated
              :help "Execute block through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-jython-dedicated" py-execute-block-jython-dedicated
              :help "Execute block through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-python3.2-dedicated" py-execute-block-python3.2-dedicated
              :help "Execute block through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-block-python-switch" py-execute-block-python-switch
              :help "Execute block through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-block-ipython-switch" py-execute-block-ipython-switch
              :help "Execute block through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-block-python3-switch" py-execute-block-python3-switch
              :help "Execute block through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-block-python2-switch" py-execute-block-python2-switch
              :help "Execute block through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-block-python2.7-switch" py-execute-block-python2.7-switch
              :help "Execute block through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-block-jython-switch" py-execute-block-jython-switch
              :help "Execute block through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-block-python3.2-switch" py-execute-block-python3.2-switch
              :help "Execute block through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-block-python-dedicated-switch" py-execute-block-python-dedicated-switch
              :help "Execute block through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-ipython-dedicated-switch" py-execute-block-ipython-dedicated-switch
              :help "Execute block through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-python3-dedicated-switch" py-execute-block-python3-dedicated-switch
              :help "Execute block through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-python2-dedicated-switch" py-execute-block-python2-dedicated-switch
              :help "Execute block through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-python2.7-dedicated-switch" py-execute-block-python2.7-dedicated-switch
              :help "Execute block through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-jython-dedicated-switch" py-execute-block-jython-dedicated-switch
              :help "Execute block through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-python3.2-dedicated-switch" py-execute-block-python3.2-dedicated-switch
              :help "Execute block through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )

            ;; block-or-clause
            ("Execute block-or-clause ... "
             :help "Execute block-or-clause functions"
             ["py-execute-block-or-clause-python" py-execute-block-or-clause-python
              :help "Execute block-or-clause through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-block-or-clause-ipython" py-execute-block-or-clause-ipython
              :help "Execute block-or-clause through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-block-or-clause-python3" py-execute-block-or-clause-python3
              :help "Execute block-or-clause through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-block-or-clause-python2" py-execute-block-or-clause-python2
              :help "Execute block-or-clause through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-block-or-clause-python2.7" py-execute-block-or-clause-python2.7
              :help "Execute block-or-clause through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-block-or-clause-jython" py-execute-block-or-clause-jython
              :help "Execute block-or-clause through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-block-or-clause-python3.2" py-execute-block-or-clause-python3.2
              :help "Execute block-or-clause through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-block-or-clause-python-dedicated" py-execute-block-or-clause-python-dedicated
              :help "Execute block-or-clause through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-ipython-dedicated" py-execute-block-or-clause-ipython-dedicated
              :help "Execute block-or-clause through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-python3-dedicated" py-execute-block-or-clause-python3-dedicated
              :help "Execute block-or-clause through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-python2-dedicated" py-execute-block-or-clause-python2-dedicated
              :help "Execute block-or-clause through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-python2.7-dedicated" py-execute-block-or-clause-python2.7-dedicated
              :help "Execute block-or-clause through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-jython-dedicated" py-execute-block-or-clause-jython-dedicated
              :help "Execute block-or-clause through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-python3.2-dedicated" py-execute-block-or-clause-python3.2-dedicated
              :help "Execute block-or-clause through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-block-or-clause-python-switch" py-execute-block-or-clause-python-switch
              :help "Execute block-or-clause through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-block-or-clause-ipython-switch" py-execute-block-or-clause-ipython-switch
              :help "Execute block-or-clause through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-block-or-clause-python3-switch" py-execute-block-or-clause-python3-switch
              :help "Execute block-or-clause through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-block-or-clause-python2-switch" py-execute-block-or-clause-python2-switch
              :help "Execute block-or-clause through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-block-or-clause-python2.7-switch" py-execute-block-or-clause-python2.7-switch
              :help "Execute block-or-clause through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-block-or-clause-jython-switch" py-execute-block-or-clause-jython-switch
              :help "Execute block-or-clause through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-block-or-clause-python3.2-switch" py-execute-block-or-clause-python3.2-switch
              :help "Execute block-or-clause through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-block-or-clause-python-dedicated-switch" py-execute-block-or-clause-python-dedicated-switch
              :help "Execute block-or-clause through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-ipython-dedicated-switch" py-execute-block-or-clause-ipython-dedicated-switch
              :help "Execute block-or-clause through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-python3-dedicated-switch" py-execute-block-or-clause-python3-dedicated-switch
              :help "Execute block-or-clause through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-python2-dedicated-switch" py-execute-block-or-clause-python2-dedicated-switch
              :help "Execute block-or-clause through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-python2.7-dedicated-switch" py-execute-block-or-clause-python2.7-dedicated-switch
              :help "Execute block-or-clause through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-jython-dedicated-switch" py-execute-block-or-clause-jython-dedicated-switch
              :help "Execute block-or-clause through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-block-or-clause-python3.2-dedicated-switch" py-execute-block-or-clause-python3.2-dedicated-switch
              :help "Execute block-or-clause through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )

            ;; def
            ("Execute def ... "
             :help "Execute def functions"
             ["py-execute-def-python" py-execute-def-python
              :help "Execute def through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-def-ipython" py-execute-def-ipython
              :help "Execute def through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-def-python3" py-execute-def-python3
              :help "Execute def through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-def-python2" py-execute-def-python2
              :help "Execute def through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-def-python2.7" py-execute-def-python2.7
              :help "Execute def through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-def-jython" py-execute-def-jython
              :help "Execute def through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-def-python3.2" py-execute-def-python3.2
              :help "Execute def through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-def-python-dedicated" py-execute-def-python-dedicated
              :help "Execute def through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-ipython-dedicated" py-execute-def-ipython-dedicated
              :help "Execute def through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-python3-dedicated" py-execute-def-python3-dedicated
              :help "Execute def through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-python2-dedicated" py-execute-def-python2-dedicated
              :help "Execute def through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-python2.7-dedicated" py-execute-def-python2.7-dedicated
              :help "Execute def through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-jython-dedicated" py-execute-def-jython-dedicated
              :help "Execute def through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-python3.2-dedicated" py-execute-def-python3.2-dedicated
              :help "Execute def through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-def-python-switch" py-execute-def-python-switch
              :help "Execute def through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-def-ipython-switch" py-execute-def-ipython-switch
              :help "Execute def through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-def-python3-switch" py-execute-def-python3-switch
              :help "Execute def through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-def-python2-switch" py-execute-def-python2-switch
              :help "Execute def through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-def-python2.7-switch" py-execute-def-python2.7-switch
              :help "Execute def through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-def-jython-switch" py-execute-def-jython-switch
              :help "Execute def through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-def-python3.2-switch" py-execute-def-python3.2-switch
              :help "Execute def through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-def-python-dedicated-switch" py-execute-def-python-dedicated-switch
              :help "Execute def through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-ipython-dedicated-switch" py-execute-def-ipython-dedicated-switch
              :help "Execute def through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-python3-dedicated-switch" py-execute-def-python3-dedicated-switch
              :help "Execute def through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-python2-dedicated-switch" py-execute-def-python2-dedicated-switch
              :help "Execute def through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-python2.7-dedicated-switch" py-execute-def-python2.7-dedicated-switch
              :help "Execute def through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-jython-dedicated-switch" py-execute-def-jython-dedicated-switch
              :help "Execute def through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-def-python3.2-dedicated-switch" py-execute-def-python3.2-dedicated-switch
              :help "Execute def through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )

            ;; class
            ("Execute class ... "
             :help "Execute class functions"
             ["py-execute-class-python" py-execute-class-python
              :help "Execute class through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-class-ipython" py-execute-class-ipython
              :help "Execute class through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-class-python3" py-execute-class-python3
              :help "Execute class through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-class-python2" py-execute-class-python2
              :help "Execute class through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-class-python2.7" py-execute-class-python2.7
              :help "Execute class through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-class-jython" py-execute-class-jython
              :help "Execute class through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-class-python3.2" py-execute-class-python3.2
              :help "Execute class through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-class-python-dedicated" py-execute-class-python-dedicated
              :help "Execute class through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-ipython-dedicated" py-execute-class-ipython-dedicated
              :help "Execute class through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-python3-dedicated" py-execute-class-python3-dedicated
              :help "Execute class through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-python2-dedicated" py-execute-class-python2-dedicated
              :help "Execute class through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-python2.7-dedicated" py-execute-class-python2.7-dedicated
              :help "Execute class through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-jython-dedicated" py-execute-class-jython-dedicated
              :help "Execute class through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-python3.2-dedicated" py-execute-class-python3.2-dedicated
              :help "Execute class through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-class-python-switch" py-execute-class-python-switch
              :help "Execute class through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-class-ipython-switch" py-execute-class-ipython-switch
              :help "Execute class through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-class-python3-switch" py-execute-class-python3-switch
              :help "Execute class through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-class-python2-switch" py-execute-class-python2-switch
              :help "Execute class through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-class-python2.7-switch" py-execute-class-python2.7-switch
              :help "Execute class through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-class-jython-switch" py-execute-class-jython-switch
              :help "Execute class through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-class-python3.2-switch" py-execute-class-python3.2-switch
              :help "Execute class through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-class-python-dedicated-switch" py-execute-class-python-dedicated-switch
              :help "Execute class through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-ipython-dedicated-switch" py-execute-class-ipython-dedicated-switch
              :help "Execute class through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-python3-dedicated-switch" py-execute-class-python3-dedicated-switch
              :help "Execute class through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-python2-dedicated-switch" py-execute-class-python2-dedicated-switch
              :help "Execute class through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-python2.7-dedicated-switch" py-execute-class-python2.7-dedicated-switch
              :help "Execute class through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-jython-dedicated-switch" py-execute-class-jython-dedicated-switch
              :help "Execute class through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-class-python3.2-dedicated-switch" py-execute-class-python3.2-dedicated-switch
              :help "Execute class through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )

            ;; region
            ("Execute region ... "
             :help "Execute region functions"
             ["py-execute-region-python" py-execute-region-python
              :help "Execute region through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-region-ipython" py-execute-region-ipython
              :help "Execute region through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-region-python3" py-execute-region-python3
              :help "Execute region through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-region-python2" py-execute-region-python2
              :help "Execute region through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-region-python2.7" py-execute-region-python2.7
              :help "Execute region through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-region-jython" py-execute-region-jython
              :help "Execute region through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-region-python3.2" py-execute-region-python3.2
              :help "Execute region through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-region-python-dedicated" py-execute-region-python-dedicated
              :help "Execute region through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-ipython-dedicated" py-execute-region-ipython-dedicated
              :help "Execute region through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-python3-dedicated" py-execute-region-python3-dedicated
              :help "Execute region through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-python2-dedicated" py-execute-region-python2-dedicated
              :help "Execute region through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-python2.7-dedicated" py-execute-region-python2.7-dedicated
              :help "Execute region through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-jython-dedicated" py-execute-region-jython-dedicated
              :help "Execute region through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-python3.2-dedicated" py-execute-region-python3.2-dedicated
              :help "Execute region through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-region-python-switch" py-execute-region-python-switch
              :help "Execute region through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-region-ipython-switch" py-execute-region-ipython-switch
              :help "Execute region through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-region-python3-switch" py-execute-region-python3-switch
              :help "Execute region through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-region-python2-switch" py-execute-region-python2-switch
              :help "Execute region through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-region-python2.7-switch" py-execute-region-python2.7-switch
              :help "Execute region through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-region-jython-switch" py-execute-region-jython-switch
              :help "Execute region through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-region-python3.2-switch" py-execute-region-python3.2-switch
              :help "Execute region through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-region-python-dedicated-switch" py-execute-region-python-dedicated-switch
              :help "Execute region through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-ipython-dedicated-switch" py-execute-region-ipython-dedicated-switch
              :help "Execute region through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-python3-dedicated-switch" py-execute-region-python3-dedicated-switch
              :help "Execute region through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-python2-dedicated-switch" py-execute-region-python2-dedicated-switch
              :help "Execute region through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-python2.7-dedicated-switch" py-execute-region-python2.7-dedicated-switch
              :help "Execute region through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-jython-dedicated-switch" py-execute-region-jython-dedicated-switch
              :help "Execute region through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-region-python3.2-dedicated-switch" py-execute-region-python3.2-dedicated-switch
              :help "Execute region through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )

            ;; buffer
            ("Execute buffer ... "
             :help "Execute buffer functions"
             ["py-execute-buffer-python" py-execute-buffer-python
              :help "Execute buffer through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-buffer-ipython" py-execute-buffer-ipython
              :help "Execute buffer through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-buffer-python3" py-execute-buffer-python3
              :help "Execute buffer through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-buffer-python2" py-execute-buffer-python2
              :help "Execute buffer through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-buffer-python2.7" py-execute-buffer-python2.7
              :help "Execute buffer through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-buffer-jython" py-execute-buffer-jython
              :help "Execute buffer through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-buffer-python3.2" py-execute-buffer-python3.2
              :help "Execute buffer through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-buffer-python-dedicated" py-execute-buffer-python-dedicated
              :help "Execute buffer through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-ipython-dedicated" py-execute-buffer-ipython-dedicated
              :help "Execute buffer through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-python3-dedicated" py-execute-buffer-python3-dedicated
              :help "Execute buffer through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-python2-dedicated" py-execute-buffer-python2-dedicated
              :help "Execute buffer through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-python2.7-dedicated" py-execute-buffer-python2.7-dedicated
              :help "Execute buffer through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-jython-dedicated" py-execute-buffer-jython-dedicated
              :help "Execute buffer through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-python3.2-dedicated" py-execute-buffer-python3.2-dedicated
              :help "Execute buffer through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-buffer-python-switch" py-execute-buffer-python-switch
              :help "Execute buffer through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-buffer-ipython-switch" py-execute-buffer-ipython-switch
              :help "Execute buffer through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-buffer-python3-switch" py-execute-buffer-python3-switch
              :help "Execute buffer through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-buffer-python2-switch" py-execute-buffer-python2-switch
              :help "Execute buffer through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-buffer-python2.7-switch" py-execute-buffer-python2.7-switch
              :help "Execute buffer through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-buffer-jython-switch" py-execute-buffer-jython-switch
              :help "Execute buffer through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-buffer-python3.2-switch" py-execute-buffer-python3.2-switch
              :help "Execute buffer through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-buffer-python-dedicated-switch" py-execute-buffer-python-dedicated-switch
              :help "Execute buffer through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-ipython-dedicated-switch" py-execute-buffer-ipython-dedicated-switch
              :help "Execute buffer through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-python3-dedicated-switch" py-execute-buffer-python3-dedicated-switch
              :help "Execute buffer through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-python2-dedicated-switch" py-execute-buffer-python2-dedicated-switch
              :help "Execute buffer through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-python2.7-dedicated-switch" py-execute-buffer-python2.7-dedicated-switch
              :help "Execute buffer through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-jython-dedicated-switch" py-execute-buffer-jython-dedicated-switch
              :help "Execute buffer through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-buffer-python3.2-dedicated-switch" py-execute-buffer-python3.2-dedicated-switch
              :help "Execute buffer through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )

            ;; expression
            ("Execute expression ... "
             :help "Execute expression functions"
             ["py-execute-expression-python" py-execute-expression-python
              :help "Execute expression through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-expression-ipython" py-execute-expression-ipython
              :help "Execute expression through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-expression-python3" py-execute-expression-python3
              :help "Execute expression through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-expression-python2" py-execute-expression-python2
              :help "Execute expression through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-expression-python2.7" py-execute-expression-python2.7
              :help "Execute expression through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-expression-jython" py-execute-expression-jython
              :help "Execute expression through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-expression-python3.2" py-execute-expression-python3.2
              :help "Execute expression through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-expression-python-dedicated" py-execute-expression-python-dedicated
              :help "Execute expression through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-ipython-dedicated" py-execute-expression-ipython-dedicated
              :help "Execute expression through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-python3-dedicated" py-execute-expression-python3-dedicated
              :help "Execute expression through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-python2-dedicated" py-execute-expression-python2-dedicated
              :help "Execute expression through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-python2.7-dedicated" py-execute-expression-python2.7-dedicated
              :help "Execute expression through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-jython-dedicated" py-execute-expression-jython-dedicated
              :help "Execute expression through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-python3.2-dedicated" py-execute-expression-python3.2-dedicated
              :help "Execute expression through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-expression-python-switch" py-execute-expression-python-switch
              :help "Execute expression through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-expression-ipython-switch" py-execute-expression-ipython-switch
              :help "Execute expression through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-expression-python3-switch" py-execute-expression-python3-switch
              :help "Execute expression through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-expression-python2-switch" py-execute-expression-python2-switch
              :help "Execute expression through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-expression-python2.7-switch" py-execute-expression-python2.7-switch
              :help "Execute expression through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-expression-jython-switch" py-execute-expression-jython-switch
              :help "Execute expression through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-expression-python3.2-switch" py-execute-expression-python3.2-switch
              :help "Execute expression through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-expression-python-dedicated-switch" py-execute-expression-python-dedicated-switch
              :help "Execute expression through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-ipython-dedicated-switch" py-execute-expression-ipython-dedicated-switch
              :help "Execute expression through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-python3-dedicated-switch" py-execute-expression-python3-dedicated-switch
              :help "Execute expression through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-python2-dedicated-switch" py-execute-expression-python2-dedicated-switch
              :help "Execute expression through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-python2.7-dedicated-switch" py-execute-expression-python2.7-dedicated-switch
              :help "Execute expression through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-jython-dedicated-switch" py-execute-expression-jython-dedicated-switch
              :help "Execute expression through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-expression-python3.2-dedicated-switch" py-execute-expression-python3.2-dedicated-switch
              :help "Execute expression through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )            ;; partial-expression

            ("Execute partial-expression ... "
             :help "Execute partial-expression functions"
             ["py-execute-partial-expression-python" py-execute-partial-expression-python
              :help "Execute minor-expression through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-minor-expression-ipython" py-execute-minor-expression-ipython
              :help "Execute minor-expression through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-minor-expression-python3" py-execute-minor-expression-python3
              :help "Execute minor-expression through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-minor-expression-python2" py-execute-minor-expression-python2
              :help "Execute minor-expression through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-minor-expression-python2.7" py-execute-minor-expression-python2.7
              :help "Execute minor-expression through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-minor-expression-jython" py-execute-minor-expression-jython
              :help "Execute minor-expression through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-minor-expression-python3.2" py-execute-minor-expression-python3.2
              :help "Execute minor-expression through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-minor-expression-python-dedicated" py-execute-minor-expression-python-dedicated
              :help "Execute minor-expression through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-ipython-dedicated" py-execute-minor-expression-ipython-dedicated
              :help "Execute minor-expression through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-python3-dedicated" py-execute-minor-expression-python3-dedicated
              :help "Execute minor-expression through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-python2-dedicated" py-execute-minor-expression-python2-dedicated
              :help "Execute minor-expression through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-python2.7-dedicated" py-execute-minor-expression-python2.7-dedicated
              :help "Execute minor-expression through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-jython-dedicated" py-execute-minor-expression-jython-dedicated
              :help "Execute minor-expression through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-python3.2-dedicated" py-execute-minor-expression-python3.2-dedicated
              :help "Execute minor-expression through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-minor-expression-python-switch" py-execute-minor-expression-python-switch
              :help "Execute minor-expression through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-minor-expression-ipython-switch" py-execute-minor-expression-ipython-switch
              :help "Execute minor-expression through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-minor-expression-python3-switch" py-execute-minor-expression-python3-switch
              :help "Execute minor-expression through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-minor-expression-python2-switch" py-execute-minor-expression-python2-switch
              :help "Execute minor-expression through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-minor-expression-python2.7-switch" py-execute-minor-expression-python2.7-switch
              :help "Execute minor-expression through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-minor-expression-jython-switch" py-execute-minor-expression-jython-switch
              :help "Execute minor-expression through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-minor-expression-python3.2-switch" py-execute-minor-expression-python3.2-switch
              :help "Execute minor-expression through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-minor-expression-python-dedicated-switch" py-execute-minor-expression-python-dedicated-switch
              :help "Execute minor-expression through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-ipython-dedicated-switch" py-execute-minor-expression-ipython-dedicated-switch
              :help "Execute minor-expression through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-python3-dedicated-switch" py-execute-minor-expression-python3-dedicated-switch
              :help "Execute minor-expression through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-python2-dedicated-switch" py-execute-minor-expression-python2-dedicated-switch
              :help "Execute minor-expression through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-python2.7-dedicated-switch" py-execute-minor-expression-python2.7-dedicated-switch
              :help "Execute minor-expression through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-jython-dedicated-switch" py-execute-minor-expression-jython-dedicated-switch
              :help "Execute minor-expression through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-minor-expression-python3.2-dedicated-switch" py-execute-minor-expression-python3.2-dedicated-switch
              :help "Execute minor-expression through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )            ;; line

            ("Execute line ... "
             :help "Execute line functions"
             ["py-execute-line-python" py-execute-line-python
              :help "Execute line through a Python interpreter.
        With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-line-ipython" py-execute-line-ipython
              :help "Execute line through an IPython interpreter.
        With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-line-python3" py-execute-line-python3
              :help "Execute line through a Python3 interpreter.
        With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-line-python2" py-execute-line-python2
              :help "Execute line through a Python2 interpreter.
        With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-line-python2.7" py-execute-line-python2.7
              :help "Execute line through a Python2.7 interpreter.
        With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-line-jython" py-execute-line-jython
              :help "Execute line through a Jython interpreter.
        With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-line-python3.2" py-execute-line-python3.2
              :help "Execute line through a Python3.2 interpreter.
        With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated
             ["py-execute-line-python-dedicated" py-execute-line-python-dedicated
              :help "Execute line through a unique Python interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-ipython-dedicated" py-execute-line-ipython-dedicated
              :help "Execute line through a unique IPython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-python3-dedicated" py-execute-line-python3-dedicated
              :help "Execute line through a unique Python3 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-python2-dedicated" py-execute-line-python2-dedicated
              :help "Execute line through a unique Python2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-python2.7-dedicated" py-execute-line-python2.7-dedicated
              :help "Execute line through a unique Python2.7 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-jython-dedicated" py-execute-line-jython-dedicated
              :help "Execute line through a unique Jython interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-python3.2-dedicated" py-execute-line-python3.2-dedicated
              :help "Execute line through a unique Python3.2 interpreter.
Optional \\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. "]
             ;; switch
             ["py-execute-line-python-switch" py-execute-line-python-switch
              :help "Execute line through a Python interpreter.
With \\[universal-argument] use an unique Python interpreter. "]
             ["py-execute-line-ipython-switch" py-execute-line-ipython-switch
              :help "Execute line through an IPython interpreter.
With \\[universal-argument] use an unique IPython interpreter. "]
             ["py-execute-line-python3-switch" py-execute-line-python3-switch
              :help "Execute line through a Python3 interpreter.
With \\[universal-argument] use an unique Python3 interpreter. "]
             ["py-execute-line-python2-switch" py-execute-line-python2-switch
              :help "Execute line through a Python2 interpreter.
With \\[universal-argument] use an unique Python2 interpreter. "]
             ["py-execute-line-python2.7-switch" py-execute-line-python2.7-switch
              :help "Execute line through a Python2.7 interpreter.
With \\[universal-argument] use an unique Python2.7 interpreter. "]
             ["py-execute-line-jython-switch" py-execute-line-jython-switch
              :help "Execute line through a Jython interpreter.
With \\[universal-argument] use an unique Jython interpreter. "]
             ["py-execute-line-python3.2-switch" py-execute-line-python3.2-switch
              :help "Execute line through a Python3.2 interpreter.
With \\[universal-argument] use an unique Python3.2 interpreter. "]
             ;; dedicated-switch
             ["py-execute-line-python-dedicated-switch" py-execute-line-python-dedicated-switch
              :help "Execute line through a unique Python interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-ipython-dedicated-switch" py-execute-line-ipython-dedicated-switch
              :help "Execute line through a uniquen IPython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-python3-dedicated-switch" py-execute-line-python3-dedicated-switch
              :help "Execute line through a unique Python3 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-python2-dedicated-switch" py-execute-line-python2-dedicated-switch
              :help "Execute line through a unique Python2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-python2.7-dedicated-switch" py-execute-line-python2.7-dedicated-switch
              :help "Execute line through a unique Python2.7 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-jython-dedicated-switch" py-execute-line-jython-dedicated-switch
              :help "Execute line through a unique Jython interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             ["py-execute-line-python3.2-dedicated-switch" py-execute-line-python3.2-dedicated-switch
              :help "Execute line through a unique Python3.2 interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. "]
             )))

        ;; Menu command forms
        (easy-menu-define py-menu map "Python Mode Commands"
          `("PyEdit"
            :help "Python-specific features"
            ["Copy block" py-copy-block
             :help "`py-copy-block'
Copy innermost compound statement at point"]

            ["Copy clause" py-copy-clause
             :help "`py-copy-clause'
Copy clause at point"]

            ["Copy def-or-class" py-copy-def-or-class
             :help "`py-copy-def-or-class'
Copy innermost definition at point"]

            ["Copy def" py-copy-def
             :help "`py-copy-def'
Copy method/function definition at point"]

            ["Copy class" py-copy-class
             :help "`py-copy-class'
Copy class definition at point"]

            ["Copy statement" py-copy-statement
             :help "`py-copy-statement'
Copy statement at point"]
            ["Copy expression" py-copy-expression
             :help "`py-copy-expression'
Copy expression at point"]

            ["Copy partial expression" py-copy-partial-expression
             :help "`py-copy-partial-expression'
\".\" operators delimit a partial-expression expression on it's level"]
            "-"
            ["Beginning of block" py-beginning-of-block
             :help "`py-beginning-of-block'
Go to start of innermost compound statement at point"]
            ["End of block" py-end-of-block
             :help "`py-end-of-block'
Go to end of innermost compound statement at point"]
            ["Beginning of Def-or-Class" py-beginning-of-def-or-class
             :help "`py-beginning-of-def-or-class'
Go to start of innermost definition at point"]
            ["End of Def-or-Class" py-end-of-def-or-class
             :help "`py-end-of-def-or-class'
Go to end of innermost function definition at point"]
            ["Beginning of class" py-beginning-of-class
             :help "`py-beginning-of-class'
Go to start of class definition "]
            ["End of class" py-end-of-class
             :help "`py-end-of-class'
Go to end of class definition "]
            ["Beginning of statement" py-beginning-of-statement
             :help "`py-beginning-of-statement'
Go to start of a Python statement"]
            ["End of statement" py-end-of-statement
             :help "`py-end-of-statement'
Go to end of a Python statement"]
            ["Beginning of expression" py-beginning-of-expression
             :help "Go to the beginning of a compound python expression.

A a compound python expression might be concatenated by \".\" operator, thus composed by minor python expressions.

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes."]
            ["End of expression" py-end-of-expression
             :help "`py-end-of-expression'
Go to the end of a compound python expression.

A a compound python expression might be concatenated by \".\" operator, thus composed by minor python expressions.

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes."]
            ["Beginning of minor expression" py-beginning-of-partial-expression
             :help "`py-beginning-of-partial-expression'
Go to start of an minor expression

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes."]
            ["End of partial-expression" py-end-of-partial-expression
             :help "`py-end-of-partial-expression'
Go to end of an partial-expression

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes."]
            ["Backward into nomenclature" py-backward-into-nomenclature
             :help " `py-backward-into-nomenclature'
Go backward into nomenclature

A nomenclature is a fancy way of saying AWordWithMixedCaseNotUnderscores. "]
            ["Forward into nomenclature" py-forward-into-nomenclature
             :help " `py-forward-into-nomenclature'
Go forward into nomenclature

A nomenclature is a fancy way of saying AWordWithMixedCaseNotUnderscores. "]
            "-"
            ["Down statement lc" py-down-statement-lc
             :help "`py-down-statement-lc'
Goto beginning of line following end of statement.

Returns position reached, if successful, nil otherwise.

\"-lc\" stands for \"left-corner\" - a complementary command travelling left, whilst `py-end-of-statement' stops at right corner.

See also `py-down-statement': down from current definition to next beginning of statement below. "]
            ["Down block lc" py-down-block-lc
             :help "`py-down-block-lc'
Goto beginning of line following end of block.

Returns position reached, if successful, nil otherwise.

\"-lc\" stands for \"left-corner\" - a complementary command travelling left, whilst `py-end-of-block' stops at right corner.

See also `py-down-block': down from current definition to next beginning of block below. "]
            ["Down def lc" py-down-def-lc
             :help "`py-down-def-lc'
Goto beginning of line following end of def.

Returns position reached, if successful, nil otherwise.

\"-lc\" stands for \"left-corner\" - a complementary command travelling left, whilst `py-end-of-def' stops at right corner.

See also `py-down-def': down from current definition to next beginning of def below.
 "]
            ["Down statement" py-down-statement
             :help "`py-down-statement'

Go to the beginning of next statement below in buffer.

Returns indentation if statement found, nil otherwise. "]
            ["Down block" py-down-block
             :help "`py-down-block'

Go to the beginning of next block below in buffer.

Returns indentation if block found, nil otherwise. "]
            ["Down def" py-down-def
             :help "`py-down-def'

Go to the beginning of next function definition below in buffer.

Returns indentation if found, nil otherwise. "]))
        ;; Python shell menu
        (easy-menu-define py-menu map "Python Shells"
          `("PyShell"
            :help "Python Shells"
            ["Default interpreter" py-shell
             :help "`py-shell'
Switch to `inferior' Python in separate buffer"]

            ;; ["Toggle enforcement of default interpreter" toggle-force-py-shell-name-p
            ;; :help "If customized default `py-shell-name' should be enforced upon execution. "]

            ["Enforce py-shell-name" force-py-shell-name-p-on
             :help "Enforce customized default `py-shell-name' should upon execution. "]

            ["Don't enforce default interpreter" force-py-shell-name-p-off
             :help "Make execute commands guess interpreter from environment"]

            ;; ["Enforce locally Python shell sessions interpreter " toggle-force-local-shell
            ;; :help "If locally indicated Python shell should be taken and
            ;; enforced upon sessions execute commands. "]

            ["Enforce local Python shell " py-force-local-shell-on
             :help "Locally indicated Python being enforced upon sessions execute commands. "]

            ["Remove local Python shell enforcement, restore default" py-force-local-shell-off
             :help "Restore `py-shell-name' default value and `behaviour'. "]

            "-"

            ["python" python
             :help "`python'
Start an Python interpreter.

Optional C-u prompts for options to pass to the Python interpreter. See `py-python-command-args'."]
            ["ipython" ipython
             :help "`ipython'
Start an IPython interpreter.

Optional C-u prompts for options to pass to the IPython interpreter. See `py-python-command-args'."]
            ["python3" python3
             :help "`python3'
Start an Python3 interpreter.

Optional C-u prompts for options to pass to the Python3 interpreter. See `py-python-command-args'."]
            ["python2" python2
             :help "`python2'
Start an Python2 interpreter.

Optional C-u prompts for options to pass to the Python2 interpreter. See `py-python-command-args'."]
            ["python2.7" python2.7
             :help "`python2.7'
Start an Python2.7 interpreter.

Optional C-u prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'."]
            ["jython" jython
             :help "`jython'
Start an Jython interpreter.

Optional C-u prompts for options to pass to the Jython interpreter. See `py-python-command-args'."]
            ["python3.2" python3.2
             :help "`python3.2'
Start an Python3.2 interpreter.

Optional C-u prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'."]
            "-"
            ["python-dedicated" python-dedicated
             :help "`python-dedicated'
Start an unique Python interpreter in another window.

Optional C-u prompts for options to pass to the Python interpreter. See `py-python-command-args'."]
            ["ipython-dedicated" ipython-dedicated
             :help "`ipython-dedicated'
Start an unique IPython interpreter in another window.

Optional C-u prompts for options to pass to the IPython interpreter. See `py-python-command-args'."]
            ["python3-dedicated" python3-dedicated
             :help "`python3-dedicated'
Start an unique Python3 interpreter in another window.

Optional C-u prompts for options to pass to the Python3 interpreter. See `py-python-command-args'."]
            ["python2-dedicated" python2-dedicated
             :help "`python2-dedicated'
Start an unique Python2 interpreter in another window.

Optional C-u prompts for options to pass to the Python2 interpreter. See `py-python-command-args'."]
            ["python2.7-dedicated" python2.7-dedicated
             :help "`python2'.7-dedicated
Start an unique Python2.7 interpreter in another window.

Optional C-u prompts for options to pass to the Python2.7 interpreter. See `py-python-command-args'."]
            ["jython-dedicated" jython-dedicated
             :help "`jython-dedicated'
Start an unique Jython interpreter in another window.

Optional C-u prompts for options to pass to the Jython interpreter. See `py-python-command-args'."]
            ["python3.2-dedicated" python3.2-dedicated
             :help "`python3.2-dedicated'
Start an unique Python3.2 interpreter in another window.

Optional C-u prompts for options to pass to the Python3.2 interpreter. See `py-python-command-args'."]
            "-"

            ["Toggle split-windows-on-execute" py-toggle-split-windows-on-execute
             :help "Switch boolean `py-split-windows-on-execute-p'."]
            ["Switch split-windows-on-execute ON" py-split-windows-on-execute-on
             :help "Switch `py-split-windows-on-execute-p' ON. "]
            ["Switch split-windows-on-execute OFF" py-split-windows-on-execute-off
             :help "Switch `py-split-windows-on-execute-p' OFF. "]

            ["Toggle shell-switch-buffers-on-execute" py-toggle-shell-switch-buffers-on-execute
             :help "Switch boolean `py-switch-buffers-on-execute-p'."]
            ["Switch shell-switch-buffers-on-execute ON" py-shell-switch-buffers-on-execute-on
             :help "Switch `py-switch-buffers-on-execute-p' ON. "]
            ["Switch shell-switch-buffers-on-execute OFF" py-shell-switch-buffers-on-execute-off
             :help "Switch `py-switch-buffers-on-execute-p' OFF. "]

            ))
        map))

(defvar skeleton-further-elements)
(define-derived-mode python-mode fundamental-mode "Python"
  "Major mode for editing Python files.

To submit a problem report, enter `\\[py-submit-bug-report]' from a
`python-mode' buffer.  Do `\\[py-describe-mode]' for detailed
documentation.  To see what version of `python-mode' you are running,
enter `\\[py-version]'.

This mode knows about Python indentation, tokens, comments and
continuation lines.  Paragraphs are separated by blank lines only.

COMMANDS

VARIABLES

py-indent-offset\t\tindentation increment
py-block-comment-prefix\t\tcomment string used by `comment-region'
py-shell-name\t\tshell command to invoke Python interpreter
py-temp-directory\t\tdirectory used for temp files (if needed)
py-beep-if-tab-change\t\tring the bell if `tab-width' is changed

\\{python-mode-map}"
  :group 'python-mode
  (set (make-local-variable 'font-lock-defaults)
       '(python-font-lock-keywords nil nil nil nil
				   (font-lock-syntactic-keywords
				    . python-font-lock-syntactic-keywords)
				   ;; This probably isn't worth it.
				   ;; (font-lock-syntactic-face-function
				   ;;  . python-font-lock-syntactic-face-function)
                                   ))
  (set (make-local-variable 'parse-sexp-lookup-properties) t)
  (set (make-local-variable 'parse-sexp-ignore-comments) t)
  (set (make-local-variable 'comment-start) "# ")
  (set (make-local-variable 'comment-start-skip) "^[ \t]*#+ *")
  (set (make-local-variable 'comment-column) 40)
  (set (make-local-variable 'comment-indent-function) #'py-comment-indent-function)
  (set (make-local-variable 'indent-region-function) 'py-indent-region)
  (set (make-local-variable 'indent-line-function) 'py-indent-line)
  (set (make-local-variable 'hs-hide-comments-when-hiding-all) 'py-hide-comments-when-hiding-all)
  (set (make-local-variable 'outline-heading-end-regexp) ":\\s-*\n")
  (set (make-local-variable 'outline-level) #'python-outline-level)
  (set (make-local-variable 'open-paren-in-column-0-is-defun-start) nil)
  (set (make-local-variable 'add-log-current-defun-function) 'py-current-defun)
  (set (make-local-variable 'paragraph-start) "\\s-*$")
  (set (make-local-variable 'fill-paragraph-function) 'py-fill-paragraph)
  (set (make-local-variable 'require-final-newline) mode-require-final-newline)
  (make-local-variable 'python-saved-check-command)
  (set (make-local-variable 'tab-width) py-indent-offset)

  ;; (set (make-local-variable 'outline-regexp)
  ;; (rx (* space) (or "class" "def" "elif" "else" "except" "finally"
  ;; "for" "if" "try" "while" "with")
  ;; symbol-end))

  (set (make-local-variable 'outline-regexp)
       (concat (mapconcat 'identity
                          (mapcar #'(lambda (x) (concat "^\\s-*" x "\\_>"))
                                  py-outline-mode-keywords)
                          "\\|")))
  (set (make-local-variable 'eldoc-documentation-function)
       #'py-eldoc-function)
  (set (make-local-variable 'skeleton-further-elements)
       '((< '(backward-delete-char-untabify (min py-indent-offset
                                                 (current-column))))
         (^ '(- (1+ (current-indentation))))))
  (setq completion-at-point-functions nil)
  ;; setting of var `py-local-versioned-command' is
  ;; needed to detect the completion command to choose

  ;; py-complete-function (set (make-local-variable
  ;; 'python-local-version) py-complete-function) when
  ;; set, `py-complete-function' it enforced
  (set (make-local-variable 'py-local-command) (py-choose-shell))
  ;; customized `py-complete-function' precedes
  (unless py-complete-function
    (cond ((string-match "[iI][pP]ython" py-local-command)
           ;; customized `py-complete-function' precedes
           (setq py-complete-function 'ipython-complete))
          ;; if `py-local-command' already contains version, use it
          ((string-match "[0-9]" py-local-command)
           (set (make-local-variable 'py-local-versioned-command) py-local-command))
          (t (set (make-local-variable 'python-version-numbers) (shell-command-to-string (concat py-local-command " -c \"from sys import version_info; print version_info[0:2]\"")))
             (set (make-local-variable 'py-local-versioned-command) (concat py-local-command (replace-regexp-in-string "," "." (replace-regexp-in-string "[()\.\n ]" "" python-version-numbers)))))))
  (if py-local-versioned-command
      (when (and (interactive-p) py-verbose-p) (message "py-local-versioned-command %s" py-local-versioned-command))
    (when (and (interactive-p) py-verbose-p) (message "py-local-command %s" py-local-command)))
  (if py-local-versioned-command
      (cond ((string-match "[pP]ython3[^[:alpha:]]*$" py-local-versioned-command)
             (setq py-complete-function 'py-python-script-complete))
            ((string-match "[pP]ython2[^[:alpha:]]*$" py-local-versioned-command)
             (setq py-complete-function 'py-python-script-complete))
            (t (setq py-complete-function 'py-completion-at-point)))
    ;; should never reach this clause
    (setq py-complete-function 'py-completion-at-point))
  (if py-complete-function
      (add-hook 'completion-at-point-functions
                py-complete-function nil 'local)
    (add-hook 'completion-at-point-functions
              #'python-shell-send-setup-code))
  (when (and py-imenu-create-index-p (fboundp 'imenu-add-to-menubar)(ignore-errors (require 'imenu)))
    (setq imenu-create-index-function #'py-imenu-create-index-new)
    (imenu-add-to-menubar "PyIndex"))
  (when py-org-cycle-p
    (define-key python-mode-map (kbd "<backtab>") 'org-cycle))

  ;; (set (make-local-variable 'beginning-of-defun-function)
  ;; 'py-beginning-of-def-or-class)
  ;; (set (make-local-variable 'end-of-defun-function) 'py-end-of-def-or-class)

  (add-to-list 'hs-special-modes-alist
               (list
                'python-mode
                ;; start regex
                (concat (if py-hide-show-hide-docstrings
                            "^\\s-*\"\"\"\\|" "")
                        (mapconcat 'identity
                                   (mapcar #'(lambda (x) (concat "^\\s-*" x "\\_>"))
                                           py-hide-show-keywords)
                                   "\\|"))
                ;; end regex
                nil
                ;; comment-start regex
                "#"
                ;; forward-sexp function
                (lambda (arg)
                  (py-down-block-lc)
                  (skip-chars-backward " \t\n"))
                nil))
  (add-hook 'which-func-functions 'python-which-func nil t)

  ;; Now guess `py-indent-offset'
  (when py-smart-indentation
    (if (bobp)
        (save-excursion
          (save-restriction
            (widen)
            (while (and (not (eobp))
                        (or
                         (let ((erg (syntax-ppss)))
                           (or (nth 1 erg) (nth 8 erg)))
                         (eq 0 (current-indentation))))
              (forward-line 1))
            (back-to-indentation)
            (py-guess-indent-offset)))
      (py-guess-indent-offset)))
  (when py-load-pymacs-p (py-load-pymacs))
  ;; add the menu
  (if py-menu
      (easy-menu-add py-menu))
  (when py-hide-show-minor-mode-p (hs-minor-mode 1))
  ;; (py-send-string "import emacs")
  (when py-start-run-py-shell
    ;; py-shell may split window, provide restore
    (window-configuration-to-register 213465879)
    (unless (get-process (py-process-name))
      (let ((oldbuf (current-buffer)))
        (save-excursion
          (py-shell)
          (set-buffer oldbuf))))
    (jump-to-register 213465879))
  (run-mode-hooks 'python-mode-hook)
  (when py-outline-minor-mode-p (outline-minor-mode 1))
  (when (interactive-p) (message "python-mode loaded from: %s" "python-mode.el")))

(defadvice pdb (before gud-query-cmdline activate)
  "Provide a better default command line when called interactively."
  (interactive
   (list (gud-query-cmdline pdb-path
                            (file-name-nondirectory buffer-file-name)))))

(defalias 'py-hungry-delete-forward 'c-hungry-delete-forward)
(defalias 'py-hungry-delete-backwards 'c-hungry-delete-backwards)

(define-derived-mode python2-mode python-mode "Python2"
  "Edit and run code used by Python version 2 series. "
  :group 'Python
  :abbrev nil
  (set (make-local-variable 'py-exec-command) '(format "execfile(r'%s') # PYTHON-MODE\n" filename))
  (set (make-local-variable 'py-exec-string-command) '(format "exec(r'%s') # PYTHON-MODE\n" string))
  (py-toggle-shells "python2"))

(define-derived-mode python3-mode python-mode "Python3"
  "Edit and run code used by Python version 3 series. "
  :group 'Python
  :abbrev nil
  (set (make-local-variable 'py-exec-command) '(format "exec(compile(open('%s').read(), '%s', 'exec')) # PYTHON-MODE\n" file file))
  (set (make-local-variable 'py-exec-string-command) '(format "exec(r'(%s)') # PYTHON-MODE\n" string))
  (py-toggle-shells "python3"))

;; Utilities

(defun py-def-or-class-beginning-position ()
  "Returns beginning position of function or class definition. "
  (interactive)
  (let ((here (point))
        (pos (progn (py-beginning-of-def-or-class)(point))))
    (prog1
        (point)
      (when (and py-verbose-p (interactive-p)) (message "%s" pos))
      (goto-char here))))

(defun py-def-or-class-end-position ()
  "Returns end position of function or class definition. "
  (interactive)
  (let ((here (point))
        (pos (progn (py-end-of-def-or-class) (point))))
    (prog1
        (point)
      (when (and py-verbose-p (interactive-p)) (message "%s" pos))
      (goto-char here))))

(defun py-statement-beginning-position ()
  "Returns beginning position of statement. "
  (interactive)
  (let ((here (point))
        (pos (progn (py-beginning-of-statement)(point))))
    (prog1
        (point)
      (when (and py-verbose-p (interactive-p)) (message "%s" pos))
      (goto-char here))))

(defun py-statement-end-position ()
  "Returns end position of statement. "
  (interactive)
  (let (erg)
    (save-excursion
      (setq erg (py-end-of-statement)))
    (when (and py-verbose-p (interactive-p)) (message "%s" erg))
    erg))

(defun py-current-indentation ()
  "Returns beginning position of code in line. "
  (interactive)
  (let ((here (point))
        (pos (progn (back-to-indentation)(point))))
    (prog1
        (point)
      (when (and py-verbose-p (interactive-p)) (message "%s" pos))
      (goto-char here))))

(make-obsolete 'jpython-mode 'jython-mode nil)
(define-derived-mode jython-mode python-mode  "Jython"
  "Major mode for editing Jython files.
Like `python-mode', but sets up parameters for Jython subprocesses.
Runs `jython-mode-hook' after `python-mode-hook'."
  :group 'python-mode
  (py-toggle-shells "jython"))

;; It's handy to add recognition of Python files to the
;; interpreter-mode-alist and to auto-mode-alist.  With the former, we
;; can specify different `derived-modes' based on the #! line, but
;; with the latter, we can't.  So we just won't add them if they're
;; already added.

(let ((modes '(("jython" . jython-mode)
               ("python" . python-mode)
               ("python3" . python-mode))))
  (while modes
    (when (not (assoc (car modes) interpreter-mode-alist))
      (push (car modes) interpreter-mode-alist))
    (setq modes (cdr modes))))

(when (not (or (rassq 'python-mode auto-mode-alist)
               (rassq 'jython-mode auto-mode-alist)))
  (push '("\\.py$" . python-mode) auto-mode-alist))

(defun py-kill-emacs-hook ()
  "Delete files in `py-file-queue'.
These are Python temporary files awaiting execution."
  (mapc #'(lambda (filename)
            (ignore-errors (delete-file filename)))
        py-file-queue))

;; arrange to kill temp files when Emacs exists
(add-hook 'kill-emacs-hook 'py-kill-emacs-hook)
(add-hook 'comint-output-filter-functions 'py-pdbtrack-track-stack-file)

;; inside python-mode already
;; (add-hook 'python-mode-hook
;;           (lambda ()
;;             (defvar py-mode-map python-mode-map))
;;           (set (make-local-variable 'beginning-o1f-defun-function) 'py-beginning-of-def-or-class)
;;           (set (make-local-variable 'end-of-defun-function) 'py-end-of-def-or-class))

;; Add a designator to the minor mode strings
(or (assq 'py-pdbtrack-is-tracking-p minor-mode-alist)
    (push '(py-pdbtrack-is-tracking-p py-pdbtrack-minor-mode-string)
          minor-mode-alist))

(defun py-python-version (&optional executable verbose)
  "Returns versions number of a Python EXECUTABLE, string.

If no EXECUTABLE given, `py-shell-name' is used.
Interactively output of `--version' is displayed. "
  (interactive)
  (let* ((executable (or executable py-shell-name))
         (erg (string-strip (shell-command-to-string (concat executable " --version")))))
    (when (interactive-p) (message "%s" erg))
    (unless verbose (setq erg (cadr (split-string erg))))
    erg))

(defun py-version ()
  "Echo the current version of `python-mode' in the minibuffer."
  (interactive)
  (message "Using `python-mode' version %s" py-version)
  (py-keep-region-active))

(defun py-install-search-local ()
  (interactive)
  (let ((erg (split-string (shell-command-to-string (concat "find " default-directory " -maxdepth 9 -type f -name \"*python\"")))))))

;; (defun py-install-local-epdfree ()
;;   (interactive)
;;   (py-install-local-shells "MY-PATH/epdfree"))

(defun py-install-local-shells (&optional local path-prefix)
  "Builds Python-shell commands from executable found in LOCAL.

If LOCAL is empty, shell-command `find' searches beneath current directory.
Eval resulting buffer to install it, see customizable `py-extensions'. "
  (interactive)
  (let* ((local-dir (if local
                        (expand-file-name local)
                      (read-from-minibuffer "Virtualenv directory: " default-directory)))
         (path-separator (if (string-match "/" local-dir)
                             "/"
                           "\\" t))
         (shells (split-string (shell-command-to-string (concat "find " local-dir " -maxdepth 9 -type f -executable -name \"*python\""))))
         erg newshell prefix akt end orig)
    (set-buffer (get-buffer-create py-extensions))
    (erase-buffer)
    (switch-to-buffer (current-buffer))
    (dolist (elt shells)
      (setq prefix "")
      (setq curexe (substring elt (1+ (string-match "/[^/]+$" elt))))
      (setq aktpath (substring elt 0 (1+ (string-match "/[^/]+$" elt))))
      (dolist (prf (split-string aktpath (regexp-quote path-separator)))
        (unless (string= "" prf)
          (setq prefix (concat prefix (substring prf 0 1)))))
      (setq orig (point))
      (insert py-shell-template)
      (setq end (point))
      (goto-char orig)
      (when (re-search-forward "\\<NAME\\>" end t 1)
        (replace-match (concat prefix "-" (substring elt (1+ (save-match-data (string-match "/[^/]+$" elt)))))t))
      (goto-char orig)
      (while (search-forward "DOCNAME" end t 1)
        (replace-match (if (string= "ipython" curexe)
                           "IPython"
                         (capitalize curexe)) t))
      (goto-char orig)
      (when (search-forward "FULLNAME" end t 1)
        (replace-match elt t))
      (goto-char (point-max)))
    (emacs-lisp-mode)
    (if (file-readable-p (concat py-install-directory "/" py-extensions))
        (find-file (concat py-install-directory "/" py-extensions)))))

;;; Utility stuff

;; for toggling between CPython and JPython
(defvar python-which-shell nil)
(defvar python-which-args  python-python-command-args)
(defvar python-which-bufname "Python")
(make-variable-buffer-local 'python-which-shell)
(make-variable-buffer-local 'python-which-args)
(make-variable-buffer-local 'python-which-bufname)

;; Add a designator to the minor mode strings
(or (assq 'python-pdbtrack-is-tracking-p minor-mode-alist)
    (push '(python-pdbtrack-is-tracking-p python-pdbtrack-minor-mode-string)
          minor-mode-alist))

;; Bind python-file-queue before installing the kill-emacs-hook.
(defvar python-file-queue nil
  "Queue of Python temp files awaiting execution.
Currently-active file is at the head of the list.")

(defvar python-pdbtrack-is-tracking-p nil)

(defconst python-pdbtrack-stack-entry-regexp
  "^> \\(.*\\)(\\([0-9]+\\))\\([?a-zA-Z0-9_<>]+\\)()"
  "Regular expression pdbtrack uses to find a stack trace entry.")

(defconst python-pdbtrack-input-prompt "\n[(<]*[Ii]?[Pp]db[>)]+ "
  "Regular expression pdbtrack uses to recognize a pdb prompt.")

(defconst python-pdbtrack-track-range 10000
  "Max number of characters from end of buffer to search for stack entry.")

;;;; Inferior mode stuff (following cmuscheme).

(defconst python-compilation-regexp-alist
  ;; FIXME: maybe these should move to compilation-error-regexp-alist-alist.
  ;;   The first already is (for CAML), but the second isn't.  Anyhow,
  ;;   these are specific to the inferior buffer.  -- fx
  `((,(rx line-start (1+ (any " \t")) "File \""
          (group (1+ (not (any "\"<")))) ; avoid `<stdin>' &c
          "\", line " (group (1+ digit)))
     1 2)
    (,(rx " in file " (group (1+ not-newline)) " on line "
          (group (1+ digit)))
     1 2)
    ;; pdb stack trace
    (,(rx line-start "> " (group (1+ (not (any "(\"<"))))
          "(" (group (1+ digit)) ")" (1+ (not (any "("))) "()")
     1 2))
  "`compilation-error-regexp-alist' for inferior Python.")

(defvar inferior-python-mode-syntax-table
  (let ((st (make-syntax-table py-mode-syntax-table)))
    ;; Don't get confused by apostrophes in the process's output (e.g. if
    ;; you execute "help(os)").
    (modify-syntax-entry ?\' "." st)
    ;; Maybe we should do the same for double quotes?
    ;; (modify-syntax-entry ?\" "." st)
    st))

;; Autoloaded.
(declare-function compilation-shell-minor-mode "compile" (&optional arg))

(defun python--set-prompt-regexp ()
  (let ((prompt  (cdr-safe (or (assoc python-python-command
                                      python-shell-prompt-alist)
                               (assq t python-shell-prompt-alist))))
        (cprompt (cdr-safe (or (assoc python-python-command
                                      python-shell-continuation-prompt-alist)
                               (assq t python-shell-continuation-prompt-alist)))))
    (set (make-local-variable 'comint-prompt-regexp)
         (concat "\\("
                 (mapconcat 'identity
                            (delq nil (list prompt cprompt "^([Pp]db) "))
                            "\\|")
                 "\\)"))
    (set (make-local-variable 'python--prompt-regexp) prompt)))

;; Fixme: This should inherit some stuff from `python-mode', but I'm
;; not sure how much: at least some keybindings, like C-c C-f;
;; syntax?; font-locking, e.g. for triple-quoted strings?
(define-derived-mode inferior-python-mode comint-mode "Inferior Python"
  "Major mode for interacting with an inferior Python process.
A Python process can be started with \\[run-python].

Hooks `comint-mode-hook' and `inferior-python-mode-hook' are run in
that order.

You can send text to the inferior Python process from other buffers
containing Python source.
 * \\[python-switch-to-python] switches the current buffer to the Python
    process buffer.
 * \\[python-send-region] sends the current region to the Python process.
 * \\[python-send-region-and-go] switches to the Python process buffer
    after sending the text.
For running multiple processes in multiple buffers, see `run-python' and
`python-buffer'.

\\{inferior-python-mode-map}"
  :group 'python-mode
  (setq mode-line-process '(":%s"))
  (set (make-local-variable 'comint-input-filter) 'py-history-input-filter)
  (python--set-prompt-regexp)
  (set (make-local-variable 'compilation-error-regexp-alist)
       python-compilation-regexp-alist)
  (setq completion-at-point-functions nil)
  ;; (py-set-shell-complete-function)
  (set (make-local-variable 'py-local-command)
       (car (process-command (get-buffer-process (current-buffer)))))
  (unless py-complete-function
    (if (string-match "[iI][pP]ython" py-local-command)
        (progn
          (setq py-complete-function 'ipython-complete)
          (setq ipython-version (string-to-number (substring (shell-command-to-string (concat py-shell-name " -V")) 2 -1)))
          (setq ipython-completion-command-string (if (< ipython-version 11) ipython0.10-completion-command-string ipython0.11-completion-command-string)))
      ;; if `python-local-version' already contains version
      (if (string-match "[0-9]" py-local-command)
          (set (make-local-variable 'py-local-versioned-command) py-local-command)
        (set (make-local-variable 'python-version-numbers) (shell-command-to-string (concat py-local-command " -c \"from sys import version_info; print version_info[0:2]\"")))
        ;; (message "%s" python-version-numbers)
        (set (make-local-variable 'py-local-versioned-command) (concat py-local-command (replace-regexp-in-string "," "." (replace-regexp-in-string "[()\.\n ]" "" python-version-numbers)))))
      (when (and (interactive-p) py-verbose-p) (message "py-local-versioned-command %s" py-local-versioned-command))
      (cond ((string-match "[pP]ython3[^[:alpha:]]*$" py-local-versioned-command)
             (setq py-complete-function 'py-python3-shell-complete))
            (t (setq py-complete-function 'py-python2-shell-complete)))))
  (add-hook 'comint-preoutput-filter-functions #'python-preoutput-filter
            nil t)
  ;; (add-hook 'inferior-python-mode-hook 'py-shell-hook)
  (add-hook 'completion-at-point-functions
            py-complete-function nil 'local)
  (define-key inferior-python-mode-map [tab] py-complete-function)
  (define-key inferior-python-mode-map "\t" py-complete-function)
  (compilation-shell-minor-mode 1))

(defvar python-preoutput-leftover nil)
(defvar python-preoutput-skip-next-prompt nil)

;; Using this stops us getting lines in the buffer like
;; >>> ... ... >>>
;; Also look for (and delete) an `_emacs_ok' string and call
;; `python-preoutput-continuation' if we get it.

(defun py-send-region (start end)
  "Send the region to the inferior Python process."
  ;; The region is evaluated from a temporary file.  This avoids
  ;; problems with blank lines, which have different semantics
  ;; interactively and in files.  It also saves the inferior process
  ;; buffer filling up with interpreter prompts.  We need a Python
  ;; function to remove the temporary file when it has been evaluated
  ;; (though we could probably do it in Lisp with a Comint output
  ;; filter).  This function also catches exceptions and truncates
  ;; tracebacks not to mention the frame of the function itself.
  ;;
  ;; The `compilation-shell-minor-mode' parsing takes care of relating
  ;; the reference to the temporary file to the source.
  ;;
  ;; Fixme: Write a `coding' header to the temp file if the region is
  ;; non-ASCII.
  (interactive "r")
  (let* ((f (make-temp-file "py"))
         (command
          ;; IPython puts the FakeModule module into __main__ so
          ;; emacs.eexecfile becomes useless.
          (if (string-match "^ipython" py-shell-name)
              (format "execfile %S" f)
            (format "emacs.eexecfile(%S)" f)))
         (orig-start (copy-marker start)))
    (when (save-excursion
            (goto-char start)
            (/= 0 (current-indentation))) ; need dummy block
      (save-excursion
        (goto-char orig-start)
        ;; Wrong if we had indented code at buffer start.
        (set-marker orig-start (line-beginning-position 0)))
      (write-region "if True:\n" nil f nil 'nomsg))
    (write-region start end f t 'nomsg)
    (python-send-command command)
    (with-current-buffer (process-buffer (py-proc))
      ;; Tell compile.el to redirect error locations in file `f' to
      ;; positions past marker `orig-start'.  It has to be done *after*
      ;; `python-send-command''s call to `compilation-forget-errors'.
      (compilation-fake-loc orig-start f))))

(defun py-send-buffer ()
  "Send the current buffer to the inferior Python process."
  (interactive)
  (py-send-region (point-min) (point-max)))

(defun py-switch-to-python (eob-p)
  "Switch to the Python process buffer, maybe starting new process.

With prefix arg, position cursor at end of buffer."
  (interactive "P")
  (pop-to-buffer (process-buffer (py-proc)) t) ;Runs python if needed.
  (when eob-p
    (push-mark)
    (goto-char (point-max))))

(defun py-send-region-and-go (start end)
  "Send the region to the inferior Python process.

Then switch to the process buffer."
  (interactive "r")
  (py-send-region start end)
  (py-switch-to-python t))

(defvar python-prev-dir/file nil
  "Caches (directory . file) pair used in the last `py-load-file' command.
Used for determining the default in the next one.")

(defun py-load-file (file-name)
  "Load a Python file FILE-NAME into the inferior Python process.

If the file has extension `.py' import or reload it as a module.
Treating it as a module keeps the global namespace clean, provides
function location information for debugging, and supports users of
module-qualified names."
  (interactive (comint-get-source "Load Python file: " python-prev-dir/file
                                  python-source-modes
                                  t))	; because execfile needs exact name
  (comint-check-source file-name)     ; Check to see if buffer needs saving.
  (setq python-prev-dir/file (cons (file-name-directory file-name)
                                   (file-name-nondirectory file-name)))
  (with-current-buffer (process-buffer (py-proc)) ;Runs python if needed.
    ;; Fixme: I'm not convinced by this logic from python-mode.el.
    (python-send-command
     (if (string-match "\\.py\\'" file-name)
         (let ((module (file-name-sans-extension
                        (file-name-nondirectory file-name))))
           (format "emacs.eimport(%S,%S)"
                   module (file-name-directory file-name)))
       (format "execfile(%S)" file-name)))
    (message "%s loaded" file-name)))

(defun py-set-proc ()
  "Set the default value of `python-buffer' to correspond to this buffer.

If the current buffer has a local value of `python-buffer', set the
default (global) value to that.  The associated Python process is
the one that gets input from \\[py-send-region] et al when used
in a buffer that doesn't have a local value of `python-buffer'."
  (interactive)
  (if (local-variable-p 'python-buffer)
      (setq-default python-buffer python-buffer)
    (error "No local value of `python-buffer'")))

;;; Python-el completion and help

(defvar view-return-to-alist)
(defvar python-imports)			; forward declaration


;; Called from `python-mode', this causes a recursive call of the
;; mode.  See logic there to break out of the recursion.

;; pdb tracking is alert once this file is loaded, but takes no action if
;; `python-pdbtrack-do-tracking-p' is nil.
(add-hook 'comint-output-filter-functions 'python-pdbtrack-track-stack-file)



(defun python-comint-output-filter-function (string)
  "Watch output for Python prompt and exec next file waiting in queue.
This function is appropriate for `comint-output-filter-functions'."
  ;; TBD: this should probably use split-string
  (when (and (string-match python--prompt-regexp string)
             python-file-queue)
    (condition-case nil
        (delete-file (car python-file-queue))
      (error nil))
    (setq python-file-queue (cdr python-file-queue))
    (if python-file-queue
        (let ((pyproc (get-buffer-process (current-buffer))))
          (python-execute-file pyproc (car python-file-queue))))))

(defun python-pdbtrack-overlay-arrow (activation)
  "Activate or deactivate arrow at beginning-of-line in current buffer."
  (if activation
      (progn
        (setq overlay-arrow-position (make-marker)
              overlay-arrow-string "=>"
              python-pdbtrack-is-tracking-p t)
        (set-marker overlay-arrow-position
                    (save-excursion (beginning-of-line) (point))
                    (current-buffer)))
    (setq overlay-arrow-position nil
          python-pdbtrack-is-tracking-p nil)))

(defun python-pdbtrack-track-stack-file (text)
  "Show the file indicated by the pdb stack entry line, in a separate window.

Activity is disabled if the buffer-local variable
`python-pdbtrack-do-tracking-p' is nil.

We depend on the pdb input prompt being a match for
`python-pdbtrack-input-prompt'.

If the traceback target file path is invalid, we look for the
most recently visited python-mode buffer which either has the
name of the current function or class, or which defines the
function or class.  This is to provide for scripts not in the
local filesytem (e.g., Zope's 'Script \(Python)', but it's not
Zope specific).  If you put a copy of the script in a buffer
named for the script and activate python-mode, then pdbtrack will
find it."
  ;; Instead of trying to piece things together from partial text
  ;; (which can be almost useless depending on Emacs version), we
  ;; monitor to the point where we have the next pdb prompt, and then
  ;; check all text from comint-last-input-end to process-mark.
  ;;
  ;; Also, we're very conservative about clearing the overlay arrow,
  ;; to minimize residue.  This means, for instance, that executing
  ;; other pdb commands wipe out the highlight.  You can always do a
  ;; 'where' (aka 'w') PDB command to reveal the overlay arrow.

  (let* ((origbuf (current-buffer))
         (currproc (get-buffer-process origbuf)))

    (if (not (and currproc python-pdbtrack-do-tracking-p))
        (python-pdbtrack-overlay-arrow nil)

      (let* ((procmark (process-mark currproc))
             (block (buffer-substring (max comint-last-input-end
                                           (- procmark
                                              python-pdbtrack-track-range))
                                      procmark))
             target target_fname target_lineno target_buffer)

        (if (not (string-match (concat python-pdbtrack-input-prompt "$") block))
            (python-pdbtrack-overlay-arrow nil)

          (setq target (python-pdbtrack-get-source-buffer block))

          (if (stringp target)
              (progn
                (python-pdbtrack-overlay-arrow nil)
                (message "pdbtrack: %s" target))

            (setq target_lineno (car target)
                  target_buffer (cadr target)
                  target_fname (buffer-file-name target_buffer))
            (switch-to-buffer-other-window target_buffer)
            (goto-char (point-min))
            (forward-line (1- target_lineno))
            (message "pdbtrack: line %s, file %s" target_lineno target_fname)
            (python-pdbtrack-overlay-arrow t)
            (pop-to-buffer origbuf t)
            ;; in large shell buffers, above stuff may cause point to lag output
            (goto-char procmark)))))))

(defun python-pdbtrack-get-source-buffer (block)
  "Return line number and buffer of code indicated by block's traceback text.

We look first to visit the file indicated in the trace.

Failing that, we look for the most recently visited python-mode buffer
with the same name or having the named function.

If we're unable find the source code we return a string describing the
problem."

  (if (not (string-match python-pdbtrack-stack-entry-regexp block))

      "Traceback cue not found"

    (let* ((filename (match-string 1 block))
           (lineno (string-to-number (match-string 2 block)))
           (funcname (match-string 3 block))
           funcbuffer)

      (cond ((file-exists-p filename)
             (list lineno (find-file-noselect filename)))

            ((setq funcbuffer (python-pdbtrack-grub-for-buffer funcname lineno))
             (if (string-match "/Script (Python)$" filename)
                 ;; Add in number of lines for leading '##' comments:
                 (setq lineno
                       (+ lineno
                          (with-current-buffer funcbuffer
                            (if (equal (point-min)(point-max))
                                0
                              (count-lines
                               (point-min)
                               (max (point-min)
                                    (string-match "^\\([^#]\\|#[^#]\\|#$\\)"
                                                  (buffer-substring
                                                   (point-min) (point-max))))))))))
             (list lineno funcbuffer))

            ((= (elt filename 0) ?\<)
             (format "(Non-file source: '%s')" filename))

            (t (format "Not found: %s(), %s" funcname filename))))))

(defun python-pdbtrack-grub-for-buffer (funcname lineno)
  "Find recent python-mode buffer named, or having function named funcname."
  (let ((buffers (buffer-list))
        buf
        got)
    (while (and buffers (not got))
      (setq buf (car buffers)
            buffers (cdr buffers))
      (if (and (with-current-buffer buf
                 (string= major-mode "python-mode"))
               (or (string-match funcname (buffer-name buf))
                   (string-match (concat "^\\s-*\\(def\\|class\\)\\s-+"
                                         funcname "\\s-*(")
                                 (with-current-buffer buf
                                   (buffer-substring (point-min)
                                                     (point-max))))))
          (setq got buf)))
    got))

;; Python subprocess utilities and filters
(defun python-execute-file (proc filename)
  "Send to Python interpreter process PROC \"execfile('FILENAME')\".
Make that process's buffer visible and force display.  Also make
comint believe the user typed this string so that
`kill-output-from-shell' does The Right Thing."
  (let ((curbuf (current-buffer))
        (procbuf (process-buffer proc))
                                        ;	(comint-scroll-to-bottom-on-output t)
        (msg (format "## working on region in file %s...\n" filename))
        ;; add some comment, so that we can filter it out of history
        (cmd (format "execfile(r'%s') # PYTHON-MODE\n" filename)))
    (unwind-protect
        (with-current-buffer procbuf
          (goto-char (point-max))
          (move-marker (process-mark proc) (point))
          (funcall (process-filter proc) proc msg))
      (set-buffer curbuf))
    (process-send-string proc cmd)))

;; from pycomplete.el
(defun py-find-global-imports ()
  (save-excursion
    (let (first-class-or-def imports)
      (goto-char (point-min))
      (setq first-class-or-def
            (re-search-forward "^ *\\(def\\|class\\) " nil t))
      (goto-char (point-min))
      (while (re-search-forward
              "^\\(import \\|from \\([A-Za-z_][A-Za-z_0-9]*\\) import \\).*"
              nil t)
        (setq imports (append imports
                              (list (buffer-substring
                                     (match-beginning 0)
                                     (match-end 0))))))
      imports)))

;;; Code Completion.

;; http://lists.gnu.org/archive/html/bug-gnu-emacs/2008-01/msg00076.html
(defalias
  'py-shell-redirect-send-command-to-process
  'comint-redirect-send-command-to-process)
(defalias
  'py-shell-dynamic-simple-complete
  'comint-dynamic-simple-complete)

(defvar python-imports "None"
  "String of top-level import statements updated by `py-find-imports'.")
(make-variable-buffer-local 'python-imports)

;;; Python Shell Complete
;; Author: Lukasz Pankowski

(defvar py-shell-input-lines nil
  "Collect input lines send interactively to the Python process in
order to allow injecting completion command between keyboard interrupt
and resending the lines later. The lines are stored in reverse order")

(defun py-shell-simple-send (proc string)
  (setq py-shell-input-lines (cons string py-shell-input-lines))
  (comint-simple-send proc string))

(defun py-shell-execute-string-now (string &optional shell)
  "Send to Python interpreter process PROC \"exec STRING in {}\".
and return collected output"
  (let* ((proc (cond (shell
                      (or (get-process shell)
                          (prog1
                              (get-buffer-process (py-shell nil nil shell))
                            (sit-for 0.1))))
                     (t (or (get-buffer-process (current-buffer))
                            (get-buffer-process (py-shell))))))
         (cmd (format "exec '''%s''' in {}"
                      (mapconcat 'identity (split-string string "\n") "\\n")))
         (procbuf (process-buffer proc))
         (outbuf (get-buffer-create " *pyshellcomplete-output*"))
         (lines (reverse py-shell-input-lines)))
    (if (and proc (not py-file-queue))
        (unwind-protect
            (condition-case nil
                (progn
                  (if lines
                      (with-current-buffer procbuf
                        (comint-redirect-send-command-to-process
                         "\C-c" outbuf proc nil t)
                        ;; wait for output
                        (while (not comint-redirect-completed)
                          (accept-process-output proc 1))))
                  (with-current-buffer outbuf
                    (delete-region (point-min) (point-max)))
                  (with-current-buffer procbuf
                    (comint-redirect-send-command-to-process
                     cmd outbuf proc nil t)
                    (while (not comint-redirect-completed) ; wait for output
                      (accept-process-output proc 1)))
                  (with-current-buffer outbuf
                    (buffer-substring (point-min) (point-max))))
              (quit (with-current-buffer procbuf
                      (interrupt-process proc comint-ptyp)
                      (while (not comint-redirect-completed) ; wait for output
                        (accept-process-output proc 1)))
                    (signal 'quit nil)))
          (if (with-current-buffer procbuf comint-redirect-completed)
              (while lines
                (with-current-buffer procbuf
                  (comint-redirect-send-command-to-process
                   (car lines) outbuf proc nil t))
                (accept-process-output proc 1)
                (setq lines (cdr lines))))))))

(defun py-dot-word-before-point ()
  (buffer-substring
   (save-excursion (skip-chars-backward "a-zA-Z0-9_.") (point))
   (point)))

(defun py-completion-at-point ()
  "An alternative completion, similar the way python.el does it. "
  (interactive "*")
  (let* ((start (when (skip-chars-backward "[[:alnum:]_]")(point)))
         (end (progn (skip-chars-forward "[[:alnum:]_]")(point)))
         (completion (when start
                       (py-symbol-completions (buffer-substring-no-properties start end)))))
    (if completion
        (progn
          (delete-region start end)
          (insert (car completion)))
      (tab-to-tab-stop))))

;; started from python.el's python-completion-at-point
(defun py-script-complete ()
  (interactive "*")
  (let ((end (point))
	(start (save-excursion
		 (and (re-search-backward
		       (rx (or buffer-start (regexp "[^[:alnum:]._]"))
			   (group (1+ (regexp "[[:alnum:]._]"))) point)
		       nil t)
		      (match-beginning 1)))))
    (when start
      (list start end
            (completion-table-dynamic 'py-symbol-completions)))))

(defun py-symbol-completions (symbol)
  "Return a list of completions of the string SYMBOL from Python process.
The list is sorted.
Uses `python-imports' to load modules against which to complete."
  (when (stringp symbol)
    (let ((completions
	   (condition-case ()
	       (car (read-from-string
		     (python-send-receive
		      (format "emacs.complete(%S,%s)"
			      (substring-no-properties symbol)
			      python-imports))))
	     (error nil))))
      (sort
       ;; We can get duplicates from the above -- don't know why.
       (delete-dups completions)
       #'string<))))

(defun py-python-script-complete (&optional shell)
  "Complete word before point, if any. Otherwise insert TAB. "
  (interactive)
  (let* (py-split-windows-on-execute-p
         py-switch-buffers-on-execute-p
         (shell (or shell py-local-versioned-command))
         (orig (point))
         (beg (save-excursion (skip-chars-backward "a-zA-Z0-9_.") (point)))
         (end (point))
         (word (buffer-substring-no-properties beg end))
         (imports (py-find-imports)))
    (cond ((string= word "")
           (message "%s" "Nothing to complete. ")
           (tab-to-tab-stop))
          (t (or (setq proc (get-buffer-process shell))
                 (setq proc (get-buffer-process (py-shell nil nil shell))))
             (if (processp proc)
                 (progn
                   ;; when completing instances, make them known
                   (when (string-match "^\\(^[a-zA-Z0-9_]+\\)\\.\\([a-zA-Z0-9_]+\\)$" word)
                     ;; (message "%s" (match-string 1 word))
                     (save-excursion
                       (goto-char (point-min))
                       (when (re-search-forward (concat "^[ \t]*" (match-string-no-properties 1 word) "[ \t]*=[ \t]*[^ \n\r\f\t]+") nil t 1))
                       (if imports
                           (setq imports (concat imports (match-string-no-properties 0) ";"))
                         (setq imports (match-string-no-properties 0)))))
                   (unless (python-shell-completion--do-completion-at-point proc imports word)
                     (call-interactively 'dabbrev-expand))
                   nil)
               (error "No completion process at proc"))))))

(defun py-python2-shell-complete (&optional shell)
  (interactive)
  (let* (py-split-windows-on-execute-p
         py-switch-buffers-on-execute-p
         (shell (or shell py-local-versioned-command))
         (orig (point))
         (beg (save-excursion (skip-chars-backward "a-zA-Z0-9_.") (point)))
         (end (point))
         (word (buffer-substring-no-properties beg end)))
    (cond ((string= word "")
           (message "%s" "Nothing to complete. ")
           (tab-to-tab-stop))
          (t (or (setq proc (get-buffer-process shell))
                 (setq proc (get-buffer-process (py-shell nil nil shell))))
             (message "%s" (processp proc))
             (python-shell-completion--do-completion-at-point proc)(buffer-substring-no-properties beg end) word))))

(defun py-python3-shell-complete (&optional shell)
  "Complete word before point, if any. Otherwise insert TAB. "
  (interactive)
  (let* ((shell (or shell py-local-versioned-command))
         (orig (point))
         (beg (save-excursion (skip-chars-backward "a-zA-Z0-9_.") (point)))
         (end (point))
         (word (buffer-substring-no-properties beg end)))
    (cond ((string= word "")
           (message "%s" "Nothing to complete. ")
           (tab-to-tab-stop))
          (t
           (python-shell-completion--do-completion-at-point (get-buffer-process (current-buffer)) (buffer-substring-no-properties beg end) word)))))

(defun py-shell-complete (&optional shell)
  "Complete word before point, if any. Otherwise insert TAB. "
  (interactive)
  (let ((shell (or shell
                   (ignore-errors (process-name (get-buffer-process (current-buffer)))))))
    (if (or (eq major-mode 'comint-mode)(eq major-mode 'inferior-python-mode))
        ;;  complete in shell
        (if (string-match "[iI][pP]ython" shell)
            (ipython-complete)
          (let* ((orig (point))
                 (beg (save-excursion (skip-chars-backward "a-zA-Z0-9_.") (point)))
                 (end (point))
                 (word (buffer-substring-no-properties beg end)))
            (cond ((string= word "")
                   (message "%s" "Nothing to complete. ")
                   (tab-to-tab-stop))
                  ((string-match "[pP]ython3[^[:alpha:]]*$" shell)
                   (python-shell-completion--do-completion-at-point (get-buffer-process (current-buffer))(buffer-substring-no-properties beg end) word))
                  (t (py-shell-complete-intern word beg end shell)))))
      ;; complete in script buffer
      (let* (py-split-windows-on-execute-p
             py-switch-buffers-on-execute-p
             (shell (or shell (py-choose-shell)))
             (proc (or (comint-check-proc (py-shell nil nil shell 'noswitch nil))
                       (py-shell nil nil shell 'noswitch nil)))
             (beg (save-excursion (skip-chars-backward "a-zA-Z0-9_.") (point)))
             (end (point))
             (word (buffer-substring-no-properties beg end)))
        (cond ((string= word "")
               (message "%s" "Nothing to complete. "))
              ((string-match "[iI][pP]ython" shell)
               (ipython-complete))
              ((string-match "[pP]ython3[^[:alpha:]]*$" shell)
               (python-shell-completion--do-completion-at-point proc (buffer-substring-no-properties beg end) word))
              (t (py-shell-complete-intern word beg end shell)))))))

(defun py-shell-complete-intern (word &optional beg end shell)
  (let (result)
    (setq result (py-shell-execute-string-now (format "
def print_completions(namespace, text, prefix=''):
   for name in namespace:
       if name.startswith(text):
           print(prefix + name)

def complete(text):
    import __builtin__
    import __main__
    if '.' in text:
        terms = text.split('.')
        try:
            if hasattr(__main__, terms[0]):
                obj = getattr(__main__, terms[0])
            else:
                obj = getattr(__builtin__, terms[0])
            for term in terms[1:-1]:
                obj = getattr(obj, term)
            print_completions(dir(obj), terms[-1], text[:text.rfind('.') + 1])
        except AttributeError:
            pass
    else:
        import keyword
        print_completions(keyword.kwlist, text)
        print_completions(dir(__builtin__), text)
        print_completions(dir(__main__), text)
complete('%s')" word) shell))
    (if (eq result nil)
        (message "Can't complete")
      (let ((comint-completion-addsuffix nil)
            (completions
             (sort
              (delete-dups (if (split-string "\n" "\n")
                               (split-string result "\n" t) ; XEmacs
                             (split-string result "\n")))
              #'string<)))
        (delete-region beg end)
        (insert (car completions)))
      ;; list-typ return required by `completion-at-point'
      (list beg end))))

;;; IPython Shell Complete

;; see also
;; http://lists.gnu.org/archive/html/bug-gnu-emacs/2008-01/msg00076.html

(defvar ipython-completion-command-string nil
  "Either ipython0.10-completion-command-string or ipython0.11-completion-command-string.

ipython0.11-completion-command-string also covers version 0.12")
;; (make-variable-buffer-local 'ipython-completion-command-string)

(defvar ipython0.10-completion-command-string
  "print(';'.join(__IP.Completer.all_completions('%s'))) #PYTHON-MODE SILENT\n"
  "The string send to ipython to query for all possible completions")

;; (setq ipython0.10-completion-command-string "print(';'.join(__IP.Completer.all_completions('%s'))) #PYTHON-MODE SILENT\n")

(defvar ipython0.11-completion-command-string
  "print(';'.join(get_ipython().Completer.all_completions('%s'))) #PYTHON-MODE SILENT\n"
  "The string send to ipython to query for all possible completions")

(defun ipython-complete (&optional done completion-command-string)
  "Complete the python symbol before point.

If no completion available, insert a TAB.
Returns the completed symbol, a string, if successful, nil otherwise.

Bug: if no IPython-shell is running, fails first time due to header returned, which messes up the result. Please repeat once then. "
  (interactive "*")
  (let* (py-split-windows-on-execute-p
         py-switch-buffers-on-execute-p
         (beg (progn (save-excursion (skip-chars-backward "a-z0-9A-Z_." (point-at-bol))
                                     (point))))
         (end (point))
         (pattern (buffer-substring-no-properties beg end))
         (sep ";")
         (pyshellname (py-choose-shell))
         (processlist (process-list))
         done
         (process
          (if ipython-complete-use-separate-shell-p
              (unless (comint-check-proc (process-name (get-buffer-process (get-buffer-create "*IPython-Complete*"))))
                (get-buffer-process (py-shell nil nil pyshellname 'noswitch nil "*IPython-Complete*")))
            (progn
              (while (and processlist (not done))
                (when (and
                       (string= pyshellname (process-name (car processlist)))
                       (processp (car processlist))
                       (setq done (car processlist))))
                (setq processlist (cdr processlist)))
              done)))
         (python-process (or process
                             (setq python-process (get-buffer-process (py-shell nil nil (if (string-match "[iI][pP]ython[^[:alpha:]]*$"  pyshellname) pyshellname "ipython") 'noswitch nil)))))
         (comint-output-filter-functions
          (delq 'py-comint-output-filter-function comint-output-filter-functions))
         (comint-output-filter-functions
          (append comint-output-filter-functions
                  '(ansi-color-filter-apply
                    (lambda (string)
                      (setq ugly-return (concat ugly-return string))
                      (delete-region comint-last-output-start
                                     (process-mark (get-buffer-process (current-buffer))))))))

         (ccs (or completion-command-string (py-set-ipython-completion-command-string
                                             (process-name python-process))))
         completion completions completion-table ugly-return)
    (if (string= pattern "")
        (tab-to-tab-stop)
      (process-send-string python-process (format ccs pattern))
      (accept-process-output python-process 5)
      (setq completions
            (split-string (substring ugly-return 0 (position ?\n ugly-return)) sep))
      (setq completion-table (loop for str in completions
                                   collect (list str nil)))
      (setq completion (try-completion pattern completion-table))
      (cond ((eq completion t)
             (tab-to-tab-stop))
            ((null completion)
             ;; if an (I)Python shell didn't run
             ;; before, first completion are not delivered
             ;; (if done (ipython-complete done)
             (message "Can't find completion for \"%s\"" pattern)
             (ding))
            ((not (string= pattern completion))
             (delete-region beg end)
             (insert completion))
            (t
             (message "Making completion list...")
             (with-output-to-temp-buffer "*Python Completions*"
               (display-completion-list (all-completions pattern completion-table)))
             (message "Making completion list...%s" "done"))))
    ;; minibuffer.el requires that
    (list beg end)))

(defun ipython-complete-py-shell-name (&optional done)
  "Complete the python symbol before point.

If no completion available, insert a TAB.
Returns the completed symbol, a string, if successful, nil otherwise.

Bug: if no IPython-shell is running, fails first time due to header returned, which messes up the result. Please repeat once then. "
  (interactive "*")
  (let* (py-split-windows-on-execute-p
         py-switch-buffers-on-execute-p
         (beg (progn (save-excursion (skip-chars-backward "a-z0-9A-Z_." (point-at-bol))
                                     (point))))
         (end (point))
         (pattern (buffer-substring-no-properties beg end))
         (sep ";")
         (py-process (or (get-buffer-process (current-buffer))
                         (get-buffer-process (py-shell))
                         (get-buffer-process (py-shell nil nil "ipython" 'noswitch nil))))

         (comint-output-filter-functions
          (delq 'py-comint-output-filter-function comint-output-filter-functions))
         (comint-output-filter-functions
          (append comint-output-filter-functions
                  '(ansi-color-filter-apply
                    (lambda (string)
                      (setq ugly-return (concat ugly-return string))
                      (delete-region comint-last-output-start
                                     (process-mark (get-buffer-process (current-buffer))))))))
         completion completions completion-table ugly-return)
    (if (string= pattern "")
        (tab-to-tab-stop)
      (process-send-string py-process
                           (format (py-set-ipython-completion-command-string (downcase (process-name py-process))) pattern))
      (accept-process-output py-process)
      (setq completions
            (split-string (substring ugly-return 0 (position ?\n ugly-return)) sep))
      (setq completion-table (loop for str in completions
                                   collect (list str nil)))
      (setq completion (try-completion pattern completion-table))
      (cond ((eq completion t))
            ((null completion)
             ;; if an (I)Python shell didn't run
             ;; before, first completion are not delivered
             ;; (if done (ipython-complete done)
             (message "Can't find completion for \"%s\"" pattern)
             (ding))
            ((not (string= pattern completion))
             (delete-region beg end)
             (insert completion))
            (t
             (message "Making completion list...")
             (with-output-to-temp-buffer "*Python Completions*"
               (display-completion-list (all-completions pattern completion-table)))
             (message "Making completion list...%s" "done"))))
    completion))

;;; pep8
(defun py-pep8-run (command)
  "*Run pep8, check formatting (default on the file currently visited).
"
  (interactive
   (let ((default
           (if (buffer-file-name)
               (format "%s %s %s" py-pep8-command
                       (mapconcat 'identity py-pep8-command-args " ")
                       (buffer-file-name))
             (format "%s %s" py-pep8-command
                     (mapconcat 'identity py-pep8-command-args " "))))
         (last (when py-pep8-history
                 (let* ((lastcmd (car py-pep8-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (buffer-file-name) cmd))))
                   (mapconcat 'identity newcmd " ")))))

     (list
      (if (fboundp 'read-shell-command)
          (read-shell-command "Run pep8 like this: "
                              (if last
                                  last
                                default)
                              'py-pep8-history)
        (read-string "Run pep8 like this: "
                     (if last
                         last
                       default)
                     'py-pep8-history)))))
  (save-some-buffers (not py-ask-about-save) nil)
  (if (fboundp 'compilation-start)
      ;; Emacs.
      (compilation-start command)
    ;; XEmacs.
    (when (featurep 'xemacs)
      (compile-internal command "No more errors"))))

(defun py-pep8-help ()
  "Display pep8 command line help messages. "
  (interactive)
  (set-buffer (get-buffer-create "*pep8-Help*"))
  (erase-buffer)
  (shell-command "pep8 --help" "*pep8-Help*"))

;;; Pylint
(defalias 'pylint 'py-pylint-run)
(defun py-pylint-run (command)
  "*Run pylint (default on the file currently visited).

For help see M-x pylint-help resp. M-x pylint-long-help.
Home-page: http://www.logilab.org/project/pylint "
  (interactive
   (let ((default
           (if (buffer-file-name)
               (format "%s %s %s" py-pylint-command
                       (mapconcat 'identity py-pylint-command-args " ")
                       (buffer-file-name))
             (format "%s %s" py-pylint-command
                     (mapconcat 'identity py-pylint-command-args " "))))
         (last (when py-pylint-history
                 (let* ((lastcmd (car py-pylint-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (buffer-file-name) cmd))))
                   (mapconcat 'identity newcmd " ")))))

     (list
      (if (fboundp 'read-shell-command)
          (read-shell-command "Run pylint like this: "
                              (if last
                                  last
                                default)
                              'py-pylint-history)
        (read-string "Run pylint like this: "
                     (if last
                         last
                       default)
                     'py-pylint-history)))))
  (save-some-buffers (not py-ask-about-save) nil)
  (if (fboundp 'compilation-start)
      ;; Emacs.
      (compilation-start command)
    ;; XEmacs.
    (when (featurep 'xemacs)
      (compile-internal command "No more errors"))))

(defalias 'pylint-help 'py-pylint-help)
(defun py-pylint-help ()
  "Display Pylint command line help messages.

Let's have this until more Emacs-like help is prepared "
  (interactive)
  (set-buffer (get-buffer-create "*Pylint-Help*"))
  (erase-buffer)
  (shell-command "pylint --long-help" "*Pylint-Help*"))

(defalias 'pylint-doku 'py-pylint-doku)
(defun py-pylint-doku ()
  "Display Pylint Documentation.

Calls `pylint --full-documentation'"
  (interactive)
  (set-buffer (get-buffer-create "*Pylint-Documentation*"))
  (erase-buffer)
  (shell-command "pylint --full-documentation" "*Pylint-Documentation*"))

;;; Pyflakes
(defalias 'pyflakes 'py-pyflakes-run)
(defun py-pyflakes-run (command)
  "*Run pyflakes (default on the file currently visited).

For help see M-x pyflakes-help resp. M-x pyflakes-long-help.
Home-page: http://www.logilab.org/project/pyflakes "
  (interactive
   (let ((default
           (if (buffer-file-name)
               (format "%s %s %s" py-pyflakes-command
                       (mapconcat 'identity py-pyflakes-command-args " ")
                       (buffer-file-name))
             (format "%s %s" py-pyflakes-command
                     (mapconcat 'identity py-pyflakes-command-args " "))))
         (last (when py-pyflakes-history
                 (let* ((lastcmd (car py-pyflakes-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (buffer-file-name) cmd))))
                   (mapconcat 'identity newcmd " ")))))

     (list
      (if (fboundp 'read-shell-command)
          (read-shell-command "Run pyflakes like this: "
                              (if last
                                  last
                                default)
                              'py-pyflakes-history)
        (read-string "Run pyflakes like this: "
                     (if last
                         last
                       default)
                     'py-pyflakes-history)))))
  (save-some-buffers (not py-ask-about-save) nil)
  (if (fboundp 'compilation-start)
      ;; Emacs.
      (compilation-start command)
    ;; XEmacs.
    (when (featurep 'xemacs)
      (compile-internal command "No more errors"))))

(defalias 'pyflakes-help 'py-pyflakes-help)
(defun py-pyflakes-help ()
  "Display Pyflakes command line help messages.

Let's have this until more Emacs-like help is prepared "
  (interactive)
  ;; (set-buffer (get-buffer-create "*Pyflakes-Help*"))
  ;; (erase-buffer)
  (with-help-window "*Pyflakes-Help*"
    (with-current-buffer standard-output
      (insert "       pyflakes [file-or-directory ...]

       Pyflakes is a simple program which checks Python
       source files for errors. It is similar to
       PyChecker in scope, but differs in that it does
       not execute the modules to check them. This is
       both safer and faster, although it does not
       perform as many checks. Unlike PyLint, Pyflakes
       checks only for logical errors in programs; it
       does not perform any checks on style.

       All commandline arguments are checked, which
       have to be either regular files or directories.
       If a directory is given, every .py file within
       will be checked.

       When no commandline arguments are given, data
       will be read from standard input.

       The exit status is 0 when no warnings or errors
       are found. When errors are found the exit status
       is 2. When warnings (but no errors) are found
       the exit status is 1.

Extracted from http://manpages.ubuntu.com/manpages/natty/man1/pyflakes.1.html
"))))

;;; Pyflakes-pep8
(defalias 'pyflakespep8 'py-pyflakespep8-run)
(defun py-pyflakespep8-run (command)
  "*Run pyflakespep8, check formatting (default on the file currently visited).
"
  (interactive
   (let ((default
           (if (buffer-file-name)
               (format "%s %s %s" py-pyflakespep8-command
                       (mapconcat 'identity py-pyflakespep8-command-args " ")
                       (buffer-file-name))
             (format "%s %s" py-pyflakespep8-command
                     (mapconcat 'identity py-pyflakespep8-command-args " "))))
         (last (when py-pyflakespep8-history
                 (let* ((lastcmd (car py-pyflakespep8-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (buffer-file-name) cmd))))
                   (mapconcat 'identity newcmd " ")))))

     (list
      (if (fboundp 'read-shell-command)
          (read-shell-command "Run pyflakespep8 like this: "
                              (if last
                                  last
                                default)
                              'py-pyflakespep8-history)
        (read-string "Run pyflakespep8 like this: "
                     (if last
                         last
                       default)
                     'py-pyflakespep8-history)))))
  (save-some-buffers (not py-ask-about-save) nil)
  (if (fboundp 'compilation-start)
      ;; Emacs.
      (compilation-start command)
    ;; XEmacs.
    (when (featurep 'xemacs)
      (compile-internal command "No more errors"))))

(defun py-pyflakespep8-help ()
  "Display pyflakespep8 command line help messages. "
  (interactive)
  (set-buffer (get-buffer-create "*pyflakespep8-Help*"))
  (erase-buffer)
  (shell-command "pyflakespep8 --help" "*pyflakespep8-Help*"))

;;; Pychecker
(defun py-pychecker-run (command)
  "*Run pychecker (default on the file currently visited)."
  (interactive
   (let ((default
           (if (buffer-file-name)
               (format "%s %s %s" py-pychecker-command
                       (mapconcat 'identity py-pychecker-command-args " ")
                       (buffer-file-name))
             (format "%s %s" py-pychecker-command
                     (mapconcat 'identity py-pychecker-command-args " "))))
         (last (when py-pychecker-history
                 (let* ((lastcmd (car py-pychecker-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (buffer-file-name) cmd))))
                   (mapconcat 'identity newcmd " ")))))

     (list
      (if (fboundp 'read-shell-command)
          (read-shell-command "Run pychecker like this: "
                              (if last
                                  last
                                default)
                              'py-pychecker-history)
        (read-string "Run pychecker like this: "
                     (if last
                         last
                       default)
                     'py-pychecker-history)))))
  (save-some-buffers (not py-ask-about-save) nil)
  (if (fboundp 'compilation-start)
      ;; Emacs.
      (compilation-start command)
    ;; XEmacs.
    (when (featurep 'xemacs)
      (compile-internal command "No more errors"))))

;;; python-mode skeletons
;; Derived from python.el, where it's instrumented as abbrev
;; Original code authored by Dave Love AFAIK

(define-skeleton py-else
  "Auxiliary skeleton."
  nil
  (unless (eq ?y (read-char "Add `else' clause? (y for yes or RET for no) "))
    (signal 'quit t))
  < "else:" \n)

(define-skeleton py-if
  "If condition "
  "if " "if " str ":" \n
  _ \n
  ("other condition, %s: "
   < "elif " str ":" \n
   > _ \n nil)
  '(py-else) | ^)

(define-skeleton py-else
  "Auxiliary skeleton."
  nil
  (unless (eq ?y (read-char "Add `else' clause? (y for yes or RET for no) "))
    (signal 'quit t))
  "else:" \n
  > _ \n)

(define-skeleton py-while
  "Condition: "
  "while " "while " str ":" \n
  > -1 _ \n
  '(py-else) | ^)

(define-skeleton py-for
  "Target, %s: "
  "for " "for " str " in " (skeleton-read "Expression, %s: ") ":" \n
  > -1 _ \n
  '(py-else) | ^)

(define-skeleton py-try/except
  "Py-try/except skeleton "
  "try:" "try:" \n
  > -1 _ \n
  ("Exception, %s: "
   < "except " str '(python-target) ":" \n
   > _ \n nil)
  < "except:" \n
  > _ \n
  '(py-else) | ^)

(define-skeleton py-target
  "Auxiliary skeleton."
  "Target, %s: " ", " str | -2)

(define-skeleton py-try/finally
  "Py-try/finally skeleton "
  "try:" \n
  > -1 _ \n
  < "finally:" \n
  > _ \n)

(define-skeleton py-def
  "Name: "
  "def " str " (" ("Parameter, %s: " (unless (equal ?\( (char-before)) ", ")
                   str) "):" \n
                   "\"\"\"" - "\"\"\"" \n     ; Fixme:  extra space inserted -- why?).
                   > _ \n)

(define-skeleton py-class
  "Name: "
  "class " str " (" ("Inheritance, %s: "
                     (unless (equal ?\( (char-before)) ", ")
                     str)
  & ")" | -2				; close list or remove opening
  ":" \n
  "\"\"\"" - "\"\"\"" \n
  > _ \n)

;;; Virtualenv --- Switching virtual python enviroments seamlessly
;; Thanks Gabriele Lanaro and all working on that
;; Url: http://github.com/gabrielelanaro/emacs-starter-kit
;; The installation is fairly easy, you have the load option, put this
;; in your .emacs:

;; (load-file "/path/to/virtualenv.el")
;;
;; Otherwise you can do it with the load path:

;; (add-to-list 'load-path "Path/to/virtualenv.el/containing/directory/"
;; (require 'virtualenv)

;; The usage is very intuitive, to activate a virtualenv use

;; M-x virtualenv-activate

;; It will prompt you for the virtual environment path.
;; If you want to deactivate a virtual environment, use:

;; M-x virtualenv-deactivate

(defvar virtualenv-workon-home nil)

(if (getenv "WORKON_HOME")
    (setq virtualenv-workon-home (getenv "WORKON_HOME"))
  (setq virtualenv-workon-home "~/.virtualenvs"))

(defvar virtualenv-name nil)
(setq virtualenv-name nil)

;;TODO: Move to a generic UTILITY or TOOL package
(defun virtualenv-filter (predicate sequence)
  "Apply to each element of SEQUENCE the PREDICATE, if FUNCTION
  returns non-nil append the element to the return value of
  virtualenv-filter: a list"
  (let ((retlist '()))
    (dolist (element sequence)
      (when (funcall predicate element)
        (push element retlist)))
    (nreverse retlist)))

(defun virtualenv-append-path (dir var)
  "Append DIR to a path-like varibale VAR, for example:
 (virtualenv-append-path /usr/bin:/bin /home/test/bin) -> /home/test/bin:/usr/bin:/bin"
  (concat (expand-file-name dir)
          path-separator
          var))

(defun virtualenv-add-to-path (dir)
  "Add the specified path element to the Emacs PATH"
  (setenv "PATH"
          (virtualenv-append-path dir
                                  (getenv "PATH"))))

(defun virtualenv-current ()
  "barfs the current activated virtualenv"
  (interactive)
  (message virtualenv-name))

(defun virtualenv-activate (dir)
  "Activate the virtualenv located in DIR"
  (interactive "DVirtualenv Directory: ")

  ;; Eventually deactivate previous virtualenv
  (when virtualenv-name
    (virtualenv-deactivate))

  ;; Storing old variables
  (setq virtualenv-old-path (getenv "PATH"))
  (setq virtualenv-old-exec-path exec-path)

  (setenv "VIRTUAL_ENV" dir)
  (virtualenv-add-to-path (concat dir "bin"))
  (add-to-list 'exec-path (concat dir "bin"))

  (setq virtualenv-name dir)

  (message (concat "Virtualenv '" virtualenv-name "' activated.")))

(defun virtualenv-deactivate ()
  "Deactivate the current virtual enviroment"
  (interactive)

  ;; Restoring old variables
  (setenv "PATH" virtualenv-old-path)
  (setq exec-path virtualenv-old-exec-path)

  (message (concat "Virtualenv '" virtualenv-name "' deactivated."))

  (setq virtualenv-name nil))

(defun virtualenvp (dir)
  "Check if a directory is a virtualenv"
  (file-exists-p (concat dir "/bin/activate")))

(defun virtualenv-workon-complete ()
  "return available completions for virtualenv-workon"
  (let
      ;;Varlist
      ((filelist (directory-files virtualenv-workon-home t)))
    ;; Get only the basename from the list of the virtual environments
    ;; paths
    (mapcar 'file-name-nondirectory
            ;; Filter the directories and then the virtual environments
            (virtualenv-filter 'virtualenvp
                               (virtualenv-filter 'file-directory-p filelist)))))

(defun virtualenv-workon (name)
  "Issue a virtualenvwrapper-like virtualenv-workon command"
  (interactive (list (completing-read "Virtualenv: " (virtualenv-workon-complete))))
  (virtualenv-activate (concat (getenv "WORKON_HOME") "/" name)))

(defun py-toggle-local-default-use ()
  (interactive)
  "Toggle boolean value of `py-use-local-default'.

Returns `py-use-local-default'

See also `py-install-local-shells'
Installing named virualenv shells is the preffered way,
as it leaves your system default unchanged."
  (setq py-use-local-default (not py-use-local-default))
  (when (interactive-p) (message "py-use-local-default set to %s" py-use-local-default))
  py-use-local-default)

;;; Extended executes
;; created by `write-extended-execute-forms'
(defun py-execute-prepare (form &optional shell dedicated switch)
  "Used by python-extended-executes ."
  (save-excursion
    (let ((beg (prog1
                   (or (funcall (intern-soft (concat "py-beginning-of-" form "-p")))

                       (funcall (intern-soft (concat "py-beginning-of-" form)))
                       (push-mark))))
          (end (funcall (intern-soft (concat "py-end-of-" form)))))
      (py-execute-base beg end shell dedicated switch))))

(defun py-execute-statement-python ()
  "Send statement at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python" nil nil))

(defun py-execute-statement-python-switch ()
  "Send statement at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "statement" "python" nil 'switch))

(defun py-execute-statement-python-noswitch ()
  "Send statement at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "statement" "python" nil 'noswitch))

(defun py-execute-statement-python-dedicated ()
  "Send statement at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python" t nil))

(defun py-execute-statement-python-dedicated-switch ()
  "Send statement at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "statement" "python" t 'switch))

(defun py-execute-statement-ipython ()
  "Send statement at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "statement" "ipython" nil nil))

(defun py-execute-statement-ipython-switch ()
  "Send statement at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "statement" "ipython" nil 'switch))

(defun py-execute-statement-ipython-noswitch ()
  "Send statement at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "statement" "ipython" nil 'noswitch))

(defun py-execute-statement-ipython-dedicated ()
  "Send statement at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "statement" "ipython" t nil))

(defun py-execute-statement-ipython-dedicated-switch ()
  "Send statement at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "statement" "ipython" t 'switch))

(defun py-execute-statement-python3 ()
  "Send statement at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python3" nil nil))

(defun py-execute-statement-python3-switch ()
  "Send statement at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "statement" "python3" nil 'switch))

(defun py-execute-statement-python3-noswitch ()
  "Send statement at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "statement" "python3" nil 'noswitch))

(defun py-execute-statement-python3-dedicated ()
  "Send statement at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python3" t nil))

(defun py-execute-statement-python3-dedicated-switch ()
  "Send statement at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "statement" "python3" t 'switch))

(defun py-execute-statement-python2 ()
  "Send statement at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python2" nil nil))

(defun py-execute-statement-python2-switch ()
  "Send statement at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "statement" "python2" nil 'switch))

(defun py-execute-statement-python2-noswitch ()
  "Send statement at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "statement" "python2" nil 'noswitch))

(defun py-execute-statement-python2-dedicated ()
  "Send statement at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python2" t nil))

(defun py-execute-statement-python2-dedicated-switch ()
  "Send statement at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "statement" "python2" t 'switch))

(defun py-execute-statement-python2.7 ()
  "Send statement at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python2.7" nil nil))

(defun py-execute-statement-python2.7-switch ()
  "Send statement at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "statement" "python2.7" nil 'switch))

(defun py-execute-statement-python2.7-noswitch ()
  "Send statement at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "statement" "python2.7" nil 'noswitch))

(defun py-execute-statement-python2.7-dedicated ()
  "Send statement at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python2.7" t nil))

(defun py-execute-statement-python2.7-dedicated-switch ()
  "Send statement at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "statement" "python2.7" t 'switch))

(defun py-execute-statement-jython ()
  "Send statement at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "statement" "jython" nil nil))

(defun py-execute-statement-jython-switch ()
  "Send statement at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "statement" "jython" nil 'switch))

(defun py-execute-statement-jython-noswitch ()
  "Send statement at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "statement" "jython" nil 'noswitch))

(defun py-execute-statement-jython-dedicated ()
  "Send statement at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "statement" "jython" t nil))

(defun py-execute-statement-jython-dedicated-switch ()
  "Send statement at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "statement" "jython" t 'switch))

(defun py-execute-statement-python3.2 ()
  "Send statement at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python3.2" nil nil))

(defun py-execute-statement-python3.2-switch ()
  "Send statement at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "statement" "python3.2" nil 'switch))

(defun py-execute-statement-python3.2-noswitch ()
  "Send statement at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "statement" "python3.2" nil 'noswitch))

(defun py-execute-statement-python3.2-dedicated ()
  "Send statement at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "statement" "python3.2" t nil))

(defun py-execute-statement-python3.2-dedicated-switch ()
  "Send statement at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "statement" "python3.2" t 'switch))

(defun py-execute-block-python ()
  "Send block at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "block" "python" nil nil))

(defun py-execute-block-python-switch ()
  "Send block at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block" "python" nil 'switch))

(defun py-execute-block-python-noswitch ()
  "Send block at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block" "python" nil 'noswitch))

(defun py-execute-block-python-dedicated ()
  "Send block at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "block" "python" t nil))

(defun py-execute-block-python-dedicated-switch ()
  "Send block at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block" "python" t 'switch))

(defun py-execute-block-ipython ()
  "Send block at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "block" "ipython" nil nil))

(defun py-execute-block-ipython-switch ()
  "Send block at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block" "ipython" nil 'switch))

(defun py-execute-block-ipython-noswitch ()
  "Send block at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block" "ipython" nil 'noswitch))

(defun py-execute-block-ipython-dedicated ()
  "Send block at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "block" "ipython" t nil))

(defun py-execute-block-ipython-dedicated-switch ()
  "Send block at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block" "ipython" t 'switch))

(defun py-execute-block-python3 ()
  "Send block at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "block" "python3" nil nil))

(defun py-execute-block-python3-switch ()
  "Send block at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block" "python3" nil 'switch))

(defun py-execute-block-python3-noswitch ()
  "Send block at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block" "python3" nil 'noswitch))

(defun py-execute-block-python3-dedicated ()
  "Send block at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "block" "python3" t nil))

(defun py-execute-block-python3-dedicated-switch ()
  "Send block at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block" "python3" t 'switch))

(defun py-execute-block-python2 ()
  "Send block at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "block" "python2" nil nil))

(defun py-execute-block-python2-switch ()
  "Send block at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block" "python2" nil 'switch))

(defun py-execute-block-python2-noswitch ()
  "Send block at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block" "python2" nil 'noswitch))

(defun py-execute-block-python2-dedicated ()
  "Send block at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "block" "python2" t nil))

(defun py-execute-block-python2-dedicated-switch ()
  "Send block at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block" "python2" t 'switch))

(defun py-execute-block-python2.7 ()
  "Send block at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "block" "python2.7" nil nil))

(defun py-execute-block-python2.7-switch ()
  "Send block at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block" "python2.7" nil 'switch))

(defun py-execute-block-python2.7-noswitch ()
  "Send block at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block" "python2.7" nil 'noswitch))

(defun py-execute-block-python2.7-dedicated ()
  "Send block at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "block" "python2.7" t nil))

(defun py-execute-block-python2.7-dedicated-switch ()
  "Send block at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block" "python2.7" t 'switch))

(defun py-execute-block-jython ()
  "Send block at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "block" "jython" nil nil))

(defun py-execute-block-jython-switch ()
  "Send block at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block" "jython" nil 'switch))

(defun py-execute-block-jython-noswitch ()
  "Send block at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block" "jython" nil 'noswitch))

(defun py-execute-block-jython-dedicated ()
  "Send block at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "block" "jython" t nil))

(defun py-execute-block-jython-dedicated-switch ()
  "Send block at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block" "jython" t 'switch))

(defun py-execute-block-python3.2 ()
  "Send block at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "block" "python3.2" nil nil))

(defun py-execute-block-python3.2-switch ()
  "Send block at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block" "python3.2" nil 'switch))

(defun py-execute-block-python3.2-noswitch ()
  "Send block at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block" "python3.2" nil 'noswitch))

(defun py-execute-block-python3.2-dedicated ()
  "Send block at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "block" "python3.2" t nil))

(defun py-execute-block-python3.2-dedicated-switch ()
  "Send block at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block" "python3.2" t 'switch))

(defun py-execute-clause-python ()
  "Send clause at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python" nil nil))

(defun py-execute-clause-python-switch ()
  "Send clause at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "clause" "python" nil 'switch))

(defun py-execute-clause-python-noswitch ()
  "Send clause at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "clause" "python" nil 'noswitch))

(defun py-execute-clause-python-dedicated ()
  "Send clause at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python" t nil))

(defun py-execute-clause-python-dedicated-switch ()
  "Send clause at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "clause" "python" t 'switch))

(defun py-execute-clause-ipython ()
  "Send clause at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "clause" "ipython" nil nil))

(defun py-execute-clause-ipython-switch ()
  "Send clause at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "clause" "ipython" nil 'switch))

(defun py-execute-clause-ipython-noswitch ()
  "Send clause at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "clause" "ipython" nil 'noswitch))

(defun py-execute-clause-ipython-dedicated ()
  "Send clause at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "clause" "ipython" t nil))

(defun py-execute-clause-ipython-dedicated-switch ()
  "Send clause at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "clause" "ipython" t 'switch))

(defun py-execute-clause-python3 ()
  "Send clause at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python3" nil nil))

(defun py-execute-clause-python3-switch ()
  "Send clause at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "clause" "python3" nil 'switch))

(defun py-execute-clause-python3-noswitch ()
  "Send clause at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "clause" "python3" nil 'noswitch))

(defun py-execute-clause-python3-dedicated ()
  "Send clause at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python3" t nil))

(defun py-execute-clause-python3-dedicated-switch ()
  "Send clause at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "clause" "python3" t 'switch))

(defun py-execute-clause-python2 ()
  "Send clause at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python2" nil nil))

(defun py-execute-clause-python2-switch ()
  "Send clause at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "clause" "python2" nil 'switch))

(defun py-execute-clause-python2-noswitch ()
  "Send clause at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "clause" "python2" nil 'noswitch))

(defun py-execute-clause-python2-dedicated ()
  "Send clause at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python2" t nil))

(defun py-execute-clause-python2-dedicated-switch ()
  "Send clause at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "clause" "python2" t 'switch))

(defun py-execute-clause-python2.7 ()
  "Send clause at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python2.7" nil nil))

(defun py-execute-clause-python2.7-switch ()
  "Send clause at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "clause" "python2.7" nil 'switch))

(defun py-execute-clause-python2.7-noswitch ()
  "Send clause at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "clause" "python2.7" nil 'noswitch))

(defun py-execute-clause-python2.7-dedicated ()
  "Send clause at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python2.7" t nil))

(defun py-execute-clause-python2.7-dedicated-switch ()
  "Send clause at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "clause" "python2.7" t 'switch))

(defun py-execute-clause-jython ()
  "Send clause at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "clause" "jython" nil nil))

(defun py-execute-clause-jython-switch ()
  "Send clause at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "clause" "jython" nil 'switch))

(defun py-execute-clause-jython-noswitch ()
  "Send clause at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "clause" "jython" nil 'noswitch))

(defun py-execute-clause-jython-dedicated ()
  "Send clause at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "clause" "jython" t nil))

(defun py-execute-clause-jython-dedicated-switch ()
  "Send clause at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "clause" "jython" t 'switch))

(defun py-execute-clause-python3.2 ()
  "Send clause at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python3.2" nil nil))

(defun py-execute-clause-python3.2-switch ()
  "Send clause at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "clause" "python3.2" nil 'switch))

(defun py-execute-clause-python3.2-noswitch ()
  "Send clause at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "clause" "python3.2" nil 'noswitch))

(defun py-execute-clause-python3.2-dedicated ()
  "Send clause at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "clause" "python3.2" t nil))

(defun py-execute-clause-python3.2-dedicated-switch ()
  "Send clause at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "clause" "python3.2" t 'switch))

(defun py-execute-block-or-clause-python ()
  "Send block-or-clause at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python" nil nil))

(defun py-execute-block-or-clause-python-switch ()
  "Send block-or-clause at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python" nil 'switch))

(defun py-execute-block-or-clause-python-noswitch ()
  "Send block-or-clause at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block-or-clause" "python" nil 'noswitch))

(defun py-execute-block-or-clause-python-dedicated ()
  "Send block-or-clause at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python" t nil))

(defun py-execute-block-or-clause-python-dedicated-switch ()
  "Send block-or-clause at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python" t 'switch))

(defun py-execute-block-or-clause-ipython ()
  "Send block-or-clause at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "ipython" nil nil))

(defun py-execute-block-or-clause-ipython-switch ()
  "Send block-or-clause at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block-or-clause" "ipython" nil 'switch))

(defun py-execute-block-or-clause-ipython-noswitch ()
  "Send block-or-clause at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block-or-clause" "ipython" nil 'noswitch))

(defun py-execute-block-or-clause-ipython-dedicated ()
  "Send block-or-clause at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "ipython" t nil))

(defun py-execute-block-or-clause-ipython-dedicated-switch ()
  "Send block-or-clause at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block-or-clause" "ipython" t 'switch))

(defun py-execute-block-or-clause-python3 ()
  "Send block-or-clause at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3" nil nil))

(defun py-execute-block-or-clause-python3-switch ()
  "Send block-or-clause at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3" nil 'switch))

(defun py-execute-block-or-clause-python3-noswitch ()
  "Send block-or-clause at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3" nil 'noswitch))

(defun py-execute-block-or-clause-python3-dedicated ()
  "Send block-or-clause at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3" t nil))

(defun py-execute-block-or-clause-python3-dedicated-switch ()
  "Send block-or-clause at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3" t 'switch))

(defun py-execute-block-or-clause-python2 ()
  "Send block-or-clause at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2" nil nil))

(defun py-execute-block-or-clause-python2-switch ()
  "Send block-or-clause at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2" nil 'switch))

(defun py-execute-block-or-clause-python2-noswitch ()
  "Send block-or-clause at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2" nil 'noswitch))

(defun py-execute-block-or-clause-python2-dedicated ()
  "Send block-or-clause at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2" t nil))

(defun py-execute-block-or-clause-python2-dedicated-switch ()
  "Send block-or-clause at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2" t 'switch))

(defun py-execute-block-or-clause-python2.7 ()
  "Send block-or-clause at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2.7" nil nil))

(defun py-execute-block-or-clause-python2.7-switch ()
  "Send block-or-clause at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2.7" nil 'switch))

(defun py-execute-block-or-clause-python2.7-noswitch ()
  "Send block-or-clause at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2.7" nil 'noswitch))

(defun py-execute-block-or-clause-python2.7-dedicated ()
  "Send block-or-clause at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2.7" t nil))

(defun py-execute-block-or-clause-python2.7-dedicated-switch ()
  "Send block-or-clause at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python2.7" t 'switch))

(defun py-execute-block-or-clause-jython ()
  "Send block-or-clause at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "jython" nil nil))

(defun py-execute-block-or-clause-jython-switch ()
  "Send block-or-clause at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block-or-clause" "jython" nil 'switch))

(defun py-execute-block-or-clause-jython-noswitch ()
  "Send block-or-clause at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block-or-clause" "jython" nil 'noswitch))

(defun py-execute-block-or-clause-jython-dedicated ()
  "Send block-or-clause at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "jython" t nil))

(defun py-execute-block-or-clause-jython-dedicated-switch ()
  "Send block-or-clause at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block-or-clause" "jython" t 'switch))

(defun py-execute-block-or-clause-python3.2 ()
  "Send block-or-clause at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3.2" nil nil))

(defun py-execute-block-or-clause-python3.2-switch ()
  "Send block-or-clause at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3.2" nil 'switch))

(defun py-execute-block-or-clause-python3.2-noswitch ()
  "Send block-or-clause at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3.2" nil 'noswitch))

(defun py-execute-block-or-clause-python3.2-dedicated ()
  "Send block-or-clause at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3.2" t nil))

(defun py-execute-block-or-clause-python3.2-dedicated-switch ()
  "Send block-or-clause at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "block-or-clause" "python3.2" t 'switch))

(defun py-execute-def-python ()
  "Send def at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "def" "python" nil nil))

(defun py-execute-def-python-switch ()
  "Send def at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "def" "python" nil 'switch))

(defun py-execute-def-python-noswitch ()
  "Send def at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "def" "python" nil 'noswitch))

(defun py-execute-def-python-dedicated ()
  "Send def at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "def" "python" t nil))

(defun py-execute-def-python-dedicated-switch ()
  "Send def at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "def" "python" t 'switch))

(defun py-execute-def-ipython ()
  "Send def at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "def" "ipython" nil nil))

(defun py-execute-def-ipython-switch ()
  "Send def at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "def" "ipython" nil 'switch))

(defun py-execute-def-ipython-noswitch ()
  "Send def at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "def" "ipython" nil 'noswitch))

(defun py-execute-def-ipython-dedicated ()
  "Send def at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "def" "ipython" t nil))

(defun py-execute-def-ipython-dedicated-switch ()
  "Send def at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "def" "ipython" t 'switch))

(defun py-execute-def-python3 ()
  "Send def at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "def" "python3" nil nil))

(defun py-execute-def-python3-switch ()
  "Send def at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "def" "python3" nil 'switch))

(defun py-execute-def-python3-noswitch ()
  "Send def at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "def" "python3" nil 'noswitch))

(defun py-execute-def-python3-dedicated ()
  "Send def at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "def" "python3" t nil))

(defun py-execute-def-python3-dedicated-switch ()
  "Send def at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "def" "python3" t 'switch))

(defun py-execute-def-python2 ()
  "Send def at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "def" "python2" nil nil))

(defun py-execute-def-python2-switch ()
  "Send def at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "def" "python2" nil 'switch))

(defun py-execute-def-python2-noswitch ()
  "Send def at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "def" "python2" nil 'noswitch))

(defun py-execute-def-python2-dedicated ()
  "Send def at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "def" "python2" t nil))

(defun py-execute-def-python2-dedicated-switch ()
  "Send def at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "def" "python2" t 'switch))

(defun py-execute-def-python2.7 ()
  "Send def at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "def" "python2.7" nil nil))

(defun py-execute-def-python2.7-switch ()
  "Send def at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "def" "python2.7" nil 'switch))

(defun py-execute-def-python2.7-noswitch ()
  "Send def at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "def" "python2.7" nil 'noswitch))

(defun py-execute-def-python2.7-dedicated ()
  "Send def at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "def" "python2.7" t nil))

(defun py-execute-def-python2.7-dedicated-switch ()
  "Send def at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "def" "python2.7" t 'switch))

(defun py-execute-def-jython ()
  "Send def at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "def" "jython" nil nil))

(defun py-execute-def-jython-switch ()
  "Send def at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "def" "jython" nil 'switch))

(defun py-execute-def-jython-noswitch ()
  "Send def at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "def" "jython" nil 'noswitch))

(defun py-execute-def-jython-dedicated ()
  "Send def at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "def" "jython" t nil))

(defun py-execute-def-jython-dedicated-switch ()
  "Send def at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "def" "jython" t 'switch))

(defun py-execute-def-python3.2 ()
  "Send def at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "def" "python3.2" nil nil))

(defun py-execute-def-python3.2-switch ()
  "Send def at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "def" "python3.2" nil 'switch))

(defun py-execute-def-python3.2-noswitch ()
  "Send def at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "def" "python3.2" nil 'noswitch))

(defun py-execute-def-python3.2-dedicated ()
  "Send def at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "def" "python3.2" t nil))

(defun py-execute-def-python3.2-dedicated-switch ()
  "Send def at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "def" "python3.2" t 'switch))

(defun py-execute-class-python ()
  "Send class at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "class" "python" nil nil))

(defun py-execute-class-python-switch ()
  "Send class at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "class" "python" nil 'switch))

(defun py-execute-class-python-noswitch ()
  "Send class at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "class" "python" nil 'noswitch))

(defun py-execute-class-python-dedicated ()
  "Send class at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "class" "python" t nil))

(defun py-execute-class-python-dedicated-switch ()
  "Send class at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "class" "python" t 'switch))

(defun py-execute-class-ipython ()
  "Send class at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "class" "ipython" nil nil))

(defun py-execute-class-ipython-switch ()
  "Send class at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "class" "ipython" nil 'switch))

(defun py-execute-class-ipython-noswitch ()
  "Send class at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "class" "ipython" nil 'noswitch))

(defun py-execute-class-ipython-dedicated ()
  "Send class at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "class" "ipython" t nil))

(defun py-execute-class-ipython-dedicated-switch ()
  "Send class at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "class" "ipython" t 'switch))

(defun py-execute-class-python3 ()
  "Send class at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "class" "python3" nil nil))

(defun py-execute-class-python3-switch ()
  "Send class at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "class" "python3" nil 'switch))

(defun py-execute-class-python3-noswitch ()
  "Send class at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "class" "python3" nil 'noswitch))

(defun py-execute-class-python3-dedicated ()
  "Send class at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "class" "python3" t nil))

(defun py-execute-class-python3-dedicated-switch ()
  "Send class at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "class" "python3" t 'switch))

(defun py-execute-class-python2 ()
  "Send class at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "class" "python2" nil nil))

(defun py-execute-class-python2-switch ()
  "Send class at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "class" "python2" nil 'switch))

(defun py-execute-class-python2-noswitch ()
  "Send class at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "class" "python2" nil 'noswitch))

(defun py-execute-class-python2-dedicated ()
  "Send class at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "class" "python2" t nil))

(defun py-execute-class-python2-dedicated-switch ()
  "Send class at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "class" "python2" t 'switch))

(defun py-execute-class-python2.7 ()
  "Send class at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "class" "python2.7" nil nil))

(defun py-execute-class-python2.7-switch ()
  "Send class at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "class" "python2.7" nil 'switch))

(defun py-execute-class-python2.7-noswitch ()
  "Send class at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "class" "python2.7" nil 'noswitch))

(defun py-execute-class-python2.7-dedicated ()
  "Send class at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "class" "python2.7" t nil))

(defun py-execute-class-python2.7-dedicated-switch ()
  "Send class at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "class" "python2.7" t 'switch))

(defun py-execute-class-jython ()
  "Send class at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "class" "jython" nil nil))

(defun py-execute-class-jython-switch ()
  "Send class at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "class" "jython" nil 'switch))

(defun py-execute-class-jython-noswitch ()
  "Send class at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "class" "jython" nil 'noswitch))

(defun py-execute-class-jython-dedicated ()
  "Send class at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "class" "jython" t nil))

(defun py-execute-class-jython-dedicated-switch ()
  "Send class at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "class" "jython" t 'switch))

(defun py-execute-class-python3.2 ()
  "Send class at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "class" "python3.2" nil nil))

(defun py-execute-class-python3.2-switch ()
  "Send class at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "class" "python3.2" nil 'switch))

(defun py-execute-class-python3.2-noswitch ()
  "Send class at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "class" "python3.2" nil 'noswitch))

(defun py-execute-class-python3.2-dedicated ()
  "Send class at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "class" "python3.2" t nil))

(defun py-execute-class-python3.2-dedicated-switch ()
  "Send class at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "class" "python3.2" t 'switch))

(defun py-execute-region-python (beg end)
  "Send region at point to Python interpreter. "
  (interactive "r")
  (py-execute-base beg end "python" nil nil))

(defun py-execute-region-python-switch (beg end)
  "Send region at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive "r")
  (py-execute-base beg end "python" nil 'switch))

(defun py-execute-region-python-noswitch (beg end)
  "Send region at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive "r")
  (py-execute-base beg end "python" nil 'noswitch))

(defun py-execute-region-python-dedicated (beg end)
  "Send region at point to Python unique interpreter. "
  (interactive "r")
  (py-execute-base beg end "python" t nil))

(defun py-execute-region-python-dedicated-switch (beg end)
  "Send region at point to Python unique interpreter and switch to result. "
  (interactive "r")
  (py-execute-base beg end "python" t 'switch))

(defun py-execute-region-ipython (beg end)
  "Send region at point to IPython interpreter. "
  (interactive "r")
  (py-execute-base beg end "ipython" nil nil))

(defun py-execute-region-ipython-switch (beg end)
  "Send region at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive "r")
  (py-execute-base beg end "ipython" nil 'switch))

(defun py-execute-region-ipython-noswitch (beg end)
  "Send region at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive "r")
  (py-execute-base beg end "ipython" nil 'noswitch))

(defun py-execute-region-ipython-dedicated (beg end)
  "Send region at point to IPython unique interpreter. "
  (interactive "r")
  (py-execute-base beg end "ipython" t nil))

(defun py-execute-region-ipython-dedicated-switch (beg end)
  "Send region at point to IPython unique interpreter and switch to result. "
  (interactive "r")
  (py-execute-base beg end "ipython" t 'switch))

(defun py-execute-region-python3 (beg end)
  "Send region at point to Python3 interpreter. "
  (interactive "r")
  (py-execute-base beg end "python3" nil nil))

(defun py-execute-region-python3-switch (beg end)
  "Send region at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive "r")
  (py-execute-base beg end "python3" nil 'switch))

(defun py-execute-region-python3-noswitch (beg end)
  "Send region at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive "r")
  (py-execute-base beg end "python3" nil 'noswitch))

(defun py-execute-region-python3-dedicated (beg end)
  "Send region at point to Python3 unique interpreter. "
  (interactive "r")
  (py-execute-base beg end "python3" t nil))

(defun py-execute-region-python3-dedicated-switch (beg end)
  "Send region at point to Python3 unique interpreter and switch to result. "
  (interactive "r")
  (py-execute-base beg end "python3" t 'switch))

(defun py-execute-region-python2 (beg end)
  "Send region at point to Python2 interpreter. "
  (interactive "r")
  (py-execute-base beg end "python2" nil nil))

(defun py-execute-region-python2-switch (beg end)
  "Send region at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive "r")
  (py-execute-base beg end "python2" nil 'switch))

(defun py-execute-region-python2-noswitch (beg end)
  "Send region at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive "r")
  (py-execute-base beg end "python2" nil 'noswitch))

(defun py-execute-region-python2-dedicated (beg end)
  "Send region at point to Python2 unique interpreter. "
  (interactive "r")
  (py-execute-base beg end "python2" t nil))

(defun py-execute-region-python2-dedicated-switch (beg end)
  "Send region at point to Python2 unique interpreter and switch to result. "
  (interactive "r")
  (py-execute-base beg end "python2" t 'switch))

(defun py-execute-region-python2.7 (beg end)
  "Send region at point to Python2.7 interpreter. "
  (interactive "r")
  (py-execute-base beg end "python2.7" nil nil))

(defun py-execute-region-python2.7-switch (beg end)
  "Send region at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive "r")
  (py-execute-base beg end "python2.7" nil 'switch))

(defun py-execute-region-python2.7-noswitch (beg end)
  "Send region at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive "r")
  (py-execute-base beg end "python2.7" nil 'noswitch))

(defun py-execute-region-python2.7-dedicated (beg end)
  "Send region at point to Python2.7 unique interpreter. "
  (interactive "r")
  (py-execute-base beg end "python2.7" t nil))

(defun py-execute-region-python2.7-dedicated-switch (beg end)
  "Send region at point to Python2.7 unique interpreter and switch to result. "
  (interactive "r")
  (py-execute-base beg end "python2.7" t 'switch))

(defun py-execute-region-jython (beg end)
  "Send region at point to Jython interpreter. "
  (interactive "r")
  (py-execute-base beg end "jython" nil nil))

(defun py-execute-region-jython-switch (beg end)
  "Send region at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive "r")
  (py-execute-base beg end "jython" nil 'switch))

(defun py-execute-region-jython-noswitch (beg end)
  "Send region at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive "r")
  (py-execute-base beg end "jython" nil 'noswitch))

(defun py-execute-region-jython-dedicated (beg end)
  "Send region at point to Jython unique interpreter. "
  (interactive "r")
  (py-execute-base beg end "jython" t nil))

(defun py-execute-region-jython-dedicated-switch (beg end)
  "Send region at point to Jython unique interpreter and switch to result. "
  (interactive "r")
  (py-execute-base beg end "jython" t 'switch))

(defun py-execute-region-python3.2 (beg end)
  "Send region at point to Python3.2 interpreter. "
  (interactive "r")
  (py-execute-base beg end "python3.2" nil nil))

(defun py-execute-region-python3.2-switch (beg end)
  "Send region at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive "r")
  (py-execute-base beg end "python3.2" nil 'switch))

(defun py-execute-region-python3.2-noswitch (beg end)
  "Send region at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive "r")
  (py-execute-base beg end "python3.2" nil 'noswitch))

(defun py-execute-region-python3.2-dedicated (beg end)
  "Send region at point to Python3.2 unique interpreter. "
  (interactive "r")
  (py-execute-base beg end "python3.2" t nil))

(defun py-execute-region-python3.2-dedicated-switch (beg end)
  "Send region at point to Python3.2 unique interpreter and switch to result. "
  (interactive "r")
  (py-execute-base beg end "python3.2" t 'switch))

(defun py-execute-buffer-python ()
  "Send buffer at point to Python interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python" nil nil))))

(defun py-execute-buffer-python-switch ()
  "Send buffer at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python" nil 'switch))))

(defun py-execute-buffer-python-noswitch ()
  "Send buffer at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python" nil 'noswitch))))

(defun py-execute-buffer-python-dedicated ()
  "Send buffer at point to Python unique interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python" t nil))))

(defun py-execute-buffer-python-dedicated-switch ()
  "Send buffer at point to Python unique interpreter and switch to result. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python" t 'switch))))

(defun py-execute-buffer-ipython ()
  "Send buffer at point to IPython interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "ipython" nil nil))))

(defun py-execute-buffer-ipython-switch ()
  "Send buffer at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "ipython" nil 'switch))))

(defun py-execute-buffer-ipython-noswitch ()
  "Send buffer at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "ipython" nil 'noswitch))))

(defun py-execute-buffer-ipython-dedicated ()
  "Send buffer at point to IPython unique interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "ipython" t nil))))

(defun py-execute-buffer-ipython-dedicated-switch ()
  "Send buffer at point to IPython unique interpreter and switch to result. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "ipython" t 'switch))))

(defun py-execute-buffer-python3 ()
  "Send buffer at point to Python3 interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3" nil nil))))

(defun py-execute-buffer-python3-switch ()
  "Send buffer at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3" nil 'switch))))

(defun py-execute-buffer-python3-noswitch ()
  "Send buffer at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3" nil 'noswitch))))

(defun py-execute-buffer-python3-dedicated ()
  "Send buffer at point to Python3 unique interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3" t nil))))

(defun py-execute-buffer-python3-dedicated-switch ()
  "Send buffer at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3" t 'switch))))

(defun py-execute-buffer-python2 ()
  "Send buffer at point to Python2 interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2" nil nil))))

(defun py-execute-buffer-python2-switch ()
  "Send buffer at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2" nil 'switch))))

(defun py-execute-buffer-python2-noswitch ()
  "Send buffer at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2" nil 'noswitch))))

(defun py-execute-buffer-python2-dedicated ()
  "Send buffer at point to Python2 unique interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2" t nil))))

(defun py-execute-buffer-python2-dedicated-switch ()
  "Send buffer at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2" t 'switch))))

(defun py-execute-buffer-python2.7 ()
  "Send buffer at point to Python2.7 interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2.7" nil nil))))

(defun py-execute-buffer-python2.7-switch ()
  "Send buffer at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2.7" nil 'switch))))

(defun py-execute-buffer-python2.7-noswitch ()
  "Send buffer at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2.7" nil 'noswitch))))

(defun py-execute-buffer-python2.7-dedicated ()
  "Send buffer at point to Python2.7 unique interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2.7" t nil))))

(defun py-execute-buffer-python2.7-dedicated-switch ()
  "Send buffer at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python2.7" t 'switch))))

(defun py-execute-buffer-jython ()
  "Send buffer at point to Jython interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "jython" nil nil))))

(defun py-execute-buffer-jython-switch ()
  "Send buffer at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "jython" nil 'switch))))

(defun py-execute-buffer-jython-noswitch ()
  "Send buffer at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "jython" nil 'noswitch))))

(defun py-execute-buffer-jython-dedicated ()
  "Send buffer at point to Jython unique interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "jython" t nil))))

(defun py-execute-buffer-jython-dedicated-switch ()
  "Send buffer at point to Jython unique interpreter and switch to result. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "jython" t 'switch))))

(defun py-execute-buffer-python3.2 ()
  "Send buffer at point to Python3.2 interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3.2" nil nil))))

(defun py-execute-buffer-python3.2-switch ()
  "Send buffer at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3.2" nil 'switch))))

(defun py-execute-buffer-python3.2-noswitch ()
  "Send buffer at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3.2" nil 'noswitch))))

(defun py-execute-buffer-python3.2-dedicated ()
  "Send buffer at point to Python3.2 unique interpreter. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3.2" t nil))))

(defun py-execute-buffer-python3.2-dedicated-switch ()
  "Send buffer at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (save-excursion
    (let ((wholebuf t)
          (py-master-file (or py-master-file (py-fetch-py-master-file)))
          beg end)
      (when py-master-file
        (let* ((filename (expand-file-name py-master-file))
               (buffer (or (get-file-buffer filename)
                           (find-file-noselect filename))))
          (set-buffer buffer)))
      (setq beg (point-min))
      (setq end (point-max))
      (py-execute-region beg end "python3.2" t 'switch))))

(defun py-execute-expression-python ()
  "Send expression at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python" nil nil))

(defun py-execute-expression-python-switch ()
  "Send expression at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "expression" "python" nil 'switch))

(defun py-execute-expression-python-noswitch ()
  "Send expression at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "expression" "python" nil 'noswitch))

(defun py-execute-expression-python-dedicated ()
  "Send expression at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python" t nil))

(defun py-execute-expression-python-dedicated-switch ()
  "Send expression at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "expression" "python" t 'switch))

(defun py-execute-expression-ipython ()
  "Send expression at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "expression" "ipython" nil nil))

(defun py-execute-expression-ipython-switch ()
  "Send expression at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "expression" "ipython" nil 'switch))

(defun py-execute-expression-ipython-noswitch ()
  "Send expression at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "expression" "ipython" nil 'noswitch))

(defun py-execute-expression-ipython-dedicated ()
  "Send expression at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "expression" "ipython" t nil))

(defun py-execute-expression-ipython-dedicated-switch ()
  "Send expression at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "expression" "ipython" t 'switch))

(defun py-execute-expression-python3 ()
  "Send expression at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python3" nil nil))

(defun py-execute-expression-python3-switch ()
  "Send expression at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "expression" "python3" nil 'switch))

(defun py-execute-expression-python3-noswitch ()
  "Send expression at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "expression" "python3" nil 'noswitch))

(defun py-execute-expression-python3-dedicated ()
  "Send expression at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python3" t nil))

(defun py-execute-expression-python3-dedicated-switch ()
  "Send expression at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "expression" "python3" t 'switch))

(defun py-execute-expression-python2 ()
  "Send expression at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python2" nil nil))

(defun py-execute-expression-python2-switch ()
  "Send expression at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "expression" "python2" nil 'switch))

(defun py-execute-expression-python2-noswitch ()
  "Send expression at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "expression" "python2" nil 'noswitch))

(defun py-execute-expression-python2-dedicated ()
  "Send expression at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python2" t nil))

(defun py-execute-expression-python2-dedicated-switch ()
  "Send expression at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "expression" "python2" t 'switch))

(defun py-execute-expression-python2.7 ()
  "Send expression at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python2.7" nil nil))

(defun py-execute-expression-python2.7-switch ()
  "Send expression at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "expression" "python2.7" nil 'switch))

(defun py-execute-expression-python2.7-noswitch ()
  "Send expression at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "expression" "python2.7" nil 'noswitch))

(defun py-execute-expression-python2.7-dedicated ()
  "Send expression at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python2.7" t nil))

(defun py-execute-expression-python2.7-dedicated-switch ()
  "Send expression at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "expression" "python2.7" t 'switch))

(defun py-execute-expression-jython ()
  "Send expression at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "expression" "jython" nil nil))

(defun py-execute-expression-jython-switch ()
  "Send expression at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "expression" "jython" nil 'switch))

(defun py-execute-expression-jython-noswitch ()
  "Send expression at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "expression" "jython" nil 'noswitch))

(defun py-execute-expression-jython-dedicated ()
  "Send expression at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "expression" "jython" t nil))

(defun py-execute-expression-jython-dedicated-switch ()
  "Send expression at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "expression" "jython" t 'switch))

(defun py-execute-expression-python3.2 ()
  "Send expression at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python3.2" nil nil))

(defun py-execute-expression-python3.2-switch ()
  "Send expression at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "expression" "python3.2" nil 'switch))

(defun py-execute-expression-python3.2-noswitch ()
  "Send expression at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "expression" "python3.2" nil 'noswitch))

(defun py-execute-expression-python3.2-dedicated ()
  "Send expression at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "expression" "python3.2" t nil))

(defun py-execute-expression-python3.2-dedicated-switch ()
  "Send expression at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "expression" "python3.2" t 'switch))

(defun py-execute-partial-expression-python ()
  "Send partial-expression at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python" nil nil))

(defun py-execute-partial-expression-python-switch ()
  "Send partial-expression at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "partial-expression" "python" nil 'switch))

(defun py-execute-partial-expression-python-noswitch ()
  "Send partial-expression at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "partial-expression" "python" nil 'noswitch))

(defun py-execute-partial-expression-python-dedicated ()
  "Send partial-expression at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python" t nil))

(defun py-execute-partial-expression-python-dedicated-switch ()
  "Send partial-expression at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "partial-expression" "python" t 'switch))

(defun py-execute-partial-expression-ipython ()
  "Send partial-expression at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "ipython" nil nil))

(defun py-execute-partial-expression-ipython-switch ()
  "Send partial-expression at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "partial-expression" "ipython" nil 'switch))

(defun py-execute-partial-expression-ipython-noswitch ()
  "Send partial-expression at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "partial-expression" "ipython" nil 'noswitch))

(defun py-execute-partial-expression-ipython-dedicated ()
  "Send partial-expression at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "ipython" t nil))

(defun py-execute-partial-expression-ipython-dedicated-switch ()
  "Send partial-expression at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "partial-expression" "ipython" t 'switch))

(defun py-execute-partial-expression-python3 ()
  "Send partial-expression at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python3" nil nil))

(defun py-execute-partial-expression-python3-switch ()
  "Send partial-expression at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "partial-expression" "python3" nil 'switch))

(defun py-execute-partial-expression-python3-noswitch ()
  "Send partial-expression at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "partial-expression" "python3" nil 'noswitch))

(defun py-execute-partial-expression-python3-dedicated ()
  "Send partial-expression at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python3" t nil))

(defun py-execute-partial-expression-python3-dedicated-switch ()
  "Send partial-expression at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "partial-expression" "python3" t 'switch))

(defun py-execute-partial-expression-python2 ()
  "Send partial-expression at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python2" nil nil))

(defun py-execute-partial-expression-python2-switch ()
  "Send partial-expression at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "partial-expression" "python2" nil 'switch))

(defun py-execute-partial-expression-python2-noswitch ()
  "Send partial-expression at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "partial-expression" "python2" nil 'noswitch))

(defun py-execute-partial-expression-python2-dedicated ()
  "Send partial-expression at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python2" t nil))

(defun py-execute-partial-expression-python2-dedicated-switch ()
  "Send partial-expression at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "partial-expression" "python2" t 'switch))

(defun py-execute-partial-expression-python2.7 ()
  "Send partial-expression at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python2.7" nil nil))

(defun py-execute-partial-expression-python2.7-switch ()
  "Send partial-expression at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "partial-expression" "python2.7" nil 'switch))

(defun py-execute-partial-expression-python2.7-noswitch ()
  "Send partial-expression at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "partial-expression" "python2.7" nil 'noswitch))

(defun py-execute-partial-expression-python2.7-dedicated ()
  "Send partial-expression at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python2.7" t nil))

(defun py-execute-partial-expression-python2.7-dedicated-switch ()
  "Send partial-expression at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "partial-expression" "python2.7" t 'switch))

(defun py-execute-partial-expression-jython ()
  "Send partial-expression at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "jython" nil nil))

(defun py-execute-partial-expression-jython-switch ()
  "Send partial-expression at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "partial-expression" "jython" nil 'switch))

(defun py-execute-partial-expression-jython-noswitch ()
  "Send partial-expression at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "partial-expression" "jython" nil 'noswitch))

(defun py-execute-partial-expression-jython-dedicated ()
  "Send partial-expression at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "jython" t nil))

(defun py-execute-partial-expression-jython-dedicated-switch ()
  "Send partial-expression at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "partial-expression" "jython" t 'switch))

(defun py-execute-partial-expression-python3.2 ()
  "Send partial-expression at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python3.2" nil nil))

(defun py-execute-partial-expression-python3.2-switch ()
  "Send partial-expression at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "partial-expression" "python3.2" nil 'switch))

(defun py-execute-partial-expression-python3.2-noswitch ()
  "Send partial-expression at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "partial-expression" "python3.2" nil 'noswitch))

(defun py-execute-partial-expression-python3.2-dedicated ()
  "Send partial-expression at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "partial-expression" "python3.2" t nil))

(defun py-execute-partial-expression-python3.2-dedicated-switch ()
  "Send partial-expression at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "partial-expression" "python3.2" t 'switch))

(defun py-execute-line-python ()
  "Send line at point to Python interpreter. "
  (interactive)
  (py-execute-prepare "line" "python" nil nil))

(defun py-execute-line-python-switch ()
  "Send line at point to Python interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "line" "python" nil 'switch))

(defun py-execute-line-python-noswitch ()
  "Send line at point to Python interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "line" "python" nil 'noswitch))

(defun py-execute-line-python-dedicated ()
  "Send line at point to Python unique interpreter. "
  (interactive)
  (py-execute-prepare "line" "python" t nil))

(defun py-execute-line-python-dedicated-switch ()
  "Send line at point to Python unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "line" "python" t 'switch))

(defun py-execute-line-ipython ()
  "Send line at point to IPython interpreter. "
  (interactive)
  (py-execute-prepare "line" "ipython" nil nil))

(defun py-execute-line-ipython-switch ()
  "Send line at point to IPython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "line" "ipython" nil 'switch))

(defun py-execute-line-ipython-noswitch ()
  "Send line at point to IPython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "line" "ipython" nil 'noswitch))

(defun py-execute-line-ipython-dedicated ()
  "Send line at point to IPython unique interpreter. "
  (interactive)
  (py-execute-prepare "line" "ipython" t nil))

(defun py-execute-line-ipython-dedicated-switch ()
  "Send line at point to IPython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "line" "ipython" t 'switch))

(defun py-execute-line-python3 ()
  "Send line at point to Python3 interpreter. "
  (interactive)
  (py-execute-prepare "line" "python3" nil nil))

(defun py-execute-line-python3-switch ()
  "Send line at point to Python3 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "line" "python3" nil 'switch))

(defun py-execute-line-python3-noswitch ()
  "Send line at point to Python3 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "line" "python3" nil 'noswitch))

(defun py-execute-line-python3-dedicated ()
  "Send line at point to Python3 unique interpreter. "
  (interactive)
  (py-execute-prepare "line" "python3" t nil))

(defun py-execute-line-python3-dedicated-switch ()
  "Send line at point to Python3 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "line" "python3" t 'switch))

(defun py-execute-line-python2 ()
  "Send line at point to Python2 interpreter. "
  (interactive)
  (py-execute-prepare "line" "python2" nil nil))

(defun py-execute-line-python2-switch ()
  "Send line at point to Python2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "line" "python2" nil 'switch))

(defun py-execute-line-python2-noswitch ()
  "Send line at point to Python2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "line" "python2" nil 'noswitch))

(defun py-execute-line-python2-dedicated ()
  "Send line at point to Python2 unique interpreter. "
  (interactive)
  (py-execute-prepare "line" "python2" t nil))

(defun py-execute-line-python2-dedicated-switch ()
  "Send line at point to Python2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "line" "python2" t 'switch))

(defun py-execute-line-python2.7 ()
  "Send line at point to Python2.7 interpreter. "
  (interactive)
  (py-execute-prepare "line" "python2.7" nil nil))

(defun py-execute-line-python2.7-switch ()
  "Send line at point to Python2.7 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "line" "python2.7" nil 'switch))

(defun py-execute-line-python2.7-noswitch ()
  "Send line at point to Python2.7 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "line" "python2.7" nil 'noswitch))

(defun py-execute-line-python2.7-dedicated ()
  "Send line at point to Python2.7 unique interpreter. "
  (interactive)
  (py-execute-prepare "line" "python2.7" t nil))

(defun py-execute-line-python2.7-dedicated-switch ()
  "Send line at point to Python2.7 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "line" "python2.7" t 'switch))

(defun py-execute-line-jython ()
  "Send line at point to Jython interpreter. "
  (interactive)
  (py-execute-prepare "line" "jython" nil nil))

(defun py-execute-line-jython-switch ()
  "Send line at point to Jython interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "line" "jython" nil 'switch))

(defun py-execute-line-jython-noswitch ()
  "Send line at point to Jython interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "line" "jython" nil 'noswitch))

(defun py-execute-line-jython-dedicated ()
  "Send line at point to Jython unique interpreter. "
  (interactive)
  (py-execute-prepare "line" "jython" t nil))

(defun py-execute-line-jython-dedicated-switch ()
  "Send line at point to Jython unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "line" "jython" t 'switch))

(defun py-execute-line-python3.2 ()
  "Send line at point to Python3.2 interpreter. "
  (interactive)
  (py-execute-prepare "line" "python3.2" nil nil))

(defun py-execute-line-python3.2-switch ()
  "Send line at point to Python3.2 interpreter.

Switch to output buffer. Ignores `py-shell-switch-buffers-on-execute-p'. "
  (interactive)
  (py-execute-prepare "line" "python3.2" nil 'switch))

(defun py-execute-line-python3.2-noswitch ()
  "Send line at point to Python3.2 interpreter.

Keep current buffer. Ignores `py-shell-switch-buffers-on-execute-p' "
  (interactive)
  (py-execute-prepare "line" "python3.2" nil 'noswitch))

(defun py-execute-line-python3.2-dedicated ()
  "Send line at point to Python3.2 unique interpreter. "
  (interactive)
  (py-execute-prepare "line" "python3.2" t nil))

(defun py-execute-line-python3.2-dedicated-switch ()
  "Send line at point to Python3.2 unique interpreter and switch to result. "
  (interactive)
  (py-execute-prepare "line" "python3.2" t 'switch))

;;; Column-marker - highlight columns
;; merged from column-marker.el,
;; Created: Tue Nov 22 10:26:03 2005
;; Last-Updated: Fri Jan 22 11:28:48 2010 (-0800) By: dradams
;; original Author: Rick Bielawski <rbielaws@i1.net>

(defface column-marker-1 '((t (:background "gray")))
  "Face used for a column marker.  Usually a background color."
  :group 'faces)

(defvar column-marker-1-face 'column-marker-1
  "Face used for a column marker.  Usually a background color.
Changing this directly affects only new markers.")

(defface column-marker-2 '((t (:background "cyan3")))
  "Face used for a column marker.  Usually a background color."
  :group 'faces)

(defvar column-marker-2-face 'column-marker-2
  "Face used for a column marker.  Usually a background color.
Changing this directly affects only new markers." )

(defface column-marker-3 '((t (:background "orchid3")))
  "Face used for a column marker.  Usually a background color."
  :group 'faces)

(defvar column-marker-3-face 'column-marker-3
  "Face used for a column marker.  Usually a background color.
Changing this directly affects only new markers." )

(defvar column-marker-vars ()
  "List of all internal column-marker variables")
(make-variable-buffer-local 'column-marker-vars) ; Buffer local in all buffers.

(defmacro column-marker-create (var &optional face)
  "Define a column marker named VAR.
FACE is the face to use.  If nil, then face `column-marker-1' is used."
  (setq face (or face 'column-marker-1))
  `(progn
     ;; define context variable ,VAR so marker can be removed if desired
     (defvar ,var ()
       "Buffer local. Used internally to store column marker spec.")
     ;; context must be buffer local since font-lock is
     (make-variable-buffer-local ',var)
     ;; Define wrapper function named ,VAR to call `column-marker-internal'
     (defun ,var (arg)
       ,(concat "Highlight column with face `" (symbol-name face)
                "'.\nWith no prefix argument, highlight current column.\n"
                "With non-negative numeric prefix arg, highlight that column number.\n"
                "With plain `C-u' (no number), turn off this column marker.\n"
                "With `C-u C-u' or negative prefix arg, turn off all column-marker highlighting.")
       (interactive "P")
       (unless (memq ',var column-marker-vars) (push ',var column-marker-vars))
       (cond ((null arg)          ; Default: highlight current column.
              (column-marker-internal ',var (1+ (current-column)) ,face))
             ((consp arg)
              (if (= 4 (car arg))
                  (column-marker-internal ',var nil) ; `C-u': Remove this column highlighting.
                (dolist (var column-marker-vars)
                  (column-marker-internal var nil)))) ; `C-u C-u': Remove all column highlighting.
             ((and (integerp arg) (>= arg 0)) ; `C-u 70': Highlight that column.
              (column-marker-internal ',var (1+ (prefix-numeric-value arg)) ,face))
             (t           ; `C-u -40': Remove all column highlighting.
              (dolist (var column-marker-vars)
                (column-marker-internal var nil)))))))

(defun column-marker-find (col)
  "Defines a function to locate a character in column COL.
Returns the function symbol, named `column-marker-move-to-COL'."
  (let ((fn-symb  (intern (format "column-marker-move-to-%d" col))))
    (fset `,fn-symb
          `(lambda (end)
             (let ((start (point)))
               (when (> end (point-max)) (setq end (point-max)))

               ;; Try to keep `move-to-column' from going backward, though it still can.
               (unless (< (current-column) ,col) (forward-line 1))

               ;; Again, don't go backward.  Try to move to correct column.
               (when (< (current-column) ,col) (move-to-column ,col))

               ;; If not at target column, try to move to it.
               (while (and (< (current-column) ,col) (< (point) end)
                           (= 0 (+ (forward-line 1) (current-column)))) ; Should be bol.
                 (move-to-column ,col))

               ;; If at target column, not past end, and not prior to start,
               ;; then set match data and return t.  Otherwise go to start
               ;; and return nil.
               (if (and (= ,col (current-column)) (<= (point) end) (> (point) start))
                   (progn (set-match-data (list (1- (point)) (point)))
                          t)            ; Return t.
                 (goto-char start)
                 nil))))                ; Return nil.
    fn-symb))

(defun column-marker-internal (sym col &optional face)
  "SYM is the symbol for holding the column marker context.
COL is the column in which a marker should be set.
Supplying nil or 0 for COL turns off the marker.
FACE is the face to use.  If nil, then face `column-marker-1' is used."
  (setq face (or face 'column-marker-1))
  (when (symbol-value sym)   ; Remove any previously set column marker
    (font-lock-remove-keywords nil (symbol-value sym))
    (set sym nil))
  (when (or (listp col) (< col 0)) (setq col nil)) ; Allow nonsense stuff to turn off the marker
  (when col                             ; Generate a new column marker
    (set sym `((,(column-marker-find col) (0 ',face prepend t))))
    (font-lock-add-keywords nil (symbol-value sym) t))
  (font-lock-fontify-buffer))

;; If you need more markers you can create your own similarly.
;; All markers can be in use at once, and each is buffer-local,
;; so there is no good reason to define more unless you need more
;; markers in a single buffer.
(column-marker-create column-marker-1 column-marker-1-face)
(column-marker-create column-marker-2 column-marker-2-face)
(column-marker-create column-marker-3 column-marker-3-face)

;; (autoload 'column-marker-1 "column-marker" "Highlight a column." t)

(defalias 'ipython-send-and-indent 'py-execute-line-ipython)
(defalias 'py-execute-region-in-shell 'py-execute-region)
(defalias 'py-shell-command-on-region 'py-execute-region-region)
(defalias 'py-send-region-ipython 'py-execute-region-ipython)
(defalias 'py-ipython-shell-command-on-region 'py-execute-region-ipython)
(provide 'python-mode)
;;; python-mode.el ends here
