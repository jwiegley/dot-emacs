;;; python-mode.el --- Edit, debug, develop, run Python programs. -*- lexical-binding: t; -*- 

;; Includes a minor mode for handling a Python/IPython shell,
;; and can take advantage of Pymacs when installed.

;; This file not shipped as part of GNU Emacs.

;; Keywords: languages, processes, python, oop

;; Version: "6.2.3"

;; URL: https://gitlab.com/groups/python-mode-devs

;; Package-Requires: (emacs "24")
;; Copyright (C) 1992,1993,1994  Tim Peters

;; Author: 2015-2017 https://gitlab.com/groups/python-mode-devs
;;         2003-2014 https://launchpad.net/python-mode
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

;; See documentation in README.org, README.DEVEL.org

;; Please report bugs at
;; https://gitlab.com/python-mode-devs/python-mode/issues

;; available commands are documented in directory "doc" as
;; commands-python-mode.org

;; As for `py-add-abbrev':
;; Similar to `add-mode-abbrev', but uses
;; `py-partial-expression' before point for expansion to
;; store, not `word'.  Also provides a proposal for new
;; abbrevs.

;; Proposal for an abbrev is composed from the downcased
;; initials of expansion - provided they are of char-class
;; [:alpha:]
;;
;; For example code below would be recognised as a
;; `py-expression' composed by three
;; py-partial-expressions.
;;
;; OrderedDict.popitem(last=True)
;;
;; Putting the curser at the EOL, M-3 M-x py-add-abbrev
;;
;; would prompt "op" for an abbrev to store, as first
;; `py-partial-expression' beginns with a "(", which is
;; not taken as proposal.

;;; Code:



(defgroup python-mode nil
  "Support for the Python programming language, <http://www.python.org/>"
  :group 'languages
  :prefix "py-")

(defconst py-version "6.2.3")

(defcustom py-install-directory ""
  "Directory where python-mode.el and it's subdirectories should be installed.

Needed for completion and other environment stuff only."

  :type 'string
  :tag "py-install-directory"
  :group 'python-mode)

(defcustom py-pythonpath ""
  "Define $PYTHONPATH here, if needed.

Emacs doesn't read .bashrc"

  :type 'string
  :tag "py-pythonpath"
  :group 'python-mode)

(when (string= "" py-install-directory)
  (setq py-install-directory default-directory))

(defcustom python-mode-modeline-display "Py"
  "String to display in Emacs modeline."

  :type 'string
  :tag "python-mode-modeline-display"
  :group 'python-mode)

(defcustom py-extensions "py-extensions.el"
  "File where extensions to python-mode.el should be installed.

Used by virtualenv support."

  :type 'string
  :tag "py-extensions"
  :group 'python-mode)

(defcustom info-lookup-mode "python"
  "Which Python documentation should be queried.

Make sure it's accessible from Emacs by \\<emacs-lisp-mode-map> \\[info] ...
See INSTALL-INFO-FILES for help."

  :type 'string
  :tag "info-lookup-mode"
  :group 'python-mode)

(defcustom py-fast-process-p nil
  "Use `py-fast-process'.

Commands prefixed \"py-fast-...\" suitable for large output

See: large output makes Emacs freeze, lp:1253907

Results arrive in output buffer, which is not in comint-mode"

  :type 'boolean
  :tag "py-fast-process-p"
  :group 'python-mode)

(defcustom py-shift-require-transient-mark-mode-p t
 "If py-shift commands on regions should require variable ‘transient-mark-mode’.

Default is t"

:type 'boolean
:group 'python-mode)

(defvar py-fast-output-buffer "*Py-Fast-Output-Buffer*"
  "Default ‘buffer-name’ for fast-processes.")

(defvar py-this-result nil
  "Internally used, store return-value.")

(defcustom py-comment-auto-fill-p nil
  "When non-nil, fill comments.

Defaut is nil"

  :type 'boolean
  :group 'python-mode)

(defcustom py-sexp-use-expression-p nil
  "If non-nil, ‘forward-sexp’ will call ‘py-forward-expression’.

Respective ‘backward-sexp’ will call ‘py-backward-expression’
Default is t"
  :type 'boolean
  :group 'python-mode)

(defcustom py-session-p t
  "If commands would use an existing process.

See also `py-dedicated-process-p'"

  :type 'boolean
  :tag "py-session-p"
  :group 'python-mode)

(defcustom py-max-help-buffer-p nil
  "If \"\*Python-Help\*\"-buffer should appear as the only visible.

Default is nil.  In ‘help-buffer’, \"q\" will close it."

  :type 'boolean
  :tag "py-max-help-buffer-p"
  :group 'python-mode)

(defcustom py-highlight-error-source-p nil
  "Respective code in source-buffer will be highlighted.

Default is nil.

\\<python-mode-map> `py-remove-overlays-at-point' removes that highlighting."
  :type 'boolean
  :tag "py-highlight-error-source-p"
  :group 'python-mode)

(defcustom py-set-pager-cat-p nil
  "If the shell environment variable $PAGER should set to `cat'.

Avoids lp:783828,
 \"Terminal not fully functional\", for help('COMMAND') in python-shell

When non-nil, imports module `os'"

  :type 'boolean
  :tag "py-set-pager-cat-p"
  :group 'python-mode)

(defcustom py-empty-line-closes-p nil
  "When non-nil, dedent after empty line following block.

if True:
    print(\"Part of the if-statement\")

print(\"Not part of the if-statement\")

Default is nil"

  :type 'boolean
  :tag "py-empty-line-closes-p"
  :group 'python-mode)

(defcustom py-prompt-on-changed-p t
  "Ask for save before a changed buffer is sent to interpreter.

Default is t"

  :type 'boolean
  :tag "py-prompt-on-changed-p"
  :group 'python-mode)

(defcustom py-dedicated-process-p nil
  "If commands executing code use a dedicated shell.

Default is nil

When non-nil and `py-session-p', an existing dedicated process is re-used instead of default - which allows executing stuff in parallel."
  :type 'boolean
  :tag "py-dedicated-process-p"
  :group 'python-mode)

(defcustom py-store-result-p nil
  "Put resulting string of `py-execute-...' into ‘kill-ring’.

Default is nil"

  :type 'boolean
  :tag "py-dedicated-process-p"
  :group 'python-mode)

(defvar py-shell--font-lock-buffer " *PSFLB*"
  "May contain the `py-buffer-name' currently fontified." )

(defvar py-return-result-p t
  "Internally used.

When non-nil, return resulting string of `py-execute-...'.
Imports will use it with nil.
Default is t")

(defcustom py--execute-use-temp-file-p nil
 "Assume execution at a remote machine.

 where write-access is not given."

 :type 'boolean
 :group 'python-mode)

(defvar py--match-paren-forward-p nil
  "Internally used by `py-match-paren'.")

(defvar py-new-session-p t
  "Internally used.  See lp:1393882.

Restart ‘py-shell’ once with new Emacs/‘python-mode’.")

(defcustom py-electric-close-active-p nil
  "Close completion buffer if no longer needed.

Works around a bug in `choose-completion'.
Default is nil"
  :type 'boolean
  :group 'python-mode)

(defcustom py-update-gud-pdb-history-p t
  "If pdb should provide suggestions WRT file to check and ‘py-pdb-path’.

Default is t
See lp:963253"
  :type 'boolean
  :tag "py-update-gud-pdb-history-p"
  :group 'python-mode
  :tag "py-update-gud-pdb-history-p")

(defcustom py-pdb-executable nil
  "Indicate PATH/TO/pdb.

Default is nil
See lp:963253"
  :type 'string
  :tag "py-pdb-executable"
  :group 'python-mode
  :tag "py-pdb-executable")

(defcustom py-hide-show-minor-mode-p nil
  "If hide-show minor-mode should be on, default is nil."

  :type 'boolean
  :tag "py-hide-show-minor-mode-p"
  :group 'python-mode)

(defcustom py-load-skeletons-p nil
  "If skeleton definitions should be loaded, default is nil.

If non-nil and variable ‘abbrev-mode’ on, block-skeletons will inserted.
Pressing \"if<SPACE>\" for example will prompt for the if-condition."

  :type 'boolean
  :tag "py-load-skeletons-p"
  :group 'python-mode)

(defcustom py-if-name-main-permission-p t
  "Allow execution of code inside blocks started.

by \"if __name__== '__main__':\".
Default is non-nil"

  :type 'boolean
  :tag "py-if-name-main-permission-p"
  :group 'python-mode)

(defcustom py-use-font-lock-doc-face-p nil
  "If documention string inside of def or class get `font-lock-doc-face'.

`font-lock-doc-face' inherits `font-lock-string-face'.
Call \\<emacs-lisp-mode-map> \\[customize-face] in order to have a visible effect."

  :type 'boolean
  :tag "py-use-font-lock-doc-face-p"
  :group 'python-mode)

(defcustom py-empty-comment-line-separates-paragraph-p t
  "Consider paragraph start/end lines with nothing inside but comment sign.

Default is  non-nil"
  :type 'boolean
  :tag "py-empty-comment-line-separates-paragraph-p"
  :group 'python-mode)

(defcustom py-indent-honors-inline-comment nil
  "If non-nil, indents to column of inlined comment start.
Default is nil."
  :type 'boolean
  :tag "py-indent-honors-inline-comment"
  :group 'python-mode)

(defcustom py-auto-fill-mode nil
  "If ‘python-mode’ should set ‘fill-column’.

according to values
in `py-comment-fill-column' and `py-docstring-fill-column'.
Default is  nil"

  :type 'boolean
  :tag "py-auto-fill-mode"
  :group 'python-mode)

(defcustom py-error-markup-delay 4
  "Seconds error's are highlighted in exception buffer."

  :type 'integer
  :tag "py-error-markup-delay"
  :group 'python-mode)

(defcustom py-fast-completion-delay 0.1
  "Used by ‘py--fast-send-string-intern’."

  :type 'float
  :tag "py-fast-completion-delay"
  :group 'python-mode)

(defcustom py-new-shell-delay
    (if (eq system-type 'windows-nt)
      2.0
    1.0)

  "If a new comint buffer is connected to Python, commands like completion might need some delay."

  :type 'float
  :tag "py-new-shell-delay"
  :group 'python-mode)

(defcustom py-autofill-timer-delay 1
  "Delay when idle before functions ajusting  `py-docstring-fill-column', `py-comment-fill-column' are called."
  :type 'integer
  :tag "py-autofill-timer-delay"
  :group 'python-mode)

(defcustom py-docstring-fill-column 72
  "Value of `fill-column' to use when filling a docstring.
Any non-integer value means do not use a different value of
`fill-column' when filling docstrings."
  :type '(choice (integer)
                 (const :tag "Use the current `fill-column'" t))
  :tag "py-docstring-fill-column"
  :group 'python-mode)

(defcustom py-comment-fill-column 79
  "Value of `fill-column' to use when filling a comment.
Any non-integer value means do not use a different value of
`fill-column' when filling docstrings."
  :type '(choice (integer)
		 (const :tag "Use the current `fill-column'" t))
  :tag "py-comment-fill-column"
  :group 'python-mode)

(defcustom py-fontify-shell-buffer-p nil
  "If code in Python shell should be highlighted as in script buffer.

Default is nil.

If t, related vars like `comment-start' will be set too.
Seems convenient when playing with stuff in IPython shell
Might not be TRT when a lot of output arrives"

  :type 'boolean
  :tag "py-fontify-shell-buffer-p"
  :group 'python-mode)

(defcustom py-modeline-display-full-path-p nil
  "If the full PATH/TO/PYTHON should be displayed in shell modeline.

Default is nil.  Note: when `py-shell-name' is specified with path, it's shown as an acronym in ‘buffer-name’ already."

  :type 'boolean
  :tag "py-modeline-display-full-path-p"
  :group 'python-mode)

(defcustom py-modeline-acronym-display-home-p nil
  "If the modeline acronym should contain chars indicating the home-directory.

Default is nil"
  :type 'boolean
  :tag "py-modeline-acronym-display-home-p"
  :group 'python-mode)

(defun py-smart-operator-check ()
  "Check, if ‘smart-operator-mode’ is loaded resp. available.

Give some hints, if not."
  (interactive)
  (if (featurep 'smart-operator)
      't
    (progn
      (and (boundp 'py-smart-operator-mode-p) py-smart-operator-mode-p (message "%s" "Don't see smart-operator.el. Make sure, it's installed. See in menu Options, Manage Emacs Packages. Or get it from source: URL: http://xwl.appspot.com/ref/smart-operator.el")
           nil))))

(defun py-autopair-check ()
  "Check, if ‘autopair-mode’ is available.

Give some hints, if not."
  (interactive)
  (if (featurep 'autopair)
      't
    (progn
      (message "py-autopair-check: %s" "Don't see autopair.el. Make sure, it's installed. If not, maybe see source: URL: http://autopair.googlecode.com")
      nil)))

(defvar smart-operator-mode nil)
(defvar highlight-indent-active nil)
(defvar autopair-mode nil)

(defvar-local py-edit-docstring-orig-pos nil
  "Internally used by `py-edit-docstring'.")

(defvar-local py--docbeg nil
  "Internally used by `py-edit-docstring'")

(defvar-local py--docend nil
  "Internally used by `py-edit-docstring'")

(defvar py--oldbuf nil
  "Internally used by `py-edit-docstring'.")

(defvar py-edit-docstring-buffer "Edit docstring"
  "Name of the temporary buffer to use when editing.")

(defvar py--edit-docstring-register nil)

(defvar py-result nil
  "Internally used.  May store result from Python process.")

(defvar py-error nil
  "Internally used.  Takes the error-messages from Python process.")

(defvar py-python-completions "*Python Completions*"
  "Buffer name for Python-shell completions, internally used.")

(defvar py-ipython-completions "*IPython Completions*"
  "Buffer name for IPython-shell completions, internally used.")

(defcustom py-timer-close-completions-p t
  "If `py-timer-close-completion-buffer' should run, default is non-nil."

  :type 'boolean
  :tag "py-timer-close-completions-p"
  :group 'python-mode)

(defcustom py-smart-operator-mode-p nil
  "If ‘python-mode’ calls smart-operator-mode-on.

Default is nil."

  :type 'boolean
  :tag "py-smart-operator-mode-p"
  :group 'python-mode)

(defcustom py-autopair-mode nil
  "If ‘python-mode’ calls (autopair-mode-on)

Default is nil
Load `autopair-mode' written by Joao Tavora <joaotavora [at] gmail.com>
URL: http://autopair.googlecode.com"
  :type 'boolean
  :tag "py-autopair-mode"
  :group 'python-mode)

(defcustom py-indent-no-completion-p nil
  "If completion function should insert a TAB when no completion found.

Default is nil"
  :type 'boolean
  :tag "py-indent-no-completion-p"
  :group 'python-mode)

(defcustom py-company-pycomplete-p nil
  "Load company-pycomplete stuff.  Default is  nil."

  :type 'boolean
  :tag "py-company-pycomplete-p"
  :group 'python-mode)

(defvar py-last-position nil
    "Used by ‘py-help-at-point’.

Avoid repeated call at identic pos.")

(defvar py-auto-completion-mode-p nil
  "Internally used by `py-auto-completion-mode'.")

(defvar py-complete-last-modified nil
  "Internally used by `py-auto-completion-mode'.")

(defvar py--auto-complete-timer nil
  "Internally used by `py-auto-completion-mode'.")

(defvar py-auto-completion-buffer nil
  "Internally used by `py-auto-completion-mode'.")

(defvar py--auto-complete-timer-delay 1
  "Seconds Emacs must be idle to trigger auto-completion.

See `py-auto-completion-mode'")

(defcustom py-auto-complete-p nil
  "Run python-mode's built-in auto-completion via ‘py-complete-function’.  Default is  nil."

  :type 'boolean
  :tag "py-auto-complete-p"
  :group 'python-mode)
(make-variable-buffer-local 'py-auto-complete-p)

(defcustom py-tab-shifts-region-p nil
  "If t, TAB will indent/cycle the region, not just the current line.

Default is  nil
See also `py-tab-indents-region-p'"

  :type 'boolean
  :tag "py-tab-shifts-region-p"
  :group 'python-mode)

(defcustom py-tab-indents-region-p nil
  "When t and first TAB doesn't shift, ‘indent-region’ is called.

Default is  nil
See also `py-tab-shifts-region-p'"

  :type 'boolean
  :tag "py-tab-indents-region-p"
  :group 'python-mode)

(defcustom py-block-comment-prefix-p t
  "If py-comment inserts ‘py-block-comment-prefix’.

Default is t"

  :type 'boolean
  :tag "py-block-comment-prefix-p"
  :group 'python-mode)

(defcustom py-org-cycle-p nil
  "When non-nil, command `org-cycle' is available at shift-TAB, <backtab>.

Default is nil."

  :type 'boolean
  :tag "py-org-cycle-p"
  :group 'python-mode)

(defcustom py-set-complete-keymap-p  nil
  "If `py-complete-initialize'.

Sets up enviroment for Pymacs based py-complete.
 Should load it's keys into `python-mode-map'
Default is nil.
See also resp. edit `py-complete-set-keymap'"

  :type 'boolean
  :tag "py-set-complete-keymap-p"
  :group 'python-mode)

(defcustom py-outline-minor-mode-p t
  "If outline minor-mode should be on, default is t."

  :type 'boolean
  :tag "py-outline-minor-mode-p"
  :group 'python-mode)

(defcustom py-guess-py-install-directory-p t
  "If in cases, `py-install-directory' isn't set,  `py-set-load-path'should guess it from variable `buffer-file-name'."

  :type 'boolean
  :tag "py-guess-py-install-directory-p"
  :group 'python-mode)

(defcustom py-load-pymacs-p nil
  "If Pymacs related stuff should be loaded.

Default is nil.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.ca"

  :type 'boolean
  :tag "py-load-pymacs-p"
  :group 'python-mode)

(defcustom py-verbose-p nil
  "If functions should report results.

Default is nil."

  :type 'boolean
  :tag "py-verbose-p"
  :group 'python-mode)

(defcustom py-sexp-function nil
  "Called instead of `forward-sexp', `backward-sexp'.

Default is nil."

  :type '(choice

          (const :tag "default" nil)
          (const :tag "py-end-of-partial-expression" py-end-of-partial-expression)
          (const :tag "py-end-of-expression" py-end-of-expression))
  :tag "py-sexp-function"
  :group 'python-mode)

(defcustom py-close-provides-newline t
  "If a newline is inserted, when line after block isn't empty.

Default is non-nil.
When non-nil, `py-end-of-def' and related will work faster"
  :type 'boolean
  :tag "py-close-provides-newline"
  :group 'python-mode)

(defcustom py-dedent-keep-relative-column t
  "If point should follow dedent or kind of electric move to end of line.  Default is t - keep relative position."
  :type 'boolean
  :tag "py-dedent-keep-relative-column"
  :group 'python-mode)

(defcustom py-indent-honors-multiline-listing nil
  "If t, indents to 1+ column of opening delimiter.  If nil, indent adds one level to the beginning of statement.  Default is nil."
  :type 'boolean
  :tag "py-indent-honors-multiline-listing"
  :group 'python-mode)

(defcustom py-indent-paren-spanned-multilines-p t
  "If non-nil, indents elements of list to first element.

def foo():
    if (foo &&
            baz):
        bar()

If nil line up with first element:

def foo():
    if (foo &&
        baz):
        bar()

Default is t"
  :type 'boolean
  :tag "py-indent-paren-spanned-multilines-p"
  :group 'python-mode)

(defcustom py-closing-list-dedents-bos nil
  "When non-nil, indent list's closing delimiter like start-column.

It will be lined up under the first character of
 the line that starts the multi-line construct, as in:

my_list = [
    1, 2, 3,
    4, 5, 6
]

result = some_function_that_takes_arguments(
    'a', 'b', 'c',
    'd', 'e', 'f'
)

Default is nil, i.e.

my_list = [
    1, 2, 3,
    4, 5, 6
    ]
result = some_function_that_takes_arguments(
    'a', 'b', 'c',
    'd', 'e', 'f'
    )

Examples from PEP8
URL: https://www.python.org/dev/peps/pep-0008/#indentation"

  :type 'boolean
  :tag "py-closing-list-dedents-bos"
  :group 'python-mode)

(defvar py-imenu-max-items 99)
(defcustom py-imenu-max-items 99
 "Python-mode specific `imenu-max-items'."

:type 'number
:group 'python-mode)

(defcustom py-closing-list-space 1
  "Number of chars, closing parenthesis outdent from opening, default is 1."
  :type 'number
  :tag "py-closing-list-space"
  :group 'python-mode)

(defcustom py-max-specpdl-size 99
  "Heuristic exit.
e
Limiting number of recursive calls by ‘py-forward-statement’ and related.
Default is ‘max-specpdl-size’.

This threshold is just an approximation.  It might set far higher maybe.

See lp:1235375. In case code is not to navigate due to errors, variable `which-function-mode' and others might make Emacs hang.  Rather exit than."

  :type 'number
  :tag "py-max-specpdl-size"
  :group 'python-mode)

(defcustom py-closing-list-keeps-space nil
  "If non-nil, closing parenthesis dedents onto column of opening plus `py-closing-list-space', default is nil."
  :type 'boolean
  :tag "py-closing-list-keeps-space"
  :group 'python-mode)

(defcustom py-electric-kill-backward-p nil
  "Affects `py-electric-backspace'.  Default is nil.

If behind a delimited form of braces, brackets or parentheses,
backspace will kill it's contents

With when cursor after
my_string[0:1]
--------------^

==>

my_string[]
----------^

In result cursor is insided emptied delimited form."

  :type 'boolean
  :tag "py-electric-kill-backward-p"
  :group 'python-mode)

(defcustom py-electric-colon-active-p nil
  "`py-electric-colon' feature.

Default is nil.  See lp:837065 for discussions.
See also `py-electric-colon-bobl-only'"
  :type 'boolean
  :tag "py-electric-colon-active-p"
  :group 'python-mode)

(defcustom py-electric-colon-bobl-only t

  "When inserting a colon, do not indent lines unless at beginning of block.

See lp:1207405 resp. `py-electric-colon-active-p'"

  :type 'boolean
  :tag "py-electric-colon-bobl-only"
  :group 'python-mode)

(defcustom py-electric-yank-active-p nil
  "When non-nil, `yank' will be followed by an `indent-according-to-mode'.

Default is nil"
  :type 'boolean
  :tag "py-electric-yank-active-p"
  :group 'python-mode)

(defcustom py-electric-colon-greedy-p nil
  "If ‘py-electric-colon’ should indent to the outmost reasonable level.

If nil, default, it will not move from at any reasonable level."
  :type 'boolean
  :tag "py-electric-colon-greedy-p"
  :group 'python-mode)

(defcustom py-electric-colon-newline-and-indent-p nil
  "If non-nil, `py-electric-colon' will call `newline-and-indent'.  Default is nil."
  :type 'boolean
  :tag "py-electric-colon-newline-and-indent-p"
  :group 'python-mode)

(defcustom py-electric-comment-p nil
  "If \"#\" should call `py-electric-comment'. Default is nil."
  :type 'boolean
  :tag "py-electric-comment-p"
  :group 'python-mode)

(defcustom py-electric-comment-add-space-p nil
  "If ‘py-electric-comment’ should add a space.  Default is nil."
  :type 'boolean
  :tag "py-electric-comment-add-space-p"
  :group 'python-mode)

(defcustom py-mark-decorators nil
  "If ‘py-mark-def-or-class’ functions should mark decorators too.  Default is nil."
  :type 'boolean
  :tag "py-mark-decorators"
  :group 'python-mode)

(defcustom py-defun-use-top-level-p nil
 "If ‘beginning-of-defun’, ‘end-of-defun’ calls function ‘top-level’ form.

Default is nil.

beginning-of defun, ‘end-of-defun’ forms use
commands `py-beginning-of-top-level', `py-end-of-top-level'

‘mark-defun’ marks function ‘top-level’ form at point etc."

 :type 'boolean
  :tag "py-defun-use-top-level-p"
 :group 'python-mode)

(defcustom py-tab-indent t
  "Non-nil means TAB in Python mode calls `py-indent-line'."
  :type 'boolean
  :tag "py-tab-indent"
  :group 'python-mode)

(defcustom py-return-key 'newline
  "Which command <return> should call."
  :type '(choice

          (const :tag "default" py-newline-and-indent)
          (const :tag "newline" newline)
          (const :tag "py-newline-and-indent" py-newline-and-indent)
          (const :tag "py-newline-and-dedent" py-newline-and-dedent)
          )
  :tag "py-return-key"
  :group 'python-mode)

(defcustom py-complete-function 'py-fast-complete
  "When set, enforces function todo completion, default is `py-fast-complete'.

Might not affect IPython, as `py-shell-complete' is the only known working here.
Normally ‘python-mode’ knows best which function to use."
  :type '(choice

          (const :tag "default" nil)
          (const :tag "Pymacs and company based py-complete" py-complete)
          (const :tag "py-shell-complete" py-shell-complete)
          (const :tag "py-indent-or-complete" py-indent-or-complete)
	  (const :tag "py-fast-complete" py-fast-complete)
          )
  :tag "py-complete-function"
  :group 'python-mode)

(defcustom py-encoding-string " # -*- coding: utf-8 -*-"
  "Default string specifying encoding of a Python file."
  :type 'string
  :tag "py-encoding-string"
  :group 'python-mode)

(defcustom py-shebang-startstring "#! /bin/env"
  "Detecting the shell in head of file."
  :type 'string
  :tag "py-shebang-startstring"
  :group 'python-mode)

(defcustom py-flake8-command ""
  "Which command to call flake8.

If empty, ‘python-mode’ will guess some"
  :type 'string
  :tag "py-flake8-command"
  :group 'python-mode)

(defcustom py-flake8-command-args ""
  "Arguments used by flake8.

Default is the empty string."
  :type 'string
  :tag "py-flake8-command-args"
  :group 'python-mode)

(defvar py-flake8-history nil
  "Used by flake8, resp. ‘py-flake8-command’.

Default is nil.")

(defcustom py-message-executing-temporary-file t
  "If execute functions using a temporary file should message it.

Default is t.
Messaging increments the prompt counter of IPython shell."
  :type 'boolean
  :tag "py-message-executing-temporary-file"
  :group 'python-mode)

(defcustom py-execute-no-temp-p nil
  "Seems Emacs-24.3 provided a way executing stuff without temporary files."
  :type 'boolean
  :tag "py-execute-no-temp-p"
  :group 'python-mode)

(defcustom py-lhs-inbound-indent 1
  "When line starts a multiline-assignment: How many colums indent should be more than opening bracket, brace or parenthesis."
  :type 'integer
  :tag "py-lhs-inbound-indent"
  :group 'python-mode)

(defcustom py-continuation-offset 2
  "Additional amount of offset to give for some continuation lines.
Continuation lines are those that immediately follow a backslash
terminated line."
  :type 'integer
  :tag "py-continuation-offset"
  :group 'python-mode)

(defcustom py-indent-tabs-mode nil
  "Python-mode starts `indent-tabs-mode' with the value specified here, default is nil."
  :type 'boolean
  :tag "py-indent-tabs-mode"
  :group 'python-mode)

(defcustom py-smart-indentation nil
  "Guess `py-indent-offset'.  Default is nil.

Setting it to t seems useful only in cases where customizing
`py-indent-offset' is no option - for example because the
indentation step is unknown or differs inside the code.

When this variable is non-nil, `py-indent-offset' is guessed from existing code in the buffer, which might slow down the proceeding."

  :type 'boolean
  :tag "py-smart-indentation"
  :group 'python-mode)

(defcustom py-block-comment-prefix "##"
  "String used by \\[comment-region] to comment out a block of code.
This should follow the convention for non-indenting comment lines so
that the indentation commands won't get confused (i.e., the string
should be of the form `#x...' where `x' is not a blank or a tab, and
 `...' is arbitrary).  However, this string should not end in whitespace."
  :type 'string
  :tag "py-block-comment-prefix"
  :group 'python-mode)

(defcustom py-indent-offset 4
  "Amount of offset per level of indentation.
`\\[py-guess-indent-offset]' can usually guess a good value when
you're editing someone else's Python code."
  :type 'integer
  :tag "py-indent-offset"
  :group 'python-mode)
(make-variable-buffer-local 'py-indent-offset)

(defcustom py-backslashed-lines-indent-offset 5
  "Amount of offset per level of indentation of backslashed.
No semantic indent,  which diff to `py-indent-offset' indicates"
  :type 'integer
  :tag "py-backslashed-lines-indent-offset"
  :group 'python-mode)

(defcustom py-pdb-path
  (if (or (eq system-type 'ms-dos)(eq system-type 'windows-nt))
      (quote c:/python27/python\ -i\ c:/python27/Lib/pdb.py)
    '/usr/lib/python2.7/pdb.py)
  "Where to find pdb.py.  Edit this according to your system.

If you ignore the location `M-x py-guess-pdb-path' might display it."
  :type 'variable
  :tag "py-pdb-path"
  :group 'python-mode)

(defvar py-python-ms-pdb-command ""
  "MS-systems might use that.")

(defcustom py-indent-comments t
  "When t, comment lines are indented."
  :type 'boolean
  :tag "py-indent-comments"
  :group 'python-mode)

(defcustom py-uncomment-indents-p nil
  "When non-nil, after uncomment indent lines."
  :type 'boolean
  :tag "py-uncomment-indents-p"
  :group 'python-mode)

(defcustom py-separator-char 47
  "The character, which separates the system file-path components.

Precedes guessing when not empty, returned by function `py-separator-char'."
  :type 'character
  :tag "py-separator-char"
  :group 'python-mode)

(and
 ;; used as a string finally
 ;; kept a character not to break existing customizations
 (characterp py-separator-char)(setq py-separator-char (char-to-string py-separator-char)))

(defcustom py-custom-temp-directory ""
  "If set, will take precedence over guessed values from `py-temp-directory'.  Default is the empty string."
  :type 'string
  :tag "py-custom-temp-directory"
  :group 'python-mode)

(defcustom py-beep-if-tab-change t
  "Ring the bell if `tab-width' is changed.
If a comment of the form

                           \t# vi:set tabsize=<number>:

is found before the first code line when the file is entered, and the
current value of (the general Emacs variable) `tab-width' does not
equal <number>, `tab-width' is set to <number>, a message saying so is
displayed in the echo area, and if `py-beep-if-tab-change' is non-nil
the Emacs bell is also rung as a warning."
  :type 'boolean
  :tag "py-beep-if-tab-change"
  :group 'python-mode)

(defcustom py-jump-on-exception t
  "Jump to innermost exception frame in Python output buffer.
When this variable is non-nil and an exception occurs when running
Python code synchronously in a subprocess, jump immediately to the
source code of the innermost traceback frame."
  :type 'boolean
  :tag "py-jump-on-exception"
  :group 'python-mode)

(defcustom py-ask-about-save t
  "If not nil, ask about which buffers to save before executing some code.
Otherwise, all modified buffers are saved without asking."
  :type 'boolean
  :tag "py-ask-about-save"
  :group 'python-mode)

(defcustom py-delete-function 'delete-char
  "Function called by `py-electric-delete' when deleting forwards."
  :type 'function
  :tag "py-delete-function"
  :group 'python-mode)

(defcustom py-pdbtrack-do-tracking-p t
  "Controls whether the pdbtrack feature is enabled or not.
When non-nil, pdbtrack is enabled in all comint-based buffers,
e.g. shell buffers and the *Python* buffer.  When using pdb to debug a
Python program, pdbtrack notices the pdb prompt and displays the
source file and line that the program is stopped at, much the same way
as ‘gud-mode’ does for debugging C programs with gdb."
  :type 'boolean
  :tag "py-pdbtrack-do-tracking-p"
  :group 'python-mode)
(make-variable-buffer-local 'py-pdbtrack-do-tracking-p)

(defcustom py-pdbtrack-filename-mapping nil
  "Supports mapping file paths when opening file buffers in pdbtrack.
When non-nil this is an alist mapping paths in the Python interpreter
to paths in Emacs."
  :type 'alist
  :tag "py-pdbtrack-filename-mapping"
  :group 'python-mode)

(defcustom py-pdbtrack-minor-mode-string " PDB"
  "String to use in the minor mode list when pdbtrack is enabled."
  :type 'string
  :tag "py-pdbtrack-minor-mode-string"
  :group 'python-mode)

(defcustom py-import-check-point-max
  20000
  "Max number of characters to search Java-ish import statement.

When `python-mode' tries to calculate the shell
-- either a CPython or a Jython shell --
it looks at the so-called `shebang'.
If that's not available, it looks at some of the
file heading imports to see if they look Java-like."
  :type 'integer
  :tag "py-import-check-point-max
"
  :group 'python-mode)

(defcustom py-jython-packages
  '("java" "javax")
  "Imported packages that imply `jython-mode'."
  :type '(repeat string)
  :tag "py-jython-packages
"
  :group 'python-mode)

(defcustom py-current-defun-show t
  "If `py-current-defun' should jump to the definition.

Highlights it while waiting PY-WHICH-FUNC-DELAY seconds.
Afterwards returning to previous position.

Default is t."

  :type 'boolean
  :tag "py-current-defun-show"
  :group 'python-mode)

(defcustom py-current-defun-delay 2
  "When called interactively, `py-current-defun' should wait PY-WHICH-FUNC-DELAY seconds at the definition name found, before returning to previous position."

  :type 'number
  :tag "py-current-defun-delay"
  :group 'python-mode)

(defcustom py--delete-temp-file-delay 1
  "Used by `py--delete-temp-file'."

  :type 'number
  :tag "py--delete-temp-file-delay"
  :group 'python-mode)

(defcustom py-python-send-delay 5
  "Seconds to wait for output, used by `py--send-...' functions.

See also ‘py-ipython-send-delay’"

  :type 'number
  :tag "py-python-send-delay"
  :group 'python-mode)

(defcustom py-ipython-send-delay 9
  "Seconds to wait for output, used by `py--send-...' functions.

See also ‘py-python-send-delay’"

  :type 'number
  :tag "py-ipython-send-delay"
  :group 'python-mode)

(defcustom py-master-file nil
  "Execute the named master file instead of the buffer's file.

Default is nil.
With relative path variable `default-directory' is prepended.

Beside you may set this variable in the file's local
variable section, e.g.:

                           # Local Variables:
                           # py-master-file: \"master.py\"
                           # End:"
  :type 'string
  :tag "py-master-file"
  :group 'python-mode)
(make-variable-buffer-local 'py-master-file)

(defcustom py-pychecker-command "pychecker"
  "Shell command used to run Pychecker."
  :type 'string
  :tag "py-pychecker-command"
  :group 'python-mode)

(defcustom py-pychecker-command-args "--stdlib"
  "String arguments to be passed to pychecker."
  :type 'string
  :tag "py-pychecker-command-args"
  :group 'python-mode)

(defcustom py-pyflakes-command "pyflakes"
  "Shell command used to run Pyflakes."
  :type 'string
  :tag "py-pyflakes-command"
  :group 'python-mode)

(defcustom py-pyflakes-command-args ""
  "String arguments to be passed to pyflakes.

Default is \"\""
  :type 'string
  :tag "py-pyflakes-command-args"
  :group 'python-mode)

(defcustom py-pep8-command "pep8"
  "Shell command used to run pep8."
  :type 'string
  :tag "py-pep8-command"
  :group 'python-mode)

(defcustom py-pep8-command-args ""
  "String arguments to be passed to pylint.

Default is \"\""
  :type 'string
  :tag "py-pep8-command-args"
  :group 'python-mode)

(defcustom py-pyflakespep8-command (concat py-install-directory "/pyflakespep8.py")
  "Shell command used to run `pyflakespep8'."
  :type 'string
  :tag "py-pyflakespep8-command"
  :group 'python-mode)

(defcustom py-pyflakespep8-command-args ""
  "String arguments to be passed to pyflakespep8.

Default is \"\""
  :type 'string
  :tag "py-pyflakespep8-command-args"
  :group 'python-mode)

(defcustom py-pylint-command "pylint"
  "Shell command used to run Pylint."
  :type 'string
  :tag "py-pylint-command"
  :group 'python-mode)

(defcustom py-pylint-command-args '("--errors-only")
  "String arguments to be passed to pylint.

Default is \"--errors-only\""
  :type '(repeat string)
  :tag "py-pylint-command-args"
  :group 'python-mode)

(defcustom py-shell-input-prompt-1-regexp ">>> "
  "A regular expression to match the input prompt of the shell."
  :type 'regexp
  :tag "py-shell-input-prompt-1-regexp"
  :group 'python-mode)

(defcustom py-shell-input-prompt-2-regexp "[.][.][.] "
  "A regular expression to match the input prompt.

Applies to the shell after the first line of input."
  :type 'string
  :tag "py-shell-input-prompt-2-regexp"
  :group 'python-mode)

(defcustom py-shell-prompt-read-only t
  "If non-nil, the python prompt is read only.

Setting this variable will only effect new shells."
  :type 'boolean
  :tag "py-shell-prompt-read-only"
  :group 'python-mode)

(defcustom py-honor-IPYTHONDIR-p nil
  "When non-nil ipython-history file is constructed by $IPYTHONDIR.

Default is nil.
Otherwise value of ‘py-ipython-history’ is used."
  :type 'boolean
  :tag "py-honor-IPYTHONDIR-p"
  :group 'python-mode)

(defcustom py-ipython-history "~/.ipython/history"
  "Ipython-history default file.

Used when ‘py-honor-IPYTHONDIR-p’ is nil - th default"

  :type 'string
  :tag "py-ipython-history"
  :group 'python-mode)

(defcustom py-honor-PYTHONHISTORY-p nil
  "When non-nil python-history file is set by $PYTHONHISTORY.

Default is nil.
Otherwise value of ‘py-python-history’ is used."
  :type 'boolean
  :tag "py-honor-PYTHONHISTORY-p"
  :group 'python-mode)

(defcustom py-python-history "~/.python_history"
  "Python-history default file. Used when ‘py-honor-PYTHONHISTORY-p’ is nil (default)."

  :type 'string
  :tag "py-python-history"
  :group 'python-mode)

(defcustom py-switch-buffers-on-execute-p nil
  "When non-nil switch to the Python output buffer.

If `py-keep-windows-configuration' is t, this will take precedence over setting here."

  :type 'boolean
  :tag "py-switch-buffers-on-execute-p"
  :group 'python-mode)

(defcustom py-split-window-on-execute 'just-two
  "When non-nil split windows.

Default is just-two - when code is send to interpreter.
Splits screen into source-code buffer and current ‘py-shell’ result.
Other buffer will be hidden that way.

When set to t, ‘python-mode’ tries to reuse existing windows
and will split only if needed.

With 'always, results will displayed in a new window.

Both t and `always' is experimental still.

For the moment: If a multitude of python-shells/buffers should be
visible, open them manually and set `py-keep-windows-configuration' to t.

See also `py-keep-windows-configuration'"
  :type '(choice

          (const :tag "default" just-two)
	  (const :tag "reuse" t)
          (const :tag "no split" nil)
	  (const :tag "just-two" just-two)
          (const :tag "always" always))
  :tag "py-split-window-on-execute"
  :group 'python-mode)

(defcustom py-split-window-on-execute-threshold 3
  "Maximal number of displayed windows.

Honored, when `py-split-window-on-execute' is t, i.e. \"reuse\".
Don't split when max number of displayed windows is reached."
  :type 'number
  :tag "py-split-window-on-execute-threshold"
  :group 'python-mode)

(defcustom py-split-windows-on-execute-function 'split-window-vertically
  "How window should get splitted to display results of py-execute-... functions."
  :type '(choice (const :tag "split-window-vertically" split-window-vertically)
                 (const :tag "split-window-horizontally" split-window-horizontally)
                 )
  :tag "py-split-windows-on-execute-function"
  :group 'python-mode)

(defcustom py-shell-fontify-style nil
  "Fontify current input resp. output in Python shell. Default is nil.

INPUT will leave output unfontified.
ALL keeps output fontified.

At any case only current input gets fontified."
  :type '(choice (const :tag "Default" all)
                 (const :tag "Input" input)
		 (const :tag "Nil" nil)
                 )
  :tag "py-shell-fontify-style"
  :group 'python-mode)

(defcustom py-hide-show-keywords
  '("class"    "def"    "elif"    "else"    "except"
    "for"      "if"     "while"   "finally" "try"
    "with")
  "Keywords composing visible heads."
  :type '(repeat string)
  :tag "py-hide-show-keywords
"
  :group 'python-mode)

(defcustom py-hide-show-hide-docstrings t
  "Controls if doc strings can be hidden by hide-show."
  :type 'boolean
  :tag "py-hide-show-hide-docstrings"
  :group 'python-mode)

(defcustom py-hide-comments-when-hiding-all t
  "Hide the comments too when you do an `hs-hide-all'."
  :type 'boolean
  :tag "py-hide-comments-when-hiding-all"
  :group 'python-mode)

(defcustom py-outline-mode-keywords
  '("class"    "def"    "elif"    "else"    "except"
    "for"      "if"     "while"   "finally" "try"
    "with")
  "Keywords composing visible heads."
  :type '(repeat string)
  :tag "py-outline-mode-keywords
"
  :group 'python-mode)

(defcustom python-mode-hook nil
  "Hook run when entering Python mode."

  :type 'hook
  :tag "python-mode-hook"
  :group 'python-mode
  )

(defcustom py-shell-name
  (if (eq system-type 'windows-nt)
      "C:/Python27/python"
    ;; "python"
    "python")

  "A PATH/TO/EXECUTABLE or default value `py-shell' may look for.

If no shell is specified by command.

On Windows default is C:/Python27/python
--there is no garantee it exists, please check your system--

Else python"
  :type 'string
  :tag "py-shell-name
"
  :group 'python-mode)

(defvar py-default-interpreter py-shell-name)

(defvar py-tempfile nil
  "Internally used.")

(defvar py-named-shells (list 'ipython 'ipython-dedicated 'ipython-no-switch 'ipython-switch 'ipython-switch-dedicated 'ipython2.7 'ipython2.7-dedicated 'ipython2.7-no-switch 'ipython2.7-switch 'ipython2.7-switch-dedicated 'ipython3 'ipython3-dedicated 'ipython3-no-switch 'ipython3-switch 'ipython3-switch-dedicated 'jython 'jython-dedicated 'jython-no-switch 'jython-switch 'jython-switch-dedicated 'python 'python-dedicated 'python-no-switch 'python-switch 'python-switch-dedicated 'python2 'python2-dedicated 'python2-no-switch 'python2-switch 'python2-switch-dedicated 'python3 'python3-dedicated 'python3-no-switch 'python3-switch 'python3-switch-dedicated))

(defcustom py-python-command
  (if (eq system-type 'windows-nt)
      ;; "C:\\Python27\\python.exe"
      "python"
   ;; "C:/Python33/Lib/site-packages/IPython"
    "python")

  "Make sure directory in in the PATH-variable.

Windows: edit in \"Advanced System Settings/Environment Variables\"
Commonly \"C:\\\\Python27\\\\python.exe\"
With Anaconda for example the following works here:
\"C:\\\\Users\\\\My-User-Name\\\\Anaconda\\\\Scripts\\\\python.exe\"

Else /usr/bin/python"

  :type 'string
  :tag "py-python-command
"
  :group 'python-mode)

(defcustom py-python-command-args '("-i")
  "String arguments to be used when starting a Python shell."
  :type 'string
  :tag "py-python-command-args"
  :group 'python-mode)

(defcustom py-python2-command
  (if (eq system-type 'windows-nt)
      "C:\\Python27\\python"
    ;; "python2"
    "python2")

  "Make sure, the directory where python.exe resides in in the PATH-variable.

Windows: If needed, edit in
\"Advanced System Settings/Environment Variables\"
Commonly
\"C:\\\\Python27\\\\python.exe\"
With Anaconda for example the following works here:
\"C:\\\\Users\\\\My-User-Name\\\\Anaconda\\\\Scripts\\\\python.exe\"

Else /usr/bin/python"

  :type 'string
  :tag "py-python2-command
"
  :group 'python-mode)

(defcustom py-python2-command-args '("-i")
  "String arguments to be used when starting a Python shell."
  :type '(repeat string)
  :tag "py-python2-command-args"
  :group 'python-mode)

;; "/usr/bin/python3"
(defcustom py-python3-command
  (if (eq system-type 'windows-nt)
    "C:/Python33/python"
    "python3")

  "A PATH/TO/EXECUTABLE or default value `py-shell' may look for.

Unless shell is specified by command.

On Windows see C:/Python3/python.exe
--there is no garantee it exists, please check your system--

At GNU systems see /usr/bin/python3"

  :type 'string
  :tag "py-python3-command
"
  :group 'python-mode)

(defcustom py-python3-command-args '("-i")
  "String arguments to be used when starting a Python3 shell."
  :type '(repeat string)
  :tag "py-python3-command-args"
  :group 'python-mode)

(defcustom py-ipython-command
  (if (eq system-type 'windows-nt)
      ;; "ipython"
    "C:\\Python27\\python"
    ;; "C:/Python33/Lib/site-packages/IPython"
    ;; "/usr/bin/ipython"
    "ipython")

  "A PATH/TO/EXECUTABLE or default value.

`M-x IPython RET' may look for,
Unless IPython-shell is specified by command.

On Windows default is \"C:\\\\Python27\\\\python.exe\"
While with Anaconda for example the following works here:
\"C:\\\\Users\\\\My-User-Name\\\\Anaconda\\\\Scripts\\\\ipython.exe\"

Else /usr/bin/ipython"

  :type 'string
  :tag "py-ipython-command
"
  :group 'python-mode)

(defcustom py-ipython-command-args
  (if (eq system-type 'windows-nt)
      "-i C:\\Python27\\Scripts\\ipython-script.py"
    "--pylab --automagic")
  "String arguments to be used when starting a Python shell.

At Windows make sure ipython-script.py is PATH.
Also setting PATH/TO/SCRIPT here should work, for example;
C:\\Python27\\Scripts\\ipython-script.py
With Anaconda the following is known to work:
\"C:\\\\Users\\\\My-User-Name\\\\Anaconda\\\\Scripts\\\\ipython-script-py\""
  :type 'string
  :tag "py-ipython-command-args
"
  :group 'python-mode)

(defcustom py-jython-command
  (if (eq system-type 'windows-nt)
      "jython"
    "/usr/bin/jython")

  "A PATH/TO/EXECUTABLE or default value.
`M-x Jython RET' may look for, if no Jython-shell is specified by command.

Not known to work at windows
Default /usr/bin/jython"

  :type 'string
  :tag "py-jython-command
"
  :group 'python-mode)

(defcustom py-jython-command-args ""
  "String arguments to be used when starting a Python shell."
  :type 'string
  :tag "py-jython-command-args"
  :group 'python-mode)

(defcustom py-shell-toggle-1 py-python2-command
  "A PATH/TO/EXECUTABLE or default value used by `py-toggle-shell'."
  :type 'string
  :tag "py-shell-toggle-1"
  :group 'python-mode)

(defcustom py-shell-toggle-2 py-python3-command
  "A PATH/TO/EXECUTABLE or default value used by `py-toggle-shell'."
  :type 'string
  :tag "py-shell-toggle-2"
  :group 'python-mode)

(defcustom py--imenu-create-index-p nil
  "Non-nil means Python mode creates and displays an index menu of functions and global variables."
  :type 'boolean
  :tag "py--imenu-create-index-p"
  :group 'python-mode)

(defvar py-history-filter-regexp "\\`\\s-*\\S-?\\S-?\\s-*\\'\\|'''/tmp/"
  "Input matching this regexp is not saved on the history list.
Default ignores all inputs of 0, 1, or 2 non-blank characters.")

(defcustom py-match-paren-mode nil
  "Non-nil means, cursor will jump to beginning or end of a block.
This vice versa, to beginning first.
Sets `py-match-paren-key' in ‘python-mode-map’.
Customize `py-match-paren-key' which key to use."
  :type 'boolean
  :tag "py-match-paren-mode"
  :group 'python-mode)

(defcustom py-match-paren-key "%"
  "String used by \\[comment-region] to comment out a block of code.
This should follow the convention for non-indenting comment lines so
that the indentation commands won't get confused (i.e., the string
should be of the form `#x...' where `x' is not a blank or a tab, and
                               `...' is arbitrary).  However, this string should not end in whitespace."
  :type 'string
  :tag "py-match-paren-key"
  :group 'python-mode)

(defcustom py-kill-empty-line t
  "If t, ‘py-indent-forward-line’ kills empty lines."
  :type 'boolean
  :tag "py-kill-empty-line"
  :group 'python-mode)

(defcustom py-imenu-show-method-args-p nil
  "Controls echoing of arguments of functions & methods in the Imenu buffer.
When non-nil, arguments are printed."
  :type 'boolean
  :tag "py-imenu-show-method-args-p"
  :group 'python-mode)

(defcustom py-use-local-default nil
  "If t, ‘py-shell’ will use `py-shell-local-path'.

Alternative to default Python.

Making switch between several virtualenv's easier,
                               `python-mode' should deliver an installer, so named-shells pointing to virtualenv's will be available."
  :type 'boolean
  :tag "py-use-local-default"
  :group 'python-mode)

(defcustom py-edit-only-p nil
  "Don't check for installed Python executables.

Default is nil.

See bug report at launchpad, lp:944093."
  :type 'boolean
  :tag "py-edit-only-p"
  :group 'python-mode)

(defcustom py-force-py-shell-name-p nil
  "When t, execution with kind of Python specified in `py-shell-name' is enforced, possibly shebang doesn't take precedence."

  :type 'boolean
  :tag "py-force-py-shell-name-p"
  :group 'python-mode)

(defcustom python-mode-v5-behavior-p nil
  "Execute region through `shell-command-on-region'.

As v5 did it - lp:990079. This might fail with certain chars - see UnicodeEncodeError lp:550661"

  :type 'boolean
  :tag "python-mode-v5-behavior-p"
  :group 'python-mode)

(defcustom py-trailing-whitespace-smart-delete-p nil
  "Default is nil.

When t, ‘python-mode’ calls
\(add-hook 'before-save-hook 'delete-trailing-whitespace nil 'local)

Also commands may delete trailing whitespace by the way.
When editing other peoples code, this may produce a larger diff than expected"
  :type 'boolean
  :tag "py-trailing-whitespace-smart-delete-p"
  :group 'python-mode)

(defcustom py-newline-delete-trailing-whitespace-p t
  "Delete trailing whitespace maybe left by `py-newline-and-indent'.

Default is t. See lp:1100892"
  :type 'boolean
  :tag "py-newline-delete-trailing-whitespace-p"
  :group 'python-mode)

(defcustom py--warn-tmp-files-left-p nil
  "Messages a warning, when `py-temp-directory' contains files susceptible being left by previous Python-mode sessions. See also lp:987534."
  :type 'boolean
  :tag "py--warn-tmp-files-left-p"
  :group 'python-mode)

(defcustom py-complete-ac-sources '(ac-source-pycomplete)
  "List of ‘auto-complete’ sources assigned to `ac-sources'.

In `py-complete-initialize'.

Default is known to work an Ubuntu 14.10 - having python-
mode, pymacs and auto-complete-el, with the following minimal
Emacs initialization:

\(require 'pymacs)
\(require 'auto-complete-config)
\(ac-config-default)"
  :type 'hook
  :tag "py-complete-ac-sources"
  :options '(ac-source-pycomplete ac-source-abbrev ac-source-dictionary ac-source-words-in-same-mode-buffers)
  :group 'python-mode)

(defcustom py-remove-cwd-from-path t
  "Whether to allow loading of Python modules from the current directory.
If this is non-nil, Emacs removes '' from sys.path when starting
a Python process.  This is the default, for security
reasons, as it is easy for the Python process to be started
without the user's realization (e.g. to perform completion)."
  :type 'boolean
  :tag "py-remove-cwd-from-path"
  :group 'python-mode)

(defcustom py-shell-local-path ""
  "If `py-use-local-default' is non-nil, `py-shell' will use EXECUTABLE indicated here incl. path."

  :type 'string
  :tag "py-shell-local-path"
  :group 'python-mode)

(defcustom py-python-edit-version ""
  "When not empty, fontify according to Python version specified.

Default is the empty string, a useful value \"python3\" maybe.

When empty, version is guessed via `py-choose-shell'."

  :type 'string
  :tag "py-python-edit-version"
  :group 'python-mode)

(defcustom py-ipython-execute-delay 0.3
  "Delay needed by execute functions when no IPython shell is running."
  :type 'float
  :tag "py-ipython-execute-delay"
  :group 'python-mode)

(defvar py-shell-completion-setup-code
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
  "Code used to setup completion in Python processes.")

(defvar py-shell-module-completion-code "';'.join(__COMPLETER_all_completions('''%s'''))"
  "Python code used to get completions separated by semicolons for imports.")

(defvar py-ipython-module-completion-code
  "import IPython
version = IPython.__version__
if \'0.10\' < version:
    from IPython.core.completerlib import module_completion
"
  "For IPython v0.11 or greater.
Use the following as the value of this variable:

';'.join(module_completion('''%s'''))")

(defvar py-ipython-module-completion-string
  "';'.join(module_completion('''%s'''))"
  "See also `py-ipython-module-completion-code'.")

(defcustom py--imenu-create-index-function 'py--imenu-create-index
  "Switch between `py--imenu-create-index-new', which also lists modules variables,  and series 5. index-machine."
  :type '(choice (const :tag "'py--imenu-create-index-new, also lists modules variables " py--imenu-create-index-new)

                 (const :tag "py--imenu-create-index, series 5. index-machine" py--imenu-create-index))
  :tag "py--imenu-create-index-function"
  :group 'python-mode)

(defvar py-line-re "^"
  "Used by generated functions." )

(defvar py-input-filter-re "\\`\\s-*\\S-?\\S-?\\s-*\\'"
  "Input matching this regexp is not saved on the history list.
Default ignores all inputs of 0, 1, or 2 non-blank characters.")

(defvaralias 'inferior-python-filter-regexp 'py-input-filter-re)

(defvar strip-chars-before  "\\`[ \t\r\n]*"
  "Regexp indicating which chars shall be stripped before STRING - which is defined by `string-chars-preserve'.")

(defvar strip-chars-after  "[ \t\r\n]*\\'"
  "Regexp indicating which chars shall be stripped after STRING - which is defined by `string-chars-preserve'.")

(defcustom py-docstring-style 'pep-257-nn
  "Implemented styles:

 are DJANGO, ONETWO, PEP-257, PEP-257-NN,SYMMETRIC, and NIL.

A value of NIL won't care about quotes
position and will treat docstrings a normal string, any other
value may result in one of the following docstring styles:

DJANGO:

    \"\"\"
    Process foo, return bar.
    \"\"\"

    \"\"\"
    Process foo, return bar.

    If processing fails throw ProcessingError.
    \"\"\"

ONETWO:

    \"\"\"Process foo, return bar.\"\"\"

    \"\"\"
    Process foo, return bar.

    If processing fails throw ProcessingError.

    \"\"\"

PEP-257:

    \"\"\"Process foo, return bar.\"\"\"

    \"\"\"Process foo, return bar.

    If processing fails throw ProcessingError.

    \"\"\"

PEP-257-NN:

    \"\"\"Process foo, return bar.\"\"\"

    \"\"\"Process foo, return bar.

    If processing fails throw ProcessingError.
    \"\"\"

SYMMETRIC:

    \"\"\"Process foo, return bar.\"\"\"

    \"\"\"
    Process foo, return bar.

    If processing fails throw ProcessingError.
    \"\"\""
  :type '(choice

          (const :tag "Don't format docstrings" nil)
          (const :tag "Django's coding standards style." django)
          (const :tag "One newline and start and Two at end style." onetwo)
          (const :tag "PEP-257 with 2 newlines at end of string." pep-257)
          (const :tag "PEP-257 with 1 newline at end of string." pep-257-nn)
          (const :tag "Symmetric style." symmetric))
  :tag "py-docstring-style"
  :group 'python-mode)

(defcustom py-execute-directory nil
  "Stores the file's default directory-name py-execute-... functions act upon.

Used by Python-shell for output of `py-execute-buffer' and related commands.
See also `py-use-current-dir-when-execute-p'"
  :type 'string
  :tag "py-execute-directory"
  :group 'python-mode)

(defcustom py-use-current-dir-when-execute-p t
  "Current directory used for output.

See also `py-execute-directory'"
  :type 'boolean
  :tag "py-use-current-dir-when-execute-p"
  :group 'python-mode)

(defcustom py-keep-shell-dir-when-execute-p nil
  "Don't change Python shell's current working directory when sending code.

See also `py-execute-directory'"
  :type 'boolean
  :tag "py-keep-shell-dir-when-execute-p"
  :group 'python-mode)

(defcustom py-fileless-buffer-use-default-directory-p t
  "When `py-use-current-dir-when-execute-p' is non-nil and no buffer-file exists, value of `default-directory' sets current working directory of Python output shell."
  :type 'boolean
  :tag "py-fileless-buffer-use-default-directory-p"
  :group 'python-mode)

(defcustom py-check-command "pychecker --stdlib"
  "Command used to check a Python file."
  :type 'string
  :tag "py-check-command"
  :group 'python-mode)

(defvar py-this-abbrevs-changed nil
  "Internally used by ‘python-mode-hook’.")

(defvar py-ffap-p nil)
(defvar py-ffap nil)
(defvar ffap-alist nil)

(defvar py-buffer-name nil
  "Internal use.

The buffer last output was sent to.")

(defvar py-orig-buffer-or-file nil
  "Internal use.")

(defun py--set-ffap-form ()
  (cond ((and py-ffap-p py-ffap)
         (eval-after-load "ffap"
           '(push '(python-mode . py-module-path) ffap-alist))
         (setq ffap-alist (remove '(python-mode . py-ffap-module-path) ffap-alist))
         (setq ffap-alist (remove '(py-shell-mode . py-ffap-module-path)
                                  ffap-alist)))
        (t (setq ffap-alist (remove '(python-mode . py-ffap-module-path) ffap-alist))
           (setq ffap-alist (remove '(py-shell-mode . py-ffap-module-path)
                                    ffap-alist))
           (setq ffap-alist (remove '(python-mode . py-module-path) ffap-alist)))))

(defcustom py-ffap-p nil

  "Select python-modes way to find file at point.

Default is nil"

  :type '(choice

          (const :tag "default" nil)
          (const :tag "use py-ffap" py-ffap))
  :tag "py-ffap-p"
  :set (lambda (symbol value)
         (set-default symbol value)
         (py--set-ffap-form))
    :group 'python-mode)

(defcustom py-keep-windows-configuration nil
  "Takes precedence over:

 `py-split-window-on-execute' and `py-switch-buffers-on-execute-p'.
See lp:1239498

To suppres window-changes due to error-signaling also.
Set `py-keep-windows-configuration' onto 'force

Default is nil"

  :type '(choice
          (const :tag "nil" nil)
          (const :tag "t" t)
          (const :tag "force" 'force))
  :tag "py-keep-windows-configuration"
  :group 'python-mode)

(defvar py-output-buffer "*Python Output*"
    "Currently unused.

Output buffer is created dynamically according to Python version and kind of process-handling")
(make-variable-buffer-local 'py-output-buffer)

(defvar py-ffap-string-code
  "__FFAP_get_module_path('''%s''')\n"
  "Python code used to get a string with the path of a module.")

(defcustom py-shell-prompt-regexp ">>> "
  "Regular Expression matching top\-level input prompt of python shell.
It should not contain a caret (^) at the beginning."
  :type 'string
  :tag "py-shell-prompt-regexp"
  :group 'python-mode)

(defvar py-ffap-setup-code
  "def __FFAP_get_module_path(module):
    try:
        import os
        path = __import__(module).__file__
        if path[-4:] == '.pyc' and os.path.exists(path[0:-1]):
            path = path[:-1]
        return path
    except:
        return ''
"
  "Python code to get a module path.")

(defvar py-eldoc-window-configuration nil
  "Keeps window-configuration when function ‘eldoc-mode’ is called.")

(defvar py-eldoc-setup-code
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
                    *inspect.getargspec(target))
                name = obj.__name__
                doc = '{objtype} {name}{args}'.format(
                    objtype=objtype, name=name, args=args)
        else:
            doc = doc.splitlines()[0]
    except:
        doc = ''
    try:
        exec('print doc')
    except SyntaxError:
        print(doc)"
  "Python code to setup documentation retrieval.")

(defcustom py-shell-prompt-output-regexp ""
  "Regular Expression matching output prompt of python shell.
It should not contain a caret (^) at the beginning."
  :type 'string
  :tag "py-shell-prompt-output-regexp"
  :group 'python-mode)

(defvar py-underscore-word-syntax-p t
  "This is set later by defcustom, only initial value here.

If underscore chars should be of ‘syntax-class’ `word', not of `symbol'.
Underscores in word-class makes `forward-word'.
Travels the indentifiers. Default is t.
See also command `toggle-py-underscore-word-syntax-p'")

(defvar py-autofill-timer nil)
(defvar py-fill-column-orig fill-column)

;; defvared value isn't updated maybe
(defvar python-mode-message-string
  (if (or (string= "python-mode.el" (buffer-name))
	  (ignore-errors (string-match "python-mode.el" (py--buffer-filename-remote-maybe))))
      "python-mode.el"
    "python-components-mode")
  "Internally used. Reports the ‘python-mode’ branch.")

;; defvared value isn't updated maybe
(setq python-mode-message-string
  (if (or (string= "python-mode.el" (buffer-name))
	  (ignore-errors (string-match "python-mode.el" (py--buffer-filename-remote-maybe))))
      "python-mode.el"
    "python-components-mode"))

(unless (fboundp 'string-to-syntax)
  ;; Skip's XE workaround
  (defun string-to-syntax (s)
    (cond
     ((equal s "|") '(15))
     ((equal s "_") '(3))
     (t (error "Unhandled string: %s" s)))))

(defvar python-mode-syntax-table nil
  "Give punctuation syntax to ASCII that normally has symbol.

Syntax or has word syntax and isn't a letter.")

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
        (if py-underscore-word-syntax-p
            (modify-syntax-entry ?\_ "w" table)
          (modify-syntax-entry ?\_ "_" table))
        table))

(defvar py-local-command nil
  "Returns locally used executable-name.")
(make-variable-buffer-local 'py-local-command)

(defvar py-local-versioned-command nil
  "Returns locally used executable-name including its version.")
(make-variable-buffer-local 'py-local-versioned-command)

(defvar py-ipython-completion-command-string nil
  "Select command according to IPython version.

Either ‘py-ipython0.10-completion-command-string’
or ‘py-ipython0.11-completion-command-string’.

‘py-ipython0.11-completion-command-string’ also covers version 0.12")

(defvar py-ipython0.10-completion-command-string
  "print(';'.join(__IP.Completer.all_completions('%s'))) #PYTHON-MODE SILENT\n"
  "The string send to ipython to query for all possible completions.")

(defvar py-ipython0.11-completion-command-string
  "print(';'.join(get_ipython().Completer.all_completions('%s'))) #PYTHON-MODE SILENT\n"
  "The string send to ipython to query for all possible completions.")

(defvar py-encoding-string-re "^[ \t]*#[ \t]*-\\*-[ \t]*coding:.+-\\*-"
  "Matches encoding string of a Python file.")

(defvar py-shebang-regexp "#![ \t]?\\([^ \t\n]+\\)[ \t]*\\([biptj]+ython[^ \t\n]*\\)"
  "Detecting the shell in head of file.")
;; (setq py-shebang-regexp   "#![ \t]?\\([^ \t\n]+\\)[ \t]*\\([biptj]+ython[^ \t\n]*\\)")

(defvar py-separator-char "/"
  "Values set by defcustom only will not be seen in batch-mode.")

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
                (error "Py-custom-temp-directory set but not writable")
              (error "Py-custom-temp-directory not an existing directory"))))
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
          (funcall ok (concat "c:" py-separator-char "Users"))
          (setq erg (concat "c:" py-separator-char "Users")))
     ;; (funcall ok ".")
     (error
      "Couldn't find a usable temp directory -- set `py-temp-directory'"))
    (when erg (setq py-temp-directory erg)))
  "Directory used for temporary files created by a *Python* process.
By default, guesses the first directory from this list that exists and that you
can write into: the value (if any) of the environment variable TMPDIR,
                          /usr/tmp, /tmp, /var/tmp, or the current directory.

                          `py-custom-temp-directory' will take precedence when setq")

(defvar py-pdbtrack-input-prompt "^[(<]*[Ii]?[Pp]y?db[>)]+ "
  "Recognize the prompt.")

(defvar py-pydbtrack-input-prompt "^[(]*ipydb[>)]+ "
  "Recognize the pydb-prompt.")

(defvar py-ipython-input-prompt-re "In \\[[0-9]+\\]:\\|^[ ]\\{3\\}[.]\\{3,\\}:"
  "A regular expression to match the IPython input prompt.")

 ;; prevent ipython.el's setting
(setq py-ipython-input-prompt-re   "In \\[[0-9]+\\]:\\|^[ ]\\{3\\}[.]\\{3,\\}:" )

(defvar py-exec-command nil
  "Internally used.")

(defvar py-which-bufname "Python")

(defvar py-pychecker-history nil)

(defvar py-pyflakes-history nil)

(defvar py-pep8-history nil)

(defvar py-pyflakespep8-history nil)

(defvar py-pylint-history nil)

(defvar py-ipython-output-prompt-re "^Out\\[[0-9]+\\]: "
  "A regular expression to match the output prompt of IPython.")

(defvar py-mode-output-map nil
  "Keymap used in *Python Output* buffers.")

(defvar hs-hide-comments-when-hiding-all t
  "Defined in hideshow.el, silence compiler warnings here.")

(defvar py-force-local-shell-p nil
  "Used internally, see `toggle-force-local-shell'.")

(defvar py-shell-complete-debug nil
  "For interal use when debugging, stores completions." )

(defcustom py-debug-p nil
  "When non-nil, keep resp. store information useful for debugging.

Temporary files are not deleted. Other functions might implement
some logging etc."
  :type 'boolean
  :tag "py-debug-p"
  :group 'python-mode)

(defcustom py-section-start "# {{"
  "Delimit arbitrary chunks of code."
  :type 'string
  :tag "py-section-start"
  :group 'python-mode)

(defcustom py-section-end "# }}"
  "Delimit arbitrary chunks of code."
  :type 'string
  :tag "py-section-end"
  :group 'python-mode)

(defvar py-section-re py-section-start)

(defvar py-last-window-configuration nil
  "Internal use: restore ‘py-restore-window-configuration’ when completion is done resp. abandoned.")

(defvar py-exception-buffer nil
  "Will be set internally, let-bound, remember source buffer where error might occur.")

(defvar py-string-delim-re "\\(\"\"\"\\|'''\\|\"\\|'\\)"
  "When looking at beginning of string.")

(defvar py-labelled-re "[ \\t]*:[[:graph:]]+"
  "When looking at label.")
;; (setq py-labelled-re "[ \\t]*:[[:graph:]]+")

(defvar py-expression-skip-regexp "[^ (=:#\t\r\n\f]"
  "Py-expression assumes chars indicated possible composing a ‘py-expression’, skip it.")

(defvar py-expression-skip-chars "^ (=#\t\r\n\f"
  "Py-expression assumes chars indicated possible composing a ‘py-expression’, skip it.")

(setq py-expression-skip-chars "^ [{(=#\t\r\n\f")

(defvar py-expression-re "[^ =#\t\r\n\f]+"
  "Py-expression assumes chars indicated possible composing a ‘py-expression’, when ‘looking-at’ or -back.")

(defcustom py-paragraph-re paragraph-start
  "Allow Python specific ‘paragraph-start’ var."
  :type 'string
  :tag "py-paragraph-re"
  :group 'python-mode)

(defvar py-not-expression-regexp "[ .=#\t\r\n\f)]+"
  "Py-expression assumes chars indicated probably will not compose a ‘py-expression’.")

(defvar py-not-expression-chars " #\t\r\n\f"
  "Py-expression assumes chars indicated probably will not compose a ‘py-expression’.")

(defvar py-partial-expression-backward-chars "^] .=,\"'()[{}:#\t\r\n\f"
  "Py-partial-expression assumes chars indicated possible composing a ‘py-partial-expression’, skip it.")
;; (setq py-partial-expression-backward-chars "^] .=,\"'()[{}:#\t\r\n\f")

(defvar py-partial-expression-forward-chars "^ .\"')}]:#\t\r\n\f")
;; (setq py-partial-expression-forward-chars "^ .\"')}]:#\t\r\n\f")

(defvar py-partial-expression-re (concat "[" py-partial-expression-backward-chars (substring py-partial-expression-forward-chars 1) "]+"))
(setq py-partial-expression-re (concat "[" py-partial-expression-backward-chars "]+"))

(defvar py-statement-re py-partial-expression-re)
(defvar py-indent-re ".+"
  "This var is introduced for regularity only.")
(setq py-indent-re ".+")

(defvar py-operator-re "[ \t]*\\(\\.\\|+\\|-\\|*\\|//\\|//\\|&\\|%\\||\\|\\^\\|>>\\|<<\\|<\\|<=\\|>\\|>=\\|==\\|!=\\|=\\)[ \t]*"
  "Matches most of Python syntactical meaningful characters.

See also `py-assignment-re'")

;; (setq py-operator-re "[ \t]*\\(\\.\\|+\\|-\\|*\\|//\\|//\\|&\\|%\\||\\|\\^\\|>>\\|<<\\|<\\|<=\\|>\\|>=\\|==\\|!=\\|=\\)[ \t]*")

(defvar py-assignment-re "[ \t]*=[^=]"
  "Matches assignment operator inclusive whitespaces around.

See also `py-operator-re'")

(defvar py-delimiter-re "\\(\\.[[:alnum:]]\\|,\\|;\\|:\\)[ \t\n]"
  "Delimiting elements of lists or other programming constructs.")

(defvar py-line-number-offset 0
  "When an exception occurs as a result of ‘py-execute-region’.

A subsequent ‘py-up-exception’ needs the line number where the region
started, in order to jump to the correct file line.
This variable is set in ‘py-execute-region’ and used in ‘py--jump-to-exception’.")

(defvar py-match-paren-no-use-syntax-pps nil)

(defvar py-traceback-line-re
  "[ \t]+File \"\\([^\"]+\\)\", line \\([0-9]+\\)"
  "Regular expression that describes tracebacks.")

(defvar py-XXX-tag-face 'py-XXX-tag-face)

(defvar py-pseudo-keyword-face 'py-pseudo-keyword-face)

(defvar py-variable-name-face 'py-variable-name-face)

(defvar py-number-face 'py-number-face)

(defvar py-decorators-face 'py-decorators-face)

(defvar py-object-reference-face 'py-object-reference-face)

(defvar py-builtins-face 'py-builtins-face)

(defvar py-class-name-face 'py-class-name-face)

(defvar py-exception-name-face 'py-exception-name-face)

(defvar py-import-from-face 'py-import-from-face)

(defvar py-def-class-face 'py-def-class-face)

(defvar py-try-if-face 'py-try-if-face)

(defvar py-file-queue nil
  "Queue of Python temp files awaiting execution.
Currently-active file is at the head of the list.")

(defvar jython-mode-hook nil
  "Hook called by `jython-mode'.
`jython-mode' also calls `python-mode-hook'.")

(defvar py-shell-hook nil
  "Hook called by `py-shell'.")

(defvar python-font-lock-keywords nil)

(defvar py-dotted-expression-syntax-table
  (let ((table (make-syntax-table python-mode-syntax-table)))
    (modify-syntax-entry ?_ "_" table)
    (modify-syntax-entry ?."_" table)
    table)
  "Syntax table used to identify Python dotted expressions.")

(defvar python-default-template "if"
  "Default template to expand by `python-expand-template'.
Updated on each expansion.")

(defvar py-already-guessed-indent-offset nil
  "Internal use by ‘py-indent-line’.

When `this-command' is `eq' to `last-command', use the guess already computed.")
(make-variable-buffer-local 'py-already-guessed-indent-offset)

(defvar py-shell-template "
\(defun NAME (&optional argprompt)
  \"Start an DOCNAME interpreter in another window.

With optional \\\\[universal-argument] user is prompted
for options to pass to the DOCNAME interpreter. \"
  (interactive \"P\")
  (let\* ((py-shell-name \"FULLNAME\"))
    (py-shell argprompt)
    (when (called-interactively-p 'any) (switch-to-buffer (current-buffer))
          (goto-char (point-max)))))
")

(defvar py-fast-filter-re (concat "\\("
			       (mapconcat 'identity
					  (delq nil (list py-shell-input-prompt-1-regexp py-shell-input-prompt-2-regexp py-ipython-input-prompt-re py-ipython-output-prompt-re py-pdbtrack-input-prompt py-pydbtrack-input-prompt "[.]\\{3,\\}:? *"))
					  "\\|")
			       "\\)")
  "Internally used by `py-fast-filter'.
‘ansi-color-filter-apply’ might return
Result: \"\\nIn [10]:    ....:    ....:    ....: 1\\n\\nIn [11]: \"")

;; Constants
(defconst py-block-closing-keywords-re
  "[ \t]*\\_<\\(return\\|raise\\|break\\|continue\\|pass\\)\\_>[ \n\t]"
  "Matches the beginning of a class, method or compound statement.")

(setq py-block-closing-keywords-re
  "[ \t]*\\_<\\(return\\|raise\\|break\\|continue\\|pass\\)\\_>[ \n\t]")

(defconst py-finally-re
  "[ \t]*\\_<finally\\_>[: \n\t]"
  "Regular expression matching keyword which closes a try-block.")

(defconst py-except-re
  "[ \t]*\\_<except\\_>[:( \n\t]*"
  "Regular expression matching keyword which composes a try-block.")

(defconst py-return-re
  ".*:?[ \t]*\\_<\\(return\\)\\_>[ \n\t]*"
  "Regular expression matching keyword which typically closes a function.")

(defconst py-decorator-re
  "[ \t]*@[^ ]+\\_>[ \n\t]*"
  "Regular expression matching keyword which typically closes a function.")

(defcustom py-outdent-re-raw
  (list
   "async def"
   "async for"
   "async with"
   "class"
   "def"
   "elif"
   "else"
   "except"
   "for"
   "if"
   "try"
   "while"
   "with")
  "Used by ‘py-outdent-re’."
  :type '(repeat string)
  :tag "py-outdent-re-raw"
  :group 'python-mode
  )

(defconst py-outdent-re
  (concat
   "[ \t]*\\_<"
   (regexp-opt py-outdent-re-raw)
   "\\_>[)\t]*")
  "Regular expression matching lines not to augment indent after.

See ‘py-no-outdent-re-raw’ for better readable content")

(defcustom py-no-outdent-re-raw
  (list
   "break"
   "continue"
   "import"
   "pass"
   "raise"
   "return")
  "Uused by o‘py-no-outdent-re’."
  :type '(repeat string)
  :tag "py-no-outdent-re-raw"
  :group 'python-mode)

(defconst py-no-outdent-re
  (concat
   "[ \t]*\\_<"
   (regexp-opt py-no-outdent-re-raw)
   "\\_>[)\t]*$")
  "Regular expression matching lines not to augment indent after.

See ‘py-no-outdent-re-raw’ for better readable content")

(defconst py-assignment-re "\\_<\\w+\\_>[ \t]*\\(=\\|+=\\|*=\\|%=\\|&=\\|^=\\|<<=\\|-=\\|/=\\|**=\\||=\\|>>=\\|//=\\)"
  "If looking at the beginning of an assignment.")

(defconst py-block-re "[ \t]*\\_<\\(class\\|def\\|async def\\|async for\\|for\\|if\\|try\\|while\\|with\\|async with\\)\\_>[:( \n\t]*"
  "Matches the beginning of a compound statement.")

(defconst py-minor-block-re "[ \t]*\\_<\\(for\\|async for\\|if\\|try\\|with\\|async with\\|except\\)\\_>[:( \n\t]*"
  "Matches the beginning of an `for', `if', `try', `except' or `with' block.")

(defconst py-try-block-re "[ \t]*\\_<try\\_>[: \n\t]"
  "Matches the beginning of a `try' block.")

(defconst py-except-block-re "[ \t]*\\_<except\\_> *a?s? *[[:print:]]*[: \n\t]"
  "Matches the beginning of a `except' block.")

(defconst py-for-block-re "[ \t]*\\_<\\(for\\|async for\\)\\_> +[[:alpha:]_][[:alnum:]_]* +in +[[:alpha:]_][[:alnum:]_()]* *[: \n\t]"
  "Matches the beginning of a `try' block.")

(defconst py-if-block-re "[ \t]*\\_<if\\_> +[[:alpha:]_][[:alnum:]_]* *[: \n\t]"
  "Matches the beginning of an `if' block.")

(defconst py-else-block-re "[ \t]*\\_<else:?[ \n\t]*"
  "Matches the beginning of an `else' block.")

(defconst py-elif-block-re "[ \t]*\\_<elif\\_> +[[:alpha:]_][[:alnum:]_]* *[: \n\t]"
  "Matches the beginning of an `elif' block.")

(defconst py-class-re "[ \t]*\\_<\\(class\\)\\_>[ \n\t]"
  "Matches the beginning of a class definition.")

(defconst py-def-or-class-re "[ \t]*\\_<\\(async def\\|class\\|def\\)\\_>[ \n\t]+\\([[:alnum:]_]*\\)"
  "Matches the beginning of a class- or functions definition.

Second group grabs the name")

;; (setq py-def-or-class-re "[ \t]*\\_<\\(async def\\|class\\|def\\)\\_>[ \n\t]")

;; (defconst py-def-re "[ \t]*\\_<\\(async def\\|def\\)\\_>[ \n\t]"
(defconst py-def-re "[ \t]*\\_<\\(def\\|async def\\)\\_>[ \n\t]"
  "Matches the beginning of a functions definition.")

(defcustom py-block-or-clause-re-raw
  (list
   "async for"
   "async with"
   "async def"
   "async class"
   "class"
   "def"
   "elif"
   "else"
   "except"
   "finally"
   "for"
   "if"
   "try"
   "while"
   "with"
   )
  "Matches the beginning of a compound statement or it's clause."
  :type '(repeat string)
  :tag "py-block-or-clause-re-raw"
  :group 'python-mode)

(defvar py-block-or-clause-re
  (concat
   "[ \t]*\\_<\\("
   (regexp-opt  py-block-or-clause-re-raw)
   "\\)\\_>[( \t]*.*:?")
  "See ‘py-block-or-clause-re-raw’, which it reads.")

;; (setq py-block-or-clause-re
;;   (concat
;;    "[ \t]*\\_<\\("
;;    (regexp-opt  py-block-or-clause-re-raw)
;;    "\\)\\_>[( \t]*.*:?"))


(defcustom py-block-re-raw
  (list
   "except"
   "for"
   "if"
   "try"
   "while"
   "with")
  "Matches the beginning of a compound statement but not it's clause."
  :type '(repeat string)
  :tag "py-block-re-raw"
  :group 'python-mode)

(defvar py-block-re
  (concat
   "[ \t]*\\_<\\("
   (regexp-opt  py-block-re-raw)
   "\\)\\_>[( \t]*.*:?")
  "See ‘py-block-or-clause-re-raw’, which it reads.")

(defconst py-clause-re
  (concat
   "[ \t]*\\_<\\("
   (mapconcat 'identity
              (list
               "elif"
               "else"
               "except"
               "finally")
              "\\|")
   "\\)\\_>[( \t]*.*:?")
  "Regular expression matching lines not to augment indent after.")

(defcustom py-extended-block-or-clause-re-raw
  (list
   "async def"
   "async for"
   "async with"
   "class"
   "def"
   "elif"
   "else"
   "except"
   "finally"
   "for"
   "if"
   "try"
   "while"
   "with")
  "Matches the beginning of a compound statement or it's clause."
  :type '(repeat string)
  :tag "py-extended-block-or-clause-re-raw"
  :group 'python-mode)

(defconst py-extended-block-or-clause-re
  (concat
   "[ \t]*\\_<\\("
   (regexp-opt  py-extended-block-or-clause-re-raw)
   "\\)\\_>[( \t]*.*:?")
  "See ‘py-block-or-clause-re-raw’, which it reads.")

(defcustom py-top-level-re
  (concat
   "^\\_<[a-zA-Z_]\\|^\\_<\\("
   (regexp-opt  py-extended-block-or-clause-re-raw)
   "\\)\\_>[( \t]*.*:?")
  "A form which starts at zero indent level, but is not a comment."
  :type '(regexp)
  :tag "py-top-level-re"
  :group 'python-mode
  )

(defvar py-comment-re comment-start
  "Needed for normalized processing.")

(defconst py-block-keywords
  (concat
   "\\_<\\("
   (regexp-opt py-block-or-clause-re-raw)
   "\\)\\_>")
  "Matches known keywords opening a block.

Customizing `py-block-or-clause-re-raw'  will change values here")

(defcustom py-clause-re-raw
  (list
   "elif"
   "else"
   "except"
   "finally"
   )
  "Matches the beginning of a clause."
    :type '(repeat string)
    :tag "py-clause-re-raw"
    :group 'python-mode)

(defconst py-clause-re
  (concat
   "[ \t]*\\_<\\("
   (regexp-opt  py-clause-re-raw)
   "\\)\\_>[( \t]*.*:?")
  "See ‘py-clause-re-raw’, which it reads.")

(defconst py-elif-re "[ \t]*\\_<\\elif\\_>[:( \n\t]*"
  "Matches the beginning of a compound if-statement's clause exclusively.")

(defconst py-try-clause-re
  (concat
   "[ \t]*\\_<\\("
   (mapconcat 'identity
              (list
               "else"
               "except"
               "finally")
              "\\|")
   "\\)\\_>[( \t]*.*:")
  "Matches the beginning of a compound try-statement's clause.")

(defconst py-if-re "[ \t]*\\_<if\\_>[( \n\t]*"
  "Matches the beginning of a compound statement saying `if'.")

(defconst py-try-re "[ \t]*\\_<try\\_>[:( \n\t]*"
  "Matches the beginning of a compound statement saying `try'." )

(defcustom py-compilation-regexp-alist
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
  "Fetch errors from Py-shell.
hooked into `compilation-error-regexp-alist'"
  :type '(alist string)
  :tag "py-compilation-regexp-alist"
  :group 'python-mode)

(defun py--quote-syntax (n)
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
	     (syntax (parse-partial-sexp (point-min) (point))))
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
	(unless (eq 'string (syntax-ppss-context (parse-partial-sexp (point-min) (point))))
	  (eval-when-compile (string-to-syntax "|")))))
     ;; Otherwise (we're in a non-matching string) the property is
     ;; nil, which is OK.
     )))

(defconst py-font-lock-syntactic-keywords
  ;; Make outer chars of matching triple-quote sequences into generic
  ;; string delimiters.  Fixme: Is there a better way?
  ;; First avoid a sequence preceded by an odd number of backslashes.
  `((,(concat "\\(?:^\\|[^\\]\\(?:\\\\.\\)*\\)" ;Prefix.
              "\\(?1:\"\\)\\(?2:\"\\)\\(?3:\"\\)\\(?4:\"\\)\\(?5:\"\\)\\(?6:\"\\)\\|\\(?1:\"\\)\\(?2:\"\\)\\(?3:\"\\)\\|\\(?1:'\\)\\(?2:'\\)\\(?3:'\\)\\(?4:'\\)\\(?5:'\\)\\(?6:'\\)\\|\\(?1:'\\)\\(?2:'\\)\\(?3:'\\)\\(?4:'\\)\\(?5:'\\)\\(?6:'\\)\\|\\(?1:'\\)\\(?2:'\\)\\(?3:'\\)")
     (1 (py--quote-syntax 1) t t)
     (2 (py--quote-syntax 2) t t)
     (3 (py--quote-syntax 3) t t)
     (6 (py--quote-syntax 1) t t))))

(defconst py-windows-config-register 313465889
  "Internal used.")

(defvar py-windows-config nil
  "Completion stores ‘py-windows-config-register’ here.")

(put 'py-indent-offset 'safe-local-variable 'integerp)

;; testing
(defvar py-ert-test-default-executables
  (list "python" "python3" "ipython")
  "Serialize tests employing dolist.")

(defvar py--shell-unfontify nil
  "Internally used by `py--run-unfontify-timer'.")
(make-variable-buffer-local 'py--shell-unfontify)

(defvar py--timer nil
  "Used by `py--run-unfontify-timer'.")
(make-variable-buffer-local 'py--timer)

(defvar py--timer-delay nil
  "Used by `py--run-unfontify-timer'.")
(make-variable-buffer-local 'py--timer-delay)

(defcustom py-shell-unfontify-p t
  "Run `py--run-unfontify-timer' unfontifying the shell banner-text.

Default is nil"

  :type 'boolean
  :tag "py-shell-unfontify-p"
  :group 'python-mode)

(defun py--unfontify-banner-intern (buffer)
  "Internal use, unfontify BUFFER."
  (save-excursion
    (goto-char (point-min))
    (let ((erg (or (ignore-errors (car comint-last-prompt))
		   (and
		    (re-search-forward py-fast-filter-re nil t 1)
		    (match-beginning 0))
		   (progn
		     (forward-paragraph)
		     (point)))))
      ;; (sit-for 1 t)
      (if erg
	  (progn
	    (font-lock-unfontify-region (point-min) erg)
	    (goto-char (point-max)))
	(progn (and py-debug-p (message "%s" (concat "py--unfontify-banner: Don't see a prompt in buffer " (buffer-name buffer)))))))))

(defun py--unfontify-banner (&optional buffer)
  "Unfontify the shell banner-text.

Cancels `py--timer'
Expects being called by `py--run-unfontify-timer'
Optional argument BUFFER which select."
  (interactive)
    (let ((buffer (or buffer (current-buffer))))
      (if (ignore-errors (buffer-live-p (get-buffer buffer)))
	  (with-current-buffer buffer
	    (py--unfontify-banner-intern buffer)
	    (and (timerp py--timer)(cancel-timer py--timer)))
	(and (timerp py--timer)(cancel-timer py--timer)))))

(defun py--run-unfontify-timer (&optional buffer)
  "Unfontify the shell banner-text.
Optional argument BUFFER select buffer."
  (when py--shell-unfontify
    (let ((buffer (or buffer (current-buffer))))
      (if (and
	   (buffer-live-p buffer)
	   (or
	    (eq major-mode 'py-python-shell-mode)
	    (eq major-mode 'py-ipython-shell-mode)))
	  (unless py--timer
	    (setq py--timer
		  (run-with-idle-timer
		   (if py--timer-delay (setq py--timer-delay 3)
		     (setq py--timer-delay 0.1))
		   nil
		   #'py--unfontify-banner buffer)))
	(cancel-timer py--timer)))))

(defsubst py-keep-region-active ()
  "Keep the region active in XEmacs."
  (and (boundp 'zmacs-region-stays)
       (setq zmacs-region-stays t)))

 ;; GNU's syntax-ppss-context
(unless (functionp 'syntax-ppss-context)
  (defsubst syntax-ppss-context (ppss)
    (cond
     ((nth 3 ppss) 'string)
     ((nth 4 ppss) 'comment)
     (t nil))))

(defface py-XXX-tag-face
  '((t (:inherit font-lock-string-face)))
  "XXX\\|TODO\\|FIXME "
  :tag "py-XXX-tag-face"
  :group 'python-mode)

(defface py-pseudo-keyword-face
  '((t (:inherit font-lock-keyword-face)))
  "Face for pseudo keywords in Python mode, like self, True, False,
  Ellipsis.

See also `py-object-reference-face'"
  :tag "py-pseudo-keyword-face"
  :group 'python-mode)

(defface py-object-reference-face
  '((t (:inherit py-pseudo-keyword-face)))
  "Face when referencing object members from its class resp. method., commonly \"cls\" and \"self\""
  :tag "py-object-reference-face"
  :group 'python-mode)

(defface py-variable-name-face
  '((t (:inherit default)))
  "Face method decorators."
  :tag "py-variable-name-face"
  :group 'python-mode)

(defface py-number-face
 '((t (:inherit default)))
  "Highlight numbers."
  :tag "py-number-face"
  :group 'python-mode)

(defface py-try-if-face
  '((t (:inherit font-lock-keyword-face)))
  "Highlight keywords."
  :tag "py-try-if-face"
  :group 'python-mode)

(defface py-import-from-face
  '((t (:inherit font-lock-keyword-face)))
  "Highlight keywords."
  :tag "py-import-from-face"
  :group 'python-mode)

(defface py-def-class-face
  '((t (:inherit font-lock-keyword-face)))
  "Highlight keywords."
  :tag "py-def-class-face"
  :group 'python-mode)

 ;; PEP 318 decorators
(defface py-decorators-face
  '((t (:inherit font-lock-keyword-face)))
  "Face method decorators."
  :tag "py-decorators-face"
  :group 'python-mode)

(defface py-builtins-face
  '((t (:inherit font-lock-builtin-face)))
  "Face for builtins like TypeError, object, open, and exec."
  :tag "py-builtins-face"
  :group 'python-mode)

(defface py-class-name-face
  '((t (:inherit font-lock-type-face)))
  "Face for classes."
  :tag "py-class-name-face"
  :group 'python-mode)

(defface py-exception-name-face
  '((t (:inherit font-lock-builtin-face)))
  "."
  :tag "py-exception-name-face"
  :group 'python-mode)

(defun py--python-send-setup-code-intern (name &optional msg)
  (let ((setup-file (concat (py--normalize-directory py-temp-directory) "py-" name "-setup-code.py"))
	(buf (current-buffer)))
    (unless (file-readable-p setup-file)
      (with-temp-buffer
	(insert (eval (car (read-from-string (concat "py-" name "-setup-code")))))
	(write-file setup-file)))
    (py--execute-file-base nil setup-file nil buf)
    (when msg (message "%s" (concat name " setup-code sent to " (process-name (get-buffer-process buf)))))))

(defun py--python-send-completion-setup-code ()
  "For Python see py--python-send-setup-code."
  (py--python-send-setup-code-intern "shell-completion" py-verbose-p))

(defun py--python-send-ffap-setup-code ()
  "For Python see py--python-send-setup-code."
  (py--python-send-setup-code-intern "ffap" py-verbose-p))

(defun py--python-send-eldoc-setup-code ()
  "For Python see py--python-send-setup-code."
  (py--python-send-setup-code-intern "eldoc" py-verbose-p))

(defun py--ipython-import-module-completion ()
  "Setup IPython v0.11 or greater.

Used by `py-ipython-module-completion-string'"
  (let ((setup-file (concat (py--normalize-directory py-temp-directory) "py-ipython-module-completion.py")))
    (unless (file-readable-p setup-file)
      (with-temp-buffer
	(insert py-ipython-module-completion-code)
	(write-file setup-file)))
    (py--execute-file-base nil setup-file nil (current-buffer))))

(defun py--at-raw-string ()
  "If at beginning of a raw-string."
  (and (looking-at "\"\"\"\\|'''") (member (char-before) (list ?u ?U ?r ?R))))

(defun py--docstring-p (pos)
  "Check to see if there is a docstring at POS."
    (save-excursion
      (goto-char pos)
	(when (py--at-raw-string)
	  (forward-char -1)
	  (setq pos (point)))
	(when (py-backward-statement)
	  (when (looking-at py-def-or-class-re)
	    pos))))

(defun py--font-lock-syntactic-face-function (state)
  "STATE expected as result von (parse-partial-sexp (point-min) (point)."
  (if (nth 3 state)
      (if (py--docstring-p (nth 8 state))
          font-lock-doc-face
        font-lock-string-face)
    font-lock-comment-face))

(and (fboundp 'make-obsolete-variable)
     (make-obsolete-variable 'py-mode-hook 'python-mode-hook nil))

(defun py-choose-shell-by-shebang (&optional shebang)
  "Choose shell by looking at #! on the first line.

If SHEBANG is non-nil, returns the shebang as string,
otherwise the Python resp. Jython shell command name."
  (interactive)
  ;; look for an interpreter specified in the first line
  (let* (erg res)
    (save-excursion
      (goto-char (point-min))
      (when (looking-at py-shebang-regexp)
        (if shebang
            (setq erg (match-string-no-properties 0))
          (setq erg (split-string (match-string-no-properties 0) "[#! \t]"))
          (dolist (ele erg)
            (when (string-match "[bijp]+ython" ele)
              (setq res ele))))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" res))
    res))

(defun py--choose-shell-by-import ()
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

(defun py-choose-shell-by-path (&optional separator-char)
  "SEPARATOR-CHAR according to system ‘path-separator’."
  "Select Python executable according to version desplayed in path.

Returns versioned string, nil if nothing appropriate found"
  (interactive)
  (let ((path (py--buffer-filename-remote-maybe))
	(separator-char (or separator-char py-separator-char))
                erg)
    (when (and path separator-char
               (string-match (concat separator-char "[iI]?[pP]ython[0-9.]+" separator-char) path))
      (setq erg (substring path
                           (1+ (string-match (concat separator-char "[iI]?[pP]ython[0-9.]+" separator-char) path)) (1- (match-end 0)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-which-python (&optional shell)
  "Return version of Python of current environment, a number.
Optional argument SHELL selected shell."
  (interactive)
  (let* ((cmd (or shell (py-choose-shell)))
	 (treffer (string-match "\\([23]*\\.?[0-9\\.]*\\)$" cmd))
         version erg)
    (if treffer
        ;; if a number if part of python name, assume it's the version
        (setq version (substring-no-properties cmd treffer))
      (setq erg (shell-command-to-string (concat cmd " --version")))
      (setq version (cond ((string-match (concat "\\(on top of Python \\)" "\\([0-9]\\.[0-9]+\\)") erg)
                           (match-string-no-properties 2 erg))
                          ((string-match "\\([0-9]\\.[0-9]+\\)" erg)
                           (substring erg 7 (1- (length erg)))))))
    (when (called-interactively-p 'any)
      (if version
          (when py-verbose-p (message "%s" version))
        (message "%s" "Could not detect Python on your system")))
    (string-to-number version)))

(defun py-python-current-environment ()
  "Return path of current Python installation."
  (interactive)
  (let* ((cmd (py-choose-shell))
         (denv (shell-command-to-string (concat "type " cmd)))
         (erg (substring denv (string-match "/" denv))))
    (when (called-interactively-p 'any)
      (if erg
          (message "%s" erg)
        (message "%s" "Could not detect Python on your system")))
    erg))

 ;; requested by org-mode still
(defalias 'py-toggle-shells 'py-choose-shell)

(defun py--cleanup-process-name (res)
  "Make res ready for use by `executable-find'.

Returns RES or substring of RES"
  (if (string-match "<" res)
      (substring res 0 (match-beginning 0))
    res))

(defalias 'py-which-shell 'py-choose-shell)
(defun py-choose-shell (&optional arg fast)
  "Return an appropriate executable as a string.

Returns nil, if no executable found.

This does the following:
 - look for an interpreter with `py-choose-shell-by-shebang'
 - examine imports using `py--choose-shell-by-import'
 - look if Path/To/File indicates a Python version
 - if not successful, return default value of `py-shell-name'

When interactivly called, messages the shell name.

With \\[universal-argument] 4 is called `py-switch-shell'.
Optional argument ARG switch shell with universal argument.
Optional argument FAST use fast-process."
  (interactive "P")
  (if (eq 4 (prefix-numeric-value arg))
      (py-switch-shell '(4))
    (let* (res done
	       (erg (cond (py-force-py-shell-name-p
			   (default-value 'py-shell-name))
			  (py-use-local-default
			   (if (not (string= "" py-shell-local-path))
			       (expand-file-name py-shell-local-path)
			     (message "Abort: `py-use-local-default' is set to `t' but `py-shell-local-path' is empty. Maybe call `py-toggle-local-default-use'")))
			  ((and (or fast py-fast-process-p)
				(comint-check-proc (current-buffer))
				(string-match "ython" (process-name (get-buffer-process (current-buffer)))))
			   (progn
			     (setq res (process-name (get-buffer-process (current-buffer))))
			     (py--cleanup-process-name res)))
			  ((and (not py-fast-process-p)
				(comint-check-proc (current-buffer))
				(setq done t)
				(string-match "ython" (process-name (get-buffer-process (current-buffer)))))
			   (setq res (process-name (get-buffer-process (current-buffer))))
			   (py--cleanup-process-name res))
			  ((py-choose-shell-by-shebang))
			  ((py--choose-shell-by-import))
			  ((py-choose-shell-by-path))
			  (t (or
			      (default-value 'py-shell-name)
			      "python"))))
	       (cmd (if (or
			 ;; comint-check-proc was succesful
			 done
			 py-edit-only-p) erg
		      (executable-find erg))))
      (if cmd
          (when (called-interactively-p 'any)
            (message "%s" cmd))
        (when (called-interactively-p 'any) (message "%s" "Could not detect Python on your system. Maybe set `py-edit-only-p'?")))
      erg)))


(defun py--normalize-directory (directory)
  "Make sure DIRECTORY ends with a file-path separator char.

Returns DIRECTORY"
  (let ((erg (cond ((string-match (concat py-separator-char "$") directory)
                    directory)
                   ((not (string= "" directory))
                    (concat directory py-separator-char)))))
    (unless erg (when py-verbose-p (message "Warning: directory is empty")))
    erg))

(defun py--normalize-pythonpath (pythonpath)
  "Make sure PYTHONPATH ends with a colon.

Returns PYTHONPATH"
  (let ((erg (cond ((string-match (concat path-separator "$") pythonpath)
                    pythonpath)
                   ((not (string= "" pythonpath))
                    (concat pythonpath path-separator))
		   (t pythonpath))))
    erg))

(defun py-install-directory-check ()
  "Do some sanity check for `py-install-directory'.

Returns t if successful."
  (interactive)
  (let ((erg (and (boundp 'py-install-directory) (stringp py-install-directory) (< 1 (length py-install-directory)))))
    (when (called-interactively-p 'any) (message "py-install-directory-check: %s" erg))
    erg))

(defun py-guess-py-install-directory ()
  "Takes value of user directory aka $HOME.

If `(locate-library \"python-mode\")' is not succesful.

Used only, if `py-install-directory' is empty."
  (interactive)
  (let ((erg (cond ((locate-library "python-mode")
		    (file-name-directory (locate-library "python-mode")))
		   ((ignore-errors (string-match "python-mode" (py--buffer-filename-remote-maybe)))
		    (file-name-directory (py--buffer-filename-remote-maybe)))
		   ((string-match "python-mode" (buffer-name))
		    default-directory))))
    (cond ((and (or (not py-install-directory) (string= "" py-install-directory)) erg)
	   (setq py-install-directory erg))
	  (t (setq py-install-directory (expand-file-name "~/")))))
  (when (and py-verbose-p (called-interactively-p 'any)) (message "Setting py-install-directory to: %s" py-install-directory))
  py-install-directory)

(defun py--fetch-pythonpath ()
  "Consider settings of ‘py-pythonpath’."
  (if (string= "" py-pythonpath)
      (getenv "PYTHONPATH")
    (concat (py--normalize-pythonpath (getenv "PYTHONPATH")) py-pythonpath)))

(defun py-load-pymacs ()
  "Load Pymacs as delivered.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.ca"
  (interactive)
  (let ((pyshell (py-choose-shell))
        (path (py--fetch-pythonpath))
        (py-install-directory (cond ((string= "" py-install-directory)
                                     (py-guess-py-install-directory))
                                    (t (py--normalize-directory py-install-directory)))))
    (if (py-install-directory-check)
        (progn
          ;; If Pymacs has not been loaded before, prepend py-install-directory to
          ;; PYTHONPATH, so that the Pymacs delivered with python-mode is used.
          (unless (featurep 'pymacs)
            (setenv "PYTHONPATH" (concat
                                  (expand-file-name py-install-directory)
                                  (if path (concat path-separator path)))))
          (setenv "PYMACS_PYTHON" (if (string-match "IP" pyshell)
                                      "python"
                                    pyshell))
          (require 'pymacs))
      (error "`py-install-directory' not set, see INSTALL"))))

(when py-load-pymacs-p (py-load-pymacs))

(when (and py-load-pymacs-p (featurep 'pymacs))
  (defun py-load-pycomplete ()
    "Load Pymacs based pycomplete."
    (interactive)
    (let* ((path (py--fetch-pythonpath))
           (py-install-directory (cond ((string= "" py-install-directory)
                                        (py-guess-py-install-directory))
                                       (t (py--normalize-directory py-install-directory))))
           (pycomplete-directory (concat (expand-file-name py-install-directory) "completion")))
      (if (py-install-directory-check)
          (progn
            ;; If the Pymacs process is already running, augment its path.
            (when (and (get-process "pymacs") (fboundp 'pymacs-exec))
              (pymacs-exec (concat "sys.path.insert(0, '" pycomplete-directory "')")))
            (require 'pymacs)
            (setenv "PYTHONPATH" (concat
                                  pycomplete-directory
                                  (if path (concat path-separator path))))
            (push pycomplete-directory load-path)
            (require 'pycomplete)
            (add-hook 'python-mode-hook 'py-complete-initialize))
        (error "`py-install-directory' not set, see INSTALL")))))

(when (functionp 'py-load-pycomplete)
  (py-load-pycomplete))

(defun py-set-load-path ()
  "Include needed subdirs of ‘python-mode’ directory."
  (interactive)
  (let ((py-install-directory (py--normalize-directory py-install-directory)))
    (cond ((and (not (string= "" py-install-directory))(stringp py-install-directory))
           (push (expand-file-name py-install-directory) load-path)
           (push (concat (expand-file-name py-install-directory) "completion")  load-path)
           (push (concat (expand-file-name py-install-directory) "extensions")  load-path)
           (push (concat (expand-file-name py-install-directory) "test") load-path)
           (push (concat (expand-file-name py-install-directory) "tools")  load-path)
           (push (concat (expand-file-name py-install-directory) "autopair")  load-path))
          (py-guess-py-install-directory-p
	   (let ((guessed-py-install-directory (py-guess-py-install-directory)))
	     (when guessed-py-install-directory
	       (push guessed-py-install-directory  load-path))))
          (t (error "Please set `py-install-directory', see INSTALL"))
          (when (called-interactively-p 'any) (message "%s" load-path)))))

(unless py-install-directory
  (push default-directory  load-path)
  (push (concat default-directory "extensions")  load-path))

(defun py-count-lines (&optional beg end)
  "Count lines in accessible part until current line.

See http://debbugs.gnu.org/cgi/bugreport.cgi?bug=7115
Optional argument BEG specify beginning.
Optional argument END specify end."
  (interactive)
  (save-excursion
    (let ((count 0)
	  (beg (or beg (point-min)))
	  (end (or end (point))))
      (save-match-data
	(if (or (eq major-mode 'comint-mode)
		(eq major-mode 'py-shell-mode))
	    (if
		(re-search-backward py-fast-filter-re nil t 1)
		(goto-char (match-end 0))
	      ;; (when py-debug-p (message "%s"  "py-count-lines: Don't see a prompt here"))
	      (goto-char beg))
	  (goto-char beg)))
      (while (and (< (point) end)(not (eobp)) (skip-chars-forward "^\n" end))
        (setq count (1+ count))
        (unless (or (not (< (point) end)) (eobp)) (forward-char 1)
                (setq count (+ count (abs (skip-chars-forward "\n" end))))))
      (when (bolp) (setq count (1+ count)))
      (when (and py-debug-p (called-interactively-p 'any)) (message "%s" count))
      count)))

(defmacro py-escaped ()
  "Return t if char is preceded by an odd number of backslashes."
  `(save-excursion
     (< 0 (% (abs (skip-chars-backward "\\\\")) 2))))

(defmacro py-current-line-backslashed-p ()
  "Return t if current line is a backslashed continuation line."
  `(save-excursion
     (end-of-line)
     (skip-chars-backward " \t\r\n\f")
     (and (eq (char-before (point)) ?\\ )
          (py-escaped))))

(defmacro py-preceding-line-backslashed-p ()
  "Return t if preceding line is a backslashed continuation line."
  `(save-excursion
     (beginning-of-line)
     (skip-chars-backward " \t\r\n\f")
     (and (eq (char-before (point)) ?\\ )
          (py-escaped))))

(defun py--escape-doublequotes (start end)
  "Escape doublequotes in region by START END."
  (let ((end (copy-marker end)))
    (save-excursion
      (goto-char start)
      (while (and (not (eobp)) (< 0 (abs (skip-chars-forward "^\"" end))))
	(when (eq (char-after) ?\")
	  (unless (py-escaped)
	    (insert "\\")
	    (forward-char 1)))))))

(defun py--escape-open-paren-col1 (start end)
  "Start from position START until position END."
  (goto-char start)
  ;; (switch-to-buffer (current-buffer))
  (while (re-search-forward "^(" end t 1)
    (insert "\\")
    (end-of-line)))

(and py-company-pycomplete-p (require 'company-pycomplete))

;; Macros
(defmacro empty-line-p ()
  "Return t if cursor is at an line with nothing but whitespace-characters, nil otherwise."
  `(save-excursion
     (progn
       (beginning-of-line)
       (looking-at "\\s-*$"))))



(require 'ansi-color)
(require 'cc-cmds)
(require 'cl)
(require 'comint)
(require 'compile)
(require 'custom)
(require 'flymake)
(require 'hippie-exp)
(require 'shell)
(require 'thingatpt)
(require 'which-func)

(defun py-define-menu (map)
  (easy-menu-define py-menu map "Py"
    `("Python"
      ("Interpreter"
       ["Ipython" ipython
	:help " `ipython'
Start an IPython interpreter."]

       ["Ipython2\.7" ipython2\.7
	:help " `ipython2\.7'"]

       ["Ipython3" ipython3
	:help " `ipython3'
Start an IPython3 interpreter."]

       ["Jython" jython
	:help " `jython'
Start an Jython interpreter."]

       ["Python" python
	:help " `python'
Start an Python interpreter."]

       ["Python2" python2
	:help " `python2'
Start an Python2 interpreter."]

       ["Python3" python3
	:help " `python3'
Start an Python3 interpreter."])
      ("Edit"
       ("Shift"
	("Shift right"
	 ["Shift block right" py-shift-block-right
	  :help " `py-shift-block-right'
Indent block by COUNT spaces."]

	 ["Shift block or clause right" py-shift-block-or-clause-right
	  :help " `py-shift-block-or-clause-right'
Indent block-or-clause by COUNT spaces."]

	 ["Shift class right" py-shift-class-right
	  :help " `py-shift-class-right'
Indent class by COUNT spaces."]

	 ["Shift clause right" py-shift-clause-right
	  :help " `py-shift-clause-right'
Indent clause by COUNT spaces."]

	 ["Shift comment right" py-shift-comment-right
	  :help " `py-shift-comment-right'
Indent comment by COUNT spaces."]

	 ["Shift def right" py-shift-def-right
	  :help " `py-shift-def-right'
Indent def by COUNT spaces."]

	 ["Shift def or class right" py-shift-def-or-class-right
	  :help " `py-shift-def-or-class-right'
Indent def-or-class by COUNT spaces."]

	 ["Shift indent right" py-shift-indent-right
	  :help " `py-shift-indent-right'
Indent indent by COUNT spaces."]

	 ["Shift minor block right" py-shift-minor-block-right
	  :help " `py-shift-minor-block-right'
Indent minor-block by COUNT spaces."]

	 ["Shift paragraph right" py-shift-paragraph-right
	  :help " `py-shift-paragraph-right'
Indent paragraph by COUNT spaces."]

	 ["Shift region right" py-shift-region-right
	  :help " `py-shift-region-right'
Indent region by COUNT spaces."]

	 ["Shift statement right" py-shift-statement-right
	  :help " `py-shift-statement-right'
Indent statement by COUNT spaces."]

	 ["Shift top level right" py-shift-top-level-right
	  :help " `py-shift-top-level-right'
Indent top-level by COUNT spaces."])
	("Shift left"
	 ["Shift block left" py-shift-block-left
	  :help " `py-shift-block-left'
Dedent block by COUNT spaces."]

	 ["Shift block or clause left" py-shift-block-or-clause-left
	  :help " `py-shift-block-or-clause-left'
Dedent block-or-clause by COUNT spaces."]

	 ["Shift class left" py-shift-class-left
	  :help " `py-shift-class-left'
Dedent class by COUNT spaces."]

	 ["Shift clause left" py-shift-clause-left
	  :help " `py-shift-clause-left'
Dedent clause by COUNT spaces."]

	 ["Shift comment left" py-shift-comment-left
	  :help " `py-shift-comment-left'
Dedent comment by COUNT spaces."]

	 ["Shift def left" py-shift-def-left
	  :help " `py-shift-def-left'
Dedent def by COUNT spaces."]

	 ["Shift def or class left" py-shift-def-or-class-left
	  :help " `py-shift-def-or-class-left'
Dedent def-or-class by COUNT spaces."]

	 ["Shift indent left" py-shift-indent-left
	  :help " `py-shift-indent-left'
Dedent indent by COUNT spaces."]

	 ["Shift minor block left" py-shift-minor-block-left
	  :help " `py-shift-minor-block-left'
Dedent minor-block by COUNT spaces."]

	 ["Shift paragraph left" py-shift-paragraph-left
	  :help " `py-shift-paragraph-left'
Dedent paragraph by COUNT spaces."]

	 ["Shift region left" py-shift-region-left
	  :help " `py-shift-region-left'
Dedent region by COUNT spaces."]

	 ["Shift statement left" py-shift-statement-left
	  :help " `py-shift-statement-left'
Dedent statement by COUNT spaces."]))
       ("Mark"
	["Mark block" py-mark-block
	 :help " `py-mark-block'
Mark block, take beginning of line positions."]

	["Mark block or clause" py-mark-block-or-clause
	 :help " `py-mark-block-or-clause'
Mark block-or-clause, take beginning of line positions."]

	["Mark class" py-mark-class
	 :help " `py-mark-class'
Mark class, take beginning of line positions."]

	["Mark clause" py-mark-clause
	 :help " `py-mark-clause'
Mark clause, take beginning of line positions."]

	["Mark comment" py-mark-comment
	 :help " `py-mark-comment'
Mark comment at point."]

	["Mark def" py-mark-def
	 :help " `py-mark-def'
Mark def, take beginning of line positions."]

	["Mark def or class" py-mark-def-or-class
	 :help " `py-mark-def-or-class'
Mark def-or-class, take beginning of line positions."]

	["Mark expression" py-mark-expression
	 :help " `py-mark-expression'
Mark expression at point."]

	["Mark except block" py-mark-except-block
	 :help " `py-mark-except-block'
Mark except-block, take beginning of line positions."]

	["Mark if block" py-mark-if-block
	 :help " `py-mark-if-block'
Mark if-block, take beginning of line positions."]

	["Mark indent" py-mark-indent
	 :help " `py-mark-indent'
Mark indent, take beginning of line positions."]

	["Mark line" py-mark-line
	 :help " `py-mark-line'
Mark line at point."]

	["Mark minor block" py-mark-minor-block
	 :help " `py-mark-minor-block'
Mark minor-block, take beginning of line positions."]

	["Mark partial expression" py-mark-partial-expression
	 :help " `py-mark-partial-expression'
Mark partial-expression at point."]

	["Mark paragraph" py-mark-paragraph
	 :help " `py-mark-paragraph'
Mark paragraph at point."]

	["Mark section" py-mark-section
	 :help " `py-mark-section'
Mark section at point."]

	["Mark statement" py-mark-statement
	 :help " `py-mark-statement'
Mark statement, take beginning of line positions."]

	["Mark top level" py-mark-top-level
	 :help " `py-mark-top-level'
Mark top-level, take beginning of line positions."]

	["Mark try block" py-mark-try-block
	 :help " `py-mark-try-block'
Mark try-block, take beginning of line positions."])
       ("Copy"
	["Copy block" py-copy-block
	 :help " `py-copy-block'
Copy block at point."]

	["Copy block or clause" py-copy-block-or-clause
	 :help " `py-copy-block-or-clause'
Copy block-or-clause at point."]

	["Copy class" py-copy-class
	 :help " `py-copy-class'
Copy class at point."]

	["Copy clause" py-copy-clause
	 :help " `py-copy-clause'
Copy clause at point."]

	["Copy comment" py-copy-comment
	 :help " `py-copy-comment'"]

	["Copy def" py-copy-def
	 :help " `py-copy-def'
Copy def at point."]

	["Copy def or class" py-copy-def-or-class
	 :help " `py-copy-def-or-class'
Copy def-or-class at point."]

	["Copy expression" py-copy-expression
	 :help " `py-copy-expression'
Copy expression at point."]

	["Copy except block" py-copy-except-block
	 :help " `py-copy-except-block'"]

	["Copy if block" py-copy-if-block
	 :help " `py-copy-if-block'"]

	["Copy indent" py-copy-indent
	 :help " `py-copy-indent'
Copy indent at point."]

	["Copy line" py-copy-line
	 :help " `py-copy-line'
Copy line at point."]

	["Copy minor block" py-copy-minor-block
	 :help " `py-copy-minor-block'
Copy minor-block at point."]

	["Copy partial expression" py-copy-partial-expression
	 :help " `py-copy-partial-expression'
Copy partial-expression at point."]

	["Copy paragraph" py-copy-paragraph
	 :help " `py-copy-paragraph'
Copy paragraph at point."]

	["Copy section" py-copy-section
	 :help " `py-copy-section'"]

	["Copy statement" py-copy-statement
	 :help " `py-copy-statement'
Copy statement at point."]

	["Copy top level" py-copy-top-level
	 :help " `py-copy-top-level'
Copy top-level at point."]

	["Copy try block" py-copy-try-block
	 :help " `py-copy-try-block'"])
       ("Kill"
	["Kill block" py-kill-block
	 :help " `py-kill-block'
Delete block at point."]

	["Kill block or clause" py-kill-block-or-clause
	 :help " `py-kill-block-or-clause'
Delete block-or-clause at point."]

	["Kill class" py-kill-class
	 :help " `py-kill-class'
Delete class at point."]

	["Kill clause" py-kill-clause
	 :help " `py-kill-clause'
Delete clause at point."]

	["Kill comment" py-kill-comment
	 :help " `py-kill-comment'
Delete comment at point."]

	["Kill def" py-kill-def
	 :help " `py-kill-def'
Delete def at point."]

	["Kill def or class" py-kill-def-or-class
	 :help " `py-kill-def-or-class'
Delete def-or-class at point."]

	["Kill expression" py-kill-expression
	 :help " `py-kill-expression'
Delete expression at point."]

	["Kill except block" py-kill-except-block
	 :help " `py-kill-except-block'
Delete except-block at point."]

	["Kill if block" py-kill-if-block
	 :help " `py-kill-if-block'
Delete if-block at point."]

	["Kill indent" py-kill-indent
	 :help " `py-kill-indent'
Delete indent at point."]

	["Kill line" py-kill-line
	 :help " `py-kill-line'
Delete line at point."]

	["Kill minor block" py-kill-minor-block
	 :help " `py-kill-minor-block'
Delete minor-block at point."]

	["Kill partial expression" py-kill-partial-expression
	 :help " `py-kill-partial-expression'
Delete partial-expression at point."]

	["Kill paragraph" py-kill-paragraph
	 :help " `py-kill-paragraph'
Delete paragraph at point."]

	["Kill section" py-kill-section
	 :help " `py-kill-section'
Delete section at point."]

	["Kill statement" py-kill-statement
	 :help " `py-kill-statement'
Delete statement at point."]

	["Kill top level" py-kill-top-level
	 :help " `py-kill-top-level'
Delete top-level at point."]

	["Kill try block" py-kill-try-block
	 :help " `py-kill-try-block'
Delete try-block at point."])
       ("Delete"
	["Delete block" py-delete-block
	 :help " `py-delete-block'
Delete BLOCK at point until beginning-of-line."]

	["Delete block or clause" py-delete-block-or-clause
	 :help " `py-delete-block-or-clause'
Delete BLOCK-OR-CLAUSE at point until beginning-of-line."]

	["Delete class" py-delete-class
	 :help " `py-delete-class'
Delete CLASS at point until beginning-of-line."]

	["Delete clause" py-delete-clause
	 :help " `py-delete-clause'
Delete CLAUSE at point until beginning-of-line."]

	["Delete comment" py-delete-comment
	 :help " `py-delete-comment'
Delete COMMENT at point."]

	["Delete def" py-delete-def
	 :help " `py-delete-def'
Delete DEF at point until beginning-of-line."]

	["Delete def or class" py-delete-def-or-class
	 :help " `py-delete-def-or-class'
Delete DEF-OR-CLASS at point until beginning-of-line."]

	["Delete expression" py-delete-expression
	 :help " `py-delete-expression'
Delete EXPRESSION at point."]

	["Delete except block" py-delete-except-block
	 :help " `py-delete-except-block'
Delete EXCEPT-BLOCK at point until beginning-of-line."]

	["Delete if block" py-delete-if-block
	 :help " `py-delete-if-block'
Delete IF-BLOCK at point until beginning-of-line."]

	["Delete indent" py-delete-indent
	 :help " `py-delete-indent'
Delete INDENT at point until beginning-of-line."]

	["Delete line" py-delete-line
	 :help " `py-delete-line'
Delete LINE at point."]

	["Delete minor block" py-delete-minor-block
	 :help " `py-delete-minor-block'
Delete MINOR-BLOCK at point until beginning-of-line."]

	["Delete partial expression" py-delete-partial-expression
	 :help " `py-delete-partial-expression'
Delete PARTIAL-EXPRESSION at point."]

	["Delete paragraph" py-delete-paragraph
	 :help " `py-delete-paragraph'
Delete PARAGRAPH at point."]

	["Delete section" py-delete-section
	 :help " `py-delete-section'
Delete SECTION at point."]

	["Delete statement" py-delete-statement
	 :help " `py-delete-statement'
Delete STATEMENT at point until beginning-of-line."]

	["Delete top level" py-delete-top-level
	 :help " `py-delete-top-level'
Delete TOP-LEVEL at point."]

	["Delete try block" py-delete-try-block
	 :help " `py-delete-try-block'
Delete TRY-BLOCK at point until beginning-of-line."])
       ("Comment"
	["Comment block" py-comment-block
	 :help " `py-comment-block'
Comments block at point."]

	["Comment block or clause" py-comment-block-or-clause
	 :help " `py-comment-block-or-clause'
Comments block-or-clause at point."]

	["Comment class" py-comment-class
	 :help " `py-comment-class'
Comments class at point."]

	["Comment clause" py-comment-clause
	 :help " `py-comment-clause'
Comments clause at point."]

	["Comment def" py-comment-def
	 :help " `py-comment-def'
Comments def at point."]

	["Comment def or class" py-comment-def-or-class
	 :help " `py-comment-def-or-class'
Comments def-or-class at point."]

	["Comment indent" py-comment-indent
	 :help " `py-comment-indent'
Comments indent at point."]

	["Comment minor block" py-comment-minor-block
	 :help " `py-comment-minor-block'
Comments minor-block at point."]

	["Comment section" py-comment-section
	 :help " `py-comment-section'
Comments section at point."]

	["Comment statement" py-comment-statement
	 :help " `py-comment-statement'
Comments statement at point."]

	["Comment top level" py-comment-top-level
	 :help " `py-comment-top-level'
Comments top-level at point."]))
      ("Move"
       ("Backward"
	["Backward block" py-backward-block
	 :help " `py-backward-block'
Go to beginning of ‘block’."]

	["Backward block or clause" py-backward-block-or-clause
	 :help " `py-backward-block-or-clause'
Go to beginning of ‘block-or-clause’."]

	["Backward class" py-backward-class
	 :help " `py-backward-class'
Go to beginning of class."]

	["Backward clause" py-backward-clause
	 :help " `py-backward-clause'
Go to beginning of ‘clause’."]

	["Backward def" py-backward-def
	 :help " `py-backward-def'
Go to beginning of def."]

	["Backward def or class" py-backward-def-or-class
	 :help " `py-backward-def-or-class'
Go to beginning of def-or-class."]

	["Backward elif block" py-backward-elif-block
	 :help " `py-backward-elif-block'
Go to beginning of ‘elif-block’."]

	["Backward else block" py-backward-else-block
	 :help " `py-backward-else-block'
Go to beginning of ‘else-block’."]

	["Backward except block" py-backward-except-block
	 :help " `py-backward-except-block'
Go to beginning of ‘except-block’."]

	["Backward expression" py-backward-expression
	 :help " `py-backward-expression'
Go to the beginning of a python expression."]

	["Backward for block" py-backward-for-block
	 :help " `py-backward-for-block'
Go to beginning of ‘for-block’."]

	["Backward if block" py-backward-if-block
	 :help " `py-backward-if-block'
Go to beginning of ‘if-block’."]

	["Backward indent" py-backward-indent
	 :help " `py-backward-indent'
Go to the beginning of a section of equal indent."]

	["Backward minor block" py-backward-minor-block
	 :help " `py-backward-minor-block'
Go to beginning of ‘minor-block’."]

	["Backward partial expression" py-backward-partial-expression
	 :help " `py-backward-partial-expression'"]

	["Backward section" py-backward-section
	 :help " `py-backward-section'
Go to next section start upward in buffer."]

	["Backward statement" py-backward-statement
	 :help " `py-backward-statement'
Go to the initial line of a simple statement."]

	["Backward top level" py-backward-top-level
	 :help " `py-backward-top-level'
Go up to beginning of statments until level of indentation is null."]

	["Backward try block" py-backward-try-block
	 :help " `py-backward-try-block'
Go to beginning of ‘try-block’."])
       ("Forward"
	["Forward block" py-forward-block
	 :help " `py-forward-block'
Go to end of block."]

	["Forward block or clause" py-forward-block-or-clause
	 :help " `py-forward-block-or-clause'
Go to end of block-or-clause."]

	["Forward class" py-forward-class
	 :help " `py-forward-class'
Go to end of class."]

	["Forward clause" py-forward-clause
	 :help " `py-forward-clause'
Go to end of clause."]

	["Forward def" py-forward-def
	 :help " `py-forward-def'
Go to end of def."]

	["Forward def or class" py-forward-def-or-class
	 :help " `py-forward-def-or-class'
Go to end of def-or-class."]

	["Forward elif block" py-forward-elif-block
	 :help " `py-forward-elif-block'
Go to end of elif-block."]

	["Forward else block" py-forward-else-block
	 :help " `py-forward-else-block'
Go to end of else-block."]

	["Forward except block" py-forward-except-block
	 :help " `py-forward-except-block'
Go to end of except-block."]

	["Forward expression" py-forward-expression
	 :help " `py-forward-expression'
Go to the end of a compound python expression."]

	["Forward for block" py-forward-for-block
	 :help " `py-forward-for-block'
Go to end of for-block."]

	["Forward if block" py-forward-if-block
	 :help " `py-forward-if-block'
Go to end of if-block."]

	["Forward indent" py-forward-indent
	 :help " `py-forward-indent'
Go to the end of a section of equal indentation."]

	["Forward minor block" py-forward-minor-block
	 :help " `py-forward-minor-block'
Go to end of minor-block."]

	["Forward partial expression" py-forward-partial-expression
	 :help " `py-forward-partial-expression'"]

	["Forward section" py-forward-section
	 :help " `py-forward-section'
Go to next section end downward in buffer."]

	["Forward statement" py-forward-statement
	 :help " `py-forward-statement'
Go to the last char of current statement."]

	["Forward top level" py-forward-top-level
	 :help " `py-forward-top-level'
Go to end of top-level form at point."]

	["Forward try block" py-forward-try-block
	 :help " `py-forward-try-block'
Go to end of try-block."])
       ("BOL-forms"
	("Backward"
	 ["Backward block bol" py-backward-block-bol
	  :help " `py-backward-block-bol'
Go to beginning of ‘block’, go to BOL."]

	 ["Backward block or clause bol" py-backward-block-or-clause-bol
	  :help " `py-backward-block-or-clause-bol'
Go to beginning of ‘block-or-clause’, go to BOL."]

	 ["Backward class bol" py-backward-class-bol
	  :help " `py-backward-class-bol'
Go to beginning of class, go to BOL."]

	 ["Backward clause bol" py-backward-clause-bol
	  :help " `py-backward-clause-bol'
Go to beginning of ‘clause’, go to BOL."]

	 ["Backward def bol" py-backward-def-bol
	  :help " `py-backward-def-bol'
Go to beginning of def, go to BOL."]

	 ["Backward def or class bol" py-backward-def-or-class-bol
	  :help " `py-backward-def-or-class-bol'
Go to beginning of def-or-class, go to BOL."]

	 ["Backward elif block bol" py-backward-elif-block-bol
	  :help " `py-backward-elif-block-bol'
Go to beginning of ‘elif-block’, go to BOL."]

	 ["Backward else block bol" py-backward-else-block-bol
	  :help " `py-backward-else-block-bol'
Go to beginning of ‘else-block’, go to BOL."]

	 ["Backward except block bol" py-backward-except-block-bol
	  :help " `py-backward-except-block-bol'
Go to beginning of ‘except-block’, go to BOL."]

	 ["Backward expression bol" py-backward-expression-bol
	  :help " `py-backward-expression-bol'"]

	 ["Backward for block bol" py-backward-for-block-bol
	  :help " `py-backward-for-block-bol'
Go to beginning of ‘for-block’, go to BOL."]

	 ["Backward if block bol" py-backward-if-block-bol
	  :help " `py-backward-if-block-bol'
Go to beginning of ‘if-block’, go to BOL."]

	 ["Backward indent bol" py-backward-indent-bol
	  :help " `py-backward-indent-bol'
Go to the beginning of line of a section of equal indent."]

	 ["Backward minor block bol" py-backward-minor-block-bol
	  :help " `py-backward-minor-block-bol'
Go to beginning of ‘minor-block’, go to BOL."]

	 ["Backward partial expression bol" py-backward-partial-expression-bol
	  :help " `py-backward-partial-expression-bol'"]

	 ["Backward section bol" py-backward-section-bol
	  :help " `py-backward-section-bol'"]

	 ["Backward statement bol" py-backward-statement-bol
	  :help " `py-backward-statement-bol'
Goto beginning of line where statement starts."]

	 ["Backward try block bol" py-backward-try-block-bol
	  :help " `py-backward-try-block-bol'
Go to beginning of ‘try-block’, go to BOL."])
	("Forward"
	 ["Forward block bol" py-forward-block-bol
	  :help " `py-forward-block-bol'
Goto beginning of line following end of block."]

	 ["Forward block or clause bol" py-forward-block-or-clause-bol
	  :help " `py-forward-block-or-clause-bol'
Goto beginning of line following end of block-or-clause."]

	 ["Forward class bol" py-forward-class-bol
	  :help " `py-forward-class-bol'
Goto beginning of line following end of class."]

	 ["Forward clause bol" py-forward-clause-bol
	  :help " `py-forward-clause-bol'
Goto beginning of line following end of clause."]

	 ["Forward def bol" py-forward-def-bol
	  :help " `py-forward-def-bol'
Goto beginning of line following end of def."]

	 ["Forward def or class bol" py-forward-def-or-class-bol
	  :help " `py-forward-def-or-class-bol'
Goto beginning of line following end of def-or-class."]

	 ["Forward elif block bol" py-forward-elif-block-bol
	  :help " `py-forward-elif-block-bol'
Goto beginning of line following end of elif-block."]

	 ["Forward else block bol" py-forward-else-block-bol
	  :help " `py-forward-else-block-bol'
Goto beginning of line following end of else-block."]

	 ["Forward except block bol" py-forward-except-block-bol
	  :help " `py-forward-except-block-bol'
Goto beginning of line following end of except-block."]

	 ["Forward expression bol" py-forward-expression-bol
	  :help " `py-forward-expression-bol'"]

	 ["Forward for block bol" py-forward-for-block-bol
	  :help " `py-forward-for-block-bol'
Goto beginning of line following end of for-block."]

	 ["Forward if block bol" py-forward-if-block-bol
	  :help " `py-forward-if-block-bol'
Goto beginning of line following end of if-block."]

	 ["Forward indent bol" py-forward-indent-bol
	  :help " `py-forward-indent-bol'
Go to beginning of line following of a section of equal indentation."]

	 ["Forward minor block bol" py-forward-minor-block-bol
	  :help " `py-forward-minor-block-bol'
Goto beginning of line following end of minor-block."]

	 ["Forward partial expression bol" py-forward-partial-expression-bol
	  :help " `py-forward-partial-expression-bol'"]

	 ["Forward section bol" py-forward-section-bol
	  :help " `py-forward-section-bol'"]

	 ["Forward statement bol" py-forward-statement-bol
	  :help " `py-forward-statement-bol'
Go to the beginning-of-line following current statement."]

	 ["Forward top level bol" py-forward-top-level-bol
	  :help " `py-forward-top-level-bol'
Go to end of top-level form at point, stop at next beginning-of-line."]

	 ["Forward try block bol" py-forward-try-block-bol
	  :help " `py-forward-try-block-bol'
Goto beginning of line following end of try-block."]))
       ("Up/Down"
	["Up" py-up
	 :help " `py-up'
Go up or to beginning of form if inside."]

	["Down" py-down
	 :help " `py-down'
Go to beginning one level below of compound statement or definition at point."]))
      ("Send"
       ["Execute block" py-execute-block
	:help " `py-execute-block'
Send block at point to interpreter."]

       ["Execute block or clause" py-execute-block-or-clause
	:help " `py-execute-block-or-clause'
Send block-or-clause at point to interpreter."]

       ["Execute buffer" py-execute-buffer
	:help " `py-execute-buffer'
:around advice: ‘ad-Advice-py-execute-buffer’"]

       ["Execute class" py-execute-class
	:help " `py-execute-class'
Send class at point to interpreter."]

       ["Execute clause" py-execute-clause
	:help " `py-execute-clause'
Send clause at point to interpreter."]

       ["Execute def" py-execute-def
	:help " `py-execute-def'
Send def at point to interpreter."]

       ["Execute def or class" py-execute-def-or-class
	:help " `py-execute-def-or-class'
Send def-or-class at point to interpreter."]

       ["Execute expression" py-execute-expression
	:help " `py-execute-expression'
Send expression at point to interpreter."]

       ["Execute indent" py-execute-indent
	:help " `py-execute-indent'
Send indent at point to interpreter."]

       ["Execute line" py-execute-line
	:help " `py-execute-line'
Send line at point to interpreter."]

       ["Execute minor block" py-execute-minor-block
	:help " `py-execute-minor-block'
Send minor-block at point to interpreter."]

       ["Execute paragraph" py-execute-paragraph
	:help " `py-execute-paragraph'
Send paragraph at point to interpreter."]

       ["Execute partial expression" py-execute-partial-expression
	:help " `py-execute-partial-expression'
Send partial-expression at point to interpreter."]

       ["Execute region" py-execute-region
	:help " `py-execute-region'
Send region at point to interpreter."]

       ["Execute statement" py-execute-statement
	:help " `py-execute-statement'
Send statement at point to interpreter."]

       ["Execute top level" py-execute-top-level
	:help " `py-execute-top-level'
Send top-level at point to interpreter."]
       ("Other"
	("IPython"
	 ["Execute block ipython" py-execute-block-ipython
	  :help " `py-execute-block-ipython'
Send block at point to IPython interpreter."]

	 ["Execute block or clause ipython" py-execute-block-or-clause-ipython
	  :help " `py-execute-block-or-clause-ipython'
Send block-or-clause at point to IPython interpreter."]

	 ["Execute buffer ipython" py-execute-buffer-ipython
	  :help " `py-execute-buffer-ipython'
Send buffer at point to IPython interpreter."]

	 ["Execute class ipython" py-execute-class-ipython
	  :help " `py-execute-class-ipython'
Send class at point to IPython interpreter."]

	 ["Execute clause ipython" py-execute-clause-ipython
	  :help " `py-execute-clause-ipython'
Send clause at point to IPython interpreter."]

	 ["Execute def ipython" py-execute-def-ipython
	  :help " `py-execute-def-ipython'
Send def at point to IPython interpreter."]

	 ["Execute def or class ipython" py-execute-def-or-class-ipython
	  :help " `py-execute-def-or-class-ipython'
Send def-or-class at point to IPython interpreter."]

	 ["Execute expression ipython" py-execute-expression-ipython
	  :help " `py-execute-expression-ipython'
Send expression at point to IPython interpreter."]

	 ["Execute indent ipython" py-execute-indent-ipython
	  :help " `py-execute-indent-ipython'
Send indent at point to IPython interpreter."]

	 ["Execute line ipython" py-execute-line-ipython
	  :help " `py-execute-line-ipython'
Send line at point to IPython interpreter."]

	 ["Execute minor block ipython" py-execute-minor-block-ipython
	  :help " `py-execute-minor-block-ipython'
Send minor-block at point to IPython interpreter."]

	 ["Execute paragraph ipython" py-execute-paragraph-ipython
	  :help " `py-execute-paragraph-ipython'
Send paragraph at point to IPython interpreter."]

	 ["Execute partial expression ipython" py-execute-partial-expression-ipython
	  :help " `py-execute-partial-expression-ipython'
Send partial-expression at point to IPython interpreter."]

	 ["Execute region ipython" py-execute-region-ipython
	  :help " `py-execute-region-ipython'
Send region at point to IPython interpreter."]

	 ["Execute statement ipython" py-execute-statement-ipython
	  :help " `py-execute-statement-ipython'
Send statement at point to IPython interpreter."]

	 ["Execute top level ipython" py-execute-top-level-ipython
	  :help " `py-execute-top-level-ipython'
Send top-level at point to IPython interpreter."])
	("IPython2\.7"
	 ["Execute block ipython2\.7" py-execute-block-ipython2\.7
	  :help " `py-execute-block-ipython2\.7'"]

	 ["Execute block or clause ipython2\.7" py-execute-block-or-clause-ipython2\.7
	  :help " `py-execute-block-or-clause-ipython2\.7'"]

	 ["Execute buffer ipython2\.7" py-execute-buffer-ipython2\.7
	  :help " `py-execute-buffer-ipython2\.7'"]

	 ["Execute class ipython2\.7" py-execute-class-ipython2\.7
	  :help " `py-execute-class-ipython2\.7'"]

	 ["Execute clause ipython2\.7" py-execute-clause-ipython2\.7
	  :help " `py-execute-clause-ipython2\.7'"]

	 ["Execute def ipython2\.7" py-execute-def-ipython2\.7
	  :help " `py-execute-def-ipython2\.7'"]

	 ["Execute def or class ipython2\.7" py-execute-def-or-class-ipython2\.7
	  :help " `py-execute-def-or-class-ipython2\.7'"]

	 ["Execute expression ipython2\.7" py-execute-expression-ipython2\.7
	  :help " `py-execute-expression-ipython2\.7'"]

	 ["Execute indent ipython2\.7" py-execute-indent-ipython2\.7
	  :help " `py-execute-indent-ipython2\.7'"]

	 ["Execute line ipython2\.7" py-execute-line-ipython2\.7
	  :help " `py-execute-line-ipython2\.7'"]

	 ["Execute minor block ipython2\.7" py-execute-minor-block-ipython2\.7
	  :help " `py-execute-minor-block-ipython2\.7'"]

	 ["Execute paragraph ipython2\.7" py-execute-paragraph-ipython2\.7
	  :help " `py-execute-paragraph-ipython2\.7'"]

	 ["Execute partial expression ipython2\.7" py-execute-partial-expression-ipython2\.7
	  :help " `py-execute-partial-expression-ipython2\.7'"]

	 ["Execute region ipython2\.7" py-execute-region-ipython2\.7
	  :help " `py-execute-region-ipython2\.7'"]

	 ["Execute statement ipython2\.7" py-execute-statement-ipython2\.7
	  :help " `py-execute-statement-ipython2\.7'"]

	 ["Execute top level ipython2\.7" py-execute-top-level-ipython2\.7
	  :help " `py-execute-top-level-ipython2\.7'"])
	("IPython3"
	 ["Execute block ipython3" py-execute-block-ipython3
	  :help " `py-execute-block-ipython3'
Send block at point to IPython interpreter."]

	 ["Execute block or clause ipython3" py-execute-block-or-clause-ipython3
	  :help " `py-execute-block-or-clause-ipython3'
Send block-or-clause at point to IPython interpreter."]

	 ["Execute buffer ipython3" py-execute-buffer-ipython3
	  :help " `py-execute-buffer-ipython3'
Send buffer at point to IPython interpreter."]

	 ["Execute class ipython3" py-execute-class-ipython3
	  :help " `py-execute-class-ipython3'
Send class at point to IPython interpreter."]

	 ["Execute clause ipython3" py-execute-clause-ipython3
	  :help " `py-execute-clause-ipython3'
Send clause at point to IPython interpreter."]

	 ["Execute def ipython3" py-execute-def-ipython3
	  :help " `py-execute-def-ipython3'
Send def at point to IPython interpreter."]

	 ["Execute def or class ipython3" py-execute-def-or-class-ipython3
	  :help " `py-execute-def-or-class-ipython3'
Send def-or-class at point to IPython interpreter."]

	 ["Execute expression ipython3" py-execute-expression-ipython3
	  :help " `py-execute-expression-ipython3'
Send expression at point to IPython interpreter."]

	 ["Execute indent ipython3" py-execute-indent-ipython3
	  :help " `py-execute-indent-ipython3'
Send indent at point to IPython interpreter."]

	 ["Execute line ipython3" py-execute-line-ipython3
	  :help " `py-execute-line-ipython3'
Send line at point to IPython interpreter."]

	 ["Execute minor block ipython3" py-execute-minor-block-ipython3
	  :help " `py-execute-minor-block-ipython3'
Send minor-block at point to IPython interpreter."]

	 ["Execute paragraph ipython3" py-execute-paragraph-ipython3
	  :help " `py-execute-paragraph-ipython3'
Send paragraph at point to IPython interpreter."]

	 ["Execute partial expression ipython3" py-execute-partial-expression-ipython3
	  :help " `py-execute-partial-expression-ipython3'
Send partial-expression at point to IPython interpreter."]

	 ["Execute region ipython3" py-execute-region-ipython3
	  :help " `py-execute-region-ipython3'
Send region at point to IPython interpreter."]

	 ["Execute statement ipython3" py-execute-statement-ipython3
	  :help " `py-execute-statement-ipython3'
Send statement at point to IPython interpreter."]

	 ["Execute top level ipython3" py-execute-top-level-ipython3
	  :help " `py-execute-top-level-ipython3'
Send top-level at point to IPython interpreter."])
	("Jython"
	 ["Execute block jython" py-execute-block-jython
	  :help " `py-execute-block-jython'
Send block at point to Jython interpreter."]

	 ["Execute block or clause jython" py-execute-block-or-clause-jython
	  :help " `py-execute-block-or-clause-jython'
Send block-or-clause at point to Jython interpreter."]

	 ["Execute buffer jython" py-execute-buffer-jython
	  :help " `py-execute-buffer-jython'
Send buffer at point to Jython interpreter."]

	 ["Execute class jython" py-execute-class-jython
	  :help " `py-execute-class-jython'
Send class at point to Jython interpreter."]

	 ["Execute clause jython" py-execute-clause-jython
	  :help " `py-execute-clause-jython'
Send clause at point to Jython interpreter."]

	 ["Execute def jython" py-execute-def-jython
	  :help " `py-execute-def-jython'
Send def at point to Jython interpreter."]

	 ["Execute def or class jython" py-execute-def-or-class-jython
	  :help " `py-execute-def-or-class-jython'
Send def-or-class at point to Jython interpreter."]

	 ["Execute expression jython" py-execute-expression-jython
	  :help " `py-execute-expression-jython'
Send expression at point to Jython interpreter."]

	 ["Execute indent jython" py-execute-indent-jython
	  :help " `py-execute-indent-jython'
Send indent at point to Jython interpreter."]

	 ["Execute line jython" py-execute-line-jython
	  :help " `py-execute-line-jython'
Send line at point to Jython interpreter."]

	 ["Execute minor block jython" py-execute-minor-block-jython
	  :help " `py-execute-minor-block-jython'
Send minor-block at point to Jython interpreter."]

	 ["Execute paragraph jython" py-execute-paragraph-jython
	  :help " `py-execute-paragraph-jython'
Send paragraph at point to Jython interpreter."]

	 ["Execute partial expression jython" py-execute-partial-expression-jython
	  :help " `py-execute-partial-expression-jython'
Send partial-expression at point to Jython interpreter."]

	 ["Execute region jython" py-execute-region-jython
	  :help " `py-execute-region-jython'
Send region at point to Jython interpreter."]

	 ["Execute statement jython" py-execute-statement-jython
	  :help " `py-execute-statement-jython'
Send statement at point to Jython interpreter."]

	 ["Execute top level jython" py-execute-top-level-jython
	  :help " `py-execute-top-level-jython'
Send top-level at point to Jython interpreter."])
	("Python"
	 ["Execute block python" py-execute-block-python
	  :help " `py-execute-block-python'
Send block at point to default interpreter."]

	 ["Execute block or clause python" py-execute-block-or-clause-python
	  :help " `py-execute-block-or-clause-python'
Send block-or-clause at point to default interpreter."]

	 ["Execute buffer python" py-execute-buffer-python
	  :help " `py-execute-buffer-python'
Send buffer at point to default interpreter."]

	 ["Execute class python" py-execute-class-python
	  :help " `py-execute-class-python'
Send class at point to default interpreter."]

	 ["Execute clause python" py-execute-clause-python
	  :help " `py-execute-clause-python'
Send clause at point to default interpreter."]

	 ["Execute def python" py-execute-def-python
	  :help " `py-execute-def-python'
Send def at point to default interpreter."]

	 ["Execute def or class python" py-execute-def-or-class-python
	  :help " `py-execute-def-or-class-python'
Send def-or-class at point to default interpreter."]

	 ["Execute expression python" py-execute-expression-python
	  :help " `py-execute-expression-python'
Send expression at point to default interpreter."]

	 ["Execute indent python" py-execute-indent-python
	  :help " `py-execute-indent-python'
Send indent at point to default interpreter."]

	 ["Execute line python" py-execute-line-python
	  :help " `py-execute-line-python'
Send line at point to default interpreter."]

	 ["Execute minor block python" py-execute-minor-block-python
	  :help " `py-execute-minor-block-python'
Send minor-block at point to default interpreter."]

	 ["Execute paragraph python" py-execute-paragraph-python
	  :help " `py-execute-paragraph-python'
Send paragraph at point to default interpreter."]

	 ["Execute partial expression python" py-execute-partial-expression-python
	  :help " `py-execute-partial-expression-python'
Send partial-expression at point to default interpreter."]

	 ["Execute region python" py-execute-region-python
	  :help " `py-execute-region-python'
Send region at point to default interpreter."]

	 ["Execute statement python" py-execute-statement-python
	  :help " `py-execute-statement-python'
Send statement at point to default interpreter."]

	 ["Execute top level python" py-execute-top-level-python
	  :help " `py-execute-top-level-python'
Send top-level at point to default interpreter."])
	("Python2"
	 ["Execute block python2" py-execute-block-python2
	  :help " `py-execute-block-python2'
Send block at point to Python2 interpreter."]

	 ["Execute block or clause python2" py-execute-block-or-clause-python2
	  :help " `py-execute-block-or-clause-python2'
Send block-or-clause at point to Python2 interpreter."]

	 ["Execute buffer python2" py-execute-buffer-python2
	  :help " `py-execute-buffer-python2'
Send buffer at point to Python2 interpreter."]

	 ["Execute class python2" py-execute-class-python2
	  :help " `py-execute-class-python2'
Send class at point to Python2 interpreter."]

	 ["Execute clause python2" py-execute-clause-python2
	  :help " `py-execute-clause-python2'
Send clause at point to Python2 interpreter."]

	 ["Execute def python2" py-execute-def-python2
	  :help " `py-execute-def-python2'
Send def at point to Python2 interpreter."]

	 ["Execute def or class python2" py-execute-def-or-class-python2
	  :help " `py-execute-def-or-class-python2'
Send def-or-class at point to Python2 interpreter."]

	 ["Execute expression python2" py-execute-expression-python2
	  :help " `py-execute-expression-python2'
Send expression at point to Python2 interpreter."]

	 ["Execute indent python2" py-execute-indent-python2
	  :help " `py-execute-indent-python2'
Send indent at point to Python2 interpreter."]

	 ["Execute line python2" py-execute-line-python2
	  :help " `py-execute-line-python2'
Send line at point to Python2 interpreter."]

	 ["Execute minor block python2" py-execute-minor-block-python2
	  :help " `py-execute-minor-block-python2'
Send minor-block at point to Python2 interpreter."]

	 ["Execute paragraph python2" py-execute-paragraph-python2
	  :help " `py-execute-paragraph-python2'
Send paragraph at point to Python2 interpreter."]

	 ["Execute partial expression python2" py-execute-partial-expression-python2
	  :help " `py-execute-partial-expression-python2'
Send partial-expression at point to Python2 interpreter."]

	 ["Execute region python2" py-execute-region-python2
	  :help " `py-execute-region-python2'
Send region at point to Python2 interpreter."]

	 ["Execute statement python2" py-execute-statement-python2
	  :help " `py-execute-statement-python2'
Send statement at point to Python2 interpreter."]

	 ["Execute top level python2" py-execute-top-level-python2
	  :help " `py-execute-top-level-python2'
Send top-level at point to Python2 interpreter."])
	("Python3"
	 ["Execute block python3" py-execute-block-python3
	  :help " `py-execute-block-python3'
Send block at point to Python3 interpreter."]

	 ["Execute block or clause python3" py-execute-block-or-clause-python3
	  :help " `py-execute-block-or-clause-python3'
Send block-or-clause at point to Python3 interpreter."]

	 ["Execute buffer python3" py-execute-buffer-python3
	  :help " `py-execute-buffer-python3'
Send buffer at point to Python3 interpreter."]

	 ["Execute class python3" py-execute-class-python3
	  :help " `py-execute-class-python3'
Send class at point to Python3 interpreter."]

	 ["Execute clause python3" py-execute-clause-python3
	  :help " `py-execute-clause-python3'
Send clause at point to Python3 interpreter."]

	 ["Execute def python3" py-execute-def-python3
	  :help " `py-execute-def-python3'
Send def at point to Python3 interpreter."]

	 ["Execute def or class python3" py-execute-def-or-class-python3
	  :help " `py-execute-def-or-class-python3'
Send def-or-class at point to Python3 interpreter."]

	 ["Execute expression python3" py-execute-expression-python3
	  :help " `py-execute-expression-python3'
Send expression at point to Python3 interpreter."]

	 ["Execute indent python3" py-execute-indent-python3
	  :help " `py-execute-indent-python3'
Send indent at point to Python3 interpreter."]

	 ["Execute line python3" py-execute-line-python3
	  :help " `py-execute-line-python3'
Send line at point to Python3 interpreter."]

	 ["Execute minor block python3" py-execute-minor-block-python3
	  :help " `py-execute-minor-block-python3'
Send minor-block at point to Python3 interpreter."]

	 ["Execute paragraph python3" py-execute-paragraph-python3
	  :help " `py-execute-paragraph-python3'
Send paragraph at point to Python3 interpreter."]

	 ["Execute partial expression python3" py-execute-partial-expression-python3
	  :help " `py-execute-partial-expression-python3'
Send partial-expression at point to Python3 interpreter."]

	 ["Execute region python3" py-execute-region-python3
	  :help " `py-execute-region-python3'
Send region at point to Python3 interpreter."]

	 ["Execute statement python3" py-execute-statement-python3
	  :help " `py-execute-statement-python3'
Send statement at point to Python3 interpreter."]

	 ["Execute top level python3" py-execute-top-level-python3
	  :help " `py-execute-top-level-python3'
Send top-level at point to Python3 interpreter."])
	("Ignoring defaults "
	 :help "`M-x py-execute-statement- TAB' for example list commands ignoring defaults

 of `py-switch-buffers-on-execute-p' and `py-split-window-on-execute'")))
      ("Hide-Show"
       ("Hide"
	["Hide block" py-hide-block
	 :help " `py-hide-block'
Hide block at point."]

	["Hide block or clause" py-hide-block-or-clause
	 :help " `py-hide-block-or-clause'
Hide block-or-clause at point."]

	["Hide class" py-hide-class
	 :help " `py-hide-class'
Hide class at point."]

	["Hide clause" py-hide-clause
	 :help " `py-hide-clause'
Hide clause at point."]

	["Hide comment" py-hide-comment
	 :help " `py-hide-comment'
Hide comment at point."]

	["Hide def" py-hide-def
	 :help " `py-hide-def'
Hide def at point."]

	["Hide def or class" py-hide-def-or-class
	 :help " `py-hide-def-or-class'
Hide def-or-class at point."]

	["Hide elif block" py-hide-elif-block
	 :help " `py-hide-elif-block'
Hide elif-block at point."]

	["Hide else block" py-hide-else-block
	 :help " `py-hide-else-block'
Hide else-block at point."]

	["Hide except block" py-hide-except-block
	 :help " `py-hide-except-block'
Hide except-block at point."]

	["Hide expression" py-hide-expression
	 :help " `py-hide-expression'
Hide expression at point."]

	["Hide for block" py-hide-for-block
	 :help " `py-hide-for-block'
Hide for-block at point."]

	["Hide if block" py-hide-if-block
	 :help " `py-hide-if-block'
Hide if-block at point."]

	["Hide indent" py-hide-indent
	 :help " `py-hide-indent'
Hide indent at point."]

	["Hide line" py-hide-line
	 :help " `py-hide-line'
Hide line at point."]

	["Hide minor block" py-hide-minor-block
	 :help " `py-hide-minor-block'
Hide minor-block at point."]

	["Hide minor block" py-hide-minor-block
	 :help " `py-hide-minor-block'
Hide minor-block at point."]

	["Hide paragraph" py-hide-paragraph
	 :help " `py-hide-paragraph'
Hide paragraph at point."]

	["Hide partial expression" py-hide-partial-expression
	 :help " `py-hide-partial-expression'
Hide partial-expression at point."]

	["Hide section" py-hide-section
	 :help " `py-hide-section'
Hide section at point."]

	["Hide statement" py-hide-statement
	 :help " `py-hide-statement'
Hide statement at point."]

	["Hide top level" py-hide-top-level
	 :help " `py-hide-top-level'
Hide top-level at point."])
       ("Show"
	["Show block" py-show-block
	 :help " `py-show-block'
Show block at point."]

	["Show block or clause" py-show-block-or-clause
	 :help " `py-show-block-or-clause'
Show block-or-clause at point."]

	["Show class" py-show-class
	 :help " `py-show-class'
Show class at point."]

	["Show clause" py-show-clause
	 :help " `py-show-clause'
Show clause at point."]

	["Show comment" py-show-comment
	 :help " `py-show-comment'
Show comment at point."]

	["Show def" py-show-def
	 :help " `py-show-def'
Show def at point."]

	["Show def or class" py-show-def-or-class
	 :help " `py-show-def-or-class'
Show def-or-class at point."]

	["Show elif block" py-show-elif-block
	 :help " `py-show-elif-block'
Show elif-block at point."]

	["Show else block" py-show-else-block
	 :help " `py-show-else-block'
Show else-block at point."]

	["Show except block" py-show-except-block
	 :help " `py-show-except-block'
Show except-block at point."]

	["Show expression" py-show-expression
	 :help " `py-show-expression'
Show expression at point."]

	["Show for block" py-show-for-block
	 :help " `py-show-for-block'
Show for-block at point."]

	["Show if block" py-show-if-block
	 :help " `py-show-if-block'
Show if-block at point."]

	["Show indent" py-show-indent
	 :help " `py-show-indent'
Show indent at point."]

	["Show line" py-show-line
	 :help " `py-show-line'
Show line at point."]

	["Show minor block" py-show-minor-block
	 :help " `py-show-minor-block'
Show minor-block at point."]

	["Show minor block" py-show-minor-block
	 :help " `py-show-minor-block'
Show minor-block at point."]

	["Show paragraph" py-show-paragraph
	 :help " `py-show-paragraph'
Show paragraph at point."]

	["Show partial expression" py-show-partial-expression
	 :help " `py-show-partial-expression'
Show partial-expression at point."]

	["Show section" py-show-section
	 :help " `py-show-section'
Show section at point."]

	["Show statement" py-show-statement
	 :help " `py-show-statement'
Show statement at point."]

	["Show top level" py-show-top-level
	 :help " `py-show-top-level'
Show top-level at point."]))
      ("Fast process"
       ["Execute block fast" py-execute-block-fast
	:help " `py-execute-block-fast'
Process block at point by a Python interpreter."]

       ["Execute block or clause fast" py-execute-block-or-clause-fast
	:help " `py-execute-block-or-clause-fast'
Process block-or-clause at point by a Python interpreter."]

       ["Execute class fast" py-execute-class-fast
	:help " `py-execute-class-fast'
Process class at point by a Python interpreter."]

       ["Execute clause fast" py-execute-clause-fast
	:help " `py-execute-clause-fast'
Process clause at point by a Python interpreter."]

       ["Execute def fast" py-execute-def-fast
	:help " `py-execute-def-fast'
Process def at point by a Python interpreter."]

       ["Execute def or class fast" py-execute-def-or-class-fast
	:help " `py-execute-def-or-class-fast'
Process def-or-class at point by a Python interpreter."]

       ["Execute expression fast" py-execute-expression-fast
	:help " `py-execute-expression-fast'
Process expression at point by a Python interpreter."]

       ["Execute partial expression fast" py-execute-partial-expression-fast
	:help " `py-execute-partial-expression-fast'
Process partial-expression at point by a Python interpreter."]

       ["Execute region fast" py-execute-region-fast
	:help " `py-execute-region-fast'"]

       ["Execute statement fast" py-execute-statement-fast
	:help " `py-execute-statement-fast'
Process statement at point by a Python interpreter."]

       ["Execute string fast" py-execute-string-fast
	:help " `py-execute-string-fast'"]

       ["Execute top level fast" py-execute-top-level-fast
	:help " `py-execute-top-level-fast'
Process top-level at point by a Python interpreter."])
      ("Virtualenv"
       ["Virtualenv activate" virtualenv-activate
	:help " `virtualenv-activate'
Activate the virtualenv located in DIR"]

       ["Virtualenv deactivate" virtualenv-deactivate
	:help " `virtualenv-deactivate'
Deactivate the current virtual enviroment"]

       ["Virtualenv p" virtualenv-p
	:help " `virtualenv-p'
Check if a directory is a virtualenv"]

       ["Virtualenv workon" virtualenv-workon
	:help " `virtualenv-workon'
Issue a virtualenvwrapper-like virtualenv-workon command"])

      ["Execute import or reload" py-execute-import-or-reload
       :help " `py-execute-import-or-reload'
Import the current buffer’s file in a Python interpreter."]
      ("Help"
       ["Find definition" py-find-definition
	:help " `py-find-definition'
Find source of definition of SYMBOL."]

       ["Help at point" py-help-at-point
	:help " `py-help-at-point'
Print help on symbol at point."]

       ["Info lookup symbol" py-info-lookup-symbol
	:help " `py-info-lookup-symbol'"]

       ["Symbol at point" py-symbol-at-point
	:help " `py-symbol-at-point'
Return the current Python symbol."])
      ("Debugger"
       ["Execute statement pdb" py-execute-statement-pdb
	:help " `py-execute-statement-pdb'
Execute statement running pdb."]

       ["Pdb" pdb
	:help " `pdb'
Run pdb on program FILE in buffer ‘*gud-FILE*’."])
      ("Checks"
       ["Flycheck mode" py-flycheck-mode
	:help " `py-flycheck-mode'
Toggle ‘flycheck-mode’."]

       ["Pychecker run" py-pychecker-run
	:help " `py-pychecker-run'
*Run pychecker (default on the file currently visited)."]
       ("Pylint"
	["Pylint run" py-pylint-run
	 :help " `py-pylint-run'
*Run pylint (default on the file currently visited)."]

	["Pylint help" py-pylint-help
	 :help " `py-pylint-help'
Display Pylint command line help messages."]

	["Pylint flymake mode" pylint-flymake-mode
	 :help " `pylint-flymake-mode'
Toggle ‘pylint’ ‘flymake-mode’."])
       ("Pep8"
	["Pep8 run" py-pep8-run
	 :help " `py-pep8-run'
*Run pep8, check formatting - default on the file currently visited."]

	["Pep8 help" py-pep8-help
	 :help " `py-pep8-help'
Display pep8 command line help messages."]

	["Pep8 flymake mode" pep8-flymake-mode
	 :help " `pep8-flymake-mode'
Toggle ‘pep8’ ‘flymake-mode’."])
       ("Pyflakes"
	["Pyflakes run" py-pyflakes-run
	 :help " `py-pyflakes-run'
*Run pyflakes (default on the file currently visited)."]

	["Pyflakes help" py-pyflakes-help
	 :help " `py-pyflakes-help'
Display Pyflakes command line help messages."]

	["Pyflakes flymake mode" pyflakes-flymake-mode
	 :help " `pyflakes-flymake-mode'
Toggle ‘pyflakes’ ‘flymake-mode’."])
       ("Flake8"
	["Flake8 run" py-flake8-run
	 :help " `py-flake8-run'
Flake8 is a wrapper around these tools:"]

	["Flake8 help" py-flake8-help
	 :help " `py-flake8-help'
Display flake8 command line help messages."]
	("Pyflakes-pep8"
	 ["Pyflakes pep8 run" py-pyflakes-pep8-run
	  :help " `py-pyflakes-pep8-run'"]

	 ["Pyflakes pep8 help" py-pyflakes-pep8-help
	  :help " `py-pyflakes-pep8-help'"]

	 ["Pyflakes pep8 flymake mode" pyflakes-pep8-flymake-mode
	  :help " `pyflakes-pep8-flymake-mode'"])))
      ("Customize"

       ["Python-mode customize group" (customize-group 'python-mode)
	:help "Open the customization buffer for Python mode"]
       ("Switches"
	:help "Toggle useful modes"
	("Interpreter"

	 ["Shell prompt read only"
	  (setq py-shell-prompt-read-only
		(not py-shell-prompt-read-only))
	  :help "If non-nil, the python prompt is read only.  Setting this variable will only effect new shells.Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-shell-prompt-read-only]

	 ["Remove cwd from path"
	  (setq py-remove-cwd-from-path
		(not py-remove-cwd-from-path))
	  :help "Whether to allow loading of Python modules from the current directory.
If this is non-nil, Emacs removes '' from sys.path when starting
a Python process.  This is the default, for security
reasons, as it is easy for the Python process to be started
without the user's realization (e.g. to perform completion).Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-remove-cwd-from-path]

	 ["Honor IPYTHONDIR "
	  (setq py-honor-IPYTHONDIR-p
		(not py-honor-IPYTHONDIR-p))
	  :help "When non-nil ipython-history file is constructed by \$IPYTHONDIR
followed by "/history". Default is nil.

Otherwise value of py-ipython-history is used. Use `M-x customize-variable' to set it permanently"
:style toggle :selected py-honor-IPYTHONDIR-p]

	 ["Honor PYTHONHISTORY "
	  (setq py-honor-PYTHONHISTORY-p
		(not py-honor-PYTHONHISTORY-p))
	  :help "When non-nil python-history file is set by \$PYTHONHISTORY
Default is nil.

Otherwise value of py-python-history is used. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-honor-PYTHONHISTORY-p]

	 ["Enforce py-shell-name" force-py-shell-name-p-on
	  :help "Enforce customized default `py-shell-name' should upon execution. "]

	 ["Don't enforce default interpreter" force-py-shell-name-p-off
	  :help "Make execute commands guess interpreter from environment"]

	 ["Enforce local Python shell " py-force-local-shell-on
	  :help "Locally indicated Python being enforced upon sessions execute commands. "]

	 ["Remove local Python shell enforcement, restore default" py-force-local-shell-off
	  :help "Restore `py-shell-name' default value and `behaviour'. "])

	("Execute"

	 ["Fast process" py-fast-process-p
	  :help " `py-fast-process-p'

Use `py-fast-process'\.

Commands prefixed \"py-fast-...\" suitable for large output

See: large output makes Emacs freeze, lp:1253907

Output-buffer is not in comint-mode"
	  :style toggle :selected py-fast-process-p]

	 ["Python mode v5 behavior"
	  (setq python-mode-v5-behavior-p
		(not python-mode-v5-behavior-p))
	  :help "Execute region through `shell-command-on-region' as
v5 did it - lp:990079. This might fail with certain chars - see UnicodeEncodeError lp:550661

Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected python-mode-v5-behavior-p]

	 ["Force shell name "
	  (setq py-force-py-shell-name-p
		(not py-force-py-shell-name-p))
	  :help "When `t', execution with kind of Python specified in `py-shell-name' is enforced, possibly shebang doesn't take precedence. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-force-py-shell-name-p]

	 ["Execute \"if name == main\" blocks p"
	  (setq py-if-name-main-permission-p
		(not py-if-name-main-permission-p))
	  :help " `py-if-name-main-permission-p'

Allow execution of code inside blocks delimited by
if __name__ == '__main__'

Default is non-nil. "
	  :style toggle :selected py-if-name-main-permission-p]

	 ["Ask about save"
	  (setq py-ask-about-save
		(not py-ask-about-save))
	  :help "If not nil, ask about which buffers to save before executing some code.
Otherwise, all modified buffers are saved without asking.Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-ask-about-save]

	 ["Store result"
	  (setq py-store-result-p
		(not py-store-result-p))
	  :help " `py-store-result-p'

When non-nil, put resulting string of `py-execute-...' into kill-ring, so it might be yanked. "
	  :style toggle :selected py-store-result-p]

	 ["Prompt on changed "
	  (setq py-prompt-on-changed-p
		(not py-prompt-on-changed-p))
	  :help "When called interactively, ask for save before a changed buffer is sent to interpreter.

Default is `t'Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-prompt-on-changed-p]

	 ["Dedicated process "
	  (setq py-dedicated-process-p
		(not py-dedicated-process-p))
	  :help "If commands executing code use a dedicated shell.

Default is nilUse `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-dedicated-process-p]

	 ["Execute without temporary file"
	  (setq py-execute-no-temp-p
		(not py-execute-no-temp-p))
	  :help " `py-execute-no-temp-p'
Seems Emacs-24.3 provided a way executing stuff without temporary files.
In experimental state yet "
	  :style toggle :selected py-execute-no-temp-p]

	 ["Warn tmp files left "
	  (setq py--warn-tmp-files-left-p
		(not py--warn-tmp-files-left-p))
	  :help "Messages a warning, when `py-temp-directory' contains files susceptible being left by previous Python-mode sessions. See also lp:987534 Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py--warn-tmp-files-left-p])

	("Edit"

	 ("Completion"

	  ["Set Pymacs-based complete keymap "
	   (setq py-set-complete-keymap-p
		 (not py-set-complete-keymap-p))
	   :help "If `py-complete-initialize', which sets up enviroment for Pymacs based py-complete, should load it's keys into `python-mode-map'

Default is nil.
See also resp. edit `py-complete-set-keymap' Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-set-complete-keymap-p]

	  ["Indent no completion "
	   (setq py-indent-no-completion-p
		 (not py-indent-no-completion-p))
	   :help "If completion function should indent when no completion found. Default is `t'

Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-indent-no-completion-p]

	  ["Company pycomplete "
	   (setq py-company-pycomplete-p
		 (not py-company-pycomplete-p))
	   :help "Load company-pycomplete stuff. Default is nilUse `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-company-pycomplete-p])

	 ("Filling"

	  ("Docstring styles"
	   :help "Switch docstring-style"

	   ["Nil" py-set-nil-docstring-style
	    :help " `py-set-nil-docstring-style'

Set py-docstring-style to nil, format string normally. "]

	   ["pep-257-nn" py-set-pep-257-nn-docstring-style
	    :help " `py-set-pep-257-nn-docstring-style'

Set py-docstring-style to 'pep-257-nn "]

	   ["pep-257" py-set-pep-257-docstring-style
	    :help " `py-set-pep-257-docstring-style'

Set py-docstring-style to 'pep-257 "]

	   ["django" py-set-django-docstring-style
	    :help " `py-set-django-docstring-style'

Set py-docstring-style to 'django "]

	   ["onetwo" py-set-onetwo-docstring-style
	    :help " `py-set-onetwo-docstring-style'

Set py-docstring-style to 'onetwo "]

	   ["symmetric" py-set-symmetric-docstring-style
	    :help " `py-set-symmetric-docstring-style'

Set py-docstring-style to 'symmetric "])

	  ["Auto-fill mode"
	   (setq py-auto-fill-mode
		 (not py-auto-fill-mode))
	   :help "Fill according to `py-docstring-fill-column' and `py-comment-fill-column'

Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-auto-fill-mode])

	 ["Use current dir when execute"
	  (setq py-use-current-dir-when-execute-p
		(not py-use-current-dir-when-execute-p))
	  :help " `toggle-py-use-current-dir-when-execute-p'

Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-use-current-dir-when-execute-p]

	 ("Indent"
	  ("TAB related"

	   ["indent-tabs-mode"
	    (setq indent-tabs-mode
		  (not indent-tabs-mode))
	    :help "Indentation can insert tabs if this is non-nil.

Use `M-x customize-variable' to set it permanently"
	    :style toggle :selected indent-tabs-mode]

	   ["Tab indent"
	    (setq py-tab-indent
		  (not py-tab-indent))
	    :help "Non-nil means TAB in Python mode calls `py-indent-line'.Use `M-x customize-variable' to set it permanently"
	    :style toggle :selected py-tab-indent]

	   ["Tab shifts region "
	    (setq py-tab-shifts-region-p
		  (not py-tab-shifts-region-p))
	    :help "If `t', TAB will indent/cycle the region, not just the current line.

Default is nil
See also `py-tab-indents-region-p'

Use `M-x customize-variable' to set it permanently"
	    :style toggle :selected py-tab-shifts-region-p]

	   ["Tab indents region "
	    (setq py-tab-indents-region-p
		  (not py-tab-indents-region-p))
	    :help "When `t' and first TAB doesn't shift, indent-region is called.

Default is nil
See also `py-tab-shifts-region-p'

Use `M-x customize-variable' to set it permanently"
	    :style toggle :selected py-tab-indents-region-p])

	  ["Close at start column"
	   (setq py-closing-list-dedents-bos
		 (not py-closing-list-dedents-bos))
	   :help "When non-nil, indent list's closing delimiter like start-column.

It will be lined up under the first character of
 the line that starts the multi-line construct, as in:

my_list = \[
    1, 2, 3,
    4, 5, 6,
]

Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-closing-list-dedents-bos]

	  ["Closing list keeps space"
	   (setq py-closing-list-keeps-space
		 (not py-closing-list-keeps-space))
	   :help "If non-nil, closing parenthesis dedents onto column of opening plus `py-closing-list-space', default is nil Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-closing-list-keeps-space]

	  ["Closing list space"
	   (setq py-closing-list-space
		 (not py-closing-list-space))
	   :help "Number of chars, closing parenthesis outdent from opening, default is 1 Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-closing-list-space]

	  ["Tab shifts region "
	   (setq py-tab-shifts-region-p
		 (not py-tab-shifts-region-p))
	   :help "If `t', TAB will indent/cycle the region, not just the current line.

Default is nil
See also `py-tab-indents-region-p'Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-tab-shifts-region-p]

	  ["Lhs inbound indent"
	   (setq py-lhs-inbound-indent
		 (not py-lhs-inbound-indent))
	   :help "When line starts a multiline-assignment: How many colums indent should be more than opening bracket, brace or parenthesis. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-lhs-inbound-indent]

	  ["Continuation offset"
	   (setq py-continuation-offset
		 (not py-continuation-offset))
	   :help "With numeric ARG different from 1 py-continuation-offset is set to that value; returns py-continuation-offset. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-continuation-offset]

	  ["Electric colon"
	   (setq py-electric-colon-active-p
		 (not py-electric-colon-active-p))
	   :help " `py-electric-colon-active-p'

`py-electric-colon' feature.  Default is `nil'. See lp:837065 for discussions. "
	   :style toggle :selected py-electric-colon-active-p]

	  ["Electric colon at beginning of block only"
	   (setq py-electric-colon-bobl-only
		 (not py-electric-colon-bobl-only))
	   :help "When inserting a colon, do not indent lines unless at beginning of block.

Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-electric-colon-bobl-only]

	  ["Electric yank active "
	   (setq py-electric-yank-active-p
		 (not py-electric-yank-active-p))
	   :help " When non-nil, `yank' will be followed by an `indent-according-to-mode'.

Default is nilUse `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-electric-yank-active-p]

	  ["Electric kill backward "
	   (setq py-electric-kill-backward-p
		 (not py-electric-kill-backward-p))
	   :help "Affects `py-electric-backspace'. Default is nil.

If behind a delimited form of braces, brackets or parentheses,
backspace will kill it's contents

With when cursor after
my_string\[0:1]
--------------^

==>

my_string\[]
----------^

In result cursor is insided emptied delimited form.Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-electric-kill-backward-p]

	  ["Trailing whitespace smart delete "
	   (setq py-trailing-whitespace-smart-delete-p
		 (not py-trailing-whitespace-smart-delete-p))
	   :help "Default is nil. When t, python-mode calls
    (add-hook 'before-save-hook 'delete-trailing-whitespace nil 'local)

Also commands may delete trailing whitespace by the way.
When editing other peoples code, this may produce a larger diff than expected Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-trailing-whitespace-smart-delete-p]

	  ["Newline delete trailing whitespace "
	   (setq py-newline-delete-trailing-whitespace-p
		 (not py-newline-delete-trailing-whitespace-p))
	   :help "Delete trailing whitespace maybe left by `py-newline-and-indent'.

Default is `t'. See lp:1100892 Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-newline-delete-trailing-whitespace-p]

	  ["Dedent keep relative column"
	   (setq py-dedent-keep-relative-column
		 (not py-dedent-keep-relative-column))
	   :help "If point should follow dedent or kind of electric move to end of line. Default is t - keep relative position. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-dedent-keep-relative-column]

	  ["Indent paren spanned multilines "
	   (setq py-indent-paren-spanned-multilines-p
		 (not py-indent-paren-spanned-multilines-p))
	   :help "If non-nil, indents elements of list a value of `py-indent-offset' to first element:

def foo():
    if (foo &&
            baz):
        bar()

Default lines up with first element:

def foo():
    if (foo &&
        baz):
        bar()
Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-indent-paren-spanned-multilines-p]

	  ["Indent honors multiline listing"
	   (setq py-indent-honors-multiline-listing
		 (not py-indent-honors-multiline-listing))
	   :help "If `t', indents to 1\+ column of opening delimiter. If `nil', indent adds one level to the beginning of statement. Default is `nil'. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-indent-honors-multiline-listing]

	  ["Indent comment "
	   (setq py-indent-comments
		 (not py-indent-comments))
	   :help "If comments should be indented like code. Default is `nil'.

Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-indent-comments]

	  ["Uncomment indents "
	   (setq py-uncomment-indents-p
		 (not py-uncomment-indents-p))
	   :help "When non-nil, after uncomment indent lines. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-uncomment-indents-p]

	  ["Indent honors inline comment"
	   (setq py-indent-honors-inline-comment
		 (not py-indent-honors-inline-comment))
	   :help "If non-nil, indents to column of inlined comment start.
Default is nil. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-indent-honors-inline-comment]

	  ["Kill empty line"
	   (setq py-kill-empty-line
		 (not py-kill-empty-line))
	   :help "If t, py-indent-forward-line kills empty lines. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-kill-empty-line]

	  ("Smart indentation"
	   :help "Toggle py-smart-indentation'

Use `M-x customize-variable' to set it permanently"

	   ["Toggle py-smart-indentation" toggle-py-smart-indentation
	    :help "Toggles py-smart-indentation

Use `M-x customize-variable' to set it permanently"]

	   ["py-smart-indentation on" py-smart-indentation-on
	    :help "Switches py-smart-indentation on

Use `M-x customize-variable' to set it permanently"]

	   ["py-smart-indentation off" py-smart-indentation-off
	    :help "Switches py-smart-indentation off

Use `M-x customize-variable' to set it permanently"])

	  ["Beep if tab change"
	   (setq py-beep-if-tab-change
		 (not py-beep-if-tab-change))
	   :help "Ring the bell if `tab-width' is changed.
If a comment of the form

                           	# vi:set tabsize=<number>:

is found before the first code line when the file is entered, and the
current value of (the general Emacs variable) `tab-width' does not
equal <number>, `tab-width' is set to <number>, a message saying so is
displayed in the echo area, and if `py-beep-if-tab-change' is non-nil
the Emacs bell is also rung as a warning.Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-beep-if-tab-change]

	  ["Electric comment "
	   (setq py-electric-comment-p
		 (not py-electric-comment-p))
	   :help "If \"#\" should call `py-electric-comment'. Default is `nil'.

Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-electric-comment-p]

	  ["Electric comment add space "
	   (setq py-electric-comment-add-space-p
		 (not py-electric-comment-add-space-p))
	   :help "If py-electric-comment should add a space.  Default is `nil'. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-electric-comment-add-space-p]

	  ["Empty line closes "
	   (setq py-empty-line-closes-p
		 (not py-empty-line-closes-p))
	   :help "When non-nil, dedent after empty line following block

if True:
    print(\"Part of the if-statement\")

print(\"Not part of the if-statement\")

Default is nil

If non-nil, a C-j from empty line dedents.
Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-empty-line-closes-p])
	 ["Defun use top level "
	  (setq py-defun-use-top-level-p
		(not py-defun-use-top-level-p))
	  :help "When non-nil, keys C-M-a, C-M-e address top-level form.

Beginning- end-of-defun forms use
commands `py-backward-top-level', `py-forward-top-level'

mark-defun marks top-level form at point etc. "
	  :style toggle :selected py-defun-use-top-level-p]

	 ["Close provides newline"
	  (setq py-close-provides-newline
		(not py-close-provides-newline))
	  :help "If a newline is inserted, when line after block isn't empty. Default is non-nil. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-close-provides-newline]

	 ["Block comment prefix "
	  (setq py-block-comment-prefix-p
		(not py-block-comment-prefix-p))
	  :help "If py-comment inserts py-block-comment-prefix.

Default is tUse `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-block-comment-prefix-p])

	("Display"

	 ("Index"

	  ["Imenu create index "
	   (setq py--imenu-create-index-p
		 (not py--imenu-create-index-p))
	   :help "Non-nil means Python mode creates and displays an index menu of functions and global variables. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py--imenu-create-index-p]

	  ["Imenu show method args "
	   (setq py-imenu-show-method-args-p
		 (not py-imenu-show-method-args-p))
	   :help "Controls echoing of arguments of functions & methods in the Imenu buffer.
When non-nil, arguments are printed.Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-imenu-show-method-args-p]
	  ["Switch index-function" py-switch-imenu-index-function
	   :help "`py-switch-imenu-index-function'
Switch between `py--imenu-create-index' from 5.1 series and `py--imenu-create-index-new'."])

	 ("Fontification"

	  ["Mark decorators"
	   (setq py-mark-decorators
		 (not py-mark-decorators))
	   :help "If py-mark-def-or-class functions should mark decorators too. Default is `nil'. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-mark-decorators]

	  ["Fontify shell buffer "
	   (setq py-fontify-shell-buffer-p
		 (not py-fontify-shell-buffer-p))
	   :help "If code in Python shell should be highlighted as in script buffer.

Default is nil.

If `t', related vars like `comment-start' will be set too.
Seems convenient when playing with stuff in IPython shell
Might not be TRT when a lot of output arrives Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-fontify-shell-buffer-p]

	  ["Use font lock doc face "
	   (setq py-use-font-lock-doc-face-p
		 (not py-use-font-lock-doc-face-p))
	   :help "If documention string inside of def or class get `font-lock-doc-face'.

`font-lock-doc-face' inherits `font-lock-string-face'.

Call M-x `customize-face' in order to have a visible effect. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-use-font-lock-doc-face-p])

	 ["Switch buffers on execute"
	  (setq py-switch-buffers-on-execute-p
		(not py-switch-buffers-on-execute-p))
	  :help "When non-nil switch to the Python output buffer.

Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-switch-buffers-on-execute-p]

	 ["Split windows on execute"
	  (setq py-split-window-on-execute
		(not py-split-window-on-execute))
	  :help "When non-nil split windows.

Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-split-window-on-execute]

	 ["Keep windows configuration"
	  (setq py-keep-windows-configuration
		(not py-keep-windows-configuration))
	  :help "If a windows is splitted displaying results, this is directed by variable `py-split-window-on-execute'\. Also setting `py-switch-buffers-on-execute-p' affects window-configuration\. While commonly a screen splitted into source and Python-shell buffer is assumed, user may want to keep a different config\.

Setting `py-keep-windows-configuration' to `t' will restore windows-config regardless of settings mentioned above\. However, if an error occurs, it's displayed\.

To suppres window-changes due to error-signaling also: M-x customize-variable RET. Set `py-keep-4windows-configuration' onto 'force

Default is nil Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-keep-windows-configuration]

	 ["Which split windows on execute function"
	  (progn
	    (if (eq 'split-window-vertically py-split-windows-on-execute-function)
		(setq py-split-windows-on-execute-function'split-window-horizontally)
	      (setq py-split-windows-on-execute-function 'split-window-vertically))
	    (message "py-split-windows-on-execute-function set to: %s" py-split-windows-on-execute-function))

	  :help "If `split-window-vertically' or `...-horizontally'. Use `M-x customize-variable' RET `py-split-windows-on-execute-function' RET to set it permanently"
	  :style toggle :selected py-split-windows-on-execute-function]

	 ["Modeline display full path "
	  (setq py-modeline-display-full-path-p
		(not py-modeline-display-full-path-p))
	  :help "If the full PATH/TO/PYTHON should be displayed in shell modeline.

Default is nil. Note: when `py-shell-name' is specified with path, it's shown as an acronym in buffer-name already. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-modeline-display-full-path-p]

	 ["Modeline acronym display home "
	  (setq py-modeline-acronym-display-home-p
		(not py-modeline-acronym-display-home-p))
	  :help "If the modeline acronym should contain chars indicating the home-directory.

Default is nil Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-modeline-acronym-display-home-p]

	 ["Hide show hide docstrings"
	  (setq py-hide-show-hide-docstrings
		(not py-hide-show-hide-docstrings))
	  :help "Controls if doc strings can be hidden by hide-showUse `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-hide-show-hide-docstrings]

	 ["Hide comments when hiding all"
	  (setq py-hide-comments-when-hiding-all
		(not py-hide-comments-when-hiding-all))
	  :help "Hide the comments too when you do `hs-hide-all'. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-hide-comments-when-hiding-all]

	 ["Max help buffer "
	  (setq py-max-help-buffer-p
		(not py-max-help-buffer-p))
	  :help "If \"\*Python-Help\*\"-buffer should appear as the only visible.

Default is nil. In help-buffer, \"q\" will close it.  Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-max-help-buffer-p]

	 ["Current defun show"
	  (setq py-current-defun-show
		(not py-current-defun-show))
	  :help "If `py-current-defun' should jump to the definition, highlight it while waiting PY-WHICH-FUNC-DELAY seconds, before returning to previous position.

Default is `t'.Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-current-defun-show]

	 ["Match paren mode"
	  (setq py-match-paren-mode
		(not py-match-paren-mode))
	  :help "Non-nil means, cursor will jump to beginning or end of a block.
This vice versa, to beginning first.
Sets `py-match-paren-key' in python-mode-map.
Customize `py-match-paren-key' which key to use. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-match-paren-mode])

	("Debug"

	 ["py-debug-p"
	  (setq py-debug-p
		(not py-debug-p))
	  :help "When non-nil, keep resp\. store information useful for debugging\.

Temporary files are not deleted\. Other functions might implement
some logging etc\. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-debug-p]

	 ["Pdbtrack do tracking "
	  (setq py-pdbtrack-do-tracking-p
		(not py-pdbtrack-do-tracking-p))
	  :help "Controls whether the pdbtrack feature is enabled or not.
When non-nil, pdbtrack is enabled in all comint-based buffers,
e.g. shell buffers and the \*Python\* buffer.  When using pdb to debug a
Python program, pdbtrack notices the pdb prompt and displays the
source file and line that the program is stopped at, much the same way
as gud-mode does for debugging C programs with gdb.Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-pdbtrack-do-tracking-p]

	 ["Jump on exception"
	  (setq py-jump-on-exception
		(not py-jump-on-exception))
	  :help "Jump to innermost exception frame in Python output buffer.
When this variable is non-nil and an exception occurs when running
Python code synchronously in a subprocess, jump immediately to the
source code of the innermost traceback frame.

Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-jump-on-exception]

	 ["Highlight error in source "
	  (setq py-highlight-error-source-p
		(not py-highlight-error-source-p))
	  :help "Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-highlight-error-source-p])

	("Other"

	 ("Directory"

	  ["Guess install directory "
	   (setq py-guess-py-install-directory-p
		 (not py-guess-py-install-directory-p))
	   :help "If in cases, `py-install-directory' isn't set,  `py-set-load-path'should guess it from `buffer-file-name'. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-guess-py-install-directory-p]

	  ["Use local default"
	   (setq py-use-local-default
		 (not py-use-local-default))
	   :help "If `t', py-shell will use `py-shell-local-path' instead
of default Python.

Making switch between several virtualenv's easier,
                               `python-mode' should deliver an installer, so named-shells pointing to virtualenv's will be available. Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-use-local-default]

	  ["Use current dir when execute "
	   (setq py-use-current-dir-when-execute-p
		 (not py-use-current-dir-when-execute-p))
	   :help "When `t', current directory is used by Python-shell for output of `py-execute-buffer' and related commands.

See also `py-execute-directory'Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-use-current-dir-when-execute-p]

	  ["Keep shell dir when execute "
	   (setq py-keep-shell-dir-when-execute-p
		 (not py-keep-shell-dir-when-execute-p))
	   :help "Don't change Python shell's current working directory when sending code.

See also `py-execute-directory'Use `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-keep-shell-dir-when-execute-p]

	  ["Fileless buffer use default directory "
	   (setq py-fileless-buffer-use-default-directory-p
		 (not py-fileless-buffer-use-default-directory-p))
	   :help "When `py-use-current-dir-when-execute-p' is non-nil and no buffer-file exists, value of `default-directory' sets current working directory of Python output shellUse `M-x customize-variable' to set it permanently"
	   :style toggle :selected py-fileless-buffer-use-default-directory-p])

	 ("Underscore word syntax"
	  :help "Toggle `py-underscore-word-syntax-p'"

	  ["Toggle underscore word syntax" toggle-py-underscore-word-syntax-p
	   :help " `toggle-py-underscore-word-syntax-p'

If `py-underscore-word-syntax-p' should be on or off.

  Returns value of `py-underscore-word-syntax-p' switched to. .

Use `M-x customize-variable' to set it permanently"]

	  ["Underscore word syntax on" py-underscore-word-syntax-p-on
	   :help " `py-underscore-word-syntax-p-on'

Make sure, py-underscore-word-syntax-p' is on.

Returns value of `py-underscore-word-syntax-p'. .

Use `M-x customize-variable' to set it permanently"]

	  ["Underscore word syntax off" py-underscore-word-syntax-p-off
	   :help " `py-underscore-word-syntax-p-off'

Make sure, `py-underscore-word-syntax-p' is off.

Returns value of `py-underscore-word-syntax-p'. .

Use `M-x customize-variable' to set it permanently"])

	 ["Load pymacs "
	  (setq py-load-pymacs-p
		(not py-load-pymacs-p))
	  :help "If Pymacs related stuff should be loaded.

Default is nil.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.caUse `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-load-pymacs-p]

	 ["Verbose "
	  (setq py-verbose-p
		(not py-verbose-p))
	  :help "If functions should report results.

Default is nil. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-verbose-p]

	 ["Empty comment line separates paragraph "
	  (setq py-empty-comment-line-separates-paragraph-p
		(not py-empty-comment-line-separates-paragraph-p))
	  :help "Consider paragraph start/end lines with nothing inside but comment sign.

Default is non-nilUse `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-empty-comment-line-separates-paragraph-p]

	 ["Org cycle "
	  (setq py-org-cycle-p
		(not py-org-cycle-p))
	  :help "When non-nil, command `org-cycle' is available at shift-TAB, <backtab>

Default is nil. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-org-cycle-p]

	 ["Set pager cat"
	  (setq py-set-pager-cat-p
		(not py-set-pager-cat-p))
	  :help "If the shell environment variable \$PAGER should set to `cat'.

If `t', use `C-c C-r' to jump to beginning of output. Then scroll normally.

Avoids lp:783828, \"Terminal not fully functional\", for help('COMMAND') in python-shell

When non-nil, imports module `os' Use `M-x customize-variable' to
set it permanently"
	  :style toggle :selected py-set-pager-cat-p]

	 ["Edit only "
	  (setq py-edit-only-p
		(not py-edit-only-p))
	  :help "When `t' `python-mode' will not take resort nor check for installed Python executables. Default is nil.

See bug report at launchpad, lp:944093. Use `M-x customize-variable' to set it permanently"
	  :style toggle :selected py-edit-only-p])))
      ("Other"
       ["Boolswitch" py-boolswitch
	:help " `py-boolswitch'
Edit the assignment of a boolean variable, revert them."]

       ["Empty out list backward" py-empty-out-list-backward
	:help " `py-empty-out-list-backward'
Deletes all elements from list before point."]

       ["Kill buffer unconditional" py-kill-buffer-unconditional
	:help " `py-kill-buffer-unconditional'
Kill buffer unconditional, kill buffer-process if existing."]

       ["Remove overlays at point" py-remove-overlays-at-point
	:help " `py-remove-overlays-at-point'
Remove overlays as set when ‘py-highlight-error-source-p’ is non-nil."]
       ("Electric"
	["Complete electric comma" py-complete-electric-comma
	 :help " `py-complete-electric-comma'"]

	["Complete electric lparen" py-complete-electric-lparen
	 :help " `py-complete-electric-lparen'"]

	["Electric backspace" py-electric-backspace
	 :help " `py-electric-backspace'
Delete preceding character or level of indentation."]

	["Electric colon" py-electric-colon
	 :help " `py-electric-colon'
Insert a colon and indent accordingly."]

	["Electric comment" py-electric-comment
	 :help " `py-electric-comment'
Insert a comment. If starting a comment, indent accordingly."]

	["Electric delete" py-electric-delete
	 :help " `py-electric-delete'
Delete following character or levels of whitespace."]

	["Electric yank" py-electric-yank
	 :help " `py-electric-yank'
Perform command ‘yank’ followed by an ‘indent-according-to-mode’"]

	["Hungry delete backwards" py-hungry-delete-backwards
	 :help " `py-hungry-delete-backwards'
Delete the preceding character or all preceding whitespace"]

	["Hungry delete forward" py-hungry-delete-forward
	 :help " `py-hungry-delete-forward'
Delete the following character or all following whitespace"])
       ("Filling"
	["Py docstring style" py-py-docstring-style
	 :help " `py-py-docstring-style'"]

	["Py fill comment" py-py-fill-comment
	 :help " `py-py-fill-comment'"]

	["Py fill paragraph" py-py-fill-paragraph
	 :help " `py-py-fill-paragraph'"]

	["Py fill string" py-py-fill-string
	 :help " `py-py-fill-string'"]

	["Py fill string django" py-py-fill-string-django
	 :help " `py-py-fill-string-django'"]

	["Py fill string onetwo" py-py-fill-string-onetwo
	 :help " `py-py-fill-string-onetwo'"]

	["Py fill string pep 257" py-py-fill-string-pep-257
	 :help " `py-py-fill-string-pep-257'"]

	["Py fill string pep 257 nn" py-py-fill-string-pep-257-nn
	 :help " `py-py-fill-string-pep-257-nn'"]

	["Py fill string symmetric" py-py-fill-string-symmetric
	 :help " `py-py-fill-string-symmetric'"])
       ("Abbrevs"	   :help "see also `py-add-abbrev'"
	:filter (lambda (&rest junk)
		  (abbrev-table-menu python-mode-abbrev-table)))

       ["Add abbrev" py-add-abbrev
	:help " `py-add-abbrev'
Defines python-mode specific abbrev for last expressions before point."]
       ("Completion"
	["Py indent or complete" py-py-indent-or-complete
	 :help " `py-py-indent-or-complete'"]

	["Py shell complete" py-py-shell-complete
	 :help " `py-py-shell-complete'"]

	["Py complete" py-py-complete
	 :help " `py-py-complete'"])

       ["Find function" py-find-function
	:help " `py-find-function'
Find source of definition of SYMBOL."])))
  map)

;; python-components-map

(defvar py-use-menu-p t
  "If the menu should be loaded.

Default is t")

(defvar py-menu nil
  "Make a dynamically bound variable ‘py-menu’.")

(defvar python-mode-map nil)
(setq python-mode-map
      (let ((map (make-sparse-keymap)))
        ;; electric keys
        (define-key map [(:)] 'py-electric-colon)
        (define-key map [(\#)] 'py-electric-comment)
        (define-key map [(delete)] 'py-electric-delete)
        (define-key map [(backspace)] 'py-electric-backspace)
        (define-key map [(control backspace)] 'py-hungry-delete-backwards)
        (define-key map [(control c) (delete)] 'py-hungry-delete-forward)
        ;; (define-key map [(control y)] 'py-electric-yank)
        ;; moving point
        (define-key map [(control c)(control p)] 'py-backward-statement)
        (define-key map [(control c)(control n)] 'py-forward-statement)
        (define-key map [(control c)(control u)] 'py-backward-block)
        (define-key map [(control c)(control q)] 'py-forward-block)
        (define-key map [(control meta a)] 'py-backward-def-or-class)
        (define-key map [(control meta e)] 'py-forward-def-or-class)

        ;; (define-key map [(meta i)] 'py-indent-forward-line)
        (define-key map [(control j)] 'py-newline-and-indent)
        ;; Most Pythoneers expect RET `py-newline-and-indent'
        ;; (define-key map (kbd "RET") 'py-newline-and-dedent)
        (define-key map (kbd "RET") py-return-key)
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
        ;; (define-key map [(super q)] 'py-copy-statement)
        (define-key map [(control c)(control d)] 'py-pdbtrack-toggle-stack-tracking)
        (define-key map [(control c)(control f)] 'py-sort-imports)
        (define-key map [(control c)(\#)] 'py-comment-region)
        (define-key map [(control c)(\?)] 'py-describe-mode)
        (define-key map [(control c)(control e)] 'py-help-at-point)
        (define-key map [(control c)(-)] 'py-up-exception)
        (define-key map [(control c)(=)] 'py-down-exception)
        (define-key map [(control x) (n) (d)] 'py-narrow-to-defun)
        ;; information
        (define-key map [(control c)(control b)] 'py-submit-bug-report)
        (define-key map [(control c)(control v)] 'py-version)
        (define-key map [(control c)(control w)] 'py-pychecker-run)
        ;; (define-key map (kbd "TAB") 'py-indent-line)
        (define-key map (kbd "TAB") 'py-indent-or-complete)
	;; (if py-complete-function
        ;;     (progn
        ;;       (define-key map [(meta tab)] py-complete-function)
        ;;       (define-key map [(esc) (tab)] py-complete-function))
        ;;   (define-key map [(meta tab)] 'py-shell-complete)
        ;;   (define-key map [(esc) (tab)] 'py-shell-complete))
        (substitute-key-definition 'complete-symbol 'completion-at-point
                                   map global-map)
        (substitute-key-definition 'backward-up-list 'py-up
                                   map global-map)
        (substitute-key-definition 'down-list 'py-down
                                   map global-map)
	(when py-use-menu-p
	  (setq map (py-define-menu map)))
        map))

(defvaralias 'py-mode-map 'python-mode-map)

(defvar py-python-shell-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") 'comint-send-input)
    (define-key map [(control c)(-)] 'py-up-exception)
    (define-key map [(control c)(=)] 'py-down-exception)
    (define-key map (kbd "TAB") 'py-indent-or-complete)
    (define-key map [(meta tab)] 'py-shell-complete)
    (define-key map [(control c)(!)] 'py-shell)
    (define-key map [(control c)(control t)] 'py-toggle-shell)
    ;; electric keys
    ;; (define-key map [(:)] 'py-electric-colon)
    ;; (define-key map [(\#)] 'py-electric-comment)
    ;; (define-key map [(delete)] 'py-electric-delete)
    ;; (define-key map [(backspace)] 'py-electric-backspace)
    ;; (define-key map [(control backspace)] 'py-hungry-delete-backwards)
    ;; (define-key map [(control c) (delete)] 'py-hungry-delete-forward)
    ;; (define-key map [(control y)] 'py-electric-yank)
    ;; moving point
    (define-key map [(control c)(control p)] 'py-backward-statement)
    (define-key map [(control c)(control n)] 'py-forward-statement)
    (define-key map [(control c)(control u)] 'py-backward-block)
    (define-key map [(control c)(control q)] 'py-forward-block)
    (define-key map [(control meta a)] 'py-backward-def-or-class)
    (define-key map [(control meta e)] 'py-forward-def-or-class)
    (define-key map [(control j)] 'py-newline-and-indent)
    (define-key map [(super backspace)] 'py-dedent)
    ;; (define-key map [(control return)] 'py-newline-and-dedent)
    ;; indentation level modifiers
    (define-key map [(control c)(control l)] 'comint-dynamic-list-input-ring)
    (define-key map [(control c)(control r)] 'comint-previous-prompt)
    (define-key map [(control c)(<)] 'py-shift-left)
    (define-key map [(control c)(>)] 'py-shift-right)
    (define-key map [(control c)(tab)] 'py-indent-region)
    (define-key map [(control c)(:)] 'py-guess-indent-offset)
    ;; subprocess commands
    (define-key map [(control meta h)] 'py-mark-def-or-class)
    (define-key map [(control c)(control k)] 'py-mark-block-or-clause)
    (define-key map [(control c)(.)] 'py-expression)
    ;; Miscellaneous
    ;; (define-key map [(super q)] 'py-copy-statement)
    (define-key map [(control c)(control d)] 'py-pdbtrack-toggle-stack-tracking)
    (define-key map [(control c)(\#)] 'py-comment-region)
    (define-key map [(control c)(\?)] 'py-describe-mode)
    (define-key map [(control c)(control e)] 'py-help-at-point)
    (define-key map [(control x) (n) (d)] 'py-narrow-to-defun)
    ;; information
    (define-key map [(control c)(control b)] 'py-submit-bug-report)
    (define-key map [(control c)(control v)] 'py-version)
    (define-key map [(control c)(control w)] 'py-pychecker-run)
    (substitute-key-definition 'complete-symbol 'completion-at-point
			       map global-map)
    (substitute-key-definition 'backward-up-list 'py-up
			       map global-map)
    (substitute-key-definition 'down-list 'py-down
			       map global-map)
    map)
  "Used inside a Python-shell.")

(defvar py-ipython-shell-mode-map py-python-shell-mode-map
  "Unless setting of ipython-shell-mode needs to be different, let's save some lines of code and copy ‘py-python-shell-mode-map’ here.")

(defvar py-shell-map py-python-shell-mode-map)

(setq python-font-lock-keywords
      ;; Keywords
      `(,(rx symbol-start
             (or
	      "if" "and" "del"  "not" "while" "as" "elif" "global"
	      "or" "async with" "with" "assert" "else"  "pass" "yield" "break"
	      "exec" "in" "continue" "finally" "is" "except" "raise"
	      "return"  "async for" "for" "lambda" "await")
             symbol-end)
        (,(rx symbol-start (or "async def" "def" "class") symbol-end) . py-def-class-face)
        (,(rx symbol-start (or "import" "from") symbol-end) . py-import-from-face)
        (,(rx symbol-start (or "try" "if") symbol-end) . py-try-if-face)
        ;; functions
        (,(rx symbol-start "def" (1+ space) (group (1+ (or word ?_))))
         (1 font-lock-function-name-face))
        (,(rx symbol-start "async def" (1+ space) (group (1+ (or word ?_))))
         (1 font-lock-function-name-face))
        ;; classes
        (,(rx symbol-start (group "class") (1+ space) (group (1+ (or word ?_))))
         (1 py-def-class-face) (2 py-class-name-face))
        (,(rx symbol-start
              (or "Ellipsis" "True" "False" "None"  "__debug__" "NotImplemented")
              symbol-end) . py-pseudo-keyword-face)
        ;; Decorators.
        (,(rx line-start (* (any " \t")) (group "@" (1+ (or word ?_))
                                                (0+ "." (1+ (or word ?_)))))
         (1 py-decorators-face))
	(,(rx symbol-start (or "cls" "self")
	      symbol-end) . py-object-reference-face)

        ;; Exceptions
        (,(rx word-start
              (or "ArithmeticError" "AssertionError" "AttributeError"
                  "BaseException" "BufferError" "BytesWarning" "DeprecationWarning"
                  "EOFError" "EnvironmentError" "Exception" "FloatingPointError"
                  "FutureWarning" "GeneratorExit" "IOError" "ImportError"
                  "ImportWarning" "IndentationError" "IndexError" "KeyError"
                  "KeyboardInterrupt" "LookupError" "MemoryError" "NameError" "NoResultFound"
                  "NotImplementedError" "OSError" "OverflowError"
                  "PendingDeprecationWarning" "ReferenceError" "RuntimeError"
                  "RuntimeWarning" "StandardError" "StopIteration" "SyntaxError"
                  "SyntaxWarning" "SystemError" "SystemExit" "TabError" "TypeError"
                  "UnboundLocalError" "UnicodeDecodeError" "UnicodeEncodeError"
                  "UnicodeError" "UnicodeTranslateError" "UnicodeWarning"
                  "UserWarning" "ValueError" "Warning" "ZeroDivisionError")
              word-end) . py-exception-name-face)
        ;; Builtins
        (,(rx
	   (or space line-start (not (any ".(")))
	   symbol-start
	   (group (or "_" "__doc__" "__import__" "__name__" "__package__" "abs" "all"
		      "any" "apply" "basestring" "bin" "bool" "buffer" "bytearray"
		      "bytes" "callable" "chr" "classmethod" "cmp" "coerce" "compile"
		      "complex" "delattr" "dict" "dir" "divmod" "enumerate" "eval"
		      "execfile" "filter" "float" "format" "frozenset"
		      "getattr" "globals" "hasattr" "hash" "help" "hex" "id" "input"
		      "int" "intern" "isinstance" "issubclass" "iter" "len" "list"
		      "locals" "long" "map" "max" "min" "next" "object" "oct" "open"
		      "ord" "pow" "property" "range" "raw_input" "reduce"
		      "reload" "repr" "reversed" "round" "set" "setattr" "slice"
		      "sorted" "staticmethod" "str" "sum" "super" "tuple" "type"
		      "unichr" "unicode" "vars" "xrange" "zip"))
	   symbol-end) (1 py-builtins-face))
        ("\\([._[:word:]]+\\)\\(?:\\[[^]]+]\\)?[[:space:]]*\\(?:\\(?:\\*\\*\\|//\\|<<\\|>>\\|[%&*+/|^-]\\)?=\\)"
         (1 py-variable-name-face nil nil))
        ;; a, b, c = (1, 2, 3)
        (,(lambda (limit)
            (let ((re (rx (group (+ (any word ?. ?_))) (* space)
			   (* ?, (* space) (+ (any word ?. ?_)) (* space))
			   ?, (* space) (+ (any word ?. ?_)) (* space)
			   (or "=" "+=" "-=" "*=" "/=" "//=" "%=" "**=" ">>=" "<<=" "&=" "^=" "|=")))
                  (res nil))
              (while (and (setq res (re-search-forward re limit t))
                          (goto-char (match-end 1))
                          (nth 1 (parse-partial-sexp (point-min) (point)))
                          ;; (python-syntax-context 'paren)
			  ))
              res))
         (1 py-variable-name-face nil nil))
        ;; Numbers
	;;        (,(rx symbol-start (or (1+ digit) (1+ hex-digit)) symbol-end) . py-number-face)
	(,(rx symbol-start (1+ digit) symbol-end) . py-number-face)))

;; python-components-switches

;;  Smart indentation
(defalias 'toggle-py-smart-indentation 'py-toggle-smart-indentation)
(defun py-toggle-smart-indentation (&optional arg)
  "Toggle `py-smart-indentation' - on with positiv ARG.

Returns value of `py-smart-indentation' switched to."
  (interactive)
  (let ((arg (or arg (if py-smart-indentation -1 1))))
    (if (< 0 arg)
        (progn
          (setq py-smart-indentation t)
          (py-guess-indent-offset))
      (setq py-smart-indentation nil)
      (setq py-indent-offset (default-value 'py-indent-offset)))
    (when (called-interactively-p 'any) (message "py-smart-indentation: %s" py-smart-indentation))
    py-smart-indentation))

(defun py-smart-indentation-on (&optional arg)
  "Toggle`py-smart-indentation' - on with positive ARG.

Returns value of `py-smart-indentation'."
  (interactive "p")
  (let ((arg (or arg 1)))
    (toggle-py-smart-indentation arg))
  (when (called-interactively-p 'any) (message "py-smart-indentation: %s" py-smart-indentation))
  py-smart-indentation)

(defun py-smart-indentation-off (&optional arg)
  "Toggle `py-smart-indentation' according to ARG.

Returns value of `py-smart-indentation'."
  (interactive "p")
  (let ((arg (if arg (- arg) -1)))
    (toggle-py-smart-indentation arg))
  (when (called-interactively-p 'any) (message "py-smart-indentation: %s" py-smart-indentation))
  py-smart-indentation)

(defun py-toggle-sexp-function ()
  "Opens customization."
  (interactive)
  (customize-variable 'py-sexp-function))

;; Autopair mode
;; py-autopair-mode forms
(defalias 'toggle-py-autopair-mode 'py-toggle-autopair-mode)
(defun py-toggle-autopair-mode ()
  "If `py-autopair-mode' should be on or off.

  Returns value of `py-autopair-mode' switched to."
  (interactive)
  (and (py-autopair-check)
       (setq py-autopair-mode (autopair-mode (if autopair-mode 0 1)))))

(defun py-autopair-mode-on ()
  "Make sure, py-autopair-mode' is on.

Returns value of `py-autopair-mode'."
  (interactive)
  (and (py-autopair-check)
       (setq py-autopair-mode (autopair-mode 1))))

(defun py-autopair-mode-off ()
  "Make sure, py-autopair-mode' is off.

Returns value of `py-autopair-mode'."
  (interactive)
  (setq py-autopair-mode (autopair-mode 0)))

;; Smart operator
;; py-smart-operator-mode-p forms
(defun toggle-py-smart-operator-mode-p ()
  "If `py-smart-operator-mode-p' should be on or off.

  Returns value of `py-smart-operator-mode-p' switched to."
  (interactive)
  (and (py-smart-operator-check)
       (setq py-smart-operator-mode-p (smart-operator-mode (if smart-operator-mode 0 1)))))

(defun py-smart-operator-mode-p-on ()
  "Make sure, py-smart-operator-mode-p' is on.

Returns value of `py-smart-operator-mode-p'."
  (interactive)
  (and (py-smart-operator-check)
       (setq py-smart-operator-mode-p (smart-operator-mode 1))))

(defun py-smart-operator-mode-p-off ()
  "Make sure, py-smart-operator-mode-p' is off.

Returns value of `py-smart-operator-mode-p'."
  (interactive)
  (setq py-smart-operator-mode-p (smart-operator-mode 0)))

;;  py-switch-buffers-on-execute-p forms
(defun toggle-py-switch-buffers-on-execute-p (&optional arg)
  "Toggle `py-switch-buffers-on-execute-p' according to ARG.

  Returns value of `py-switch-buffers-on-execute-p' switched to."
  (interactive)
  (let ((arg (or arg (if py-switch-buffers-on-execute-p -1 1))))
    (if (< 0 arg)
        (setq py-switch-buffers-on-execute-p t)
      (setq py-switch-buffers-on-execute-p nil))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "py-switch-buffers-on-execute-p: %s" py-switch-buffers-on-execute-p))
    py-switch-buffers-on-execute-p))

(defun py-switch-buffers-on-execute-p-on (&optional arg)
  "Toggle `py-py-switch-buffers-on-execute-p' according to ARG.

Returns value of `py-switch-buffers-on-execute-p'."
  (interactive)
  (let ((arg (or arg 1)))
    (toggle-py-switch-buffers-on-execute-p arg))
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-switch-buffers-on-execute-p: %s" py-switch-buffers-on-execute-p))
  py-switch-buffers-on-execute-p)

(defun py-switch-buffers-on-execute-p-off ()
  "Make sure, `py-switch-buffers-on-execute-p' is off.

Returns value of `py-switch-buffers-on-execute-p'."
  (interactive)
  (toggle-py-switch-buffers-on-execute-p -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-switch-buffers-on-execute-p: %s" py-switch-buffers-on-execute-p))
  py-switch-buffers-on-execute-p)

;;  py-split-window-on-execute forms
(defun toggle-py-split-window-on-execute (&optional arg)
  "Toggle `py-split-window-on-execute' according to ARG.

  Returns value of `py-split-window-on-execute' switched to."
  (interactive)
  (let ((arg (or arg (if py-split-window-on-execute -1 1))))
    (if (< 0 arg)
        (setq py-split-window-on-execute t)
      (setq py-split-window-on-execute nil))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "py-split-window-on-execute: %s" py-split-window-on-execute))
    py-split-window-on-execute))

(defun py-split-window-on-execute-on (&optional arg)
  "Toggle `py-py-split-window-on-execute' according to ARG.

Returns value of `py-split-window-on-execute'."
  (interactive)
  (let ((arg (or arg 1)))
    (toggle-py-split-window-on-execute arg))
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-split-window-on-execute: %s" py-split-window-on-execute))
  py-split-window-on-execute)

(defun py-split-window-on-execute-off ()
  "Make sure, `py-split-window-on-execute' is off.

Returns value of `py-split-window-on-execute'."
  (interactive)
  (toggle-py-split-window-on-execute -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-split-window-on-execute: %s" py-split-window-on-execute))
  py-split-window-on-execute)

;;  py-fontify-shell-buffer-p forms
(defun toggle-py-fontify-shell-buffer-p (&optional arg)
  "Toggle `py-fontify-shell-buffer-p' according to ARG.

  Returns value of `py-fontify-shell-buffer-p' switched to."
  (interactive)
  (let ((arg (or arg (if py-fontify-shell-buffer-p -1 1))))
    (if (< 0 arg)
        (progn
          (setq py-fontify-shell-buffer-p t)
          (set (make-local-variable 'font-lock-defaults)
             '(python-font-lock-keywords nil nil nil nil
                                         (font-lock-syntactic-keywords
                                          . py-font-lock-syntactic-keywords)))
          (unless (looking-at comint-prompt-regexp)
            (when (re-search-backward comint-prompt-regexp nil t 1)
              (font-lock-fontify-region (line-beginning-position) (point-max)))))
      (setq py-fontify-shell-buffer-p nil))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "py-fontify-shell-buffer-p: %s" py-fontify-shell-buffer-p))
    py-fontify-shell-buffer-p))

(defun py-fontify-shell-buffer-p-on (&optional arg)
  "Toggle `py-py-fontify-shell-buffer-p' according to ARG.

Returns value of `py-fontify-shell-buffer-p'."
  (interactive)
  (let ((arg (or arg 1)))
    (toggle-py-fontify-shell-buffer-p arg))
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-fontify-shell-buffer-p: %s" py-fontify-shell-buffer-p))
  py-fontify-shell-buffer-p)

(defun py-fontify-shell-buffer-p-off ()
  "Make sure, `py-fontify-shell-buffer-p' is off.

Returns value of `py-fontify-shell-buffer-p'."
  (interactive)
  (toggle-py-fontify-shell-buffer-p -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-fontify-shell-buffer-p: %s" py-fontify-shell-buffer-p))
  py-fontify-shell-buffer-p)

;;  python-mode-v5-behavior-p forms
(defun toggle-python-mode-v5-behavior-p (&optional arg)
  "Toggle `python-mode-v5-behavior-p' according to ARG.

  Returns value of `python-mode-v5-behavior-p' switched to."
  (interactive)
  (let ((arg (or arg (if python-mode-v5-behavior-p -1 1))))
    (if (< 0 arg)
        (setq python-mode-v5-behavior-p t)
      (setq python-mode-v5-behavior-p nil))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "python-mode-v5-behavior-p: %s" python-mode-v5-behavior-p))
    python-mode-v5-behavior-p))

(defun python-mode-v5-behavior-p-on (&optional arg)
  "To `python-mode-v5-behavior-p' according to ARG.

Returns value of `python-mode-v5-behavior-p'."
  (interactive)
  (let ((arg (or arg 1)))
    (toggle-python-mode-v5-behavior-p arg))
  (when (or py-verbose-p (called-interactively-p 'any)) (message "python-mode-v5-behavior-p: %s" python-mode-v5-behavior-p))
  python-mode-v5-behavior-p)

(defun python-mode-v5-behavior-p-off ()
  "Make sure, `python-mode-v5-behavior-p' is off.

Returns value of `python-mode-v5-behavior-p'."
  (interactive)
  (toggle-python-mode-v5-behavior-p -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "python-mode-v5-behavior-p: %s" python-mode-v5-behavior-p))
  python-mode-v5-behavior-p)

;;  py-jump-on-exception forms
(defun toggle-py-jump-on-exception (&optional arg)
  "Toggle `py-jump-on-exception' according to ARG.

  Returns value of `py-jump-on-exception' switched to."
  (interactive)
  (let ((arg (or arg (if py-jump-on-exception -1 1))))
    (if (< 0 arg)
        (setq py-jump-on-exception t)
      (setq py-jump-on-exception nil))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "py-jump-on-exception: %s" py-jump-on-exception))
    py-jump-on-exception))

(defun py-jump-on-exception-on (&optional arg)
  "Toggle py-jump-on-exception' according to ARG.

Returns value of `py-jump-on-exception'."
  (interactive)
  (let ((arg (or arg 1)))
    (toggle-py-jump-on-exception arg))
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-jump-on-exception: %s" py-jump-on-exception))
  py-jump-on-exception)

(defun py-jump-on-exception-off ()
  "Make sure, `py-jump-on-exception' is off.

Returns value of `py-jump-on-exception'."
  (interactive)
  (toggle-py-jump-on-exception -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-jump-on-exception: %s" py-jump-on-exception))
  py-jump-on-exception)

;;  py-use-current-dir-when-execute-p forms
(defun toggle-py-use-current-dir-when-execute-p (&optional arg)
  "Toggle `py-use-current-dir-when-execute-p' according to ARG.

  Returns value of `py-use-current-dir-when-execute-p' switched to."
  (interactive)
  (let ((arg (or arg (if py-use-current-dir-when-execute-p -1 1))))
    (if (< 0 arg)
        (setq py-use-current-dir-when-execute-p t)
      (setq py-use-current-dir-when-execute-p nil))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "py-use-current-dir-when-execute-p: %s" py-use-current-dir-when-execute-p))
    py-use-current-dir-when-execute-p))

(defun py-use-current-dir-when-execute-p-on (&optional arg)
  "Toggle py-use-current-dir-when-execute-p' according to ARG.

Returns value of `py-use-current-dir-when-execute-p'."
  (interactive)
  (let ((arg (or arg 1)))
    (toggle-py-use-current-dir-when-execute-p arg))
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-use-current-dir-when-execute-p: %s" py-use-current-dir-when-execute-p))
  py-use-current-dir-when-execute-p)

(defun py-use-current-dir-when-execute-p-off ()
  "Make sure, `py-use-current-dir-when-execute-p' is off.

Returns value of `py-use-current-dir-when-execute-p'."
  (interactive)
  (toggle-py-use-current-dir-when-execute-p -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-use-current-dir-when-execute-p: %s" py-use-current-dir-when-execute-p))
  py-use-current-dir-when-execute-p)

;;  py-electric-comment-p forms
(defun toggle-py-electric-comment-p (&optional arg)
  "Toggle `py-electric-comment-p' according to ARG.

  Returns value of `py-electric-comment-p' switched to."
  (interactive)
  (let ((arg (or arg (if py-electric-comment-p -1 1))))
    (if (< 0 arg)
        (setq py-electric-comment-p t)
      (setq py-electric-comment-p nil))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "py-electric-comment-p: %s" py-electric-comment-p))
    py-electric-comment-p))

(defun py-electric-comment-p-on (&optional arg)
  "Toggle py-electric-comment-p' according to ARG.

Returns value of `py-electric-comment-p'."
  (interactive)
  (let ((arg (or arg 1)))
    (toggle-py-electric-comment-p arg))
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-electric-comment-p: %s" py-electric-comment-p))
  py-electric-comment-p)

(defun py-electric-comment-p-off ()
  "Make sure, `py-electric-comment-p' is off.

Returns value of `py-electric-comment-p'."
  (interactive)
  (toggle-py-electric-comment-p -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-electric-comment-p: %s" py-electric-comment-p))
  py-electric-comment-p)

;;  py-underscore-word-syntax-p forms
(defun toggle-py-underscore-word-syntax-p (&optional arg)
  "Toggle `py-underscore-word-syntax-p' according to ARG.

  Returns value of `py-underscore-word-syntax-p' switched to."
  (interactive)
  (let ((arg (or arg (if py-underscore-word-syntax-p -1 1))))
    (if (< 0 arg)
        (progn
          (setq py-underscore-word-syntax-p t)
          (modify-syntax-entry ?\_ "w" python-mode-syntax-table))
      (setq py-underscore-word-syntax-p nil)
      (modify-syntax-entry ?\_ "_" python-mode-syntax-table))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "py-underscore-word-syntax-p: %s" py-underscore-word-syntax-p))
    py-underscore-word-syntax-p))

(defun py-underscore-word-syntax-p-on (&optional arg)
  "Toggle py-underscore-word-syntax-p' according to ARG.

Returns value of `py-underscore-word-syntax-p'."
  (interactive)
  (let ((arg (or arg 1)))
    (toggle-py-underscore-word-syntax-p arg))
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-underscore-word-syntax-p: %s" py-underscore-word-syntax-p))
  py-underscore-word-syntax-p)

(defun py-underscore-word-syntax-p-off ()
  "Make sure, `py-underscore-word-syntax-p' is off.

Returns value of `py-underscore-word-syntax-p'."
  (interactive)
  (toggle-py-underscore-word-syntax-p -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-underscore-word-syntax-p: %s" py-underscore-word-syntax-p))
  py-underscore-word-syntax-p)

;; toggle-py-underscore-word-syntax-p must be known already
;; circular: toggle-py-underscore-word-syntax-p sets and calls it
(defcustom py-underscore-word-syntax-p t
  "If underscore chars should be of ‘syntax-class’ word.

I.e. not of `symbol'.

Underscores in word-class like `forward-word' travel the indentifiers.
Default is t.

See bug report at launchpad, lp:940812"
  :type 'boolean
  :tag "py-underscore-word-syntax-p"
  :group 'python-mode
  :set (lambda (symbol value)
         (set-default symbol value)
         (toggle-py-underscore-word-syntax-p (if value 1 0))))

;; python-components-edit
(defvar py-keywords "\\<\\(ArithmeticError\\|AssertionError\\|AttributeError\\|BaseException\\|BufferError\\|BytesWarning\\|DeprecationWarning\\|EOFError\\|Ellipsis\\|EnvironmentError\\|Exception\\|False\\|FloatingPointError\\|FutureWarning\\|GeneratorExit\\|IOError\\|ImportError\\|ImportWarning\\|IndentationError\\|IndexError\\|KeyError\\|KeyboardInterrupt\\|LookupError\\|MemoryError\\|NameError\\|NoneNotImplementedError\\|NotImplemented\\|OSError\\|OverflowError\\|PendingDeprecationWarning\\|ReferenceError\\|RuntimeError\\|RuntimeWarning\\|StandardError\\|StopIteration\\|SyntaxError\\|SyntaxWarning\\|SystemError\\|SystemExit\\|TabError\\|True\\|TypeError\\|UnboundLocalError\\|UnicodeDecodeError\\|UnicodeEncodeError\\|UnicodeError\\|UnicodeTranslateError\\|UnicodeWarning\\|UserWarning\\|ValueError\\|Warning\\|ZeroDivisionError\\|__debug__\\|__import__\\|__name__\\|abs\\|all\\|and\\|any\\|apply\\|as\\|assert\\|basestring\\|bin\\|bool\\|break\\|buffer\\|bytearray\\|callable\\|chr\\|class\\|classmethod\\|cmp\\|coerce\\|compile\\|complex\\|continue\\|copyright\\|credits\\|def\\|del\\|delattr\\|dict\\|dir\\|divmod\\|elif\\|else\\|enumerate\\|eval\\|except\\|exec\\|execfile\\|exit\\|file\\|filter\\|float\\|for\\|format\\|from\\|getattr\\|global\\|globals\\|hasattr\\|hash\\|help\\|hex\\|id\\|if\\|import\\|in\\|input\\|int\\|intern\\|is\\|isinstance\\|issubclass\\|iter\\|lambda\\|len\\|license\\|list\\|locals\\|long\\|map\\|max\\|memoryview\\|min\\|next\\|not\\|object\\|oct\\|open\\|or\\|ord\\|pass\\|pow\\|print\\|property\\|quit\\|raise\\|range\\|raw_input\\|reduce\\|reload\\|repr\\|return\\|round\\|set\\|setattr\\|slice\\|sorted\\|staticmethod\\|str\\|sum\\|super\\|tuple\\|type\\|unichr\\|unicode\\|vars\\|while\\|with\\|xrange\\|yield\\|zip\\|\\)\\>"
  "Contents like py-fond-lock-keyword.")

;; ;
(defun py-insert-default-shebang ()
  "Insert in buffer shebang of installed default Python."
  (interactive "*")
  (let* ((erg (if py-edit-only-p
                  py-shell-name
                (executable-find py-shell-name)))
         (sheb (concat "#! " erg)))
    (insert sheb)))

(defun py--top-level-form-p ()
  "Return non-nil, if line start with a top level definition.

Used by `py-electric-colon', which will not indent than."
  (let (erg)
    (save-excursion
      (beginning-of-line)
      (setq erg (or (looking-at py-class-re)
                    (looking-at py-def-re))))
    erg))


(defun py-indent-line-outmost (&optional arg)
  "Indent the current line to the outmost reasonable indent.

With optional \\[universal-argument] ARG an indent with length `py-indent-offset' is inserted unconditionally"
  (interactive "*P")
  (let* ((need (py-compute-indentation (point)))
         (cui (current-indentation))
         (cuc (current-column)))
    (cond ((eq 4 (prefix-numeric-value arg))
	   (if indent-tabs-mode
	       (insert (make-string 1 9))
	     (insert (make-string py-indent-offset 32))))
          (t
           (if (and (eq need cui)(not (eq cuc cui)))
               (back-to-indentation)
             (beginning-of-line)
             (delete-horizontal-space)
             (indent-to need))))))

(defun py--indent-fix-region-intern (beg end)
  "Used when `py-tab-indents-region-p' is non-nil.

Requires BEG, END as the boundery of region"
  (let ()
    (save-excursion
      (save-restriction
        (beginning-of-line)
        (narrow-to-region beg end)
        (forward-line 1)
        (narrow-to-region (line-beginning-position) end)
        (beginning-of-line)
        (delete-region (point) (progn (skip-chars-forward " \t\r\n\f") (point)))
        (indent-to (py-compute-indentation))
        (while
            (< (line-end-position) end)
          (forward-line 1)
          (beginning-of-line)
          (delete-region (point) (progn (skip-chars-forward " \t\r\n\f") (point)))
          (indent-to (py-compute-indentation)))))))

(defun py--indent-line-intern (need cui indent col &optional beg end region)
  (let (erg)
    (if py-tab-indent
	(progn
	  (and py-tab-indents-region-p region
	       (py--indent-fix-region-intern beg end))
	  (cond
	   ((bolp)
	    (if (and py-tab-shifts-region-p region)
		(progn
		  (while (< (current-indentation) need)
		    (py-shift-region-right 1)))
	      (beginning-of-line)
	      (delete-horizontal-space)
	      (indent-to need)))
	   ((< need cui)
	    (if (and py-tab-shifts-region-p region)
		(progn
		  (when (eq (point) (region-end))
		    (exchange-point-and-mark))
		  (while (< 0 (current-indentation))
		    (py-shift-region-left 1)))
	      (beginning-of-line)
	      (delete-horizontal-space)
	      (indent-to need)))
	   ((eq need cui)
	    (if (or (eq this-command last-command)
		    (eq this-command 'py-indent-line))
		(if (and py-tab-shifts-region-p region)
		    (while (and (goto-char beg) (< 0 (current-indentation)))
		      (py-shift-region-left 1 beg end))
		  (beginning-of-line)
		  (delete-horizontal-space)
		  (if (<= (line-beginning-position) (+ (point) (- col cui)))
		      (forward-char (- col cui))
		    (beginning-of-line)))))
	   ((< cui need)
	    (if (and py-tab-shifts-region-p region)
		(progn
		  (py-shift-region-right 1))
	      (progn
		(beginning-of-line)
		(delete-horizontal-space)
		;; indent one indent only if goal < need
		(setq erg (+ (* (/ cui indent) indent) indent))
		(if (< need erg)
		    (indent-to need)
		  (indent-to erg))
		(forward-char (- col cui)))))
	   (t
	    (if (and py-tab-shifts-region-p region)
		(progn
		  (while (< (current-indentation) need)
		    (py-shift-region-right 1)))
	      (beginning-of-line)
	      (delete-horizontal-space)
	      (indent-to need)
	      (back-to-indentation)
	      (if (<= (line-beginning-position) (+ (point) (- col cui)))
		  (forward-char (- col cui))
		(beginning-of-line))))))
      (insert-tab))))

(defun py--indent-line-base (beg end region cui need arg this-indent-offset col)
  (cond ((eq 4 (prefix-numeric-value arg))
	 (if (and (eq cui (current-indentation))
		  (<= need cui))
	     (if indent-tabs-mode (insert "\t")(insert (make-string py-indent-offset 32)))
	   (beginning-of-line)
	   (delete-horizontal-space)
	   (indent-to (+ need py-indent-offset))))
	((not (eq 1 (prefix-numeric-value arg)))
	 (py-smart-indentation-off)
	 (py--indent-line-intern need cui this-indent-offset col beg end region))
	(t (py--indent-line-intern need cui this-indent-offset col beg end region))))

(defun py--calculate-indent-backwards (cui indent-offset)
  "Return the next reasonable indent lower than current indentation.

Requires current indent as CUI
Requires current indent-offset as INDENT-OFFSET"
  (if (< 0 (% cui py-indent-offset))
      ;; not correctly indented at all
      (/ cui indent-offset)
    (- cui indent-offset)))

(defun py-indent-line (&optional arg outmost-only)
  "Indent the current line according ARG.

When called interactivly with \\[universal-argument],
ignore dedenting rules for block closing statements
\(e.g. return, raise, break, continue, pass)

An optional \\[universal-argument] followed by a numeric argument
neither 1 nor 4 will switch off `py-smart-indentation' for this execution.
This permits to correct allowed but unwanted indents. Similar to
`toggle-py-smart-indentation' resp. `py-smart-indentation-off' followed by TAB.

This function is normally used by `indent-line-function' resp.
\\[indent-for-tab-command].

When bound to TAB, \\[quoted-insert] TAB inserts a TAB.

OUTMOST-ONLY stops circling possible indent.

When `py-tab-shifts-region-p' is t, not just the current line,
but the region is shiftet that way.

If `py-tab-indents-region-p' is t and first TAB doesn't shift
--as indent is at outmost reasonable--, ‘indent-region’ is called.

\\[quoted-insert] TAB inserts a literal TAB-character."
  (interactive "P")
  (unless (eq this-command last-command)
    (setq py-already-guessed-indent-offset nil))
  (let ((orig (copy-marker (point)))
	;; TAB-leaves-point-in-the-wrong-lp-1178453-test
	(region (use-region-p))
        cui
	outmost
	col
	beg
	end
	need
	this-indent-offset)
    (and region
	 (setq beg (region-beginning))
	 (setq end (region-end))
	 (goto-char beg))
    (setq cui (current-indentation))
    (setq col (current-column))
    (setq this-indent-offset
	  (cond ((and py-smart-indentation (not (eq this-command last-command)))
		 (py-guess-indent-offset))
		((and py-smart-indentation (eq this-command last-command) py-already-guessed-indent-offset)
		 py-already-guessed-indent-offset)
		(t (default-value 'py-indent-offset))))
    (setq outmost (py-compute-indentation nil nil nil nil nil nil this-indent-offset))
    ;; now choose the indent
    (setq need
	  (cond ((eq this-command last-command)
		 (if (eq cui outmost)
		     (when (not outmost-only)
		       (py--calculate-indent-backwards cui this-indent-offset)))
		 (if (bolp)
		     (py-compute-indentation orig)
		   (py--calculate-indent-backwards cui this-indent-offset)))
		(t
		 outmost
		 ;; (py-compute-indentation orig)
		 )))
    (when (and (called-interactively-p 'any) py-verbose-p) (message "py-indent-line, need: %s" need))
    ;; if at outmost
    ;; and not (eq this-command last-command), need remains nil
    (when need
      (py--indent-line-base beg end region cui need arg this-indent-offset col)
      (and region (or py-tab-shifts-region-p
		      py-tab-indents-region-p)
	   (not (eq (point) orig))
	   (exchange-point-and-mark))
      (when (and (called-interactively-p 'any) py-verbose-p)(message "%s" (current-indentation)))
      (current-indentation))))

(defun py--delete-trailing-whitespace (orig)
  "Delete trailing whitespace.

Either `py-newline-delete-trailing-whitespace-p'
or `
py-trailing-whitespace-smart-delete-p' must be t.

Start from position ORIG"
  (when (or py-newline-delete-trailing-whitespace-p py-trailing-whitespace-smart-delete-p)
    (let ((pos (copy-marker (point))))
      (save-excursion
	(goto-char orig)
	(if (empty-line-p)
	    (if (py---emacs-version-greater-23)
		(delete-trailing-whitespace (line-beginning-position) pos)
	      (save-restriction
		(narrow-to-region (line-beginning-position) pos)
		(delete-trailing-whitespace)))
	  (skip-chars-backward " \t")
	  (if (py---emacs-version-greater-23)
	      (delete-trailing-whitespace (line-beginning-position) pos)
	    (save-restriction
	      (narrow-to-region (point) pos)
	      (delete-trailing-whitespace))))))))

(defun py-newline-and-indent ()
  "Add a newline and indent to outmost reasonable indent.
When indent is set back manually, this is honoured in following lines."
  (interactive "*")
  (let* ((orig (point))
	 ;; lp:1280982, deliberatly dedented by user
	 (this-dedent
	  (when (and (or (eq 10 (char-after))(eobp))(looking-back "^[ \t]*" (line-beginning-position)))
	    (current-column)))
	 erg)
    (newline)
    (py--delete-trailing-whitespace orig)
    (setq erg
	  (cond (this-dedent
		 (indent-to-column this-dedent))
		((and py-empty-line-closes-p (or (eq this-command last-command)(py--after-empty-line)))
		 (indent-to-column (save-excursion (py-backward-statement)(- (current-indentation) py-indent-offset))))
		(t
		 (fixup-whitespace)
		 (indent-to-column (py-compute-indentation)))))
    (when (and (called-interactively-p 'any) py-verbose-p) (message "%s" erg))
    erg))

(defalias 'py-newline-and-close-block 'py-newline-and-dedent)
(defun py-newline-and-dedent ()
  "Add a newline and indent to one level below current.
Returns column."
  (interactive "*")
  (let ((cui (current-indentation))
        erg)
    (newline)
    (when (< 0 cui)
      (setq erg (- (py-compute-indentation) py-indent-offset))
      (indent-to-column erg))
    (when (and (called-interactively-p 'any) py-verbose-p) (message "%s" erg))
    erg))

(defun py-toggle-indent-tabs-mode ()
  "Toggle `indent-tabs-mode'.

Returns value of `indent-tabs-mode' switched to."
  (interactive)
  (when
      (setq indent-tabs-mode (not indent-tabs-mode))
    (setq tab-width py-indent-offset))
  (when (and py-verbose-p (called-interactively-p 'any)) (message "indent-tabs-mode %s  py-indent-offset %s" indent-tabs-mode py-indent-offset))
  indent-tabs-mode)

(defun py-indent-tabs-mode (arg &optional iact)
  "With positive ARG switch `indent-tabs-mode' on.

With negative ARG switch `indent-tabs-mode' off.
Returns value of `indent-tabs-mode' switched to.

If IACT is provided, message result"
  (interactive "p")
  (if (< 0 arg)
      (progn
        (setq indent-tabs-mode t)
        (setq tab-width py-indent-offset))
    (setq indent-tabs-mode nil))
  (when (and py-verbose-p (or iact (called-interactively-p 'any))) (message "indent-tabs-mode %s   py-indent-offset %s" indent-tabs-mode py-indent-offset))
  indent-tabs-mode)

(defun py-indent-tabs-mode-on (arg)
  "Switch `indent-tabs-mode' according to ARG."
  (interactive "p")
  (py-indent-tabs-mode (abs arg)(called-interactively-p 'any)))

(defun py-indent-tabs-mode-off (arg)
  "Switch `indent-tabs-mode' according to ARG."
  (interactive "p")
  (py-indent-tabs-mode (- (abs arg))(called-interactively-p 'any)))

;;  Guess indent offset
(defun py-guessed-sanity-check (guessed)
  (and (>= guessed 2)(<= guessed 8)(eq 0 (% guessed 2))))

(defun py--guess-indent-final (indents)
  "Calculate and do sanity-check.

Expects INDENTS, a cons"
  (let* ((first (car indents))
         (second (cadr indents))
         (erg (if (and first second)
                  (if (< second first)
                      (- first second)
                    (- second first))
                (default-value 'py-indent-offset))))
    (setq erg (and (py-guessed-sanity-check erg) erg))
    erg))

(defun py--guess-indent-forward ()
  "Called when moving to end of a form and `py-smart-indentation' is on."
  (let* ((first (if
                    (py--beginning-of-statement-p)
                    (current-indentation)
                  (progn
                    (py-forward-statement)
                    (py-backward-statement)
                    (current-indentation))))
         (second (if (or (looking-at py-extended-block-or-clause-re)(eq 0 first))
                     (progn
                       (py-forward-statement)
                       (py-forward-statement)
                       (py-backward-statement)
                       (current-indentation))
                   ;; when not starting from block, look above
                   (while (and (re-search-backward py-extended-block-or-clause-re nil 'movet 1)
                               (or (>= (current-indentation) first)
                                   (nth 8 (parse-partial-sexp (point-min) (point))))))
                   (current-indentation))))
    (list first second)))

(defun py--guess-indent-backward ()
  "Called when moving to beginning of a form and `py-smart-indentation' is on."
  (let* ((cui (current-indentation))
         (indent (if (< 0 cui) cui 999))
         (pos (progn (while (and (re-search-backward py-extended-block-or-clause-re nil 'move 1)
                                 (or (>= (current-indentation) indent)
                                     (nth 8 (parse-partial-sexp (point-min) (point))))))
                     (unless (bobp) (point))))
         (first (and pos (current-indentation)))
         (second (and pos (py-forward-statement) (py-forward-statement) (py-backward-statement)(current-indentation))))
    (list first second)))

(defun py-guess-indent-offset (&optional direction)
  "Guess `py-indent-offset'.

Set local value of `py-indent-offset', return it

Might change local value of `py-indent-offset' only when called
downwards from beginning of block followed by a statement.
Otherwise ‘default-value’ is returned.
Unless DIRECTION is symbol 'forward, go backward first"
  (interactive)
  (save-excursion
    (let* ((indents
            (cond (direction
                   (if (eq 'forward direction)
                       (py--guess-indent-forward)
                     (py--guess-indent-backward)))
                  ;; guess some usable indent is above current position
                  ((eq 0 (current-indentation))
                   (py--guess-indent-forward))
                  (t (py--guess-indent-backward))))
           (erg (py--guess-indent-final indents)))
      (if erg (setq py-indent-offset erg)
        (setq py-indent-offset
              (default-value 'py-indent-offset)))
      (when (called-interactively-p 'any) (message "%s" py-indent-offset))
      py-indent-offset)))

(defun py--comment-indent-function ()
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

;;  make general form below work also in these cases
;;  (defalias 'py-backward-paragraph 'backward-paragraph)
(defun py-backward-paragraph ()
  "Go to beginning of current paragraph.

If already at beginning, go to start of next paragraph upwards"
  (interactive)
  (let ((erg (and (backward-paragraph)(point))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

;;  (defalias 'py-end-of-paragraph 'forward-paragraph)
(defun py-forward-paragraph ()
    "Go to end of current paragraph.

If already at end, go to end of next paragraph downwards"
  (interactive)
  (let ((erg (and (forward-paragraph)(point))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

;; ;
(defun py-indent-and-forward (&optional indent)
  "Indent current line according to mode, move one line forward.

If optional INDENT is given, use it"
  (interactive "*")
  (beginning-of-line)
  (when (member (char-after) (list 32 9 10 12 13)) (delete-region (point) (progn (skip-chars-forward " \t\r\n\f")(point))))
  (indent-to (or indent (py-compute-indentation)))
  (if (eobp)
      (newline-and-indent)
    (forward-line 1))
  (back-to-indentation))

(defun py--indent-line-by-line (beg end)
  "Indent every line until end to max reasonable extend.

Starts from second line of region specified
BEG END deliver the boundaries of region to work within"
  (goto-char beg)
  (py-indent-and-forward)
  ;; (forward-line 1)
  (while (< (line-end-position) end)
    (if (empty-line-p)
	(forward-line 1)
      (py-indent-and-forward)))
  (unless (empty-line-p) (py-indent-and-forward)))

(defun py-indent-region (beg end)
  "Reindent a region delimited by BEG END.

In case first line accepts an indent, keep the remaining
lines relative.
Otherwise lines in region get outmost indent,
same with optional argument

In order to shift a chunk of code, where the first line is okay, start with second line."
  (interactive "*")
  (let ((end (copy-marker end)))
    (goto-char beg)
    (beginning-of-line)
    (setq beg (point))
    (skip-chars-forward " \t\r\n\f")
    (py--indent-line-by-line beg end)))

(defun py--beginning-of-buffer-position ()
  "Provided for abstract reasons."
  (point-min))

(defun py--end-of-buffer-position ()
  "Provided for abstract reasons."
  (point-max))

;;  Declarations start
(defun py--bounds-of-declarations ()
  "Bounds of consecutive multitude of assigments resp. statements around point.

Indented same level, which don't open blocks.
Typically declarations resp. initialisations of variables following
a class or function definition.
See also ‘py--bounds-of-statements’"
  (let* ((orig-indent (progn
                        (back-to-indentation)
                        (unless (py--beginning-of-statement-p)
                          (py-backward-statement))
                        (unless (py--beginning-of-block-p)
                          (current-indentation))))
         (orig (point))
         last beg end)
    (when orig-indent
      (setq beg (line-beginning-position))
      ;; look upward first
      (while (and
              (progn
                (unless (py--beginning-of-statement-p)
                  (py-backward-statement))
                (line-beginning-position))
              (py-backward-statement)
              (not (py--beginning-of-block-p))
              (eq (current-indentation) orig-indent))
        (setq beg (line-beginning-position)))
      (goto-char orig)
      (while (and (setq last (line-end-position))
                  (setq end (py-down-statement))
                  (not (py--beginning-of-block-p))
                  (eq (py-indentation-of-statement) orig-indent)))
      (setq end last)
      (goto-char beg)
      (if (and beg end)
          (progn
            (when (called-interactively-p 'any) (message "%s %s" beg end))
            (cons beg end))
        (when (called-interactively-p 'any) (message "%s" nil))
        nil))))

(defun py-backward-declarations ()
  "Got to the beginning of assigments resp. statements in current level which don't open blocks."
  (interactive)
  (let* ((bounds (py--bounds-of-declarations))
         (erg (car bounds)))
    (when erg (goto-char erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-declarations ()
  "Got to the end of assigments resp. statements in current level which don't open blocks."
  (interactive)
  (let* ((bounds (py--bounds-of-declarations))
         (erg (cdr bounds)))
    (when erg (goto-char erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defalias 'py-copy-declarations 'py-declarations)
(defun py-declarations ()
  "Forms in current level,which don't open blocks or start with a keyword.

See also `py-statements', which is more general, taking also simple statements starting with a keyword."
  (interactive)
  (let* ((bounds (py--bounds-of-declarations))
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

Store deleted variables in ‘kill-ring’"
  (interactive "*")
  (let* ((bounds (py--bounds-of-declarations))
         (beg (car bounds))
         (end (cdr bounds)))
    (when (and beg end)
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (kill-new (buffer-substring-no-properties beg end))
      (delete-region beg end))))
;;  Declarations end

;;  Statements start
(defun py--bounds-of-statements ()
  "Bounds of consecutive multitude of statements around point.

Indented same level, which don't open blocks."
  (interactive)
  (let* ((orig-indent (progn
                        (back-to-indentation)
                        (unless (py--beginning-of-statement-p)
                          (py-backward-statement))
                        (unless (py--beginning-of-block-p)
                          (current-indentation))))
         (orig (point))
         last beg end)
    (when orig-indent
      (setq beg (point))
      (while (and (setq last beg)
                  (setq beg
                        (when (py-backward-statement)
                          (line-beginning-position)))
                  (not (py-in-string-p))
                  (not (py--beginning-of-block-p))
                  (eq (current-indentation) orig-indent)))
      (setq beg last)
      (goto-char orig)
      (setq end (line-end-position))
      (while (and (setq last (py--end-of-statement-position))
                  (setq end (py-down-statement))
                  (not (py--beginning-of-block-p))
                  ;; (not (looking-at py-keywords))
                  ;; (not (looking-at "pdb\."))
                  (not (py-in-string-p))
                  (eq (py-indentation-of-statement) orig-indent)))
      (setq end last)
      (goto-char orig)
      (if (and beg end)
          (progn
            (when (called-interactively-p 'any) (message "%s %s" beg end))
            (cons beg end))
        (when (called-interactively-p 'any) (message "%s" nil))
        nil))))

(defun py-backward-statements ()
  "Got to the beginning of statements in current level which don't open blocks."
  (interactive)
  (let* ((bounds (py--bounds-of-statements))
         (erg (car bounds)))
    (when erg (goto-char erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-statements ()
  "Got to the end of statements in current level which don't open blocks."
  (interactive)
  (let* ((bounds (py--bounds-of-statements))
         (erg (cdr bounds)))
    (when erg (goto-char erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defalias 'py-copy-statements 'py-statements)
(defun py-statements ()
  "Copy and mark simple statements in current level which don't open blocks.

More general than ‘py-declarations’, which would stop at keywords like a print-statement."
  (interactive)
  (let* ((bounds (py--bounds-of-statements))
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

Store deleted statements in ‘kill-ring’"
  (interactive "*")
  (let* ((bounds (py--bounds-of-statements))
         (beg (car bounds))
         (end (cdr bounds)))
    (when (and beg end)
      (kill-new (buffer-substring-no-properties beg end))
      (delete-region beg end))))

(defun py--join-words-wrapping (words separator prefix line-length)
  (let ((lines ())
        (current-line prefix))
    (while words
      (let* ((word (car words))
             (maybe-line (concat current-line word separator)))
        (if (> (length maybe-line) line-length)
            (setq lines (cons (substring current-line 0 -1) lines)
                  current-line (concat prefix word separator " "))
          (setq current-line (concat maybe-line " "))))
      (setq words (cdr words)))
    (setq lines (cons (substring
                       current-line 0 (- 0 (length separator) 1)) lines))
    (mapconcat 'identity (nreverse lines) "\n")))

(defun py-insert-super ()
  "Insert a function \"super()\" from current environment.

As example given in Python v3.1 documentation » The Python Standard Library »

class C(B):
    def method(self, arg):
        super().method(arg) # This does the same thing as:
                               # super(C, self).method(arg)

Returns the string inserted."
  (interactive "*")
  (let* ((orig (point))
         (funcname (progn
                     (py-backward-def)
                     (when (looking-at (concat py-def-re " *\\([^(]+\\) *(\\(?:[^),]*\\),? *\\([^)]*\\))"))
                       (match-string-no-properties 2))))
         (args (match-string-no-properties 3))
         (ver (py-which-python))
         classname erg)
    (if (< ver 3)
        (progn
          (py-backward-class)
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

;; Comments
(defun py-delete-comments-in-def-or-class ()
  "Delete all commented lines in def-or-class at point."
  (interactive "*")
  (save-excursion
    (let ((beg (py--beginning-of-def-or-class-position))
          (end (py--end-of-def-or-class-position)))
      (and beg end (py--delete-comments-intern beg end)))))

(defun py-delete-comments-in-class ()
  "Delete all commented lines in class at point."
  (interactive "*")
  (save-excursion
    (let ((beg (py--beginning-of-class-position))
          (end (py--end-of-class-position)))
      (and beg end (py--delete-comments-intern beg end)))))

(defun py-delete-comments-in-block ()
  "Delete all commented lines in block at point."
  (interactive "*")
  (save-excursion
    (let ((beg (py--beginning-of-block-position))
          (end (py--end-of-block-position)))
      (and beg end (py--delete-comments-intern beg end)))))

(defun py-delete-comments-in-region (beg end)
  "Delete all commented lines in region delimited by BEG END."
  (interactive "r*")
  (save-excursion
    (py--delete-comments-intern beg end)))

(defun py--delete-comments-intern (beg end)
  (save-restriction
    (narrow-to-region beg end)
    (goto-char beg)
    (while (and (< (line-end-position) end) (not (eobp)))
      (beginning-of-line)
      (if (looking-at (concat "[ \t]*" comment-start))
          (delete-region (point) (1+ (line-end-position)))
        (forward-line 1)))))

;; Edit docstring
(defun py--edit-docstring-set-vars ()
  (save-excursion
    (setq py--docbeg (when (use-region-p) (region-beginning)))
    (setq py--docend (when (use-region-p) (region-end)))
    (let ((pps (parse-partial-sexp (point-min) (point))))
      (when (nth 3 pps)
	(setq py--docbeg (or py--docbeg (progn (goto-char (nth 8 pps))
					       (skip-chars-forward (char-to-string (char-after)))(push-mark)(point))))
	(setq py--docend (or py--docend
			     (progn (goto-char (nth 8 pps))
				    (forward-sexp)
				    (skip-chars-backward (char-to-string (char-before)))
				    (point)))))
      (setq py--docbeg (copy-marker py--docbeg))
      (setq py--docend (copy-marker py--docend)))))

(defun py--write-back-docstring ()
  "When edit is finished, write docstring back to orginal buffer."
  (interactive)
  (unless (eq (current-buffer) (get-buffer py-edit-docstring-buffer))
    (set-buffer py-edit-docstring-buffer))
  (goto-char (point-min))
  (while (re-search-forward "[\"']" nil t 1)
    (or (py-escaped)
	(replace-match (concat "\\\\" (match-string-no-properties 0)))))
  (jump-to-register py--edit-docstring-register)
  ;; (py-restore-window-configuration)
  (delete-region py--docbeg py--docend)
  (insert-buffer-substring py-edit-docstring-buffer))

(defun py-edit-docstring ()
  "Edit docstring or active region in ‘python-mode’."
  (interactive "*")
  (save-excursion
    (save-restriction
      (window-configuration-to-register py--edit-docstring-register)
      (setq py--oldbuf (current-buffer))
      (let ((orig (point))
	    relpos docstring)
	(py--edit-docstring-set-vars)
	;; store relative position in docstring
	(setq relpos (1+ (- orig py--docbeg)))
	(setq docstring (buffer-substring py--docbeg py--docend))
	(setq py-edit-docstring-orig-pos orig)
	(set-buffer (get-buffer-create py-edit-docstring-buffer))
	(erase-buffer)
	(switch-to-buffer (current-buffer))
	(insert docstring)
	(python-mode)
	(local-set-key [(control c)(control c)] 'py--write-back-docstring)
	(goto-char relpos)
	(message "%s" "Type C-c C-c writes contents back")))))

;; python-components-backward-forms

(defun py-backward-region ()
  "Go to the beginning of current region."
  (interactive)
  (let ((beg (region-beginning)))
    (when beg (goto-char beg))))

(defun py-backward-block (&optional indent)
  "Go to beginning of ‘block’ according to INDENT.

If already at beginning, go one ‘block’ backward.
Return beginning of ‘block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-block-re 'py-block-re (called-interactively-p 'any)))

(defun py-backward-block-or-clause (&optional indent)
  "Go to beginning of ‘block-or-clause’ according to INDENT.

If already at beginning, go one ‘block-or-clause’ backward.
Return beginning of ‘block-or-clause’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-extended-block-or-clause-re 'py-extended-block-or-clause-re (called-interactively-p 'any)))

;;;###autoload
(defun py-backward-class (&optional indent decorator bol)
  "Go to beginning of ‘class’ according to INDENT.

If already at beginning, go one ‘class’ backward.
Optional DECORATOR BOL

Return beginning of ‘class’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-class-re 'py-class-re (called-interactively-p 'any) decorator bol))

(defun py-backward-clause (&optional indent)
  "Go to beginning of ‘clause’ according to INDENT.

If already at beginning, go one ‘clause’ backward.
Return beginning of ‘clause’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-extended-block-or-clause-re 'py-extended-block-or-clause-re (called-interactively-p 'any)))

;;;###autoload
(defun py-backward-def (&optional indent decorator bol)
  "Go to beginning of ‘def’ according to INDENT.

If already at beginning, go one ‘def’ backward.
Optional DECORATOR BOL

Return beginning of ‘def’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-def-re 'py-def-re (called-interactively-p 'any) decorator bol))

;;;###autoload
(defun py-backward-def-or-class (&optional indent decorator bol)
  "Go to beginning of ‘def-or-class’ according to INDENT.

If already at beginning, go one ‘def-or-class’ backward.
Optional DECORATOR BOL

Return beginning of ‘def-or-class’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-def-or-class-re 'py-def-or-class-re (called-interactively-p 'any) decorator bol))

(defun py-backward-elif-block (&optional indent)
  "Go to beginning of ‘elif-block’ according to INDENT.

If already at beginning, go one ‘elif-block’ backward.
Return beginning of ‘elif-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-elif-block-re 'py-elif-block-re (called-interactively-p 'any)))

(defun py-backward-else-block (&optional indent)
  "Go to beginning of ‘else-block’ according to INDENT.

If already at beginning, go one ‘else-block’ backward.
Return beginning of ‘else-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-else-block-re 'py-else-block-re (called-interactively-p 'any)))

(defun py-backward-except-block (&optional indent)
  "Go to beginning of ‘except-block’ according to INDENT.

If already at beginning, go one ‘except-block’ backward.
Return beginning of ‘except-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-except-block-re 'py-except-block-re (called-interactively-p 'any)))

(defun py-backward-for-block (&optional indent)
  "Go to beginning of ‘for-block’ according to INDENT.

If already at beginning, go one ‘for-block’ backward.
Return beginning of ‘for-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-for-block-re 'py-for-block-re (called-interactively-p 'any)))

(defun py-backward-if-block (&optional indent)
  "Go to beginning of ‘if-block’ according to INDENT.

If already at beginning, go one ‘if-block’ backward.
Return beginning of ‘if-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-if-block-re 'py-if-block-re (called-interactively-p 'any)))

(defun py-backward-minor-block (&optional indent)
  "Go to beginning of ‘minor-block’ according to INDENT.

If already at beginning, go one ‘minor-block’ backward.
Return beginning of ‘minor-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-minor-block-re 'py-minor-block-re (called-interactively-p 'any)))

(defun py-backward-try-block (&optional indent)
  "Go to beginning of ‘try-block’ according to INDENT.

If already at beginning, go one ‘try-block’ backward.
Return beginning of ‘try-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-try-block-re 'py-try-block-re (called-interactively-p 'any)))

(defun py-backward-block-bol (&optional indent)
  "Go to beginning of ‘block’ according to INDENT, go to BOL.
If already at beginning, go one ‘block’ backward.
Return beginning of ‘block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-block-re 'py-clause-re (called-interactively-p 'any) nil t))

(defun py-backward-block-or-clause-bol (&optional indent)
  "Go to beginning of ‘block-or-clause’ according to INDENT, go to BOL.
If already at beginning, go one ‘block-or-clause’ backward.
Return beginning of ‘block-or-clause’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-extended-block-or-clause-re 'py-extended-block-or-clause-re (called-interactively-p 'any) nil t))

;;;###autoload
(defun py-backward-class-bol (&optional indent decorator)
  "Go to beginning of ‘class’ according to INDENT, go to BOL.
Optional DECORATOR BOL

If already at beginning, go one ‘class’ backward.
Return beginning of ‘class’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-class-re 'py-extended-block-or-clause-re (called-interactively-p 'any) decorator t))

(defun py-backward-clause-bol (&optional indent)
  "Go to beginning of ‘clause’ according to INDENT, go to BOL.
If already at beginning, go one ‘clause’ backward.
Return beginning of ‘clause’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-extended-block-or-clause-re 'py-extended-block-or-clause-re (called-interactively-p 'any) nil t))

;;;###autoload
(defun py-backward-def-bol (&optional indent decorator)
  "Go to beginning of ‘def’ according to INDENT, go to BOL.
Optional DECORATOR BOL

If already at beginning, go one ‘def’ backward.
Return beginning of ‘def’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-def-re 'py-extended-block-or-clause-re (called-interactively-p 'any) decorator t))

;;;###autoload
(defun py-backward-def-or-class-bol (&optional indent decorator)
  "Go to beginning of ‘def-or-class’ according to INDENT, go to BOL.
Optional DECORATOR BOL

If already at beginning, go one ‘def-or-class’ backward.
Return beginning of ‘def-or-class’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-def-or-class-re 'py-extended-block-or-clause-re (called-interactively-p 'any) decorator t))

(defun py-backward-elif-block-bol (&optional indent)
  "Go to beginning of ‘elif-block’ according to INDENT, go to BOL.
If already at beginning, go one ‘elif-block’ backward.
Return beginning of ‘elif-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-elif-block-re 'py-clause-re (called-interactively-p 'any) nil t))

(defun py-backward-else-block-bol (&optional indent)
  "Go to beginning of ‘else-block’ according to INDENT, go to BOL.
If already at beginning, go one ‘else-block’ backward.
Return beginning of ‘else-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-else-block-re 'py-clause-re (called-interactively-p 'any) nil t))

(defun py-backward-except-block-bol (&optional indent)
  "Go to beginning of ‘except-block’ according to INDENT, go to BOL.
If already at beginning, go one ‘except-block’ backward.
Return beginning of ‘except-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-except-block-re 'py-clause-re (called-interactively-p 'any) nil t))

(defun py-backward-for-block-bol (&optional indent)
  "Go to beginning of ‘for-block’ according to INDENT, go to BOL.
If already at beginning, go one ‘for-block’ backward.
Return beginning of ‘for-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-for-block-re 'py-clause-re (called-interactively-p 'any) nil t))

(defun py-backward-if-block-bol (&optional indent)
  "Go to beginning of ‘if-block’ according to INDENT, go to BOL.
If already at beginning, go one ‘if-block’ backward.
Return beginning of ‘if-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-if-block-re 'py-clause-re (called-interactively-p 'any) nil t))

(defun py-backward-minor-block-bol (&optional indent)
  "Go to beginning of ‘minor-block’ according to INDENT, go to BOL.
If already at beginning, go one ‘minor-block’ backward.
Return beginning of ‘minor-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-minor-block-re 'py-clause-re (called-interactively-p 'any) nil t))

(defun py-backward-try-block-bol (&optional indent)
  "Go to beginning of ‘try-block’ according to INDENT, go to BOL.
If already at beginning, go one ‘try-block’ backward.
Return beginning of ‘try-block’ if successful, nil otherwise"
  (interactive)
  (py--backward-prepare indent 'py-try-block-re 'py-clause-re (called-interactively-p 'any) nil t))

;; python-components-forward-forms

(defun py-forward-region ()
  "Go to the end of current region."
  (interactive)
  (let ((end (region-end)))
    (when end (goto-char end))))

(defun py-forward-block (&optional decorator bol)
  "Go to end of block.

Return end of block if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-block-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-block-bol ()
  "Goto beginning of line following end of block.

Return position reached, if successful, nil otherwise.
See also ‘py-down-block’: down from current definition to next beginning of block below."
  (interactive)
  (let ((erg (py-forward-block)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-block-or-clause (&optional decorator bol)
  "Go to end of block-or-clause.

Return end of block-or-clause if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-block-or-clause-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-block-or-clause-bol ()
  "Goto beginning of line following end of block-or-clause.

Return position reached, if successful, nil otherwise.
See also ‘py-down-block-or-clause’: down from current definition to next beginning of block-or-clause below."
  (interactive)
  (let ((erg (py-forward-block-or-clause)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

;;;###autoload
(defun py-forward-class (&optional decorator bol)
  "Go to end of class.

Return end of class if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-class-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-class-bol ()
  "Goto beginning of line following end of class.

Return position reached, if successful, nil otherwise.
See also ‘py-down-class’: down from current definition to next beginning of class below."
  (interactive)
  (let ((erg (py-forward-class)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-clause (&optional decorator bol)
  "Go to end of clause.

Return end of clause if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-clause-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-clause-bol ()
  "Goto beginning of line following end of clause.

Return position reached, if successful, nil otherwise.
See also ‘py-down-clause’: down from current definition to next beginning of clause below."
  (interactive)
  (let ((erg (py-forward-clause)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

;;;###autoload
(defun py-forward-def-or-class (&optional decorator bol)
  "Go to end of def-or-class.

Return end of def-or-class if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-def-or-class-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-def-or-class-bol ()
  "Goto beginning of line following end of def-or-class.

Return position reached, if successful, nil otherwise.
See also ‘py-down-def-or-class’: down from current definition to next beginning of def-or-class below."
  (interactive)
  (let ((erg (py-forward-def-or-class)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

;;;###autoload
(defun py-forward-def (&optional decorator bol)
  "Go to end of def.

Return end of def if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-def-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-def-bol ()
  "Goto beginning of line following end of def.

Return position reached, if successful, nil otherwise.
See also ‘py-down-def’: down from current definition to next beginning of def below."
  (interactive)
  (let ((erg (py-forward-def)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-if-block (&optional decorator bol)
  "Go to end of if-block.

Return end of if-block if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-if-block-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-if-block-bol ()
  "Goto beginning of line following end of if-block.

Return position reached, if successful, nil otherwise.
See also ‘py-down-if-block’: down from current definition to next beginning of if-block below."
  (interactive)
  (let ((erg (py-forward-if-block)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-elif-block (&optional decorator bol)
  "Go to end of elif-block.

Return end of elif-block if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-elif-block-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-elif-block-bol ()
  "Goto beginning of line following end of elif-block.

Return position reached, if successful, nil otherwise.
See also ‘py-down-elif-block’: down from current definition to next beginning of elif-block below."
  (interactive)
  (let ((erg (py-forward-elif-block)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-else-block (&optional decorator bol)
  "Go to end of else-block.

Return end of else-block if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-else-block-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-else-block-bol ()
  "Goto beginning of line following end of else-block.

Return position reached, if successful, nil otherwise.
See also ‘py-down-else-block’: down from current definition to next beginning of else-block below."
  (interactive)
  (let ((erg (py-forward-else-block)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-for-block (&optional decorator bol)
  "Go to end of for-block.

Return end of for-block if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-for-block-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-for-block-bol ()
  "Goto beginning of line following end of for-block.

Return position reached, if successful, nil otherwise.
See also ‘py-down-for-block’: down from current definition to next beginning of for-block below."
  (interactive)
  (let ((erg (py-forward-for-block)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-except-block (&optional decorator bol)
  "Go to end of except-block.

Return end of except-block if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-except-block-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-except-block-bol ()
  "Goto beginning of line following end of except-block.

Return position reached, if successful, nil otherwise.
See also ‘py-down-except-block’: down from current definition to next beginning of except-block below."
  (interactive)
  (let ((erg (py-forward-except-block)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-try-block (&optional decorator bol)
  "Go to end of try-block.

Return end of try-block if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-try-block-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-try-block-bol ()
  "Goto beginning of line following end of try-block.

Return position reached, if successful, nil otherwise.
See also ‘py-down-try-block’: down from current definition to next beginning of try-block below."
  (interactive)
  (let ((erg (py-forward-try-block)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-minor-block (&optional decorator bol)
  "Go to end of minor-block.

Return end of minor-block if successful, nil otherwise
Optional arg DECORATOR is used if form supports one
With optional BOL, go to beginning of line following match."
  (interactive)
  (let* ((orig (point))
         (erg (py--end-base 'py-minor-block-re orig decorator bol)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-minor-block-bol ()
  "Goto beginning of line following end of minor-block.

Return position reached, if successful, nil otherwise.
See also ‘py-down-minor-block’: down from current definition to next beginning of minor-block below."
  (interactive)
  (let ((erg (py-forward-minor-block)))
    (setq erg (py--beginning-of-line-form erg))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

;; python-components-forward-forms.el ends here
;; python-components-move

;; Indentation
;; Travel current level of indentation
(defun py--travel-this-indent-backward (&optional indent)
  "Travel INDENT given.

Otherwise travel current level of indentation"
  (let (erg)
    (while (and (py-backward-statement)
		(or indent (setq indent (current-indentation)))
		(eq indent (current-indentation))(setq erg (point)) (not (bobp))))
    erg))

(defun py-backward-indent ()
  "Go to the beginning of a section of equal indent.

If already at the beginning or before a indent, go to next indent upwards
Returns final position when called from inside section, nil otherwise"
  (interactive)
  (unless (bobp)
    (let (erg)
      (setq erg (py--travel-this-indent-backward))
      (when erg (goto-char erg))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg)))

(defun py--travel-this-indent-backward-bol (indent)
  "Internal use.

Travel this INDENT backward until bol"
  (let (erg)
    (while (and (py-backward-statement-bol)
		(or indent (setq indent (current-indentation)))
		(eq indent (current-indentation))(setq erg (point)) (not (bobp))))
    (when erg (goto-char erg))))

(defun py-backward-indent-bol ()
  "Go to the beginning of line of a section of equal indent.

If already at the beginning or before an indent,
go to next indent in buffer upwards
Returns final position when called from inside section, nil otherwise"
  (interactive)
  (unless (bobp)
    (let ((indent (when (eq (current-indentation) (current-column)) (current-column)))
	  erg)
      (setq erg (py--travel-this-indent-backward-bol indent))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg)))

(defun py--travel-this-indent-forward (indent)
  "Internal use.

Travel this INDENT forward"
  (let (last erg)
    (while (and (py-down-statement)
		(eq indent (current-indentation))
		(setq last (point))))
    (when last (goto-char last))
    (setq erg (py-forward-statement))
    erg))

(defun py-forward-indent ()
  "Go to the end of a section of equal indentation.

If already at the end, go down to next indent in buffer
Returns final position when called from inside section, nil otherwise"
  (interactive)
  (unless (eobp)
    (let (done indent)
      (when (py-forward-statement)
	(save-excursion
	  (setq done (point))
	  (setq indent (and (py-backward-statement)(current-indentation))))
      (setq done (py--travel-this-indent-forward indent))
      (when done (goto-char done)))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" done))
      done)))

(defun py-forward-indent-bol ()
  "Go to beginning of line following of a section of equal indentation.

If already at the end, go down to next indent in buffer
Returns final position when called from inside section, nil otherwise"
  (interactive)
  (unless (eobp)
    (let (erg indent)
      (when (py-forward-statement)
      	(save-excursion
      	  (setq indent (and (py-backward-statement)(current-indentation))))
	(setq erg (py--travel-this-indent-forward indent))
	(unless (eobp) (forward-line 1) (beginning-of-line) (setq erg (point)))
	(when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg)))
      erg)))

(defun py-backward-expression (&optional orig done repeat)
  "Go to the beginning of a python expression.

If already at the beginning or before a expression,
go to next expression in buffer upwards

ORIG - consider orignial position or point.
DONE - transaktional argument
REPEAT - count and consider repeats"
  (interactive)
  (unless (bobp)
    (unless done (skip-chars-backward " \t\r\n\f"))
    (let ((repeat (or (and repeat (1+ repeat)) 0))
	  (pps (parse-partial-sexp (point-min) (point)))
          (orig (or orig (point)))
          erg)
      (if (< py-max-specpdl-size repeat)
	  (error "`py-backward-expression' reached loops max")
	(cond
	 ;; comments
	 ((nth 8 pps)
	  (goto-char (nth 8 pps))
	  (py-backward-expression orig done repeat))
	 ;; lists
	 ((nth 1 pps)
	  (goto-char (nth 1 pps))
	  (skip-chars-backward py-expression-skip-chars))
	 ;; in string
	 ((nth 3 pps)
	  (goto-char (nth 8 pps)))
	 ;; after operator
	 ((and (not done) (looking-back py-operator-re (line-beginning-position)))
	  (skip-chars-backward "^ \t\r\n\f")
	  (skip-chars-backward " \t\r\n\f")
	  (py-backward-expression orig done repeat))
	 ((and (not done)
	       (< 0 (abs (skip-chars-backward py-expression-skip-chars))))
	  (setq done t)
	  (py-backward-expression orig done repeat))))
      (unless (or (eq (point) orig)(and (bobp)(eolp)))
	(setq erg (point)))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg)))

(defun py-forward-expression (&optional orig done repeat)
  "Go to the end of a compound python expression.

Operators are ignored.
ORIG - consider orignial position or point.
DONE - transaktional argument
REPEAT - count and consider repeats"
  (interactive)
  (unless done (skip-chars-forward " \t\r\n\f"))
  (unless (eobp)
    (let ((repeat (or (and repeat (1+ repeat)) 0))
	  (pps (parse-partial-sexp (point-min) (point)))
          (orig (or orig (point)))
          erg)
      (if (< py-max-specpdl-size repeat)
	  (error "`py-forward-expression' reached loops max")
	(cond
	 ;; in comment
	 ((nth 4 pps)
	  (or (< (point) (progn (forward-comment 1)(point)))(forward-line 1))
	  (py-forward-expression orig done repeat))
	 ;; empty before comment
	 ((and (looking-at "[ \t]*#")(looking-back "^[ \t]*" (line-beginning-position)))
	  (while (and (looking-at "[ \t]*#") (not (eobp)))
	    (forward-line 1))
	  (py-forward-expression orig done repeat))
	 ;; inside string
	 ((nth 3 pps)
	  (goto-char (nth 8 pps))
	  (goto-char (scan-sexps (point) 1))
	  (setq done t)
	  (py-forward-expression orig done repeat))
	 ((looking-at "\"\"\"\\|'''\\|\"\\|'")
	  (goto-char (scan-sexps (point) 1))
	  (setq done t)
	  (py-forward-expression orig done repeat))
	 ((nth 1 pps)
	  (goto-char (nth 1 pps))
	  (goto-char (scan-sexps (point) 1))
	  (setq done t)
	  (py-forward-expression orig done repeat))
	 ;; looking at opening delimiter
	 ((eq 4 (car-safe (syntax-after (point))))
	  (goto-char (scan-sexps (point) 1))
	  (setq done t)
	  (py-forward-expression orig done repeat))
	 ((and (eq orig (point)) (looking-at py-operator-re))
	  (goto-char (match-end 0))
	  (py-forward-expression orig done repeat))
	 ((and (not done)
	       (< 0 (skip-chars-forward py-expression-skip-chars)))
	  (setq done t)
	  (py-forward-expression orig done repeat))
	 ;; at colon following arglist
	 ((looking-at ":[ \t]*$")
	  (forward-char 1)))
	(unless (or (eq (point) orig)(and (eobp)(bolp)))
	  (setq erg (point)))
	(when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
	erg))))

(defun py-backward-partial-expression ()
  "Backward partial-expression."
  (interactive)
  (let ((orig (point))
	erg)
    (and (< 0 (abs (skip-chars-backward " \t\r\n\f")))(not (bobp))(forward-char -1))
    (when (py--in-comment-p)
      (py-backward-comment)
      (skip-chars-backward " \t\r\n\f"))
    ;; part of py-partial-expression-forward-chars
    (when (member (char-after) (list ?\ ?\" ?' ?\) ?} ?\] ?: ?#))
      (forward-char -1))
    (skip-chars-backward py-partial-expression-forward-chars)
    (when (< 0 (abs (skip-chars-backward py-partial-expression-backward-chars)))
      (while (and (not (bobp)) (py--in-comment-p)(< 0 (abs (skip-chars-backward py-partial-expression-backward-chars))))))
    (when (< (point) orig)
      (unless
	  (and (bobp) (member (char-after) (list ?\ ?\t ?\r ?\n ?\f)))
	(setq erg (point))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-partial-expression ()
  "Forward partial-expression."
  (interactive)
  (let (erg)
    (skip-chars-forward py-partial-expression-backward-chars)
    ;; group arg
    (while
     (looking-at "[\[{(]")
     (goto-char (scan-sexps (point) 1)))
    (setq erg (point))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

;; Partial- or Minor Expression
;;  Line
(defun py-backward-line ()
  "Go to ‘beginning-of-line’, return position.

If already at ‘beginning-of-line’ and not at BOB, go to beginning of previous line."
  (interactive)
  (unless (bobp)
    (let ((erg
           (if (bolp)
               (progn
                 (forward-line -1)
                 (progn (beginning-of-line)(point)))
             (progn (beginning-of-line)(point)))))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg)))

(defun py-forward-line ()
  "Go to ‘end-of-line’, return position.

If already at ‘end-of-line’ and not at EOB, go to end of next line."
  (interactive)
  (unless (eobp)
    (let ((orig (point))
	  erg)
      (when (eolp) (forward-line 1))
      (end-of-line)
      (when (< orig (point))(setq erg (point)))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg)))

;;  Statement
(defun py-backward-statement (&optional orig done limit ignore-in-string-p repeat)
  "Go to the initial line of a simple statement.

For beginning of compound statement use ‘py-backward-block’.
For beginning of clause ‘py-backward-clause’.

`ignore-in-string-p' allows moves inside a docstring, used when
computing indents
ORIG - consider orignial position or point.
DONE - transaktional argument
LIMIT - honor limit
IGNORE-IN-STRING-P - also much inside a string
REPEAT - count and consider repeats"
  (interactive)
  (save-restriction
    (unless (bobp)
      (let* ((repeat (or (and repeat (1+ repeat)) 0))
	     (orig (or orig (point)))
             (pps (parse-partial-sexp (or limit (point-min))(point)))
             (done done)
             erg)
	;; lp:1382788
	(unless done
	  (and (< 0 (abs (skip-chars-backward " \t\r\n\f")))
 	       (setq pps (parse-partial-sexp (or limit (point-min))(point)))))
        (cond
	 ((< py-max-specpdl-size repeat)
	  (error "Py-forward-statement reached loops max. If no error, customize `py-max-specpdl-size'"))
         ((and (bolp)(eolp))
          (skip-chars-backward " \t\r\n\f")
          (py-backward-statement orig done limit ignore-in-string-p repeat))
	 ;; inside string
         ((and (nth 3 pps)(not ignore-in-string-p))
	  (setq done t)
	  (goto-char (nth 8 pps))
	  (py-backward-statement orig done limit ignore-in-string-p repeat))
	 ((nth 4 pps)
	  (while (ignore-errors (goto-char (nth 8 pps)))
	    (skip-chars-backward " \t\r\n\f")
	    (setq pps (parse-partial-sexp (line-beginning-position) (point)))
	    )
	  (py-backward-statement orig done limit ignore-in-string-p repeat))
         ((nth 1 pps)
          (goto-char (1- (nth 1 pps)))
	  (when (py--skip-to-semicolon-backward (save-excursion (back-to-indentation)(point)))
	    (setq done t))
          (py-backward-statement orig done limit ignore-in-string-p repeat))
         ((py-preceding-line-backslashed-p)
          (forward-line -1)
          (back-to-indentation)
          (setq done t)
          (py-backward-statement orig done limit ignore-in-string-p repeat))
	 ;; at raw-string
	 ;; (and (looking-at "\"\"\"\\|'''") (member (char-before) (list ?u ?U ?r ?R)))
	 ((and (looking-at "\"\"\"\\|'''") (member (char-before) (list ?u ?U ?r ?R)))
	  (forward-char -1)
	  (py-backward-statement orig done limit ignore-in-string-p repeat))
	 ;; BOL or at space before comment
         ((and (looking-at "[ \t]*#")(looking-back "^[ \t]*" (line-beginning-position)))
          (forward-comment -1)
          (while (and (not (bobp)) (looking-at "[ \t]*#")(looking-back "^[ \t]*" (line-beginning-position)))
            (forward-comment -1))
          (unless (bobp)
            (py-backward-statement orig done limit ignore-in-string-p repeat)))
	 ;; at inline comment
         ((looking-at "[ \t]*#")
	  (when (py--skip-to-semicolon-backward (save-excursion (back-to-indentation)(point)))
	    (setq done t))
	  (py-backward-statement orig done limit ignore-in-string-p repeat))
	 ;; at beginning of string
	 ((looking-at py-string-delim-re)
	  (when (< 0 (abs (skip-chars-backward " \t\r\n\f")))
	    (setq done t))
	  (back-to-indentation)
	  (py-backward-statement orig done limit ignore-in-string-p repeat))
	 ;; after end of statement
	 ((and (not done) (eq (char-before) ?\;))
	  (skip-chars-backward ";")
	  (py-backward-statement orig done limit ignore-in-string-p repeat))
	 ;; travel until indentation or semicolon
	 ((and (not done) (py--skip-to-semicolon-backward))
	  (setq done t)
	  (py-backward-statement orig done limit ignore-in-string-p repeat))
	 ;; at current indent
	 ((and (not done) (not (eq 0 (skip-chars-backward " \t\r\n\f"))))
	  (py-backward-statement orig done limit ignore-in-string-p repeat)))
	;; return nil when before comment
	(unless (and (looking-at "[ \t]*#") (looking-back "^[ \t]*" (line-beginning-position)))
	  (when (< (point) orig)(setq erg (point))))
	(when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
	erg))))

(defun py-backward-statement-bol ()
  "Goto beginning of line where statement start.
Returns position reached, if successful, nil otherwise.

See also `py-up-statement': up from current definition to next beginning of statement above."
  (interactive)
  (let* ((orig (point))
         erg)
    (unless (bobp)
      (cond ((bolp)
	     (and (py-backward-statement orig)
		  (progn (beginning-of-line)
			 (setq erg (point)))))
	    (t (setq erg
		     (and
		      (py-backward-statement)
		      (progn (beginning-of-line) (point)))))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-forward-statement (&optional orig done repeat)
  "Go to the last char of current statement.

ORIG - consider orignial position or point.
DONE - transaktional argument
REPEAT - count and consider repeats"
  (interactive)
  (unless (eobp)
    (let ((repeat (or (and repeat (1+ repeat)) 0))
	  (orig (or orig (point)))
	  erg last
	  ;; use by scan-lists
	  forward-sexp-function pps err)
      ;; (unless done (py--skip-to-comment-or-semicolon done))
      (setq pps (parse-partial-sexp (point-min) (point)))
      ;; (origline (or origline (py-count-lines)))
      (cond
       ;; which-function-mode, lp:1235375
       ((< py-max-specpdl-size repeat)
	(error "Py-forward-statement reached loops max. If no error, customize `py-max-specpdl-size'"))
       ;; list
       ((nth 1 pps)
	(if (<= orig (point))
	    (progn
	      (setq orig (point))
	      ;; do not go back at a possible unclosed list
	      (goto-char (nth 1 pps))
	      (if
		  (ignore-errors (forward-list))
		  (progn
		    (when (looking-at ":[ \t]*$")
		      (forward-char 1))
		    (setq done t)
		    (skip-chars-forward "^#" (line-end-position))
		    (skip-chars-backward " \t\r\n\f" (line-beginning-position))
		    (py-forward-statement orig done repeat))
		(setq err (py--record-list-error pps))
		(goto-char orig)))))
       ;; in comment
       ((looking-at (concat " *" comment-start))
	(goto-char (match-end 0))
	(py-forward-statement orig done repeat))
       ((nth 4 pps)
	(py--end-of-comment-intern (point))
	(py--skip-to-comment-or-semicolon done)
	(while (and (eq (char-before (point)) ?\\ )
		    (py-escaped)(setq last (point)))
	  (forward-line 1)(end-of-line))
	(and last (goto-char last)
	     (forward-line 1)
	     (back-to-indentation))
	(py-forward-statement orig done repeat))
       ;; string
       ((looking-at py-string-delim-re)
	(goto-char (match-end 0))
	(py-forward-statement orig done repeat))
       ((nth 3 pps)
	(when (py-end-of-string)
	  (end-of-line)
	  (skip-chars-forward " \t\r\n\f")
	  (setq pps (parse-partial-sexp (point-min) (point)))
	  (unless (and done (not (or (nth 1 pps) (nth 8 pps))) (eolp)) (py-forward-statement orig done repeat))))
       ((py-current-line-backslashed-p)
	(end-of-line)
	(skip-chars-backward " \t\r\n\f" (line-beginning-position))
	(while (and (eq (char-before (point)) ?\\ )
		    (py-escaped))
	  (forward-line 1)
	  (end-of-line)
	  (skip-chars-backward " \t\r\n\f" (line-beginning-position)))
	(unless (eobp)
	  (py-forward-statement orig done repeat)))
       ((eq orig (point))
	(if (eolp)
	    (skip-chars-forward " \t\r\n\f#'\"")
	  (end-of-line)
	  (skip-chars-backward " \t\r\n\f" orig))
	;; point at orig due to a trailing whitespace
	(and (eq (point) orig) (skip-chars-forward " \t\r\n\f"))
	(setq done t)
	(py-forward-statement orig done repeat))
       ((eq (current-indentation) (current-column))
	(py--skip-to-comment-or-semicolon done)
	(setq pps (parse-partial-sexp orig (point)))
	(if (nth 1 pps)
	    (py-forward-statement orig done repeat)
	  (unless done
	    (py-forward-statement orig done repeat))))
       ((and (looking-at "[[:print:]]+$") (not done) (py--skip-to-comment-or-semicolon done))
	(py-forward-statement orig done repeat)))
      (unless
	  (or
	   (eq (point) orig)
	   (member (char-before) (list 10 32 9 ?#)))
	(setq erg (point)))
      (if (and py-verbose-p err)
	  (py--message-error err)
	(and py-verbose-p (called-interactively-p 'any) (message "%s" erg)))
      erg)))

(defun py-forward-statement-bol ()
  "Go to the ‘beginning-of-line’ following current statement."
  (interactive)
  (let ((erg (py-forward-statement)))
    (setq erg (py--beginning-of-line-form erg))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

;;  Decorator
(defun py-backward-decorator ()
  "Go to the beginning of a decorator.

Returns position if succesful"
  (interactive)
  (back-to-indentation)
  (while (and (not (looking-at "@\\w+"))
              (not
               ;; (empty-line-p)
               (eq 9 (char-after)))
              (not (bobp))(forward-line -1))
    (back-to-indentation))
  (let ((erg (when (looking-at "@\\w+")(match-beginning 0))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-decorator ()
  "Go to the end of a decorator.

Returns position if succesful"
  (interactive)
  (let ((orig (point)) erg)
    (unless (looking-at "@\\w+")
      (setq erg (py-backward-decorator)))
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
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg)))

(defun py-backward-comment (&optional pos)
  "Got to beginning of a commented section.

Start from POS if specified"
  (interactive)
  (let ((erg pos)
	last)
    (when erg (goto-char erg))
    (while (and (not (bobp)) (setq erg (py-in-comment-p)))
      (when (< erg (point))
	(goto-char erg)
	(setq last (point)))
      (skip-chars-backward " \t\r\n\f"))
    (when last (goto-char last))
    last))

(defun py-forward-comment (&optional pos char)
  "Go to end of commented section.

Optional args position and ‘comment-start’ character
Travel empty lines
Start from POS if specified
Use CHAR as ‘comment-start’ if provided"
  (interactive)
  (let ((orig (or pos (point)))
	(char (or char (string-to-char comment-start)))
	py-forward-comment-last erg)
    (while (and (not (eobp))
		(or
		 (forward-comment 99999)
		 (when (py--in-comment-p)
		   (progn
		     (end-of-line)
		     (skip-chars-backward " \t\r\n\f")
		     (setq py-forward-comment-last (point))))
		 (prog1 (forward-line 1)
		   (end-of-line)))))
    (when py-forward-comment-last (goto-char py-forward-comment-last))
    ;; forward-comment fails sometimes
    (and (eq orig (point)) (prog1 (forward-line 1) (back-to-indentation))
	 (while (member (char-after) (list char 10))(forward-line 1)(back-to-indentation)))
    (when (< orig (point)) (setq erg (point)))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

;;  Helper functions
(defun py-go-to-beginning-of-comment ()
  "Go to the beginning of current line's comment, if any.

From a programm use macro `py-backward-comment' instead"
  (interactive)
  (let ((erg (py-backward-comment)))
    (when (and py-verbose-p (called-interactively-p 'any))
      (message "%s" erg))))

(defun py--up-decorators-maybe (indent)
  (let (done erg)
    (while (and (not done) (not (bobp)))
      (py-backward-statement)
      (if
	  (and (current-indentation) indent
	       (looking-at py-decorator-re))
	  (setq erg (point))
	(setq done t)))
    erg))

(defun py--go-to-keyword-bol (regexp)
  (let ((orig (point))
	done pps)
    (while (and (not done) (not (bobp)) (re-search-backward (concat "^" regexp) nil t 1))
      (setq pps (parse-partial-sexp (point-min) (point)))
      (or
       (nth 8 pps)(nth 1 pps)
       ;; (member (char-after)(list 32 9 ?# ?' ?\"))
       (setq done (point))))
    (when (< (point) orig) (point))))

(defun py--go-to-keyword (regexp &optional maxindent)
  "Return a list, whose car is indentation, cdr position.

Keyword detected from REGEXP
Honor MAXINDENT if provided"
  (let ((maxindent
	 (or maxindent
	     (if (empty-line-p)
		 (progn
		   (py-backward-statement)
		   (current-indentation))
	       (or maxindent (and (< 0 (current-indentation))(current-indentation))
		   ;; make maxindent large enough if not set
		   (* 99 py-indent-offset)))))
        done erg)
    (if (eq 0 maxindent)
	;; faster jump to top-level forms
	(setq erg (py--go-to-keyword-bol regexp))
      (while (and (not done) (not (bobp)))
	(py-backward-statement)
	(cond ((eq 0 (current-indentation))
	       (when (looking-at regexp) (setq erg (point)))
	       (setq done t))
	      ;; ((and (< (current-indentation) maxindent)
	      ;; 	  (setq maxindent (current-indentation))
	      ;; 	  (looking-at regexp))
	      ;;  (setq erg (point))
	      ;;  (setq done t))
	      ((and (<= (current-indentation) maxindent)
		    (setq maxindent (current-indentation))
		    (looking-at regexp))
	       (setq erg (point))
	       (setq done t)))))
    (when (and py-mark-decorators (looking-at py-def-or-class-re))
      (setq done (py--up-decorators-maybe (current-indentation)))
      (when done (setq erg done)))
    (when erg (setq erg (cons (current-indentation) erg)))
    erg))

(defun py--clause-lookup-keyword (regexp arg &optional indent origline)
  "Return a list, whose car is indentation, cdr position.

Keyword detected from REGEXP
ARG specifies the direction of search:
\(< 0 arg)'(eobp)'(bobp))
Consider INDENT and ORIGLINE if provided"
  (let* ((origline (or origline (py-count-lines)))
         (stop (if (< 0 arg)'(eobp)'(bobp)))
         (function (if (< 0 arg) 'py-forward-statement 'py-backward-statement))
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
         ((and complement-re (looking-at complement-re)(<= (current-indentation) maxindent))
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

(defun py-leave-comment-or-string-backward ()
  "If inside a comment or string, leave it backward."
  (interactive)
  (let ((pps
         (if (featurep 'xemacs)
             (parse-partial-sexp (point-min) (point))
           (parse-partial-sexp (point-min) (point)))))
    (when (nth 8 pps)
      (goto-char (1- (nth 8 pps))))))

(defun py-beginning-of-list-pps (&optional iact last ppstart orig done)
  "Go to the beginning of a list.

IACT - if called interactively
LAST - was last match.
Optional PPSTART indicates a start-position for `parse-partial-sexp'.
ORIG - consider orignial position or point.
DONE - transaktional argument
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
                           (parse-partial-sexp (point-min) (point)))))
        (progn
          (setq last erg)
          (goto-char erg)
          (py-beginning-of-list-pps iact last ppstart orig done))
      (when iact (message "%s" last))
      last)))

(defun py-forward-into-nomenclature (&optional arg iact)
  "Move forward to end of a nomenclature symbol.

With \\[universal-argument] (programmatically, optional argument ARG), do it that many times.
IACT - if called interactively
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
          (when (looking-back "[[:upper:]]" (line-beginning-position))
            ;; (looking-back "[[:blank:]]"
            (forward-char -1))
          (if (looking-at "[[:alnum:]ß]")
              (setq erg (point))
            (setq erg nil)))
      (if (and (< orig (point)) (not (eobp)))
          (setq erg (point))
        (setq erg nil)))
    (when (and py-verbose-p (or iact (called-interactively-p 'any))) (message "%s" erg))
    erg))

(defun py-backward-into-nomenclature (&optional arg)
  "Move backward to beginning of a nomenclature symbol.

With optional ARG, move that many times.  If ARG is negative, move
forward.

A `nomenclature' is a fancy way of saying AWordWithMixedCaseNotUnderscores."
  (interactive "p")
  (setq arg (or arg 1))
  (py-forward-into-nomenclature (- arg) arg))

(defun py--travel-current-indent (indent &optional orig)
  "Move down until clause is closed, i.e. current indentation is reached.

Takes a list, INDENT and ORIG position."
  (unless (eobp)
    (let ((orig (or orig (point)))
          last)
      (while (and (setq last (point))(not (eobp))(py-forward-statement)
                  (save-excursion (or (<= indent (progn  (py-backward-statement)(current-indentation)))(eq last (line-beginning-position))))
                  ;; (py--end-of-statement-p)
))
      (goto-char last)
      (when (< orig last)
        last))))

(defun py-beginning-of-block-current-column ()
  "Reach next beginning of block upwards which start at current column.

Return position"
  (interactive)
  (let* ((orig (point))
         (cuco (current-column))
         (str (make-string cuco ?\s))
         pps erg)
    (while (and (not (bobp))(re-search-backward (concat "^" str py-block-keywords) nil t)(or (nth 8 (setq pps (parse-partial-sexp (point-min) (point)))) (nth 1 pps))))
    (back-to-indentation)
    (and (< (point) orig)(setq erg (point)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-backward-section ()
  "Go to next section start upward in buffer.

Return position if successful"
  (interactive)
  (let ((orig (point)))
    (while (and (re-search-backward py-section-start nil t 1)
		(nth 8 (parse-partial-sexp (point-min) (point)))))
    (when (and (looking-at py-section-start)(< (point) orig))
      (point))))

(defun py-forward-section ()
  "Go to next section end downward in buffer.

Return position if successful"
  (interactive)
  (let ((orig (point))
	last)
    (while (and (re-search-forward py-section-end nil t 1)
		(setq last (point))
		(goto-char (match-beginning 0))
		(nth 8 (parse-partial-sexp (point-min) (point)))
		(goto-char (match-end 0))))
    (and last (goto-char last))
    (when (and (looking-back py-section-end (line-beginning-position))(< orig (point)))
      (point))))

;; python-components-kill-forms


(defun py-kill-comment ()
  "Delete comment at point.

Stores data in kill ring"
  (interactive "*")
  (let ((erg (py--mark-base "comment")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-line ()
  "Delete line at point.

Stores data in kill ring"
  (interactive "*")
  (let ((erg (py--mark-base "line")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-paragraph ()
  "Delete paragraph at point.

Stores data in kill ring"
  (interactive "*")
  (let ((erg (py--mark-base "paragraph")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-expression ()
  "Delete expression at point.

Stores data in kill ring"
  (interactive "*")
  (let ((erg (py--mark-base "expression")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-partial-expression ()
  "Delete partial-expression at point.

Stores data in kill ring"
  (interactive "*")
  (let ((erg (py--mark-base "partial-expression")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-section ()
  "Delete section at point.

Stores data in kill ring"
  (interactive "*")
  (let ((erg (py--mark-base "section")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-top-level ()
  "Delete top-level at point.

Stores data in kill ring"
  (interactive "*")
  (let ((erg (py--mark-base "top-level")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-block ()
  "Delete block at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "block")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-block-or-clause ()
  "Delete block-or-clause at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "block-or-clause")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-class ()
  "Delete class at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "class")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-clause ()
  "Delete clause at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "clause")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-def ()
  "Delete def at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "def")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-def-or-class ()
  "Delete def-or-class at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "def-or-class")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-elif-block ()
  "Delete elif-block at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "elif-block")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-else-block ()
  "Delete else-block at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "else-block")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-except-block ()
  "Delete except-block at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "except-block")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-for-block ()
  "Delete for-block at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "for-block")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-if-block ()
  "Delete if-block at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "if-block")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-indent ()
  "Delete indent at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "indent")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-minor-block ()
  "Delete minor-block at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "minor-block")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-statement ()
  "Delete statement at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "statement")))
    (kill-region (car erg) (cdr erg))))

(defun py-kill-try-block ()
  "Delete try-block at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (let ((erg (py--mark-base-bol "try-block")))
    (kill-region (car erg) (cdr erg))))

;; python-components-close-forms


(defun py-close-block ()
  "Close block at point.

Set indent level to that of beginning of function definition.

If final line isn't empty and ‘py-close-block-provides-newline’ non-nil, insert a newline."
  (interactive "*")
  (let ((erg (py--close-intern 'py-block-re)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-close-class ()
  "Close class at point.

Set indent level to that of beginning of function definition.

If final line isn't empty and ‘py-close-block-provides-newline’ non-nil, insert a newline."
  (interactive "*")
  (let ((erg (py--close-intern 'py-class-re)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-close-def ()
  "Close def at point.

Set indent level to that of beginning of function definition.

If final line isn't empty and ‘py-close-block-provides-newline’ non-nil, insert a newline."
  (interactive "*")
  (let ((erg (py--close-intern 'py-def-re)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-close-def-or-class ()
  "Close def-or-class at point.

Set indent level to that of beginning of function definition.

If final line isn't empty and ‘py-close-block-provides-newline’ non-nil, insert a newline."
  (interactive "*")
  (let ((erg (py--close-intern 'py-def-or-class-re)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-close-minor-block ()
  "Close minor-block at point.

Set indent level to that of beginning of function definition.

If final line isn't empty and ‘py-close-block-provides-newline’ non-nil, insert a newline."
  (interactive "*")
  (let ((erg (py--close-intern 'py-minor-block-re)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-close-statement ()
  "Close statement at point.

Set indent level to that of beginning of function definition.

If final line isn't empty and ‘py-close-block-provides-newline’ non-nil, insert a newline."
  (interactive "*")
  (let ((erg (py--close-intern 'py-statement-re)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

;; python-components-mark-forms


(defun py-mark-comment ()
  "Mark comment at point.

Return beginning and end positions of marked area, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base "comment"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-line ()
  "Mark line at point.

Return beginning and end positions of marked area, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base "line"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-paragraph ()
  "Mark paragraph at point.

Return beginning and end positions of marked area, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base "paragraph"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-expression ()
  "Mark expression at point.

Return beginning and end positions of marked area, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base "expression"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-partial-expression ()
  "Mark partial-expression at point.

Return beginning and end positions of marked area, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base "partial-expression"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-section ()
  "Mark section at point.

Return beginning and end positions of marked area, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base "section"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-top-level ()
  "Mark top-level at point.

Return beginning and end positions of marked area, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base "top-level"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-block ()
  "Mark block, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-block-or-clause ()
  "Mark block-or-clause, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "block-or-clause"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-class (&optional arg)
  "Mark class, take beginning of line positions. 

With ARG \\[universal-argument] or ‘py-mark-decorators’ set to t, decorators are marked too.
Return beginning and end positions of region, a cons."
  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        erg)
    (py--mark-base-bol "class" py-mark-decorators)
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-clause ()
  "Mark clause, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "clause"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-def (&optional arg)
  "Mark def, take beginning of line positions. 

With ARG \\[universal-argument] or ‘py-mark-decorators’ set to t, decorators are marked too.
Return beginning and end positions of region, a cons."
  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        erg)
    (py--mark-base-bol "def" py-mark-decorators)
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-def-or-class (&optional arg)
  "Mark def-or-class, take beginning of line positions. 

With ARG \\[universal-argument] or ‘py-mark-decorators’ set to t, decorators are marked too.
Return beginning and end positions of region, a cons."
  (interactive "P")
  (let ((py-mark-decorators (or arg py-mark-decorators))
        erg)
    (py--mark-base-bol "def-or-class" py-mark-decorators)
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-elif-block ()
  "Mark elif-block, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "elif-block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-else-block ()
  "Mark else-block, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "else-block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-except-block ()
  "Mark except-block, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "except-block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-for-block ()
  "Mark for-block, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "for-block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-if-block ()
  "Mark if-block, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "if-block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-indent ()
  "Mark indent, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "indent"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-minor-block ()
  "Mark minor-block, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "minor-block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-statement ()
  "Mark statement, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "statement"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-mark-try-block ()
  "Mark try-block, take beginning of line positions. 

Return beginning and end positions of region, a cons."
  (interactive)
  (let (erg)
    (setq erg (py--mark-base-bol "try-block"))
    (exchange-point-and-mark)
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

;; python-components-copy-forms


(defun py-copy-block ()
  "Copy block at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "block")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-block-or-clause ()
  "Copy block-or-clause at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "block-or-clause")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-buffer ()
  "Copy buffer at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "buffer")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-class ()
  "Copy class at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "class")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-clause ()
  "Copy clause at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "clause")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-def ()
  "Copy def at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "def")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-def-or-class ()
  "Copy def-or-class at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "def-or-class")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-expression ()
  "Copy expression at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "expression")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-indent ()
  "Copy indent at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "indent")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-line ()
  "Copy line at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "line")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-minor-block ()
  "Copy minor-block at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "minor-block")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-paragraph ()
  "Copy paragraph at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "paragraph")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-partial-expression ()
  "Copy partial-expression at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "partial-expression")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-region ()
  "Copy region at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "region")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-statement ()
  "Copy statement at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "statement")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-top-level ()
  "Copy top-level at point.

Store data in kill ring, so it might yanked back."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "top-level")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-block-bol ()
  "Delete block bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "block")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-block-or-clause-bol ()
  "Delete block-or-clause bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "block-or-clause")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-buffer-bol ()
  "Delete buffer bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "buffer")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-class-bol ()
  "Delete class bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "class")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-clause-bol ()
  "Delete clause bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "clause")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-def-bol ()
  "Delete def bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "def")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-def-or-class-bol ()
  "Delete def-or-class bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "def-or-class")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-expression-bol ()
  "Delete expression bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "expression")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-indent-bol ()
  "Delete indent bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "indent")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-line-bol ()
  "Delete line bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "line")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-minor-block-bol ()
  "Delete minor-block bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "minor-block")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-paragraph-bol ()
  "Delete paragraph bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "paragraph")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-partial-expression-bol ()
  "Delete partial-expression bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "partial-expression")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-region-bol ()
  "Delete region bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "region")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-statement-bol ()
  "Delete statement bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "statement")))
      (copy-region-as-kill (car erg) (cdr erg)))))

(defun py-copy-top-level-bol ()
  "Delete top-level bol at point.

Stores data in kill ring. Might be yanked back using ‘C-y’."
  (interactive "*")
  (save-excursion
    (let ((erg (py--mark-base-bol "top-level")))
      (copy-region-as-kill (car erg) (cdr erg)))))

;; python-components-delete-forms


(defun py-delete-block ()
  "Delete BLOCK at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "block")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-block-or-clause ()
  "Delete BLOCK-OR-CLAUSE at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "block-or-clause")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-class (&optional arg)
  "Delete CLASS at point until ‘beginning-of-line’.

Don't store data in kill ring.
With ARG \\[universal-argument] or ‘py-mark-decorators’ set to t, ‘decorators’ are included."
  (interactive "P")
 (let* ((py-mark-decorators (or arg py-mark-decorators))
        (erg (py--mark-base "class" py-mark-decorators)))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-clause ()
  "Delete CLAUSE at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "clause")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-def (&optional arg)
  "Delete DEF at point until ‘beginning-of-line’.

Don't store data in kill ring.
With ARG \\[universal-argument] or ‘py-mark-decorators’ set to t, ‘decorators’ are included."
  (interactive "P")
 (let* ((py-mark-decorators (or arg py-mark-decorators))
        (erg (py--mark-base "def" py-mark-decorators)))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-def-or-class (&optional arg)
  "Delete DEF-OR-CLASS at point until ‘beginning-of-line’.

Don't store data in kill ring.
With ARG \\[universal-argument] or ‘py-mark-decorators’ set to t, ‘decorators’ are included."
  (interactive "P")
 (let* ((py-mark-decorators (or arg py-mark-decorators))
        (erg (py--mark-base "def-or-class" py-mark-decorators)))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-elif-block ()
  "Delete ELIF-BLOCK at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "elif-block")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-else-block ()
  "Delete ELSE-BLOCK at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "else-block")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-except-block ()
  "Delete EXCEPT-BLOCK at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "except-block")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-for-block ()
  "Delete FOR-BLOCK at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "for-block")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-if-block ()
  "Delete IF-BLOCK at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "if-block")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-indent ()
  "Delete INDENT at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "indent")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-minor-block ()
  "Delete MINOR-BLOCK at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "minor-block")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-statement ()
  "Delete STATEMENT at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "statement")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-try-block ()
  "Delete TRY-BLOCK at point until ‘beginning-of-line’.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base-bol "try-block")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-comment ()
  "Delete COMMENT at point.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base "comment")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-line ()
  "Delete LINE at point.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base "line")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-paragraph ()
  "Delete PARAGRAPH at point.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base "paragraph")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-expression ()
  "Delete EXPRESSION at point.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base "expression")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-partial-expression ()
  "Delete PARTIAL-EXPRESSION at point.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base "partial-expression")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-section ()
  "Delete SECTION at point.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base "section")))
    (delete-region (car erg) (cdr erg))))

(defun py-delete-top-level ()
  "Delete TOP-LEVEL at point.

Don't store data in kill ring."
  (interactive)
  (let ((erg (py--mark-base "top-level")))
    (delete-region (car erg) (cdr erg))))

;; python-components-execute
(defun py-restore-window-configuration ()
  "Restore ‘py-restore-window-configuration’ when completion is done resp. abandoned."
  (let (val)
    (and (setq val (get-register py-windows-config-register))(and (consp val) (window-configuration-p (car val))(markerp (cadr val)))(marker-buffer (cadr val))
	 (jump-to-register py-windows-config-register))))

(defun py-shell-execute-string-now (strg &optional shell buffer proc)
  "Send STRG to Python interpreter process.

Return collected output

Optional SHELL BUFFER PROC"
  (let* (wait
         (procbuf (or buffer (process-buffer proc) (progn (setq wait py-new-shell-delay) (py-shell nil nil shell))))
         (proc (or proc (get-buffer-process procbuf)))
	 (cmd (format "exec '''%s''' in {}"
		      (mapconcat 'identity (split-string strg "\n") "\\n")))
	 ;; TBD remove redundant outbuf
         (outbuf procbuf))
    ;; wait is used only when a new py-shell buffer was connected
    (and wait (sit-for wait))
    (unwind-protect
        (condition-case nil
            (progn
              (with-current-buffer outbuf
                (delete-region (point-min) (point-max)))
              (with-current-buffer procbuf
                ;; (sit-for 3)
                (comint-redirect-send-command-to-process
                 cmd outbuf proc nil t)
                (accept-process-output proc 5))
              (with-current-buffer outbuf
                (buffer-substring (point-min) (point-max))))
          (quit (with-current-buffer procbuf
                  (interrupt-process proc comint-ptyp)
                  (while (not comint-redirect-completed) ; wait for output
                    (accept-process-output proc 1)))
                (signal 'quit nil))))))

(defun py-switch-to-python (eob-p)
  "Switch to the Python process buffer, maybe starting new process.

With EOB-P, go to end of buffer."
  (interactive "p")
  (pop-to-buffer (process-buffer (py-proc)) t) ;Runs python if needed.
  (when eob-p
    (goto-char (point-max))))

(defalias 'py-shell-send-file 'py-send-file)
(defun py-send-file (file-name &optional process temp-file-name)
  "Send FILE-NAME to Python PROCESS.

If TEMP-FILE-NAME is passed then that file is used for processing
instead, while internally the shell will continue to use
FILE-NAME."
  (interactive "fFile to send: ")
  (let* ((process (or process (get-buffer-process (py-shell))))
         (temp-file-name (when temp-file-name
                           (expand-file-name temp-file-name)))
         (file-name (or (expand-file-name file-name) temp-file-name)))
    (when (not file-name)
      (error "If FILE-NAME is nil then TEMP-FILE-NAME must be non-nil"))
    (py-send-string
     (format
      (concat "__pyfile = open('''%s''');"
              "exec(compile(__pyfile.read(), '''%s''', 'exec'));"
              "__pyfile.close()")
      file-name file-name)
     process)))

(defun toggle-force-local-shell (&optional arg fast)
  "If locally indicated Python shell should be taken.

Enforced upon sessions execute commands.

Toggles boolean ‘py-force-local-shell-p’ along with ‘py-force-py-shell-name-p’
Returns value of ‘toggle-force-local-shell’ switched to.
Optional ARG FAST
When on, kind of an option 'follow'
local shell sets ‘py-shell-name’, enforces its use afterwards.

See also commands
‘py-force-local-shell-on’
‘py-force-local-shell-off’"
  (interactive)
  (let ((arg (or arg (if py-force-local-shell-p -1 1))))
    (if (< 0 arg)
        (progn
          (setq py-shell-name (or py-local-command (py-choose-shell nil fast)))
          (setq py-force-local-shell-p t))
      (setq py-shell-name (default-value 'py-shell-name))
      (setq py-force-local-shell-p nil))
    (when (called-interactively-p 'any)
      (if py-force-local-shell-p
          (when py-verbose-p (message "Enforce %s"  py-shell-name))
        (when py-verbose-p (message "py-shell-name default restored to: %s" py-shell-name))))
    py-shell-name))

(defun py-force-local-shell-on (&optional fast)
  "Make sure, ‘py-force-local-shell-p’ is on.

Returns value of ‘py-force-local-shell-p’.
Optional FAST
Kind of an option 'follow', local shell sets ‘py-shell-name’, enforces its use afterwards"
  (interactive)
  (toggle-force-local-shell 1 fast)
  (when (or py-verbose-p (called-interactively-p 'any))
    (message "Enforce %s" py-shell-name)))

(defun py-force-local-shell-off (&optional fast)
  "Restore ‘py-shell-name’ default value and ‘behaviour’.

Optional FAST"
  (interactive)
  (toggle-force-local-shell 1 fast)
  (when (or py-verbose-p (called-interactively-p 'any))
    (message "py-shell-name default restored to: %s" py-shell-name)))

(defun toggle-force-py-shell-name-p (&optional arg)
  "If customized default ‘py-shell-name’ should be enforced upon execution.

If ‘py-force-py-shell-name-p’ should be on or off.
Returns value of ‘py-force-py-shell-name-p’ switched to.

Optional ARG
See also commands
‘force-py-shell-name-p-on’
‘force-py-shell-name-p-off’

Caveat: Completion might not work that way."
  (interactive)
  (let ((arg (or arg (if py-force-py-shell-name-p -1 1))))
    (if (< 0 arg)
        (setq py-force-py-shell-name-p t)
      (setq py-force-py-shell-name-p nil))
    (when (or py-verbose-p (called-interactively-p 'any)) (message "py-force-py-shell-name-p: %s" py-force-py-shell-name-p))
    py-force-py-shell-name-p))

(defun force-py-shell-name-p-on ()
  "Switch ‘py-force-py-shell-name-p’ on.

Customized default ‘py-shell-name’ will be enforced upon execution.
Returns value of ‘py-force-py-shell-name-p’.

Caveat: Completion might not work that way."
  (interactive)
  (toggle-force-py-shell-name-p 1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-force-py-shell-name-p: %s" py-force-py-shell-name-p))
  py-force-py-shell-name-p)

(defun force-py-shell-name-p-off ()
  "Make sure, ‘py-force-py-shell-name-p’ is off.

Function to use by executes will be guessed from environment.
Returns value of ‘py-force-py-shell-name-p’."
  (interactive)
  (toggle-force-py-shell-name-p -1)
  (when (or py-verbose-p (called-interactively-p 'any)) (message "py-force-py-shell-name-p: %s" py-force-py-shell-name-p))
  py-force-py-shell-name-p)

;;  Split-Windows-On-Execute forms
(defalias 'toggle-py-split-windows-on-execute 'py-toggle-split-windows-on-execute)
(defun py-toggle-split-windows-on-execute (&optional arg)
  "If ‘py-split-window-on-execute’ should be on or off.

optional ARG
  Returns value of ‘py-split-window-on-execute’ switched to."
  (interactive)
  (let ((arg (or arg (if py-split-window-on-execute -1 1))))
    (if (< 0 arg)
        (setq py-split-window-on-execute t)
      (setq py-split-window-on-execute nil))
    (when (called-interactively-p 'any) (message "py-split-window-on-execute: %s" py-split-window-on-execute))
    py-split-window-on-execute))

(defun py-split-windows-on-execute-on (&optional arg)
  "Make sure, ‘py-split-window-on-execute’ according to ARG.

Returns value of ‘py-split-window-on-execute’."
  (interactive "p")
  (let ((arg (or arg 1)))
    (toggle-py-split-windows-on-execute arg))
  (when (called-interactively-p 'any) (message "py-split-window-on-execute: %s" py-split-window-on-execute))
  py-split-window-on-execute)

(defun py-split-windows-on-execute-off ()
  "Make sure, ‘py-split-window-on-execute’ is off.

Returns value of ‘py-split-window-on-execute’."
  (interactive)
  (toggle-py-split-windows-on-execute -1)
  (when (called-interactively-p 'any) (message "py-split-window-on-execute: %s" py-split-window-on-execute))
  py-split-window-on-execute)

;;  Shell-Switch-Buffers-On-Execute forms
(defalias 'py-toggle-switch-buffers-on-execute 'py-toggle-shell-switch-buffers-on-execute)
(defalias 'toggle-py-shell-switch-buffers-on-execute 'py-toggle-shell-switch-buffers-on-execute)
(defun py-toggle-shell-switch-buffers-on-execute (&optional arg)
  "If ‘py-switch-buffers-on-execute-p’ according to ARG.

  Returns value of ‘py-switch-buffers-on-execute-p’ switched to."
  (interactive)
  (let ((arg (or arg (if py-switch-buffers-on-execute-p -1 1))))
    (if (< 0 arg)
        (setq py-switch-buffers-on-execute-p t)
      (setq py-switch-buffers-on-execute-p nil))
    (when (called-interactively-p 'any) (message "py-shell-switch-buffers-on-execute: %s" py-switch-buffers-on-execute-p))
    py-switch-buffers-on-execute-p))

(defun py-shell-switch-buffers-on-execute-on (&optional arg)
  "Make sure, ‘py-switch-buffers-on-execute-p’ according to ARG.

Returns value of ‘py-switch-buffers-on-execute-p’."
  (interactive "p")
  (let ((arg (or arg 1)))
    (toggle-py-shell-switch-buffers-on-execute arg))
  (when (called-interactively-p 'any) (message "py-shell-switch-buffers-on-execute: %s" py-switch-buffers-on-execute-p))
  py-switch-buffers-on-execute-p)

(defun py-shell-switch-buffers-on-execute-off ()
  "Make sure, ‘py-switch-buffers-on-execute-p’ is off.

Returns value of ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (toggle-py-shell-switch-buffers-on-execute -1)
  (when (called-interactively-p 'any) (message "py-shell-switch-buffers-on-execute: %s" py-switch-buffers-on-execute-p))
  py-switch-buffers-on-execute-p)

(defun py-guess-default-python ()
  "Defaults to \"python\", if guessing didn't succeed."
  (interactive)
  (let* ((ptn (or py-shell-name (py-choose-shell) "python"))
         (erg (if py-edit-only-p ptn (executable-find ptn))))
    (when (called-interactively-p 'any)
      (if erg
          (message "%s" ptn)
        (message "%s" "Could not detect Python on your system")))))

;;  from ipython.el
(defun py-dirstack-hook ()
  "To synchronize dir-changes."
  (make-local-variable 'shell-dirstack)
  (setq shell-dirstack nil)
  (make-local-variable 'shell-last-dir)
  (setq shell-last-dir nil)
  (make-local-variable 'shell-dirtrackp)
  (setq shell-dirtrackp t)
  (add-hook 'comint-input-filter-functions 'shell-directory-tracker nil t))

(defalias 'py-dedicated-shell 'py-shell-dedicated)
(defun py-shell-dedicated (&optional argprompt)
  "Start an interpreter in another window according to ARGPROMPT.

With optional \\[universal-argument] user is prompted by
‘py-choose-shell’ for command and options to pass to the Python
interpreter."
  (interactive "P")
  (py-shell argprompt t))

(defun py-set-ipython-completion-command-string (shell)
  "Set and return ‘py-ipython-completion-command-string’ according to SHELL."
  (interactive)
  (let* ((ipython-version (shell-command-to-string (concat shell " -V"))))
    (if (string-match "[0-9]" ipython-version)
        (setq py-ipython-completion-command-string
              (cond ((string-match "^[^0].+" ipython-version)
		     py-ipython0.11-completion-command-string)
                    ((string-match "^0.1[1-3]" ipython-version)
                     py-ipython0.11-completion-command-string)
                    ((string= "^0.10" ipython-version)
                     py-ipython0.10-completion-command-string)))
      (error ipython-version))))

(defun py-ipython--module-completion-import (proc)
  "Import module-completion according to PROC."
  (interactive)
  (let ((ipython-version (shell-command-to-string (concat py-shell-name " -V"))))
    (when (and (string-match "^[0-9]" ipython-version)
               (string-match "^[^0].+" ipython-version))
      (process-send-string proc "from IPython.core.completerlib import module_completion"))))

(defun py--compose-buffer-name-initials (liste)
  (let (erg)
    (dolist (ele liste)
      (unless (string= "" ele)
	(setq erg (concat erg (char-to-string (aref ele 0))))))
    erg))

(defun py--remove-home-directory-from-list (liste)
  "Prepare for compose-buffer-name-initials according to LISTE."
  (let ((case-fold-search t)
	(liste liste)
	erg)
    (if (listp (setq erg (split-string (expand-file-name "~") "\/")))
	erg
      (setq erg (split-string (expand-file-name "~") "\\\\")))
     (while erg
      (when (member (car erg) liste)
	(setq liste (cdr (member (car erg) liste))))
      (setq erg (cdr erg)))
    (butlast liste)))

(defun py--choose-buffer-name (&optional name dedicated fast-process)
  "Return an appropriate NAME to display in modeline.

Optional DEDICATED FAST-PROCESS
SEPCHAR is the file-path separator of your system."
  (let* ((name-first (or name py-shell-name))
	 (erg (when name-first (if (stringp name-first) name-first (prin1-to-string name-first))))
	 (fast-process (or fast-process py-fast-process-p))
	 prefix)
    (when (string-match "^py-" erg)
      (setq erg (nth 1 (split-string erg "-"))))
    ;; remove home-directory from prefix to display
    (unless py-modeline-acronym-display-home-p
      (save-match-data
	(let ((case-fold-search t))
	  (when (string-match (concat ".*" (expand-file-name "~")) erg)
	    (setq erg (replace-regexp-in-string (concat "^" (expand-file-name "~")) "" erg))))))
    (if (or (and (setq prefix (split-string erg "\\\\"))
		 (< 1 (length prefix)))
	    (and (setq prefix (split-string erg "\/"))
		 (< 1 (length prefix))))
	(progn
	  ;; exect something like default py-shell-name
	  (setq erg (car (last prefix)))
	  (unless py-modeline-acronym-display-home-p
	    ;; home-directory may still inside
	    (setq prefix (py--remove-home-directory-from-list prefix))
	    (setq prefix (py--compose-buffer-name-initials prefix))))
      (setq erg (or name py-shell-name))
      (setq prefix nil))
    (when fast-process (setq erg (concat erg " Fast")))
    (setq erg
          (cond ((string-match "^ipython" erg)
                 (replace-regexp-in-string "ipython" "IPython" erg))
                ((string-match "^jython" erg)
                 (replace-regexp-in-string "jython" "Jython" erg))
                ((string-match "^python" erg)
                 (replace-regexp-in-string "python" "Python" erg))
                ((string-match "^python2" erg)
                 (replace-regexp-in-string "python2" "Python2" erg))
                ((string-match "^python3" erg)
                 (replace-regexp-in-string "python3" "Python3" erg))
                (t erg)))
    (when (or dedicated py-dedicated-process-p)
      (setq erg (make-temp-name (concat erg "-"))))
    (cond ((and prefix (string-match "^\*" erg))
           (setq erg (replace-regexp-in-string "^\*" (concat "*" prefix " ") erg)))
          (prefix
           (setq erg (concat "*" prefix " " erg "*")))
          (t (unless (string-match "^\*" erg)(setq erg (concat "*" erg "*")))))
    erg))

(defun py--jump-to-exception-intern (act exception-buffer origline)
  (let (erg)
    (set-buffer exception-buffer)
    (goto-char (point-min))
    (forward-line (1- origline))
    (and (search-forward act (line-end-position) t)
         (and py-verbose-p (message "exception-buffer: %s on line %d" py-exception-buffer origline))
         (and py-highlight-error-source-p
              (setq erg (make-overlay (match-beginning 0) (match-end 0)))
              (overlay-put erg
                           'face 'highlight)))))

(defun py--jump-to-exception (perr origline &optional file)
  "Jump to the PERR Python code at ORIGLINE in optional FILE."
  (let (
        ;; (inhibit-point-motion-hooks t)
        (file (or file (car perr)))
        (act (nth 2 perr)))
    (cond ((and py-exception-buffer
                (buffer-live-p py-exception-buffer))
           ;; (pop-to-buffer procbuf)
           (py--jump-to-exception-intern act py-exception-buffer origline))
          ((ignore-errors (file-readable-p file))
           (find-file file)
           (py--jump-to-exception-intern act (get-buffer (file-name-nondirectory file)) origline))
          ((buffer-live-p (get-buffer file))
           (set-buffer file)
           (py--jump-to-exception-intern act file origline))
          (t (setq file (find-file (read-file-name "Exception file: "
                                                   nil
                                                   file t)))
             (py--jump-to-exception-intern act file origline)))))

(defalias 'py-toggle-split-window-on-execute-function 'py-toggle-split-window-function)
(defun py-toggle-split-window-function ()
  "If window is splitted vertically or horizontally.

When code is executed and ‘py-split-window-on-execute’ is t,
the result is displays in an output-buffer, \"\*Python\*\" by default.

Customizable variable ‘py-split-windows-on-execute-function’
tells how to split the screen."
  (interactive)
  (if (eq 'split-window-vertically py-split-windows-on-execute-function)
      (setq py-split-windows-on-execute-function'split-window-horizontally)
    (setq py-split-windows-on-execute-function 'split-window-vertically))
  (when (and py-verbose-p (called-interactively-p 'any))
    (message "py-split-windows-on-execute-function set to: %s" py-split-windows-on-execute-function)))

(defun py--manage-windows-set-and-switch (buffer)
  "Switch to output BUFFER, go to ‘point-max’.

Internal use"
  (set-buffer buffer)
  (goto-char (process-mark (get-buffer-process (current-buffer)))))

(defun py--alternative-split-windows-on-execute-function ()
  "If ‘py--split-windows-on-execute-function’ is ‘split-window-vertically’ return ‘split-window-horizontally’ and vice versa."
  (if (eq py-split-windows-on-execute-function 'split-window-vertically)
      'split-window-horizontally
    'split-window-vertically))

(defun py--get-splittable-window ()
  "If selected window doesn't permit a further split, search ‘window-list’ for a suitable one."
  (or (and (window-left-child)(split-window (window-left-child)))
      (and (window-top-child)(split-window (window-top-child)))
      (and (window-parent)(ignore-errors (split-window (window-parent))))
      (and (window-atom-root)(split-window (window-atom-root)))))

(defun py--manage-windows-split (buffer)
  "If one window, split BUFFER.

according to ‘py-split-windows-on-execute-function’."
  (interactive)
  (set-buffer buffer)
  (or
   ;; (split-window (selected-window) nil ’below)
   (ignore-errors (funcall py-split-windows-on-execute-function))
   ;; If call didn't succeed according to settings of
   ;; ‘split-height-threshold’, ‘split-width-threshold’
   ;; resp. ‘window-min-height’, ‘window-min-width’
   ;; try alternative split
   (unless (ignore-errors (funcall (py--alternative-split-windows-on-execute-function)))
     ;; if alternative split fails, look for larger window
     (py--get-splittable-window)
     (ignore-errors (funcall (py--alternative-split-windows-on-execute-function))))))

;; (defun py--display-windows (output-buffer)
;;     "Otherwise new window appears above"
;;       (display-buffer output-buffer)
;;       (select-window py-exception-window))

(defun py--split-t-not-switch-wm (output-buffer number-of-windows exception-buffer)
  (unless (window-live-p output-buffer)
    (with-current-buffer (get-buffer exception-buffer)
      (when (< number-of-windows py-split-window-on-execute-threshold)
	(unless
	    (member (get-buffer-window output-buffer)(window-list))
	  (py--manage-windows-split exception-buffer)))
      (display-buffer output-buffer t))))

(defun py--shell-manage-windows (output-buffer &optional exception-buffer split switch)
  "Adapt or restore window configuration from OUTPUT-BUFFER.

Optional EXCEPTION-BUFFER SPLIT SWITCH
Return nil."
  (let* ((py-exception-buffer (or exception-buffer (and py-exception-buffer (buffer-live-p py-exception-buffer) py-exception-buffer)))
	 (output-buffer (or output-buffer py-buffer-name))
	 (old-window-list (window-list))
	 (number-of-windows (length old-window-list))
	 (split (or split py-split-window-on-execute))
	 (switch (or switch py-switch-buffers-on-execute-p)))
    ;; (output-buffer-displayed-p)
    (cond
     (py-keep-windows-configuration
      (py-restore-window-configuration)
      (set-buffer output-buffer)
      (goto-char (point-max)))
     ((and (eq split 'always)
	   switch)
      (if (member (get-buffer-window output-buffer)(window-list))
	  ;; (delete-window (get-buffer-window output-buffer))
	  (select-window (get-buffer-window output-buffer))
	(py--manage-windows-split py-exception-buffer)
	;; otherwise new window appears above
	(save-excursion
	  (other-window 1)
	  (switch-to-buffer output-buffer))
	(display-buffer py-exception-buffer)))
     ((and
       (eq split 'always)
       (not switch))
      (if (member (get-buffer-window output-buffer)(window-list))
	  (select-window (get-buffer-window output-buffer))
	(py--manage-windows-split py-exception-buffer)
	(display-buffer output-buffer)
	(pop-to-buffer py-exception-buffer)))
     ((and
       (eq split 'just-two)
       switch)
      (switch-to-buffer (current-buffer))
      (delete-other-windows)
      ;; (sit-for py-new-shell-delay)
      (py--manage-windows-split py-exception-buffer)
      ;; otherwise new window appears above
      (other-window 1)
      (set-buffer output-buffer)
      (switch-to-buffer (current-buffer)))
     ((and
       (eq split 'just-two)
       (not switch))
      (switch-to-buffer py-exception-buffer)
      (delete-other-windows)
      (unless
	  (member (get-buffer-window output-buffer)(window-list))
	(py--manage-windows-split py-exception-buffer))
      ;; Fixme: otherwise new window appears above
      (save-excursion
	(other-window 1)
	(pop-to-buffer output-buffer)
	(goto-char (point-max))
	(other-window 1)))
     ((and
       split
       (not switch))
      ;; https://bugs.launchpad.net/python-mode/+bug/1478122
      ;; > If the shell is visible in any of the windows it  should re-use that window
      ;; > I did double check and py-keep-window-configuration is nil and split is t.
      (py--split-t-not-switch-wm output-buffer number-of-windows exception-buffer))
     ((and split switch)
      (unless
	  (member (get-buffer-window output-buffer)(window-list))
	(py--manage-windows-split py-exception-buffer))
      ;; Fixme: otherwise new window appears above
      ;; (save-excursion
      ;; (other-window 1)
	;; (pop-to-buffer output-buffer)
	;; [Bug 1579309] python buffer window on top when using python3
	(set-buffer output-buffer)
	(switch-to-buffer output-buffer)
	(goto-char (point-max))
	;; (other-window 1)
	)
     ((not switch)
      (let (pop-up-windows)
	(py-restore-window-configuration))))))

(defun py-kill-shell-unconditional (&optional shell)
  "With optional argument SHELL.

Otherwise kill default (I)Python shell.
Kill buffer and its process.
Receives a ‘buffer-name’ as argument"
  (interactive)
  (let ((shell (or shell (py-shell))))
    (py-kill-buffer-unconditional shell)))

(defun py-kill-default-shell-unconditional ()
  "Kill buffer \"\*Python\*\" and its process."
  (interactive)
  (py-kill-buffer-unconditional "*Python*"))

(defun py--report-executable (buffer)
  (let ((erg (downcase (replace-regexp-in-string
                        "<\\([0-9]+\\)>" ""
                        (replace-regexp-in-string
                         "\*" ""
                         (if
                             (string-match " " buffer)
                             (substring buffer (1+ (string-match " " buffer)))
                           buffer))))))
    (when (string-match "-" erg)
      (setq erg (substring erg 0 (string-match "-" erg))))
    erg))

(defun py--shell-make-comint (executable buffer args)
  "Create comint-proces according to EXECUTABLE return the BUFFER and ARGS."
  (let* ((buffer (apply #'make-comint-in-buffer executable buffer executable nil (split-string-and-unquote (car args))))
	 (proc (get-buffer-process buffer)))
    (with-current-buffer buffer
      (if (string-match "^i" (process-name proc))
	  (py-ipython-shell-mode)
	(py-python-shell-mode)))
    buffer))

(defun py--guess-buffer-name (argprompt dedicated)
  "Guess the ‘buffer-name’ core string according to ARGPROMPT DEDICATED."
  (when (and (not dedicated) argprompt
	     (eq 4 (prefix-numeric-value argprompt)))
    (read-buffer "Py-Shell buffer: "
		 (generate-new-buffer-name (py--choose-buffer-name)))))

(defun py--configured-shell (name)
  "Return the configured PATH/TO/STRING if any according to NAME."
  (if (string-match "//\\|\\\\" name)
      name
    (cond ((string-match "^[Ii]" name)
	   (or py-ipython-command name))
	  ((string-match "[Pp]ython3" name)
	   (or py-python3-command name))
	  ((string-match "[Pp]ython2" name)
	   (or py-python2-command name))
	  ((string-match "[Jj]ython" name)
	   (or py-jython-command name))
	  (t (or py-python-command name)))))

(defun py--grab-prompt-ps1 (proc buffer)
  (py--send-string-no-output "import sys")
  (py--fast-send-string-intern "sys.ps1" proc buffer t))

(defun py--start-fast-process (shell buffer)
  (let ((proc (start-process shell buffer shell)))
    (with-current-buffer buffer
      (erase-buffer))
    proc))

(defun py--shell-fast-proceeding (proc buffer shell setup-code)
  (unless (get-buffer-process (get-buffer buffer))
    (setq proc (py--start-fast-process shell buffer))
    (setq py-output-buffer buffer)
    (py--fast-send-string-no-output setup-code proc buffer)))

(defun py--reuse-existing-shell (exception-buffer)
  (setq py-exception-buffer (or exception-buffer (and py-exception-buffer (buffer-live-p py-exception-buffer) py-exception-buffer) py-buffer-name)))

(defun py--create-new-shell (executable args buffer-name exception-buffer)
  (let ((buf (current-buffer)))
    (with-current-buffer
	(apply #'make-comint-in-buffer executable buffer-name executable nil (split-string-and-unquote args))
      (let ((proc (get-buffer-process (current-buffer))))
	(if (string-match "^i" (process-name proc))
	    (py-ipython-shell-mode)
	  (py-python-shell-mode)))
      (setq py-output-buffer (current-buffer))
      (sit-for 0.1 t)
      (goto-char (point-max))
      ;; otherwise comint might initialize it with point-min
      (set-marker comint-last-input-end (point))
      (setq py-exception-buffer (or exception-buffer (and py-exception-buffer (buffer-live-p py-exception-buffer) py-exception-buffer) buf)))))

(defun py--determine-local-default ()
  (if (not (string= "" py-shell-local-path))
      (expand-file-name py-shell-local-path)
    (when py-use-local-default
      (error "Abort: ‘py-use-local-default’ is set to t but ‘py-shell-local-path’ is empty. Maybe call ‘py-toggle-local-default-use’"))))

(defun py--provide-command-args (fast-process argprompt)
  (cond (fast-process nil)
	((eq 2 (prefix-numeric-value argprompt))
	 (mapconcat 'identity py-python2-command-args " "))
	((string-match "^[Ii]" py-shell-name)
	 py-ipython-command-args)
	((string-match "^[^-]+3" py-shell-name)
	 (mapconcat 'identity py-python3-command-args " "))
	(t (mapconcat 'identity py-python-command-args " "))))

;;;###autoload
(defun py-shell (&optional argprompt dedicated shell buffer fast exception-buffer split switch)
  "Start an interactive Python interpreter in another window.
Interactively, \\[universal-argument] prompts for a new ‘buffer-name’.
  \\[universal-argument] 2 prompts for ‘py-python-command-args’.
  If ‘default-directory’ is a remote file name, it is also prompted
  to change if called with a prefix arg.
  Optional ARGPROMPT DEDICATED
  Optional string SHELL overrides default ‘py-shell-name’.
  Returns py-shell's ‘buffer-name’.
  BUFFER allows specifying a name, the Python process is connected to
  FAST process not in ‘comint-mode’ buffer
  EXCEPTION-BUFFER point to error
  SPLIT see var ‘py-split-window-on-execute’
  SWITCH see var ‘py-switch-buffers-on-execute-p’"
  (interactive "P")
  ;; done by py-shell-mode
  (let* (
	 ;; (windows-config (window-configuration-to-register 313465889))
	 (fast (or fast py-fast-process-p))
	 (dedicated (or dedicated py-dedicated-process-p))
	 (py-shell-name (or shell
			    (py-choose-shell nil fast)))
	 (args (py--provide-command-args fast argprompt))
	 (py-use-local-default (py--determine-local-default))
	 (py-buffer-name (or buffer (py--guess-buffer-name argprompt dedicated)))
	 (py-buffer-name (or py-buffer-name (py--choose-buffer-name nil dedicated fast)))
	 (executable (cond (py-shell-name)
			   (py-buffer-name
			    (py--report-executable py-buffer-name))))
	 proc)
    (and (bufferp (get-buffer py-buffer-name))(buffer-live-p (get-buffer py-buffer-name))(string= (buffer-name (current-buffer)) (buffer-name (get-buffer py-buffer-name)))
	 (setq py-buffer-name (generate-new-buffer-name py-buffer-name)))
    (sit-for 0.1 t)
    (if fast
	;; user rather wants an interactive shell
	(py--shell-fast-proceeding proc py-buffer-name py-shell-name py-shell-completion-setup-code)
      (if (comint-check-proc py-buffer-name)
	  (py--reuse-existing-shell exception-buffer)
	;; buffer might exist but not being empty
	(when (buffer-live-p py-buffer-name)
	  (with-current-buffer py-buffer-name
	    (erase-buffer)))
	(py--create-new-shell executable args py-buffer-name exception-buffer))
      (when (or (called-interactively-p 'any)
		(eq 1 argprompt)
		(or switch py-switch-buffers-on-execute-p))
	(py--shell-manage-windows py-buffer-name py-exception-buffer split switch)))
    py-buffer-name))

(defun py-shell-get-process (&optional argprompt dedicated shell buffer)
  "Get appropriate Python process for current buffer and return it.

Optional ARGPROMPT DEDICATED SHELL BUFFER"
  (interactive)
  (let ((erg (get-buffer-process (py-shell argprompt dedicated shell buffer))))
    (when (called-interactively-p 'any) (message "%S" erg))
    erg))

(defun py-switch-to-shell ()
  "Switch to Python process buffer."
  (interactive)
  (pop-to-buffer (py-shell) t))

;;  Code execution commands
(defun py-which-execute-file-command (filename)
  "Return the command appropriate to Python version and FILENAME.

Per default it's \"(format \"execfile(r'%s') # PYTHON-MODE\\n\" filename)\" for Python 2 series."
  (format "exec(compile(open(r'%s').read(), r'%s', 'exec')) # PYTHON-MODE\n" filename filename))

(defun py--store-result-maybe (erg)
  "If no error occurred and ‘py-store-result-p’ store ERG for yank."
  (and (not py-error) erg (or py-debug-p py-store-result-p) (kill-new erg)))

(defun py--close-execution (tempbuf tempfile)
  "Delete TEMPBUF and TEMPFILE."
  (unless py-debug-p
    (when tempfile (py-delete-temporary tempfile tempbuf))))

(defun py--execute-base (&optional start end shell filename proc file wholebuf fast dedicated split switch return)
  "Update optionial variables START END SHELL FILENAME PROC FILE WHOLEBUF FAST DEDICATED SPLIT SWITCH RETURN."
  (setq py-error nil)
  (let* ((exception-buffer (current-buffer))
	 (start (or start (and (use-region-p) (region-beginning)) (point-min)))
	 (end (or end (and (use-region-p) (region-end)) (point-max)))
	 (strg-raw (if py-if-name-main-permission-p
                       (buffer-substring-no-properties start end)
                     (py--fix-if-name-main-permission (buffer-substring-no-properties start end))))
         (strg (py--fix-start strg-raw))
         (wholebuf (unless file (or wholebuf (and (eq (buffer-size) (- end start))))))
	 ;; (windows-config (window-configuration-to-register py-windows-config-register))
	 (origline
	  (save-restriction
	    (widen)
	    (py-count-lines (point-min) end)))
	 ;; argument SHELL might be a string like "python", "IPython" "python3", a symbol holding PATH/TO/EXECUTABLE or just a symbol like 'python3
	 (shell (or
		 (and shell
		      ;; shell might be specified in different ways
		      (or (and (stringp shell) shell)
			  (ignore-errors (eval shell))
			  (and (symbolp shell) (format "%s" shell))))
		 (py-choose-shell nil fast)))
	 (execute-directory
	  (cond ((ignore-errors (file-name-directory (file-remote-p (buffer-file-name) 'localname))))
		((and py-use-current-dir-when-execute-p (buffer-file-name))
		 (file-name-directory (buffer-file-name)))
		((and py-use-current-dir-when-execute-p
		      py-fileless-buffer-use-default-directory-p)
		 (expand-file-name default-directory))
		((stringp py-execute-directory)
		 py-execute-directory)
		((getenv "VIRTUAL_ENV"))
		(t (getenv "HOME"))))
	 (buffer (py--choose-buffer-name shell dedicated fast))
	 (filename (or (and filename (expand-file-name filename))
		       (py--buffer-filename-remote-maybe)))
	 (py-orig-buffer-or-file (or filename (current-buffer)))
	 (proc (or proc (get-buffer-process buffer)
		   (get-buffer-process (py-shell nil dedicated shell buffer fast exception-buffer split switch))))
	 (fast (or fast py-fast-process-p))
	 (return (or return py-return-result-p py-return-store-p)))
    (setq py-buffer-name buffer)
    (py--execute-base-intern strg filename proc file wholebuf buffer origline execute-directory start end shell fast return)
    (when (or split py-split-window-on-execute py-switch-buffers-on-execute-p)
      (py--shell-manage-windows buffer exception-buffer split switch))))

(defun py--send-to-fast-process (strg proc output-buffer return)
  "Called inside of ‘py--execute-base-intern’.

Optional STRG PROC OUTPUT-BUFFER RETURN"
  (let ((output-buffer (or output-buffer (process-buffer proc))))
  (with-current-buffer output-buffer
    (py--fast-send-string-intern strg
				 proc
				 output-buffer return)
    (sit-for 0.1))))

(defun py--delete-temp-file (tempfile &optional tempbuf)
  "After ‘py--execute-buffer-finally’ returned delete TEMPFILE &optional TEMPBUF."
  (sit-for py--delete-temp-file-delay t)
  (py--close-execution tempbuf tempfile))

(defun py--execute-buffer-finally (strg which-shell proc procbuf origline)
  (let* ((temp (make-temp-name
		;; FixMe: that should be simpler
                (concat (replace-regexp-in-string py-separator-char "-" (replace-regexp-in-string (concat "^" py-separator-char) "" (replace-regexp-in-string ":" "-" (if (stringp which-shell) which-shell (prin1-to-string which-shell))))) "-")))
         (tempbuf (get-buffer-create temp))
	 erg)
    (setq py-tempfile (concat (expand-file-name py-temp-directory) py-separator-char (replace-regexp-in-string py-separator-char "-" temp) ".py"))
    (with-current-buffer tempbuf
      (insert strg)
      (write-file py-tempfile))
    (unwind-protect
	(setq erg (py--execute-file-base proc py-tempfile nil procbuf origline)))
    erg))

(defun py--execute-base-intern (strg filename proc file wholebuf buffer origline execute-directory start end which-shell &optional fast return)
  "Select the handler according to:

STRG FILENAME PROC FILE WHOLEBUF
BUFFER ORIGLINE EXECUTE-DIRECTORY START END WHICH-SHELL
Optional FAST RETURN"
  (let ()
    (setq py-error nil)
    (py--update-execute-directory proc buffer execute-directory)
    (cond (fast (py--send-to-fast-process strg proc buffer return))
	  ;; enforce proceeding as python-mode.el v5
	  (python-mode-v5-behavior-p
	   (py-execute-python-mode-v5 start end py-exception-buffer origline))
	  (py-execute-no-temp-p
	   (py--execute-ge24.3 start end execute-directory which-shell py-exception-buffer proc file origline))
	  ((and filename wholebuf)
	   (py--execute-file-base proc filename nil buffer origline))
	  (t
	   (py--execute-buffer-finally strg which-shell proc buffer origline)
	   (py--delete-temp-file py-tempfile)))))

(defun py--fetch-error (&optional origline)
  "Highlight exceptions found in BUF.

If an exception occurred return error-string, otherwise return nil.
BUF must exist.

Indicate LINE if code wasn't run from a file, thus remember ORIGLINE of source buffer"
  (let* (erg)
    (when py-debug-p (switch-to-buffer (current-buffer)))
    (goto-char (point-min))
    (when (re-search-forward "File \"\\(.+\\)\", line \\([0-9]+\\)\\(.*\\)$" nil t)
      ;; (while (re-search-forward "File \"\\(.+\\)\", line \\([0-9]+\\)\\(.*\\)$" nil t))
      (setq erg (copy-marker (point)))
      ;; Replace hints to temp-file by orig-file
      (delete-region (progn (beginning-of-line)
			    (save-match-data
			      (when (looking-at
				     ;; all prompt-regexp known
				     py-fast-filter-re)
				(goto-char (match-end 0))))

			    (skip-chars-forward " \t\r\n\f")(point)) (line-end-position))
      (insert (concat "    File " py-exception-buffer ", line "
		      (prin1-to-string origline))))
    (when erg
      (goto-char erg)
      (save-match-data
	(and (not (py--buffer-filename-remote-maybe
		   (or
		    (get-buffer py-exception-buffer)
		    (get-buffer (file-name-nondirectory py-exception-buffer)))))
	     (string-match "^[ \t]*File" (buffer-substring-no-properties (point) (line-end-position)))
	     (looking-at "[ \t]*File")
	     (replace-match " Buffer")))
      (setq py-error (buffer-substring-no-properties (point-min) (point-max)))
      (sit-for 0.1 t)
      py-error)))

(defun py--fetch-result (orig)
  "Return ‘buffer-substring’ from ORIG to ‘point-max’."
  (switch-to-buffer (current-buffer))
  (goto-char orig)
  (if (derived-mode-p 'comint-mode)
      (replace-regexp-in-string
       (format "[ \n]*%s[ \n]*" py-fast-filter-re)
       ""
       (buffer-substring-no-properties orig (point-max)))
    (while (re-search-forward (format "[ \n]*%s[ \n]*" py-fast-filter-re) nil t 1)
      (replace-match ""))
    (buffer-substring-no-properties orig (point-max))))

(defun py--postprocess-comint (output-buffer origline orig)
  "Provide return values, check result for error, manage windows.

According to OUTPUT-BUFFER ORIGLINE ORIG"
  ;; py--fast-send-string doesn't set origline
  (let (py-result py-error)
    (with-current-buffer output-buffer
      (sit-for 0.1 t)
      ;; (when py-debug-p (switch-to-buffer (current-buffer)))
      ;; (delete-region (point-min) orig)
      (setq py-result (py--fetch-result orig)))
    ;; (when py-debug-p (message "py-result: %s" py-result))
    (and (string-match "\n$" py-result)
	 (setq py-result (replace-regexp-in-string py-fast-filter-re "" (substring py-result 0 (match-beginning 0)))))
    (if py-result
	(if (string-match "^Traceback" py-result)
	    (progn
	      (with-temp-buffer
		(insert py-result)
		(sit-for 0.1 t)
		(setq py-error (py--fetch-error origline)))
	      ;; (with-current-buffer output-buffer
	      ;; 	;; ‘comint-last-prompt’ must not exist
	      ;; 	(delete-region (point) (or (ignore-errors (car comint-last-prompt)) (point-max)))
	      ;; 	(sit-for 0.1 t)
	      ;; 	(insert py-error)
	      ;; 	(newline)
	      ;; 	(goto-char (point-max)))
	      )
	  ;; position no longer needed, no need to correct
	  (when py-store-result-p
	    (when (and py-result (not (string= "" py-result))(not (string= (car kill-ring) py-result))) (kill-new py-result)))
	  py-result)
      (message "py--postprocess-comint: %s" "Don't see any result"))))

(defun py--execute-ge24.3 (start end execute-directory which-shell &optional exception-buffer proc file origline)
  "An alternative way to do it.

According to START END EXECUTE-DIRECTORY WHICH-SHELL
Optional EXCEPTION-BUFFER PROC FILE ORIGLINE
May we get rid of the temporary file?"
  (and (py--buffer-filename-remote-maybe) buffer-offer-save (buffer-modified-p (py--buffer-filename-remote-maybe)) (y-or-n-p "Save buffer before executing? ")
       (write-file (py--buffer-filename-remote-maybe)))
  (let* ((start (copy-marker start))
         (end (copy-marker end))
         (exception-buffer (or exception-buffer (current-buffer)))
         (line (py-count-lines (point-min) (if (eq start (line-beginning-position)) (1+ start) start)))
         (strg (buffer-substring-no-properties start end))
         (tempfile (or (py--buffer-filename-remote-maybe) (concat (expand-file-name py-temp-directory) py-separator-char (replace-regexp-in-string py-separator-char "-" "temp") ".py")))

         (proc (or proc (if py-dedicated-process-p
                            (get-buffer-process (py-shell nil py-dedicated-process-p which-shell py-buffer-name))
                          (or (get-buffer-process py-buffer-name)
                              (get-buffer-process (py-shell nil py-dedicated-process-p which-shell py-buffer-name))))))
         (procbuf (process-buffer proc))
         (file (or file (with-current-buffer py-buffer-name
                          (concat (file-remote-p default-directory) tempfile))))
         (filebuf (get-buffer-create file)))
    (set-buffer filebuf)
    (erase-buffer)
    (newline line)
    (save-excursion
      (insert strg))
    (py--fix-start (buffer-substring-no-properties (point) (point-max)))
    (unless (string-match "[jJ]ython" which-shell)
      ;; (when (and execute-directory py-use-current-dir-when-execute-p
      ;; (not (string= execute-directory default-directory)))
      ;; (message "Warning: options ‘execute-directory’ and ‘py-use-current-dir-when-execute-p’ may conflict"))
      (and execute-directory
           (process-send-string proc (concat "import os; os.chdir(\"" execute-directory "\")\n"))
	   ))
    (set-buffer filebuf)
    (process-send-string proc
                         (buffer-substring-no-properties
                          (point-min) (point-max)))
    (sit-for 0.1 t)
    (if (and (setq py-error (save-excursion (py--postprocess-intern origline exception-buffer)))
             (car py-error)
             (not (markerp py-error)))
        (py--jump-to-exception py-error origline)
      (unless (string= (buffer-name (current-buffer)) (buffer-name procbuf))
        (when py-verbose-p (message "Output buffer: %s" procbuf))))))

(defun py-delete-temporary (&optional file filebuf)
  (when (file-readable-p file)
    (delete-file file))
  (when (buffer-live-p filebuf)
    (set-buffer filebuf)
    (set-buffer-modified-p 'nil)
    (kill-buffer filebuf)))

(defun py-execute-python-mode-v5 (start end &optional exception-buffer origline)
  "Take START END &optional EXCEPTION-BUFFER ORIGLINE."
  (interactive "r")
  (let ((exception-buffer (or exception-buffer (current-buffer)))
        (pcmd (concat py-shell-name (if (string-equal py-which-bufname
                                                      "Jython")
                                        " -"
                                      ;; " -c "
                                      ""))))
    (save-excursion
      (shell-command-on-region start end
                               pcmd py-output-buffer))
    (if (not (get-buffer py-output-buffer))
        (message "No output.")
      (setq py-error (py--postprocess-intern origline exception-buffer))
      (let* ((line (cadr py-error)))
        (if py-error
            (when (and py-jump-on-exception line)
              (pop-to-buffer exception-buffer))
          (pop-to-buffer py-output-buffer)
          (goto-char (point-max))
          (copy-marker (point)))))))

(defun py--insert-offset-lines (line)
  "Fix offline amount, make error point at the correct LINE."
  (insert (make-string (- line (py-count-lines (point-min) (point))) 10)))

(defun py--execute-file-base (&optional proc filename cmd procbuf origline)
  "Send to Python interpreter process PROC.

In Python version 2.. \"execfile('FILENAME')\".

Takes also CMD PROCBUF ORIGLINE.

Make that process's buffer visible and force display.  Also make
comint believe the user typed this string so that
‘kill-output-from-shell’ does The Right Thing.
Returns position where output starts."
  (let* ((origline (or (ignore-errors origline) 1))
	 (buffer (or procbuf (py-shell nil nil nil procbuf)))
	 (proc (or proc (get-buffer-process buffer)))
	 (cmd (or cmd (py-which-execute-file-command filename)))

	 ;; (windows-config (window-configuration-to-register py-windows-config-register))
	 erg orig)
    (with-current-buffer buffer
      ;; (when py-debug-p (switch-to-buffer (current-buffer)))
      (goto-char (point-max))
      (setq orig (copy-marker (point)))
      (py-send-string cmd proc)
      (when (or py-return-result-p py-store-result-p)
	(setq erg (py--postprocess-comint buffer origline orig))
	(if py-error
	    (setq py-error (prin1-to-string py-error))
	  erg)))))

(defun py-execute-file (filename)
  "When called interactively, user is prompted for FILENAME."
  (interactive "fFilename: ")
  (let (;; postprocess-output-buffer might want origline
        (origline 1)
        ;; (windows-config (window-configuration-to-register 313465889))
        (py-exception-buffer filename)
        erg)
    (if (file-readable-p filename)
        (if py-store-result-p
            (setq erg (py--execute-file-base nil (expand-file-name filename) nil nil origline))
          (py--execute-file-base nil (expand-file-name filename)))
      (message "%s not readable. %s" filename "Do you have write permissions?"))
    erg))

(defun py--current-working-directory (&optional shell)
  "Return the directory of current SHELL."
  (replace-regexp-in-string "\n" "" (shell-command-to-string (concat (or shell py-shell-name) " -c \"import os; print(os.getcwd())\""))))

(defun py--update-execute-directory-intern (dir proc)
  (comint-send-string proc (concat "import os;os.chdir(\"" dir "\")\n")))

(defun py--update-execute-directory (proc procbuf execute-directory)
  (let ((py-exception-buffer (current-buffer))
        orig cwd)
    (set-buffer procbuf)
    (setq cwd (py--current-working-directory))
    (setq orig (point))
    (unless (string= execute-directory (concat cwd "/"))
      (py--update-execute-directory-intern (or py-execute-directory execute-directory) proc)
      (delete-region orig (point-max)))
    (set-buffer py-exception-buffer)))

(defun py-execute-string (&optional strg shell dedicated switch fast)
  "Send the optional argument STRG to Python default interpreter.

Optional SHELL DEDICATED SWITCH FAST
See also ‘py-execute-region’."
  (interactive)
  (let ((strg (or strg (read-from-minibuffer "String: ")))
        (shell (or shell (default-value 'py-shell-name))))
    (with-temp-buffer
      (insert strg)
      (py-execute-region (point-min) (point-max) shell dedicated switch fast))))

(defun py-execute-string-dedicated (&optional strg shell switch fast)
  "Send the argument STRG to an unique Python interpreter.

Optional SHELL SWITCH FAST
See also ‘py-execute-region’."
  (interactive)
  (let ((strg (or strg (read-from-minibuffer "String: ")))
        (shell (or shell (default-value 'py-shell-name))))
    (with-temp-buffer
      (insert strg)
      (py-execute-region (point-min) (point-max) shell t switch fast))))

(defun py--insert-execute-directory (directory &optional orig done)
  (let ((orig (or orig (point)))
        (done done))
    (if done (goto-char done) (goto-char (point-min)))
    (cond ((re-search-forward "^from __future__ import " nil t 1)
           (py-forward-statement)
           (setq done (point))
           (py--insert-execute-directory directory orig done))
          ((re-search-forward py-encoding-string-re nil t 1)
           (setq done (point))
           (py--insert-execute-directory directory orig done))
          ((re-search-forward py-shebang-regexp nil t 1)
           (setq done (point))
           (py--insert-execute-directory directory orig done))
          (t (forward-line 1)
             (unless  ;; (empty-line-p)
                 (eq 9 (char-after)) (newline))
             (insert (concat "import os; os.chdir(\"" directory "\")\n"))))))

(defun py--fix-if-name-main-permission (strg)
  "Remove \"if __name__ == '__main__ '\" STRG from code to execute.

See ‘py-if-name-main-permission-p’"
  (let ((strg (if py-if-name-main-permission-p strg
		(replace-regexp-in-string
		 "if[( ]*__name__[) ]*==[( ]*['\"]\\{1,3\\}__main__['\"]\\{1,3\\}[) ]*:"
		 ;; space after __main__, i.e. will not be executed
		 "if __name__ == '__main__ ':" strg))))
    strg))

;; ‘py-execute-line’ calls void function, lp:1492054,  lp:1519859
(or (functionp 'indent-rigidly-left)
    (defun indent-rigidly--pop-undo ()
      (and (memq last-command '(indent-rigidly-left indent-rigidly-right
						    indent-rigidly-left-to-tab-stop
						    indent-rigidly-right-to-tab-stop))
	   (consp buffer-undo-list)
	   (eq (car buffer-undo-list) nil)
	   (pop buffer-undo-list)))

    (defun indent-rigidly-left (beg end)
      "Indent all lines between BEG and END leftward by one space."
      (interactive "r")
      (indent-rigidly--pop-undo)
      (indent-rigidly
       beg end
       (if (eq (current-bidi-paragraph-direction) 'right-to-left) 1 -1))))

(defun py--fix-start (strg)
  "Internal use by py-execute... functions.

Takes STRG
Avoid empty lines at the beginning."
  ;; (when py-debug-p (message "py--fix-start:"))
  (with-temp-buffer
    (python-mode)
    (let (erg)
      (insert strg)
      (goto-char 1)
      (when (< 0 (setq erg (skip-chars-forward " \t\r\n\f" (line-end-position))))
	(dotimes (_ erg)
	  (indent-rigidly-left (point-min) (point-max))))
      (unless (py--beginning-of-statement-p)
	(py-forward-statement))
      (while (not (eq (current-indentation) 0))
	(py-shift-left py-indent-offset))
      (goto-char (point-max))
      (unless (empty-line-p)
	(newline))
      (buffer-substring-no-properties 1 (point-max)))))

(defun py-fetch-py-master-file ()
  "Lookup if a ‘py-master-file’ is specified.

See also doku of variable ‘py-master-file’"
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (goto-char (point-min))
      (when (re-search-forward "^ *# Local Variables:" nil (quote move) 1)
        (when
            (re-search-forward (concat "^\\( *# py-master-file: *\\)\"\\([^ \t]+\\)\" *$") nil t 1)
          (setq py-master-file (match-string-no-properties 2))))))
  (when (called-interactively-p 'any) (message "%s" py-master-file)))

(defun py-execute-import-or-reload (&optional shell)
  "Import the current buffer's file in a Python interpreter.

Optional SHELL
If the file has already been imported, then do reload instead to get
the latest version.

If the file's name does not end in \".py\", then do execfile instead.

If the current buffer is not visiting a file, do ‘py-execute-buffer’
instead.

If the file local variable ‘py-master-file’ is non-nil, import or
reload the named file instead of the buffer's file.  The file may be
saved based on the value of ‘py-execute-import-or-reload-save-p’.

See also ‘\\[py-execute-region]’.

This may be preferable to ‘\\[py-execute-buffer]’ because:

 - Definitions stay in their module rather than appearing at top
   level, where they would clutter the global namespace and not affect
   uses of qualified names (MODULE.NAME).

 - The Python debugger gets line number information about the functions."
  (interactive)
  ;; Check file local variable py-master-file
  (when py-master-file
    (let* ((filename (expand-file-name py-master-file))
           (buffer (or (get-file-buffer filename)
                       (find-file-noselect filename))))
      (set-buffer buffer)))
  (let ((py-shell-name (or shell (py-choose-shell)))
        (file (py--buffer-filename-remote-maybe)))
    (if file
        (let ((proc (or
                     (ignore-errors (get-process (file-name-directory shell)))
                     (get-buffer-process (py-shell nil py-dedicated-process-p shell (or shell (default-value 'py-shell-name)))))))
          ;; Maybe save some buffers
          (save-some-buffers (not py-ask-about-save) nil)
          (py--execute-file-base proc file
                                (if (string-match "\\.py$" file)
                                    (let ((m (py--qualified-module-name (expand-file-name file))))
                                      (if (string-match "python2" py-shell-name)
                                          (format "import sys\nif sys.modules.has_key('%s'):\n reload(%s)\nelse:\n import %s\n" m m m)
                                        (format "import sys,imp\nif'%s' in sys.modules:\n imp.reload(%s)\nelse:\n import %s\n" m m m)))
                                  ;; (format "execfile(r'%s')\n" file)
                                  (py-which-execute-file-command file))))
      (py-execute-buffer))))

(defun py--qualified-module-name (file)
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

;;  Fixme: Try to define the function or class within the relevant
;;  module, not just at top level.
(defun py-execute-defun ()
  "Send the current defun (class or method) to the Python process."
  (interactive)
  (save-excursion (py-execute-region (progn (beginning-of-defun) (point))
                                     (progn (end-of-defun) (point)))))

(defun py-process-file (filename &optional output-buffer error-buffer)
  "Process \"python FILENAME\".

Optional OUTPUT-BUFFER and ERROR-BUFFER might be given."
  (interactive "fDatei:")
  (let ((coding-system-for-read 'utf-8)
        (coding-system-for-write 'utf-8)
        (output-buffer (or output-buffer (make-temp-name "py-process-file-output")))
        (pcmd (py-choose-shell)))
    (unless (buffer-live-p output-buffer)
      (set-buffer (get-buffer-create output-buffer)))
    (shell-command (concat pcmd " " filename) output-buffer error-buffer)
    (when (called-interactively-p 'any) (switch-to-buffer output-buffer))))

(defvar py-last-exeption-buffer nil
  "Internal use only - when ‘py-up-exception’ is called.

In source-buffer, this will deliver the exception-buffer again.")

(defun py-remove-overlays-at-point ()
  "Remove overlays as set when ‘py-highlight-error-source-p’ is non-nil."
  (interactive "*")
  (delete-overlay (car (overlays-at (point)))))

(defun py-mouseto-exception (event)
  "Jump to the code which caused the Python exception at EVENT.
EVENT is usually a mouse click."
  (interactive "e")
  (cond
   ((fboundp 'event-point)
    ;; XEmacs
    (let* ((point (event-point event))
           (buffer (event-buffer event))
           (e (and point buffer (extent-at point buffer 'py-exc-info)))
           (info (and e (extent-property e 'py-exc-info))))
      (message "Event point: %d, info: %s" point info)
      (and info
           (py--jump-to-exception (car info) nil (cdr info)))))))

(defun py-goto-exception (&optional file line)
  "Go to FILE and LINE indicated by the traceback."
  (interactive)
  (let ((file file)
        (line line))
    (unless (and file line)
      (save-excursion
        (beginning-of-line)
        (if (looking-at py-traceback-line-re)
            (setq file (substring-no-properties (match-string 1))
                  line (string-to-number (match-string 2))))))
    (if (not file)
        (error "Not on a traceback line"))
    (find-file file)
    (goto-char (point-min))
    (forward-line (1- line))))

(defun py--find-next-exception (start buffer searchdir errwhere)
  "Find the next Python exception and jump to the code that caused it.
START is the buffer position in BUFFER from which to begin searching
for an exception.  SEARCHDIR is a function, either
‘re-search-backward’ or ‘re-search-forward’ indicating the direction
to search.  ERRWHERE is used in an error message if the limit (top or
bottom) of the trackback stack is encountered."
  (let (file line)
    (save-excursion
      (with-current-buffer buffer
	(goto-char (py--point start))
	(if (funcall searchdir py-traceback-line-re nil t)
	    (setq file (match-string 1)
		  line (string-to-number (match-string 2))))))
    (if (and file line)
        (py-goto-exception file line)
      (error "%s of traceback" errwhere))))

(defun py-down-exception (&optional bottom)
  "Go to the next line down in the traceback.
With \\[univeral-argument] (programmatically, optional argument
BOTTOM), jump to the bottom (innermost) exception in the exception
stack."
  (interactive "P")
  (let* ((proc (get-process "Python"))
         (buffer (if proc "*Python*" py-output-buffer)))
    (if bottom
        (py--find-next-exception 'eob buffer 're-search-backward "Bottom")
      (py--find-next-exception 'eol buffer 're-search-forward "Bottom"))))

(defun py-up-exception (&optional top)
  "Go to the previous line up in the traceback.
With \\[universal-argument] (programmatically, optional argument TOP)
jump to the top (outermost) exception in the exception stack."
  (interactive "P")
  (let* ((proc (get-process "Python"))
         (buffer (if proc "*Python*" py-output-buffer)))
    (if top
        (py--find-next-exception 'bob buffer 're-search-forward "Top")
      (py--find-next-exception 'bol buffer 're-search-backward "Top"))))
;; ;
;;  obsolete by py--fetch-result
;;  followed by py--fetch-error
;;  still used by py--execute-ge24.3
(defun py--postprocess-intern (&optional origline exception-buffer)
  "Highlight exceptions found in BUF.

Optional ORIGLINE EXCEPTION-BUFFER
If an exception occurred return error-string, otherwise return nil.
BUF must exist.

Indicate LINE if code wasn't run from a file, thus remember line of source buffer"
  (let* ((pmx (copy-marker (point-max)))
	 estring ecode erg)
    ;; (switch-to-buffer (current-buffer))
    (goto-char pmx)
    (sit-for 0.1 t)
    (save-excursion
      (unless (looking-back py-pdbtrack-input-prompt (line-beginning-position))
        (forward-line -1)
        (end-of-line)
        (when (or (re-search-backward py-shell-prompt-regexp nil t 1)
                  (re-search-backward (concat py-ipython-input-prompt-re "\\|" py-ipython-output-prompt-re) nil t 1))
          (save-excursion
            (when (re-search-forward "File \"\\(.+\\)\", line \\([0-9]+\\)\\(.*\\)$" nil t)
              (setq erg (copy-marker (point)))
              (delete-region (progn (beginning-of-line)
				    (save-match-data
				      (when (looking-at
					     ;; all prompt-regexp known
					     py-fast-filter-re)
					(goto-char (match-end 0))))

				    (skip-chars-forward " \t\r\n\f")(point)) (line-end-position))
	      (insert (concat "    File " (buffer-name exception-buffer) ", line "
			      (prin1-to-string origline)))))
	  ;; these are let-bound as ‘tempbuf’
	  (and (boundp 'tempbuf)
	       ;; (message "%s" tempbuf)
	       (search-forward (buffer-name tempbuf) nil t)
	       (delete-region (line-beginning-position) (1+ (line-end-position))))
          ;; if no buffer-file exists, signal "Buffer", not "File(when
          (when erg
            (goto-char erg)
            ;; (forward-char -1)
            ;; (skip-chars-backward "^\t\r\n\f")
            ;; (skip-chars-forward " \t")
            (save-match-data
              (and (not (py--buffer-filename-remote-maybe
                         (or
                          (get-buffer exception-buffer)
                          (get-buffer (file-name-nondirectory exception-buffer)))))
		   (string-match "^[ \t]*File" (buffer-substring-no-properties (point) (line-end-position)))
		   (looking-at "[ \t]*File")
		   (replace-match " Buffer")))
            (push origline py-error)
            (push (buffer-name exception-buffer) py-error)
            (forward-line 1)
            (when (looking-at "[ \t]*\\([^\t\n\r\f]+\\)[ \t]*$")
              (setq estring (match-string-no-properties 1))
              (setq ecode (replace-regexp-in-string "[ \n\t\f\r^]+" " " estring))
              (push 'py-error ecode))))))
    py-error))

(defun py--find-next-exception-prepare (direction start)
  "According to DIRECTION and START setup exception regexps.

Depends from kind of Python shell."
  (let* ((name (get-process (substring (buffer-name (current-buffer)) 1 -1)))
         (buffer (cond (name (buffer-name (current-buffer)))
                       ((buffer-live-p (get-buffer py-output-buffer))
                        py-output-buffer)
                       (py-last-exeption-buffer (buffer-name py-last-exeption-buffer))
                       (t (error "Don't see exeption buffer")))))
    (when buffer (set-buffer (get-buffer buffer)))
    (if (eq direction 'up)
        (if (string= start "TOP")
            (py--find-next-exception 'bob buffer 're-search-forward "Top")
          (py--find-next-exception 'bol buffer 're-search-backward "Top"))
      (if (string= start "BOTTOM")
          (py--find-next-exception 'eob buffer 're-search-backward "Bottom")
        (py--find-next-exception 'eol buffer 're-search-forward "Bottom")))))

(defalias 'ipython-send-and-indent 'py-execute-line-ipython)
(defalias 'py-execute-region-in-shell 'py-execute-region)
(defalias 'py-ipython-shell-command-on-region 'py-execute-region-ipython)
(defalias 'py-shell-command-on-region 'py-execute-region)
(defalias 'py-send-region-ipython 'py-execute-region-ipython)

;; python-components-send
(defun py-output-buffer-filter (&optional beg end)
  "Clear output buffer from py-shell-input prompt etc.

Optional BEG END"
  (interactive "*")
  (let ((beg (cond (beg)
                   ((use-region-p)
                    (region-beginning))
                   (t (point-min))))
        (end (cond (end (copy-marker end))
                   ((use-region-p)
                    (copy-marker (region-end)))
                   (t (copy-marker (point-max))))))
    (goto-char beg)
    (while (re-search-forward (concat "\\(" py-shell-input-prompt-1-regexp "\\|" py-shell-input-prompt-2-regexp "\\|" "^In \\[[0-9]+\\]: *" "\\)") end (quote move) 1)
      (replace-match ""))
    (goto-char beg)))

(defun py-output-filter (strg)
  "Clear STRG from py-shell-input prompt."
  (interactive "*")
  (let (erg)
    (while
	(not (equal erg (setq erg (replace-regexp-in-string
				   (concat "\\(\n\\|" py-shell-input-prompt-1-regexp "\\|"
					   py-shell-input-prompt-2-regexp "\\|" "^In \\[[0-9]+\\]: *" "\\)") "" strg))))
      (sit-for 0.1 t))
    erg))

(defun py-send-string (strg &optional process)
  "Evaluate STRG in Python PROCESS."
  (interactive "sPython command: ")
  (let* ((proc (or process (get-buffer-process (py-shell))))
	 (buffer (process-buffer proc)))
    (with-current-buffer buffer
      (goto-char (point-max))
      (unless (string-match "\\`" strg)
	(comint-send-string proc "\n"))
      (comint-send-string proc strg)
      (goto-char (point-max))
      (unless (string-match "\n\\'" strg)
	;; Make sure the text is properly LF-terminated.
	(comint-send-string proc "\n"))
      ;; (when py-debug-p (message "%s" (current-buffer)))
      (goto-char (point-max)))))

;; python-components-shell-complete

(defalias 'py-script-complete 'py-shell-complete)
(defalias 'py-python2-shell-complete 'py-shell-complete)
(defalias 'py-python3-shell-complete 'py-shell-complete)

(defun py--shell-completion-get-completions (input process completion-code)
  "Retrieve available completions for INPUT using PROCESS.
Argument COMPLETION-CODE is the python code used to get
completions on the current context."
  (let ((erg
	 (py--send-string-return-output
	  (format completion-code input) process)))
    (sit-for 0.2 t)
    (when (and erg (> (length erg) 2))
      (setq erg (split-string erg "^'\\|^\"\\|;\\|'$\\|\"$" t)))
    erg))

;; post-command-hook
;; caused insert-file-contents error lp:1293172
(defun py--after-change-function (end)
  "Restore window-confiuration after completion.

Takes END"
  (when
      (and (or
            (eq this-command 'completion-at-point)
            (eq this-command 'choose-completion)
            (eq this-command 'choose-completion)
            (eq this-command 'py-shell-complete)
            (and (or
                  (eq last-command 'completion-at-point)
                  (eq last-command 'choose-completion)
                  (eq last-command 'choose-completion)
                  (eq last-command 'py-shell-complete))
                 (eq this-command 'self-insert-command))))
    (set-window-configuration
     py-last-window-configuration))
  (goto-char end))

(defalias 'ipython-complete 'py-shell-complete)

(defun py--try-completion-intern (input completion)
  (let (erg)
    (when (and (stringp (setq erg (try-completion input completion)))
	       (looking-back input (line-beginning-position))
	       (not (string= input erg)))
      (delete-region (match-beginning 0) (match-end 0))
      (insert erg))
    erg))

(defun py--try-completion (input completion)
  "Repeat `try-completion' as long as match are found.

Interal used. Takes INPUT COMPLETION"
  (let (erg newlist)
    (setq erg (py--try-completion-intern input completion))
    (when erg
      (dolist (elt completion)
	(unless (string= erg elt)
	  (push elt newlist)))
      (if (< 1 (length newlist))
	  (with-output-to-temp-buffer py-python-completions
	    (display-completion-list
	     (all-completions input (or newlist completion))))
	(when newlist (py--try-completion erg newlist)))
      (skip-chars-forward "^ \t\r\n\f")
      ;; (move-marker orig (point))
      nil)))

(defun py--shell-insert-completion-maybe (completion input)
  (cond ((eq completion t)
	 (and py-verbose-p (message "py--shell-do-completion-at-point %s" "`t' is returned, not completion. Might be a bug."))
	 nil)
	((or (null completion)
	     (and completion (stringp completion)
		  (or
		   (string-match "\\`''\\'" completion)
		   (string= "" completion))))
	 (and py-verbose-p (message "py--shell-do-completion-at-point %s" "Don't see a completion"))
	 nil)
	((and completion
	      (or (and (listp completion)
		       (string= input (car completion)))
		  (and (stringp completion)
		       (string= input completion))))
	 nil)
	((and completion (stringp completion)(not (string= input completion)))
	 (progn (delete-char (- (length input)))
		(insert completion)
		;; (move-marker orig (point))
		;; minibuffer.el expects a list, a bug IMO
		nil))
	(t (py--try-completion input completion)))

  nil)

(defun py--shell-do-completion-at-point (process imports input exception-buffer code)
  "Do completion at point for PROCESS.

Takes PROCESS IMPORTS INPUT EXCEPTION-BUFFER CODE"
  ;; (py--send-string-no-output py-shell-completion-setup-code process)
  (when imports
    (py--send-string-no-output imports process))
  ;; (py--delay-process-dependent process)
  (sit-for 0.1 t)
  (let* ((completion
	  (py--shell-completion-get-completions
	   input process code)))
    (set-buffer exception-buffer)
    ;; (py--delay-process-dependent process)
    ;; (sit-for 1 t)
    (py--shell-insert-completion-maybe completion input)))

(defun py--complete-base (shell word imports exception-buffer)
  (let* ((shell (or shell (py-choose-shell)))
         (proc (or
		;; completing inside a shell
		(get-buffer-process exception-buffer)
		   (and (comint-check-proc shell)
			(get-process shell))
	       (prog1
		   (get-buffer-process (py-shell nil nil shell))
		 (sit-for py-new-shell-delay))))
    (code (if (string-match "[Ii][Pp]ython*" shell)
	      (py-set-ipython-completion-command-string shell)
	    py-shell-module-completion-code)))
  (py--shell-do-completion-at-point proc imports word exception-buffer code)))

(defun py--complete-prepare (&optional shell beg end word fast-complete)
  (let* ((exception-buffer (current-buffer))
         (pos (copy-marker (point)))
	 (pps (parse-partial-sexp (or (ignore-errors (overlay-end comint-last-prompt-overlay))(line-beginning-position)) (point)))
	 (in-string (when (nth 3 pps) (nth 8 pps)))
         (beg
	  (save-excursion
	    (or beg
		(and in-string
		     ;; possible completion of filenames
		     (progn
		       (goto-char in-string)
		       (and
			(save-excursion
			  (skip-chars-backward "^ \t\r\n\f")(looking-at "open")))

		       (skip-chars-forward "\"'")(point)))
		(progn (and (eq (char-before) ?\()(forward-char -1))
		       (skip-chars-backward "a-zA-Z0-9_.'") (point)))))
         (end (or end (point)))
	 ;;
         (word (or word (buffer-substring-no-properties beg end)))
	 (ausdruck (and (string-match "^/" word)(setq word (substring-no-properties word 1))(concat "\"" word "*\"")))
	 ;; when in string, assume looking for filename
	 (filenames (and in-string ausdruck
			 (list (replace-regexp-in-string "\n" "" (shell-command-to-string (concat "find / -maxdepth 1 -name " ausdruck))))))
         (imports (py-find-imports))
         py-fontify-shell-buffer-p erg)
    (cond (fast-complete (py--fast-complete-base shell pos word imports exception-buffer))
	  ((and in-string filenames)
	   (when (setq erg (try-completion (concat "/" word) filenames))
	     (delete-region beg end)
	     (insert erg)))
	  (t (py--complete-base shell word imports exception-buffer)))
    nil))

(defun py-shell-complete (&optional shell beg end word)
  "Complete word before point, if any.

Optional SHELL BEG END WORD"
  (interactive)
  (save-excursion
    (and (buffer-live-p (get-buffer "*Python Completions*"))
	 (py-kill-buffer-unconditional "*Python Completions*")))
  (setq py-last-window-configuration
        (current-window-configuration))
  (py--complete-prepare shell beg end word nil))

(defun py-indent-or-complete ()
  "Complete or indent depending on the context.

If cursor is at end of a symbol, try to complete
Otherwise call `py-indent-line'

If `(use-region-p)' returns t, indent region.
Use `C-q TAB' to insert a literally TAB-character

In ‘python-mode’ `py-complete-function' is called,
in (I)Python shell-modes `py-shell-complete'"
  (interactive "*")
  (cond ((use-region-p)
	 (py-indent-region (region-beginning) (region-end)))
	((or (bolp)
	     (member (char-before)(list 9 10 12 13 32 ?: ?\) ?\] ?\}))
	     (not (looking-at "[ \t]*$")))
	 ;; (not (eolp)))
	 (py-indent-line))
	((or (eq major-mode 'python-mode)(derived-mode-p 'python-mode))	 (if (string-match "ipython" (py-choose-shell))
	     (py-shell-complete)
	   (funcall py-complete-function)))
	((comint-check-proc (current-buffer))
	 (py-shell-complete (process-name (get-buffer-process (current-buffer)))))
	(t
	 (funcall py-complete-function))))

;; python-components-pdb

(defun py-execute-statement-pdb ()
  "Execute statement running pdb."
  (interactive)
  (let ((py-python-command-args "-i -m pdb"))
    (py-execute-statement)))

(defun py-execute-region-pdb (beg end)
  "Takes region between BEG END."
  (interactive "r")
  (let ((py-python-command-args "-i -m pdb")))
    (py-execute-region beg end))

(defun py-pdb-execute-statement ()
  "Execute statement running pdb."
  (interactive)
  (let ((stm (progn (py-statement) (car kill-ring))))
    (py-execute-string (concat "import pdb;pdb.run('" stm "')"))))

(defun py-pdb-help ()
  "Print generic pdb.help() message."
  (interactive)
  (py-execute-string "import pdb;pdb.help()"))

;; https://stackoverflow.com/questions/6980749/simpler-way-to-put-pdb-breakpoints-in-python-code
;; breakpoint at line 3 

;; python -m pdb -c "b 3" -c c your_script.py

(defun py-pdb-break-at-current-line (&optional line file condition)
  "Set breakpoint at current line.

Optional LINE FILE CONDITION"
  (interactive)
  (py-execute-string (concat "import pdb;pdb.break('" (py-count-lines)  "')")))

(defun py--pdb-versioned ()
  "Guess existing pdb version from py-shell-name

Return \"pdb[VERSION]\" if executable found, just \"pdb\" otherwise"
  (interactive)
  (let ((erg (when (string-match "[23]" py-shell-name)
	       ;; versions-part
	       (substring py-shell-name (string-match "[23]" py-shell-name)))))
    (if erg
      (cond ((executable-find (concat "pdb" erg))
	     (concat "pdb" erg))
	    ((and (string-match "\\." erg)
		  (executable-find (concat "pdb" (substring erg 0 (string-match "\\." erg)))))
	     (concat "pdb" (substring erg 0 (string-match "\\." erg)))))
      "pdb")))

(defun py-pdb (command-line)
  "Run pdb on program FILE in buffer `*gud-FILE*'.
The directory containing FILE becomes the initial working directory
and source-file directory for your debugger.

At GNU Linux systems required pdb version should be detected by `py--pdb-version', at Windows configure `py-python-ms-pdb-command'

lp:963253"
  (interactive
   (progn
     (require 'gud)
     (list (gud-query-cmdline
	    (if (or (eq system-type 'ms-dos)(eq system-type 'windows-nt))
		(car (read-from-string py-python-ms-pdb-command))
	      ;; sys.version_info[0]
	      ;; (car (read-from-string (py--pdb-version)))
	      'pdb)
	    (py--buffer-filename-remote-maybe)))))
  (pdb command-line))

(defun py--pdb-current-executable ()
  "When py-pdb-executable is set, return it.

Otherwise return resuslt from `executable-find' "
  (or py-pdb-executable
      (executable-find "pdb")))

(defun py-update-gud-pdb-history ()
  "If pdb is called at a Python buffer, put it's file name at the head of `gud-pdb-history'. "
  (interactive)
  (let* (;; PATH/TO/pdb
	 (first (cond ((and gud-pdb-history (ignore-errors (car gud-pdb-history)))
		       (replace-regexp-in-string "^\\([^ ]+\\) +.+$" "\\1" (car gud-pdb-history)))
		      (py-pdb-executable
		       py-pdb-executable)
		      ((or (eq system-type 'ms-dos)(eq system-type 'windows-nt))
		       ;; lp:963253
		       "c:/python27/python\ -i\ c:/python27/Lib/pdb.py")
		      (t
		       (py--pdb-current-executable))))
	 ;; file to debug
         (second (cond ((not (ignore-errors
			       (py--buffer-filename-remote-maybe)))
			(error "%s" "Buffer must be saved first."))
		       ((py--buffer-filename-remote-maybe))
		       (t (and gud-pdb-history (stringp (car gud-pdb-history)) (replace-regexp-in-string "^\\([^ ]+\\) +\\(.+\\)$" "\\2" (car gud-pdb-history))))))
         (erg (and first second (concat first " " second))))
    (when erg
      (push erg gud-pdb-history))))

(defadvice pdb (before gud-query-cmdline activate)
  "Provide a better default command line when called interactively."
  (interactive
   (list (gud-query-cmdline py-pdb-path
                            ;; (file-name-nondirectory buffer-file-name)
			    (file-name-nondirectory (py--buffer-filename-remote-maybe)) ))))

;; tbreak [ ([filename:]lineno | function) [, condition] ]
;;         Same arguments as break, but sets a temporary breakpoint: it
;;         is automatically deleted when first hit.

;; python -m pdb -c "b 3" -c c your_script.py

(defun py-pdb-tbreak ()
  (interactive)
  (let (
	(py-python-command-args '("-i -c \"b 30\" -c c \"eyp.py\""))
	(py-python3-command-args '("-i -c \"b 30\" -c c \"eyp.py\""))
	)
    (py-execute-buffer)))


;; python-components-pdbtrack

;; pdbtrack constants
(defconst py-pdbtrack-stack-entry-regexp
   (concat ".*\\("py-shell-input-prompt-1-regexp">\\|>\\) *\\(.*\\)(\\([0-9]+\\))\\([?a-zA-Z0-9_<>()]+\\)()")
  "Regular expression pdbtrack uses to find a stack trace entry.")

(defconst py-pdbtrack-marker-regexp-file-group 2
  "Group position in gud-pydb-marker-regexp that matches the file name.")

(defconst py-pdbtrack-marker-regexp-line-group 3
  "Group position in gud-pydb-marker-regexp that matches the line number.")

(defconst py-pdbtrack-marker-regexp-funcname-group 4
  "Group position in gud-pydb-marker-regexp that matches the function name.")

(defconst py-pdbtrack-track-range 10000
  "Max number of characters from end of buffer to search for stack entry.")

(defvar py-pdbtrack-is-tracking-p nil)

(defun py--pdbtrack-overlay-arrow (activation)
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

(defun py--pdbtrack-track-stack-file (text)
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
        (py--pdbtrack-overlay-arrow nil)

      (let* ((procmark (process-mark currproc))
             (block (buffer-substring (max comint-last-input-end
                                           (- procmark
                                              py-pdbtrack-track-range))
                                      procmark))
             target target_fname target_lineno target_buffer)

        (if (not (string-match (concat py-pdbtrack-input-prompt "$") block))
            (py--pdbtrack-overlay-arrow nil)

          (setq target (py--pdbtrack-get-source-buffer block))

          (if (stringp target)
              (message "pdbtrack: %s" target)

            (setq target_lineno (car target))
            (setq target_buffer (cadr target))
            (setq target_fname
		  (py--buffer-filename-remote-maybe target_buffer))
            (switch-to-buffer-other-window target_buffer)
            (goto-char (point-min))
            (forward-line (1- target_lineno))
            (message "pdbtrack: line %s, file %s" target_lineno target_fname)
            (py--pdbtrack-overlay-arrow t)
            (pop-to-buffer origbuf t)))))))

(defun py--pdbtrack-map-filename (filename)

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

(defun py--pdbtrack-get-source-buffer (block)
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

      (cond ((string= filename "")
             (format "(Skipping empty filename)"))

            ((file-exists-p filename)
             (list lineno (find-file-noselect filename)))

            ((file-exists-p (py--pdbtrack-map-filename filename))
             (list lineno (find-file-noselect (py--pdbtrack-map-filename filename))))

            ((setq funcbuffer (py--pdbtrack-grub-for-buffer funcname lineno))
             (if (string-match "/Script (Python)$" filename)
                 ;; Add in number of lines for leading '##' comments:
                 (setq lineno
                       (+ lineno
                          (save-excursion
                            (with-current-buffer funcbuffer
			      (count-lines
			       (point-min)
			       (max (point-min)
				    (string-match "^\\([^#]\\|#[^#]\\|#$\\)"
						  (buffer-substring (point-min)
								    (point-max))))))))))
             (list lineno funcbuffer))

            ((= (elt filename 0) ?\<)
             (format "(Non-file source: '%s')" filename))

            (t (format "Not found: %s(), %s" funcname filename))))))

(defun py--pdbtrack-grub-for-buffer (funcname lineno)
  "Find most recent buffer itself named or having function funcname.

We walk the buffer-list history for python-mode buffers that are
named for funcname or define a function funcname."
  (let ((buffers (buffer-list))
        buf
        got)
    (while (and buffers (not got))
      (setq buf (car buffers)
            buffers (cdr buffers))
      (if (and (save-excursion
		 (with-current-buffer buf
		   (string= major-mode "python-mode")))
               (or (string-match funcname (buffer-name buf))
                   (string-match (concat "^\\s-*\\(def\\|class\\)\\s-+"
                                         funcname "\\s-*(")
                                 (save-excursion
                                   (with-current-buffer  buf
                                   (buffer-substring (point-min)
                                                     (point-max)))))))
          (setq got buf)))
    got))


;; pdbtrack functions
(defun py-pdbtrack-toggle-stack-tracking (arg)
  "Set variable `py-pdbtrack-do-tracking-p'. "
  (interactive "P")
  ;; (if (not (get-buffer-process (current-buffer)))
  ;; (error "No process associated with buffer '%s'" (current-buffer)))

  ;; missing or 0 is toggle, >0 turn on, <0 turn off
  (cond ((not arg)
         (setq py-pdbtrack-do-tracking-p (not py-pdbtrack-do-tracking-p)))
        ((zerop (prefix-numeric-value arg))
         (setq py-pdbtrack-do-tracking-p nil))
        ((> (prefix-numeric-value arg) 0)
         (setq py-pdbtrack-do-tracking-p t)))
  (if py-pdbtrack-do-tracking-p
      (progn
        (add-hook 'comint-output-filter-functions 'py--pdbtrack-track-stack-file t)
        (remove-hook 'comint-output-filter-functions 'python-pdbtrack-track-stack-file t))
    (remove-hook 'comint-output-filter-functions 'py--pdbtrack-track-stack-file t)
    )
  (message "%sabled Python's pdbtrack"
           (if py-pdbtrack-do-tracking-p "En" "Dis")))

(defun turn-on-pdbtrack ()
  (interactive)
  (py-pdbtrack-toggle-stack-tracking 1))

(defun turn-off-pdbtrack ()
  (interactive)
  (py-pdbtrack-toggle-stack-tracking 0))

;; python-components-help
(defvar py-eldoc-string-code
  "__PYDOC_get_help('''%s''')\n"
  "Python code used to get a string with the documentation of an object.")

(defalias 'py-eldoc 'py-eldoc-function)

;;  Info-look functionality.
(require 'info-look)
(eval-when-compile (require 'info))

(defun py-info-lookup-symbol ()
  "Call ‘info-lookup-symbol’.

Sends help if stuff is missing."
  (interactive)
  (if (functionp 'pydoc-info-add-help)
      (call-interactively 'info-lookup-symbol)
    (message "pydoc-info-add-help not found. Please check INSTALL-INFO-FILES")))

(info-lookup-add-help
 :mode 'python-mode
 :regexp "[[:alnum:]_]+"
 :doc-spec
'(("(python)Index" nil "")))

(defun python-after-info-look ()
  "Set up info-look for Python.

Tries to take account of versioned Python Info files, e.g. Debian's
python2.5-ref.info.gz.
Used with ‘eval-after-load’."
  (let* ((version (let ((s (shell-command-to-string (concat py-python-command
							    " -V"))))
		    (string-match "^Python \\([0-9]+\\.[0-9]+\\>\\)" s)
		    (match-string 1 s)))
	 ;; Whether info files have a Python version suffix, e.g. in Debian.
	 (versioned
	  (with-temp-buffer
	    (Info-mode)
	    ;; First look for Info files corresponding to the version
	    ;; of the interpreter we're running.
	    (condition-case ()
		;; Don't use ‘info’ because it would pop-up a *info* buffer.
		(progn
		  (Info-goto-node (format "(python%s-lib)Miscellaneous Index"
					  version))
		  t)
	      (error
	       ;; Otherwise see if we actually have an un-versioned one.
	       (condition-case ()
		   (progn
		     (Info-goto-node
		      (format "(python-lib)Miscellaneous Index" version))
		     nil)
		 (error
		  ;; Otherwise look for any versioned Info file.
		  (condition-case ()
		      (let (found)
			(dolist (dir (or Info-directory-list
					 Info-default-directory-list))
			  (unless found
			    (let ((file (car (file-expand-wildcards
					      (expand-file-name "python*-lib*"
								dir)))))
			      (if (and file
				       (string-match
					"\\<python\\([0-9]+\\.[0-9]+\\>\\)-"
					file))
				  (setq version (match-string 1 file)
					found t)))))
			found)
		    (error)))))))))
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
	 `((,(concat "(python" version "-ref)Miscellaneous Index"))
	   (,(concat "(python" version "-ref)Module Index"))
	   (,(concat "(python" version "-ref)Function-Method-Variable Index"))
	   (,(concat "(python" version "-ref)Class-Exception-Object Index"))
	   (,(concat "(python" version "-lib)Module Index"))
	   (,(concat "(python" version "-lib)Class-Exception-Object Index"))
	   (,(concat "(python" version "-lib)Function-Method-Variable Index"))
	   (,(concat "(python" version "-lib)Miscellaneous Index")))
       '(("(python-ref)Miscellaneous Index")
	 ("(python-ref)Module Index")
	 ("(python-ref)Function-Method-Variable Index")
	 ("(python-ref)Class-Exception-Object Index")
	 ("(python-lib)Module Index")
	 ("(python-lib)Class-Exception-Object Index")
	 ("(python-lib)Function-Method-Variable Index")
	 ("(python-lib)Miscellaneous Index"))))))

;;  (if (featurep 'info-look)
;;      (python-after-info-look))

;;  (eval-after-load "info-look" '(python-after-info-look))

;; ;
(defun py--warn-tmp-files-left ()
  "Detect and warn about file of form \"py11046IoE\" in py-temp-directory."
  (let ((erg1 (file-readable-p (concat py-temp-directory (char-to-string py-separator-char)  (car (directory-files  py-temp-directory nil "py[[:alnum:]]+$"))))))
    (when (and py-verbose-p erg1)
      (message "py--warn-tmp-files-left: %s ?" (concat py-temp-directory (char-to-string py-separator-char) (car (directory-files  py-temp-directory nil "py[[:alnum:]]*$")))))))

(defun py-fetch-docu ()
  "Lookup in current buffer for the doku for the symbol at point.

Useful for newly defined symbol, not known to python yet."
  (interactive)
  (let* ((symb (prin1-to-string (symbol-at-point)))
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
            (when (called-interactively-p 'any) (switch-to-buffer (current-buffer)))
            (insert erg)))))))

(defun py-info-current-defun (&optional include-type)
  "Return name of surrounding function.

Use Python compatible dotted expression syntax
Optional argument INCLUDE-TYPE indicates to include the type of the defun.
This function is compatible to be used as
‘add-log-current-defun-function’ since it returns nil if point is
not inside a defun."
  (interactive)
  (let ((names '())
        (min-indent)
        (first-run t))
    (save-restriction
      (widen)
      (save-excursion
        (goto-char (line-end-position))
        (forward-comment -9999)
        (setq min-indent (current-indentation))
        (while (py-beginning-of-def-or-class)
          (when (or (< (current-indentation) min-indent)
                    first-run)
            (setq first-run nil)
            (setq min-indent (current-indentation))
            (looking-at py-def-or-class-re)
            (setq names (cons
                         (if (not include-type)
                             (match-string-no-properties 1)
                           (mapconcat 'identity
                                      (split-string
                                       (match-string-no-properties 0)) " "))
                         names))))))
    (when names
      (mapconcat (lambda (strg) strg) names "."))))

(defalias 'py-describe-symbol 'py-help-at-point)
(defalias 'py-eldoc-function 'py-help-at-point)
(defun py--help-at-point-intern (orig)
  (let* ((beg (point))
	 (end (progn (skip-chars-forward "a-zA-Z0-9_." (line-end-position))(point)))
	 (sym (buffer-substring-no-properties beg end))
	 (origfile (py--buffer-filename-remote-maybe))
	 (temp (md5 (buffer-name)))
	 (file (concat (py--normalize-directory py-temp-directory) temp "-py-help-at-point.py"))
	 (cmd (py-find-imports))
	 ;; if symbol is defined in current buffer, go to
	 (erg (progn (goto-char (point-min))
		     (when
			 (re-search-forward (concat "^[ \t]*def " sym "(") nil t 1)
		       (forward-char -2)
		       (point)))))
    (if erg
	(progn (push-mark orig)(push-mark (point))
	       (when (and (called-interactively-p 'any) py-verbose-p) (message "Jump to previous position with %s" "C-u C-<SPC> C-u C-<SPC>")))
      (goto-char orig))
    ;; (when cmd
    ;;   (setq cmd (mapconcat
    ;; 		 (lambda (arg) (concat "try: " arg "\nexcept: pass\n"))
    ;; 		 (split-string cmd ";" t)
    ;; 		 "")))
    (setq cmd (concat cmd "\nimport pydoc\n"
		      ))
    (when (not py-remove-cwd-from-path)
      (setq cmd (concat cmd "import sys\n"
			"sys.path.insert(0, '"
			(file-name-directory origfile) "')\n")))
    (setq cmd (concat cmd "pydoc.help('" sym "')\n"))
    (with-temp-buffer
      (insert cmd)
      (write-file file))
    (py-process-file file "*Python-Help*")
    (when (file-readable-p file)
      (unless py-debug-p (delete-file file)))))

(defun py-help-at-point ()
  "Print help on symbol at point.

If symbol is defined in current buffer, jump to it's definition"
  (interactive)
  (let ((orig (point)))
    ;; avoid repeated call at identic pos
    (unless (eq orig (ignore-errors py-last-position))
      (setq py-last-position orig))
    (unless (member (get-buffer-window "*Python-Help*")(window-list))
      (window-configuration-to-register py-windows-config-register))
    (and (looking-back "(" (line-beginning-position))(not (looking-at "\\sw")) (forward-char -1))
    (if (or (eq (face-at-point) 'font-lock-string-face)(eq (face-at-point) 'font-lock-comment-face))
	(progn
	  (py-restore-window-configuration)
	  (goto-char orig))
      (if (or (< 0 (abs (skip-chars-backward "a-zA-Z0-9_." (line-beginning-position))))(looking-at "\\sw"))
	  (py--help-at-point-intern orig)
	(py-restore-window-configuration)))))

;;  Documentation functions

;;  dump the long form of the mode blurb; does the usual doc escapes,
;;  plus lines of the form ^[vc]:name\$ to suck variable & command docs
;;  out of the right places, along with the keys they're on & current
;;  values

(defun py--dump-help-string (str)
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
          (error "Error in py--dump-help-string, tag %s" funckind)))
        (princ (format "\n-> %s:\t%s\t%s\n\n"
                       (if (equal funckind "c") "Command" "Variable")
                       funcname keys))
        (princ funcdoc)
        (terpri)
        (setq start end))
      (princ (substitute-command-keys (substring str start)))
      ;; (and comint-vars-p (py-report-comint-variable-setting))
      )
    (if (featurep 'xemacs) (print-help-return-message)
      (help-print-return-message))))

(defun py-describe-mode ()
  "Dump long form of ‘python-mode’ docs."
  (interactive)
  (py--dump-help-string "Major mode for editing Python files.
Knows about Python indentation, tokens, comments and continuation lines.
Paragraphs are separated by blank lines only.

Major sections below begin with the string ‘@’; specific function and
variable docs begin with ->.

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

py-install-directory\twherefrom ‘python-mode’ looks for extensions
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

Each physical line in the file is either a ‘continuation line’ (the
preceding line ends with a backslash that's not part of a comment, or
the paren/bracket/brace nesting level at the start of the line is
non-zero, or both) or an ‘initial line’ (everything else).

An initial line is in turn a ‘blank line’ (contains nothing except
possibly blanks or tabs), a ‘comment line’ (leftmost non-blank
character is ‘#’), or a ‘code line’ (everything else).

Comment Lines

Although all comment lines are treated alike by Python, Python mode
recognizes two kinds that act differently with respect to indentation.

An ‘indenting comment line’ is a comment line with a blank, tab or
nothing after the initial ‘#’.  The indentation commands (see below)
treat these exactly as if they were code lines: a line following an
indenting comment line will be indented like the comment line.  All
other comment lines (those with a non-whitespace character immediately
following the initial ‘#’) are ‘non-indenting comment lines’, and
their indentation is ignored by the indentation commands.

Indenting comment lines are by far the usual case, and should be used
whenever possible.  Non-indenting comment lines are useful in cases
like these:

\ta = b # a very wordy single-line comment that ends up being
\t #... continued onto another line

\tif a == b:
##\t\tprint 'panic!' # old code we've ‘commented out’
\t\treturn a

Since the ‘#...’ and ‘##’ comment lines have a non-whitespace
character following the initial ‘#’, Python mode ignores them when
computing the proper indentation for the next line.

Continuation Lines and Statements

The ‘python-mode’ commands generally work on statements instead of on
individual lines, where a ‘statement’ is a comment or blank line, or a
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
automatically by ‘python-mode’ is just an educated guess:  only you know
the block structure you intend, so only you can supply correct
indentation.

The \\[indent-for-tab-command] and \\[py-newline-and-indent] keys try to suggest plausible indentation, based on
the indentation of preceding statements.  E.g., assuming
py-indent-offset is 4, after you enter
\tif a > 0: \\[py-newline-and-indent]
the cursor will be moved to the position of the ‘_’ (_ is not a
character in the file, it's just used here to indicate the location of
the cursor):
\tif a > 0:
\t _
If you then enter ‘c = d’ \\[py-newline-and-indent], the cursor will move
to
\tif a > 0:
\t c = d
\t _
‘python-mode’ cannot know whether that's what you intended, or whether
\tif a > 0:
\t c = d
\t_
was your intent.  In general, ‘python-mode’ either reproduces the
indentation of the (closest code or indenting-comment) preceding
statement, or adds an extra py-indent-offset blanks if the preceding
statement has ‘:’ as its last significant (non-whitespace and non-
comment) character.  If the suggested indentation is too much, use
\\[py-electric-backspace] to reduce it.

Continuation lines are given extra indentation.  If you don't like the
suggested indentation, change it to something you do like, and Python-
mode will strive to indent later lines of the statement in the same way.

If a line is a continuation line by virtue of being in an unclosed
paren/bracket/brace structure (‘list’, for short), the suggested
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
than the backslash following the leftmost assigning ‘=’, the second line
is indented two columns beyond that ‘=’.  Else it's indented to two
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

The remaining ‘indent’ functions apply to a region of Python code.  They
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
do not count as ‘statements’ for these commands.  So, e.g., you can go
to the first code statement in a file by entering
\t\\[beginning-of-buffer]\t to move to the top of the file
\t\\[py-next-statement]\t to skip over initial comments and blank lines
Or do \\[py-previous-statement] with a huge prefix argument.
%c:py-previous-statement
%c:py-next-statement
%c:py-goto-block-up
%c:py-beginning-of-def-or-class
%c:py-end-of-def-or-class

@LITTLE-KNOWN EMACS COMMANDS PARTICULARLY USEFUL IN PYTHON MODE

\\[indent-new-comment-line] is handy for entering a multi-line comment.

\\[set-selective-display] with a ‘small’ prefix arg is ideally suited for viewing the
overall class and def structure of a module.

‘\\[back-to-indentation]’ moves point to a line's first non-blank character.

‘\\[indent-relative]’ is handy for creating odd indentation.

@OTHER EMACS HINTS

If you don't like the default value of a variable, change its value to
whatever you do like by putting a ‘setq’ line in your .emacs file.
E.g., to set the indentation increment to 4, put this line in your
.emacs:
\t(setq py-indent-offset 4)
To see the value of a variable, do ‘\\[describe-variable]’ and enter the variable
name at the prompt.

When entering a key sequence like ‘C-c C-n’, it is not necessary to
release the CONTROL key after doing the ‘C-c’ part -- it suffices to
press the CONTROL key, press and release ‘c’ (while still holding down
CONTROL), press and release ‘n’ (while still holding down CONTROL), &
then release CONTROL.

Entering Python mode calls with no arguments the value of the variable
‘python-mode-hook’, if that value exists and is not nil; for backward
compatibility it also tries ‘py-mode-hook’; see the ‘Hooks’ section of
the Elisp manual for details.

Obscure:  When python-mode is first loaded, it looks for all bindings
to newline-and-indent in the global keymap, and shadows them with
local bindings to py-newline-and-indent."))

;;  (require 'info-look)
;;  The info-look package does not always provide this function (it
;;  appears this is the case with XEmacs 21.1)
(when (fboundp 'info-lookup-maybe-add-help)
  (info-lookup-maybe-add-help
   :mode 'python-mode
   :regexp "[a-zA-Z0-9_]+"
   :doc-spec '(("(python-lib)Module Index")
               ("(python-lib)Class-Exception-Object Index")
               ("(python-lib)Function-Method-Variable Index")
               ("(python-lib)Miscellaneous Index"))))

(defun py--find-definition-in-source (sourcefile symbol)
  (called-interactively-p 'any) (message "sourcefile: %s" sourcefile)
  (when (find-file sourcefile)
    ;; (if (stringp py-separator-char)
    ;; py-separator-char
    ;; (char-to-string py-separator-char))

    (goto-char (point-min))
    (when
	(or (re-search-forward (concat py-def-or-class-re symbol) nil t 1)
	    (progn
	      ;; maybe a variable definition?
	      (goto-char (point-min))
	      (re-search-forward (concat "^.+ " symbol) nil t 1)))
      (push-mark)
      (goto-char (match-beginning 0))
      (exchange-point-and-mark))))

;;  Find function stuff, lifted from python.el
(defalias 'py-find-function 'py-find-definition)
(defun py--find-definition-question-type (symbol imports)
  (let (erg)
    (cond ((setq erg (py--send-string-return-output (concat "import inspect;inspect.isbuiltin(\"" symbol "\")"))))
	  (t (setq erg (py--send-string-return-output (concat imports "import inspect;inspect.getmodule(\"" symbol "\")")))))
    erg))

(defun py-find-definition (&optional symbol)
  "Find source of definition of SYMBOL.

Interactively, prompt for SYMBOL."
  (interactive)
  ;; (set-register 98888888 (list (current-window-configuration) (point-marker)))
  (let* ((last-window-configuration
          (current-window-configuration))
         (py-exception-buffer (current-buffer))
         (imports (py-find-imports))
         (symbol (or symbol (with-syntax-table py-dotted-expression-syntax-table
                              (current-word))))
         (enable-recursive-minibuffers t)
         (symbol
          (if (called-interactively-p 'any)
              (read-string (if symbol
                               (format "Find location of (default %s): " symbol)
                             "Find location of: ")
                           nil nil symbol)
            symbol))
         (local (or
                 (py--until-found (concat "class " symbol) imenu--index-alist)
                 (py--until-found symbol imenu--index-alist)))
         erg sourcefile)
    ;; ismethod(), isclass(), isfunction() or isbuiltin()
    ;; ismethod isclass isfunction isbuiltin)
    (if local
        (if (numberp local)
            (progn
              (goto-char local)
              (search-forward symbol (line-end-position) nil 1)
              (push-mark)
	      (setq erg (buffer-substring-no-properties (line-beginning-position) (match-end 0)))
              (goto-char (match-beginning 0))
              (exchange-point-and-mark))
          (error "%s" "local not a number"))
      (setq erg (py--find-definition-question-type symbol imports))
      (cond ((string-match "SyntaxError" erg)
             (setq erg (substring-no-properties erg (match-beginning 0)))
             (set-window-configuration last-window-configuration)
             ;; (jump-to-register 98888888)
             (message "Can't get source: %s" erg))
            ((and erg (string-match "builtin" erg))
             (progn
               (set-window-configuration last-window-configuration)
               ;; (jump-to-register 98888888)
	       (message "%s" erg)))
            ((and erg (setq erg (replace-regexp-in-string "'" "" (py--send-string-return-output "import os;os.getcwd()")))
                  (setq sourcefile (replace-regexp-in-string "'" "" (py--send-string-return-output (concat "inspect.getsourcefile(" symbol ")")))))
	     (message "%s" sourcefile)
	     (py--find-definition-in-source sourcefile symbol)
             (display-buffer py-exception-buffer))))
    erg))

(defun py-find-imports ()
  "Find top-level imports.

Returns imports"
  (interactive)
  (let (imports erg)
    (save-excursion
      (if (eq major-mode 'comint-mode)
	  (progn
	    (re-search-backward comint-prompt-regexp nil t 1)
	    (goto-char (match-end 0))
	    (while (re-search-forward
		    "import *[A-Za-z_][A-Za-z_0-9].*\\|^from +[A-Za-z_][A-Za-z_0-9.]+ +import .*" nil t)
	      (setq imports
		    (concat
		     imports
		     (replace-regexp-in-string
		      "[\\]\r?\n?\s*" ""
		      (buffer-substring-no-properties (match-beginning 0) (point))) ";")))
	    (when (ignore-errors (string-match ";" imports))
	      (setq imports (split-string imports ";" t))
	      (dolist (ele imports)
		(and (string-match "import" ele)
		     (if erg
			 (setq erg (concat erg ";" ele))
		       (setq erg ele)))
		(setq imports erg))))
	(goto-char (point-min))
	(while (re-search-forward
		"^import *[A-Za-z_][A-Za-z_0-9].*\\|^from +[A-Za-z_][A-Za-z_0-9.]+ +import .*" nil t)
	  (unless (py--end-of-statement-p)
	    (py-forward-statement))
	  (setq imports
		(concat
		 imports
		 (replace-regexp-in-string
		  "[\\]\r*\n*\s*" ""
		  (buffer-substring-no-properties (match-beginning 0) (point))) ";")))))
    ;; (and imports
    ;; (setq imports (replace-regexp-in-string ";$" "" imports)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" imports))
    imports))

(defun py-update-imports ()
  "Return imports.

Imports done are displayed in message buffer."
  (interactive)
  (save-excursion
    (let ((py-exception-buffer (current-buffer))
          (orig (point))
          (erg (py-find-imports)))

      ;; (mapc 'py-execute-string (split-string (car (read-from-string (py-find-imports))) "\n" t)))
      ;; (setq erg (car (read-from-string python-imports)))
      (goto-char orig)
      (when (called-interactively-p 'any)
        (switch-to-buffer (current-buffer))
        (message "%s" erg))
      erg)))

;;  Code-Checker
;;  pep8
(defalias 'pep8 'py-pep8-run)
(defun py-pep8-run (command)
  "*Run pep8 using COMMAND, check formatting - default on the file currently visited."
  (interactive
   (let ((default
           (if (py--buffer-filename-remote-maybe)
               (format "%s %s %s" py-pep8-command
                       (mapconcat 'identity py-pep8-command-args " ")
                       (py--buffer-filename-remote-maybe))
             (format "%s %s" py-pep8-command
                     (mapconcat 'identity py-pep8-command-args " "))))
         (last (when py-pep8-history
                 (let* ((lastcmd (car py-pep8-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (py--buffer-filename-remote-maybe) cmd))))
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
  "Display pep8 command line help messages."
  (interactive)
  (set-buffer (get-buffer-create "*pep8-Help*"))
  (erase-buffer)
  (shell-command "pep8 --help" "*pep8-Help*"))

;;  Pylint
(defalias 'pylint 'py-pylint-run)
(defun py-pylint-run (command)
  "Run pylint from COMMAND (default on the file currently visited).

For help see \\[pylint-help] resp. \\[pylint-long-help].
Home-page: http://www.logilab.org/project/pylint"
  (interactive
   (let ((default (format "%s %s %s" py-pylint-command
			  (mapconcat 'identity py-pylint-command-args " ")
			  (py--buffer-filename-remote-maybe)))
         (last (and py-pylint-history (car py-pylint-history))))
     (list (funcall (if (fboundp 'read-shell-command)
			'read-shell-command 'read-string)
		    "Run pylint like this: "
		    (or default last)
		    'py-pylint-history))))
    (save-some-buffers (not py-ask-about-save))
  (set-buffer (get-buffer-create "*Pylint*"))
  (erase-buffer)
  (unless (file-readable-p (car (cddr (split-string command))))
    (message "Warning: %s" "pylint needs a file"))
  (shell-command command "*Pylint*"))

(defalias 'pylint-help 'py-pylint-help)
(defun py-pylint-help ()
  "Display Pylint command line help messages.

Let's have this until more Emacs-like help is prepared"
  (interactive)
  (set-buffer (get-buffer-create "*Pylint-Help*"))
  (erase-buffer)
  (shell-command "pylint --long-help" "*Pylint-Help*"))

(defalias 'pylint-doku 'py-pylint-doku)
(defun py-pylint-doku ()
  "Display Pylint Documentation.

Calls ‘pylint --full-documentation’"
  (interactive)
  (set-buffer (get-buffer-create "*Pylint-Documentation*"))
  (erase-buffer)
  (shell-command "pylint --full-documentation" "*Pylint-Documentation*"))

;;  Pyflakes
(defalias 'pyflakes 'py-pyflakes-run)
(defun py-pyflakes-run (command)
  "*Run pyflakes on COMMAND (default on the file currently visited).

For help see \\[pyflakes-help] resp. \\[pyflakes-long-help].
Home-page: http://www.logilab.org/project/pyflakes"
  (interactive
   (let ((default
           (if (py--buffer-filename-remote-maybe)
               (format "%s %s %s" py-pyflakes-command
                       (mapconcat 'identity py-pyflakes-command-args " ")
                       (py--buffer-filename-remote-maybe))
             (format "%s %s" py-pyflakes-command
                     (mapconcat 'identity py-pyflakes-command-args " "))))
         (last (when py-pyflakes-history
                 (let* ((lastcmd (car py-pyflakes-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (py--buffer-filename-remote-maybe) cmd))))
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

Let's have this until more Emacs-like help is prepared"
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

Extracted from http://manpages.ubuntu.com/manpages/natty/man1/pyflakes.1.html"))))

;;  Pyflakes-pep8
(defalias 'pyflakespep8 'py-pyflakespep8-run)
(defun py-pyflakespep8-run (command)
  "*Run COMMAND pyflakespep8, check formatting (default on the file currently visited)."
  (interactive
   (let ((default
           (if (py--buffer-filename-remote-maybe)
               (format "%s %s %s" py-pyflakespep8-command
                       (mapconcat 'identity py-pyflakespep8-command-args " ")
                       (py--buffer-filename-remote-maybe))
             (format "%s %s" py-pyflakespep8-command
                     (mapconcat 'identity py-pyflakespep8-command-args " "))))
         (last (when py-pyflakespep8-history
                 (let* ((lastcmd (car py-pyflakespep8-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (py--buffer-filename-remote-maybe) cmd))))
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
  "Display pyflakespep8 command line help messages."
  (interactive)
  (set-buffer (get-buffer-create "*pyflakespep8-Help*"))
  (erase-buffer)
  (shell-command "pyflakespep8 --help" "*pyflakespep8-Help*"))

;;  Pychecker
;;  hack for GNU Emacs
;;  (unless (fboundp 'read-shell-command)
;;  (defalias 'read-shell-command 'read-string))

(defun py-pychecker-run (command)
  "Run COMMAND pychecker (default on the file currently visited)."
  (interactive
   (let ((default
           (if (py--buffer-filename-remote-maybe)
               (format "%s %s %s" py-pychecker-command
		       py-pychecker-command-args
		       (py--buffer-filename-remote-maybe))
             (format "%s %s" py-pychecker-command py-pychecker-command-args)))
         (last (when py-pychecker-history
                 (let* ((lastcmd (car py-pychecker-history))
                        (cmd (cdr (reverse (split-string lastcmd))))
                        (newcmd (reverse (cons (py--buffer-filename-remote-maybe) cmd))))
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

;;  After ‘sgml-validate-command’.
(defun py-check-command (command)
  "Check a Python file (default current buffer's file).
Runs COMMAND, a shell command, as if by ‘compile’.
See ‘py-check-command’ for the default."
  (interactive
   (list (read-string "Checker command: "
                      (concat py-check-command " "
                              (let ((name (py--buffer-filename-remote-maybe)))
                                (if name
                                    (file-name-nondirectory name)))))))
  (require 'compile)                    ;To define compilation-* variables.
  (save-some-buffers (not compilation-ask-about-save) nil)
  (let ((compilation-error-regexp-alist
	 (cons '("(\\([^,]+\\), line \\([0-9]+\\))" 1 2)
	       compilation-error-regexp-alist)))
    (compilation-start command)))

;;  flake8
(defalias 'flake8 'py-flake8-run)
(defun py-flake8-run (command)
  "COMMAND Flake8 is a wrapper around these tools:
- PyFlakes
        - pep8
        - Ned Batchelder's McCabe script

        It also adds features:
        - files that contain this line are skipped::
            # flake8: noqa
        - no-warn lines that contain a `# noqa`` comment at the end.
        - a Git and a Mercurial hook.
        - a McCabe complexity checker.
        - extendable through ``flake8.extension`` entry points."
  (interactive
   (let* ((py-flake8-command
           (if (string= "" py-flake8-command)
               (or (executable-find "flake8")
                   (error "Don't see \"flake8\" on your system.
Consider \"pip install flake8\" resp. visit \"pypi.python.org\""))
             py-flake8-command))
          (default
            (if (py--buffer-filename-remote-maybe)
                (format "%s %s %s" py-flake8-command
                        py-flake8-command-args
                        (py--buffer-filename-remote-maybe))
              (format "%s %s" py-flake8-command
                      py-flake8-command-args)))
          (last
           (when py-flake8-history
             (let* ((lastcmd (car py-flake8-history))
                    (cmd (cdr (reverse (split-string lastcmd))))
                    (newcmd (reverse (cons (py--buffer-filename-remote-maybe) cmd))))
               (mapconcat 'identity newcmd " ")))))
     (list
      (if (fboundp 'read-shell-command)
          (read-shell-command "Run flake8 like this: "
                              ;; (if last
                              ;; last
                              default
                              'py-flake8-history1)
        (read-string "Run flake8 like this: "
                     (if last
                         last
                       default)
                     'py-flake8-history)))))
  (save-some-buffers (not py-ask-about-save) nil)
  (if (fboundp 'compilation-start)
      ;; Emacs.
      (compilation-start command)
    ;; XEmacs.
    (when (featurep 'xemacs)
      (compile-internal command "No more errors"))))

(defun py-flake8-help ()
  "Display flake8 command line help messages."
  (interactive)
  (set-buffer (get-buffer-create "*flake8-Help*"))
  (erase-buffer)
  (shell-command "flake8 --help" "*flake8-Help*"))

;;  from string-strip.el --- Strip CHARS from STRING

(defvar py-chars-before " \t\n\r\f"
  "Used by ‘py--string-strip’.")

(defvar py-chars-after " \t\n\r\f"
    "Used by ‘py--string-strip’.")

;;  (setq strip-chars-before  "[ \t\r\n]*")
(defun py--string-strip (str &optional chars-before chars-after)
  "Return a copy of STR, CHARS removed.
‘CHARS-BEFORE’ and ‘CHARS-AFTER’ default is \"[ \t\r\n]*\",
i.e. spaces, tabs, carriage returns, newlines and newpages."
  (let ((s-c-b (or chars-before
                   py-chars-before))
        (s-c-a (or chars-after
                   py-chars-after))
        (erg str))
    (setq erg (replace-regexp-in-string  s-c-b "" erg))
    (setq erg (replace-regexp-in-string  s-c-a "" erg))
    erg))

(defun py-nesting-level (&optional pps)
  "Accepts the output of ‘parse-partial-sexp’ - PPS."
  (interactive)
  (let* ((pps (or (ignore-errors (nth 0 pps))
                  (if (featurep 'xemacs)
                      (parse-partial-sexp (point-min) (point))
                    (parse-partial-sexp (point-min) (point)))))
         (erg (nth 0 pps)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

;;  ffap
(defun py-ffap-module-path (module)
  "Function for ‘ffap-alist’ to return path for MODULE."
  (let ((process (or
                  (and (eq major-mode 'py-shell-mode)
                       (get-buffer-process (current-buffer)))
                  (py-shell-get-process))))
    (if (not process)
        nil
      (let ((module-file
             (py--send-string-no-output
              (format py-ffap-string-code module) process)))
        (when module-file
          (substring-no-properties module-file 1 -1))))))

(eval-after-load "ffap"
  '(progn
     (push '(python-mode . py-ffap-module-path) ffap-alist)
     (push '(py-shell-mode . py-ffap-module-path) ffap-alist)))

;;  Flymake
(defun py-toggle-flymake-intern (name command)
  "Clear flymake allowed file-name masks.

Takes NAME COMMAND"
  (unless (string-match "pyflakespep8" name)
    (unless (executable-find name)
      (when py-verbose-p (message "Don't see %s. Use ‘easy_install’ %s? " name name))))
  (if (py--buffer-filename-remote-maybe)
      (let* ((temp-file (flymake-init-create-temp-buffer-copy
                         'flymake-create-temp-inplace))
             (local-file (file-relative-name
                          temp-file
                          (file-name-directory (py--buffer-filename-remote-maybe)))))
        (push (car (read-from-string (concat "(\"\\.py\\'\" flymake-" name ")"))) flymake-allowed-file-name-masks)
        (list command (list local-file)))
    (message "%s" "flymake needs a ‘file-name’. Please save before calling.")))

(defun py-flycheck-mode (&optional arg)
  "Toggle ‘flycheck-mode’.

With negative ARG switch off ‘flycheck-mode’
See menu \"Tools/Syntax Checking\""
  (interactive "p")
  (setq arg (or arg (if flycheck-mode 0 1)))
  (if (featurep 'flycheck)
      (if (< arg 0)
	  ;; switch off
	  (flycheck-mode 0)
	(when (and py-verbose-p (called-interactively-p 'any)) (message "flycheck-mode: %s" flycheck-mode))
	(flycheck-mode 1)
	(when (and py-verbose-p (called-interactively-p 'any)) (message "flycheck-mode: %s" flycheck-mode)))
    (error "Can't find flycheck - see README.org")))

(defun pylint-flymake-mode ()
  "Toggle ‘pylint’ ‘flymake-mode’."
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode 0)
    (py-toggle-flymake-intern "pylint" "pylint")
    (flymake-mode 1)))

(defun pyflakes-flymake-mode ()
  "Toggle ‘pyflakes’ ‘flymake-mode’."
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pyflakes" "pyflakes")
    (flymake-mode)))

(defun pychecker-flymake-mode ()
  "Toggle ‘pychecker’ ‘flymake-mode’."
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pychecker" "pychecker")
    (flymake-mode)))

(defun pep8-flymake-mode ()
  "Toggle ‘pep8’ ‘flymake-mode’."
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pep8" "pep8")
    (flymake-mode)))

(defun pyflakespep8-flymake-mode ()
  "Toggle ‘pyflakespep8’ ‘flymake-mode’.

Joint call to pyflakes and pep8 as proposed by
Keegan Carruthers-Smith"
  (interactive)
  (if flymake-mode
      ;; switch off
      (flymake-mode)
    (py-toggle-flymake-intern "pyflakespep8" "pyflakespep8")
    (flymake-mode)))

;; ;
(defun variables-state (&optional buffer directory-in directory-out)
  "Diplays state of ‘python-mode’ variables in an ‘org-mode’ BUFFER.

Optional DIRECTORY-IN DIRECTORY-OUT
Reads variables from python-mode.el as current buffer.

Variables which would produce a large output are left out:
- syntax-tables
- ‘python-mode-map’

Maybe call \\[describe-variable] RET to query its value."
  (interactive)
  (variables-prepare "state"))

(defun variables-base-state (exception-buffer orgname reSTname directory-in directory-out)
  (save-restriction
    (let ((suffix (file-name-nondirectory (py--buffer-filename-remote-maybe)))
          variableslist)
      ;; (widen)
      (goto-char (point-min))
      ;; (eval-buffer)
      (while (and (not (eobp))(re-search-forward "^(defvar [[:alpha:]]\\|^(defcustom [[:alpha:]]\\|^(defconst [[:alpha:]]" nil t 1))
        (let* ((name (symbol-at-point))
               (state
                (unless
                    (or (eq name 'py-menu)
                        (eq name 'python-mode-map)
                        (string-match "syntax-table" (prin1-to-string name)))

                  (prin1-to-string (symbol-value name)))))
          (if state
              (push (cons (prin1-to-string name) state) variableslist)
            (message "don't see a state for %s" (prin1-to-string name))))
        (forward-line 1))
      (setq variableslist (nreverse variableslist))
      ;; (with-temp-buffer
      (set-buffer (get-buffer-create "State-of-Python-mode-variables.org"))
      (erase-buffer)
      ;; org
      (insert "State of python-mode variables\n\n")
      (switch-to-buffer (current-buffer))
      (dolist (ele variableslist)
        (if (string-match "^;;; " (car ele))
            (unless (or (string-match "^;;; Constants\\|^;;; Commentary\\|^;;; Code\\|^;;; Macro definitions\\|^;;; Customization" (car ele)))

              (insert (concat (replace-regexp-in-string "^;;; " "* " (car ele)) "\n")))
          (insert (concat "\n** "(car ele) "\n"))
          (insert (concat "   " (cdr ele) "\n\n")))
        ;; (richten)
        (sit-for 0.01))
      (sit-for 0.01)
      (org-mode))))

;; common typo
(defalias 'iypthon 'ipython)
(defalias 'pyhton 'python)

;; python-components-extensions

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
      (if (and (py--in-comment-p)(not py-indent-comments))
          (forward-line 1)
        (py-indent-line-outmost)
        (unless (eq 4 (prefix-numeric-value arg))
          (if (eobp) (newline)
            (progn (forward-line 1))
            (when (and py-kill-empty-line (empty-line-p) (not (looking-at "[ \t]*\n[[:alpha:]]")) (not (eobp)))
              (delete-region (line-beginning-position) (line-end-position)))))))
    (back-to-indentation)
    (when (or (eq 4 (prefix-numeric-value arg)) (< orig (point))) (setq erg (current-column)))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-dedent-forward-line (&optional arg)
  "Dedent line and move one line forward. "
  (interactive "*p")
  (py-dedent arg)
  (if (eobp)
      (newline)
    (forward-line 1))
  (end-of-line))

(defun py-dedent (&optional arg)
  "Dedent line according to `py-indent-offset'.

With arg, do it that many times.
If point is between indent levels, dedent to next level.
Return indentation reached, if dedent done, nil otherwise.

Affected by `py-dedent-keep-relative-column'. "
  (interactive "*p")
  (or arg (setq arg 1))
  (let ((orig (copy-marker (point)))
        erg)
    (dotimes (_ arg)
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
    (when py-dedent-keep-relative-column (goto-char orig))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-class-at-point ()
  "Return class definition as string.

With interactive call, send it to the message buffer too. "
  (interactive)
  (save-excursion
    (let* ((beg (py-backward-class))
	   (end (py-forward-class))
	   (res (when (and (numberp beg)(numberp end)(< beg end)) (buffer-substring-no-properties beg end))))
      (when (called-interactively-p 'any) (message "%s" res))
      res)))

(defun py-function-at-point ()
  "Return functions definition as string.

With interactive call, send it to the message buffer too. "
  (interactive)
  (save-excursion
    (let* ((beg (py-backward-function))
	   (end (py-forward-function))
	   (res (when (and (numberp beg)(numberp end)(< beg end)) (buffer-substring-no-properties beg end))))
      (when (called-interactively-p 'any) (message "%s" res))
      res)))

(defun py-backward-function ()
  "Jump to the beginning of defun. Returns point. "
  (interactive "p")
  (let ((pos (py-backward-def-or-class)))
    (when (called-interactively-p 'any) (message "%s" pos))
    pos))

(defun py-forward-function ()
  "Jump to the end of function. "
  (interactive "p")
  (let ((pos (py-forward-def-or-class)))
    (when (called-interactively-p 'any) (message "%s" pos))
    pos))

;; Functions for marking regions

(defun py-line-at-point ()
  "Return line as string.
  With interactive call, send it to the message buffer too. "
  (interactive)
  (let* ((beg (line-beginning-position))
	 (end (line-end-position))
	 (res (when (and (numberp beg)(numberp end)(< beg end)) (buffer-substring-no-properties beg end))))
    (when (called-interactively-p 'any) (message "%s" res))
    res))

(defun py-match-paren-mode (&optional arg)
  "py-match-paren-mode nil oder t"
  (interactive "P")
  (if (or arg (not py-match-paren-mode))
      (progn
	(setq py-match-paren-mode t)
        (setq py-match-paren-mode nil))))

(defun py--match-end-finish (cui)
  (let (skipped)
    (unless (eq (current-column) cui)
      (when (< (current-column) cui)
	(setq skipped (skip-chars-forward " \t" (line-end-position)))
	(setq cui (- cui skipped))
	;; may current-column greater as needed indent?
	(if (< 0 cui)
	    (progn
	      (unless (empty-line-p) (split-line))
	      (indent-to cui))
	  (forward-char cui))
	(unless (eq (char-before) 32)(insert 32)(forward-char -1))))))

(defun py--match-paren-forward ()
  (setq py--match-paren-forward-p t)
  (let ((cui (current-indentation)))
    (cond
     ((py--beginning-of-top-level-p)
      (py-forward-top-level-bol)
      (py--match-end-finish cui))
     ((py--beginning-of-class-p)
      (py-forward-class-bol)
      (py--match-end-finish cui))
     ((py--beginning-of-def-p)
      (py-forward-def-bol)
      (py--match-end-finish cui))
     ((py--beginning-of-if-block-p)
      (py-forward-if-block-bol)
      (py--match-end-finish cui))
     ((py--beginning-of-try-block-p)
      (py-forward-try-block-bol)
      (py--match-end-finish cui))
     ((py--beginning-of-for-block-p)
      (py-forward-for-block-bol)
      (py--match-end-finish cui))
     ((py--beginning-of-block-p)
      (py-forward-block-bol)
      (py--match-end-finish cui))
     ((py--beginning-of-clause-p)
      (py-forward-clause-bol)
      (py--match-end-finish cui))
     ((py--beginning-of-statement-p)
      (py-forward-statement-bol)
      (py--match-end-finish cui))
     (t (py-forward-statement)
	(py--match-end-finish cui)))))

(defun py--match-paren-backward ()
  (setq py--match-paren-forward-p nil)
  (let* ((cui (current-indentation))
	 (cuc (current-column))
	 (cui (min cuc cui)))
    (if (eq 0 cui)
	(py-backward-top-level)
      (when (empty-line-p) (delete-region (line-beginning-position) (point)))
      (py-backward-statement)
      (unless (< (current-column) cuc)
      (while (and (not (bobp))
		  (< cui (current-column))
		  (py-backward-statement)))))))

(defun py--match-paren-blocks ()
  (cond
   ((and (looking-back "^[ \t]*" (line-beginning-position))(if (eq last-command 'py-match-paren)(not py--match-paren-forward-p)t)
	 ;; (looking-at py-extended-block-or-clause-re)
	 (looking-at "[[:alpha:]_]"))
    ;; from beginning of top-level, block, clause, statement
    (py--match-paren-forward))
   (t
    (py--match-paren-backward))))

(defun py-match-paren (&optional arg)
  "If at a beginning, jump to end and vice versa.

When called from within, go to the start.
Matches lists, but also block, statement, string and comment. "
  (interactive "*P")
  (if (eq 4 (prefix-numeric-value arg))
      (insert "%")
    (let ((pps (parse-partial-sexp (point-min) (point))))
      (cond
       ;; if inside string, go to beginning
       ((nth 3 pps)
	(goto-char (nth 8 pps)))
       ;; if inside comment, go to beginning
       ((nth 4 pps)
	(py-backward-comment))
       ;; at comment start, go to end of commented section
       ((and
	 ;; unless comment starts where jumped to some end
	 (not py--match-paren-forward-p)
	 (eq 11 (car-safe (syntax-after (point)))))
	(py-forward-comment))
       ;; at string start, go to end
       ((or (eq 15 (car-safe (syntax-after (point))))
	    (eq 7 (car (syntax-after (point)))))
	(goto-char (scan-sexps (point) 1))
	(forward-char -1))
       ;; open paren
       ((eq 4 (car (syntax-after (point))))
	(goto-char (scan-sexps (point) 1))
	(forward-char -1))
       ((eq 5 (car (syntax-after (point))))
	(goto-char (scan-sexps (1+ (point)) -1)))
       ((nth 1 pps)
	(goto-char (nth 1 pps)))
       (t
	;; Python specific blocks
	(py--match-paren-blocks))))))

(unless (boundp 'empty-line-p-chars)
  (defvar empty-line-p-chars "^[ \t\f\r]*$"))

(unless (functionp 'in-string-p)
  (defun in-string-p (&optional pos)
    (interactive)
    (let* ((orig (or pos (point)))
           (erg
            (save-excursion
              (save-restriction
                (widen)
                (beginning-of-defun)
                (numberp
                 (progn
                   (if (featurep 'xemacs)
                       (nth 3 (parse-partial-sexp (point) orig)
                            (nth 3 (parse-partial-sexp (point-min) (point)))))))))))
      (when (called-interactively-p 'any) (message "%s" erg))
      erg)))

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

(defalias 'durck 'py-printform-insert)
(defalias 'druck 'py-printform-insert)

(defun py-printform-insert (&optional arg strg)
  "Inserts a print statement out of current `(car kill-ring)' by default, inserts STRING if delivered.

With optional \\[universal-argument] print as string"
  (interactive "*P")
  (let* ((name (py--string-strip (or strg (car kill-ring))))
         ;; guess if doublequotes or parentheses are needed
         (numbered (not (eq 4 (prefix-numeric-value arg))))
         (form (if numbered
		   (concat "print(\"" name ": %s \" % (" name "))")
		 (concat "print(\"" name ": %s \" % \"" name "\")"))))
    (insert form)))

(defun py-line-to-printform-python2 ()
  "Transforms the item on current in a print statement. "
  (interactive "*")
  (let* ((name (thing-at-point 'word))
         (form (concat "print(\"" name ": %s \" % " name ")")))
    (delete-region (line-beginning-position) (line-end-position))
    (insert form))
  (forward-line 1)
  (back-to-indentation))

(defun py-boolswitch ()
  "Edit the assignment of a boolean variable, revert them.

I.e. switch it from \"True\" to \"False\" and vice versa"
  (interactive "*")
  (save-excursion
    (unless (py--end-of-statement-p)
      (py-forward-statement))
    (backward-word)
    (cond ((looking-at "True")
           (replace-match "False"))
          ((looking-at "False")
           (replace-match "True"))
          (t (message "%s" "Can't see \"True or False\" here")))))

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

;; python-components-imenu
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
  "Regexp for Python classes for use with the Imenu package."
  )

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
  "Regexp for Python methods/functions for use with the Imenu package."
  )

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
    py-imenu-method-regexp
    )
   py-imenu-method-no-arg-parens)
  "Generic Python expression which may be used directly with Imenu.
Used by setting the variable `imenu-generic-expression' to this value.
Also, see the function \\[py--imenu-create-index] for a better
alternative for finding the index.")

;; These next two variables are used when searching for the Python
;; class/definitions. Just saving some time in accessing the
;; generic-python-expression, really.
;; (set (make-local-variable 'imenu-generic-expression) 'py-imenu-generic-regexp)

(defvar py-imenu-generic-regexp nil)
(defvar py-imenu-generic-parens nil)

(defun py-switch-imenu-index-function ()
  "Switch between series 5. index machine `py--imenu-create-index' and `py--imenu-create-index-new', which also lists modules variables "
  (interactive)
  (if (eq py--imenu-create-index-function 'py--imenu-create-index-new)
      (set (make-local-variable 'py--imenu-create-index-function) 'py--imenu-create-index)
    (set (make-local-variable 'py--imenu-create-index-function) 'py--imenu-create-index-new))
  (when py-verbose-p (message "imenu-create-index-function: %s" (prin1-to-string py--imenu-create-index-function)))
  (funcall imenu-create-index-function))

(defun py--imenu-create-index ()
  "Python interface function for the Imenu package.
Finds all Python classes and functions/methods. Calls function
\\[py--imenu-create-index-engine].  See that function for the details
of how this works."
  (save-excursion
    (setq py-imenu-generic-regexp (car py-imenu-generic-expression)
	  py-imenu-generic-parens (if py-imenu-show-method-args-p
				      py-imenu-method-arg-parens
				    py-imenu-method-no-arg-parens))
    (goto-char (point-min))
    ;; Warning: When the buffer has no classes or functions, this will
    ;; return nil, which seems proper according to the Imenu API, but
    ;; causes an error in the XEmacs port of Imenu.  Sigh.
    (setq index-alist (cdr (py--imenu-create-index-engine nil)))))

(defun py--imenu-create-index-engine (&optional start-indent)
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
the function \\[py--imenu-create-index-function].

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
       ((py--in-literal))
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
        (setq sub-method-alist (py--imenu-create-index-engine cur-indent))
        (if sub-method-alist
            ;; we put the last element on the index-alist on the start
            ;; of the submethod alist so the user can still get to it.
            (let* ((save-elmt (pop index-alist))
                   (classname (and (string-match "^class " (car save-elmt))(replace-regexp-in-string "^class " "" (car save-elmt)))))
              (if (and classname (not (string-match "^class " (caar sub-method-alist))))
                  (setcar (car sub-method-alist) (concat classname "." (caar sub-method-alist))))
              (push (cons prev-name
                          (cons save-elmt sub-method-alist))
                    index-alist))))
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

(defun py--imenu-create-index-new (&optional beg end)
  (interactive)
  "`imenu-create-index-function' for Python. "
  (set (make-local-variable 'imenu-max-items) py-imenu-max-items)
  (let ((orig (point))
        (beg (or beg (point-min)))
        (end (or end (point-max)))
        index-alist vars thisend sublist classname pos name)
    (goto-char beg)
    (while (and (re-search-forward "^[ \t]*\\(def\\|class\\)[ \t]+\\(\\sw+\\)" end t 1)(not (nth 8 (parse-partial-sexp (point-min) (point)))))
      (if (save-match-data (string= "class" (match-string-no-properties 1)))
          (progn
            (setq pos (match-beginning 0)
                  name (match-string-no-properties 2)
                  classname (concat "class " name)
                  thisend (save-match-data (py--end-of-def-or-class-position))
                  sublist '())
            (while (and (re-search-forward "^[ \t]*\\(def\\|class\\)[ \t]+\\(\\sw+\\)" (or thisend end) t 1)(not (nth 8 (parse-partial-sexp (point-min) (point)))))
              (let* ((pos (match-beginning 0))
                     (name (match-string-no-properties 2)))
		(push (cons (concat " " name) pos) sublist)))
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
      (unless (nth 8 (parse-partial-sexp (point-min) (point)))
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

;; python-components-named-shells

;;;###autoload
(defun ipython (&optional argprompt buffer fast exception-buffer split switch)
  "Start an IPython interpreter.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython" buffer fast exception-buffer split switch))

;;;###autoload
(defun ipython2.7 (&optional argprompt buffer fast exception-buffer split switch)
  "Start an IPython2.7 interpreter.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython2.7" buffer fast exception-buffer split switch))

;;;###autoload
(defun ipython3 (&optional argprompt buffer fast exception-buffer split switch)
  "Start an IPython3 interpreter.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython3" buffer fast exception-buffer split switch))

;;;###autoload
(defun jython (&optional argprompt buffer fast exception-buffer split switch)
  "Start an Jython interpreter.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "jython" buffer fast exception-buffer split switch))

;;;###autoload
(defun python (&optional argprompt buffer fast exception-buffer split switch)
  "Start an Python interpreter.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python" buffer fast exception-buffer split switch))

;;;###autoload
(defun python2 (&optional argprompt buffer fast exception-buffer split switch)
  "Start an Python2 interpreter.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python2" buffer fast exception-buffer split switch))

;;;###autoload
(defun python3 (&optional argprompt buffer fast exception-buffer split switch)
  "Start an Python3 interpreter.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python3" buffer fast exception-buffer split switch))

;; dedicated
(defun ipython-dedicated (&optional argprompt buffer fast exception-buffer split switch)
  "Start an unique IPython interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "ipython" buffer fast exception-buffer split switch))

(defun ipython2.7-dedicated (&optional argprompt buffer fast exception-buffer split switch)
  "Start an unique IPython2.7 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "ipython2.7" buffer fast exception-buffer split switch))

(defun ipython3-dedicated (&optional argprompt buffer fast exception-buffer split switch)
  "Start an unique IPython3 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "ipython3" buffer fast exception-buffer split switch))

(defun jython-dedicated (&optional argprompt buffer fast exception-buffer split switch)
  "Start an unique Jython interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "jython" buffer fast exception-buffer split switch))

(defun python-dedicated (&optional argprompt buffer fast exception-buffer split switch)
  "Start an unique Python interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "python" buffer fast exception-buffer split switch))

(defun python2-dedicated (&optional argprompt buffer fast exception-buffer split switch)
  "Start an unique Python2 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "python2" buffer fast exception-buffer split switch))

(defun python3-dedicated (&optional argprompt buffer fast exception-buffer split switch)
  "Start an unique Python3 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "python3" buffer fast exception-buffer split switch))

;; switch
(defun ipython-switch (&optional argprompt buffer fast exception-buffer split)
  "Switch to IPython interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython" buffer fast exception-buffer split t))

(defun ipython2.7-switch (&optional argprompt buffer fast exception-buffer split)
  "Switch to IPython2.7 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython2.7" buffer fast exception-buffer split t))

(defun ipython3-switch (&optional argprompt buffer fast exception-buffer split)
  "Switch to IPython3 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython3" buffer fast exception-buffer split t))

(defun jython-switch (&optional argprompt buffer fast exception-buffer split)
  "Switch to Jython interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "jython" buffer fast exception-buffer split t))

(defun python-switch (&optional argprompt buffer fast exception-buffer split)
  "Switch to Python interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python" buffer fast exception-buffer split t))

(defun python2-switch (&optional argprompt buffer fast exception-buffer split)
  "Switch to Python2 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python2" buffer fast exception-buffer split t))

(defun python3-switch (&optional argprompt buffer fast exception-buffer split)
  "Switch to Python3 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python3" buffer fast exception-buffer split t))

;; no-switch
(defun ipython-no-switch (&optional argprompt buffer fast exception-buffer split)
  "Open an IPython interpreter in another window, but do not switch to it.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython" buffer fast exception-buffer split))

(defun ipython2.7-no-switch (&optional argprompt buffer fast exception-buffer split)
  "Open an IPython2.7 interpreter in another window, but do not switch to it.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython2.7" buffer fast exception-buffer split))

(defun ipython3-no-switch (&optional argprompt buffer fast exception-buffer split)
  "Open an IPython3 interpreter in another window, but do not switch to it.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "ipython3" buffer fast exception-buffer split))

(defun jython-no-switch (&optional argprompt buffer fast exception-buffer split)
  "Open an Jython interpreter in another window, but do not switch to it.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "jython" buffer fast exception-buffer split))

(defun python-no-switch (&optional argprompt buffer fast exception-buffer split)
  "Open an Python interpreter in another window, but do not switch to it.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python" buffer fast exception-buffer split))

(defun python2-no-switch (&optional argprompt buffer fast exception-buffer split)
  "Open an Python2 interpreter in another window, but do not switch to it.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python2" buffer fast exception-buffer split))

(defun python3-no-switch (&optional argprompt buffer fast exception-buffer split)
  "Open an Python3 interpreter in another window, but do not switch to it.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt nil "python3" buffer fast exception-buffer split))

;; dedicated switch
(defalias 'ipython-dedicated-switch 'ipython-switch-dedicated)
(defun ipython-switch-dedicated (&optional argprompt buffer fast exception-buffer split)
  "Switch to an unique IPython interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "ipython" buffer fast exception-buffer split t))

(defalias 'ipython2.7-dedicated-switch 'ipython2.7-switch-dedicated)
(defun ipython2.7-switch-dedicated (&optional argprompt buffer fast exception-buffer split)
  "Switch to an unique IPython2.7 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "ipython2.7" buffer fast exception-buffer split t))

(defalias 'ipython3-dedicated-switch 'ipython3-switch-dedicated)
(defun ipython3-switch-dedicated (&optional argprompt buffer fast exception-buffer split)
  "Switch to an unique IPython3 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "ipython3" buffer fast exception-buffer split t))

(defalias 'jython-dedicated-switch 'jython-switch-dedicated)
(defun jython-switch-dedicated (&optional argprompt buffer fast exception-buffer split)
  "Switch to an unique Jython interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "jython" buffer fast exception-buffer split t))

(defalias 'python-dedicated-switch 'python-switch-dedicated)
(defun python-switch-dedicated (&optional argprompt buffer fast exception-buffer split)
  "Switch to an unique Python interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "python" buffer fast exception-buffer split t))

(defalias 'python2-dedicated-switch 'python2-switch-dedicated)
(defun python2-switch-dedicated (&optional argprompt buffer fast exception-buffer split)
  "Switch to an unique Python2 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "python2" buffer fast exception-buffer split t))

(defalias 'python3-dedicated-switch 'python3-switch-dedicated)
(defun python3-switch-dedicated (&optional argprompt buffer fast exception-buffer split)
  "Switch to an unique Python3 interpreter in another window.

Optional ARG \\[universal-argument] prompts for path to the interpreter."
  (interactive "P")
  (py-shell argprompt t "python3" buffer fast exception-buffer split t))

;; python-components-electric
(defun py-electric-colon (arg)
  "Insert a colon and indent accordingly.

If a numeric argument ARG is provided, that many colons are inserted
non-electrically.

Electric behavior is inhibited inside a string or
comment or by universal prefix C-u.

Switched by `py-electric-colon-active-p', default is nil
See also `py-electric-colon-greedy-p' "
  (interactive "*P")
  (cond ((not py-electric-colon-active-p)
         (self-insert-command (prefix-numeric-value arg)))
        ((and py-electric-colon-bobl-only (save-excursion (py-backward-statement) (not (py--beginning-of-block-p))))
         (self-insert-command (prefix-numeric-value arg)))
        ((eq 4 (prefix-numeric-value arg))
         (self-insert-command 1))
        (t (insert ":")
           (unless (py-in-string-or-comment-p)
             (let ((orig (copy-marker (point)))
                   (indent (py-compute-indentation)))
               (unless (or (eq (current-indentation) indent)
                           (and py-electric-colon-greedy-p
                                (eq indent (save-excursion (py-backward-statement)(current-indentation))))
                           (and (py--top-level-form-p)(< (current-indentation) indent)))
                 (beginning-of-line)
                 (delete-horizontal-space)
                 (indent-to indent))
               (goto-char orig))
             (when py-electric-colon-newline-and-indent-p
               (py-newline-and-indent))))))

(defun py-electric-close (arg)
  "Close completion buffer when it's sure, it's no longer needed, i.e. when inserting a space.

Works around a bug in `choose-completion'. "

  (interactive "*P")
  (cond ((not py-electric-close-active-p)
         (self-insert-command (prefix-numeric-value arg)))
        ((eq 4 (prefix-numeric-value arg))
         (self-insert-command 1))
        (t (if (called-interactively-p 'any) (self-insert-command (prefix-numeric-value arg))
             ;; used from dont-indent-code-unnecessarily-lp-1048778-test
             (insert " ")))))

(defun py-electric-comment (arg)
  "Insert a comment. If starting a comment, indent accordingly.

If a numeric argument ARG is provided, that many \"#\" are inserted
non-electrically.
With \\[universal-argument] \"#\" electric behavior is inhibited inside a string or comment."
  (interactive "*P")
  (if (and py-indent-comments py-electric-comment-p)
      (if (ignore-errors (eq 4 (car-safe arg)))
          (insert "#")
        (when (and (eq last-command 'py-electric-comment) (looking-back " " (line-beginning-position)))
          (forward-char -1))
        (if (called-interactively-p 'any) (self-insert-command (prefix-numeric-value arg))
          (insert "#"))
        (let ((orig (copy-marker (point)))
              (indent (py-compute-indentation)))
          (unless
	      (eq (current-indentation) indent)
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

;; Electric deletion

(defun py-empty-out-list-backward ()
  "Deletes all elements from list before point. "
  (interactive "*")
  (and (member (char-before) (list ?\) ?\] ?\}))
       (let ((orig (point))
             (thischar (char-before))
             pps cn)
         (forward-char -1)
         (setq pps (parse-partial-sexp (point-min) (point)))
         (if (and (not (nth 8 pps)) (nth 1 pps))
             (progn
               (goto-char (nth 1 pps))
               (forward-char 1))
           (cond ((or (eq thischar 41)(eq thischar ?\)))
                  (setq cn "("))
                 ((or (eq thischar 125) (eq thischar ?\}))
                  (setq cn "{"))
                 ((or (eq thischar 93)(eq thischar ?\]))
                  (setq cn "[")))
           (skip-chars-backward (concat "^" cn)))
         (delete-region (point) orig)
         (insert-char thischar 1)
         (forward-char -1))))

(defun py-electric-backspace (&optional arg)
  "Delete preceding character or level of indentation.

When `delete-active-region' and (use-region-p), delete region.

Unless at indentation:
  With `py-electric-kill-backward-p' delete whitespace before point.
  With `py-electric-kill-backward-p' at end of a list, empty that list.

Returns column reached. "
  (interactive "p*")
  (or arg (setq arg 1))
  (let (erg)
    (cond ((and (use-region-p)
		;; Emacs23 doesn't know that var
		(boundp 'delete-active-region) delete-active-region)
	   (backward-delete-char-untabify arg))
	  ;; (delete-region (region-beginning) (region-end)))
	  ((looking-back "^[ \t]+" (line-beginning-position))
	   (let* ((remains (% (current-column) py-indent-offset)))
	     (if (< 0 remains)
		 (delete-char (- remains))
	       (indent-line-to (- (current-indentation) py-indent-offset)))))
	  ((and py-electric-kill-backward-p (member (char-before) (list ?\) ?\] ?\})))
	   (py-empty-out-list-backward))
	  ((and py-electric-kill-backward-p  (< 0 (setq erg (abs (skip-chars-backward " \t\r\n\f")))))
	   (delete-region (point) (+ erg (point))))
	  (t (delete-char (- 1))))
    (setq erg (current-column))
    (when (and (called-interactively-p 'any) py-verbose-p) (message "%s" erg))
    erg))

(defun py-electric-delete (&optional arg)
  "Delete following character or levels of whitespace.

When `delete-active-region' and (use-region-p), delete region "
  (interactive "*p")
  (let ((orig (point)))
    (cond ((and (use-region-p)
		;; Emacs23 doesn't know that var
		(boundp 'delete-active-region) delete-active-region)
	   (delete-region (region-beginning) (region-end)))
	  ((save-excursion (and (< (current-column)(current-indentation)) (<= py-indent-offset (skip-chars-forward " \t"))))
	   (goto-char orig)
	   (delete-char py-indent-offset))
	  ((< 0 (skip-chars-forward " \t"))
	   (delete-region orig (point)))
	  (t (delete-char (or arg 1))))))

(defun py-electric-yank (&optional arg)
  "Perform command `yank' followed by an `indent-according-to-mode' "
  (interactive "P")
  (cond (py-electric-yank-active-p
         (yank arg)
         ;; (py-indent-line)
         )
        (t (yank arg))))

;; required for pending-del and delsel modes
(put 'py-electric-colon 'delete-selection t) ;delsel
(put 'py-electric-colon 'pending-delete t) ;pending-del
(put 'py-electric-backspace 'delete-selection 'supersede) ;delsel
(put 'py-electric-backspace 'pending-delete 'supersede) ;pending-del
(put 'py-electric-delete 'delete-selection 'supersede) ;delsel
(put 'py-electric-delete 'pending-delete 'supersede) ;pending-del

;; python-components-virtualenv

(defvar virtualenv-workon-home nil)

(defvar virtualenv-name nil)

(defvar virtualenv-old-path nil)

(defvar virtualenv-old-exec-path nil)

(if (getenv "WORKON_HOME")
    (setq virtualenv-workon-home (getenv "WORKON_HOME"))
  (setq virtualenv-workon-home "~/.virtualenvs"))

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
  "Barfs the current activated virtualenv"
  (interactive)
  (message virtualenv-name))

(defun virtualenv-activate (dir)
  "Activate the virtualenv located in DIR"
  (interactive "DVirtualenv Directory: ")
  ;; Eventually deactivate previous virtualenv
  (when virtualenv-name
    (virtualenv-deactivate))
  (let ((cmd (concat "source " dir "/bin/activate\n")))
    (comint-send-string (get-process (get-buffer-process "*shell*")) cmd)
    ;; Storing old variables
    (setq virtualenv-old-path (getenv "PATH"))
    (setq virtualenv-old-exec-path exec-path)

    (setenv "VIRTUAL_ENV" dir)
    (virtualenv-add-to-path (concat (py--normalize-directory dir) "bin"))
    (push (concat (py--normalize-directory dir) "bin")  exec-path)

    (setq virtualenv-name dir)))

(defun virtualenv-deactivate ()
  "Deactivate the current virtual enviroment"
  (interactive)
  ;; Restoring old variables
  (setenv "PATH" virtualenv-old-path)
  (setq exec-path virtualenv-old-exec-path)
  (message (concat "Virtualenv '" virtualenv-name "' deactivated."))
  (setq virtualenv-name nil))

(defun virtualenv-p (dir)
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
            (virtualenv-filter 'virtualenv-p
                               (virtualenv-filter 'file-directory-p filelist)))))

(defun virtualenv-workon (name)
  "Issue a virtualenvwrapper-like virtualenv-workon command"
  (interactive (list (completing-read "Virtualenv: " (virtualenv-workon-complete))))
  (if (getenv "WORKON_HOME")
      (virtualenv-activate (concat (py--normalize-directory (getenv "WORKON_HOME")) name))
    (virtualenv-activate (concat (py--normalize-directory virtualenv-workon-home) name))))

;; python-components-booleans-beginning-forms

(defun py--beginning-of-comment-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘comment’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-comment-re)
         (point))))

(defun py--beginning-of-line-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘line’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-line-re)
         (point))))

(defun py--beginning-of-paragraph-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘paragraph’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-paragraph-re)
         (point))))

(defun py--beginning-of-expression-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘expression’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-expression-re)
         (point))))

(defun py--beginning-of-partial-expression-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘partial-expression’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-partial-expression-re)
         (point))))

(defun py--beginning-of-section-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘section’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-section-re)
         (point))))

(defun py--beginning-of-top-level-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘top-level’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-top-level-re)
         (point))))

(defun py--beginning-of-block-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-block-or-clause-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘block-or-clause’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-block-or-clause-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-class-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘class’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-class-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-clause-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘clause’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-clause-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-def-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘def’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-def-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-def-or-class-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘def-or-class’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-def-or-class-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-elif-block-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘elif-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-elif-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-else-block-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘else-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-else-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-except-block-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘except-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-except-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-for-block-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘for-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-for-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-if-block-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘if-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-if-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-indent-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘indent’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-indent-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-minor-block-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘minor-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-minor-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-statement-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘statement’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-statement-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-try-block-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘try-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-try-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (eq (current-column)(current-indentation))
         (point))))

(defun py--beginning-of-block-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-block-or-clause-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘block-or-clause’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-block-or-clause-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-class-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘class’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-class-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-clause-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘clause’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-clause-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-def-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘def’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-def-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-def-or-class-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘def-or-class’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-def-or-class-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-elif-block-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘elif-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-elif-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-else-block-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘else-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-else-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-except-block-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘except-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-except-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-for-block-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘for-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-for-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-if-block-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘if-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-if-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-indent-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘indent’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-indent-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-minor-block-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘minor-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-minor-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-statement-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘statement’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-statement-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

(defun py--beginning-of-try-block-bol-p (&optional pps)
  "Return position, if cursor is at the beginning of a ‘try-block’, nil otherwise."
  (let ((pps (or pps (parse-partial-sexp (point-min) (point)))))
    (and (bolp)
         (not (or (nth 8 pps)(nth 1 pps)))
         (looking-at py-try-block-re)
         (looking-back "[^ \t]*" (line-beginning-position))
         (point))))

;; python-components-booleans-end-forms


(defun py--end-of-comment-p ()
  "Return position, if cursor is at the end of a comment, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-comment)
      (py-forward-comment)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-line-p ()
  "Return position, if cursor is at the end of a line, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-line)
      (py-forward-line)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-paragraph-p ()
  "Return position, if cursor is at the end of a paragraph, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-paragraph)
      (py-forward-paragraph)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-expression-p ()
  "Return position, if cursor is at the end of a expression, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-expression)
      (py-forward-expression)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-partial-expression-p ()
  "Return position, if cursor is at the end of a partial-expression, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-partial-expression)
      (py-forward-partial-expression)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-section-p ()
  "Return position, if cursor is at the end of a section, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-section)
      (py-forward-section)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-top-level-p ()
  "Return position, if cursor is at the end of a top-level, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-top-level)
      (py-forward-top-level)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-block-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-block-bol)
      (py-forward-block-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-block-or-clause-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a block-or-clause, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-block-or-clause-bol)
      (py-forward-block-or-clause-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-class-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a class, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-class-bol)
      (py-forward-class-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-clause-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a clause, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-clause-bol)
      (py-forward-clause-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-def-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a def, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-def-bol)
      (py-forward-def-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-def-or-class-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a def-or-class, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-def-or-class-bol)
      (py-forward-def-or-class-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-elif-block-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a elif-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-elif-block-bol)
      (py-forward-elif-block-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-else-block-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a else-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-else-block-bol)
      (py-forward-else-block-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-except-block-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a except-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-except-block-bol)
      (py-forward-except-block-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-for-block-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a for-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-for-block-bol)
      (py-forward-for-block-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-if-block-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a if-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-if-block-bol)
      (py-forward-if-block-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-indent-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a indent, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-indent-bol)
      (py-forward-indent-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-minor-block-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a minor-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-minor-block-bol)
      (py-forward-minor-block-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-statement-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a statement, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-statement-bol)
      (py-forward-statement-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-try-block-bol-p ()
  "Return position, if cursor is at ‘beginning-of-line’ at the end of a try-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-try-block-bol)
      (py-forward-try-block-bol)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-block-p ()
  "Return position, if cursor is at the end of a block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-block)
      (py-forward-block)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-block-or-clause-p ()
  "Return position, if cursor is at the end of a block-or-clause, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-block-or-clause)
      (py-forward-block-or-clause)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-class-p ()
  "Return position, if cursor is at the end of a class, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-class)
      (py-forward-class)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-clause-p ()
  "Return position, if cursor is at the end of a clause, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-clause)
      (py-forward-clause)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-def-p ()
  "Return position, if cursor is at the end of a def, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-def)
      (py-forward-def)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-def-or-class-p ()
  "Return position, if cursor is at the end of a def-or-class, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-def-or-class)
      (py-forward-def-or-class)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-elif-block-p ()
  "Return position, if cursor is at the end of a elif-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-elif-block)
      (py-forward-elif-block)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-else-block-p ()
  "Return position, if cursor is at the end of a else-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-else-block)
      (py-forward-else-block)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-except-block-p ()
  "Return position, if cursor is at the end of a except-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-except-block)
      (py-forward-except-block)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-for-block-p ()
  "Return position, if cursor is at the end of a for-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-for-block)
      (py-forward-for-block)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-if-block-p ()
  "Return position, if cursor is at the end of a if-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-if-block)
      (py-forward-if-block)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-indent-p ()
  "Return position, if cursor is at the end of a indent, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-indent)
      (py-forward-indent)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-minor-block-p ()
  "Return position, if cursor is at the end of a minor-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-minor-block)
      (py-forward-minor-block)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-statement-p ()
  "Return position, if cursor is at the end of a statement, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-statement)
      (py-forward-statement)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

(defun py--end-of-try-block-p ()
  "Return position, if cursor is at the end of a try-block, nil otherwise."
  (let ((orig (point))
	erg)
    (save-excursion
      (py-backward-try-block)
      (py-forward-try-block)
      (when (eq orig (point))
	(setq erg orig))
      erg)))

;; python-components-beginning-position-forms


(defun py--beginning-of-block-position ()
  "Return beginning of block position."
  (save-excursion
    (let ((erg (or (py--beginning-of-block-p)
                   (py-backward-block))))
      erg)))

(defun py--beginning-of-block-or-clause-position ()
  "Return beginning of block-or-clause position."
  (save-excursion
    (let ((erg (or (py--beginning-of-block-or-clause-p)
                   (py-backward-block-or-clause))))
      erg)))

(defun py--beginning-of-class-position ()
  "Return beginning of class position."
  (save-excursion
    (let ((erg (or (py--beginning-of-class-p)
                   (py-backward-class))))
      erg)))

(defun py--beginning-of-clause-position ()
  "Return beginning of clause position."
  (save-excursion
    (let ((erg (or (py--beginning-of-clause-p)
                   (py-backward-clause))))
      erg)))

(defun py--beginning-of-comment-position ()
  "Return beginning of comment position."
  (save-excursion
    (let ((erg (or (py--beginning-of-comment-p)
                   (py-backward-comment))))
      erg)))

(defun py--beginning-of-def-position ()
  "Return beginning of def position."
  (save-excursion
    (let ((erg (or (py--beginning-of-def-p)
                   (py-backward-def))))
      erg)))

(defun py--beginning-of-def-or-class-position ()
  "Return beginning of def-or-class position."
  (save-excursion
    (let ((erg (or (py--beginning-of-def-or-class-p)
                   (py-backward-def-or-class))))
      erg)))

(defun py--beginning-of-expression-position ()
  "Return beginning of expression position."
  (save-excursion
    (let ((erg (or (py--beginning-of-expression-p)
                   (py-backward-expression))))
      erg)))

(defun py--beginning-of-except-block-position ()
  "Return beginning of except-block position."
  (save-excursion
    (let ((erg (or (py--beginning-of-except-block-p)
                   (py-backward-except-block))))
      erg)))

(defun py--beginning-of-if-block-position ()
  "Return beginning of if-block position."
  (save-excursion
    (let ((erg (or (py--beginning-of-if-block-p)
                   (py-backward-if-block))))
      erg)))

(defun py--beginning-of-indent-position ()
  "Return beginning of indent position."
  (save-excursion
    (let ((erg (or (py--beginning-of-indent-p)
                   (py-backward-indent))))
      erg)))

(defun py--beginning-of-line-position ()
  "Return beginning of line position."
  (save-excursion
    (let ((erg (or (py--beginning-of-line-p)
                   (py-backward-line))))
      erg)))

(defun py--beginning-of-minor-block-position ()
  "Return beginning of minor-block position."
  (save-excursion
    (let ((erg (or (py--beginning-of-minor-block-p)
                   (py-backward-minor-block))))
      erg)))

(defun py--beginning-of-partial-expression-position ()
  "Return beginning of partial-expression position."
  (save-excursion
    (let ((erg (or (py--beginning-of-partial-expression-p)
                   (py-backward-partial-expression))))
      erg)))

(defun py--beginning-of-paragraph-position ()
  "Return beginning of paragraph position."
  (save-excursion
    (let ((erg (or (py--beginning-of-paragraph-p)
                   (py-backward-paragraph))))
      erg)))

(defun py--beginning-of-section-position ()
  "Return beginning of section position."
  (save-excursion
    (let ((erg (or (py--beginning-of-section-p)
                   (py-backward-section))))
      erg)))

(defun py--beginning-of-statement-position ()
  "Return beginning of statement position."
  (save-excursion
    (let ((erg (or (py--beginning-of-statement-p)
                   (py-backward-statement))))
      erg)))

(defun py--beginning-of-top-level-position ()
  "Return beginning of top-level position."
  (save-excursion
    (let ((erg (or (py--beginning-of-top-level-p)
                   (py-backward-top-level))))
      erg)))

(defun py--beginning-of-try-block-position ()
  "Return beginning of try-block position."
  (save-excursion
    (let ((erg (or (py--beginning-of-try-block-p)
                   (py-backward-try-block))))
      erg)))

(defun py--beginning-of-block-position-bol ()
  "Return beginning of block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-block-bol-p)
                   (py-backward-block-bol))))
      erg)))

(defun py--beginning-of-block-or-clause-position-bol ()
  "Return beginning of block-or-clause position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-block-or-clause-bol-p)
                   (py-backward-block-or-clause-bol))))
      erg)))

(defun py--beginning-of-class-position-bol ()
  "Return beginning of class position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-class-bol-p)
                   (py-backward-class-bol))))
      erg)))

(defun py--beginning-of-clause-position-bol ()
  "Return beginning of clause position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-clause-bol-p)
                   (py-backward-clause-bol))))
      erg)))

(defun py--beginning-of-def-position-bol ()
  "Return beginning of def position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-def-bol-p)
                   (py-backward-def-bol))))
      erg)))

(defun py--beginning-of-def-or-class-position-bol ()
  "Return beginning of def-or-class position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-def-or-class-bol-p)
                   (py-backward-def-or-class-bol))))
      erg)))

(defun py--beginning-of-elif-block-position-bol ()
  "Return beginning of elif-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-elif-block-bol-p)
                   (py-backward-elif-block-bol))))
      erg)))

(defun py--beginning-of-else-block-position-bol ()
  "Return beginning of else-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-else-block-bol-p)
                   (py-backward-else-block-bol))))
      erg)))

(defun py--beginning-of-except-block-position-bol ()
  "Return beginning of except-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-except-block-bol-p)
                   (py-backward-except-block-bol))))
      erg)))

(defun py--beginning-of-for-block-position-bol ()
  "Return beginning of for-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-for-block-bol-p)
                   (py-backward-for-block-bol))))
      erg)))

(defun py--beginning-of-if-block-position-bol ()
  "Return beginning of if-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-if-block-bol-p)
                   (py-backward-if-block-bol))))
      erg)))

(defun py--beginning-of-indent-position-bol ()
  "Return beginning of indent position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-indent-bol-p)
                   (py-backward-indent-bol))))
      erg)))

(defun py--beginning-of-minor-block-position-bol ()
  "Return beginning of minor-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-minor-block-bol-p)
                   (py-backward-minor-block-bol))))
      erg)))

(defun py--beginning-of-statement-position-bol ()
  "Return beginning of statement position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-statement-bol-p)
                   (py-backward-statement-bol))))
      erg)))

(defun py--beginning-of-try-block-position-bol ()
  "Return beginning of try-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (or (py--beginning-of-try-block-bol-p)
                   (py-backward-try-block-bol))))
      erg)))

;; python-components-end-position-forms


(defun py--end-of-block-position ()
  "Return end of block position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-block))))
      erg)))

(defun py--end-of-block-or-clause-position ()
  "Return end of block-or-clause position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-block-or-clause))))
      erg)))

(defun py--end-of-class-position ()
  "Return end of class position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-class))))
      erg)))

(defun py--end-of-clause-position ()
  "Return end of clause position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-clause))))
      erg)))

(defun py--end-of-comment-position ()
  "Return end of comment position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-comment))))
      erg)))

(defun py--end-of-def-position ()
  "Return end of def position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-def))))
      erg)))

(defun py--end-of-def-or-class-position ()
  "Return end of def-or-class position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-def-or-class))))
      erg)))

(defun py--end-of-expression-position ()
  "Return end of expression position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-expression))))
      erg)))

(defun py--end-of-except-block-position ()
  "Return end of except-block position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-except-block))))
      erg)))

(defun py--end-of-if-block-position ()
  "Return end of if-block position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-if-block))))
      erg)))

(defun py--end-of-indent-position ()
  "Return end of indent position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-indent))))
      erg)))

(defun py--end-of-line-position ()
  "Return end of line position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-line))))
      erg)))

(defun py--end-of-minor-block-position ()
  "Return end of minor-block position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-minor-block))))
      erg)))

(defun py--end-of-partial-expression-position ()
  "Return end of partial-expression position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-partial-expression))))
      erg)))

(defun py--end-of-paragraph-position ()
  "Return end of paragraph position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-paragraph))))
      erg)))

(defun py--end-of-section-position ()
  "Return end of section position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-section))))
      erg)))

(defun py--end-of-statement-position ()
  "Return end of statement position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-statement))))
      erg)))

(defun py--end-of-top-level-position ()
  "Return end of top-level position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-top-level))))
      erg)))

(defun py--end-of-try-block-position ()
  "Return end of try-block position."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-try-block))))
      erg)))

(defun py--end-of-block-position-bol ()
  "Return end of block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-block-bol))))
      erg)))

(defun py--end-of-block-or-clause-position-bol ()
  "Return end of block-or-clause position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-block-or-clause-bol))))
      erg)))

(defun py--end-of-class-position-bol ()
  "Return end of class position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-class-bol))))
      erg)))

(defun py--end-of-clause-position-bol ()
  "Return end of clause position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-clause-bol))))
      erg)))

(defun py--end-of-def-position-bol ()
  "Return end of def position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-def-bol))))
      erg)))

(defun py--end-of-def-or-class-position-bol ()
  "Return end of def-or-class position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-def-or-class-bol))))
      erg)))

(defun py--end-of-elif-block-position-bol ()
  "Return end of elif-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-elif-block-bol))))
      erg)))

(defun py--end-of-else-block-position-bol ()
  "Return end of else-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-else-block-bol))))
      erg)))

(defun py--end-of-except-block-position-bol ()
  "Return end of except-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-except-block-bol))))
      erg)))

(defun py--end-of-for-block-position-bol ()
  "Return end of for-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-for-block-bol))))
      erg)))

(defun py--end-of-if-block-position-bol ()
  "Return end of if-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-if-block-bol))))
      erg)))

(defun py--end-of-indent-position-bol ()
  "Return end of indent position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-indent-bol))))
      erg)))

(defun py--end-of-minor-block-position-bol ()
  "Return end of minor-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-minor-block-bol))))
      erg)))

(defun py--end-of-statement-position-bol ()
  "Return end of statement position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-statement-bol))))
      erg)))

(defun py--end-of-try-block-position-bol ()
  "Return end of try-block position at ‘beginning-of-line’."
  (save-excursion
    (let ((erg (progn
                 (when (looking-at "[ \\t\\r\\n\\f]*$")
                   (skip-chars-backward " \t\r\n\f")
                   (forward-char -1))
                 (py-forward-try-block-bol))))
      erg)))

;; python-components-up-down


(defun py-up-statement ()
  "go to the beginning of next statement upwards in buffer.

Return position if statement found, nil otherwise."
  (interactive)
  (let (erg)
    (if (py--beginning-of-statement-p)
	(setq erg (py-backward-statement))
      (setq erg (and (py-backward-statement) (py-backward-statement))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))


(defun py-up-base (regexp &optional indent orig decorator bol repeat)
  "REGEXP is a quoted symbol

Go to the beginning of next form upwards in buffer according to INDENT.

Optional ORIG DECORATOR BOL REPEAT
Return position if form found, nil otherwise."
  (unless (bobp)
    (let* ((orig (or orig (point)))
	   (repeat (or (and repeat (1+ repeat)) 0))
	   erg name command)
      (if (< py-max-specpdl-size repeat)
	  (error "‘py-up-base’ reached loops max")
	(if indent
	    (progn
	      (while (and (re-search-backward (symbol-value regexp) nil 'move 1)
			  (or (nth 8 (parse-partial-sexp (point-min) (point)))
			      (<= indent (current-indentation))))))
	  (unless (py--beginning-of-statement-p)
	    (py-backward-statement))
	  (if (looking-at (symbol-value regexp))
	      (py-up-base regexp (current-indentation) orig decorator bol repeat)
	    (setq name (symbol-name regexp))
	    (setq command (intern-soft (concat "py-backward-" (substring name (string-match "minor\\|block\\|def\\|class" name) (string-match "-re" name)))))
	    (funcall command)
	    (py-up-base regexp (current-indentation) orig decorator bol repeat)))
	(when bol (beginning-of-line))
	(and (looking-at (symbol-value regexp)) (< (point) orig) (setq erg (point)))
	(when py-verbose-p (message "%s" erg))
	erg))))

(defun py-down-statement ()
  "Go to the beginning of next statement downwards in buffer.

Return position if statement found, nil otherwise."
  (interactive)
  (let* ((orig (point))
	 erg)
    (cond ((py--end-of-statement-p)
	   (setq erg
		 (and
		  (py-forward-statement)
		  (py-backward-statement)
		  (< orig (point))
		  (point))))
	  ((< orig (and (py-forward-statement) (py-backward-statement)))
	   (setq erg (point)))
	  (t (setq erg (ignore-errors (< orig (and (py-forward-statement) (py-forward-statement)(py-backward-statement)))))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-down-base (regexp &optional orig indent decorator bol)
  "Go to the beginning of next form below in buffer.

Return position if form found, nil otherwise.
Expects a quoted symbol 'REGEXP
Optional ORIG INDENT DECORATOR BOL"
  (unless (eobp)
    (let* ((name (substring (symbol-name regexp) 3 -3))
	   (p-command (car (read-from-string (concat "py--beginning-of-" name "-p"))))
	   (backward-command (car (read-from-string (concat "py-backward-" name))))
	   (up-command (car (read-from-string (concat "py-up-" name))))
	   ;; (down-command (car (read-from-string (concat "py-down-" name))))
           (forward-command (car (read-from-string (concat "py-forward-" name))))
           erg done start)
      (if (funcall p-command)
	  (setq indent (current-indentation))
	(save-excursion
	  (cond
	   ((and indent decorator bol)
	    (when (funcall backward-command indent decorator bol)
	      (setq indent (current-indentation))
	      (setq start (point))))
	   ((and indent decorator)
	    (when (funcall backward-command indent decorator)
	      (setq indent (current-indentation))
	      (setq start (point))))
	   (t (when
		  (funcall backward-command indent)
		(setq indent (current-indentation))
		(setq start (point))))))
	(unless (and indent start)
	  (while (and (py-down-statement)
		      (not (looking-at (symbol-value regexp))))))

	(when
	    (looking-at (symbol-value regexp))
	  (setq done t)
	  (setq erg (point)) 
	  ;; (setq indent (current-indentation))
	  ;; (setq start (point))
	  ))
      ;; (setq done (funcall forward-command indent decorator bol))
      (while (and (not done)
		  (py-down-statement)
		  (< indent (current-indentation))))
      (when (looking-at (symbol-value regexp))
	(setq done (point)))
      (when done
	(when bol (beginning-of-line))
	(setq erg (point)))
      (unless done
	(goto-char orig)
	(or
	 (if
	     (and
	      (funcall up-command)
	      ;; up should not result to backward
	      (not (eq (point) start))
	      (funcall forward-command decorator bol)
	      (< orig (point))
	      (setq erg (point)))
	     (when bol (setq erg (py--beginning-of-line-form erg)))
	   (goto-char (point-max)))))
      (when py-verbose-p (message "%s" erg))
      erg)))

(defalias 'py-block-up 'py-up-block)
(defun py-up-block (&optional indent decorator bol)
  "Go to the beginning of next block upwards in buffer according to INDENT.
Optional DECORATOR BOL
Return position if block found, nil otherwise."
  (interactive)
  (py-up-base 'py-extended-block-or-clause-re indent (point) decorator bol))

(defalias 'py-class-up 'py-up-class)
(defun py-up-class (&optional indent decorator bol)
  "Go to the beginning of next class upwards in buffer according to INDENT.
Optional DECORATOR BOL
Return position if class found, nil otherwise."
  (interactive)
  (py-up-base 'py-class-re indent (point) decorator bol))

(defalias 'py-def-up 'py-up-def)
(defun py-up-def (&optional indent decorator bol)
  "Go to the beginning of next def upwards in buffer according to INDENT.
Optional DECORATOR BOL
Return position if def found, nil otherwise."
  (interactive)
  (py-up-base 'py-def-re indent (point) decorator bol))

(defalias 'py-def-or-class-up 'py-up-def-or-class)
(defun py-up-def-or-class (&optional indent decorator bol)
  "Go to the beginning of next def-or-class upwards in buffer according to INDENT.
Optional DECORATOR BOL
Return position if def-or-class found, nil otherwise."
  (interactive)
  (py-up-base 'py-def-or-class-re indent (point) decorator bol))

(defalias 'py-minor-block-up 'py-up-minor-block)
(defun py-up-minor-block (&optional indent decorator bol)
  "Go to the beginning of next minor-block upwards in buffer according to INDENT.
Optional DECORATOR BOL
Return position if minor-block found, nil otherwise."
  (interactive)
  (py-up-base 'py-extended-block-or-clause-re indent (point) decorator bol))

(defalias 'py-block-down 'py-down-block)
(defun py-down-block (&optional orig indent decorator bol)
  "Go to the beginning of next block below in buffer according to INDENT.

Optional INDENT DECORATOR BOL
Return position if block found, nil otherwise."
  (interactive)
  (py-down-base 'py-block-re (or orig (point)) indent decorator bol))

(defalias 'py-class-down 'py-down-class)
(defun py-down-class (&optional orig indent decorator bol)
  "Go to the beginning of next class below in buffer according to INDENT.

Optional INDENT DECORATOR BOL
Return position if class found, nil otherwise."
  (interactive)
  (py-down-base 'py-class-re (or orig (point)) indent decorator bol))

(defalias 'py-def-down 'py-down-def)
(defun py-down-def (&optional orig indent decorator bol)
  "Go to the beginning of next def below in buffer according to INDENT.

Optional INDENT DECORATOR BOL
Return position if def found, nil otherwise."
  (interactive)
  (py-down-base 'py-def-re (or orig (point)) indent decorator bol))

(defalias 'py-def-or-class-down 'py-down-def-or-class)
(defun py-down-def-or-class (&optional orig indent decorator bol)
  "Go to the beginning of next def-or-class below in buffer according to INDENT.

Optional INDENT DECORATOR BOL
Return position if def-or-class found, nil otherwise."
  (interactive)
  (py-down-base 'py-def-or-class-re (or orig (point)) indent decorator bol))

(defalias 'py-minor-block-down 'py-down-minor-block)
(defun py-down-minor-block (&optional orig indent decorator bol)
  "Go to the beginning of next minor-block below in buffer according to INDENT.

Optional INDENT DECORATOR BOL
Return position if minor-block found, nil otherwise."
  (interactive)
  (py-down-base 'py-minor-block-re (or orig (point)) indent decorator bol))

(defun py-up-block-bol (&optional indent decorator)
  "Go to the beginning of next block upwards in buffer according to INDENT.

Go to beginning of line.
Optional DECORATOR.
Return position if block found, nil otherwise."
  (interactive)
  (py-up-base 'py-block-re indent (point) decorator t))

(defun py-up-class-bol (&optional indent decorator)
  "Go to the beginning of next class upwards in buffer according to INDENT.

Go to beginning of line.
Optional DECORATOR.
Return position if class found, nil otherwise."
  (interactive)
  (py-up-base 'py-class-re indent (point) decorator t))

(defun py-up-def-bol (&optional indent decorator)
  "Go to the beginning of next def upwards in buffer according to INDENT.

Go to beginning of line.
Optional DECORATOR.
Return position if def found, nil otherwise."
  (interactive)
  (py-up-base 'py-def-re indent (point) decorator t))

(defun py-up-def-or-class-bol (&optional indent decorator)
  "Go to the beginning of next def-or-class upwards in buffer according to INDENT.

Go to beginning of line.
Optional DECORATOR.
Return position if def-or-class found, nil otherwise."
  (interactive)
  (py-up-base 'py-def-or-class-re indent (point) decorator t))

(defun py-up-minor-block-bol (&optional indent decorator)
  "Go to the beginning of next minor-block upwards in buffer according to INDENT.

Go to beginning of line.
Optional DECORATOR.
Return position if minor-block found, nil otherwise."
  (interactive)
  (py-up-base 'py-minor-block-re indent (point) decorator t))

(defun py-down-block-bol (&optional orig indent decorator bol)
  "Go to the beginning of next block below in buffer according to INDENT.

Optional INDENT DECORATOR BOL.
Go to beginning of line
Return position if block found, nil otherwise "
  (interactive)
  (py-down-base 'py-block-re (or orig (point)) indent decorator (or bol t)))

(defun py-down-class-bol (&optional orig indent decorator bol)
  "Go to the beginning of next class below in buffer according to INDENT.

Optional INDENT DECORATOR BOL.
Go to beginning of line
Return position if class found, nil otherwise "
  (interactive)
  (py-down-base 'py-class-re (or orig (point)) indent decorator (or bol t)))

(defun py-down-def-bol (&optional orig indent decorator bol)
  "Go to the beginning of next def below in buffer according to INDENT.

Optional INDENT DECORATOR BOL.
Go to beginning of line
Return position if def found, nil otherwise "
  (interactive)
  (py-down-base 'py-def-re (or orig (point)) indent decorator (or bol t)))

(defun py-down-def-or-class-bol (&optional orig indent decorator bol)
  "Go to the beginning of next def-or-class below in buffer according to INDENT.

Optional INDENT DECORATOR BOL.
Go to beginning of line
Return position if def-or-class found, nil otherwise "
  (interactive)
  (py-down-base 'py-def-or-class-re (or orig (point)) indent decorator (or bol t)))

(defun py-down-minor-block-bol (&optional orig indent decorator bol)
  "Go to the beginning of next minor-block below in buffer according to INDENT.

Optional INDENT DECORATOR BOL.
Go to beginning of line
Return position if minor-block found, nil otherwise "
  (interactive)
  (py-down-base 'py-minor-block-re (or orig (point)) indent decorator (or bol t)))

;; python-components-up-down.el ends here
;; python-components-exec-forms

;; Execute forms at point

(defun py-execute-try-block ()
  "Send try-block at point to Python default interpreter."
  (interactive)
  (let ((beg (prog1
                 (or (py--beginning-of-try-block-p)
                     (save-excursion
                       (py-backward-try-block)))))
        (end (save-excursion
               (py-forward-try-block))))
    (py-execute-region beg end)))

(defun py-execute-if-block ()
  "Send if-block at point to Python default interpreter."
  (interactive)
  (let ((beg (prog1
                 (or (py--beginning-of-if-block-p)
                     (save-excursion
                       (py-backward-if-block)))))
        (end (save-excursion
               (py-forward-if-block))))
    (py-execute-region beg end)))

(defun py-execute-for-block ()
  "Send for-block at point to Python default interpreter."
  (interactive)
  (let ((beg (prog1
                 (or (py--beginning-of-for-block-p)
                     (save-excursion
                       (py-backward-for-block)))))
        (end (save-excursion
               (py-forward-for-block))))
    (py-execute-region beg end)))

;; python-components-extended-executes


(defun py-execute-block (&optional shell dedicated fast split switch proc wholebuf)
  "Send block at point to  interpreter."
  (interactive)
  (py--execute-prepare 'block shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-switch (&optional shell dedicated fast split proc wholebuf)
  "Send block at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send block at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-dedicated (&optional shell fast split switch proc wholebuf)
  "Send block at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'block shell t switch nil fast proc wholebuf split))

(defun py-execute-block-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send block at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block shell t 'switch nil fast proc wholebuf split))

(defun py-execute-block-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send block at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'block 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send block at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send block at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'block 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-block-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-block-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send block at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'block 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send block at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send block at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'block 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-block-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-block-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send block at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'block 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send block at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send block at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'block 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-block-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-block-jython (&optional dedicated fast split switch proc wholebuf)
  "Send block at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'block 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send block at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send block at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'block 'jython t switch nil fast proc wholebuf split))

(defun py-execute-block-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-block-python (&optional dedicated fast split switch proc wholebuf)
  "Send block at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-python-switch (&optional dedicated fast split proc wholebuf)
  "Send block at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-python-dedicated (&optional fast split switch proc wholebuf)
  "Send block at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block 'python t switch nil fast proc wholebuf split))

(defun py-execute-block-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-block-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send block at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'block 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send block at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send block at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'block 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-block-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-block-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send block at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'block 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send block at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send block at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'block 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-block-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause (&optional shell dedicated fast split switch proc wholebuf)
  "Send block-or-clause at point to  interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-switch (&optional shell dedicated fast split proc wholebuf)
  "Send block-or-clause at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block-or-clause shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send block-or-clause at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block-or-clause shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-dedicated (&optional shell fast split switch proc wholebuf)
  "Send block-or-clause at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause shell t switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send block-or-clause at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block-or-clause shell t 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send block-or-clause at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send block-or-clause at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block-or-clause at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send block-or-clause at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block-or-clause at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send block-or-clause at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send block-or-clause at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block-or-clause at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send block-or-clause at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block-or-clause at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send block-or-clause at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send block-or-clause at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block-or-clause at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send block-or-clause at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block-or-clause at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block-or-clause 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-jython (&optional dedicated fast split switch proc wholebuf)
  "Send block-or-clause at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send block-or-clause at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block-or-clause 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block-or-clause at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block-or-clause 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send block-or-clause at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'jython t switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block-or-clause at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block-or-clause 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python (&optional dedicated fast split switch proc wholebuf)
  "Send block-or-clause at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block-or-clause 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python-switch (&optional dedicated fast split proc wholebuf)
  "Send block-or-clause at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block-or-clause 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block-or-clause at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block-or-clause 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python-dedicated (&optional fast split switch proc wholebuf)
  "Send block-or-clause at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block-or-clause 'python t switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block-or-clause at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'block-or-clause 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send block-or-clause at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send block-or-clause at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block-or-clause 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block-or-clause at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block-or-clause 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send block-or-clause at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block-or-clause at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block-or-clause 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send block-or-clause at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send block-or-clause at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'block-or-clause 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send block-or-clause at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'block-or-clause 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send block-or-clause at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'block-or-clause 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-block-or-clause-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send block-or-clause at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'block-or-clause 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-buffer (&optional shell dedicated fast split switch proc wholebuf)
  "Send buffer at point to  interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer shell dedicated switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-switch (&optional shell dedicated fast split proc wholebuf)
  "Send buffer at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer shell dedicated 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send buffer at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer shell dedicated 'no-switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-dedicated (&optional shell fast split switch proc wholebuf)
  "Send buffer at point to  unique interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer shell t switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send buffer at point to  unique interpreter and switch to result."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer shell t 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send buffer at point to IPython interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython dedicated switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send buffer at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython dedicated 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send buffer at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython dedicated 'no-switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send buffer at point to IPython unique interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython t switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send buffer at point to IPython unique interpreter and switch to result."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython t 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send buffer at point to IPython interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython2.7 dedicated switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send buffer at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython2.7 dedicated 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send buffer at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython2.7 dedicated 'no-switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send buffer at point to IPython unique interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython2.7 t switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send buffer at point to IPython unique interpreter and switch to result."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython2.7 t 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send buffer at point to IPython interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython3 dedicated switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send buffer at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython3 dedicated 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send buffer at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython3 dedicated 'no-switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send buffer at point to IPython unique interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython3 t switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send buffer at point to IPython unique interpreter and switch to result."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'ipython3 t 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-jython (&optional dedicated fast split switch proc wholebuf)
  "Send buffer at point to Jython interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'jython dedicated switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send buffer at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'jython dedicated 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send buffer at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'jython dedicated 'no-switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send buffer at point to Jython unique interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'jython t switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send buffer at point to Jython unique interpreter and switch to result."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'jython t 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python (&optional dedicated fast split switch proc wholebuf)
  "Send buffer at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python dedicated switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python-switch (&optional dedicated fast split proc wholebuf)
  "Send buffer at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python dedicated 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send buffer at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python dedicated 'no-switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python-dedicated (&optional fast split switch proc wholebuf)
  "Send buffer at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python t switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send buffer at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python t 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send buffer at point to Python2 interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python2 dedicated switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send buffer at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python2 dedicated 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send buffer at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python2 dedicated 'no-switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send buffer at point to Python2 unique interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python2 t switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send buffer at point to Python2 unique interpreter and switch to result."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python2 t 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send buffer at point to Python3 interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python3 dedicated switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send buffer at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python3 dedicated 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send buffer at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python3 dedicated 'no-switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send buffer at point to Python3 unique interpreter."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python3 t switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-buffer-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send buffer at point to Python3 unique interpreter and switch to result."
  (interactive)
  (let ((py-master-file (or py-master-file (py-fetch-py-master-file))))
    (when py-master-file
      (let* ((filename (expand-file-name py-master-file))
	     (buffer (or (get-file-buffer filename)
			 (find-file-noselect filename))))
	(set-buffer buffer))))
  (py--execute-prepare 'buffer 'python3 t 'switch (point-min) (point-max) nil fast proc wholebuf split))

(defun py-execute-class (&optional shell dedicated fast split switch proc wholebuf)
  "Send class at point to  interpreter."
  (interactive)
  (py--execute-prepare 'class shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-class-switch (&optional shell dedicated fast split proc wholebuf)
  "Send class at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'class shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-class-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send class at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'class shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-class-dedicated (&optional shell fast split switch proc wholebuf)
  "Send class at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'class shell t switch nil fast proc wholebuf split))

(defun py-execute-class-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send class at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'class shell t 'switch nil fast proc wholebuf split))

(defun py-execute-class-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send class at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'class 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-class-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send class at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'class 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-class-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send class at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'class 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-class-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send class at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'class 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-class-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send class at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'class 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-class-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send class at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'class 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-class-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send class at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'class 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-class-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send class at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'class 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-class-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send class at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'class 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-class-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send class at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'class 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-class-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send class at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'class 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-class-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send class at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'class 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-class-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send class at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'class 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-class-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send class at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'class 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-class-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send class at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'class 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-class-jython (&optional dedicated fast split switch proc wholebuf)
  "Send class at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'class 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-class-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send class at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'class 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-class-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send class at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'class 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-class-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send class at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'class 'jython t switch nil fast proc wholebuf split))

(defun py-execute-class-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send class at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'class 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-class-python (&optional dedicated fast split switch proc wholebuf)
  "Send class at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'class 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-class-python-switch (&optional dedicated fast split proc wholebuf)
  "Send class at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'class 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-class-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send class at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'class 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-class-python-dedicated (&optional fast split switch proc wholebuf)
  "Send class at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'class 'python t switch nil fast proc wholebuf split))

(defun py-execute-class-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send class at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'class 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-class-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send class at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'class 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-class-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send class at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'class 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-class-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send class at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'class 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-class-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send class at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'class 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-class-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send class at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'class 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-class-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send class at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'class 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-class-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send class at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'class 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-class-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send class at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'class 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-class-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send class at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'class 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-class-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send class at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'class 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-clause (&optional shell dedicated fast split switch proc wholebuf)
  "Send clause at point to  interpreter."
  (interactive)
  (py--execute-prepare 'clause shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-clause-switch (&optional shell dedicated fast split proc wholebuf)
  "Send clause at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'clause shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-clause-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send clause at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'clause shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-clause-dedicated (&optional shell fast split switch proc wholebuf)
  "Send clause at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'clause shell t switch nil fast proc wholebuf split))

(defun py-execute-clause-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send clause at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'clause shell t 'switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send clause at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'clause 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send clause at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'clause 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send clause at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'clause 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send clause at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'clause 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send clause at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'clause 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send clause at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'clause 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send clause at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'clause 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send clause at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'clause 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send clause at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'clause 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send clause at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'clause 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send clause at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'clause 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send clause at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'clause 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send clause at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'clause 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send clause at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'clause 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-clause-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send clause at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'clause 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-clause-jython (&optional dedicated fast split switch proc wholebuf)
  "Send clause at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'clause 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-clause-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send clause at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'clause 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-clause-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send clause at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'clause 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-clause-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send clause at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'clause 'jython t switch nil fast proc wholebuf split))

(defun py-execute-clause-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send clause at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'clause 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-clause-python (&optional dedicated fast split switch proc wholebuf)
  "Send clause at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'clause 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-clause-python-switch (&optional dedicated fast split proc wholebuf)
  "Send clause at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'clause 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-clause-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send clause at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'clause 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-clause-python-dedicated (&optional fast split switch proc wholebuf)
  "Send clause at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'clause 'python t switch nil fast proc wholebuf split))

(defun py-execute-clause-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send clause at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'clause 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-clause-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send clause at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'clause 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-clause-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send clause at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'clause 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-clause-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send clause at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'clause 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-clause-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send clause at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'clause 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-clause-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send clause at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'clause 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-clause-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send clause at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'clause 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-clause-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send clause at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'clause 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-clause-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send clause at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'clause 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-clause-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send clause at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'clause 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-clause-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send clause at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'clause 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-def (&optional shell dedicated fast split switch proc wholebuf)
  "Send def at point to  interpreter."
  (interactive)
  (py--execute-prepare 'def shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-switch (&optional shell dedicated fast split proc wholebuf)
  "Send def at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send def at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-dedicated (&optional shell fast split switch proc wholebuf)
  "Send def at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'def shell t switch nil fast proc wholebuf split))

(defun py-execute-def-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send def at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def shell t 'switch nil fast proc wholebuf split))

(defun py-execute-def-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send def at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'def 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send def at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send def at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'def 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-def-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-def-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send def at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'def 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send def at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send def at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'def 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-def-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-def-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send def at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'def 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send def at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send def at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'def 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-def-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-def-jython (&optional dedicated fast split switch proc wholebuf)
  "Send def at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'def 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send def at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send def at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'def 'jython t switch nil fast proc wholebuf split))

(defun py-execute-def-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-def-python (&optional dedicated fast split switch proc wholebuf)
  "Send def at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-python-switch (&optional dedicated fast split proc wholebuf)
  "Send def at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-python-dedicated (&optional fast split switch proc wholebuf)
  "Send def at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def 'python t switch nil fast proc wholebuf split))

(defun py-execute-def-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-def-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send def at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'def 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send def at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send def at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'def 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-def-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-def-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send def at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'def 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send def at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send def at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'def 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-def-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class (&optional shell dedicated fast split switch proc wholebuf)
  "Send def-or-class at point to  interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-switch (&optional shell dedicated fast split proc wholebuf)
  "Send def-or-class at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def-or-class shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send def-or-class at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def-or-class shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-dedicated (&optional shell fast split switch proc wholebuf)
  "Send def-or-class at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class shell t switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send def-or-class at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def-or-class shell t 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send def-or-class at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send def-or-class at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def-or-class at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send def-or-class at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def-or-class at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send def-or-class at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send def-or-class at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def-or-class at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send def-or-class at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def-or-class at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send def-or-class at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send def-or-class at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def-or-class at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send def-or-class at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def-or-class at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def-or-class 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-jython (&optional dedicated fast split switch proc wholebuf)
  "Send def-or-class at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send def-or-class at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def-or-class 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def-or-class at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def-or-class 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send def-or-class at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'jython t switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def-or-class at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def-or-class 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python (&optional dedicated fast split switch proc wholebuf)
  "Send def-or-class at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def-or-class 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python-switch (&optional dedicated fast split proc wholebuf)
  "Send def-or-class at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def-or-class 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def-or-class at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def-or-class 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python-dedicated (&optional fast split switch proc wholebuf)
  "Send def-or-class at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def-or-class 'python t switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def-or-class at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'def-or-class 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send def-or-class at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send def-or-class at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def-or-class 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def-or-class at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def-or-class 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send def-or-class at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def-or-class at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def-or-class 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send def-or-class at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send def-or-class at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'def-or-class 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send def-or-class at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'def-or-class 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send def-or-class at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'def-or-class 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-def-or-class-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send def-or-class at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'def-or-class 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-expression (&optional shell dedicated fast split switch proc wholebuf)
  "Send expression at point to  interpreter."
  (interactive)
  (py--execute-prepare 'expression shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-expression-switch (&optional shell dedicated fast split proc wholebuf)
  "Send expression at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'expression shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-expression-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send expression at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'expression shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-expression-dedicated (&optional shell fast split switch proc wholebuf)
  "Send expression at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'expression shell t switch nil fast proc wholebuf split))

(defun py-execute-expression-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send expression at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'expression shell t 'switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send expression at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'expression 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send expression at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'expression 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send expression at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'expression 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send expression at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'expression 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send expression at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'expression 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send expression at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'expression 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send expression at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'expression 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send expression at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'expression 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send expression at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'expression 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send expression at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'expression 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send expression at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'expression 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send expression at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'expression 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send expression at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'expression 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send expression at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'expression 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-expression-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send expression at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'expression 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-expression-jython (&optional dedicated fast split switch proc wholebuf)
  "Send expression at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'expression 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-expression-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send expression at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'expression 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-expression-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send expression at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'expression 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-expression-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send expression at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'expression 'jython t switch nil fast proc wholebuf split))

(defun py-execute-expression-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send expression at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'expression 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-expression-python (&optional dedicated fast split switch proc wholebuf)
  "Send expression at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'expression 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-expression-python-switch (&optional dedicated fast split proc wholebuf)
  "Send expression at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'expression 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-expression-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send expression at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'expression 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-expression-python-dedicated (&optional fast split switch proc wholebuf)
  "Send expression at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'expression 'python t switch nil fast proc wholebuf split))

(defun py-execute-expression-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send expression at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'expression 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-expression-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send expression at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'expression 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-expression-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send expression at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'expression 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-expression-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send expression at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'expression 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-expression-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send expression at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'expression 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-expression-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send expression at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'expression 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-expression-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send expression at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'expression 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-expression-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send expression at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'expression 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-expression-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send expression at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'expression 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-expression-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send expression at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'expression 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-expression-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send expression at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'expression 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-indent (&optional shell dedicated fast split switch proc wholebuf)
  "Send indent at point to  interpreter."
  (interactive)
  (py--execute-prepare 'indent shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-indent-switch (&optional shell dedicated fast split proc wholebuf)
  "Send indent at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'indent shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-indent-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send indent at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'indent shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-indent-dedicated (&optional shell fast split switch proc wholebuf)
  "Send indent at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'indent shell t switch nil fast proc wholebuf split))

(defun py-execute-indent-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send indent at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'indent shell t 'switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send indent at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'indent 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send indent at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'indent 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send indent at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'indent 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send indent at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'indent 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send indent at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'indent 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send indent at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'indent 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send indent at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'indent 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send indent at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'indent 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send indent at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'indent 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send indent at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'indent 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send indent at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'indent 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send indent at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'indent 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send indent at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'indent 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send indent at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'indent 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-indent-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send indent at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'indent 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-indent-jython (&optional dedicated fast split switch proc wholebuf)
  "Send indent at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'indent 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-indent-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send indent at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'indent 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-indent-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send indent at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'indent 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-indent-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send indent at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'indent 'jython t switch nil fast proc wholebuf split))

(defun py-execute-indent-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send indent at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'indent 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-indent-python (&optional dedicated fast split switch proc wholebuf)
  "Send indent at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'indent 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-indent-python-switch (&optional dedicated fast split proc wholebuf)
  "Send indent at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'indent 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-indent-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send indent at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'indent 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-indent-python-dedicated (&optional fast split switch proc wholebuf)
  "Send indent at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'indent 'python t switch nil fast proc wholebuf split))

(defun py-execute-indent-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send indent at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'indent 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-indent-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send indent at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'indent 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-indent-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send indent at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'indent 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-indent-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send indent at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'indent 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-indent-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send indent at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'indent 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-indent-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send indent at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'indent 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-indent-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send indent at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'indent 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-indent-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send indent at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'indent 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-indent-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send indent at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'indent 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-indent-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send indent at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'indent 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-indent-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send indent at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'indent 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-line (&optional shell dedicated fast split switch proc wholebuf)
  "Send line at point to  interpreter."
  (interactive)
  (py--execute-prepare 'line shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-line-switch (&optional shell dedicated fast split proc wholebuf)
  "Send line at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'line shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-line-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send line at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'line shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-line-dedicated (&optional shell fast split switch proc wholebuf)
  "Send line at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'line shell t switch nil fast proc wholebuf split))

(defun py-execute-line-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send line at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'line shell t 'switch nil fast proc wholebuf split))

(defun py-execute-line-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send line at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'line 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-line-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send line at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'line 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-line-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send line at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'line 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-line-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send line at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'line 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-line-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send line at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'line 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-line-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send line at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'line 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-line-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send line at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'line 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-line-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send line at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'line 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-line-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send line at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'line 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-line-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send line at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'line 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-line-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send line at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'line 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-line-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send line at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'line 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-line-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send line at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'line 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-line-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send line at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'line 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-line-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send line at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'line 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-line-jython (&optional dedicated fast split switch proc wholebuf)
  "Send line at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'line 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-line-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send line at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'line 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-line-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send line at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'line 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-line-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send line at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'line 'jython t switch nil fast proc wholebuf split))

(defun py-execute-line-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send line at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'line 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-line-python (&optional dedicated fast split switch proc wholebuf)
  "Send line at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'line 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-line-python-switch (&optional dedicated fast split proc wholebuf)
  "Send line at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'line 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-line-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send line at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'line 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-line-python-dedicated (&optional fast split switch proc wholebuf)
  "Send line at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'line 'python t switch nil fast proc wholebuf split))

(defun py-execute-line-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send line at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'line 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-line-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send line at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'line 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-line-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send line at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'line 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-line-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send line at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'line 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-line-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send line at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'line 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-line-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send line at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'line 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-line-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send line at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'line 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-line-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send line at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'line 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-line-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send line at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'line 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-line-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send line at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'line 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-line-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send line at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'line 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block (&optional shell dedicated fast split switch proc wholebuf)
  "Send minor-block at point to  interpreter."
  (interactive)
  (py--execute-prepare 'minor-block shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-minor-block-switch (&optional shell dedicated fast split proc wholebuf)
  "Send minor-block at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'minor-block shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send minor-block at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'minor-block shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-minor-block-dedicated (&optional shell fast split switch proc wholebuf)
  "Send minor-block at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'minor-block shell t switch nil fast proc wholebuf split))

(defun py-execute-minor-block-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send minor-block at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'minor-block shell t 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send minor-block at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send minor-block at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send minor-block at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'minor-block 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send minor-block at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send minor-block at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send minor-block at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send minor-block at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send minor-block at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'minor-block 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send minor-block at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send minor-block at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send minor-block at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send minor-block at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send minor-block at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'minor-block 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send minor-block at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-minor-block-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send minor-block at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'minor-block 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-jython (&optional dedicated fast split switch proc wholebuf)
  "Send minor-block at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-minor-block-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send minor-block at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'minor-block 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send minor-block at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'minor-block 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-minor-block-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send minor-block at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'jython t switch nil fast proc wholebuf split))

(defun py-execute-minor-block-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send minor-block at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'minor-block 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python (&optional dedicated fast split switch proc wholebuf)
  "Send minor-block at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'minor-block 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python-switch (&optional dedicated fast split proc wholebuf)
  "Send minor-block at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'minor-block 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send minor-block at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'minor-block 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python-dedicated (&optional fast split switch proc wholebuf)
  "Send minor-block at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'minor-block 'python t switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send minor-block at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'minor-block 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send minor-block at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send minor-block at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'minor-block 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send minor-block at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'minor-block 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send minor-block at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send minor-block at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'minor-block 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send minor-block at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send minor-block at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'minor-block 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send minor-block at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'minor-block 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send minor-block at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'minor-block 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-minor-block-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send minor-block at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'minor-block 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph (&optional shell dedicated fast split switch proc wholebuf)
  "Send paragraph at point to  interpreter."
  (interactive)
  (py--execute-prepare 'paragraph shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-paragraph-switch (&optional shell dedicated fast split proc wholebuf)
  "Send paragraph at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'paragraph shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send paragraph at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'paragraph shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-paragraph-dedicated (&optional shell fast split switch proc wholebuf)
  "Send paragraph at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'paragraph shell t switch nil fast proc wholebuf split))

(defun py-execute-paragraph-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send paragraph at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'paragraph shell t 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send paragraph at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send paragraph at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send paragraph at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'paragraph 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send paragraph at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send paragraph at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send paragraph at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send paragraph at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send paragraph at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'paragraph 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send paragraph at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send paragraph at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send paragraph at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send paragraph at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send paragraph at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'paragraph 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send paragraph at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-paragraph-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send paragraph at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'paragraph 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-jython (&optional dedicated fast split switch proc wholebuf)
  "Send paragraph at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-paragraph-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send paragraph at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'paragraph 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send paragraph at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'paragraph 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-paragraph-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send paragraph at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'jython t switch nil fast proc wholebuf split))

(defun py-execute-paragraph-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send paragraph at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'paragraph 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python (&optional dedicated fast split switch proc wholebuf)
  "Send paragraph at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'paragraph 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python-switch (&optional dedicated fast split proc wholebuf)
  "Send paragraph at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'paragraph 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send paragraph at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'paragraph 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python-dedicated (&optional fast split switch proc wholebuf)
  "Send paragraph at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'paragraph 'python t switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send paragraph at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'paragraph 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send paragraph at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send paragraph at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'paragraph 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send paragraph at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'paragraph 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send paragraph at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send paragraph at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'paragraph 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send paragraph at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send paragraph at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'paragraph 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send paragraph at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'paragraph 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send paragraph at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'paragraph 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-paragraph-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send paragraph at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'paragraph 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression (&optional shell dedicated fast split switch proc wholebuf)
  "Send partial-expression at point to  interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-switch (&optional shell dedicated fast split proc wholebuf)
  "Send partial-expression at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'partial-expression shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send partial-expression at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'partial-expression shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-dedicated (&optional shell fast split switch proc wholebuf)
  "Send partial-expression at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression shell t switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send partial-expression at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'partial-expression shell t 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send partial-expression at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send partial-expression at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send partial-expression at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send partial-expression at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send partial-expression at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send partial-expression at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send partial-expression at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send partial-expression at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send partial-expression at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send partial-expression at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send partial-expression at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send partial-expression at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send partial-expression at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send partial-expression at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send partial-expression at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'partial-expression 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-jython (&optional dedicated fast split switch proc wholebuf)
  "Send partial-expression at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send partial-expression at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'partial-expression 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send partial-expression at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'partial-expression 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send partial-expression at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'jython t switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send partial-expression at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'partial-expression 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python (&optional dedicated fast split switch proc wholebuf)
  "Send partial-expression at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'partial-expression 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python-switch (&optional dedicated fast split proc wholebuf)
  "Send partial-expression at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'partial-expression 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send partial-expression at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'partial-expression 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python-dedicated (&optional fast split switch proc wholebuf)
  "Send partial-expression at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'partial-expression 'python t switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send partial-expression at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'partial-expression 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send partial-expression at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send partial-expression at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'partial-expression 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send partial-expression at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'partial-expression 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send partial-expression at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send partial-expression at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'partial-expression 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send partial-expression at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send partial-expression at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'partial-expression 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send partial-expression at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'partial-expression 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send partial-expression at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'partial-expression 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-partial-expression-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send partial-expression at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'partial-expression 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-region (beg end &optional shell dedicated fast split switch proc wholebuf)
  "Send region at point to  interpreter."
  (interactive "r")
  (py--execute-prepare 'region shell dedicated switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-switch (beg end &optional shell dedicated fast split proc wholebuf)
  "Send region at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive "r")
  (py--execute-prepare 'region shell dedicated 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-no-switch (beg end &optional shell dedicated fast split  proc wholebuf)
  "Send region at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive "r")
  (py--execute-prepare 'region shell dedicated 'no-switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-dedicated (beg end &optional shell fast split switch proc wholebuf)
  "Send region at point to  unique interpreter."
  (interactive "r")
  (py--execute-prepare 'region shell t switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-dedicated-switch (beg end &optional shell  fast split  proc wholebuf)
  "Send region at point to  unique interpreter and switch to result."
  (interactive "r")
  (py--execute-prepare 'region shell t 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython (beg end &optional dedicated fast split switch proc wholebuf)
  "Send region at point to IPython interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'ipython dedicated switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython-switch (beg end &optional dedicated fast split proc wholebuf)
  "Send region at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive "r")
  (py--execute-prepare 'region 'ipython dedicated 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython-no-switch (beg end &optional dedicated fast split  proc wholebuf)
  "Send region at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive "r")
  (py--execute-prepare 'region 'ipython dedicated 'no-switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython-dedicated (beg end &optional fast split switch proc wholebuf)
  "Send region at point to IPython unique interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'ipython t switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython-dedicated-switch (beg end &optional  fast split  proc wholebuf)
  "Send region at point to IPython unique interpreter and switch to result."
  (interactive "r")
  (py--execute-prepare 'region 'ipython t 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython2.7 (beg end &optional dedicated fast split switch proc wholebuf)
  "Send region at point to IPython interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'ipython2.7 dedicated switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython2.7-switch (beg end &optional dedicated fast split proc wholebuf)
  "Send region at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive "r")
  (py--execute-prepare 'region 'ipython2.7 dedicated 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython2.7-no-switch (beg end &optional dedicated fast split  proc wholebuf)
  "Send region at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive "r")
  (py--execute-prepare 'region 'ipython2.7 dedicated 'no-switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython2.7-dedicated (beg end &optional fast split switch proc wholebuf)
  "Send region at point to IPython unique interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'ipython2.7 t switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython2.7-dedicated-switch (beg end &optional  fast split  proc wholebuf)
  "Send region at point to IPython unique interpreter and switch to result."
  (interactive "r")
  (py--execute-prepare 'region 'ipython2.7 t 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython3 (beg end &optional dedicated fast split switch proc wholebuf)
  "Send region at point to IPython interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'ipython3 dedicated switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython3-switch (beg end &optional dedicated fast split proc wholebuf)
  "Send region at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive "r")
  (py--execute-prepare 'region 'ipython3 dedicated 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython3-no-switch (beg end &optional dedicated fast split  proc wholebuf)
  "Send region at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive "r")
  (py--execute-prepare 'region 'ipython3 dedicated 'no-switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython3-dedicated (beg end &optional fast split switch proc wholebuf)
  "Send region at point to IPython unique interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'ipython3 t switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-ipython3-dedicated-switch (beg end &optional  fast split  proc wholebuf)
  "Send region at point to IPython unique interpreter and switch to result."
  (interactive "r")
  (py--execute-prepare 'region 'ipython3 t 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-jython (beg end &optional dedicated fast split switch proc wholebuf)
  "Send region at point to Jython interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'jython dedicated switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-jython-switch (beg end &optional dedicated fast split proc wholebuf)
  "Send region at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive "r")
  (py--execute-prepare 'region 'jython dedicated 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-jython-no-switch (beg end &optional dedicated fast split  proc wholebuf)
  "Send region at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive "r")
  (py--execute-prepare 'region 'jython dedicated 'no-switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-jython-dedicated (beg end &optional fast split switch proc wholebuf)
  "Send region at point to Jython unique interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'jython t switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-jython-dedicated-switch (beg end &optional  fast split  proc wholebuf)
  "Send region at point to Jython unique interpreter and switch to result."
  (interactive "r")
  (py--execute-prepare 'region 'jython t 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python (beg end &optional dedicated fast split switch proc wholebuf)
  "Send region at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive "r")
  (py--execute-prepare 'region 'python dedicated switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python-switch (beg end &optional dedicated fast split proc wholebuf)
  "Send region at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive "r")
  (py--execute-prepare 'region 'python dedicated 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python-no-switch (beg end &optional dedicated fast split  proc wholebuf)
  "Send region at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive "r")
  (py--execute-prepare 'region 'python dedicated 'no-switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python-dedicated (beg end &optional fast split switch proc wholebuf)
  "Send region at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive "r")
  (py--execute-prepare 'region 'python t switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python-dedicated-switch (beg end &optional  fast split  proc wholebuf)
  "Send region at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive "r")
  (py--execute-prepare 'region 'python t 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python2 (beg end &optional dedicated fast split switch proc wholebuf)
  "Send region at point to Python2 interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'python2 dedicated switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python2-switch (beg end &optional dedicated fast split proc wholebuf)
  "Send region at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive "r")
  (py--execute-prepare 'region 'python2 dedicated 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python2-no-switch (beg end &optional dedicated fast split  proc wholebuf)
  "Send region at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive "r")
  (py--execute-prepare 'region 'python2 dedicated 'no-switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python2-dedicated (beg end &optional fast split switch proc wholebuf)
  "Send region at point to Python2 unique interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'python2 t switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python2-dedicated-switch (beg end &optional  fast split  proc wholebuf)
  "Send region at point to Python2 unique interpreter and switch to result."
  (interactive "r")
  (py--execute-prepare 'region 'python2 t 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python3 (beg end &optional dedicated fast split switch proc wholebuf)
  "Send region at point to Python3 interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'python3 dedicated switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python3-switch (beg end &optional dedicated fast split proc wholebuf)
  "Send region at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive "r")
  (py--execute-prepare 'region 'python3 dedicated 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python3-no-switch (beg end &optional dedicated fast split  proc wholebuf)
  "Send region at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive "r")
  (py--execute-prepare 'region 'python3 dedicated 'no-switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python3-dedicated (beg end &optional fast split switch proc wholebuf)
  "Send region at point to Python3 unique interpreter."
  (interactive "r")
  (py--execute-prepare 'region 'python3 t switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-region-python3-dedicated-switch (beg end &optional  fast split  proc wholebuf)
  "Send region at point to Python3 unique interpreter and switch to result."
  (interactive "r")
  (py--execute-prepare 'region 'python3 t 'switch (or beg (region-beginning)) (or end (region-end)) nil fast proc wholebuf split))

(defun py-execute-statement (&optional shell dedicated fast split switch proc wholebuf)
  "Send statement at point to  interpreter."
  (interactive)
  (py--execute-prepare 'statement shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-statement-switch (&optional shell dedicated fast split proc wholebuf)
  "Send statement at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'statement shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-statement-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send statement at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'statement shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-statement-dedicated (&optional shell fast split switch proc wholebuf)
  "Send statement at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'statement shell t switch nil fast proc wholebuf split))

(defun py-execute-statement-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send statement at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'statement shell t 'switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send statement at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'statement 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send statement at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'statement 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send statement at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'statement 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send statement at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'statement 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send statement at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'statement 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send statement at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'statement 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send statement at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'statement 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send statement at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'statement 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send statement at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'statement 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send statement at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'statement 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send statement at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'statement 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send statement at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'statement 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send statement at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'statement 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send statement at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'statement 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-statement-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send statement at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'statement 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-statement-jython (&optional dedicated fast split switch proc wholebuf)
  "Send statement at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'statement 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-statement-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send statement at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'statement 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-statement-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send statement at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'statement 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-statement-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send statement at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'statement 'jython t switch nil fast proc wholebuf split))

(defun py-execute-statement-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send statement at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'statement 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-statement-python (&optional dedicated fast split switch proc wholebuf)
  "Send statement at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'statement 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-statement-python-switch (&optional dedicated fast split proc wholebuf)
  "Send statement at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'statement 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-statement-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send statement at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'statement 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-statement-python-dedicated (&optional fast split switch proc wholebuf)
  "Send statement at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'statement 'python t switch nil fast proc wholebuf split))

(defun py-execute-statement-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send statement at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'statement 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-statement-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send statement at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'statement 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-statement-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send statement at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'statement 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-statement-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send statement at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'statement 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-statement-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send statement at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'statement 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-statement-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send statement at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'statement 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-statement-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send statement at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'statement 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-statement-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send statement at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'statement 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-statement-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send statement at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'statement 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-statement-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send statement at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'statement 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-statement-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send statement at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'statement 'python3 t 'switch nil fast proc wholebuf split))

(defun py-execute-top-level (&optional shell dedicated fast split switch proc wholebuf)
  "Send top-level at point to  interpreter."
  (interactive)
  (py--execute-prepare 'top-level shell dedicated switch nil fast proc wholebuf split))

(defun py-execute-top-level-switch (&optional shell dedicated fast split proc wholebuf)
  "Send top-level at point to  interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'top-level shell dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-no-switch (&optional shell dedicated fast split  proc wholebuf)
  "Send top-level at point to  interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'top-level shell dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-top-level-dedicated (&optional shell fast split switch proc wholebuf)
  "Send top-level at point to  unique interpreter."
  (interactive)
  (py--execute-prepare 'top-level shell t switch nil fast proc wholebuf split))

(defun py-execute-top-level-dedicated-switch (&optional shell  fast split  proc wholebuf)
  "Send top-level at point to  unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'top-level shell t 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython (&optional dedicated fast split switch proc wholebuf)
  "Send top-level at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'ipython dedicated switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython-switch (&optional dedicated fast split proc wholebuf)
  "Send top-level at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'top-level 'ipython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send top-level at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'top-level 'ipython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython-dedicated (&optional fast split switch proc wholebuf)
  "Send top-level at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'ipython t switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send top-level at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'top-level 'ipython t 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython2.7 (&optional dedicated fast split switch proc wholebuf)
  "Send top-level at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'ipython2.7 dedicated switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython2.7-switch (&optional dedicated fast split proc wholebuf)
  "Send top-level at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'top-level 'ipython2.7 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython2.7-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send top-level at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'top-level 'ipython2.7 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython2.7-dedicated (&optional fast split switch proc wholebuf)
  "Send top-level at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'ipython2.7 t switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython2.7-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send top-level at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'top-level 'ipython2.7 t 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython3 (&optional dedicated fast split switch proc wholebuf)
  "Send top-level at point to IPython interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'ipython3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython3-switch (&optional dedicated fast split proc wholebuf)
  "Send top-level at point to IPython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'top-level 'ipython3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send top-level at point to IPython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'top-level 'ipython3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython3-dedicated (&optional fast split switch proc wholebuf)
  "Send top-level at point to IPython unique interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'ipython3 t switch nil fast proc wholebuf split))

(defun py-execute-top-level-ipython3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send top-level at point to IPython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'top-level 'ipython3 t 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-jython (&optional dedicated fast split switch proc wholebuf)
  "Send top-level at point to Jython interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'jython dedicated switch nil fast proc wholebuf split))

(defun py-execute-top-level-jython-switch (&optional dedicated fast split proc wholebuf)
  "Send top-level at point to Jython interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'top-level 'jython dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-jython-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send top-level at point to Jython interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'top-level 'jython dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-top-level-jython-dedicated (&optional fast split switch proc wholebuf)
  "Send top-level at point to Jython unique interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'jython t switch nil fast proc wholebuf split))

(defun py-execute-top-level-jython-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send top-level at point to Jython unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'top-level 'jython t 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-python (&optional dedicated fast split switch proc wholebuf)
  "Send top-level at point to default interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'top-level 'python dedicated switch nil fast proc wholebuf split))

(defun py-execute-top-level-python-switch (&optional dedicated fast split proc wholebuf)
  "Send top-level at point to default interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'top-level 'python dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-python-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send top-level at point to default interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ 

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'top-level 'python dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-top-level-python-dedicated (&optional fast split switch proc wholebuf)
  "Send top-level at point to default unique interpreter.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'top-level 'python t switch nil fast proc wholebuf split))

(defun py-execute-top-level-python-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send top-level at point to default unique interpreter and switch to result.

For ‘default’ see value of ‘py-shell-name’"
  (interactive)
  (py--execute-prepare 'top-level 'python t 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-python2 (&optional dedicated fast split switch proc wholebuf)
  "Send top-level at point to Python2 interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'python2 dedicated switch nil fast proc wholebuf split))

(defun py-execute-top-level-python2-switch (&optional dedicated fast split proc wholebuf)
  "Send top-level at point to Python2 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'top-level 'python2 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-python2-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send top-level at point to Python2 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'top-level 'python2 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-top-level-python2-dedicated (&optional fast split switch proc wholebuf)
  "Send top-level at point to Python2 unique interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'python2 t switch nil fast proc wholebuf split))

(defun py-execute-top-level-python2-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send top-level at point to Python2 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'top-level 'python2 t 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-python3 (&optional dedicated fast split switch proc wholebuf)
  "Send top-level at point to Python3 interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'python3 dedicated switch nil fast proc wholebuf split))

(defun py-execute-top-level-python3-switch (&optional dedicated fast split proc wholebuf)
  "Send top-level at point to Python3 interpreter.

Switch to output buffer. Ignores ‘py-switch-buffers-on-execute-p’."
  (interactive)
  (py--execute-prepare 'top-level 'python3 dedicated 'switch nil fast proc wholebuf split))

(defun py-execute-top-level-python3-no-switch (&optional dedicated fast split  proc wholebuf)
  "Send top-level at point to Python3 interpreter.

Keep current buffer. Ignores ‘py-switch-buffers-on-execute-p’ "
  (interactive)
  (py--execute-prepare 'top-level 'python3 dedicated 'no-switch nil fast proc wholebuf split))

(defun py-execute-top-level-python3-dedicated (&optional fast split switch proc wholebuf)
  "Send top-level at point to Python3 unique interpreter."
  (interactive)
  (py--execute-prepare 'top-level 'python3 t switch nil fast proc wholebuf split))

(defun py-execute-top-level-python3-dedicated-switch (&optional  fast split  proc wholebuf)
  "Send top-level at point to Python3 unique interpreter and switch to result."
  (interactive)
  (py--execute-prepare 'top-level 'python3 t 'switch nil fast proc wholebuf split))

;; python-abbrev-propose

(defun py-edit-abbrevs ()
  "Jumps to `python-mode-abbrev-table' in a buffer containing lists of abbrev definitions.
You can edit them and type \\<edit-abbrevs-map>\\[edit-abbrevs-redefine] to redefine abbrevs
according to your editing.
Buffer contains a header line for each abbrev table,
 which is the abbrev table name in parentheses.
This is followed by one line per abbrev in that table:
NAME   USECOUNT   EXPANSION   HOOK
where NAME and EXPANSION are strings with quotes,
USECOUNT is an integer, and HOOK is any valid function
or may be omitted (it is usually omitted).  "
  (interactive)
  (save-excursion
    (let ((mat (abbrev-table-name local-abbrev-table)))
      (prepare-abbrev-list-buffer)
      (set-buffer "*Abbrevs*")
      (switch-to-buffer (current-buffer))
      (goto-char (point-min))
      (search-forward (concat "(" (format "%s" mat))))))

(defun py--add-abbrev-propose (table type arg &optional dont-ask)
  (save-excursion
    (let ((orig (point))
          proposal exp name)
      (while (< 0 arg)
        (py-beginning-of-partial-expression)
        (when (looking-at "[[:alpha:]]")
          (setq proposal (concat (downcase (match-string-no-properties 0)) proposal)))
        (setq arg (1- arg)))
      (setq exp (buffer-substring-no-properties (point) orig))
      (setq name
            ;; ask only when interactive
            (if dont-ask
                proposal
              (read-string (format (if exp "%s abbrev for \"%s\": "
                                     "Undefine %s abbrev: ")
                                   type exp) proposal)))
      (set-text-properties 0 (length name) nil name)
      (when (or (null exp)
                (not (abbrev-expansion name table))
                (y-or-n-p (format "%s expands to \"%s\"; redefine? "
                                  name (abbrev-expansion name table))))
        (define-abbrev table (downcase name) exp)))))

(defun py-add-abbrev (arg)
  "Defines python-mode specific abbrev for last expressions before point.
Argument is how many `py-partial-expression's form the expansion; or zero means the region is the expansion.

Reads the abbreviation in the minibuffer; with numeric arg it displays a proposal for an abbrev.
Proposal is composed from the initial character(s) of the
expansion.

Don't use this function in a Lisp program; use `define-abbrev' instead."
  (interactive "p")
  (save-excursion
    (py--add-abbrev-propose
     (if only-global-abbrevs
         global-abbrev-table
       (or local-abbrev-table
           (error "No per-mode abbrev table")))
     "Mode" arg)))

;; python-components-paragraph

(defun py-fill-paren (&optional justify)
  "Paren fill function for `py-fill-paragraph'.
JUSTIFY should be used (if applicable) as in `fill-paragraph'."
  (interactive "*P")
  (save-restriction
    (save-excursion
      (let ((pps (parse-partial-sexp (point-min) (point))))
	(if (nth 1 pps)
	    (let* ((beg (copy-marker (nth 1 pps)))
		   (end (and beg (save-excursion (goto-char (nth 1 pps))
						 (forward-list))))
		   (paragraph-start "\f\\|[ \t]*$")
		   (paragraph-separate ","))
	      (when end (narrow-to-region beg end)
		    (fill-region beg end justify)
		    (while (not (eobp))
		      (forward-line 1)
		      (py-indent-line)
		      (goto-char (line-end-position))))))))))

(defun py-fill-string-django (&optional justify)
  "Fill docstring according to Django's coding standards style.

    \"\"\"
    Process foo, return bar.
    \"\"\"

    \"\"\"
    Process foo, return bar.

    If processing fails throw ProcessingError.
    \"\"\"

See available styles at `py-fill-paragraph' or var `py-docstring-style'
"
  (interactive "*P")
  (py-fill-string justify 'django t))

(defun py-fill-string-onetwo (&optional justify)
  "One newline and start and Two at end style.

    \"\"\"Process foo, return bar.\"\"\"

    \"\"\"
    Process foo, return bar.

    If processing fails throw ProcessingError.

    \"\"\"

See available styles at `py-fill-paragraph' or var `py-docstring-style'
"
  (interactive "*P")
  (py-fill-string justify 'onetwo t))

(defun py-fill-string-pep-257 (&optional justify)
  "PEP-257 with 2 newlines at end of string.

    \"\"\"Process foo, return bar.\"\"\"

    \"\"\"Process foo, return bar.

    If processing fails throw ProcessingError.

    \"\"\"

See available styles at `py-fill-paragraph' or var `py-docstring-style'
"
  (interactive "*P")
  (py-fill-string justify 'pep-257 t))

(defun py-fill-string-pep-257-nn (&optional justify)
  "PEP-257 with 1 newline at end of string.

    \"\"\"Process foo, return bar.\"\"\"

    \"\"\"Process foo, return bar.

    If processing fails throw ProcessingError.
    \"\"\"

See available styles at `py-fill-paragraph' or var `py-docstring-style'
"
  (interactive "*P")
  (py-fill-string justify 'pep-257-nn t))

(defun py-fill-string-symmetric (&optional justify)
  "Symmetric style.

    \"\"\"Process foo, return bar.\"\"\"

    \"\"\"
    Process foo, return bar.

    If processing fails throw ProcessingError.
    \"\"\"

See available styles at `py-fill-paragraph' or var `py-docstring-style'
"
  (interactive "*P")
  (py-fill-string justify 'symmetric t))


(defun py-set-nil-docstring-style ()
  "Set py-docstring-style to 'nil"
  (interactive)
  (setq py-docstring-style 'nil)
  (when (and (called-interactively-p 'any) py-verbose-p)
    (message "docstring-style set to:  %s" py-docstring-style)))

(defun py-set-pep-257-nn-docstring-style ()
  "Set py-docstring-style to 'pep-257-nn"
  (interactive)
  (setq py-docstring-style 'pep-257-nn)
  (when (and (called-interactively-p 'any) py-verbose-p)
    (message "docstring-style set to:  %s" py-docstring-style)))

(defun py-set-pep-257-docstring-style ()
  "Set py-docstring-style to 'pep-257"
  (interactive)
  (setq py-docstring-style 'pep-257)
  (when (and (called-interactively-p 'any) py-verbose-p)
    (message "docstring-style set to:  %s" py-docstring-style)))

(defun py-set-django-docstring-style ()
  "Set py-docstring-style to 'django"
  (interactive)
  (setq py-docstring-style 'django)
  (when (and (called-interactively-p 'any) py-verbose-p)
    (message "docstring-style set to:  %s" py-docstring-style)))

(defun py-set-symmetric-docstring-style ()
  "Set py-docstring-style to 'symmetric"
  (interactive)
  (setq py-docstring-style 'symmetric)
  (when (and (called-interactively-p 'any) py-verbose-p)
    (message "docstring-style set to:  %s" py-docstring-style)))

(defun py-set-onetwo-docstring-style ()
  "Set py-docstring-style to 'onetwo"
  (interactive)
  (setq py-docstring-style 'onetwo)
  (when (and (called-interactively-p 'any) py-verbose-p)
    (message "docstring-style set to:  %s" py-docstring-style)))

(defun py-fill-comment (&optional justify)
  "Fill the comment paragraph at point"
  (interactive "*P")
  (let (;; Non-nil if the current line contains a comment.
        has-comment

        ;; If has-comment, the appropriate fill-prefix (format "%s" r the comment.
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
          (fill-paragraph justify))))
    t))

(defun py-fill-labelled-string (beg end)
  "Fill string or paragraph containing lines starting with label

See lp:1066489 "
  (interactive "r*")
  (let ((end (copy-marker end))
        (last (copy-marker (point)))
        this-beg)
    (save-excursion
      (save-restriction
        ;; (narrow-to-region beg end)
        (goto-char beg)
        (skip-chars-forward " \t\r\n\f")
        (if (looking-at py-labelled-re)
            (progn
              (setq this-beg (line-beginning-position))
              (goto-char (match-end 0))
              (while (and (not (eobp)) (re-search-forward py-labelled-re end t 1)(< last (match-beginning 0))(setq last (match-beginning 0)))
                (save-match-data (fill-region this-beg (1- (line-beginning-position))))
                (setq this-beg (line-beginning-position))
                (goto-char (match-end 0)))))))))

(defun py--in-or-behind-or-before-a-docstring ()
  (interactive "*")
  (save-excursion
    (let* ((raw-pps (nth 8 (parse-partial-sexp (point-min) (point))))
	   ;; ;; maybe just behind a string
	   (n8 (or raw-pps
		   ;; maybe in front of a string
		   (back-to-indentation)
		   (nth 8 (parse-partial-sexp (point-min) (point)))))
	   (n8pps (or n8
		      (when
			  (equal (string-to-syntax "|")
				 (syntax-after (point)))
			(and
			  (< 0 (skip-chars-forward "\"'"))
			  (nth 8 (parse-partial-sexp (point-min) (point))))))))
      (and n8pps (py--docstring-p n8pps)))))

(defun py--string-fence-delete-spaces (&optional start)
  "Delete spaces following or preceding delimiters of string at point. "
  (interactive "*")
  (let ((beg (or start (nth 8 (parse-partial-sexp (point-min) (point))))))
    (save-excursion
      (goto-char beg)
      (skip-chars-forward "\"'rRuU")
      (delete-region (point) (progn (skip-chars-forward " \t\r\n\f")(point)))
      (goto-char beg)
      (forward-char 1)
      (skip-syntax-forward "^\|")
      (skip-chars-backward "\"'rRuU")
      ;; (delete-region (point) (progn (skip-chars-backward " \t\r\n\f")(point)))
)))

(defun py--skip-raw-string-front-fence ()
  "Skip forward chars u, U, r, R followed by string-delimiters. "
  (when (member (char-after) (list ?u ?U ?r ?R))
    (forward-char 1))
  (skip-chars-forward "\'\""))

(defun py--fill-fix-end (thisend orig docstring delimiters-style)
  ;; Add the number of newlines indicated by the selected style
  ;; at the end.
  ;; (widen)
  (goto-char thisend)
  (skip-chars-backward "\"'\n ")
  (delete-region (point) (progn (skip-chars-forward " \t\r\n\f") (point)))
  (unless (eq (char-after) ?\n)
    (and
     (cdr delimiters-style)
     (or (newline (cdr delimiters-style)) t)))
  ;; (py-indent-region docstring thisend)
  (goto-char orig))

(defun py--fill-docstring-base (thisbeg thisend style multi-line-p first-line-p beg end py-current-indent orig docstring)
  ;; (widen)
  ;; fill-paragraph causes wrong indent, lp:1397936
  ;; (narrow-to-region thisbeg thisend)
  (let ((delimiters-style
	 (case style
	   ;; delimiters-style is a cons cell with the form
	   ;; (START-NEWLINES .  END-NEWLINES). When any of the sexps
	   ;; is NIL means to not add any newlines for start or end
	   ;; of docstring.  See `py-docstring-style' for a
	   ;; graphic idea of each style.
	   (django (cons 1 1))
	   (onetwo (and multi-line-p (cons 1 2)))
	   (pep-257 (and multi-line-p (cons nil 2)))
	   (pep-257-nn (and multi-line-p (cons nil 1)))
	   (symmetric (and multi-line-p (cons 1 1))))))
    ;;  (save-excursion
    (when style
      ;; Add the number of newlines indicated by the selected style
      ;; at the start.
      (goto-char thisbeg)
      (py--skip-raw-string-front-fence)
      (skip-chars-forward "\'\"")
      (when
	  (car delimiters-style)
	(unless (or (empty-line-p)(eolp))
	  (newline (car delimiters-style))))
      (indent-region beg end py-current-indent))
    (when multi-line-p
      (goto-char thisbeg)
      (py--skip-raw-string-front-fence)
      (skip-chars-forward " \t\r\n\f")
      (forward-line 1)
      (beginning-of-line)
      (unless (empty-line-p) (newline)))
    (py--fill-fix-end thisend orig docstring delimiters-style)))

(defun py--fill-docstring-last-line (thisend beg end multi-line-p)
  (widen)
  ;; (narrow-to-region thisbeg thisend)
  (goto-char thisend)
  (skip-chars-backward "\"'")
  (delete-region (point) (progn (skip-chars-backward " \t\r\n\f")(point)))
  ;; (narrow-to-region beg end)
  (fill-region beg end)
  (setq multi-line-p (string-match "\n" (buffer-substring-no-properties beg end)))
  (when multi-line-p
    ;; adjust the region to fill according to style
    (goto-char end)))

  ;;   (py--fill-docstring-base thisbeg thisend style multi-line-p first-line-p beg end py-current-indent orig docstring))
  ;; (goto-char orig))

(defun py--fill-docstring-first-line (beg end thisbeg thisend style)
  "Refill first line after newline maybe. "
  (fill-region beg (line-end-position))
  (forward-line 1)
  (fill-region (line-beginning-position) end)
  (save-restriction
    (widen)
    (setq multi-line-p (string-match "\n" (buffer-substring-no-properties thisbeg thisend))))
  (when multi-line-p
    ;; adjust the region to fill according to style
    (goto-char beg)
    (skip-chars-forward "\"'")
    ;; style might be nil
    (when style
      (unless (or (eq style 'pep-257-nn)(eq style 'pep-257)(eq (char-after) ?\n))
	(newline-and-indent)
	;; if TQS is at a single line, re-fill remaining line
	(fill-region (point) end)))))

(defun py--fill-docstring (justify style docstring orig py-current-indent)
  ;; Delete spaces after/before string fence
  (py--string-fence-delete-spaces docstring)
  (let* ((thisbeg (copy-marker docstring))
         (thisend (copy-marker
                   (progn
                     (goto-char thisbeg)
		     (py--skip-raw-string-front-fence)
		     (skip-syntax-forward "^\|")
                     (point))))
         (parabeg (progn (goto-char orig) (py--beginning-of-paragraph-position)))
         (paraend (progn (goto-char orig) (py--end-of-paragraph-position)))
         ;; if paragraph is a substring, take it
         (beg (copy-marker (if (< thisbeg parabeg) parabeg thisbeg)))
         (end (copy-marker (if (< thisend paraend) thisend paraend)))
	 (multi-line-p (string-match "\n" (buffer-substring-no-properties thisbeg thisend)))
         first-line-p)
    ;;    (narrow-to-region beg end)
    (goto-char beg)
    (setq first-line-p (member (char-after) (list ?\" ?\' ?u ?U ?r ?R)))
    (cond ((string-match (concat "^" py-labelled-re) (buffer-substring-no-properties beg end))
           (py-fill-labelled-string beg end))
          (first-line-p
           (py--fill-docstring-first-line beg end thisbeg thisend style))
          ((save-excursion (goto-char end)
			   (or (member (char-after) (list ?\" ?\'))
			       (member (char-before) (list ?\" ?\'))))
           (py--fill-docstring-last-line thisend beg end multi-line-p))
          (t ;; (narrow-to-region beg end)
	     (fill-region beg end justify)))
    (py--fill-docstring-base thisbeg thisend style multi-line-p first-line-p beg end py-current-indent orig docstring)))

(defun py-fill-string (&optional justify style docstring)
  "String fill function for `py-fill-paragraph'.
JUSTIFY should be used (if applicable) as in `fill-paragraph'.

Fill according to `py-docstring-style' "
  (interactive
   (list
    (progn
      (barf-if-buffer-read-only)
      (list (if current-prefix-arg 'full) t))
    py-docstring-style
    (or docstring (py--in-or-behind-or-before-a-docstring))))
  (let* ((pps (parse-partial-sexp (point-min) (point)))
	 (indent (save-excursion (and (nth 3 pps) (goto-char (nth 8 pps)) (current-indentation))))
	 ;; fill-paragraph sets orig
	 (orig (if (boundp 'orig) (copy-marker orig) (copy-marker (point))))
	 (docstring (if (and docstring (not (number-or-marker-p docstring)))
			(py--in-or-behind-or-before-a-docstring)
		      docstring)))
    (if docstring
	(py--fill-docstring justify style docstring orig indent)
      (py-fill-paragraph justify))))

(defun py-fill-paragraph (&optional justify)
  (interactive "*")
  (save-excursion
    (save-restriction
      (window-configuration-to-register py-windows-config-register)
      (let* ((pps (parse-partial-sexp (point-min) (point)))
	     (docstring (unless (not py-docstring-style)(py--in-or-behind-or-before-a-docstring)))
	     (fill-column py-comment-fill-column))
	(cond ((or (nth 4 pps)
		   (and (bolp) (looking-at "[ \t]*#[# \t]*")))
	       (py-fill-comment))
	      (docstring
	       (setq fill-column py-docstring-fill-column)
	       (py-fill-string justify py-docstring-style docstring))
	      (t
	       (let* ((beg (save-excursion
			       (if (looking-at paragraph-start)
				   (point)
				 (backward-paragraph)
				 (when (looking-at paragraph-start)
				   (point)))))
		      (end
		       (when beg
			 (save-excursion
			   (forward-paragraph)
			   (when (looking-at paragraph-separate)
			     (point))))))
		 (and beg end (fill-region beg end))))))
      (jump-to-register py-windows-config-register))))

;; python-components-shift-forms


(defun py-shift-left (&optional count start end)
  "Dedent region according to `py-indent-offset' by COUNT times.

If no region is active, current line is dedented.
Returns indentation reached. "
  (interactive "p")
  (let ((erg (py--shift-intern (- count) start end)))
    (when (and (called-interactively-p 'any) py-verbose-p) (message "%s" erg))
    erg))

(defun py-shift-right (&optional count beg end)
  "Indent region according to `py-indent-offset' by COUNT times.

If no region is active, current line is indented.
Returns indentation reached. "
  (interactive "p")
  (let ((erg (py--shift-intern count beg end)))
    (when (and (called-interactively-p 'any) py-verbose-p) (message "%s" erg))
    erg))

(defun py--shift-intern (&optional count start end)
  (save-excursion
    (let* ((count (or count 1))
	   (inhibit-point-motion-hooks t)
           deactivate-mark
           (beg (cond (start)
		      ((and py-shift-require-transient-mark-mode-p
			    (use-region-p))
		       (region-beginning))
                      ((and (not py-shift-require-transient-mark-mode-p)(mark) (not (eq (mark) (point))))
                       (save-excursion
                         (goto-char
                          (region-beginning))))
                      (t (line-beginning-position))))
           (end (cond (end)
		      ((and py-shift-require-transient-mark-mode-p
			    (use-region-p))
		       (region-end))
                      ((and (not py-shift-require-transient-mark-mode-p)(mark) (not (eq (mark) (point))))
                       (save-excursion
                         (goto-char
                          (region-end))))
                      (t (line-end-position)))))
      (setq beg (copy-marker beg))
      (setq end (copy-marker end))
      (if (< 0 count)
          (indent-rigidly beg end py-indent-offset)
        (indent-rigidly beg end (- py-indent-offset)))
      (push-mark beg t)
      (goto-char end)
      (skip-chars-backward " \t\r\n\f"))
    (py-indentation-of-statement)))

(defun py--shift-forms-base (form arg &optional beg end)
  (let* ((begform (concat "py-backward-" form))
         (endform (concat "py-forward-" form))
         (orig (copy-marker (point)))
         (beg (cond (beg)
                    ;; ((and (string-match "region" form) (mark) (not (eq (mark) (point)))(region-beginning)))
		    ((use-region-p)
		     (save-excursion
		       (goto-char (region-beginning))
		       (line-beginning-position)))
		    (t (save-excursion
			 (if
			     (ignore-errors (funcall (car (read-from-string begform))))
			     (line-beginning-position)
			   (error "py--shift-forms-base: No active region"))))))
         (end (cond (end)
                    (
		     ;; (and (mark) (not (eq (mark) (point))))
		     (use-region-p)
                     (region-end))
                    (t (funcall (car (read-from-string endform))))))
         (erg (py--shift-intern arg beg end)))
    (goto-char orig)
    erg))

(defun py-shift-block-right (&optional arg)
  "Indent block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "block" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-block-left (&optional arg)
  "Dedent block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "block" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-block-or-clause-right (&optional arg)
  "Indent block-or-clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "block-or-clause" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-block-or-clause-left (&optional arg)
  "Dedent block-or-clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "block-or-clause" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-class-right (&optional arg)
  "Indent class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "class" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-class-left (&optional arg)
  "Dedent class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "class" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-clause-right (&optional arg)
  "Indent clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "clause" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-clause-left (&optional arg)
  "Dedent clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "clause" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-comment-right (&optional arg)
  "Indent comment by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "comment" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-comment-left (&optional arg)
  "Dedent comment by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "comment" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-def-right (&optional arg)
  "Indent def by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "def" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-def-left (&optional arg)
  "Dedent def by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "def" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-def-or-class-right (&optional arg)
  "Indent def-or-class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "def-or-class" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-def-or-class-left (&optional arg)
  "Dedent def-or-class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "def-or-class" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-indent-right (&optional arg)
  "Indent indent by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "indent" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-indent-left (&optional arg)
  "Dedent indent by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "indent" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-minor-block-right (&optional arg)
  "Indent minor-block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "minor-block" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-minor-block-left (&optional arg)
  "Dedent minor-block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "minor-block" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-paragraph-right (&optional arg)
  "Indent paragraph by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "paragraph" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-paragraph-left (&optional arg)
  "Dedent paragraph by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "paragraph" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-region-right (&optional arg)
  "Indent region by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "region" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-region-left (&optional arg)
  "Dedent region by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "region" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-statement-right (&optional arg)
  "Indent statement by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "statement" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-statement-left (&optional arg)
  "Dedent statement by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "statement" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-top-level-right (&optional arg)
  "Indent top-level by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "top-level" (or arg py-indent-offset))))
        (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-shift-top-level-left (&optional arg)
  "Dedent top-level by COUNT spaces.

COUNT defaults to `py-indent-offset',
use \[universal-argument] to specify a different value.

Returns outmost indentation reached. "
  (interactive "*P")
  (let ((erg (py--shift-forms-base "top-level" (- (or arg py-indent-offset)))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

;; python-components-execute-file

;;  Execute file commands

(defun py-execute-file-python (&optional filename)
  "Send file to Python default interpreter."
  (interactive "fFile: ")
  (py--execute-prepare filename "python" nil nil nil nil t))

(defun py-execute-file-python-switch (&optional filename)
  "Send file to Python default interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python" nil 'switch nil nil t))

(defun py-execute-file-python-no-switch (&optional filename)
  "Send file to Python default interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python" nil 'no-switch nil nil t))

(defun py-execute-file-python-dedicated (&optional filename)
  "Send file to Python default interpreter.

Uses a dedicated shell."
  (interactive "fFile: ")
  (py--execute-prepare filename "python" 'dedicated nil nil nil t))

(defun py-execute-file-python-dedicated-switch (&optional filename)
  "Send file to Python default interpreter.

Uses a dedicated shell.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python" 'dedicated 'switch nil nil t))

(defun py-execute-file-ipython (&optional filename)
  "Send file to a Ipython interpreter."
  (interactive "fFile: ")
  (py--execute-prepare filename "ipython" nil nil nil nil t))

(defun py-execute-file-ipython-switch (&optional filename)
  "Send file to a Ipython interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "ipython" nil 'switch nil nil t))

(defun py-execute-file-ipython-no-switch (&optional filename)
  "Send file to a Ipython interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "ipython" nil 'no-switch nil nil t))

(defun py-execute-file-ipython-dedicated (&optional filename)
  "Send file to a Ipython interpreter.

Uses a dedicated shell."
  (interactive "fFile: ")
  (py--execute-prepare filename "ipython" 'dedicated nil nil nil t))

(defun py-execute-file-ipython-dedicated-switch (&optional filename)
  "Send file to a Ipython interpreter.

Uses a dedicated shell.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "ipython" 'dedicated 'switch nil nil t))

(defun py-execute-file-python3 (&optional filename)
  "Send file to a Python3 interpreter."
  (interactive "fFile: ")
  (py--execute-prepare filename "python3" nil nil nil nil t))

(defun py-execute-file-python3-switch (&optional filename)
  "Send file to a Python3 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3" nil 'switch nil nil t))

(defun py-execute-file-python3-no-switch (&optional filename)
  "Send file to a Python3 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3" nil 'no-switch nil nil t))

(defun py-execute-file-python3-dedicated (&optional filename)
  "Send file to a Python3 interpreter.

Uses a dedicated shell."
  (interactive "fFile: ")
  (py--execute-prepare filename "python3" 'dedicated nil nil nil t))

(defun py-execute-file-python3-dedicated-switch (&optional filename)
  "Send file to a Python3 interpreter.

Uses a dedicated shell.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3" 'dedicated 'switch nil nil t))

(defun py-execute-file-python2 (&optional filename)
  "Send file to a Python2 interpreter."
  (interactive "fFile: ")
  (py--execute-prepare filename "python2" nil nil nil nil t))

(defun py-execute-file-python2-switch (&optional filename)
  "Send file to a Python2 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python2" nil 'switch nil nil t))

(defun py-execute-file-python2-no-switch (&optional filename)
  "Send file to a Python2 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python2" nil 'no-switch nil nil t))

(defun py-execute-file-python2-dedicated (&optional filename)
  "Send file to a Python2 interpreter.

Uses a dedicated shell."
  (interactive "fFile: ")
  (py--execute-prepare filename "python2" 'dedicated nil nil nil t))

(defun py-execute-file-python2-dedicated-switch (&optional filename)
  "Send file to a Python2 interpreter.

Uses a dedicated shell.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python2" 'dedicated 'switch nil nil t))

(defun py-execute-file-python2.7 (&optional filename)
  "Send file to a Python2.7 interpreter."
  (interactive "fFile: ")
  (py--execute-prepare filename "python2.7" nil nil nil nil t))

(defun py-execute-file-python2.7-switch (&optional filename)
  "Send file to a Python2.7 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python2.7" nil 'switch nil nil t))

(defun py-execute-file-python2.7-no-switch (&optional filename)
  "Send file to a Python2.7 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python2.7" nil 'no-switch nil nil t))

(defun py-execute-file-python2.7-dedicated (&optional filename)
  "Send file to a Python2.7 interpreter.

Uses a dedicated shell."
  (interactive "fFile: ")
  (py--execute-prepare filename "python2.7" 'dedicated nil nil nil t))

(defun py-execute-file-python2.7-dedicated-switch (&optional filename)
  "Send file to a Python2.7 interpreter.

Uses a dedicated shell.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python2.7" 'dedicated 'switch nil nil t))

(defun py-execute-file-jython (&optional filename)
  "Send file to a Jython interpreter."
  (interactive "fFile: ")
  (py--execute-prepare filename "jython" nil nil nil nil t))

(defun py-execute-file-jython-switch (&optional filename)
  "Send file to a Jython interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "jython" nil 'switch nil nil t))

(defun py-execute-file-jython-no-switch (&optional filename)
  "Send file to a Jython interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "jython" nil 'no-switch nil nil t))

(defun py-execute-file-jython-dedicated (&optional filename)
  "Send file to a Jython interpreter.

Uses a dedicated shell."
  (interactive "fFile: ")
  (py--execute-prepare filename "jython" 'dedicated nil nil nil t))

(defun py-execute-file-jython-dedicated-switch (&optional filename)
  "Send file to a Jython interpreter.

Uses a dedicated shell.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "jython" 'dedicated 'switch nil nil t))

(defun py-execute-file-python3.2 (&optional filename)
  "Send file to a Python3.2 interpreter."
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.2" nil nil nil nil t))

(defun py-execute-file-python3.2-switch (&optional filename)
  "Send file to a Python3.2 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.2" nil 'switch nil nil t))

(defun py-execute-file-python3.2-no-switch (&optional filename)
  "Send file to a Python3.2 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.2" nil 'no-switch nil nil t))

(defun py-execute-file-python3.2-dedicated (&optional filename)
  "Send file to a Python3.2 interpreter.

Uses a dedicated shell."
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.2" 'dedicated nil nil nil t))

(defun py-execute-file-python3.2-dedicated-switch (&optional filename)
  "Send file to a Python3.2 interpreter.

Uses a dedicated shell.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.2" 'dedicated 'switch nil nil t))

(defun py-execute-file-python3.3 (&optional filename)
  "Send file to a Python3.3 interpreter."
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.3" nil nil nil nil t))

(defun py-execute-file-python3.3-switch (&optional filename)
  "Send file to a Python3.3 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.3" nil 'switch nil nil t))

(defun py-execute-file-python3.3-no-switch (&optional filename)
  "Send file to a Python3.3 interpreter.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.3" nil 'no-switch nil nil t))

(defun py-execute-file-python3.3-dedicated (&optional filename)
  "Send file to a Python3.3 interpreter.

Uses a dedicated shell."
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.3" 'dedicated nil nil nil t))

(defun py-execute-file-python3.3-dedicated-switch (&optional filename)
  "Send file to a Python3.3 interpreter.

Uses a dedicated shell.
Ignores default of `py-switch-buffers-on-execute-p', uses it with value \"non-nil\""
  (interactive "fFile: ")
  (py--execute-prepare filename "python3.3" 'dedicated 'switch nil nil t))

;; python-components-section-forms

(defun py-execute-section ()
  "Execute section at point."
  (interactive)
  (py-execute-section-prepare))

(defun py-execute-section-python ()
  "Execute section at point using python interpreter."
  (interactive)
  (py-execute-section-prepare "python"))

(defun py-execute-section-python2 ()
  "Execute section at point using python2 interpreter."
  (interactive)
  (py-execute-section-prepare "python2"))

(defun py-execute-section-python3 ()
  "Execute section at point using python3 interpreter."
  (interactive)
  (py-execute-section-prepare "python3"))

(defun py-execute-section-ipython ()
  "Execute section at point using ipython interpreter."
  (interactive)
  (py-execute-section-prepare "ipython"))

(defun py-execute-section-ipython2.7 ()
  "Execute section at point using ipython2.7 interpreter."
  (interactive)
  (py-execute-section-prepare "ipython2.7"))

(defun py-execute-section-ipython3 ()
  "Execute section at point using ipython3 interpreter."
  (interactive)
  (py-execute-section-prepare "ipython3"))

(defun py-execute-section-jython ()
  "Execute section at point using jython interpreter."
  (interactive)
  (py-execute-section-prepare "jython"))

;; python-components-comment


(defun py-comment-region (beg end &optional arg)
  "Like ‘comment-region’ but uses double hash (‘#’) comment starter."
  (interactive "r\nP")
  (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start)))
    (comment-region beg end arg)))

(defun py-comment-block (&optional beg end arg)
  "Comments block at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-block-position)))
          (end (or end (py-end-of-block-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-block-or-clause (&optional beg end arg)
  "Comments block-or-clause at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-block-or-clause-position)))
          (end (or end (py-end-of-block-or-clause-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-class (&optional beg end arg)
  "Comments class at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-class-position)))
          (end (or end (py-end-of-class-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-clause (&optional beg end arg)
  "Comments clause at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-clause-position)))
          (end (or end (py-end-of-clause-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-def (&optional beg end arg)
  "Comments def at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-def-position)))
          (end (or end (py-end-of-def-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-def-or-class (&optional beg end arg)
  "Comments def-or-class at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-def-or-class-position)))
          (end (or end (py-end-of-def-or-class-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-indent (&optional beg end arg)
  "Comments indent at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-indent-position)))
          (end (or end (py-end-of-indent-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-minor-block (&optional beg end arg)
  "Comments minor-block at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-minor-block-position)))
          (end (or end (py-end-of-minor-block-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-section (&optional beg end arg)
  "Comments section at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-section-position)))
          (end (or end (py-end-of-section-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-statement (&optional beg end arg)
  "Comments statement at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-statement-position)))
          (end (or end (py-end-of-statement-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))

(defun py-comment-top-level (&optional beg end arg)
  "Comments top-level at point.

Uses double hash (‘#’) comment starter when ‘py-block-comment-prefix-p’ is  t,
the default"
  (interactive "*")
  (save-excursion
    (let ((comment-start (if py-block-comment-prefix-p
                             py-block-comment-prefix
                           comment-start))
          (beg (or beg (py--beginning-of-top-level-position)))
          (end (or end (py-end-of-top-level-position))))
      (goto-char beg)
      (push-mark)
      (goto-char end)
      (comment-region beg end arg))))


;; python-components-comment ends here
;; python-components-forms-code


(defun py-block ()
  "Block at point.

Return code of ‘py-block’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "block")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-block-or-clause ()
  "Block-Or-Clause at point.

Return code of ‘py-block-or-clause’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "block-or-clause")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-buffer ()
  "Buffer at point.

Return code of ‘py-buffer’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "buffer")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-class ()
  "Class at point.

Return code of ‘py-class’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "class")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-clause ()
  "Clause at point.

Return code of ‘py-clause’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "clause")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-def ()
  "Def at point.

Return code of ‘py-def’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "def")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-def-or-class ()
  "Def-Or-Class at point.

Return code of ‘py-def-or-class’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "def-or-class")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-expression ()
  "Expression at point.

Return code of ‘py-expression’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "expression")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-indent ()
  "Indent at point.

Return code of ‘py-indent’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "indent")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-line ()
  "Line at point.

Return code of ‘py-line’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "line")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-minor-block ()
  "Minor-Block at point.

Return code of ‘py-minor-block’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "minor-block")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-paragraph ()
  "Paragraph at point.

Return code of ‘py-paragraph’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "paragraph")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-partial-expression ()
  "Partial-Expression at point.

Return code of ‘py-partial-expression’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "partial-expression")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-region ()
  "Region at point.

Return code of ‘py-region’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "region")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-statement ()
  "Statement at point.

Return code of ‘py-statement’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "statement")))
    (py--forms-report-result erg (called-interactively-p 'any))))

(defun py-top-level ()
  "Top-Level at point.

Return code of ‘py-top-level’ at point, a string."
  (interactive)
  (let ((erg (py--mark-base "top-level")))
    (py--forms-report-result erg (called-interactively-p 'any))))

;; python-components-forms-code.el ends here
;; python-components-fast-forms

;; Process forms fast



(defun py--filter-result (strg)
  "Set `py-result' according to `py-fast-filter-re'.

Remove trailing newline"
  ;; (replace-regexp-in-string (format "[ \n]*%s[ \n]*" py-fast-filter-re) ""
  (ansi-color-filter-apply strg)
  ;;)
  )

(defun py-fast-process (&optional buffer)
  "Connect am (I)Python process suitable for large output.

Output buffer displays \"Fast\"  by default
It is not in interactive, i.e. comint-mode, as its bookkeepings seem linked to the freeze reported by lp:1253907"
  (interactive)
  (let ((this-buffer
         (set-buffer (or (and buffer (get-buffer-create buffer))
                         (get-buffer-create py-buffer-name)))))
    (let ((proc (start-process py-shell-name this-buffer py-shell-name)))
      (with-current-buffer this-buffer
        (erase-buffer))
      proc)))

(defun py--fast-send-string-intern (strg proc output-buffer return)
  (with-current-buffer output-buffer
    (process-send-string proc "\n")
    (let ((orig (point)))
      (process-send-string proc strg)
      (process-send-string proc "\n")
      (accept-process-output proc 5)
      (sit-for py-fast-completion-delay t)
      (when return
	(setq py-result (py--filter-result (py--fetch-result orig))))
	py-result)))

(defun py--fast-send-string (strg)
  "Process Python strings, being prepared for large output.

Output buffer displays \"Fast\"  by default
See also `py-fast-shell'

"
  (let ((proc (or (get-buffer-process (get-buffer py-fast-output-buffer))
                  (py-fast-process))))
    ;;    (with-current-buffer py-fast-output-buffer
    ;;      (erase-buffer))
    (process-send-string proc strg)
    (or (string-match "\n$" strg)
        (process-send-string proc "\n"))
    (accept-process-output proc 1)
    (set-buffer py-fast-output-buffer)
    (beginning-of-line)
    (skip-chars-backward "\r\n")
    (delete-region (point) (point-max))))


(defun py--fast-send-string-no-output (strg proc output-buffer)
  (with-current-buffer output-buffer
    (process-send-string proc "\n")
    (let ((orig (point-max)))
      (sit-for 1 t)
      (process-send-string proc strg)
      (process-send-string proc "\n")
      (accept-process-output proc 5)
      (sit-for 1 t)
      (delete-region orig (point-max)))))

(defun py-process-region-fast (beg end)
  (interactive "r")
  (let ((py-fast-process-p t))
    (py-execute-region beg end)))

(defun py-execute-block-fast (&optional shell dedicated switch beg end file)
  "Process block at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'block shell dedicated switch beg end file t))

(defun py-execute-block-or-clause-fast (&optional shell dedicated switch beg end file)
  "Process block-or-clause at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'block-or-clause shell dedicated switch beg end file t))

(defun py-execute-class-fast (&optional shell dedicated switch beg end file)
  "Process class at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'class shell dedicated switch beg end file t))

(defun py-execute-clause-fast (&optional shell dedicated switch beg end file)
  "Process clause at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'clause shell dedicated switch beg end file t))

(defun py-execute-def-fast (&optional shell dedicated switch beg end file)
  "Process def at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'def shell dedicated switch beg end file t))

(defun py-execute-def-or-class-fast (&optional shell dedicated switch beg end file)
  "Process def-or-class at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'def-or-class shell dedicated switch beg end file t))

(defun py-execute-expression-fast (&optional shell dedicated switch beg end file)
  "Process expression at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'expression shell dedicated switch beg end file t))

(defun py-execute-partial-expression-fast (&optional shell dedicated switch beg end file)
  "Process partial-expression at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'partial-expression shell dedicated switch beg end file t))

(defun py-execute-section-fast (&optional shell dedicated switch beg end file)
  "Process section at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'section shell dedicated switch beg end file t))

(defun py-execute-statement-fast (&optional shell dedicated switch beg end file)
  "Process statement at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'statement shell dedicated switch beg end file t))

(defun py-execute-top-level-fast (&optional shell dedicated switch beg end file)
  "Process top-level at point by a Python interpreter.

Suitable for large output, doesn't mess up interactive shell.
Output buffer not in comint-mode, displays \"Fast\"  by default"
  (interactive)
  (py--execute-prepare 'top-level shell dedicated switch beg end file t))

;; python-components-narrow

(defun py-narrow-to-block ()
  "Narrow to block at point."
  (interactive)
  (py--narrow-prepare "block"))

(defun py-narrow-to-block-or-clause ()
  "Narrow to block-or-clause at point."
  (interactive)
  (py--narrow-prepare "block-or-clause"))

(defun py-narrow-to-class ()
  "Narrow to class at point."
  (interactive)
  (py--narrow-prepare "class"))

(defun py-narrow-to-clause ()
  "Narrow to clause at point."
  (interactive)
  (py--narrow-prepare "clause"))

(defun py-narrow-to-def ()
  "Narrow to def at point."
  (interactive)
  (py--narrow-prepare "def"))

(defun py-narrow-to-def-or-class ()
  "Narrow to def-or-class at point."
  (interactive)
  (py--narrow-prepare "def-or-class"))

(defun py-narrow-to-statement ()
  "Narrow to statement at point."
  (interactive)
  (py--narrow-prepare "statement"))

;; python-components-auto-fill

(defvar py-auto-fill-mode-orig (auto-fill-mode)
  "Store the original state of auto-fill-mode. ")

;; py-fill-column-orig  already defined

(defun py-comment-auto-fill (&optional arg) 
  "Toggles comment-auto-fill mode"
  (interactive "P")
  (if (or (and arg (< 0 (prefix-numeric-value arg))) (and (boundp 'py-comment-auto-fill)(not py-comment-auto-fill)))
      (progn
        (set (make-local-variable 'py-comment-auto-fill-p) t)
        (setq fill-column comment-fill-column)
        (auto-fill-mode 1))
    (set (make-local-variable 'py-comment-auto-fill-p) nil)
;;    (set (make-local-variable 'py-comment-auto-fill-only-comments) nil)
    ;; (setq fill-column fill-column-orig)
    (auto-fill-mode -1)))

(defun py-comment-auto-fill-on ()
  (interactive)
  (py-comment-auto-fill 1))

(defun py-comment-auto-fill-off ()
  (interactive)
  (py-comment-auto-fill -1))

;; python-components-hide-show


;; (setq hs-block-start-regexp 'py-extended-block-or-clause-re)
;; (setq hs-forward-sexp-func 'py-forward-block)

(defun py-hide-base (form &optional beg end)
  "Hide visibility of existing form at point."
  (hs-minor-mode 1)
  (save-excursion
    (let* ((form (prin1-to-string form))
           (beg (or beg (or (funcall (intern-soft (concat "py--beginning-of-" form "-p")))
                            (funcall (intern-soft (concat "py-backward-" form))))))
           (end (or end (funcall (intern-soft (concat "py-forward-" form)))))
           (modified (buffer-modified-p))
           (inhibit-read-only t))
      (if (and beg end)
          (progn
            (hs-make-overlay beg end 'code)
            (set-buffer-modified-p modified))
        (error (concat "No " (format "%s" form) " at point"))))))

(defun py-show-base (form &optional beg end)
  "Remove invisibility of existing form at point."
  (save-excursion
    (let* ((form (prin1-to-string form))
           (beg (or beg (or (funcall (intern-soft (concat "py--beginning-of-" form "-p")))
                            (funcall (intern-soft (concat "py-backward-" form))))))
           (end (or end (funcall (intern-soft (concat "py-forward-" form)))))
           (modified (buffer-modified-p))
           (inhibit-read-only t))
      (if (and beg end)
          (progn
            (hs-discard-overlays beg end)
            (set-buffer-modified-p modified))
        (error (concat "No " (format "%s" form) " at point"))))))

(defun py-hide-show (&optional form beg end)
  "Toggle visibility of existing forms at point."
  (interactive)
  (save-excursion
    (let* ((form (prin1-to-string form))
           (beg (or beg (or (funcall (intern-soft (concat "py--beginning-of-" form "-p")))
                            (funcall (intern-soft (concat "py-backward-" form))))))
           (end (or end (funcall (intern-soft (concat "py-forward-" form)))))
           (modified (buffer-modified-p))
           (inhibit-read-only t))
      (if (and beg end)
          (if (overlays-in beg end)
              (hs-discard-overlays beg end)
            (hs-make-overlay beg end 'code))
        (error (concat "No " (format "%s" form) " at point")))
      (set-buffer-modified-p modified))))

(defun py-hide-region (beg end)
  "Hide active region."
  (interactive
   (list
    (and (use-region-p) (region-beginning))(and (use-region-p) (region-end))))
  (py-hide-base 'region beg end))

(defun py-show-region (beg end)
  "Un-hide active region."
  (interactive
   (list
    (and (use-region-p) (region-beginning))(and (use-region-p) (region-end))))
  (py-show-base 'region beg end))

(defun py-hide-block ()
  "Hide block at point."
  (interactive)
  (py-hide-base 'block))

(defun py-show-block ()
  "Show block at point."
  (interactive)
  (py-show-base 'block))

(defun py-hide-block-or-clause ()
  "Hide block-or-clause at point."
  (interactive)
  (py-hide-base 'block-or-clause))

(defun py-show-block-or-clause ()
  "Show block-or-clause at point."
  (interactive)
  (py-show-base 'block-or-clause))

(defun py-hide-class ()
  "Hide class at point."
  (interactive)
  (py-hide-base 'class))

(defun py-show-class ()
  "Show class at point."
  (interactive)
  (py-show-base 'class))

(defun py-hide-clause ()
  "Hide clause at point."
  (interactive)
  (py-hide-base 'clause))

(defun py-show-clause ()
  "Show clause at point."
  (interactive)
  (py-show-base 'clause))

(defun py-hide-comment ()
  "Hide comment at point."
  (interactive)
  (py-hide-base 'comment))

(defun py-show-comment ()
  "Show comment at point."
  (interactive)
  (py-show-base 'comment))

(defun py-hide-def ()
  "Hide def at point."
  (interactive)
  (py-hide-base 'def))

(defun py-show-def ()
  "Show def at point."
  (interactive)
  (py-show-base 'def))

(defun py-hide-def-or-class ()
  "Hide def-or-class at point."
  (interactive)
  (py-hide-base 'def-or-class))

(defun py-show-def-or-class ()
  "Show def-or-class at point."
  (interactive)
  (py-show-base 'def-or-class))

(defun py-hide-elif-block ()
  "Hide elif-block at point."
  (interactive)
  (py-hide-base 'elif-block))

(defun py-show-elif-block ()
  "Show elif-block at point."
  (interactive)
  (py-show-base 'elif-block))

(defun py-hide-else-block ()
  "Hide else-block at point."
  (interactive)
  (py-hide-base 'else-block))

(defun py-show-else-block ()
  "Show else-block at point."
  (interactive)
  (py-show-base 'else-block))

(defun py-hide-except-block ()
  "Hide except-block at point."
  (interactive)
  (py-hide-base 'except-block))

(defun py-show-except-block ()
  "Show except-block at point."
  (interactive)
  (py-show-base 'except-block))

(defun py-hide-expression ()
  "Hide expression at point."
  (interactive)
  (py-hide-base 'expression))

(defun py-show-expression ()
  "Show expression at point."
  (interactive)
  (py-show-base 'expression))

(defun py-hide-for-block ()
  "Hide for-block at point."
  (interactive)
  (py-hide-base 'for-block))

(defun py-show-for-block ()
  "Show for-block at point."
  (interactive)
  (py-show-base 'for-block))

(defun py-hide-if-block ()
  "Hide if-block at point."
  (interactive)
  (py-hide-base 'if-block))

(defun py-show-if-block ()
  "Show if-block at point."
  (interactive)
  (py-show-base 'if-block))

(defun py-hide-indent ()
  "Hide indent at point."
  (interactive)
  (py-hide-base 'indent))

(defun py-show-indent ()
  "Show indent at point."
  (interactive)
  (py-show-base 'indent))

(defun py-hide-line ()
  "Hide line at point."
  (interactive)
  (py-hide-base 'line))

(defun py-show-line ()
  "Show line at point."
  (interactive)
  (py-show-base 'line))

(defun py-hide-minor-block ()
  "Hide minor-block at point."
  (interactive)
  (py-hide-base 'minor-block))

(defun py-show-minor-block ()
  "Show minor-block at point."
  (interactive)
  (py-show-base 'minor-block))

(defun py-hide-paragraph ()
  "Hide paragraph at point."
  (interactive)
  (py-hide-base 'paragraph))

(defun py-show-paragraph ()
  "Show paragraph at point."
  (interactive)
  (py-show-base 'paragraph))

(defun py-hide-partial-expression ()
  "Hide partial-expression at point."
  (interactive)
  (py-hide-base 'partial-expression))

(defun py-show-partial-expression ()
  "Show partial-expression at point."
  (interactive)
  (py-show-base 'partial-expression))

(defun py-hide-section ()
  "Hide section at point."
  (interactive)
  (py-hide-base 'section))

(defun py-show-section ()
  "Show section at point."
  (interactive)
  (py-show-base 'section))

(defun py-hide-statement ()
  "Hide statement at point."
  (interactive)
  (py-hide-base 'statement))

(defun py-show-statement ()
  "Show statement at point."
  (interactive)
  (py-show-base 'statement))

(defun py-hide-top-level ()
  "Hide top-level at point."
  (interactive)
  (py-hide-base 'top-level))

(defun py-show-top-level ()
  "Show top-level at point."
  (interactive)
  (py-show-base 'top-level))

;; python-components-hide-show.el ends here
;; python-components-fast-complete

(defun py--fast-completion-get-completions (input process completion-code)
  "Retrieve available completions for INPUT using PROCESS.
Argument COMPLETION-CODE is the python code used to get
completions on the current context."
  (let ((completions
	 (py--fast-send-string-intern
	  (format completion-code input) process py-buffer-name t)))
    (when (> (length completions) 2)
      (split-string completions "^'\\|^\"\\|;\\|'$\\|\"$" t))))

(defun py--fast--do-completion-at-point (process imports input orig code output-buffer)
  "Do completion at point for PROCESS."
  ;; send setup-code
  (let (py-store-result-p)
    (when imports
      ;; (message "%s" imports)
      (py--fast-send-string-no-output imports process output-buffer)))
  (let* ((completion
	  (py--fast-completion-get-completions input process code)))
    (cond ((eq completion t)
	   (and py-verbose-p (message "py--fast--do-completion-at-point %s" "`t' is returned, not completion. Might be a bug."))
	   nil)
	  ((null completion)
	   (and py-verbose-p (message "py--fast--do-completion-at-point %s" "Don't see a completion"))
	   nil)
	  ((and completion
		(or (and (listp completion)
			 (string= input (car completion)))
		    (and (stringp completion)
			 (string= input completion))))
	   nil)
	  ((and completion (stringp completion)(not (string= input completion)))
	   (progn (delete-char (- (length input)))
		  (insert completion)
		  ;; (move-marker orig (point))
		  ;; minibuffer.el expects a list
		  nil))
	  (t (py--try-completion input completion)))

    nil))

(defun py--fast-complete-base (shell pos word imports exception-buffer)
  (let* ((shell (or shell (py-choose-shell nil t)))
	 (py-buffer-name (py-shell nil nil shell nil t))
	 (proc (get-buffer-process py-buffer-name))
	 (code (if (string-match "[Ii][Pp]ython*" shell)
		   (py-set-ipython-completion-command-string shell)
		 py-shell-module-completion-code)))
    (with-current-buffer py-buffer-name
      (erase-buffer))
    (py--fast--do-completion-at-point proc imports word pos code py-buffer-name)))

(defun py-fast-complete (&optional shell debug beg end word)
  "Complete word before point, if any.

Use `py-fast-process' "
  (interactive)
  (setq py-last-window-configuration
        (current-window-configuration))
  (py--complete-prepare shell beg end word t))

;; python-components-intern

;;  Keymap

(defun py--beginning-of-form-intern (regexp &optional iact indent orig lc)
  "Go to beginning of FORM.

With INDENT, go to beginning one level above.
Whit IACT, print result in message buffer.

Returns beginning of FORM if successful, nil otherwise"
  (interactive "P")
  (let (erg)
    (unless (bobp)
      (let* ((orig (or orig (point)))
             (indent (or indent (progn
                                  (back-to-indentation)
                                  (or (py--beginning-of-statement-p)
                                      (ar-backward-statement))
                                  (current-indentation)))))
        (setq erg (cond ((and (< (point) orig) (looking-at (symbol-value regexp)))
                         (point))
                        ((and (eq 0 (current-column)) (numberp indent) (< 0 indent))
                         (when (< 0 (abs (skip-chars-backward " \t\r\n\f")))
                           (ar-backward-statement)
                           (unless (looking-at (symbol-value regexp))
                             (cdr (py--go-to-keyword (symbol-value regexp) (current-indentation))))))
                        ((numberp indent)
			 (cdr (py--go-to-keyword (symbol-value regexp) indent)))
                        (t (ignore-errors
                             (cdr (py--go-to-keyword (symbol-value regexp)
                                                    (- (progn (if (py--beginning-of-statement-p) (current-indentation) (save-excursion (ar-backward-statement) (current-indentation)))) py-indent-offset)))))))
        (when lc (beginning-of-line) (setq erg (point)))))
    erg))

(defun py--indent-prepare (inter-re)
  (progn (back-to-indentation)
	 (or (py--beginning-of-statement-p)
	     (ar-backward-statement))
	 (cond ((eq 0 (current-indentation))
		(current-indentation))
	       ((looking-at (symbol-value inter-re))
		(current-indentation))
	       (t
		(if (<= py-indent-offset (current-indentation))
		    (- (current-indentation) (if ar-smart-indentation (ar-guess-indent-offset) py-indent-offset))
		  py-indent-offset)))))

(defun py--beginning-of-prepare (indent final-re &optional inter-re iact lc)
  (let ((orig (point))
        (indent (or indent (py--indent-prepare inter-re)))
        erg)
    (if (and (< (point) orig) (looking-at (symbol-value final-re)))
        (progn
          (and lc (beginning-of-line))
          (setq erg (point))
          ;; (when (and ar-verbose-p iact) (message "%s" erg))
          erg)
      (py--beginning-of-form-intern final-re iact indent orig lc))))

(defun py--end-of-prepare (indent final-re &optional inter-re iact lc)
  (let ((orig (point))
        (indent
         (or indent
             (progn (back-to-indentation)
                    (or (py--beginning-of-statement-p)
                        (ar-backward-statement))
                    (cond ((eq 0 (current-indentation))
                           (current-indentation))
                          ((looking-at (symbol-value inter-re))
                           (current-indentation))
                          (t
                           (if (<= py-indent-offset (current-indentation))
                               (- (current-indentation) (if ar-smart-indentation (ar-guess-indent-offset) py-indent-offset))
                             py-indent-offset))))))
        erg)
    (if (and (< orig (point)) (looking-at (symbol-value final-re)))
        (progn
          (and lc (beginning-of-line))
          (setq erg (point))
          ;; (when (and ar-verbose-p iact) (message "%s" erg))
          erg)
      (py--beginning-of-form-intern final-re iact indent orig lc))))

(defun py-separator-char ()
  "Return the file-path separator char from current machine.

When `py-separator-char' is customized, its taken.
Returns char found. "
  (let ((erg (cond ((characterp py-separator-char)
                    (char-to-string py-separator-char))
                   ;; epd hack
                   ((and
                     (string-match "[Ii][Pp]ython" py-shell-name)
                     (string-match "epd\\|EPD" py-shell-name))
                    (replace-regexp-in-string "\n" ""
                                              (shell-command-to-string (concat py-shell-name " -c \"import os; print(os.sep)\"")))))))
    (if (and erg (string-match "^$" erg))
        (setq erg (substring erg (string-match "^$" erg)))
      (setq erg (replace-regexp-in-string "\n" "" (shell-command-to-string (concat py-shell-name " -W ignore" " -c \"import os; print(os.sep)\"")))))
    erg))

(defun pps-emacs-version ()
  "Include the appropriate `parse-partial-sexp' "
  (if (featurep 'xemacs)
      '(parse-partial-sexp (point-min) (point))
    '(parse-partial-sexp (point-min) (point))))

(defun py-in-comment-p ()
  "Return the beginning of current line's comment, if inside. "
  (interactive)
  (let* ((pps (parse-partial-sexp (point-min) (point)))
	 (erg (and (nth 4 pps) (nth 8 pps))))
    erg))
;;
(defun py-in-string-or-comment-p ()
  "Returns beginning position if inside a string or comment, nil otherwise. "
  (or (nth 8 (parse-partial-sexp (point-min) (point)))
      (when (or (looking-at "\"")(looking-at "[ \t]*#[ \t]*"))
        (point))))

(when py-org-cycle-p
  (define-key python-mode-map (kbd "<backtab>") 'org-cycle))

(defun py--buffer-filename-remote-maybe (&optional file-name)
  (let ((file-name (or file-name
		       (and
			(ignore-errors (file-readable-p (buffer-file-name)))
			(buffer-file-name)))))
    (if (and (featurep 'tramp) (tramp-tramp-file-p file-name))
	(tramp-file-name-localname
	 (tramp-dissect-file-name file-name))
      file-name)))

(defun py-forward-buffer ()
  "A complementary form used by auto-generated commands.

Returns position reached if successful"
  (interactive)
  (unless (eobp)
    (goto-char (point-max))))

(defun py-backward-buffer ()
  "A complementary form used by auto-generated commands.

Returns position reached if successful"
  (interactive)
  (unless (bobp)
    (goto-char (point-min))))

(defun py--execute-prepare (form &optional shell dedicated switch beg end file fast proc wholebuf split)
  "Used by python-components-extended-executes ."
  (save-excursion
    (let* ((form (prin1-to-string form))
	   (origline (py-count-lines))
	   (beg (unless file
                  (prog1
                      (or beg (funcall (intern-soft (concat "py--beginning-of-" form "-p")))

                          (funcall (intern-soft (concat "py-backward-" form)))
                          (push-mark)))))
           (end (unless file
                  (or end (funcall (intern-soft (concat "py-forward-" form))))))
           filename)
      (setq py-buffer-name nil)
      (if file
          (progn
            (setq filename (expand-file-name form))
            (if (file-readable-p filename)
                (py--execute-file-base nil filename nil nil origline)
              (message "%s not readable. %s" file "Do you have write permissions?")))
        (py--execute-base beg end shell filename proc file wholebuf fast dedicated split switch)))))

(defun py-load-skeletons ()
  "Load skeletons from extensions. "
  (interactive)
  (load (concat py-install-directory "/extensions/python-components-skeletons.el")))

(defun py--kill-emacs-hook ()
  "Delete files in `py-file-queue'.
These are Python temporary files awaiting execution."
  (mapc #'(lambda (filename)
            (ignore-errors (delete-file filename)))
        py-file-queue))

;;  Add a designator to the minor mode strings
(or (assq 'py-pdbtrack-is-tracking-p minor-mode-alist)
    (push '(py-pdbtrack-is-tracking-p py-pdbtrack-minor-mode-string)
          minor-mode-alist))

;;  bottle.py
;;  py   = sys.version_info
;;  py3k = py >= (3,0,0)
;;  py25 = py <  (2,6,0)
;;  py31 = (3,1,0) <= py < (3,2,0)

;;  sys.version_info[0]
(defun py-python-version (&optional executable verbose)
  "Returns versions number of a Python EXECUTABLE, string.

If no EXECUTABLE given, `py-shell-name' is used.
Interactively output of `--version' is displayed. "
  (interactive)
  (let* ((executable (or executable py-shell-name))
         (erg (py--string-strip (shell-command-to-string (concat executable " --version")))))
    (when (called-interactively-p 'any) (message "%s" erg))
    (unless verbose (setq erg (cadr (split-string erg))))
    erg))

(defun py-version ()
  "Echo the current version of `python-mode' in the minibuffer."
  (interactive)
  (message "Using `python-mode' version %s" py-version)
  (py-keep-region-active))

;;  Utility stuff
(declare-function compilation-shell-minor-mode "compile" (&optional arg))

;; dereived from shipped python.el
(defun py-history-input-filter (str)
  "`comint-input-filter' function for Python process.
Don't save anything for STR matching `py-history-filter-regexp'."
  (not (string-match py-history-filter-regexp str)))

(defun py-load-file (file-name)
  "Load a Python file FILE-NAME into the Python process.

If the file has extension `.py' import or reload it as a module.
Treating it as a module keeps the global namespace clean, provides
function location information for debugging, and supports users of
module-qualified names."
  (interactive "f")
  (py--execute-file-base (get-buffer-process (get-buffer (py-shell))) file-name))

(defun py-proc (&optional argprompt)
  "Return the current Python process.

Start a new process if necessary. "
  (interactive "P")
  (let ((erg
         (cond ((comint-check-proc (current-buffer))
		(get-buffer-process (buffer-name (current-buffer))))
	       (t (py-shell argprompt)))))
    ;; (when (called-interactively-p 'any) (message "%S" erg))
    erg))

;;  Miscellany.
(defun py--shell-simple-send (proc strg)
  (let* ((strg (substring-no-properties strg))
         (nln (string-match "\n$" strg)))
    ;; (or nln (setq strg (concat strg "\n")))
    ;; (comint-simple-send proc (substring-no-properties strg))
    (process-send-string proc strg)
    (or nln (process-send-string proc "\n"))))

(defalias
  'py-shell-redirect-send-command-to-process
  'comint-redirect-send-command-to-process)
(defalias
  'py-shell-dynamic-simple-complete
  'comint-dynamic-simple-complete)

;;  Hooks
;;  arrange to kill temp files when Emacs exists
(add-hook 'kill-emacs-hook 'py--kill-emacs-hook)

(when py--warn-tmp-files-left-p
  (add-hook 'python-mode-hook 'py--warn-tmp-files-left))


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
        (message "%s" erg)
      (message "%s" "pdb.py not found, please customize `py-pdb-path'"))
    erg))

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

;;  backward compatibility
(defalias 'py-switch-shells 'py-switch-shell)
(defalias 'py-toggle-shell 'py-switch-shell)
(defun py-switch-shell (&optional arg)
  "Toggles between the interpreter customized in `py-shell-toggle-1' resp. `py-shell-toggle-2'. Was hard-coded CPython and Jython in earlier versions, now starts with Python2 and Python3 by default.

ARG might be a python-version string to set to.

\\[universal-argument] `py-toggle-shell' prompts to specify a reachable Python command.
\\[universal-argument] followed by numerical arg 2 or 3, `py-toggle-shell' opens a respective Python shell.
\\[universal-argument] followed by numerical arg 5 opens a Jython shell.

Should you need more shells to select, extend this command by adding inside the first cond:

                    ((eq NUMBER (prefix-numeric-value arg))
                     \"MY-PATH-TO-SHELL\")"
  (interactive "P")
  (let ((name (cond ((eq 2 (prefix-numeric-value arg))
                     "python2")
                    ((eq 3 (prefix-numeric-value arg))
                     "python3")
                    ((eq 4 (prefix-numeric-value arg))
                     (py--string-strip
                      (read-from-minibuffer "Python Shell: " py-shell-name) "\" " "\" "
                      ))
                    ((eq 5 (prefix-numeric-value arg))
                     "jython")
                    (t (if (string-match py-shell-name
                                         py-shell-toggle-1)
                           py-shell-toggle-2
                         py-shell-toggle-1))))
        erg msg)
    (cond ((or (string= "ipython" name)
               (string= "IPython" name))
           (setq py-shell-name name
                 py-which-bufname "IPython"
                 msg "IPython"
                 mode-name "IPython"))
          ((string-match "python3" name)
           (setq py-shell-name name
                 py-which-bufname (py--choose-buffer-name)
                 msg "CPython"
                 mode-name (py--choose-buffer-name)))
          ((string-match "jython" name)
           (setq py-shell-name name
                 py-which-bufname (py--choose-buffer-name)
                 msg "Jython"
                 mode-name (py--choose-buffer-name)))
          ((string-match "python" name)
           (setq py-shell-name name
                 py-which-bufname (py--choose-buffer-name)
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
          (when (called-interactively-p 'any)
            (message "Using the %s shell, %s" msg erg))
          (setq py-output-buffer (format "*%s Output*" py-which-bufname)))
      (error (concat "Could not detect " py-shell-name " on your sys
tem")))))

(defun py-toggle-local-default-use ()
  (interactive)
  "Toggle boolean value of `py-use-local-default'.

Returns `py-use-local-default'

See also `py-install-local-shells'
Installing named virualenv shells is the preffered way,
as it leaves your system default unchanged."
  (setq py-use-local-default (not py-use-local-default))
  (when (called-interactively-p 'any) (message "py-use-local-default set to %s" py-use-local-default))
  py-use-local-default)

(defalias 'py-hungry-delete-forward 'c-hungry-delete-forward)
(defalias 'py-hungry-delete-backwards 'c-hungry-delete-backwards)

;;  FixMe: for unknown reasons this is not done by mode
(if (file-readable-p abbrev-file-name)
    (add-hook 'python-mode-hook
              (lambda ()
                (setq py-this-abbrevs-changed abbrevs-changed)
                (load abbrev-file-name nil t)
                (setq abbrevs-changed py-this-abbrevs-changed)))
  (message "Warning: %s" "no abbrev-file found, customize `abbrev-file-name' in order to make mode-specific abbrevs work. "))

;; ;
(push (list
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
              (lambda ()
                (py-forward-block-or-clause))
              nil) hs-special-modes-alist)

;; ;

(defun py--input-filter (str)
  "`comint-input-filter' function for Python.

Don't save anything for STR matching `py-input-filter-re' "
  (not (string-match py-input-filter-re str)))

(make-obsolete 'jpython-mode 'jython-mode nil)

(push (purecopy "*Python*")  same-window-buffer-names)
(push (purecopy "*IPython*")  same-window-buffer-names)

(push (cons (purecopy "\\.py\\'")  'python-mode)  auto-mode-alist)

;; Python Macro File

(unless (member '(".pym'" . python-mode) auto-mode-alist)
  (push (cons (purecopy "\\.pym\\'")  'python-mode)  auto-mode-alist))

(unless (member '(".pyc'" . python-mode)  auto-mode-alist)
  (push (cons (purecopy "\\.pyc\\'")  'python-mode)  auto-mode-alist))

;; Pyrex Source
(unless (member '(".pyx'" . python-mode)  auto-mode-alist)
  (push (cons (purecopy "\\.pyx\\'")  'python-mode) auto-mode-alist))

;; Python Optimized Code
(unless (member '(".pyo'" . python-mode)  auto-mode-alist)
  (push (cons (purecopy "\\.pyo\\'")  'python-mode) auto-mode-alist))

;; Pyrex Definition File
(unless (member '(".pxd'" . python-mode)  auto-mode-alist)
  (push (cons (purecopy "\\.pxd\\'")  'python-mode) auto-mode-alist))

;; Python Repository
(unless (member '(".pyr'" . python-mode)  auto-mode-alist)
  (push (cons (purecopy "\\.pyr\\'")  'python-mode)  auto-mode-alist))

;; Python Stub file
;; https://www.python.org/dev/peps/pep-0484/#stub-files
(unless (member '(".pyi'" . python-mode)  auto-mode-alist)
  (push (cons (purecopy "\\.pyi\\'")  'python-mode)  auto-mode-alist))

;; Python Path Configuration
(unless (member '(".pth'" . python-mode)  auto-mode-alist)
  (push (cons (purecopy "\\.pth\\'")  'python-mode)  auto-mode-alist))

;; Python Wheels
(unless (member '(".whl'" . python-mode)  auto-mode-alist)
  (push (cons (purecopy "\\.whl\\'")  'python-mode)  auto-mode-alist))

(unless (member '("!#[ 	]*/.*[jp]ython[0-9.]*" . python-mode) magic-mode-alist)
  (push '("!#[ \\t]*/.*[jp]ython[0-9.]*" . python-mode) magic-mode-alist))

;;  lp:1355458, what about using `magic-mode-alist'?

(defun py--uncomment-intern (beg end)
  (uncomment-region beg end)
  (when py-uncomment-indents-p
    (py-indent-region beg end)))

(defun py-uncomment (&optional beg)
  "Uncomment commented lines at point.

If region is active, restrict uncommenting at region "
  (interactive "*")
  (save-excursion
    (save-restriction
      (when (use-region-p)
        (narrow-to-region (region-beginning) (region-end)))
      (let* (last
             (beg (or beg (save-excursion
                            (while (and (py-beginning-of-comment) (setq last (point))(prog1 (forward-line -1)(end-of-line))))
                            last))))
        (and (py-forward-comment))
        (py--uncomment-intern beg (point))))))

(defun py--set-auto-fill-values ()
  "Internal use by `py--run-auto-fill-timer'"
  (let ((pps (parse-partial-sexp (point-min) (point))))
    (cond ((and (nth 4 pps)(numberp py-comment-fill-column))
           (setq fill-column py-comment-fill-column))
          ((and (nth 3 pps)(numberp py-docstring-fill-column))
           (set (make-local-variable 'fill-column) py-docstring-fill-column))
          (t (setq fill-column py-fill-column-orig)))))

(defun py--run-auto-fill-timer ()
  "Set fill-column to values of `py-docstring-fill-column' resp. to `py-comment-fill-column' according to environment. "
  (when py-auto-fill-mode
    (unless py-autofill-timer
      (setq py-autofill-timer
            (run-with-idle-timer
             py-autofill-timer-delay t
             'py--set-auto-fill-values)))))

;;  unconditional Hooks
;;  (orgstruct-mode 1)
(add-hook 'python-mode-hook
	  (lambda ()
	    (setq imenu-create-index-function py--imenu-create-index-function)
	    (setq indent-tabs-mode py-indent-tabs-mode)))

(remove-hook 'python-mode-hook 'python-setup-brm)

(defun py-complete-auto ()
  "Auto-complete function using py-complete. "
  ;; disable company
  ;; (when company-mode (company-mode))
  (let ((modified (buffer-chars-modified-tick)))
    ;; don't try completion if buffer wasn't modified
    (unless (eq modified py-complete-last-modified)
      (if py-auto-completion-mode-p
	  (if (string= "*PythonCompletions*" (buffer-name (current-buffer)))
	      (sit-for 0.1 t)
	    (if
		(eq py-auto-completion-buffer (current-buffer))
		;; not after whitespace, TAB or newline
		(unless (member (char-before) (list 32 9 10))
		  (py-complete)
		  (setq py-complete-last-modified (buffer-chars-modified-tick)))
	      (setq py-auto-completion-mode-p nil
		    py-auto-completion-buffer nil)
	      (cancel-timer py--auto-complete-timer)))))))

(defun py-set-command-args (arguments)
  "Set Python arguments on the fly, override defaults in this session.

Use `defcustom' to keep value across sessions "
  (interactive
   (list
    (read-from-minibuffer "Command args: " py-python-command-args)))
    (setq py-python-command-args arguments))

(defun py---emacs-version-greater-23 ()
  "Return `t' if emacs major version is above 23"
  (< 23 (string-to-number (car (split-string emacs-version "\\.")))))

(defun py--empty-arglist-indent (nesting &optional indent-offset indent-offset)
  "Internally used by `py-compute-indentation'"
  (if
      (and (eq 1 nesting)
           (save-excursion
             (back-to-indentation)
             (looking-at py-extended-block-or-clause-re)))
      (progn
        (back-to-indentation)
        (+ (current-column) (* 2 (or indent-offset py-indent-offset))))
    (+ (current-indentation) (or indent-offset py-indent-offset))))

(defun py-symbol-at-point ()
  "Return the current Python symbol."
  (interactive)
  (let ((erg (with-syntax-table
                 py-dotted-expression-syntax-table
               (current-word))))
    ;; (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py-kill-buffer-unconditional (buffer)
  "Kill buffer unconditional, kill buffer-process if existing. "
  (interactive
   (list (current-buffer)))
  (let ((buffer (or (and (bufferp buffer) buffer)
		    (get-buffer buffer)))
	proc kill-buffer-query-functions)

    (ignore-errors
      (setq proc (get-buffer-process buffer))
      (and proc (kill-process proc))
      (set-buffer buffer)
      (set-buffer-modified-p 'nil)
      (kill-buffer (current-buffer)))))

(defun py--line-backward-maybe ()
  "Return result of (< 0 (abs (skip-chars-backward \" \\t\\r\\n\\f\"))) "
  (skip-chars-backward " \t\f" (line-beginning-position))
  (< 0 (abs (skip-chars-backward " \t\r\n\f"))))

(defun py--after-empty-line ()
  "Return `t' if line before contains only whitespace characters. "
  (save-excursion
    (beginning-of-line)
    (forward-line -1)
    (beginning-of-line)
    (looking-at "\\s-*$")))

(defalias 'py-count-indentation 'py-compute-indentation)
(defun py-compute-indentation (&optional iact orig origline closing line nesting repeat indent-offset liep)
  "Compute Python indentation.

When HONOR-BLOCK-CLOSE-P is non-nil, statements such as `return',
`raise', `break', `continue', and `pass' force one level of dedenting.

Optional arguments are flags resp. values set and used by `py-compute-indentation' internally:
ORIG keeps original position
ORIGLINE keeps line where compute started
CLOSING is t when started at a char delimiting a list as \"]})\"
LINE indicates being not at origline now
NESTING is currently ignored, if executing from inside a list
REPEAT counter enables checks against `py-max-specpdl-size'
INDENT-OFFSET allows calculation of block-local values
LIEP stores line-end-position at point-of-interest
"
  (interactive "p")
  (save-excursion
    (save-restriction
      (widen)
      ;; in shell, narrow from previous prompt
      ;; needed by closing
      (unless orig (unless (bobp) (back-to-indentation)))
      (let* ((orig (or orig (point)))
             (origline (or origline (py-count-lines (point-min) (point))))
             ;; closing indicates: when started, looked
             ;; at a single closing parenthesis
             ;; line: moved already a line backward
             (liep (or liep (line-end-position)))
             (line line)
	     (verbose py-verbose-p)
             (pps (parse-partial-sexp (point-min) (point)))
             (closing
              (or closing
                  (and (nth 1 pps)
                       (looking-at ".*\\(\\s)\\)")(nth 0 pps)
                       ;; char doesn't matter for now, maybe drop
                       (string-to-char (match-string-no-properties 1)))))
             ;; in a recursive call already
             (repeat (if repeat
			 (setq repeat (1+ repeat))
		       0))
             ;; nesting: started nesting a list
             (nesting nesting)
             (cubuf (current-buffer))
             erg indent this-line)
        (if (and (< repeat 1)
                 (and (comint-check-proc (current-buffer))
                      (re-search-backward (concat py-shell-prompt-regexp "\\|" py-ipython-output-prompt-re "\\|" py-ipython-input-prompt-re) nil t 1)))
            ;; common recursion not suitable because of prompt
            (with-temp-buffer
              (insert-buffer-substring cubuf (match-end 0) orig)
              (setq indent (py-compute-indentation)))
	  (if (< py-max-specpdl-size repeat)
	      (error "`py-compute-indentation' reached loops max.")	(setq nesting (nth 0 pps))
	      (setq indent
		    (cond ((bobp)
			   (cond ((eq liep (line-end-position))
				  0)
				 ((looking-at py-outdent-re)
				  (+ (or indent-offset (and py-smart-indentation (py-guess-indent-offset)) py-indent-offset) (current-indentation)))
				 (t
				  (current-indentation))))
			  ;; in string
			  ((and (nth 3 pps)(nth 8 pps))
			   (cond
			    ((py--docstring-p (nth 8 pps))
			     (save-excursion
			       (back-to-indentation)
			       (skip-chars-backward " \t\r\n\f")
			       (back-to-indentation)
			       (current-indentation)))
			    (t 0)))
			  ((and (looking-at "\"\"\"\\|'''")(not (bobp)))
			   (py-backward-statement)
			   (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
			  ;; comments
			  ((nth 8 pps)
			   (if (eq liep (line-end-position))
			       (progn
				 (goto-char (nth 8 pps))
				 (when (py--line-backward-maybe) (setq line t))
				 (skip-chars-backward " \t")
				 (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
			     (goto-char (nth 8 pps))
			     (if
				 line
				 (if py-indent-honors-inline-comment
				     (current-column)
				   (if py-indent-comments
				       (progn
					 (py-backward-comment)
					 (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
				     0))
			       (forward-char -1)
			       (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))))
			  ((and
			    (looking-at (concat "[ \t]*" comment-start))
			    (looking-back "^[ \t]*" (line-beginning-position))(not line)
			    (eq liep (line-end-position)))
			   (if py-indent-comments
			       (progn
				 (setq line t)
				 (skip-chars-backward " \t\r\n\f")
				 ;; as previous comment-line might
				 ;; be wrongly unindented, travel
				 ;; whole commented section
				 (py-backward-comment)
				 (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
			     0))
			  ((and
			    (looking-at (concat "[ \t]*" comment-start))
			    (looking-back "^[ \t]*" (line-beginning-position))
			    (not (eq liep (line-end-position))))
			   (current-indentation))
			  ((and (eq 11 (syntax-after (point))) line py-indent-honors-inline-comment)
			   (current-column))
			  ;; lists
			  ((nth 1 pps)
			   (save-excursion
			     (goto-char (nth 1 pps))
			     (setq this-line (py-count-lines))
			     (cond
			      ((< 0 (- origline this-line))
			       (if (< 1 (- origline this-line))
				   (cond
				    (closing
				     (cond
				      (py-closing-list-dedents-bos
				       (goto-char (nth 1 pps))
				       (current-indentation))
				      ((looking-back "^[ \t]*" (line-beginning-position))
				       (current-column))
				      ((and (looking-at "\\s([ \t]*$") py-closing-list-keeps-space)
				       (+ (current-column) py-closing-list-space))
				      ((looking-at "\\s([ \t]*$")
				       (py--empty-arglist-indent nesting py-indent-offset indent-offset))
				      ((looking-at "\\s([ \t]*\\([^ \t]+.*\\)$")
				       (goto-char (match-beginning 1))
				       (if py-indent-paren-spanned-multilines-p
					   (+ (current-column) (or indent-offset py-indent-offset))
					 (current-column)))
				      (t (py--fetch-previous-indent orig))))
				    ;; already behind a dedented element in list
				    ((<= 2 (- origline this-line))
				     (py--fetch-previous-indent orig))
				    ((< (current-indentation) (current-column))
				     (+ (current-indentation) (or indent-offset py-indent-offset)))
				    (t (py--fetch-previous-indent orig)))
				 (cond ((looking-at "\\s([ \t]*$")
					(py--empty-arglist-indent nesting py-indent-offset indent-offset))
				       ((looking-at "\\s([ \t]*\\([^ \t]+.*\\)$")
					(if
					    (and (or (bolp) (eq (char-before) 32)) py-indent-paren-spanned-multilines-p)
					    (progn
					      (goto-char (match-beginning 1))
					      (+ (current-column) (or indent-offset py-indent-offset)))
					  (goto-char (match-beginning 1))
					  (current-column)))
				       (t (+ (current-column) (* (nth 0 pps)))))))
			      ((nth 1 (parse-partial-sexp (point-min) (point)))
			       (goto-char (nth 1 (parse-partial-sexp (point-min) (point))))
			       (setq line
				     ;; should be faster
				     (< (line-end-position) liep))
			       (py-compute-indentation orig origline closing line nesting repeat indent-offset liep))
			      ((not (py--beginning-of-statement-p))
			       (py-backward-statement)
			       (py-compute-indentation orig origline closing line nesting repeat indent-offset liep))
			      (t (1+ (current-column))))))
			  ((and (eq (char-after) (or ?\( ?\{ ?\[)) line)
			   (1+ (current-column)))
			  ((py-preceding-line-backslashed-p)
			   (progn
			     (py-backward-statement)
			     (setq this-line (py-count-lines))
			     (if (< 1 (- origline this-line))
				 (py--fetch-previous-indent orig)
			       (if (looking-at "from +\\([^ \t\n]+\\) +import")
				   py-backslashed-lines-indent-offset
				 (+ (current-indentation) py-continuation-offset)))))
			  ((and (looking-at py-block-closing-keywords-re)
				(eq liep (line-end-position)))
			   (skip-chars-backward "[ \t\r\n\f]")
			   (py-backward-statement)
			   (cond ((looking-at py-extended-block-or-clause-re)
				  (+
				   ;; (if py-smart-indentation (py-guess-indent-offset) indent-offset)
				   (or indent-offset (and py-smart-indentation (py-guess-indent-offset)) py-indent-offset)
				   (current-indentation)))
				 ((looking-at py-block-closing-keywords-re)
				  (- (current-indentation) (or indent-offset py-indent-offset)))
				 (t (current-column))))
			  ((looking-at py-block-closing-keywords-re)
			   (if (< (line-end-position) orig)
			       (- (current-indentation) (or indent-offset py-indent-offset))
			     (py-backward-block-or-clause (current-indentation))
			     (current-indentation)))
			  ((and (looking-at py-elif-re) (eq (py-count-lines) origline))
			   (when (py--line-backward-maybe) (setq line t))
			   (car (py--clause-lookup-keyword py-elif-re -1 nil origline)))
			  ((and (looking-at py-clause-re)(not line)
				(eq liep (line-end-position)))
			   (cond ((looking-at py-finally-re)
				  (car (py--clause-lookup-keyword py-finally-re -1 nil origline)))
				 ((looking-at py-except-re)
				  (car (py--clause-lookup-keyword py-except-re -1 nil origline)))
				 ((looking-at py-else-block-re)
				  (car (py--clause-lookup-keyword py-else-block-re -1 nil origline)))
				 ((looking-at py-elif-block-re)
				  (car (py--clause-lookup-keyword py-elif-re -1 nil origline)))
				 ;; maybe at if, try, with
				 (t (car (py--clause-lookup-keyword py-block-or-clause-re -1 nil origline)))))
			  ((looking-at py-extended-block-or-clause-re)
			   (cond ((and (not line)
				       (eq liep (line-end-position)))
				  (when (py--line-backward-maybe) (setq line t))
				  (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
				 (t (+
				     (cond (indent-offset)
					   (py-smart-indentation
					    (py-guess-indent-offset))
					   (t py-indent-offset))
				     (current-indentation)))))
			  ((and
			    (< (line-end-position) liep)
			    (eq (current-column) (current-indentation)))
			   (and
			    (looking-at py-assignment-re)
			    (goto-char (match-end 0)))
			   ;; multiline-assignment
			   (if (and nesting (looking-at " *[[{(]")(not (looking-at ".+[]})][ \t]*$")))
			       (+ (current-indentation) (or indent-offset py-indent-offset))
			     (current-indentation)))
			  ((looking-at py-assignment-re)
			   (py-backward-statement)
			   (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
			  ((and (< (current-indentation) (current-column))(not line))
			   (back-to-indentation)
			   (unless line
			     (setq nesting (nth 0 (parse-partial-sexp (point-min) (point)))))
			   (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
			  ((and (not (py--beginning-of-statement-p)) (not (and line (eq 11 (syntax-after (point))))))
			   (if (bobp)
			       (current-column)
			     (if (eq (point) orig)
				 (progn
				   (when (py--line-backward-maybe) (setq line t))
				   (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
			       (py-backward-statement)
			       (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))))
			  ((or (py--statement-opens-block-p py-extended-block-or-clause-re)(looking-at "@"))
			   (if (< (py-count-lines) origline)
			       (+ (or indent-offset (and py-smart-indentation (py-guess-indent-offset)) py-indent-offset) (current-indentation))
			     (skip-chars-backward " \t\r\n\f")
			     (setq line t)
			     (back-to-indentation)
			     (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep)))
			  ((and py-empty-line-closes-p (py--after-empty-line))
			   (progn (py-backward-statement)
				  (- (current-indentation) (or indent-offset py-indent-offset))))
			  ;; still at orignial line
			  ((and (eq liep (line-end-position))
				(save-excursion
				  (and (setq erg (py--go-to-keyword py-extended-block-or-clause-re))
				       (if (and (not indent-offset) py-smart-indentation) (setq indent-offset (py-guess-indent-offset)) t)
				       (ignore-errors (< orig (or (py-forward-block-or-clause)(point)))))))
			   (+ (car erg) (if py-smart-indentation
					    (or indent-offset (py-guess-indent-offset))
					  (or indent-offset py-indent-offset))))
			  ((and (not line)
				(eq liep (line-end-position))
				(py--beginning-of-statement-p))
			   (py-backward-statement)
			   (py-compute-indentation iact orig origline closing line nesting repeat indent-offset liep))
			  (t (current-indentation))))
	      (when (and verbose iact) (message "%s" indent))
	      indent))))))

(defun py--fetch-previous-indent (orig)
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
  (and (numberp arg) (not (eq 1 arg)) (setq py-continuation-offset arg))
  (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" py-continuation-offset))
  py-continuation-offset)

(defalias 'pios 'py-indentation-of-statement)
(defalias 'ios 'py-indentation-of-statement)
(defun py-indentation-of-statement ()
  "Returns the indenation of the statement at point. "
  (interactive)
  (let ((erg (save-excursion
               (back-to-indentation)
               (or (py--beginning-of-statement-p)
                   (py-backward-statement))
               (current-indentation))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defalias 'py-in-list-p 'py-list-beginning-position)
(defun py-list-beginning-position (&optional start)
  "Return lists beginning position, nil if not inside.

Optional ARG indicates a start-position for `parse-partial-sexp'."
  (nth 1 (parse-partial-sexp (or start (point-min)) (point))))

(defun py-end-of-list-position (&optional arg)
  "Return end position, nil if not inside.

Optional ARG indicates a start-position for `parse-partial-sexp'."
  (interactive)
  (let* ((ppstart (or arg (point-min)))
         (erg (parse-partial-sexp ppstart (point)))
         (beg (nth 1 erg))
         end)
    (when beg
      (save-excursion
        (goto-char beg)
        (forward-list 1)
        (setq end (point))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" end))
    end))

(defun py--in-comment-p ()
  "Return the beginning of current line's comment, if inside. "
  (save-restriction
    (widen)
    (let* ((pps (parse-partial-sexp (point-min) (point)))
           (erg (when (nth 4 pps) (nth 8 pps))))
      (unless erg
        (when (looking-at (concat "^[ \t]*" comment-start-skip))
          (setq erg (point))))
      erg)))

(defun py-in-triplequoted-string-p ()
  "Returns character address of start tqs-string, nil if not inside. "
  (interactive)
  (let* ((pps (parse-partial-sexp (point-min) (point)))
         (erg (when (and (nth 3 pps) (nth 8 pps))(nth 2 pps))))
    (save-excursion
      (unless erg (setq erg
                        (progn
                          (when (looking-at "\"\"\"\\|''''")
                            (goto-char (match-end 0))
                            (setq pps (parse-partial-sexp (point-min) (point)))
                            (when (and (nth 3 pps) (nth 8 pps)) (nth 2 pps)))))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-in-string-p-intern (pps)
  (goto-char (nth 8 pps))
  (list (point) (char-after)(skip-chars-forward (char-to-string (char-after)))))

(defun py-in-string-p ()
  "if inside a double- triple- or singlequoted string,

If non-nil, return a list composed of
- beginning position
- the character used as string-delimiter (in decimal)
- and length of delimiter, commonly 1 or 3 "
  (interactive)
  (save-excursion
    (let* ((pps (parse-partial-sexp (point-min) (point)))
	   (erg (when (nth 3 pps)
		  (py-in-string-p-intern pps))))
      (unless erg
	(when (looking-at "\"\\|'")
	  (forward-char 1)
	  (setq pps (parse-partial-sexp (line-beginning-position) (point)))
	  (when (nth 3 pps)
	    (setq erg (py-in-string-p-intern pps)))))

    ;; (list (nth 8 pps) (char-before) (1+ (skip-chars-forward (char-to-string (char-before)))))
      ;; (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg)))

(defun py-in-statement-p ()
  "Returns list of beginning and end-position if inside.

Result is useful for booleans too: (when (py-in-statement-p)...)
will work.
"
  (interactive)
  (let ((orig (point))
        beg end erg)
    (save-excursion
      (setq end (py-forward-statement))
      (setq beg (py-backward-statement))
      (when (and (<= beg orig)(<= orig end))
        (setq erg (cons beg end))
        (when (called-interactively-p 'any) (message "%s" erg))
        erg))))

;;  Beginning-of- p
(defun py-backward-top-level-p ()
  "Returns position, if cursor is at the beginning of a top-level, nil otherwise. "
  (interactive)
  (let (erg)
    (and (py--beginning-of-statement-p)
         (eq 0 (current-column))
         (setq erg (point))
      erg)))

(defun py--beginning-of-buffer-p ()
  "Returns position, if cursor is at the beginning of buffer, nil otherwise. "
  (when (bobp)(point)))

;;  End-of- p

;;  Opens
(defun py--statement-opens-block-p (&optional regexp)
  "Return position if the current statement opens a block
in stricter or wider sense.

For stricter sense specify regexp. "
  (let* ((regexp (or regexp py-block-or-clause-re))
         (erg (py--statement-opens-base regexp)))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py--statement-opens-base (regexp)
  (let ((orig (point))
        erg)
    (save-excursion
      (back-to-indentation)
      (py-forward-statement)
      (py-backward-statement)
      (when (and
             (<= (line-beginning-position) orig)(looking-back "^[ \t]*" (line-beginning-position))(looking-at regexp))
        (setq erg (point))))
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))

(defun py--statement-opens-clause-p ()
  "Return position if the current statement opens block or clause. "
  (py--statement-opens-base py-clause-re))

(defun py--statement-opens-block-or-clause-p ()
  "Return position if the current statement opens block or clause. "
  (py--statement-opens-base py-block-or-clause-re))

(defun py--statement-opens-class-p ()
  "Return `t' if the statement opens a functions or class definition, nil otherwise. "
  (py--statement-opens-base py-class-re))

(defun py--statement-opens-def-p ()
  "Return `t' if the statement opens a functions or class definition, nil otherwise. "
  (py--statement-opens-base py-def-re))

(defun py--statement-opens-def-or-class-p ()
  "Return `t' if the statement opens a functions or class definition, nil otherwise. "
  (py--statement-opens-base py-def-or-class-re))

(defun py--record-list-error (pps)
  "When encountering a missing parenthesis, store its line, position. `py-verbose-p'  must be t

Unclosed-string errors are not handled here, as made visible by fontification already.
"
  (let ((this-err
         (save-excursion
           (list
            (nth 1 pps)
            (progn
              (goto-char (nth 1 pps))
              (py-count-lines (point-min) (point)))))))
    this-err))

(defun py--message-error (err)
  "Receives a list (position line) "
  (message "Closing paren missed: line %s pos %s" (cadr err) (car err)))

(defun py--end-base-look-upward (thisregexp regexp)
  (progn (back-to-indentation)
	 (let ((bofst (py--beginning-of-statement-p)))
	   (cond ((and bofst (eq regexp 'py-clause-re)(looking-at py-extended-block-or-clause-re))
		  (point))
		 ((and bofst (looking-at thisregexp))
		  (point))
		 (t
		  (when
		      (cdr-safe
		       (py--go-to-keyword
			thisregexp))
		    (when (py--statement-opens-block-p py-extended-block-or-clause-re)
		      (point))))))))

(defun py--go-down-when-found-upward (regexp)
  (let ((thisindent (current-indentation))
	last)
    (back-to-indentation)
    (while
	(and (py-down-statement)
	     (or (< thisindent (current-indentation))
		 (and (eq thisindent (current-indentation))
		      (or (eq regexp 'py-minor-block-re)
			  (eq regexp 'py-block-re)
			  (eq regexp 'py-if-block-re))
		      (looking-at py-clause-re)))
	     (py-forward-statement)(setq last (point))))
    (and last (goto-char last))))

(defun py--end-of-paragraph (regexp)
  (let* ((regexp (if (symbolp regexp) (symbol-value regexp)
		       regexp)))
    (while (and (not (eobp)) (re-search-forward regexp nil 'move 1)(nth 8 (parse-partial-sexp (point-min) (point)))))))


(defun py--end-base (regexp &optional orig decorator bol indent done)
  "Used internal by functions going to the end forms.

Must find start first "
  (unless (eobp)
    (if (eq regexp 'py-paragraph-re)
	(py--end-of-paragraph regexp)
      (let* ((pps (parse-partial-sexp (point-min) (point)))
	     ;; (repeat (or (and repeat (1+ repeat)) 0))
	     (orig (or orig (point)))
	     (regexp (or regexp (symbol-value 'py-extended-block-or-clause-re)))
	     (thisregexp (if (symbolp regexp)
			     (cond ((eq regexp 'py-clause-re)
				    (symbol-value 'py-extended-block-or-clause-re))
				   (t (symbol-value regexp)))
			   regexp))
	     (indent (or indent
			 ;; avoid costly moves by statement
			 (when (and (not (nth 8 pps))
				    (or (looking-back py-decorator-re)
					(looking-back (concat (symbol-value regexp) ".+"))))
			   (current-indentation))
			 (if (py--beginning-of-statement-p)
			     (current-indentation)
			   (save-excursion (py-backward-statement) (current-indentation)))))

	     ;; start of form maybe inside
	     (this
	      (cond ((and (looking-at thisregexp) (not (or (nth 1 pps) (nth 8 pps))))
		     (point))
		    ((and (not (nth 8 pps))(looking-back py-decorator-re))
		     (and (re-search-forward thisregexp nil t 1)
			  (match-beginning 0)))
		    ;; when building the index, avoid costly moves by
		    ;; statement
		    ((and (not (nth 8 pps))(looking-back (symbol-value regexp)))
		     (match-beginning 0))
		    (t (py--go-to-keyword thisregexp indent))))
	     ;; (done done)
	     erg)
	(cond
	 (this (setq erg (py--go-down-when-found-upward regexp)))
	 (t (goto-char orig)))
	(if (< orig (point))
	    (and erg bol (setq erg (py--beginning-of-line-form erg)))
	  (setq erg nil)
	  ;; Prevent eternal loop
	  (unless done
	    (when
		(py-forward-statement)
	      (py--end-base regexp (point) decorator bol
			    ;; update required indent
			    (if (py--beginning-of-statement-p)
				(- (current-indentation) py-indent-offset)
			      (save-excursion (py-backward-statement) (- (current-indentation) py-indent-offset))) t
			    ;; indent
			    ))))
	erg))))

(defun py--look-downward-for-beginning (regexp)
  "When above any beginning of FORM, search downward. "
  (let* ((orig (point))
         (erg orig)
         (last orig)
         pps)
    (while (and (setq last (point)) (not (eobp)) (re-search-forward regexp nil t 1)(setq erg (match-beginning 0)) (setq pps (parse-partial-sexp (point-min) (point)))
                (or (nth 8 pps) (nth 1 pps))))
    (cond ((not (or (nth 8 pps) (nth 1 pps) (or (looking-at comment-start))))
           (when (ignore-errors (< orig erg))
             erg)))))

(defun py-look-downward-for-clause (&optional ind orig regexp)
  "If beginning of other clause exists downward in current block.

If succesful return position. "
  (interactive)
  (unless (eobp)
    (let ((ind (or ind
                   (save-excursion
                     (py-backward-statement)
                     (if (py--statement-opens-block-p)
                         (current-indentation)
                       (- (current-indentation) py-indent-offset)))))
          (orig (or orig (point)))
          (regexp (or regexp py-extended-block-or-clause-re))
          erg last)
      (end-of-line)
      (when (re-search-forward regexp nil t 1)
        (when (nth 8 (parse-partial-sexp (point-min) (point)))
          (while (and (re-search-forward regexp nil t 1)
                      (nth 8 (parse-partial-sexp (point-min) (point))))))
        (setq last (point))
        (back-to-indentation)
        (unless (and (looking-at py-clause-re)
                     (not (nth 8 (parse-partial-sexp (point-min) (point)))) (eq (current-indentation) ind))
          (progn (setq ind (current-indentation))
                 (while (and (py-forward-statement-bol)(not (looking-at py-clause-re))(<= ind (current-indentation)))))
          (if (and (looking-at py-clause-re)
                   (not (nth 8 (parse-partial-sexp (point-min) (point))))
                   (< orig (point)))
              (setq erg (point))
            (goto-char orig))))
      (when (called-interactively-p 'any) (message "%s" erg))
      erg)))

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
      (let ((erg (when (py-backward-def-or-class)
                   (forward-word 1)
                   (skip-chars-forward " \t")
                   (prin1-to-string (symbol-at-point)))))
        (when (and erg py-current-defun-show)
	  (push-mark (point) t t) (skip-chars-forward "^ (")
	  (exchange-point-and-mark)
	  (sit-for py-current-defun-delay))
        (when iact (message (prin1-to-string erg)))
        erg))))

(defun py-sort-imports ()
  "Sort multiline imports.

Put point inside the parentheses of a multiline import and hit
\\[py-sort-imports] to sort the imports lexicographically"
  (interactive)
  (save-excursion
    (let ((open-paren (ignore-errors (save-excursion (progn (up-list -1) (point)))))
          (close-paren (ignore-errors (save-excursion (progn (up-list 1) (point)))))
          sorted-imports)
      (when (and open-paren close-paren)
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
	(insert (py--join-words-wrapping (remove "" sorted-imports) "," "    " 78))
	(insert ")")))))

(defun py--in-literal (&optional lim)
  "Return non-nil if point is in a Python literal (a comment or string).
Optional argument LIM indicates the beginning of the containing form,
i.e. the limit on how far back to scan."
  (let* ((lim (or lim (point-min)))
         (state (parse-partial-sexp (point-min) (point))))
    (cond
     ((nth 3 state) 'string)
     ((nth 4 state) 'comment))))

(defconst py-help-address "python-mode@python.org"
  "List dealing with usage and developing python-mode.

Also accepts submission of bug reports, whilst a ticket at
http://launchpad.net/python-mode
is preferable for that. ")

;;  Utilities
(defun py--point (position)
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
               ((eq position 'bod) (py-backward-def-or-class))
               ((eq position 'eod) (py-forward-def-or-class))
               ;; Kind of funny, I know, but useful for py-up-exception.
               ((eq position 'bob) (goto-char (point-min)))
               ((eq position 'eob) (goto-char (point-max)))
               ((eq position 'boi) (back-to-indentation))
               ((eq position 'bos) (py-backward-statement))
               (t (error "Unknown buffer position requested: %s" position))) (point))))
    erg))

(defun py-install-search-local ()
  (interactive)
  (let ((erg (split-string (shell-command-to-string (concat "find " default-directory " -maxdepth 9 -type f -name \"*python\"")))))))

(defun py-install-local-shells (&optional local)
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
         prefix end orig curexe aktpath)
    (set-buffer (get-buffer-create py-extensions))
    (erase-buffer)
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

(defun py-end-of-string (&optional beginning-of-string-position)
  "Go to end of string at point if any, if successful return position. "
  (interactive)
  (let ((orig (point))
	(beginning-of-string-position (or beginning-of-string-position (and (nth 3 (parse-partial-sexp 1 (point)))(nth 8 (parse-partial-sexp 1 (point))))
                                          (and (looking-at "\"\"\"\\|'''\\|\"\\|\'")(match-beginning 0))))
        erg)
    (if beginning-of-string-position
        (progn
          (goto-char beginning-of-string-position)
	  (when
	      ;; work around parse-partial-sexp error
	      (and (nth 3 (parse-partial-sexp 1 (point)))(nth 8 (parse-partial-sexp 1 (point))))
	    (goto-char (nth 3 (parse-partial-sexp 1 (point)))))
          (if (ignore-errors (setq erg (scan-sexps (point) 1)))
			      (goto-char erg)
	    (goto-char orig)))

      (error (concat "py-end-of-string: don't see end-of-string at " (buffer-name (current-buffer)) "at pos " (point))))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

;;  (goto-char (match-end 0))
;;  (search-forward (match-string-no-properties 0))))

(defun py--until-found (search-string liste)
  "Search liste for search-string until found. "
  (let ((liste liste) element)
    (while liste
      (if (member search-string (car liste))
          (setq element (car liste) liste nil))
      (setq liste (cdr liste)))
    (when element
      (while (and element (not (numberp element)))
        (if (member search-string (car element))
            (setq element (car element))
          (setq element (cdr element))))
      element)))

(defun py--delay-process-dependent (process)
  "Call a `py-ipython-send-delay' or `py-python-send-delay' according to process"
  (if (string-match "ipython" (prin1-to-string process))
      (sit-for py-ipython-send-delay t)
    (sit-for py-python-send-delay t)))

(defun py--send-string-no-output (strg &optional process msg)
  "Send STRING to PROCESS and inhibit output display.
When MSG is non-nil messages the first line of STRING.  Return
the output."
  (let* (output
         (process (or process (get-buffer-process (py-shell))))
         (comint-preoutput-filter-functions
          (append comint-preoutput-filter-functions
                  '(ansi-color-filter-apply
                    (lambda (strg)
                      (setq output strg)
                      "")))))
    (py-send-string strg process)
    (sit-for 0.1 t)
    ;; (py--delay-process-dependent process)
    (when (and output (not (string= "" output)))
	    (py--string-strip
	     (format "[ \n]*%s[ \n]*" py-fast-filter-re)))))

(defun py--send-string-return-output (strg &optional process msg)
  "Send STRING to PROCESS and return output.

When MSG is non-nil messages the first line of STRING.  Return
the output."
  (let ((process (or process (get-buffer-process (py-shell)))))
    (with-current-buffer (process-buffer process)
      (let* (erg
	     (comint-preoutput-filter-functions
	      (append comint-preoutput-filter-functions
		      '(ansi-color-filter-apply
			(lambda (strg)
			  strg)))))
	(py-send-string strg process)
	(accept-process-output process 5)
	(sit-for 0.1 t)
	(when (and erg (not (string= "" erg)))
	  (setq erg
		(replace-regexp-in-string
		 (format "[ \n]*%s[ \n]*" py-fast-filter-re)
		 "" erg)))
	;; (sit-for 0.1 t)
	erg))))

(defun py-which-def-or-class (&optional orig)
  "Returns concatenated `def' and `class' names in hierarchical order, if cursor is inside.

Returns \"???\" otherwise
Used by variable `which-func-functions' "
  (interactive)
  (let* ((orig (or orig (point)))
	 (backindent 99999)
	 (re py-def-or-class-re
	  ;; (concat py-def-or-class-re "\\([[:alnum:]_]+\\)")
	  )
         erg forward indent backward limit)
    (if
	(and (looking-at re)
	     (not (nth 8 (parse-partial-sexp (point-min) (point)))))
	(progn
	  (setq erg (list (match-string-no-properties 2)))
	  (setq backindent (current-indentation)))
      ;; maybe inside a definition's symbol
      (or (eolp) (and (looking-at "[[:alnum:]]")(forward-word 1))))
    (if
	(and (not (and erg (eq 0 (current-indentation))))
	     (setq limit (py-backward-top-level))
	     (looking-at re))
	(progn
	  (push (match-string-no-properties 2)  erg)
	  (setq indent (current-indentation)))
      (goto-char orig)
      (while (and
	      (re-search-backward py-def-or-class-re limit t 1)
	      (< (current-indentation) backindent)
	      (setq backindent (current-indentation))
	      (setq backward (point))
	      (or (< 0 (current-indentation))
		  (nth 8 (parse-partial-sexp (point-min) (point))))))
      (when (and backward
		 (goto-char backward)
		 (looking-at re))
	(push (match-string-no-properties 2)  erg)
	(setq indent (current-indentation))))
    ;; (goto-char orig))
    (if erg
	(progn
	  (end-of-line)
	  (while (and (re-search-forward py-def-or-class-re nil t 1)
		      (<= (point) orig)
		      (< indent (current-indentation))
		      (or
		       (nth 8 (parse-partial-sexp (point-min) (point)))
		       (setq forward (point)))))
	  (if forward
	      (progn
		(goto-char forward)
		(save-excursion
		  (back-to-indentation)
		  (and (looking-at re)
		       (setq erg (list (car erg) (match-string-no-properties 2)))
		       ;; (< (py-forward-def-or-class) orig)
		       ;; if match was beyond definition, nil
		       ;; (setq erg nil)
)))
	    (goto-char orig))))
    (if erg
	(if (< 1 (length erg))
	    (setq erg (mapconcat 'identity erg "."))
	  (setq erg (car erg)))
      (setq erg "???"))
    (goto-char orig)
    (when (called-interactively-p 'any) (message "%s" erg))
    erg))


(defun py--trim-regexp-empty-spaces-left (regexp)
    (let ((erg (symbol-value regexp)))
      (substring erg (1+ (string-match "\*" erg)))))

(defun py--beginning-of-form-intern (final-re &optional inter-re iact indent orig lc decorator)
  "Go to beginning of FORM.

With INDENT, go to beginning one level above.
Whit IACT, print result in message buffer.

Returns beginning of FORM if successful, nil otherwise"
  (interactive "P")
  (let ((regexp
	 ;; (if inter-re
	 ;; (concat (symbol-value inter-re) "\\|" (symbol-value final-re))
	 (if (eq 0 indent)
	     (py--trim-regexp-empty-spaces-left final-re)
		  (symbol-value final-re)))
		  ;; ))
	erg)
    (unless (bobp)
      (let* ((orig (or orig (point)))
             (indent (or indent (progn
                                  (back-to-indentation)
                                  (or (py--beginning-of-statement-p)
                                      (py-backward-statement))
                                  (current-indentation)))))
        (setq erg (cond ((and (< (point) orig) (looking-at regexp))
                         (point))
                        ((and (eq 0 (current-column)) (numberp indent) (< 0 indent))
                         (when (< 0 (abs (skip-chars-backward " \t\r\n\f")))
                           (py-backward-statement)
                           (unless (looking-at regexp)
                             (cdr (py--go-to-keyword regexp (current-indentation))))))
                        ((numberp indent)
			 (or (cdr (py--go-to-keyword regexp indent))
			     (progn
			       (goto-char orig)
			       (cdr (py--go-to-keyword regexp indent)))))
                        (t (ignore-errors
                             (cdr (py--go-to-keyword regexp
						     (- (progn (if (py--beginning-of-statement-p) (current-indentation) (save-excursion (py-backward-statement) (current-indentation)))) py-indent-offset)))))))
        (when lc (beginning-of-line) (setq erg (point)))))
    (when (and py-verbose-p iact) (message "%s" erg))
    erg))

(defun py--backward-prepare (&optional indent final-re inter-re iact decorator lc)
  (let* ((orig (point))
	 (indent
	  (or indent
	      (progn
		(or (py--beginning-of-statement-p)
		    (py-backward-statement))
		;; maybe after last statement?
		(if (save-excursion
		      (< (py-forward-statement) orig))
		    (progn (goto-char orig)
			   (back-to-indentation) 
			   (current-indentation))
		  (cond ((looking-back "^[ \t]*" (line-beginning-position))
			 (current-indentation))
			(t (progn (back-to-indentation)
				  (cond ((eq 0 (current-indentation))
					 (current-indentation))
					((and inter-re (looking-at (symbol-value inter-re)))
					 (current-indentation))))))))))
	 erg)
    ;; def and class need lesser value
    (when (and
	   (member final-re (list 'py-def-or-class-re 'py-class-re 'py-def-re))
	   (<= 0 (- indent (if py-smart-indentation (py-guess-indent-offset) py-indent-offset))))
      (setq indent (- indent (if py-smart-indentation (py-guess-indent-offset) py-indent-offset))))
    (if (and (< (point) orig) (looking-at (symbol-value final-re)))
        (progn
          (and lc (beginning-of-line))
          (setq erg (point))
          (when (and py-verbose-p iact) (message "%s" erg))
          erg)
      (py--beginning-of-form-intern final-re inter-re iact indent orig lc decorator))))

(defun py--fetch-first-python-buffer ()
  "Returns first (I)Python-buffer found in `buffer-list'"
  (let ((buli (buffer-list))
        erg)
    (while (and buli (not erg))
      (if (string-match "Python" (prin1-to-string (car buli)))
          (setq erg (car buli))
        (setq buli (cdr buli))))
    erg))

(defun py-unload-python-el ()
  "Unloads python-mode delivered by shipped python.el

Removes python-skeleton forms from abbrevs.
These would interfere when inserting forms heading a block"
  (interactive)
  (let (done)
    (when (featurep 'python) (unload-feature 'python t))
    (when (file-readable-p abbrev-file-name)
      (find-file abbrev-file-name)
      (goto-char (point-min))
      (while (re-search-forward "^.+python-skeleton.+$" nil t 1)
	(setq done t)
	(delete-region (match-beginning 0) (1+ (match-end 0))))
      (when done (write-file abbrev-file-name)
	    ;; now reload
	    (read-abbrev-file abbrev-file-name))
      (kill-buffer (file-name-nondirectory abbrev-file-name)))))

(defmacro py--kill-buffer-unconditional (buffer)
  "Kill buffer unconditional, kill buffer-process if existing. "
  `(let ((proc (get-buffer-process ,buffer))
	 kill-buffer-query-functions)
     (ignore-errors
       (and proc (kill-process proc))
       (set-buffer ,buffer)
       (set-buffer-modified-p 'nil)
       (kill-buffer (current-buffer)))))

(defun py--skip-to-semicolon-backward (&optional limit)
  "Fetch the beginning of statement after a semicolon.

Returns `t' if point was moved"
  (prog1
      (< 0 (abs (skip-chars-backward "^;" (or limit (line-beginning-position)))))
    (skip-chars-forward " \t" (line-end-position))))

(defun py--end-of-comment-intern (pos)
  (while (and (not (eobp))
              (forward-comment 99999)))
  ;; forward-comment fails sometimes
  (and (eq pos (point)) (prog1 (forward-line 1) (back-to-indentation))
       (while (member (char-after) (list comment-start 10))(forward-line 1)(back-to-indentation))))

(defun py--skip-to-comment-or-semicolon (done)
  "Returns position if comment or semicolon found. "
  (let ((orig (point)))
    (cond ((and done (< 0 (abs (skip-chars-forward "^#;" (line-end-position))))
		(member (char-after) (list ?# ?\;)))
	   (when (eq ?\; (char-after))
	     (skip-chars-forward ";" (line-end-position))))
	  ((and (< 0 (abs (skip-chars-forward "^#;" (line-end-position))))
		(member (char-after) (list ?# ?\;)))
	   (when (eq ?\; (char-after))
	     (skip-chars-forward ";" (line-end-position))))
	  ((not done)
	   (end-of-line)))
    (skip-chars-backward " \t" (line-beginning-position))
    (and (< orig (point))(setq done t)
	 done)))

(defun py-backward-top-level ()
  "Go up to beginning of statments until level of indentation is null.

Returns position if successful, nil otherwise "
  (interactive)
  (let (erg done)
    (unless (bobp)
      (while (and (not done)(not (bobp))
		  (setq erg (re-search-backward "^[[:alpha:]_'\"]" nil t 1)))
	(if
	    (nth 8 (parse-partial-sexp (point-min) (point)))
	    (setq erg nil)
	  (setq done t)))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg)))

(defun py-forward-top-level ()
  "Go to end of top-level form at point.

Returns position if successful, nil otherwise"
  (interactive)
  (let ((orig (point))
	erg)
    (unless (eobp)
      (unless (py--beginning-of-statement-p)
	(py-backward-statement))
      (unless (eq 0 (current-column))
	(py-backward-top-level))
      (cond ((looking-at py-def-re)
	     (setq erg (py-forward-def)))
	    ((looking-at py-class-re)
	     (setq erg (py-forward-class)))
	    ((looking-at py-block-re)
	     (setq erg (py-forward-block)))
	    (t (setq erg (py-forward-statement))))
      (unless (< orig (point))
	(while (and (not (eobp)) (py-down-statement)(< 0 (current-indentation))))
	(if (looking-at py-block-re)
	    (setq erg (py-forward-block))
	  (setq erg (py-forward-statement))))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg)))

(defun py-down-top-level ()
  "Go to beginning of next top-level form downward.

Returns position if successful, nil otherwise"
  (interactive)
  (let ((orig (point))
        erg)
    (while (and (not (eobp))
		(progn (end-of-line)
		       (re-search-forward "^[[:alpha:]_'\"]" nil 'move 1))
		(nth 8 (parse-partial-sexp (point-min) (point)))))
    (when (and (not (eobp)) (< orig (point)))
      (goto-char (match-beginning 0))
	(setq erg (point)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-forward-top-level-bol ()
  "Go to end of top-level form at point, stop at next beginning-of-line.

Returns position successful, nil otherwise"
  (interactive)
  (let (erg)
    (py-forward-top-level)
    (unless (or (eobp) (bolp))
      (forward-line 1)
      (beginning-of-line)
      (setq erg (point)))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py-down (&optional indent)
  "Go to beginning one level below of compound statement or definition at point.

If no statement or block below, but a delimited form --string or list-- go to its beginning. Repeated call from there will behave like down-list.

Returns position if successful, nil otherwise"
  (interactive "P")
  (let* ((orig (point))
         erg
         (indent (if
                     (py--beginning-of-statement-p)
                     (current-indentation)
                   (progn
                     (py-backward-statement)
                     (current-indentation))))
         last)
    (while (and (setq last (point)) (py-forward-statement) (py-forward-statement) (py-backward-statement) (eq (current-indentation) indent)))
    (if (< indent (current-indentation))
        (setq erg (point))
      (goto-char last))
    (when (< (point) orig)
      (goto-char orig))
    (when (and (eq (point) orig)
               (progn (forward-char 1)
                      (skip-chars-forward "^\"'[({" (line-end-position))
                      (member (char-after) (list ?\( ?\" ?\' ?\[ ?\{)))
               (setq erg (point))))
    (unless erg
      (goto-char orig))
    (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
    erg))

(defun py--beginning-of-line-form (erg)
  "Internal use: Go to beginning of line following end of form. "
  (when erg
    (unless (eobp)
      (forward-line 1)
      (beginning-of-line)
      (setq erg (point)))))

(defun py--mark-base (form &optional mark-decorators)
  "Returns boundaries of FORM, a cons.

If PY-MARK-DECORATORS, `def'- and `class'-forms include decorators
If BOL is t, mark from beginning-of-line"
  (let* ((begform (intern-soft (concat "py-backward-" form)))
         (endform (intern-soft (concat "py-forward-" form)))
         (begcheckform (intern-soft (concat "py--beginning-of-" form "-p")))
         (orig (point))
         beg end erg)
    (setq beg (if
                  (setq beg (funcall begcheckform))
                  beg
                (funcall begform)))
    (and mark-decorators
         (and (setq erg (py-backward-decorator))
              (setq beg erg)))
    (push-mark)
    (setq end (funcall endform))
    (unless end (when (< beg (point))
                  (setq end (point))))
    (if (and beg end (<= beg orig) (<= orig end))
	(cons beg end)
      nil)))

(defun py--mark-base-bol (form &optional py-mark-decorators)
  (let* ((begform (intern-soft (concat "py-backward-" form "-bol")))
         (endform (intern-soft (concat "py-forward-" form "-bol")))
         (begcheckform (intern-soft (concat "py--beginning-of-" form "-bol-p")))
         beg end erg)
    (setq beg (if
                  (setq beg (funcall begcheckform))
                  beg
                (funcall begform)))
    (when py-mark-decorators
      (save-excursion
        (when (setq erg (py-backward-decorator))
          (setq beg erg))))
    (setq end (funcall endform))
    (push-mark beg t t)
    (unless end (when (< beg (point))
                  (setq end (point))))
    (cons beg end)))

(defun py-mark-base (form &optional mark-decorators)
  "Calls py--mark-base, returns bounds of form, a cons. "
  (let* ((bounds (py--mark-base form mark-decorators))
         (beg (car bounds)))
    (push-mark beg t t)
    bounds))

(defun py-beginning (&optional indent)
 "Go to beginning of compound statement or definition at point.

With \\[universal-argument], go to beginning one level above.
Returns position if successful, nil otherwise"
  (interactive "P")
  (py--beginning-of-form-intern py-extended-block-or-clause-re (called-interactively-p 'any) indent))

(defun py-end ()
 "Go to end of of compound statement or definition at point.

Returns position block if successful, nil otherwise"
  (interactive "P")
    (let* ((orig (point))
           (erg (py--end-base 'py-extended-block-or-clause-re orig)))
      (when (and py-verbose-p (called-interactively-p 'any)) (message "%s" erg))
      erg))

;;  Buffer
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

(defun py-backward-same-level ()
  "Go form backward keeping indent level if possible.

If inside a delimited form --string or list-- go to its beginning.
If not at beginning of a statement or block, go to its beginning.
If at beginning of a statement or block, go to previous beginning of compound statement or definition at point.
If no further element at same level, go one level up."
  (interactive)
  (let ((pps (parse-partial-sexp (point-min) (point))))
    (cond ((nth 8 pps) (goto-char (nth 8 pps)))
          ((nth 1 pps) (goto-char (nth 1 pps)))
          (t (if (eq (current-column) (current-indentation))
		 (py--beginning-of-form-intern 'py-extended-block-or-clause-re (called-interactively-p 'any))
	       (back-to-indentation)
	       (py-backward-same-level))))))

(defun py--end-of-buffer-p ()
  "Returns position, if cursor is at the end of buffer, nil otherwise. "
  (when (eobp)(point)))

(defun py-sectionize-region (&optional beg end)
  "Markup code in region as section.

Use current region unless optional args BEG END are delivered."
  (interactive "*")
  (let ((beg (or beg (region-beginning)))
	(end (or (and end (copy-marker end)) (copy-marker (region-end)))))
    (save-excursion
      (goto-char beg)
      (unless (empty-line-p) (split-line))
      (beginning-of-line)
      (insert py-section-start)
      (goto-char end)
      (unless (empty-line-p) (newline))
      (insert py-section-end))))

(defun py-execute-section-prepare (&optional shell)
  "Execute section at point. "
  (save-excursion
    (let ((start (when (or (py--beginning-of-section-p)
			   (py-backward-section))
		   (forward-line 1)
		   (beginning-of-line)
		   (point))))
      (if (and start (py-forward-section))
	  (progn
	    (beginning-of-line)
	    (skip-chars-backward " \t\r\n\f")
	    (if shell
		(funcall (car (read-from-string (concat "py-execute-region-" shell))) start (point))
	      (py-execute-region start (point))))
	(error "Can't see `py-section-start' resp. `py-section-end'")))))

(defun py--narrow-prepare (name)
  "Used internally. "
  (save-excursion
    (let ((start (cond ((string= name "statement")
			(if (py--beginning-of-statement-p)
			    (point)
			  (py-backward-statement-bol)))
		       ((funcall (car (read-from-string (concat "py--statement-opens-" name "-p")))))
		       (t (funcall (car (read-from-string (concat "py-backward-" name "-bol"))))))))
      (funcall (car (read-from-string (concat "py-forward-" name))))
      (narrow-to-region (point) start))))

(defun py--forms-report-result (erg &optional iact)
  (let ((res (ignore-errors (buffer-substring-no-properties (car-safe erg) (cdr-safe erg)))))
    (when (and res iact)
      (goto-char (car-safe erg))
      (set-mark (point))
      (goto-char (cdr-safe erg)))
    res))

(defun py-rotate-shell-fontify-style (msg)
  "Rotates between possible values 'all, 'input and nil. "
  (interactive "p")
  (cond ((eq py-shell-fontify-style 'all)
	 (setq py-shell-fontify-style nil))
	((eq py-shell-fontify-style 'input)
	 (setq py-shell-fontify-style 'all))
	(t (setq py-shell-fontify-style 'input)))
  (py--shell-setup-fontification py-shell-fontify-style)
  (when msg (message "py-shell-fontify-style set to: %s" py-shell-fontify-style)))

(defun py-toggle-execute-use-temp-file ()
  (interactive)
  (setq py--execute-use-temp-file-p (not py--execute-use-temp-file-p)))

(defun py--close-intern (regexp)
  "Core function, internal used only. "
  (let ((cui (car (py--go-to-keyword (symbol-value regexp)))))
    (message "%s" cui)
    (py--end-base regexp (point))
    (forward-line 1)
    (if py-close-provides-newline
        (unless (empty-line-p) (split-line))
      (fixup-whitespace))
    (indent-to-column cui)
    cui))

;; /usr/lib/python2.7/pdb.py eyp.py
(defalias 'IPython 'ipython)
(defalias 'Ipython 'ipython)
(defalias 'Python 'python)
(defalias 'Python2 'python2)
(defalias 'Python3 'python3)
(defalias 'ipy 'ipython)
(defalias 'iyp 'ipython)
(defalias 'py-execute-region-default 'py-execute-region)
(defalias 'py-execute-region-default-dedicated 'py-execute-region-dedicated)
(defalias 'py-fast-send-string 'py-execute-string-fast)
(defalias 'py-kill-minor-expression 'py-kill-partial-expression)
(defalias 'pyhotn 'python)
(defalias 'pyhton 'python)
(defalias 'pyt 'python)

;; python-components-shell-menu

(and (ignore-errors (require 'easymenu) t)
     ;; (easy-menu-define py-menu map "Python Tools"
     ;;           `("PyTools"
     (easy-menu-define
       py-shell-menu py-python-shell-mode-map "Py-Shell Mode menu"
       `("Py-Shell"
         ("Edit"
          ("Shift"
           ("Shift right"
	    ["Shift block right" py-shift-block-right
	     :help " `py-shift-block-right'
Indent block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift block or clause right" py-shift-block-or-clause-right
	     :help " `py-shift-block-or-clause-right'
Indent block-or-clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift class right" py-shift-class-right
	     :help " `py-shift-class-right'
Indent class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift clause right" py-shift-clause-right
	     :help " `py-shift-clause-right'
Indent clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift comment right" py-shift-comment-right
	     :help " `py-shift-comment-right'"]

	    ["Shift def right" py-shift-def-right
	     :help " `py-shift-def-right'
Indent def by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift def or class right" py-shift-def-or-class-right
	     :help " `py-shift-def-or-class-right'
Indent def-or-class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift minor block right" py-shift-minor-block-right
	     :help " `py-shift-minor-block-right'
Indent minor-block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached.
A minor block is started by a `for', `if', `try' or `with'."]

	    ["Shift paragraph right" py-shift-paragraph-right
	     :help " `py-shift-paragraph-right'
Indent paragraph by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift region right" py-shift-region-right
	     :help " `py-shift-region-right'
Indent region according to `py-indent-offset' by COUNT times.

If no region is active, current line is indented.
Returns indentation reached."]

	    ["Shift statement right" py-shift-statement-right
	     :help " `py-shift-statement-right'
Indent statement by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift top level right" py-shift-top-level-right
	     :help " `py-shift-top-level-right'"]
            )
           ("Shift left"
	    ["Shift block left" py-shift-block-left
	     :help " `py-shift-block-left'
Dedent block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift block or clause left" py-shift-block-or-clause-left
	     :help " `py-shift-block-or-clause-left'
Dedent block-or-clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift class left" py-shift-class-left
	     :help " `py-shift-class-left'
Dedent class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift clause left" py-shift-clause-left
	     :help " `py-shift-clause-left'
Dedent clause by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift comment left" py-shift-comment-left
	     :help " `py-shift-comment-left'"]

	    ["Shift def left" py-shift-def-left
	     :help " `py-shift-def-left'
Dedent def by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift def or class left" py-shift-def-or-class-left
	     :help " `py-shift-def-or-class-left'
Dedent def-or-class by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift minor block left" py-shift-minor-block-left
	     :help " `py-shift-minor-block-left'
Dedent minor-block by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached.
A minor block is started by a `for', `if', `try' or `with'."]

	    ["Shift paragraph left" py-shift-paragraph-left
	     :help " `py-shift-paragraph-left'
Dedent paragraph by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]

	    ["Shift region left" py-shift-region-left
	     :help " `py-shift-region-left'
Dedent region according to `py-indent-offset' by COUNT times.

If no region is active, current line is dedented.
Returns indentation reached."]

	    ["Shift statement left" py-shift-statement-left
	     :help " `py-shift-statement-left'
Dedent statement by COUNT spaces.

COUNT defaults to `py-indent-offset',
use [universal-argument] to specify a different value.

Returns outmost indentation reached."]
            ))
          ("Mark"
	   ["Mark block" py-mark-block
	    :help " `py-mark-block'
Mark block at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark block or clause" py-mark-block-or-clause
	    :help " `py-mark-block-or-clause'
Mark block-or-clause at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark class" py-mark-class
	    :help " `py-mark-class'
Mark class at point.

With C-u or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons."]

	   ["Mark clause" py-mark-clause
	    :help " `py-mark-clause'
Mark clause at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark comment" py-mark-comment
	    :help " `py-mark-comment'
Mark comment at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark def" py-mark-def
	    :help " `py-mark-def'
Mark def at point.

With C-u or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons."]

	   ["Mark def or class" py-mark-def-or-class
	    :help " `py-mark-def-or-class'
Mark def-or-class at point.

With C-u or `py-mark-decorators' set to `t', decorators are marked too.
Returns beginning and end positions of marked area, a cons."]

	   ["Mark expression" py-mark-expression
	    :help " `py-mark-expression'
Mark expression at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark line" py-mark-line
	    :help " `py-mark-line'
Mark line at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark minor block" py-mark-minor-block
	    :help " `py-mark-minor-block'
Mark minor-block at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark paragraph" py-mark-paragraph
	    :help " `py-mark-paragraph'
Mark paragraph at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark partial expression" py-mark-partial-expression
	    :help " `py-mark-partial-expression'
Mark partial-expression at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark statement" py-mark-statement
	    :help " `py-mark-statement'
Mark statement at point.

Returns beginning and end positions of marked area, a cons."]

	   ["Mark top level" py-mark-top-level
	    :help " `py-mark-top-level'
Mark top-level at point.

Returns beginning and end positions of marked area, a cons."]
           )
          ("Copy"
	   ["Copy block" py-copy-block
	    :help " `py-copy-block'
Copy block at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy block or clause" py-copy-block-or-clause
	    :help " `py-copy-block-or-clause'
Copy block-or-clause at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy class" py-copy-class
	    :help " `py-copy-class'
Copy class at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy clause" py-copy-clause
	    :help " `py-copy-clause'
Copy clause at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy comment" py-copy-comment
	    :help " `py-copy-comment'"]

	   ["Copy def" py-copy-def
	    :help " `py-copy-def'
Copy def at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy def or class" py-copy-def-or-class
	    :help " `py-copy-def-or-class'
Copy def-or-class at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy expression" py-copy-expression
	    :help " `py-copy-expression'
Copy expression at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy line" py-copy-line
	    :help " `py-copy-line'"]

	   ["Copy minor block" py-copy-minor-block
	    :help " `py-copy-minor-block'
Copy minor-block at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy paragraph" py-copy-paragraph
	    :help " `py-copy-paragraph'"]

	   ["Copy partial expression" py-copy-partial-expression
	    :help " `py-copy-partial-expression'
Copy partial-expression at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy statement" py-copy-statement
	    :help " `py-copy-statement'
Copy statement at point.

Store data in kill ring, so it might yanked back."]

	   ["Copy top level" py-copy-top-level
	    :help " `py-copy-top-level'
Copy top-level at point.

Store data in kill ring, so it might yanked back."]
           )
          ("Kill"
	   ["Kill block" py-kill-block
	    :help " `py-kill-block'
Delete `block' at point.

Stores data in kill ring"]

	   ["Kill block or clause" py-kill-block-or-clause
	    :help " `py-kill-block-or-clause'
Delete `block-or-clause' at point.

Stores data in kill ring"]

	   ["Kill class" py-kill-class
	    :help " `py-kill-class'
Delete `class' at point.

Stores data in kill ring"]

	   ["Kill clause" py-kill-clause
	    :help " `py-kill-clause'
Delete `clause' at point.

Stores data in kill ring"]

	   ["Kill comment" py-kill-comment
	    :help " `py-kill-comment'"]

	   ["Kill def" py-kill-def
	    :help " `py-kill-def'
Delete `def' at point.

Stores data in kill ring"]

	   ["Kill def or class" py-kill-def-or-class
	    :help " `py-kill-def-or-class'
Delete `def-or-class' at point.

Stores data in kill ring"]

	   ["Kill expression" py-kill-expression
	    :help " `py-kill-expression'
Delete `expression' at point.

Stores data in kill ring"]

	   ["Kill line" py-kill-line
	    :help " `py-kill-line'"]

	   ["Kill minor block" py-kill-minor-block
	    :help " `py-kill-minor-block'
Delete `minor-block' at point.

Stores data in kill ring"]

	   ["Kill paragraph" py-kill-paragraph
	    :help " `py-kill-paragraph'"]

	   ["Kill partial expression" py-kill-partial-expression
	    :help " `py-kill-partial-expression'
Delete `partial-expression' at point.

Stores data in kill ring"]

	   ["Kill statement" py-kill-statement
	    :help " `py-kill-statement'
Delete `statement' at point.

Stores data in kill ring"]

	   ["Kill top level" py-kill-top-level
	    :help " `py-kill-top-level'
Delete `top-level' at point.

Stores data in kill ring"]
           )
          ("Delete"
	   ["Delete block" py-delete-block
	    :help " `py-delete-block'
Delete BLOCK at point.

Don't store data in kill ring."]

	   ["Delete block or clause" py-delete-block-or-clause
	    :help " `py-delete-block-or-clause'
Delete BLOCK-OR-CLAUSE at point.

Don't store data in kill ring."]

	   ["Delete class" py-delete-class
	    :help " `py-delete-class'
Delete CLASS at point.

Don't store data in kill ring.
With C-u or `py-mark-decorators' set to `t', `decorators' are included."]

	   ["Delete clause" py-delete-clause
	    :help " `py-delete-clause'
Delete CLAUSE at point.

Don't store data in kill ring."]

	   ["Delete comment" py-delete-comment
	    :help " `py-delete-comment'"]

	   ["Delete def" py-delete-def
	    :help " `py-delete-def'
Delete DEF at point.

Don't store data in kill ring.
With C-u or `py-mark-decorators' set to `t', `decorators' are included."]

	   ["Delete def or class" py-delete-def-or-class
	    :help " `py-delete-def-or-class'
Delete DEF-OR-CLASS at point.

Don't store data in kill ring.
With C-u or `py-mark-decorators' set to `t', `decorators' are included."]

	   ["Delete expression" py-delete-expression
	    :help " `py-delete-expression'
Delete EXPRESSION at point.

Don't store data in kill ring."]

	   ["Delete line" py-delete-line
	    :help " `py-delete-line'"]

	   ["Delete minor block" py-delete-minor-block
	    :help " `py-delete-minor-block'
Delete MINOR-BLOCK at point.

Don't store data in kill ring."]

	   ["Delete paragraph" py-delete-paragraph
	    :help " `py-delete-paragraph'"]

	   ["Delete partial expression" py-delete-partial-expression
	    :help " `py-delete-partial-expression'
Delete PARTIAL-EXPRESSION at point.

Don't store data in kill ring."]

	   ["Delete statement" py-delete-statement
	    :help " `py-delete-statement'
Delete STATEMENT at point.

Don't store data in kill ring."]

	   ["Delete top level" py-delete-top-level
	    :help " `py-delete-top-level'
Delete TOP-LEVEL at point.

Don't store data in kill ring."]
           )
          ("Comment"
	   ["Comment block" py-comment-block
	    :help " `py-comment-block'
Comments block at point.

Uses double hash (`#') comment starter when `py-block-comment-prefix-p' is  `t',
the default"]

	   ["Comment block or clause" py-comment-block-or-clause
	    :help " `py-comment-block-or-clause'
Comments block-or-clause at point.

Uses double hash (`#') comment starter when `py-block-comment-prefix-p' is  `t',
the default"]

	   ["Comment class" py-comment-class
	    :help " `py-comment-class'
Comments class at point.

Uses double hash (`#') comment starter when `py-block-comment-prefix-p' is  `t',
the default"]

	   ["Comment clause" py-comment-clause
	    :help " `py-comment-clause'
Comments clause at point.

Uses double hash (`#') comment starter when `py-block-comment-prefix-p' is  `t',
the default"]

	   ["Comment def" py-comment-def
	    :help " `py-comment-def'
Comments def at point.

Uses double hash (`#') comment starter when `py-block-comment-prefix-p' is  `t',
the default"]

	   ["Comment def or class" py-comment-def-or-class
	    :help " `py-comment-def-or-class'
Comments def-or-class at point.

Uses double hash (`#') comment starter when `py-block-comment-prefix-p' is  `t',
the default"]

	   ["Comment statement" py-comment-statement
	    :help " `py-comment-statement'
Comments statement at point.

Uses double hash (`#') comment starter when `py-block-comment-prefix-p' is  `t',
the default"]
           ))
         ("Move"
          ("Backward"
	   ["Beginning of block" py-beginning-of-block
	    :help " `py-beginning-of-block'
Go to beginning block, skip whitespace at BOL.

Returns beginning of block if successful, nil otherwise"]

	   ["Beginning of block or clause" py-beginning-of-block-or-clause
	    :help " `py-beginning-of-block-or-clause'
Go to beginning block-or-clause, skip whitespace at BOL.

Returns beginning of block-or-clause if successful, nil otherwise"]

	   ["Beginning of class" py-beginning-of-class
	    :help " `py-beginning-of-class'
Go to beginning class, skip whitespace at BOL.

Returns beginning of class if successful, nil otherwise

When `py-mark-decorators' is non-nil, decorators are considered too."]

	   ["Beginning of clause" py-beginning-of-clause
	    :help " `py-beginning-of-clause'
Go to beginning clause, skip whitespace at BOL.

Returns beginning of clause if successful, nil otherwise"]

	   ["Beginning of def" py-beginning-of-def
	    :help " `py-beginning-of-def'
Go to beginning def, skip whitespace at BOL.

Returns beginning of def if successful, nil otherwise

When `py-mark-decorators' is non-nil, decorators are considered too."]

	   ["Beginning of def or class" py-beginning-of-def-or-class
	    :help " `py-beginning-of-def-or-class'
Go to beginning def-or-class, skip whitespace at BOL.

Returns beginning of def-or-class if successful, nil otherwise

When `py-mark-decorators' is non-nil, decorators are considered too."]

	   ["Beginning of elif block" py-beginning-of-elif-block
	    :help " `py-beginning-of-elif-block'
Go to beginning elif-block, skip whitespace at BOL.

Returns beginning of elif-block if successful, nil otherwise"]

	   ["Beginning of else block" py-beginning-of-else-block
	    :help " `py-beginning-of-else-block'
Go to beginning else-block, skip whitespace at BOL.

Returns beginning of else-block if successful, nil otherwise"]

	   ["Beginning of except block" py-beginning-of-except-block
	    :help " `py-beginning-of-except-block'
Go to beginning except-block, skip whitespace at BOL.

Returns beginning of except-block if successful, nil otherwise"]

	   ["Beginning of expression" py-beginning-of-expression
	    :help " `py-beginning-of-expression'
Go to the beginning of a compound python expression.

With numeric ARG do it that many times.

A a compound python expression might be concatenated by \".\" operator, thus composed by minor python expressions.

If already at the beginning or before a expression, go to next expression in buffer upwards

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference
Operators however are left aside resp. limit py-expression designed for edit-purposes."]

	   ["Beginning of if block" py-beginning-of-if-block
	    :help " `py-beginning-of-if-block'
Go to beginning if-block, skip whitespace at BOL.

Returns beginning of if-block if successful, nil otherwise"]

	   ["Beginning of partial expression" py-beginning-of-partial-expression
	    :help " `py-beginning-of-partial-expression'"]

	   ["Beginning of statement" py-beginning-of-statement
	    :help " `py-beginning-of-statement'
Go to the initial line of a simple statement.

For beginning of compound statement use py-beginning-of-block.
For beginning of clause py-beginning-of-clause."]

	   ["Beginning of top level" py-beginning-of-top-level
	    :help " `py-beginning-of-top-level'
Go up to beginning of statments until level of indentation is null.

Returns position if successful, nil otherwise"]

	   ["Beginning of try block" py-beginning-of-try-block
	    :help " `py-beginning-of-try-block'
Go to beginning try-block, skip whitespace at BOL.

Returns beginning of try-block if successful, nil otherwise"]
           )
          ("Forward"
	   ["End of block" py-end-of-block
	    :help " `py-end-of-block'
Go to end of block.

Returns end of block if successful, nil otherwise"]

	   ["End of block or clause" py-end-of-block-or-clause
	    :help " `py-end-of-block-or-clause'
Go to end of block-or-clause.

Returns end of block-or-clause if successful, nil otherwise"]

	   ["End of class" py-end-of-class
	    :help " `py-end-of-class'
Go to end of class.

Returns end of class if successful, nil otherwise"]

	   ["End of clause" py-end-of-clause
	    :help " `py-end-of-clause'
Go to end of clause.

Returns end of clause if successful, nil otherwise"]

	   ["End of def" py-end-of-def
	    :help " `py-end-of-def'
Go to end of def.

Returns end of def if successful, nil otherwise"]

	   ["End of def or class" py-end-of-def-or-class
	    :help " `py-end-of-def-or-class'
Go to end of def-or-class.

Returns end of def-or-class if successful, nil otherwise"]

	   ["End of elif block" py-end-of-elif-block
	    :help " `py-end-of-elif-block'
Go to end of elif-block.

Returns end of elif-block if successful, nil otherwise"]

	   ["End of else block" py-end-of-else-block
	    :help " `py-end-of-else-block'
Go to end of else-block.

Returns end of else-block if successful, nil otherwise"]

	   ["End of except block" py-end-of-except-block
	    :help " `py-end-of-except-block'
Go to end of except-block.

Returns end of except-block if successful, nil otherwise"]

	   ["End of expression" py-end-of-expression
	    :help " `py-end-of-expression'
Go to the end of a compound python expression.

With numeric ARG do it that many times.

A a compound python expression might be concatenated by \".\" operator, thus composed by minor python expressions.

Expression here is conceived as the syntactical component of a statement in Python. See http://docs.python.org/reference

Operators however are left aside resp. limit py-expression designed for edit-purposes."]

	   ["End of if block" py-end-of-if-block
	    :help " `py-end-of-if-block'
Go to end of if-block.

Returns end of if-block if successful, nil otherwise"]

	   ["End of partial expression" py-end-of-partial-expression
	    :help " `py-end-of-partial-expression'"]

	   ["End of statement" py-end-of-statement
	    :help " `py-end-of-statement'
Go to the last char of current statement.

Optional argument REPEAT, the number of loops done already, is checked for py-max-specpdl-size error. Avoid eternal loops due to missing string delimters etc."]

	   ["End of top level" py-end-of-top-level
	    :help " `py-end-of-top-level'
Go to end of top-level form at point.

Returns position if successful, nil otherwise"]

	   ["End of try block" py-end-of-try-block
	    :help " `py-end-of-try-block'
Go to end of try-block.

Returns end of try-block if successful, nil otherwise"]
           )
          ("BOL-forms"
           ("Backward"
	    ["Beginning of block bol" py-beginning-of-block-bol
	     :help " `py-beginning-of-block-bol'
Go to beginning block, go to BOL.

Returns beginning of block if successful, nil otherwise"]

	    ["Beginning of block or clause bol" py-beginning-of-block-or-clause-bol
	     :help " `py-beginning-of-block-or-clause-bol'
Go to beginning block-or-clause, go to BOL.

Returns beginning of block-or-clause if successful, nil otherwise"]

	    ["Beginning of class bol" py-beginning-of-class-bol
	     :help " `py-beginning-of-class-bol'
Go to beginning class, go to BOL.

Returns beginning of class if successful, nil otherwise

When `py-mark-decorators' is non-nil, decorators are considered too."]

	    ["Beginning of clause bol" py-beginning-of-clause-bol
	     :help " `py-beginning-of-clause-bol'
Go to beginning clause, go to BOL.

Returns beginning of clause if successful, nil otherwise"]

	    ["Beginning of def bol" py-beginning-of-def-bol
	     :help " `py-beginning-of-def-bol'
Go to beginning def, go to BOL.

Returns beginning of def if successful, nil otherwise

When `py-mark-decorators' is non-nil, decorators are considered too."]

	    ["Beginning of def or class bol" py-beginning-of-def-or-class-bol
	     :help " `py-beginning-of-def-or-class-bol'
Go to beginning def-or-class, go to BOL.

Returns beginning of def-or-class if successful, nil otherwise

When `py-mark-decorators' is non-nil, decorators are considered too."]

	    ["Beginning of elif block bol" py-beginning-of-elif-block-bol
	     :help " `py-beginning-of-elif-block-bol'
Go to beginning elif-block, go to BOL.

Returns beginning of elif-block if successful, nil otherwise"]

	    ["Beginning of else block bol" py-beginning-of-else-block-bol
	     :help " `py-beginning-of-else-block-bol'
Go to beginning else-block, go to BOL.

Returns beginning of else-block if successful, nil otherwise"]

	    ["Beginning of except block bol" py-beginning-of-except-block-bol
	     :help " `py-beginning-of-except-block-bol'
Go to beginning except-block, go to BOL.

Returns beginning of except-block if successful, nil otherwise"]

	    ["Beginning of expression bol" py-beginning-of-expression-bol
	     :help " `py-beginning-of-expression-bol'"]

	    ["Beginning of if block bol" py-beginning-of-if-block-bol
	     :help " `py-beginning-of-if-block-bol'
Go to beginning if-block, go to BOL.

Returns beginning of if-block if successful, nil otherwise"]

	    ["Beginning of partial expression bol" py-beginning-of-partial-expression-bol
	     :help " `py-beginning-of-partial-expression-bol'"]

	    ["Beginning of statement bol" py-beginning-of-statement-bol
	     :help " `py-beginning-of-statement-bol'
Goto beginning of line where statement starts.
  Returns position reached, if successful, nil otherwise.

See also `py-up-statement': up from current definition to next beginning of statement above."]

	    ["Beginning of try block bol" py-beginning-of-try-block-bol
	     :help " `py-beginning-of-try-block-bol'
Go to beginning try-block, go to BOL.

Returns beginning of try-block if successful, nil otherwise"]
            )
           ("Forward"
	    ["End of block bol" py-end-of-block-bol
	     :help " `py-end-of-block-bol'
Goto beginning of line following end of block.
  Returns position reached, if successful, nil otherwise.

See also `py-down-block': down from current definition to next beginning of block below."]

	    ["End of block or clause bol" py-end-of-block-or-clause-bol
	     :help " `py-end-of-block-or-clause-bol'
Goto beginning of line following end of block-or-clause.
  Returns position reached, if successful, nil otherwise.

See also `py-down-block-or-clause': down from current definition to next beginning of block-or-clause below."]

	    ["End of class bol" py-end-of-class-bol
	     :help " `py-end-of-class-bol'
Goto beginning of line following end of class.
  Returns position reached, if successful, nil otherwise.

See also `py-down-class': down from current definition to next beginning of class below."]

	    ["End of clause bol" py-end-of-clause-bol
	     :help " `py-end-of-clause-bol'
Goto beginning of line following end of clause.
  Returns position reached, if successful, nil otherwise.

See also `py-down-clause': down from current definition to next beginning of clause below."]

	    ["End of def bol" py-end-of-def-bol
	     :help " `py-end-of-def-bol'
Goto beginning of line following end of def.
  Returns position reached, if successful, nil otherwise.

See also `py-down-def': down from current definition to next beginning of def below."]

	    ["End of def or class bol" py-end-of-def-or-class-bol
	     :help " `py-end-of-def-or-class-bol'
Goto beginning of line following end of def-or-class.
  Returns position reached, if successful, nil otherwise.

See also `py-down-def-or-class': down from current definition to next beginning of def-or-class below."]

	    ["End of elif block bol" py-end-of-elif-block-bol
	     :help " `py-end-of-elif-block-bol'
Goto beginning of line following end of elif-block.
  Returns position reached, if successful, nil otherwise.

See also `py-down-elif-block': down from current definition to next beginning of elif-block below."]

	    ["End of else block bol" py-end-of-else-block-bol
	     :help " `py-end-of-else-block-bol'
Goto beginning of line following end of else-block.
  Returns position reached, if successful, nil otherwise.

See also `py-down-else-block': down from current definition to next beginning of else-block below."]

	    ["End of except block bol" py-end-of-except-block-bol
	     :help " `py-end-of-except-block-bol'
Goto beginning of line following end of except-block.
  Returns position reached, if successful, nil otherwise.

See also `py-down-except-block': down from current definition to next beginning of except-block below."]

	    ["End of expression bol" py-end-of-expression-bol
	     :help " `py-end-of-expression-bol'"]

	    ["End of if block bol" py-end-of-if-block-bol
	     :help " `py-end-of-if-block-bol'
Goto beginning of line following end of if-block.
  Returns position reached, if successful, nil otherwise.

See also `py-down-if-block': down from current definition to next beginning of if-block below."]

	    ["End of partial expression bol" py-end-of-partial-expression-bol
	     :help " `py-end-of-partial-expression-bol'"]

	    ["End of statement bol" py-end-of-statement-bol
	     :help " `py-end-of-statement-bol'
Go to the beginning-of-line following current statement."]

	    ["End of top level bol" py-end-of-top-level-bol
	     :help " `py-end-of-top-level-bol'
Go to end of top-level form at point, stop at next beginning-of-line.

Returns position successful, nil otherwise"]

	    ["End of try block bol" py-end-of-try-block-bol
	     :help " `py-end-of-try-block-bol'
Goto beginning of line following end of try-block.
  Returns position reached, if successful, nil otherwise.

See also `py-down-try-block': down from current definition to next beginning of try-block below."]
            ))
          ("Up/Down"
	   ["Up" py-up
	    :help " `py-up'
Go up or to beginning of form if inside.

If inside a delimited form --string or list-- go to its beginning.
If not at beginning of a statement or block, go to its beginning.
If at beginning of a statement or block, go to beginning one level above of compound statement or definition at point."]

	   ["Down" py-down
	    :help " `py-down'
Go to beginning one level below of compound statement or definition at point.

If no statement or block below, but a delimited form --string or list-- go to its beginning. Repeated call from there will behave like down-list.

Returns position if successful, nil otherwise"]
           ))
         ("Hide-Show"
          ("Hide"
	   ["Hide region" py-hide-region
	    :help " `py-hide-region'
Hide active region."]

	   ["Hide statement" py-hide-statement
	    :help " `py-hide-statement'
Hide statement at point."]

	   ["Hide block" py-hide-block
	    :help " `py-hide-block'
Hide block at point."]

	   ["Hide clause" py-hide-clause
	    :help " `py-hide-clause'
Hide clause at point."]

	   ["Hide block or clause" py-hide-block-or-clause
	    :help " `py-hide-block-or-clause'
Hide block-or-clause at point."]

	   ["Hide def" py-hide-def
	    :help " `py-hide-def'
Hide def at point."]

	   ["Hide class" py-hide-class
	    :help " `py-hide-class'
Hide class at point."]

	   ["Hide expression" py-hide-expression
	    :help " `py-hide-expression'
Hide expression at point."]

	   ["Hide partial expression" py-hide-partial-expression
	    :help " `py-hide-partial-expression'
Hide partial-expression at point."]

	   ["Hide line" py-hide-line
	    :help " `py-hide-line'
Hide line at point."]

	   ["Hide top level" py-hide-top-level
	    :help " `py-hide-top-level'
Hide top-level at point."]
           )
          ("Show"
	   ["Show region" py-show-region
	    :help " `py-show-region'
Un-hide active region."]

	   ["Show statement" py-show-statement
	    :help " `py-show-statement'
Show statement at point."]

	   ["Show block" py-show-block
	    :help " `py-show-block'
Show block at point."]

	   ["Show clause" py-show-clause
	    :help " `py-show-clause'
Show clause at point."]

	   ["Show block or clause" py-show-block-or-clause
	    :help " `py-show-block-or-clause'
Show block-or-clause at point."]

	   ["Show def" py-show-def
	    :help " `py-show-def'
Show def at point."]

	   ["Show class" py-show-class
	    :help " `py-show-class'
Show class at point."]

	   ["Show expression" py-show-expression
	    :help " `py-show-expression'
Show expression at point."]

	   ["Show partial expression" py-show-partial-expression
	    :help " `py-show-partial-expression'
Show partial-expression at point."]

	   ["Show line" py-show-line
	    :help " `py-show-line'
Show line at point."]

	   ["Show top level" py-show-top-level
	    :help " `py-show-top-level'
Show top-level at point."]
           ))
         ("Virtualenv"
          ["Virtualenv activate" virtualenv-activate
	   :help " `virtualenv-activate'
Activate the virtualenv located in DIR"]

          ["Virtualenv deactivate" virtualenv-deactivate
	   :help " `virtualenv-deactivate'
Deactivate the current virtual enviroment"]

          ["Virtualenv p" virtualenv-p
	   :help " `virtualenv-p'
Check if a directory is a virtualenv"]

          ["Virtualenv workon" virtualenv-workon
	   :help " `virtualenv-workon'
Issue a virtualenvwrapper-like virtualenv-workon command"]
          )
         ("Help"
          ["Find definition" py-find-definition
	   :help " `py-find-definition'
Find source of definition of SYMBOL.

Interactively, prompt for SYMBOL."]

          ["Help at point" py-help-at-point
	   :help " `py-help-at-point'
Print help on symbol at point.

If symbol is defined in current buffer, jump to it's definition
Optional C-u used for debugging, will prevent deletion of temp file."]

          ["Info lookup symbol" py-info-lookup-symbol
	   :help " `py-info-lookup-symbol'"]

          ["Symbol at point" py-symbol-at-point
	   :help " `py-symbol-at-point'
Return the current Python symbol."]
          )
         ("Customize"

	  ["Python-mode customize group" (customize-group 'python-mode)
	   :help "Open the customization buffer for Python mode"]
	  ("Switches"
	   :help "Toggle useful modes"
	   ("Interpreter"

	    ["Shell prompt read only"
	     (setq py-shell-prompt-read-only
		   (not py-shell-prompt-read-only))
	     :help "If non-nil, the python prompt is read only.  Setting this variable will only effect new shells.Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-shell-prompt-read-only]

	    ["Remove cwd from path"
	     (setq py-remove-cwd-from-path
		   (not py-remove-cwd-from-path))
	     :help "Whether to allow loading of Python modules from the current directory.
If this is non-nil, Emacs removes '' from sys.path when starting
a Python process.  This is the default, for security
reasons, as it is easy for the Python process to be started
without the user's realization (e.g. to perform completion).Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-remove-cwd-from-path]

	    ["Honor IPYTHONDIR "
	     (setq py-honor-IPYTHONDIR-p
		   (not py-honor-IPYTHONDIR-p))
	     :help "When non-nil ipython-history file is constructed by \$IPYTHONDIR
followed by "/history". Default is nil.

Otherwise value of py-ipython-history is used. Use `M-x customize-variable' to set it permanently"
:style toggle :selected py-honor-IPYTHONDIR-p]

	    ["Honor PYTHONHISTORY "
	     (setq py-honor-PYTHONHISTORY-p
		   (not py-honor-PYTHONHISTORY-p))
	     :help "When non-nil python-history file is set by \$PYTHONHISTORY
Default is nil.

Otherwise value of py-python-history is used. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-honor-PYTHONHISTORY-p]

	    ["Enforce py-shell-name" force-py-shell-name-p-on
	     :help "Enforce customized default `py-shell-name' should upon execution. "]

	    ["Don't enforce default interpreter" force-py-shell-name-p-off
	     :help "Make execute commands guess interpreter from environment"]

	    ["Enforce local Python shell " py-force-local-shell-on
	     :help "Locally indicated Python being enforced upon sessions execute commands. "]

	    ["Remove local Python shell enforcement, restore default" py-force-local-shell-off
	     :help "Restore `py-shell-name' default value and `behaviour'. "])

	   ("Execute"

	    ["Fast process" py-fast-process-p
	     :help " `py-fast-process-p'

Use `py-fast-process'\.

Commands prefixed \"py-fast-...\" suitable for large output

See: large output makes Emacs freeze, lp:1253907

Output-buffer is not in comint-mode"
	     :style toggle :selected py-fast-process-p]

	    ["Python mode v5 behavior"
	     (setq python-mode-v5-behavior-p
		   (not python-mode-v5-behavior-p))
	     :help "Execute region through `shell-command-on-region' as
v5 did it - lp:990079. This might fail with certain chars - see UnicodeEncodeError lp:550661

Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected python-mode-v5-behavior-p]

	    ["Force shell name "
	     (setq py-force-py-shell-name-p
		   (not py-force-py-shell-name-p))
	     :help "When `t', execution with kind of Python specified in `py-shell-name' is enforced, possibly shebang doesn't take precedence. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-force-py-shell-name-p]

	    ["Execute \"if name == main\" blocks p"
	     (setq py-if-name-main-permission-p
		   (not py-if-name-main-permission-p))
	     :help " `py-if-name-main-permission-p'

Allow execution of code inside blocks delimited by
if __name__ == '__main__'

Default is non-nil. "
	     :style toggle :selected py-if-name-main-permission-p]

	    ["Ask about save"
	     (setq py-ask-about-save
		   (not py-ask-about-save))
	     :help "If not nil, ask about which buffers to save before executing some code.
Otherwise, all modified buffers are saved without asking.Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-ask-about-save]

	    ["Store result"
	     (setq py-store-result-p
		   (not py-store-result-p))
	     :help " `py-store-result-p'

When non-nil, put resulting string of `py-execute-...' into kill-ring, so it might be yanked. "
	     :style toggle :selected py-store-result-p]

	    ["Prompt on changed "
	     (setq py-prompt-on-changed-p
		   (not py-prompt-on-changed-p))
	     :help "When called interactively, ask for save before a changed buffer is sent to interpreter.

Default is `t'Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-prompt-on-changed-p]

	    ["Dedicated process "
	     (setq py-dedicated-process-p
		   (not py-dedicated-process-p))
	     :help "If commands executing code use a dedicated shell.

Default is nilUse `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-dedicated-process-p]

	    ["Execute without temporary file"
	     (setq py-execute-no-temp-p
		   (not py-execute-no-temp-p))
	     :help " `py-execute-no-temp-p'
Seems Emacs-24.3 provided a way executing stuff without temporary files.
In experimental state yet "
	     :style toggle :selected py-execute-no-temp-p]

	    ["Warn tmp files left "
	     (setq py--warn-tmp-files-left-p
		   (not py--warn-tmp-files-left-p))
	     :help "Messages a warning, when `py-temp-directory' contains files susceptible being left by previous Python-mode sessions. See also lp:987534 Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py--warn-tmp-files-left-p])

	   ("Edit"

	    ("Completion"

	     ["Set Pymacs-based complete keymap "
	      (setq py-set-complete-keymap-p
		    (not py-set-complete-keymap-p))
	      :help "If `py-complete-initialize', which sets up enviroment for Pymacs based py-complete, should load it's keys into `python-mode-map'

Default is nil.
See also resp. edit `py-complete-set-keymap' Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-set-complete-keymap-p]

	     ["Indent no completion "
	      (setq py-indent-no-completion-p
		    (not py-indent-no-completion-p))
	      :help "If completion function should indent when no completion found. Default is `t'

Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-indent-no-completion-p]

	     ["Company pycomplete "
	      (setq py-company-pycomplete-p
		    (not py-company-pycomplete-p))
	      :help "Load company-pycomplete stuff. Default is nilUse `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-company-pycomplete-p])

	    ("Filling"

	     ("Docstring styles"
	      :help "Switch docstring-style"

	      ["Nil" py-set-nil-docstring-style
	       :help " `py-set-nil-docstring-style'

Set py-docstring-style to nil, format string normally. "]

	      ["pep-257-nn" py-set-pep-257-nn-docstring-style
	       :help " `py-set-pep-257-nn-docstring-style'

Set py-docstring-style to 'pep-257-nn "]

	      ["pep-257" py-set-pep-257-docstring-style
	       :help " `py-set-pep-257-docstring-style'

Set py-docstring-style to 'pep-257 "]

	      ["django" py-set-django-docstring-style
	       :help " `py-set-django-docstring-style'

Set py-docstring-style to 'django "]

	      ["onetwo" py-set-onetwo-docstring-style
	       :help " `py-set-onetwo-docstring-style'

Set py-docstring-style to 'onetwo "]

	      ["symmetric" py-set-symmetric-docstring-style
	       :help " `py-set-symmetric-docstring-style'

Set py-docstring-style to 'symmetric "])

	     ["Auto-fill mode"
	      (setq py-auto-fill-mode
		    (not py-auto-fill-mode))
	      :help "Fill according to `py-docstring-fill-column' and `py-comment-fill-column'

Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-auto-fill-mode])

	    ["Use current dir when execute"
	     (setq py-use-current-dir-when-execute-p
		   (not py-use-current-dir-when-execute-p))
	     :help " `toggle-py-use-current-dir-when-execute-p'

Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-use-current-dir-when-execute-p]

	    ("Indent"
	     ("TAB related"

	      ["indent-tabs-mode"
	       (setq indent-tabs-mode
		     (not indent-tabs-mode))
	       :help "Indentation can insert tabs if this is non-nil.

Use `M-x customize-variable' to set it permanently"
	       :style toggle :selected indent-tabs-mode]

	      ["Tab indent"
	       (setq py-tab-indent
		     (not py-tab-indent))
	       :help "Non-nil means TAB in Python mode calls `py-indent-line'.Use `M-x customize-variable' to set it permanently"
	       :style toggle :selected py-tab-indent]

	      ["Tab shifts region "
	       (setq py-tab-shifts-region-p
		     (not py-tab-shifts-region-p))
	       :help "If `t', TAB will indent/cycle the region, not just the current line.

Default is nil
See also `py-tab-indents-region-p'

Use `M-x customize-variable' to set it permanently"
	       :style toggle :selected py-tab-shifts-region-p]

	      ["Tab indents region "
	       (setq py-tab-indents-region-p
		     (not py-tab-indents-region-p))
	       :help "When `t' and first TAB doesn't shift, indent-region is called.

Default is nil
See also `py-tab-shifts-region-p'

Use `M-x customize-variable' to set it permanently"
	       :style toggle :selected py-tab-indents-region-p])

	     ["Close at start column"
	      (setq py-closing-list-dedents-bos
		    (not py-closing-list-dedents-bos))
	      :help "When non-nil, indent list's closing delimiter like start-column.

It will be lined up under the first character of
 the line that starts the multi-line construct, as in:

my_list = \[
    1, 2, 3,
    4, 5, 6,
]

Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-closing-list-dedents-bos]

	     ["Closing list keeps space"
	      (setq py-closing-list-keeps-space
		    (not py-closing-list-keeps-space))
	      :help "If non-nil, closing parenthesis dedents onto column of opening plus `py-closing-list-space', default is nil Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-closing-list-keeps-space]

	     ["Closing list space"
	      (setq py-closing-list-space
		    (not py-closing-list-space))
	      :help "Number of chars, closing parenthesis outdent from opening, default is 1 Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-closing-list-space]

	     ["Tab shifts region "
	      (setq py-tab-shifts-region-p
		    (not py-tab-shifts-region-p))
	      :help "If `t', TAB will indent/cycle the region, not just the current line.

Default is nil
See also `py-tab-indents-region-p'Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-tab-shifts-region-p]

	     ["Lhs inbound indent"
	      (setq py-lhs-inbound-indent
		    (not py-lhs-inbound-indent))
	      :help "When line starts a multiline-assignment: How many colums indent should be more than opening bracket, brace or parenthesis. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-lhs-inbound-indent]

	     ["Continuation offset"
	      (setq py-continuation-offset
		    (not py-continuation-offset))
	      :help "With numeric ARG different from 1 py-continuation-offset is set to that value; returns py-continuation-offset. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-continuation-offset]

	     ["Electric colon"
	      (setq py-electric-colon-active-p
		    (not py-electric-colon-active-p))
	      :help " `py-electric-colon-active-p'

`py-electric-colon' feature.  Default is `nil'. See lp:837065 for discussions. "
	      :style toggle :selected py-electric-colon-active-p]

	     ["Electric colon at beginning of block only"
	      (setq py-electric-colon-bobl-only
		    (not py-electric-colon-bobl-only))
	      :help "When inserting a colon, do not indent lines unless at beginning of block.

Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-electric-colon-bobl-only]

	     ["Electric yank active "
	      (setq py-electric-yank-active-p
		    (not py-electric-yank-active-p))
	      :help " When non-nil, `yank' will be followed by an `indent-according-to-mode'.

Default is nilUse `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-electric-yank-active-p]

	     ["Electric kill backward "
	      (setq py-electric-kill-backward-p
		    (not py-electric-kill-backward-p))
	      :help "Affects `py-electric-backspace'. Default is nil.

If behind a delimited form of braces, brackets or parentheses,
backspace will kill it's contents

With when cursor after
my_string\[0:1]
--------------^

==>

my_string\[]
----------^

In result cursor is insided emptied delimited form.Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-electric-kill-backward-p]

	     ["Trailing whitespace smart delete "
	      (setq py-trailing-whitespace-smart-delete-p
		    (not py-trailing-whitespace-smart-delete-p))
	      :help "Default is nil. When t, python-mode calls
    (add-hook 'before-save-hook 'delete-trailing-whitespace nil 'local)

Also commands may delete trailing whitespace by the way.
When editing other peoples code, this may produce a larger diff than expected Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-trailing-whitespace-smart-delete-p]

	     ["Newline delete trailing whitespace "
	      (setq py-newline-delete-trailing-whitespace-p
		    (not py-newline-delete-trailing-whitespace-p))
	      :help "Delete trailing whitespace maybe left by `py-newline-and-indent'.

Default is `t'. See lp:1100892 Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-newline-delete-trailing-whitespace-p]

	     ["Dedent keep relative column"
	      (setq py-dedent-keep-relative-column
		    (not py-dedent-keep-relative-column))
	      :help "If point should follow dedent or kind of electric move to end of line. Default is t - keep relative position. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-dedent-keep-relative-column]

	     ["Indent paren spanned multilines "
	      (setq py-indent-paren-spanned-multilines-p
		    (not py-indent-paren-spanned-multilines-p))
	      :help "If non-nil, indents elements of list a value of `py-indent-offset' to first element:

def foo():
    if (foo &&
            baz):
        bar()

Default lines up with first element:

def foo():
    if (foo &&
        baz):
        bar()
Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-indent-paren-spanned-multilines-p]

	     ["Indent honors multiline listing"
	      (setq py-indent-honors-multiline-listing
		    (not py-indent-honors-multiline-listing))
	      :help "If `t', indents to 1\+ column of opening delimiter. If `nil', indent adds one level to the beginning of statement. Default is `nil'. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-indent-honors-multiline-listing]

	     ["Indent comment "
	      (setq py-indent-comments
		    (not py-indent-comments))
	      :help "If comments should be indented like code. Default is `nil'.

Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-indent-comments]

	     ["Uncomment indents "
	      (setq py-uncomment-indents-p
		    (not py-uncomment-indents-p))
	      :help "When non-nil, after uncomment indent lines. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-uncomment-indents-p]

	     ["Indent honors inline comment"
	      (setq py-indent-honors-inline-comment
		    (not py-indent-honors-inline-comment))
	      :help "If non-nil, indents to column of inlined comment start.
Default is nil. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-indent-honors-inline-comment]

	     ["Kill empty line"
	      (setq py-kill-empty-line
		    (not py-kill-empty-line))
	      :help "If t, py-indent-forward-line kills empty lines. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-kill-empty-line]

	     ("Smart indentation"
	      :help "Toggle py-smart-indentation'

Use `M-x customize-variable' to set it permanently"

	      ["Toggle py-smart-indentation" toggle-py-smart-indentation
	       :help "Toggles py-smart-indentation

Use `M-x customize-variable' to set it permanently"]

	      ["py-smart-indentation on" py-smart-indentation-on
	       :help "Switches py-smart-indentation on

Use `M-x customize-variable' to set it permanently"]

	      ["py-smart-indentation off" py-smart-indentation-off
	       :help "Switches py-smart-indentation off

Use `M-x customize-variable' to set it permanently"])

	     ["Beep if tab change"
	      (setq py-beep-if-tab-change
		    (not py-beep-if-tab-change))
	      :help "Ring the bell if `tab-width' is changed.
If a comment of the form

                           	# vi:set tabsize=<number>:

is found before the first code line when the file is entered, and the
current value of (the general Emacs variable) `tab-width' does not
equal <number>, `tab-width' is set to <number>, a message saying so is
displayed in the echo area, and if `py-beep-if-tab-change' is non-nil
the Emacs bell is also rung as a warning.Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-beep-if-tab-change]

	     ["Electric comment "
	      (setq py-electric-comment-p
		    (not py-electric-comment-p))
	      :help "If \"#\" should call `py-electric-comment'. Default is `nil'.

Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-electric-comment-p]

	     ["Electric comment add space "
	      (setq py-electric-comment-add-space-p
		    (not py-electric-comment-add-space-p))
	      :help "If py-electric-comment should add a space.  Default is `nil'. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-electric-comment-add-space-p]

	     ["Empty line closes "
	      (setq py-empty-line-closes-p
		    (not py-empty-line-closes-p))
	      :help "When non-nil, dedent after empty line following block

if True:
    print(\"Part of the if-statement\")

print(\"Not part of the if-statement\")

Default is nil

If non-nil, a C-j from empty line dedents.
Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-empty-line-closes-p])
	    ["Defun use top level "
	     (setq py-defun-use-top-level-p
		   (not py-defun-use-top-level-p))
	     :help "When non-nil, keys C-M-a, C-M-e address top-level form.

Beginning- end-of-defun forms use
commands `py-beginning-of-top-level', `py-end-of-top-level'

mark-defun marks top-level form at point etc. "
	     :style toggle :selected py-defun-use-top-level-p]

	    ["Close provides newline"
	     (setq py-close-provides-newline
		   (not py-close-provides-newline))
	     :help "If a newline is inserted, when line after block isn't empty. Default is non-nil. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-close-provides-newline]

	    ["Block comment prefix "
	     (setq py-block-comment-prefix-p
		   (not py-block-comment-prefix-p))
	     :help "If py-comment inserts py-block-comment-prefix.

Default is tUse `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-block-comment-prefix-p])

	   ("Display"

	    ("Index"

	     ["Imenu create index "
	      (setq py--imenu-create-index-p
		    (not py--imenu-create-index-p))
	      :help "Non-nil means Python mode creates and displays an index menu of functions and global variables. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py--imenu-create-index-p]

	     ["Imenu show method args "
	      (setq py-imenu-show-method-args-p
		    (not py-imenu-show-method-args-p))
	      :help "Controls echoing of arguments of functions & methods in the Imenu buffer.
When non-nil, arguments are printed.Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-imenu-show-method-args-p]
	     ["Switch index-function" py-switch-imenu-index-function
	      :help "`py-switch-imenu-index-function'
Switch between `py--imenu-create-index' from 5.1 series and `py--imenu-create-index-new'."])

	    ("Fontification"

	     ["Mark decorators"
	      (setq py-mark-decorators
		    (not py-mark-decorators))
	      :help "If py-mark-def-or-class functions should mark decorators too. Default is `nil'. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-mark-decorators]

	     ["Fontify shell buffer "
	      (setq py-fontify-shell-buffer-p
		    (not py-fontify-shell-buffer-p))
	      :help "If code in Python shell should be highlighted as in script buffer.

Default is nil.

If `t', related vars like `comment-start' will be set too.
Seems convenient when playing with stuff in IPython shell
Might not be TRT when a lot of output arrives Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-fontify-shell-buffer-p]

	     ["Use font lock doc face "
	      (setq py-use-font-lock-doc-face-p
		    (not py-use-font-lock-doc-face-p))
	      :help "If documention string inside of def or class get `font-lock-doc-face'.

`font-lock-doc-face' inherits `font-lock-string-face'.

Call M-x `customize-face' in order to have a visible effect. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-use-font-lock-doc-face-p])

	    ["Switch buffers on execute"
	     (setq py-switch-buffers-on-execute-p
		   (not py-switch-buffers-on-execute-p))
	     :help "When non-nil switch to the Python output buffer.

Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-switch-buffers-on-execute-p]

	    ["Split windows on execute"
	     (setq py-split-window-on-execute
		   (not py-split-window-on-execute))
	     :help "When non-nil split windows.

Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-split-window-on-execute]

	    ["Keep windows configuration"
	     (setq py-keep-windows-configuration
		   (not py-keep-windows-configuration))
	     :help "If a windows is splitted displaying results, this is directed by variable `py-split-window-on-execute'\. Also setting `py-switch-buffers-on-execute-p' affects window-configuration\. While commonly a screen splitted into source and Python-shell buffer is assumed, user may want to keep a different config\.

Setting `py-keep-windows-configuration' to `t' will restore windows-config regardless of settings mentioned above\. However, if an error occurs, it's displayed\.

To suppres window-changes due to error-signaling also: M-x customize-variable RET. Set `py-keep-4windows-configuration' onto 'force

Default is nil Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-keep-windows-configuration]

	    ["Which split windows on execute function"
	     (progn
	       (if (eq 'split-window-vertically py-split-windows-on-execute-function)
		   (setq py-split-windows-on-execute-function'split-window-horizontally)
		 (setq py-split-windows-on-execute-function 'split-window-vertically))
	       (message "py-split-windows-on-execute-function set to: %s" py-split-windows-on-execute-function))

	     :help "If `split-window-vertically' or `...-horizontally'. Use `M-x customize-variable' RET `py-split-windows-on-execute-function' RET to set it permanently"
	     :style toggle :selected py-split-windows-on-execute-function]

	    ["Modeline display full path "
	     (setq py-modeline-display-full-path-p
		   (not py-modeline-display-full-path-p))
	     :help "If the full PATH/TO/PYTHON should be displayed in shell modeline.

Default is nil. Note: when `py-shell-name' is specified with path, it's shown as an acronym in buffer-name already. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-modeline-display-full-path-p]

	    ["Modeline acronym display home "
	     (setq py-modeline-acronym-display-home-p
		   (not py-modeline-acronym-display-home-p))
	     :help "If the modeline acronym should contain chars indicating the home-directory.

Default is nil Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-modeline-acronym-display-home-p]

	    ["Hide show hide docstrings"
	     (setq py-hide-show-hide-docstrings
		   (not py-hide-show-hide-docstrings))
	     :help "Controls if doc strings can be hidden by hide-showUse `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-hide-show-hide-docstrings]

	    ["Hide comments when hiding all"
	     (setq py-hide-comments-when-hiding-all
		   (not py-hide-comments-when-hiding-all))
	     :help "Hide the comments too when you do `hs-hide-all'. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-hide-comments-when-hiding-all]

	    ["Max help buffer "
	     (setq py-max-help-buffer-p
		   (not py-max-help-buffer-p))
	     :help "If \"\*Python-Help\*\"-buffer should appear as the only visible.

Default is nil. In help-buffer, \"q\" will close it.  Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-max-help-buffer-p]

	    ["Current defun show"
	     (setq py-current-defun-show
		   (not py-current-defun-show))
	     :help "If `py-current-defun' should jump to the definition, highlight it while waiting PY-WHICH-FUNC-DELAY seconds, before returning to previous position.

Default is `t'.Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-current-defun-show]

	    ["Match paren mode"
	     (setq py-match-paren-mode
		   (not py-match-paren-mode))
	     :help "Non-nil means, cursor will jump to beginning or end of a block.
This vice versa, to beginning first.
Sets `py-match-paren-key' in python-mode-map.
Customize `py-match-paren-key' which key to use. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-match-paren-mode])

	   ("Debug"

	    ["py-debug-p"
	     (setq py-debug-p
		   (not py-debug-p))
	     :help "When non-nil, keep resp\. store information useful for debugging\.

Temporary files are not deleted\. Other functions might implement
some logging etc\. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-debug-p]

	    ["Pdbtrack do tracking "
	     (setq py-pdbtrack-do-tracking-p
		   (not py-pdbtrack-do-tracking-p))
	     :help "Controls whether the pdbtrack feature is enabled or not.
When non-nil, pdbtrack is enabled in all comint-based buffers,
e.g. shell buffers and the \*Python\* buffer.  When using pdb to debug a
Python program, pdbtrack notices the pdb prompt and displays the
source file and line that the program is stopped at, much the same way
as gud-mode does for debugging C programs with gdb.Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-pdbtrack-do-tracking-p]

	    ["Jump on exception"
	     (setq py-jump-on-exception
		   (not py-jump-on-exception))
	     :help "Jump to innermost exception frame in Python output buffer.
When this variable is non-nil and an exception occurs when running
Python code synchronously in a subprocess, jump immediately to the
source code of the innermost traceback frame.

Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-jump-on-exception]

	    ["Highlight error in source "
	     (setq py-highlight-error-source-p
		   (not py-highlight-error-source-p))
	     :help "Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-highlight-error-source-p])

	   ("Other"

	    ("Directory"

	     ["Guess install directory "
	      (setq py-guess-py-install-directory-p
		    (not py-guess-py-install-directory-p))
	      :help "If in cases, `py-install-directory' isn't set,  `py-set-load-path'should guess it from `buffer-file-name'. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-guess-py-install-directory-p]

	     ["Use local default"
	      (setq py-use-local-default
		    (not py-use-local-default))
	      :help "If `t', py-shell will use `py-shell-local-path' instead
of default Python.

Making switch between several virtualenv's easier,
                               `python-mode' should deliver an installer, so named-shells pointing to virtualenv's will be available. Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-use-local-default]

	     ["Use current dir when execute "
	      (setq py-use-current-dir-when-execute-p
		    (not py-use-current-dir-when-execute-p))
	      :help "When `t', current directory is used by Python-shell for output of `py-execute-buffer' and related commands.

See also `py-execute-directory'Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-use-current-dir-when-execute-p]

	     ["Keep shell dir when execute "
	      (setq py-keep-shell-dir-when-execute-p
		    (not py-keep-shell-dir-when-execute-p))
	      :help "Don't change Python shell's current working directory when sending code.

See also `py-execute-directory'Use `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-keep-shell-dir-when-execute-p]

	     ["Fileless buffer use default directory "
	      (setq py-fileless-buffer-use-default-directory-p
		    (not py-fileless-buffer-use-default-directory-p))
	      :help "When `py-use-current-dir-when-execute-p' is non-nil and no buffer-file exists, value of `default-directory' sets current working directory of Python output shellUse `M-x customize-variable' to set it permanently"
	      :style toggle :selected py-fileless-buffer-use-default-directory-p])

	    ("Underscore word syntax"
	     :help "Toggle `py-underscore-word-syntax-p'"

	     ["Toggle underscore word syntax" toggle-py-underscore-word-syntax-p
	      :help " `toggle-py-underscore-word-syntax-p'

If `py-underscore-word-syntax-p' should be on or off.

  Returns value of `py-underscore-word-syntax-p' switched to. .

Use `M-x customize-variable' to set it permanently"]

	     ["Underscore word syntax on" py-underscore-word-syntax-p-on
	      :help " `py-underscore-word-syntax-p-on'

Make sure, py-underscore-word-syntax-p' is on.

Returns value of `py-underscore-word-syntax-p'. .

Use `M-x customize-variable' to set it permanently"]

	     ["Underscore word syntax off" py-underscore-word-syntax-p-off
	      :help " `py-underscore-word-syntax-p-off'

Make sure, `py-underscore-word-syntax-p' is off.

Returns value of `py-underscore-word-syntax-p'. .

Use `M-x customize-variable' to set it permanently"])

	    ["Load pymacs "
	     (setq py-load-pymacs-p
		   (not py-load-pymacs-p))
	     :help "If Pymacs related stuff should be loaded.

Default is nil.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.caUse `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-load-pymacs-p]

	    ["Verbose "
	     (setq py-verbose-p
		   (not py-verbose-p))
	     :help "If functions should report results.

Default is nil. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-verbose-p]

	    ["Empty comment line separates paragraph "
	     (setq py-empty-comment-line-separates-paragraph-p
		   (not py-empty-comment-line-separates-paragraph-p))
	     :help "Consider paragraph start/end lines with nothing inside but comment sign.

Default is non-nilUse `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-empty-comment-line-separates-paragraph-p]

	    ["Org cycle "
	     (setq py-org-cycle-p
		   (not py-org-cycle-p))
	     :help "When non-nil, command `org-cycle' is available at shift-TAB, <backtab>

Default is nil. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-org-cycle-p]

	    ["Set pager cat"
	     (setq py-set-pager-cat-p
		   (not py-set-pager-cat-p))
	     :help "If the shell environment variable \$PAGER should set to `cat'.

If `t', use `C-c C-r' to jump to beginning of output. Then scroll normally.

Avoids lp:783828, \"Terminal not fully functional\", for help('COMMAND') in python-shell

When non-nil, imports module `os' Use `M-x customize-variable' to
set it permanently"
	     :style toggle :selected py-set-pager-cat-p]

	    ["Edit only "
	     (setq py-edit-only-p
		   (not py-edit-only-p))
	     :help "When `t' `python-mode' will not take resort nor check for installed Python executables. Default is nil.

See bug report at launchpad, lp:944093. Use `M-x customize-variable' to set it permanently"
	     :style toggle :selected py-edit-only-p])))
         ("Other"
          ["Boolswitch" py-boolswitch
	   :help " `py-boolswitch'
Edit the assignment of a boolean variable, revert them.

I.e. switch it from \"True\" to \"False\" and vice versa"]

          ["Empty out list backward" py-empty-out-list-backward
	   :help " `py-empty-out-list-backward'
Deletes all elements from list before point."]

          ["Kill buffer unconditional" py-kill-buffer-unconditional
	   :help " `py-kill-buffer-unconditional'
Kill buffer unconditional, kill buffer-process if existing."]

          ["Remove overlays at point" py-remove-overlays-at-point
	   :help " `py-remove-overlays-at-point'
Remove overlays as set when `py-highlight-error-source-p' is non-nil."]
          ("Electric"
	   ["Complete electric comma" py-complete-electric-comma
	    :help " `py-complete-electric-comma'"]

	   ["Complete electric lparen" py-complete-electric-lparen
	    :help " `py-complete-electric-lparen'"]

	   ["Electric backspace" py-electric-backspace
	    :help " `py-electric-backspace'
Delete preceding character or level of indentation.

With ARG do that ARG times.
Returns column reached."]

	   ["Electric colon" py-electric-colon
	    :help " `py-electric-colon'
Insert a colon and indent accordingly.

If a numeric argument ARG is provided, that many colons are inserted
non-electrically.

Electric behavior is inhibited inside a string or
comment or by universal prefix C-u.

Switched by `py-electric-colon-active-p', default is nil
See also `py-electric-colon-greedy-p'"]

	   ["Electric comment" py-electric-comment
	    :help " `py-electric-comment'
Insert a comment. If starting a comment, indent accordingly.

If a numeric argument ARG is provided, that many \"#\" are inserted
non-electrically.
With C-u \"#\" electric behavior is inhibited inside a string or comment."]

	   ["Electric delete" py-electric-delete
	    :help " `py-electric-delete'
Delete following character or levels of whitespace.

With ARG do that ARG times."]

	   ["Electric yank" py-electric-yank
	    :help " `py-electric-yank'
Perform command `yank' followed by an `indent-according-to-mode'"]

	   ["Hungry delete backwards" py-hungry-delete-backwards
	    :help " `py-hungry-delete-backwards'
Delete the preceding character or all preceding whitespace
back to the previous non-whitespace character.
See also C-c <delete>."]

	   ["Hungry delete forward" py-hungry-delete-forward
	    :help " `py-hungry-delete-forward'
Delete the following character or all following whitespace
up to the next non-whitespace character.
See also C-c <C-backspace>."]
            )
          ("Abbrevs"	   :help "see also `py-add-abbrev'"
	   :filter (lambda (&rest junk)
		     (abbrev-table-menu python-mode-abbrev-table))            )

          ["Add abbrev" py-add-abbrev
	   :help " `py-add-abbrev'
Defines python-mode specific abbrev for last expressions before point.
Argument is how many `py-partial-expression's form the expansion; or zero means the region is the expansion.

Reads the abbreviation in the minibuffer; with numeric arg it displays a proposal for an abbrev.
Proposal is composed from the initial character(s) of the
expansion.

Don't use this function in a Lisp program; use `define-abbrev' instead."]
          ("Completion"
	   ["Py indent or complete" py-py-indent-or-complete
	    :help " `py-py-indent-or-complete'"]

	   ["Py shell complete" py-py-shell-complete
	    :help " `py-py-shell-complete'"]

	   ["Py complete" py-py-complete
	    :help " `py-py-complete'"]
            )))))

;; python-components-foot

(defun py-shell-fontify ()
  "Fontifies input in shell buffer. "
  ;; causes delay in fontification until next trigger
  ;; (unless (or (member (char-before) (list 32 ?: ?\)))
  ;; (unless (and (eq last-command 'self-insert-command) (eq (char-before) 32))
  ;; (< (abs (save-excursion (skip-chars-backward "^ \t\r\n\f"))) 2))
  (let* ((pps (parse-partial-sexp (line-beginning-position) (point)))
	 (start (if (and (nth 8 pps) (nth 1 pps))
		    (max (nth 1 pps) (nth 8 pps))
		  (or (nth 1 pps) (nth 8 pps)))))
    (when (or start
	      (setq start (ignore-errors (cdr comint-last-prompt))))
      (let* ((input (buffer-substring-no-properties
		     start (point-max)))
	     (buffer-undo-list t)
	     (replacement
	      (save-current-buffer
		(set-buffer py-shell--font-lock-buffer)
		(erase-buffer)
		(insert input)
		;; Ensure buffer is fontified, keeping it
		;; compatible with Emacs < 24.4.
		(if (fboundp 'font-lock-ensure)
		    (funcall 'font-lock-ensure)
		  (font-lock-default-fontify-buffer))
		(buffer-substring (point-min) (point-max))))
	     (replacement-length (length replacement))
	     (i 0))
	;; Inject text properties to get input fontified.
	(while (not (= i replacement-length))
	  (let* ((plist (text-properties-at i replacement))
		 (next-change (or (next-property-change i replacement)
				  replacement-length))
		 (plist (let ((face (plist-get plist 'face)))
			  (if (not face)
			      plist
			    ;; Replace FACE text properties with
			    ;; FONT-LOCK-FACE so input is fontified.
			    (plist-put plist 'face nil)
			    (plist-put plist 'font-lock-face face)))))
	    (set-text-properties
	     (+ start i) (+ start next-change) plist)
	    (setq i next-change)))))))

(defun py-message-which-python-mode ()
  (if (buffer-file-name)
      (if (string= "python-mode-el" (buffer-file-name))
	  (message "%s" "python-mode loaded from python-mode-el")
	(message "%s" "python-mode loaded from python-components-mode"))
    (message "python-mode loaded from: %s" python-mode-message-string)))

;;;###autoload
(define-derived-mode py-auto-completion-mode python-mode "Pac"
  "Run auto-completion"
  ;; disable company
  ;; (when company-mode (company-mode))
  (if py-auto-completion-mode-p
      (progn
	(setq py-auto-completion-mode-p nil
	      py-auto-completion-buffer nil)
	(when (timerp py--auto-complete-timer)(cancel-timer py--auto-complete-timer)))
    (setq py-auto-completion-mode-p t
	  py-auto-completion-buffer (current-buffer))
    (setq py--auto-complete-timer
	  (run-with-idle-timer
	   py--auto-complete-timer-delay
	   ;; 1
	   t
	   #'py-complete-auto)))
  (force-mode-line-update))

;;;###autoload
(define-derived-mode python-mode prog-mode python-mode-modeline-display
  "Major mode for editing Python files.

To submit a problem report, enter `\\[py-submit-bug-report]' from a
`python-mode' buffer.  Do `\\[py-describe-mode]' for detailed
documentation.  To see what version of `python-mode' you are running,
enter `\\[py-version]'.

This mode knows about Python indentation, tokens, comments and
continuation lines.  Paragraphs are separated by blank lines only.

COMMANDS

`py-shell'\tStart an interactive Python interpreter in another window
`py-execute-statement'\tSend statement at point to Python default interpreter
`py-backward-statement'\tGo to the initial line of a simple statement

etc.

See available commands listed in files commands-python-mode at directory doc

VARIABLES

`py-indent-offset'	indentation increment
`py-shell-name'		shell command to invoke Python interpreter
`py-split-window-on-execute'		When non-nil split windows
`py-switch-buffers-on-execute-p'	When non-nil switch to the Python output buffer

See available customizations listed in files variables-python-mode at directory doc

\\{python-mode-map}"
  :group 'python-mode
  ;; Local vars
  (set (make-local-variable 'electric-indent-inhibit) nil)
  (set (make-local-variable 'outline-regexp)
       (concat (mapconcat 'identity
                          (mapcar #'(lambda (x) (concat "^\\s-*" x "\\_>"))
                                  py-outline-mode-keywords)
                          "\\|")))
  (when (>= emacs-major-version 25)
    (global-eldoc-mode -1))
  (if py-use-font-lock-doc-face-p
      (set (make-local-variable 'font-lock-defaults)
           '(python-font-lock-keywords nil nil nil nil
				       (font-lock-syntactic-keywords
					. py-font-lock-syntactic-keywords)
				       (font-lock-syntactic-face-function
					. py--font-lock-syntactic-face-function)))
    (set (make-local-variable 'font-lock-defaults)
         '(python-font-lock-keywords nil nil nil nil
				     (font-lock-syntactic-keywords
				      . py-font-lock-syntactic-keywords))))
  ;; avoid to run py-choose-shell again from `py--fix-start'
  (cond ((string-match "ython3" py-python-edit-version)
	 (font-lock-add-keywords 'python-mode
				 '(("\\<print\\>" . 'py-builtins-face)
				   ("\\<file\\>" . nil))))
	(t (font-lock-add-keywords 'python-mode
				   '(("\\<print\\>" . 'font-lock-keyword-face)
				     ("\\<file\\>" . 'py-builtins-face)))))
  (set (make-local-variable 'which-func-functions) 'py-which-def-or-class)
  (set (make-local-variable 'parse-sexp-lookup-properties) t)
  (set (make-local-variable 'comment-use-syntax) t)
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-start-skip) "^[ \t]*#+ *")

  (if py-empty-comment-line-separates-paragraph-p
      (progn
        (set (make-local-variable 'paragraph-separate) (concat "\f\\|^[ \t]*$\\|^[ \t]*" comment-start "[ \t]*$\\|^[ \t\f]*:[[:alpha:]]+ [[:alpha:]]+:.+$"))
        (set (make-local-variable 'paragraph-start)
	     (concat "\f\\|^[ \t]*$\\|^[ \t]*" comment-start "[ \t]*$\\|^[ \t\f]*:[[:alpha:]]+ [[:alpha:]]+:.+$"))
	(set (make-local-variable 'paragraph-separate)
	     (concat "\f\\|^[ \t]*$\\|^[ \t]*" comment-start "[ \t]*$\\|^[ \t\f]*:[[:alpha:]]+ [[:alpha:]]+:.+$")))
    ;; (progn
    ;;   (set (make-local-variable 'paragraph-separate) "\f\\|^[ \t]*$\\|^[ \t]*#[ \t]*$\\|^[ \t\f]*:[[:alpha:]]+ [[:alpha:]]+:.+$")
    ;;   (set (make-local-variable 'paragraph-start) "\f\\|^[ \t]*$\\|^[ \t]*#[ \t]*$\\|^[ \t\f]*:[[:alpha:]]+ [[:alpha:]]+:.+$"))
    (set (make-local-variable 'paragraph-separate) "\f\\|^[ \t]*$\\|^[ \t]*#[ \t]*$\\|^[ \t\f]*:[[:alpha:]]+ [[:alpha:]]+:.+$")
    (set (make-local-variable 'paragraph-start) "\f\\|^[ \t]*$\\|^[ \t]*#[ \t]*$\\|^[ \t\f]*:[[:alpha:]]+ [[:alpha:]]+:.+$"))
  (set (make-local-variable 'comment-column) 40)
  (set (make-local-variable 'comment-indent-function) #'py--comment-indent-function)
  (set (make-local-variable 'indent-region-function) 'py-indent-region)
  (set (make-local-variable 'indent-line-function) 'py-indent-line)
  (set (make-local-variable 'hs-hide-comments-when-hiding-all) 'py-hide-comments-when-hiding-all)
  (set (make-local-variable 'outline-heading-end-regexp) ":[^\n]*\n")
  (set (make-local-variable 'open-paren-in-column-0-is-defun-start) nil)
  (set (make-local-variable 'add-log-current-defun-function) 'py-current-defun)
  (set (make-local-variable 'fill-paragraph-function) 'py-fill-paragraph)
  (set (make-local-variable 'require-final-newline) mode-require-final-newline)
  (set (make-local-variable 'tab-width) py-indent-offset)
  (set (make-local-variable 'eldoc-documentation-function)
       #'py-eldoc-function)
  (and py-load-skeletons-p
       (py-load-skeletons)
       (set (make-local-variable 'skeleton-further-elements)
            '((< '(backward-delete-char-untabify (min py-indent-offset
                                                      (current-column))))
              (^ '(- (1+ (current-indentation)))))))
  (and py-guess-py-install-directory-p (py-set-load-path))
  (and py-autopair-mode
       (load-library "autopair")
       (add-hook 'python-mode-hook
                 #'(lambda ()
                     (setq autopair-handle-action-fns
                           (list #'autopair-default-handle-action
                                 #'autopair-python-triple-quote-action))))
       (py-autopair-mode-on))
  (when py-trailing-whitespace-smart-delete-p
    (add-hook 'before-save-hook 'delete-trailing-whitespace nil 'local))
  (when py-pdbtrack-do-tracking-p
    (add-hook 'comint-output-filter-functions 'py--pdbtrack-track-stack-file))
  (cond
   (py-complete-function
    (add-hook 'completion-at-point-functions
              py-complete-function nil 'local))
   (py-load-pymacs-p
    (add-hook 'completion-at-point-functions
              'py-complete-completion-at-point nil 'local))
   (t
    (add-hook 'completion-at-point-functions
              'py-shell-complete nil 'local)))
  ;; (if py-auto-complete-p
  ;; (add-hook 'python-mode-hook 'py--run-completion-timer)
  ;; (remove-hook 'python-mode-hook 'py--run-completion-timer))
  ;; (when py-auto-complete-p
  ;; (add-hook 'python-mode-hook
  ;; (lambda ()
  ;; (run-with-idle-timer 1 t 'py-shell-complete))))
  (if py-auto-fill-mode
      (add-hook 'python-mode-hook 'py--run-auto-fill-timer)
    (remove-hook 'python-mode-hook 'py--run-auto-fill-timer))

  ;; caused insert-file-contents error lp:1293172
  ;;  (add-hook 'after-change-functions 'py--after-change-function nil t)
  (if py-defun-use-top-level-p
      (progn
        (set (make-local-variable 'beginning-of-defun-function) 'py-backward-top-level)
        (set (make-local-variable 'end-of-defun-function) 'py-end-of-top-level)
        (define-key python-mode-map [(control meta a)] 'py-backward-top-level)
        (define-key python-mode-map [(control meta e)] 'py-end-of-top-level))
    (set (make-local-variable 'beginning-of-defun-function) 'py-backward-def-or-class)
    (set (make-local-variable 'end-of-defun-function) 'py-end-of-def-or-class)
    (define-key python-mode-map [(control meta a)] 'py-backward-def-or-class)
    (define-key python-mode-map [(control meta e)] 'py-end-of-def-or-class))
  (when py-sexp-use-expression-p
    (define-key python-mode-map [(control meta f)] 'py-forward-expression)
    (define-key python-mode-map [(control meta b)] 'py-backward-expression))
  (when (and py--imenu-create-index-p
             (fboundp 'imenu-add-to-menubar)
             (ignore-errors (require 'imenu)))
    (setq imenu-create-index-function 'py--imenu-create-index-function)
    (setq imenu--index-alist (funcall py--imenu-create-index-function))
    ;; fallback
    (unless imenu--index-alist
      (setq imenu--index-alist (py--imenu-create-index-new)))
    ;; (message "imenu--index-alist: %s" imenu--index-alist)
    (imenu-add-to-menubar "PyIndex"))
  (when py-hide-show-minor-mode-p (hs-minor-mode 1))
  (when py-outline-minor-mode-p (outline-minor-mode 1))
  (when (interactive-p)
    (py-message-which-python-mode))
  (force-mode-line-update))

(defun py--shell-setup-fontification (&optional style)
  "Expected values are either nil, 'all or 'input. "
  (setq style (or style py-shell-fontify-style))
  (if style
      (progn
	(cond ((eq 'all style)
	       (remove-hook 'change-major-mode-hook 'font-lock-defontify)
	       (set (make-local-variable 'py--shell-unfontify) 'py-shell-unfontify-p)
	       (when py--shell-unfontify
	       	 (add-hook 'py-python-shell-mode-hook #'py--run-unfontify-timer (current-buffer)))
	       (remove-hook 'post-command-hook 'py-shell-fontify t)
	       (set (make-local-variable 'font-lock-defaults)
		    '(python-font-lock-keywords nil nil nil nil
						(font-lock-syntactic-keywords
						 . py-font-lock-syntactic-keywords)))
	       (if (fboundp 'font-lock-ensure)
		   (funcall 'font-lock-ensure)
		 (font-lock-default-fontify-buffer)))
	      ;; style is 'input, prepare `py-shell-fontify'
	      (t (set (make-local-variable 'delay-mode-hooks) t)
		 (save-current-buffer
		   ;; Prepare the buffer where the input is fontified
		   (set-buffer (get-buffer-create py-shell--font-lock-buffer))
		   (font-lock-mode 1)
		   (python-mode))
		 ;; post-self-insert-hook
		 (add-hook 'post-command-hook
			   #'py-shell-fontify nil 'local)))
	(force-mode-line-update))
    ;; no fontification in py-shell
    (remove-hook 'py-python-shell-mode-hook 'py--run-unfontify-timer t)
    (remove-hook 'post-command-hook 'py-shell-fontify t)))

(defun py--all-shell-mode-setting ()
  (py--shell-setup-fontification)
  (setenv "PAGER" "cat")
  (setenv "TERM" "dumb")
  (set-syntax-table python-mode-syntax-table)
  (if py-auto-complete-p
      (add-hook 'py-shell-mode-hook 'py--run-completion-timer)
    (remove-hook 'py-shell-mode-hook 'py--run-completion-timer))
  ;; comint settings
  (set (make-local-variable 'comint-prompt-regexp)
       (cond ((string-match "[iI][pP]ython[[:alnum:]*-]*$" py-buffer-name)
	      (concat "\\("
		      (mapconcat 'identity
				 (delq nil (list py-shell-input-prompt-1-regexp py-shell-input-prompt-2-regexp py-ipython-input-prompt-re py-ipython-output-prompt-re py-pdbtrack-input-prompt py-pydbtrack-input-prompt))
				 "\\|")
		      "\\)"))
	     (t (concat "\\("
			(mapconcat 'identity
				   (delq nil (list py-shell-input-prompt-1-regexp py-shell-input-prompt-2-regexp py-pdbtrack-input-prompt py-pydbtrack-input-prompt))
				   "\\|")
			"\\)"))))
  (remove-hook 'comint-output-filter-functions 'font-lock-extend-jit-lock-region-after-change t)
  ;; (set (make-local-variable 'comint-output-filter-functions)
  ;; 'set-text-properties comint-last-input-start comint-last-input-end 'nil)
  (set (make-local-variable 'comint-input-filter) 'py-history-input-filter)
  (set (make-local-variable 'comint-prompt-read-only) py-shell-prompt-read-only)
  ;; (set (make-local-variable 'comint-use-prompt-regexp) nil)
  (set (make-local-variable 'compilation-error-regexp-alist)
       py-compilation-regexp-alist)
  (set (make-local-variable 'comment-start) "# ")
  (set (make-local-variable 'comment-start-skip) "^[ \t]*#+ *")
  (set (make-local-variable 'comment-column) 40)
  (set (make-local-variable 'comment-indent-function) #'py--comment-indent-function)
  (set (make-local-variable 'indent-region-function) 'py-indent-region)
  (set (make-local-variable 'indent-line-function) 'py-indent-line)
  (set (make-local-variable 'inhibit-point-motion-hooks) t)
  (set (make-local-variable 'comint-input-sender) 'py--shell-simple-send))

;;;###autoload
(define-derived-mode py-python-shell-mode comint-mode "Py"
  "Major mode for interacting with a Python process.
A Python process can be started with \\[py-shell].

You can send text to the Python process from other buffers
containing Python source.
 * \\[py-execute-region] sends the current region to the Python process.

Sets basic comint variables, see also versions-related stuff in `py-shell'.
\\{py-python-shell-mode-map}"
  :group 'python-mode
  ;; (require 'ansi-color) ; for ipython
  (setq mode-line-process '(":%s"))
  ;; (sit-for 0.1)
  (when py-verbose-p (message "%s" "Initializing Python shell, please wait"))
  (py--all-shell-mode-setting)
  (py--python-send-completion-setup-code)
  (py--python-send-ffap-setup-code)
  (py--python-send-eldoc-setup-code)
  (set-process-sentinel (get-buffer-process (current-buffer)) #'shell-write-history-on-exit)

  ;; (setq comint-input-ring-file-name
  ;;       (cond ((string-match "[iI][pP]ython[[:alnum:]*-]*$" py-buffer-name)
  ;;              (if py-honor-IPYTHONDIR-p
  ;;                  (if (getenv "IPYTHONDIR")
  ;;                      (concat (getenv "IPYTHONDIR") "/history")
  ;;                    py-ipython-history)
  ;;                py-ipython-history))
  ;;             (t
  ;;              (if py-honor-PYTHONHISTORY-p
  ;;                  (if (getenv "PYTHONHISTORY")
  ;;                      (concat (getenv "PYTHONHISTORY") "/" (py--report-executable py-buffer-name) "_history")
  ;;                    py-ipython-history)
  ;;                py-ipython-history)))
  ;;)
  (comint-read-input-ring t)
  (compilation-shell-minor-mode 1)
  ;;
  (if py-complete-function
      (progn
  	(add-hook 'completion-at-point-functions
  		  py-complete-function nil 'local)
  	(push py-complete-function comint-dynamic-complete-functions))
    (add-hook 'completion-at-point-functions
              'py-shell-complete nil 'local)
    (push 'py-shell-complete  comint-dynamic-complete-functions))
  (when py-sexp-use-expression-p
    (define-key py-python-shell-mode-map [(control meta f)] 'py-forward-expression)
    (define-key py-python-shell-mode-map [(control meta b)] 'py-backward-expression))
  (force-mode-line-update))

;;;###autoload
(define-derived-mode py-ipython-shell-mode comint-mode "IPy"
  "Major mode for interacting with a Python process.
A Python process can be started with \\[py-shell].

You can send text to the Python process from other buffers
containing Python source.
 * \\[py-execute-region] sends the current region to the Python process.

Sets basic comint variables, see also versions-related stuff in `py-shell'.
\\{py-ipython-shell-mode-map}"
  :group 'python-mode
  ;; (require 'ansi-color) ; for ipython
  (setq mode-line-process '(":%s"))
  (when py-verbose-p (message "%s" "Initializing IPython shell, please wait"))
  ;; (set (make-local-variable 'inhibit-eol-conversion) (getenv "PYTHONUNBUFFERED"))
  (set (make-local-variable 'inhibit-eol-conversion) t)
  (py--all-shell-mode-setting)
  (py--python-send-completion-setup-code)
  (py--python-send-ffap-setup-code)
  (py--python-send-eldoc-setup-code)
  (py--ipython-import-module-completion)
  (py-set-ipython-completion-command-string (process-name (get-buffer-process (current-buffer))))
  (sit-for 0.1 t)
  (comint-read-input-ring t)
  (compilation-shell-minor-mode 1)
  (if py-complete-function
      (progn
  	(add-hook 'completion-at-point-functions
  		  py-complete-function nil 'local)
  	(push py-complete-function  comint-dynamic-complete-functions))
    (add-hook 'completion-at-point-functions
              'py-shell-complete nil 'local)
    (push 'py-shell-complete  comint-dynamic-complete-functions))
  (sit-for 0.5 t)
  (force-mode-line-update))

(defalias 'py-backward-decorator-bol 'py-backward-decorator)
(defalias 'py-beginning-of-block 'py-backward-block)
(defalias 'py-beginning-of-block-bol 'py-backward-block-bol)
(defalias 'py-beginning-of-block-or-clause 'py-backward-block-or-clause)
(defalias 'py-beginning-of-class 'py-backward-class)
(defalias 'py-beginning-of-class-bol 'py-backward-class-bol)
(defalias 'py-beginning-of-clause 'py-backward-clause)
(defalias 'py-beginning-of-clause-bol 'py-backward-clause-bol)
(defalias 'py-beginning-of-comment 'py-backward-comment)
(defalias 'py-beginning-of-declarations 'py-backward-declarations)
(defalias 'py-beginning-of-decorator 'py-backward-decorator)
(defalias 'py-beginning-of-decorator-bol 'py-backward-decorator)
(defalias 'py-beginning-of-def-or-class 'py-backward-def-or-class)
(defalias 'py-beginning-of-expression 'py-backward-expression)
(defalias 'py-beginning-of-line 'py-backward-line)
(defalias 'py-beginning-of-minor-block 'py-backward-minor-block)
(defalias 'py-beginning-of-partial-expression 'py-backward-partial-expression)
(defalias 'py-beginning-of-section 'py-backward-section)
(defalias 'py-beginning-of-statement 'py-backward-statement)
(defalias 'py-beginning-of-statement-bol 'py-backward-statement-bol)
(defalias 'py-beginning-of-top-level 'py-backward-top-level)
(defalias 'py-end-of-block 'py-forward-block)
(defalias 'py-end-of-block-or-clause 'py-forward-block-or-clause)
(defalias 'py-end-of-class 'py-forward-class)
(defalias 'py-end-of-clause 'py-forward-clause)
(defalias 'py-end-of-comment 'py-forward-comment)
(defalias 'py-end-of-decorator 'py-forward-decorator)
(defalias 'py-end-of-def-or-class 'py-forward-def-or-class)
(defalias 'py-end-of-expression 'py-forward-expression)
(defalias 'py-end-of-line 'py-forward-line)
(defalias 'py-end-of-partial-expression 'py-forward-partial-expression)
(defalias 'py-end-of-section 'py-forward-section)
(defalias 'py-end-of-statement 'py-forward-statement)
(defalias 'py-end-of-statement-bol 'py-forward-statement-bol)
(defalias 'py-end-of-top-level 'py-forward-top-level)
(defalias 'py-next-statement 'py-forward-statement)
(defalias 'py-markup-region-as-section 'py-sectionize-region)
(defalias 'py-up 'py-up-block)

;;;
(provide 'python-mode)
;;; python-mode.el ends here
