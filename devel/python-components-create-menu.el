;;; python-components-create-menu.el - Generate the menu

;; Copyright (C) 2015  Andreas Röhler

;; Author: Andreas Röhler <andreas.roehler@online.de>

;; Keywords: languages, processes, python, oop

;; Python-components-mode started from python-mode.el
;; and python.el, where Tim Peters, Barry A. Warsaw,
;; Skip Montanaro, Ken Manheimer, Dave Love and many
;; others wrote major parts. Author of ipython.el's
;; stuff merged is Alexander Schmolck.

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

;;; Some of this forms to generate parts of
;; python-mode.el are just drafts, others outdated.
;; Kept for inspiration.

;;; Code:

;; Forms used building the menu

(setq py-menu-forms
      (list
       "block"
       "block-or-clause"
       "class"
       "clause"
       "comment"
       "def"
       "def-or-class"
       "expression"
       "except-block"
       "if-block"
       "indent"
       "line"
       "minor-block"
       "partial-expression"
       "paragraph"
       "section"
       "statement"
       "top-level"
       "try-block"
       ))

(setq py-menu-abbrev-form "	   :help \"see also `py-add-abbrev'\"
	   :filter (lambda (&rest junk)
		     (abbrev-table-menu python-mode-abbrev-table))")

(setq py-menu-head ";; python-components-menu.el --- Provide the python-mode menu

;; This file not shipped as part of GNU Emacs.

;; Copyright (C) 2015  Andreas Röhler
;; Author: Andreas Röhler <andreas.roehler@online.de>

;; Keywords: languages, processes, python, oop

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

;;; Code:
")

(setq py-menu-custom-forms "         (\"Customize\"

	  [\"Python-mode customize group\" (customize-group 'python-mode)
	   :help \"Open the customization buffer for Python mode\"]
	  (\"Switches\"
	   :help \"Toggle useful modes like `highlight-indentation'\"
	   (\"Interpreter\"

	    [\"Shell prompt read only\"
	     (setq py-shell-prompt-read-only
		   (not py-shell-prompt-read-only))
	     :help \"If non-nil, the python prompt is read only.  Setting this variable will only effect new shells.Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-shell-prompt-read-only]

	    [\"Remove cwd from path\"
	     (setq py-remove-cwd-from-path
		   (not py-remove-cwd-from-path))
	     :help \"Whether to allow loading of Python modules from the current directory.
If this is non-nil, Emacs removes '' from sys.path when starting
a Python process.  This is the default, for security
reasons, as it is easy for the Python process to be started
without the user's realization (e.g. to perform completion).Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-remove-cwd-from-path]

	    [\"Honor IPYTHONDIR \"
	     (setq py-honor-IPYTHONDIR-p
		   (not py-honor-IPYTHONDIR-p))
	     :help \"When non-nil ipython-history file is constructed by \\\$IPYTHONDIR
followed by \"/history\". Default is nil.

Otherwise value of py-ipython-history is used. Use `M-x customize-variable' to set it permanently\"
:style toggle :selected py-honor-IPYTHONDIR-p]

	    [\"Honor PYTHONHISTORY \"
	     (setq py-honor-PYTHONHISTORY-p
		   (not py-honor-PYTHONHISTORY-p))
	     :help \"When non-nil python-history file is set by \\\$PYTHONHISTORY
Default is nil.

Otherwise value of py-python-history is used. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-honor-PYTHONHISTORY-p]

	    [\"Enforce py-shell-name\" force-py-shell-name-p-on
	     :help \"Enforce customized default `py-shell-name' should upon execution. \"]

	    [\"Don't enforce default interpreter\" force-py-shell-name-p-off
	     :help \"Make execute commands guess interpreter from environment\"]

	    [\"Enforce local Python shell \" py-force-local-shell-on
	     :help \"Locally indicated Python being enforced upon sessions execute commands. \"]

	    [\"Remove local Python shell enforcement, restore default\" py-force-local-shell-off
	     :help \"Restore `py-shell-name' default value and `behaviour'. \"])

	   (\"Execute\"

	    [\"Fast process\" py-fast-process-p
	     :help \" `py-fast-process-p'

Use `py-fast-process'\\.

Commands prefixed \\\"py-fast-...\\\" suitable for large output

See: large output makes Emacs freeze, lp:1253907

Output-buffer is not in comint-mode\"
	     :style toggle :selected py-fast-process-p]

	    [\"Python mode v5 behavior\"
	     (setq python-mode-v5-behavior-p
		   (not python-mode-v5-behavior-p))
	     :help \"Execute region through `shell-command-on-region' as
v5 did it - lp:990079. This might fail with certain chars - see UnicodeEncodeError lp:550661

Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected python-mode-v5-behavior-p]

	    [\"Force shell name \"
	     (setq py-force-py-shell-name-p
		   (not py-force-py-shell-name-p))
	     :help \"When `t', execution with kind of Python specified in `py-shell-name' is enforced, possibly shebang doesn't take precedence. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-force-py-shell-name-p]

	    [\"Execute \\\"if name == main\\\" blocks p\"
	     (setq py-if-name-main-permission-p
		   (not py-if-name-main-permission-p))
	     :help \" `py-if-name-main-permission-p'

Allow execution of code inside blocks delimited by
if __name__ == '__main__'

Default is non-nil. \"
	     :style toggle :selected py-if-name-main-permission-p]

	    [\"Ask about save\"
	     (setq py-ask-about-save
		   (not py-ask-about-save))
	     :help \"If not nil, ask about which buffers to save before executing some code.
Otherwise, all modified buffers are saved without asking.Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-ask-about-save]

	    [\"Store result\"
	     (setq py-store-result-p
		   (not py-store-result-p))
	     :help \" `py-store-result-p'

When non-nil, put resulting string of `py-execute-...' into kill-ring, so it might be yanked. \"
	     :style toggle :selected py-store-result-p]

	    [\"Prompt on changed \"
	     (setq py-prompt-on-changed-p
		   (not py-prompt-on-changed-p))
	     :help \"When called interactively, ask for save before a changed buffer is sent to interpreter.

Default is `t'Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-prompt-on-changed-p]

	    [\"Dedicated process \"
	     (setq py-dedicated-process-p
		   (not py-dedicated-process-p))
	     :help \"If commands executing code use a dedicated shell.

Default is nilUse `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-dedicated-process-p]

	    [\"Execute without temporary file\"
	     (setq py-execute-no-temp-p
		   (not py-execute-no-temp-p))
	     :help \" `py-execute-no-temp-p'
Seems Emacs-24.3 provided a way executing stuff without temporary files.
In experimental state yet \"
	     :style toggle :selected py-execute-no-temp-p]

	    [\"Warn tmp files left \"
	     (setq py--warn-tmp-files-left-p
		   (not py--warn-tmp-files-left-p))
	     :help \"Messages a warning, when `py-temp-directory' contains files susceptible being left by previous Python-mode sessions. See also lp:987534 Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py--warn-tmp-files-left-p])

	   (\"Edit\"

	    (\"Completion\"

	     [\"Set Pymacs-based complete keymap \"
	      (setq py-set-complete-keymap-p
		    (not py-set-complete-keymap-p))
	      :help \"If `py-complete-initialize', which sets up enviroment for Pymacs based py-complete, should load it's keys into `python-mode-map'

Default is nil.
See also resp. edit `py-complete-set-keymap' Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-set-complete-keymap-p]

	     [\"Indent no completion \"
	      (setq py-indent-no-completion-p
		    (not py-indent-no-completion-p))
	      :help \"If completion function should indent when no completion found. Default is `t'

Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-indent-no-completion-p]

	     [\"Company pycomplete \"
	      (setq py-company-pycomplete-p
		    (not py-company-pycomplete-p))
	      :help \"Load company-pycomplete stuff. Default is nilUse `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-company-pycomplete-p])

	    (\"Filling\"

	     (\"Docstring styles\"
	      :help \"Switch docstring-style\"

	      [\"Nil\" py-set-nil-docstring-style
	       :help \" `py-set-nil-docstring-style'

Set py-docstring-style to nil, format string normally. \"]

	      [\"pep-257-nn\" py-set-pep-257-nn-docstring-style
	       :help \" `py-set-pep-257-nn-docstring-style'

Set py-docstring-style to 'pep-257-nn \"]

	      [\"pep-257\" py-set-pep-257-docstring-style
	       :help \" `py-set-pep-257-docstring-style'

Set py-docstring-style to 'pep-257 \"]

	      [\"django\" py-set-django-docstring-style
	       :help \" `py-set-django-docstring-style'

Set py-docstring-style to 'django \"]

	      [\"onetwo\" py-set-onetwo-docstring-style
	       :help \" `py-set-onetwo-docstring-style'

Set py-docstring-style to 'onetwo \"]

	      [\"symmetric\" py-set-symmetric-docstring-style
	       :help \" `py-set-symmetric-docstring-style'

Set py-docstring-style to 'symmetric \"])

	     [\"Auto-fill mode\"
	      (setq py-auto-fill-mode
		    (not py-auto-fill-mode))
	      :help \"Fill according to `py-docstring-fill-column' and `py-comment-fill-column'

Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-auto-fill-mode])

	    [\"Use current dir when execute\"
	     (setq py-use-current-dir-when-execute-p
		   (not py-use-current-dir-when-execute-p))
	     :help \" `toggle-py-use-current-dir-when-execute-p'

Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-use-current-dir-when-execute-p]

	    (\"Indent\"
	     (\"TAB related\"

	      [\"indent-tabs-mode\"
	       (setq indent-tabs-mode
		     (not indent-tabs-mode))
	       :help \"Indentation can insert tabs if this is non-nil.

Use `M-x customize-variable' to set it permanently\"
	       :style toggle :selected indent-tabs-mode]

	      [\"Tab indent\"
	       (setq py-tab-indent
		     (not py-tab-indent))
	       :help \"Non-nil means TAB in Python mode calls `py-indent-line'.Use `M-x customize-variable' to set it permanently\"
	       :style toggle :selected py-tab-indent]

	      [\"Tab shifts region \"
	       (setq py-tab-shifts-region-p
		     (not py-tab-shifts-region-p))
	       :help \"If `t', TAB will indent/cycle the region, not just the current line.

Default is nil
See also `py-tab-indents-region-p'

Use `M-x customize-variable' to set it permanently\"
	       :style toggle :selected py-tab-shifts-region-p]

	      [\"Tab indents region \"
	       (setq py-tab-indents-region-p
		     (not py-tab-indents-region-p))
	       :help \"When `t' and first TAB doesn't shift, indent-region is called.

Default is nil
See also `py-tab-shifts-region-p'

Use `M-x customize-variable' to set it permanently\"
	       :style toggle :selected py-tab-indents-region-p])

	     [\"Close at start column\"
	      (setq py-closing-list-dedents-bos
		    (not py-closing-list-dedents-bos))
	      :help \"When non-nil, indent list's closing delimiter like start-column.

It will be lined up under the first character of
 the line that starts the multi-line construct, as in:

my_list = \\[
    1, 2, 3,
    4, 5, 6,
]

Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-closing-list-dedents-bos]

	     [\"Closing list keeps space\"
	      (setq py-closing-list-keeps-space
		    (not py-closing-list-keeps-space))
	      :help \"If non-nil, closing parenthesis dedents onto column of opening plus `py-closing-list-space', default is nil Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-closing-list-keeps-space]

	     [\"Closing list space\"
	      (setq py-closing-list-space
		    (not py-closing-list-space))
	      :help \"Number of chars, closing parenthesis outdent from opening, default is 1 Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-closing-list-space]

	     [\"Tab shifts region \"
	      (setq py-tab-shifts-region-p
		    (not py-tab-shifts-region-p))
	      :help \"If `t', TAB will indent/cycle the region, not just the current line.

Default is nil
See also `py-tab-indents-region-p'Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-tab-shifts-region-p]

	     [\"Lhs inbound indent\"
	      (setq py-lhs-inbound-indent
		    (not py-lhs-inbound-indent))
	      :help \"When line starts a multiline-assignment: How many colums indent should be more than opening bracket, brace or parenthesis. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-lhs-inbound-indent]

	     [\"Continuation offset\"
	      (setq py-continuation-offset
		    (not py-continuation-offset))
	      :help \"With numeric ARG different from 1 py-continuation-offset is set to that value; returns py-continuation-offset. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-continuation-offset]

	     [\"Electric colon\"
	      (setq py-electric-colon-active-p
		    (not py-electric-colon-active-p))
	      :help \" `py-electric-colon-active-p'

`py-electric-colon' feature.  Default is `nil'. See lp:837065 for discussions. \"
	      :style toggle :selected py-electric-colon-active-p]

	     [\"Electric colon at beginning of block only\"
	      (setq py-electric-colon-bobl-only
		    (not py-electric-colon-bobl-only))
	      :help \"When inserting a colon, do not indent lines unless at beginning of block.

Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-electric-colon-bobl-only]

	     [\"Electric yank active \"
	      (setq py-electric-yank-active-p
		    (not py-electric-yank-active-p))
	      :help \" When non-nil, `yank' will be followed by an `indent-according-to-mode'.

Default is nilUse `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-electric-yank-active-p]

	     [\"Electric kill backward \"
	      (setq py-electric-kill-backward-p
		    (not py-electric-kill-backward-p))
	      :help \"Affects `py-electric-backspace'. Default is nil.

If behind a delimited form of braces, brackets or parentheses,
backspace will kill it's contents

With when cursor after
my_string\\[0:1]
--------------^

==>

my_string\\[]
----------^

In result cursor is insided emptied delimited form.Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-electric-kill-backward-p]

	     [\"Trailing whitespace smart delete \"
	      (setq py-trailing-whitespace-smart-delete-p
		    (not py-trailing-whitespace-smart-delete-p))
	      :help \"Default is nil. When t, python-mode calls
    (add-hook 'before-save-hook 'delete-trailing-whitespace nil 'local)

Also commands may delete trailing whitespace by the way.
When editing other peoples code, this may produce a larger diff than expected Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-trailing-whitespace-smart-delete-p]

	     [\"Newline delete trailing whitespace \"
	      (setq py-newline-delete-trailing-whitespace-p
		    (not py-newline-delete-trailing-whitespace-p))
	      :help \"Delete trailing whitespace maybe left by `py-newline-and-indent'.

Default is `t'. See lp:1100892 Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-newline-delete-trailing-whitespace-p]

	     [\"Dedent keep relative column\"
	      (setq py-dedent-keep-relative-column
		    (not py-dedent-keep-relative-column))
	      :help \"If point should follow dedent or kind of electric move to end of line. Default is t - keep relative position. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-dedent-keep-relative-column]

	     [\"Indent paren spanned multilines \"
	      (setq py-indent-paren-spanned-multilines-p
		    (not py-indent-paren-spanned-multilines-p))
	      :help \"If non-nil, indents elements of list a value of `py-indent-offset' to first element:

def foo():
    if (foo &&
            baz):
        bar()

Default lines up with first element:

def foo():
    if (foo &&
        baz):
        bar()
Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-indent-paren-spanned-multilines-p]

	     [\"Indent honors multiline listing\"
	      (setq py-indent-honors-multiline-listing
		    (not py-indent-honors-multiline-listing))
	      :help \"If `t', indents to 1\\+ column of opening delimiter. If `nil', indent adds one level to the beginning of statement. Default is `nil'. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-indent-honors-multiline-listing]

	     [\"Indent comment \"
	      (setq py-indent-comments
		    (not py-indent-comments))
	      :help \"If comments should be indented like code. Default is `nil'.

Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-indent-comments]

	     [\"Uncomment indents \"
	      (setq py-uncomment-indents-p
		    (not py-uncomment-indents-p))
	      :help \"When non-nil, after uncomment indent lines. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-uncomment-indents-p]

	     [\"Indent honors inline comment\"
	      (setq py-indent-honors-inline-comment
		    (not py-indent-honors-inline-comment))
	      :help \"If non-nil, indents to column of inlined comment start.
Default is nil. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-indent-honors-inline-comment]

	     [\"Kill empty line\"
	      (setq py-kill-empty-line
		    (not py-kill-empty-line))
	      :help \"If t, py-indent-forward-line kills empty lines. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-kill-empty-line]

	     (\"Smart indentation\"
	      :help \"Toggle py-smart-indentation'

Use `M-x customize-variable' to set it permanently\"

	      [\"Toggle py-smart-indentation\" toggle-py-smart-indentation
	       :help \"Toggles py-smart-indentation

Use `M-x customize-variable' to set it permanently\"]

	      [\"py-smart-indentation on\" py-smart-indentation-on
	       :help \"Switches py-smart-indentation on

Use `M-x customize-variable' to set it permanently\"]

	      [\"py-smart-indentation off\" py-smart-indentation-off
	       :help \"Switches py-smart-indentation off

Use `M-x customize-variable' to set it permanently\"])

	     [\"Beep if tab change\"
	      (setq py-beep-if-tab-change
		    (not py-beep-if-tab-change))
	      :help \"Ring the bell if `tab-width' is changed.
If a comment of the form

                           	# vi:set tabsize=<number>:

is found before the first code line when the file is entered, and the
current value of (the general Emacs variable) `tab-width' does not
equal <number>, `tab-width' is set to <number>, a message saying so is
displayed in the echo area, and if `py-beep-if-tab-change' is non-nil
the Emacs bell is also rung as a warning.Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-beep-if-tab-change]

	     [\"Highlight indentation\" highlight-indentation
	      :help \"Toggle highlight indentation.

Use `M-x customize-variable' to set it permanently

Make sure `highlight-indentation' is installed\"

	      ]

	     [\"Electric comment \"
	      (setq py-electric-comment-p
		    (not py-electric-comment-p))
	      :help \"If \\\"#\\\" should call `py-electric-comment'. Default is `nil'.

Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-electric-comment-p]

	     [\"Electric comment add space \"
	      (setq py-electric-comment-add-space-p
		    (not py-electric-comment-add-space-p))
	      :help \"If py-electric-comment should add a space.  Default is `nil'. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-electric-comment-add-space-p]

	     [\"Empty line closes \"
	      (setq py-empty-line-closes-p
		    (not py-empty-line-closes-p))
	      :help \"When non-nil, dedent after empty line following block

if True:
    print(\\\"Part of the if-statement\\\")

print(\\\"Not part of the if-statement\\\")

Default is nil

If non-nil, a C-j from empty line dedents.
Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-empty-line-closes-p])
	    [\"Defun use top level \"
	     (setq py-defun-use-top-level-p
		   (not py-defun-use-top-level-p))
	     :help \"When non-nil, keys C-M-a, C-M-e address top-level form.

Beginning- end-of-defun forms use
commands `py-backward-top-level', `py-forward-top-level'

mark-defun marks top-level form at point etc. \"
	     :style toggle :selected py-defun-use-top-level-p]

	    [\"Close provides newline\"
	     (setq py-close-provides-newline
		   (not py-close-provides-newline))
	     :help \"If a newline is inserted, when line after block isn't empty. Default is non-nil. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-close-provides-newline]

	    [\"Block comment prefix \"
	     (setq py-block-comment-prefix-p
		   (not py-block-comment-prefix-p))
	     :help \"If py-comment inserts py-block-comment-prefix.

Default is tUse `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-block-comment-prefix-p])

	   (\"Display\"

	    (\"Index\"

	     [\"Imenu create index \"
	      (setq py--imenu-create-index-p
		    (not py--imenu-create-index-p))
	      :help \"Non-nil means Python mode creates and displays an index menu of functions and global variables. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py--imenu-create-index-p]

	     [\"Imenu show method args \"
	      (setq py-imenu-show-method-args-p
		    (not py-imenu-show-method-args-p))
	      :help \"Controls echoing of arguments of functions & methods in the Imenu buffer.
When non-nil, arguments are printed.Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-imenu-show-method-args-p]
	     [\"Switch index-function\" py-switch-imenu-index-function
	      :help \"`py-switch-imenu-index-function'
Switch between `py--imenu-create-index' from 5.1 series and `py--imenu-create-index-new'.\"])

	    (\"Fontification\"

	     [\"Mark decorators\"
	      (setq py-mark-decorators
		    (not py-mark-decorators))
	      :help \"If py-mark-def-or-class functions should mark decorators too. Default is `nil'. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-mark-decorators]

	     [\"Fontify shell buffer \"
	      (setq py-fontify-shell-buffer-p
		    (not py-fontify-shell-buffer-p))
	      :help \"If code in Python shell should be highlighted as in script buffer.

Default is nil.

If `t', related vars like `comment-start' will be set too.
Seems convenient when playing with stuff in IPython shell
Might not be TRT when a lot of output arrives Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-fontify-shell-buffer-p]

	     [\"Use font lock doc face \"
	      (setq py-use-font-lock-doc-face-p
		    (not py-use-font-lock-doc-face-p))
	      :help \"If documention string inside of def or class get `font-lock-doc-face'.

`font-lock-doc-face' inherits `font-lock-string-face'.

Call M-x `customize-face' in order to have a visible effect. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-use-font-lock-doc-face-p])

	    [\"Switch buffers on execute\"
	     (setq py-switch-buffers-on-execute-p
		   (not py-switch-buffers-on-execute-p))
	     :help \"When non-nil switch to the Python output buffer.

Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-switch-buffers-on-execute-p]

	    [\"Split windows on execute\"
	     (setq py-split-window-on-execute
		   (not py-split-window-on-execute))
	     :help \"When non-nil split windows.

Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-split-window-on-execute]

	    [\"Keep windows configuration\"
	     (setq py-keep-windows-configuration
		   (not py-keep-windows-configuration))
	     :help \"If a windows is splitted displaying results, this is directed by variable `py-split-window-on-execute'\\. Also setting `py-switch-buffers-on-execute-p' affects window-configuration\\. While commonly a screen splitted into source and Python-shell buffer is assumed, user may want to keep a different config\\.

Setting `py-keep-windows-configuration' to `t' will restore windows-config regardless of settings mentioned above\\. However, if an error occurs, it's displayed\\.

To suppres window-changes due to error-signaling also: M-x customize-variable RET. Set `py-keep-4windows-configuration' onto 'force

Default is nil Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-keep-windows-configuration]

	    [\"Which split windows on execute function\"
	     (progn
	       (if (eq 'split-window-vertically py-split-windows-on-execute-function)
		   (setq py-split-windows-on-execute-function'split-window-horizontally)
		 (setq py-split-windows-on-execute-function 'split-window-vertically))
	       (message \"py-split-windows-on-execute-function set to: %s\" py-split-windows-on-execute-function))

	     :help \"If `split-window-vertically' or `...-horizontally'. Use `M-x customize-variable' RET `py-split-windows-on-execute-function' RET to set it permanently\"
	     :style toggle :selected py-split-windows-on-execute-function]

	    [\"Modeline display full path \"
	     (setq py-modeline-display-full-path-p
		   (not py-modeline-display-full-path-p))
	     :help \"If the full PATH/TO/PYTHON should be displayed in shell modeline.

Default is nil. Note: when `py-shell-name' is specified with path, it's shown as an acronym in buffer-name already. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-modeline-display-full-path-p]

	    [\"Modeline acronym display home \"
	     (setq py-modeline-acronym-display-home-p
		   (not py-modeline-acronym-display-home-p))
	     :help \"If the modeline acronym should contain chars indicating the home-directory.

Default is nil Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-modeline-acronym-display-home-p]

	    [\"Hide show hide docstrings\"
	     (setq py-hide-show-hide-docstrings
		   (not py-hide-show-hide-docstrings))
	     :help \"Controls if doc strings can be hidden by hide-showUse `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-hide-show-hide-docstrings]

	    [\"Hide comments when hiding all\"
	     (setq py-hide-comments-when-hiding-all
		   (not py-hide-comments-when-hiding-all))
	     :help \"Hide the comments too when you do `hs-hide-all'. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-hide-comments-when-hiding-all]

	    [\"Max help buffer \"
	     (setq py-max-help-buffer-p
		   (not py-max-help-buffer-p))
	     :help \"If \\\"\\\*Python-Help\\\*\\\"-buffer should appear as the only visible.

Default is nil. In help-buffer, \\\"q\\\" will close it.  Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-max-help-buffer-p]

	    [\"Current defun show\"
	     (setq py-current-defun-show
		   (not py-current-defun-show))
	     :help \"If `py-current-defun' should jump to the definition, highlight it while waiting PY-WHICH-FUNC-DELAY seconds, before returning to previous position.

Default is `t'.Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-current-defun-show]

	    [\"Match paren mode\"
	     (setq py-match-paren-mode
		   (not py-match-paren-mode))
	     :help \"Non-nil means, cursor will jump to beginning or end of a block.
This vice versa, to beginning first.
Sets `py-match-paren-key' in python-mode-map.
Customize `py-match-paren-key' which key to use. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-match-paren-mode])

	   (\"Debug\"

	    [\"py-debug-p\"
	     (setq py-debug-p
		   (not py-debug-p))
	     :help \"When non-nil, keep resp\\. store information useful for debugging\\.

Temporary files are not deleted\\. Other functions might implement
some logging etc\\. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-debug-p]

	    [\"Pdbtrack do tracking \"
	     (setq py-pdbtrack-do-tracking-p
		   (not py-pdbtrack-do-tracking-p))
	     :help \"Controls whether the pdbtrack feature is enabled or not.
When non-nil, pdbtrack is enabled in all comint-based buffers,
e.g. shell buffers and the \\\*Python\\\* buffer.  When using pdb to debug a
Python program, pdbtrack notices the pdb prompt and displays the
source file and line that the program is stopped at, much the same way
as gud-mode does for debugging C programs with gdb.Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-pdbtrack-do-tracking-p]

	    [\"Jump on exception\"
	     (setq py-jump-on-exception
		   (not py-jump-on-exception))
	     :help \"Jump to innermost exception frame in Python output buffer.
When this variable is non-nil and an exception occurs when running
Python code synchronously in a subprocess, jump immediately to the
source code of the innermost traceback frame.

Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-jump-on-exception]

	    [\"Highlight error in source \"
	     (setq py-highlight-error-source-p
		   (not py-highlight-error-source-p))
	     :help \"Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-highlight-error-source-p])

	   (\"Other\"

	    (\"Directory\"

	     [\"Guess install directory \"
	      (setq py-guess-py-install-directory-p
		    (not py-guess-py-install-directory-p))
	      :help \"If in cases, `py-install-directory' isn't set,  `py-set-load-path'should guess it from `buffer-file-name'. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-guess-py-install-directory-p]

	     [\"Use local default\"
	      (setq py-use-local-default
		    (not py-use-local-default))
	      :help \"If `t', py-shell will use `py-shell-local-path' instead
of default Python.

Making switch between several virtualenv's easier,
                               `python-mode' should deliver an installer, so named-shells pointing to virtualenv's will be available. Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-use-local-default]

	     [\"Use current dir when execute \"
	      (setq py-use-current-dir-when-execute-p
		    (not py-use-current-dir-when-execute-p))
	      :help \"When `t', current directory is used by Python-shell for output of `py-execute-buffer' and related commands.

See also `py-execute-directory'Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-use-current-dir-when-execute-p]

	     [\"Keep shell dir when execute \"
	      (setq py-keep-shell-dir-when-execute-p
		    (not py-keep-shell-dir-when-execute-p))
	      :help \"Don't change Python shell's current working directory when sending code.

See also `py-execute-directory'Use `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-keep-shell-dir-when-execute-p]

	     [\"Fileless buffer use default directory \"
	      (setq py-fileless-buffer-use-default-directory-p
		    (not py-fileless-buffer-use-default-directory-p))
	      :help \"When `py-use-current-dir-when-execute-p' is non-nil and no buffer-file exists, value of `default-directory' sets current working directory of Python output shellUse `M-x customize-variable' to set it permanently\"
	      :style toggle :selected py-fileless-buffer-use-default-directory-p])

	    (\"Underscore word syntax\"
	     :help \"Toggle `py-underscore-word-syntax-p'\"

	     [\"Toggle underscore word syntax\" toggle-py-underscore-word-syntax-p
	      :help \" `toggle-py-underscore-word-syntax-p'

If `py-underscore-word-syntax-p' should be on or off.

  Returns value of `py-underscore-word-syntax-p' switched to. .

Use `M-x customize-variable' to set it permanently\"]

	     [\"Underscore word syntax on\" py-underscore-word-syntax-p-on
	      :help \" `py-underscore-word-syntax-p-on'

Make sure, py-underscore-word-syntax-p' is on.

Returns value of `py-underscore-word-syntax-p'. .

Use `M-x customize-variable' to set it permanently\"]

	     [\"Underscore word syntax off\" py-underscore-word-syntax-p-off
	      :help \" `py-underscore-word-syntax-p-off'

Make sure, `py-underscore-word-syntax-p' is off.

Returns value of `py-underscore-word-syntax-p'. .

Use `M-x customize-variable' to set it permanently\"])

	    [\"Load pymacs \"
	     (setq py-load-pymacs-p
		   (not py-load-pymacs-p))
	     :help \"If Pymacs related stuff should be loaded.

Default is nil.

Pymacs has been written by François Pinard and many others.
See original source: http://pymacs.progiciels-bpi.caUse `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-load-pymacs-p]

	    [\"Verbose \"
	     (setq py-verbose-p
		   (not py-verbose-p))
	     :help \"If functions should report results.

Default is nil. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-verbose-p]

	    [\"Empty comment line separates paragraph \"
	     (setq py-empty-comment-line-separates-paragraph-p
		   (not py-empty-comment-line-separates-paragraph-p))
	     :help \"Consider paragraph start/end lines with nothing inside but comment sign.

Default is non-nilUse `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-empty-comment-line-separates-paragraph-p]

	    [\"Org cycle \"
	     (setq py-org-cycle-p
		   (not py-org-cycle-p))
	     :help \"When non-nil, command `org-cycle' is available at shift-TAB, <backtab>

Default is nil. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-org-cycle-p]

	    [\"Set pager cat\"
	     (setq py-set-pager-cat-p
		   (not py-set-pager-cat-p))
	     :help \"If the shell environment variable \\\$PAGER should set to `cat'.

If `t', use `C-c C-r' to jump to beginning of output. Then scroll normally.

Avoids lp:783828, \\\"Terminal not fully functional\\\", for help('COMMAND') in python-shell

When non-nil, imports module `os' Use `M-x customize-variable' to
set it permanently\"
	     :style toggle :selected py-set-pager-cat-p]

	    [\"Edit only \"
	     (setq py-edit-only-p
		   (not py-edit-only-p))
	     :help \"When `t' `python-mode' will not take resort nor check for installed Python executables. Default is nil.

See bug report at launchpad, lp:944093. Use `M-x customize-variable' to set it permanently\"
	     :style toggle :selected py-edit-only-p])))")

(defun write-all-py-menu ()
  (interactive)
  (write-py-menu py-bounds-command-names))

(defun write-py-executes-menu (&optional commands)
  "Reads py-shells. "
  (interactive)
  (let ((menu-buffer "Python Executes Menu Buffer")
        done)
    (set-buffer (get-buffer-create menu-buffer))
    (erase-buffer)
    (switch-to-buffer (current-buffer))
    (insert ";; Menu py-execute forms
    \(easy-menu-define py-menu map \"Execute Python\"
          `(\"PyExec\"
            :help \"Python-specific features\"\n")
    (dolist (ccc (or commands py-core-command-name))
      ;; ["Execute statement" py-execute-statement
      ;;              :help "`py-execute-statement'
      ;; Send statement at point to Python interpreter. "]
      (insert (concat "
            [\"Execute " ccc "\" py-execute-" ccc "
             :help \"`py-execute-" ccc "'
       Send " ccc " at point to Python interpreter. \"]\n")))
    (dolist (ccc (or commands py-core-command-name))
      (insert (concat "            ;; " ccc "\n
            (\"Execute " ccc " ... \"
            :help \"Execute " ccc " functions\"\n"))
      (dolist (ele py-shells)
        ;; ["if" py-if
        ;; :help "Inserts if-statement"]
        (insert (concat "
            \[\"py-execute-" ccc "-" ele "\" py-execute-" ccc "-" ele "
            :help \"Execute " ccc " through a"))
        (if (string= "ipython" ele)
            (insert "n IPython")
          (insert (concat " " (capitalize ele))))
        (insert (concat " interpreter.
        With \\\\[universal-argument] use an unique "))
        (if (string= "ipython" ele)
            (insert "IPython")
          (insert (capitalize ele)))
        (insert (concat " interpreter. \"]\n")))
      (insert "            ;; dedicated\n")
      (switch-to-buffer (current-buffer))
      (dolist (ele py-shells)
        ;; ["if" py-if
        ;; :help "Inserts if-statement"]
        (insert (concat "
            \[\"py-execute-" ccc "-" ele "-dedicated\" py-execute-" ccc "-" ele "-dedicated
:help \"Execute " ccc " through a unique"))
        (if (string= "ipython" ele)
            (insert " IPython")
          (insert (concat " " (capitalize ele))))
        (insert (concat " interpreter.
Optional \\\\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. \"]\n")))
      ;; (unless done
            (insert "            (\"Ignoring defaults ... \"
             :help \"Commands will ignore default setting of
`py-switch-buffers-on-execute-p' and `py-split-window-on-execute'\"")
            ;; (setq done t))
      (insert "            ;; switch\n")
      (dolist (ele py-shells)
        ;; ["if" py-if
        ;; :help "Inserts if-statement"]
        (insert (concat "
            \[\"py-execute-" ccc "-" ele "-switch\" py-execute-" ccc "-" ele "-switch
:help \"Execute " ccc " through a"))
        (if (string= "ipython" ele)
            (insert "n IPython")
          (insert (concat " " (capitalize ele))))
        (insert (concat " interpreter.
With \\\\[universal-argument] use an unique "))
        (if (string= "ipython" ele)
            (insert "IPython")
          (insert (capitalize ele)))
        (insert (concat " interpreter. \"]\n")))
      (insert "            ;; dedicated-switch\n")
      (dolist (ele py-shells)
        ;; ["if" py-if
        ;; :help "Inserts if-statement"]
        (insert (concat "
            \[\"py-execute-" ccc "-" ele "-dedicated-switch\" py-execute-" ccc "-" ele "-dedicated-switch
:help \"Execute " ccc " through a unique"))
        (if (string= "ipython" ele)
            (insert "n IPython")
          (insert (concat " " (capitalize ele))))
        (insert (concat " interpreter.
Switch to output buffer; ignores `py-switch-buffers-on-execute-p' \"]\n")))
      (insert "))"))
    (insert "))")

    (emacs-lisp-mode)
    (switch-to-buffer (current-buffer))))

(defun write-py-menu-doppel ()
  "Reads py-shells. "
  (interactive)
  (let ((menu-buffer "*Python Executes Menu Buffer*"))
    (set-buffer (get-buffer-create menu-buffer))
    (erase-buffer)
    (switch-to-buffer (current-buffer))
    (insert "(easy-menu-define py-menu map \"Execute Python\"
          `(\"PyExec\"
            :help \"Python-specific features\"\n")
    (dolist (ccc py-core-command-name)
      (insert (concat ";; " ccc "\n"))
      ;; ["Execute statement" py-execute-statement
      ;;              :help "`py-execute-statement'
      ;; Send statement at point to Python interpreter. "]
      (insert (concat "[\"Execute " ccc "\" py-execute-" ccc "
             :help \"`py-execute-" ccc "'
Send statement at point to Python interpreter. \"]\n
             (\"Execute " ccc " ... \"
             :help \"Execute " ccc " functions\"\n"))
      (dolist (ele py-shells)
        ;; ["if" py-if
        ;; :help "Inserts if-statement"]
        (insert (concat "\[\"py-execute-" ccc "-" ele "\" py-execute-" ccc "-" ele "\n
:help \"  Execute " ccc " through a"))
        (if (string= "ipython" ele)
            (insert "n IPython")
          (insert (concat " " (capitalize ele))))
        (insert (concat " interpreter.

With \\\\[universal-argument] use an unique "))
        (if (string= "ipython" ele)
            (insert "IPython")
          (insert (capitalize ele)))
        (insert (concat " interpreter. \"]\n")))

      (insert ";; dedicated\n")
      (switch-to-buffer (current-buffer))
      (dolist (ele py-shells)
        ;; ["if" py-if
        ;; :help "Inserts if-statement"]
        (insert (concat "\[\"py-execute-" ccc "-" ele "-dedicated\" py-execute-" ccc "-" ele "-dedicated
:help \"  Execute " ccc " through a unique"))
        (if (string= "ipython" ele)
            (insert " IPython")
          (insert (concat " " (capitalize ele))))
        (insert (concat " interpreter.

Optional \\\\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. \"]\n")))

      (insert ";; switch\n")
      (dolist (ele py-shells)
        ;; ["if" py-if
        ;; :help "Inserts if-statement"]
        (insert (concat "\[\"py-execute-" ccc "-" ele "-switch\" py-execute-" ccc "-" ele "-switch
:help \"  Execute " ccc " through a"))
        (if (string= "ipython" ele)
            (insert "n IPython")
          (insert (concat " " (capitalize ele))))
        (insert (concat " interpreter.

With \\\\[universal-argument] use an unique "))
        (if (string= "ipython" ele)
            (insert "IPython")
          (insert (capitalize ele)))
        (insert (concat " interpreter. \"]\n")))
      (insert ";; dedicated-switch\n")
      (dolist (ele py-shells)
        ;; ["if" py-if
        ;; :help "Inserts if-statement"]
        (insert (concat "\[\"py-execute-" ccc "-" ele "-dedicated-switch\" py-execute-" ccc "-" ele "-dedicated-switch
:help \"  Execute " ccc " through a unique"))
        (if (string= "ipython" ele)
            (insert "n IPython")
          (insert (concat " " (capitalize ele))))
        (insert (concat " interpreter.

Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. \"]\n")))
      (insert ")"))
    (insert "))")

    (emacs-lisp-mode)
    (switch-to-buffer (current-buffer))))

(defun py-make-shell-menu ()
  "Reads py-shells, menu entries for these shells. "
  (interactive)
  (let ((temp-buffer "*Python Shell Menu Buffer*"))
    (set-buffer (get-buffer-create temp-buffer))
    (erase-buffer)
    (insert ";; Python shell menu")
    (newline)
    (switch-to-buffer (current-buffer))
    (insert "(easy-menu-define py-menu map \"Python Shells\"
'(\"Py-Shell\"
  :help \"Python Shells\"\n
  \[\"Switch to interpreter\" py-shell
   :help \"Switch to Python process in separate buffer\"]\n")
    (let ((liste py-shells)
          erg)
      (while liste
        (setq ele (car liste))
        (setq erg (documentation (intern-soft (car liste))))
        (when (string-match "Optional DEDICATED SWITCH are provided for use from programs. " erg)
          (setq erg (replace-regexp-in-string "\n *Optional DEDICATED SWITCH are provided for use from programs. " "" erg)))
        ;; '("Python"
        ;;       :help "Python-specific features"
        ;;       ["Execute statement" py-execute-statement
        ;;        :help "Send statement at point to Python interpreter. "]
        (insert (concat " \[\"" ele "\" " ele "
  :help \"" erg "\"]\n"))
        (setq liste (cdr liste))))
    (insert "\"-\"")
    ;; dedicated
    (let ((liste py-shells)
          erg)
      (while liste
        (setq ele (concat (car liste) "-dedicated"))
        (setq erg (documentation (intern-soft ele)))
        ;; '("Python"
        ;;       :help "Python-specific features"
        ;;       ["Execute statement" py-execute-statement
        ;;        :help "Send statement at point to Python interpreter. "]
        (insert (concat " \[\"" ele "\" " ele "
  :help \"" erg "\"]\n"))
        (setq liste (cdr liste))))
    (insert "))")))

(defun py-provide-executes-menu-with-resp-to-installed-python ()
  (interactive)
  (with-current-buffer "*Python Executes Menu Buffer*"
    (erase-buffer)
      ;; ["if" py-if
      ;; :help "Inserts if-statement"]
    (dolist (ele py-shells)
      (insert (concat "\[\"py-execute-buffer-" ele "\" py-execute-buffer-" ele "
:help \"  Execute buffer through a"))
      (if (string= "ipython" ele)
          (insert "n IPython")
        (insert (concat " " (capitalize ele))))
      (insert (concat " interpreter.

With \\\\[universal-argument] use an unique "))
      (if (string= "ipython" ele)
          (insert "IPython")
        (insert (capitalize ele)))
      (insert (concat " interpreter. \"]\n")

      ;; ["if" py-if
      ;; :help "Inserts if-statement"]
      (insert (concat "\[\"py-execute-buffer-" ele "-dedicated\" py-execute-buffer-" ele "-dedicated
:help \"  Execute buffer through a unique"))
      (if (string= "ipython" ele)
          (insert " IPython")
        (insert (concat " " (capitalize ele))))
      (insert (concat " interpreter.

Optional \\\\[universal-argument] forces switch to output buffer, ignores `py-switch-buffers-on-execute-p'. \"]\n")))

      ;; ["if" py-if
      ;; :help "Inserts if-statement"]
      (insert (concat "\[\"py-execute-buffer-" ele "-switch\" py-execute-buffer-" ele "-switch
:help \"  Execute buffer through a"))
      (if (string= "ipython" ele)
          (insert "n IPython")
        (insert (concat " " (capitalize ele))))
      (insert (concat " interpreter.

With \\\\[universal-argument] use an unique "))
      (if (string= "ipython" ele)
          (insert "IPython")
        (insert (capitalize ele)))
      (insert (concat " interpreter. \"]\n")))

      ;; ["if" py-if
      ;; :help "Inserts if-statement"]
      (insert (concat "\[\"py-execute-buffer-" ele "-dedicated-switch\" py-execute-buffer-" ele "-dedicated-switch
:help \"  Execute buffer through a unique"))
      (if (string= "ipython" ele)
          (insert "n IPython")
        (insert (concat " " (capitalize ele))))
      (insert (concat " interpreter.

Switch to output buffer; ignores `py-switch-buffers-on-execute-p'. \"]\n"))))

(defun py--emen-curb-docu (line)
  "Make docu fit for displaying in tooltip. "
  (setq end (copy-marker (line-end-position)))
  (while (< 5 (- line origline))
    (while (and (not (bobp)) (< orig (point)) (forward-line -1) (not (empty-line-p))))
    (delete-region (line-beginning-position) end)))

;; (defun py-write-delete-menu ()
;;   (interactive)
;;     (set-buffer (get-buffer-create "Delete-menu.el"))
;;     (erase-buffer)
;;     (insert "         (\"Delete\"")
;;     (dolist (ele py-execute-forms)
;;       (insert (concat "
;;              [\"Delete " ele " \" py-delete-" ele "
;;               :help \"`py-delete-" ele "'
;; Delete " (upcase ele) " at point, don't store in kill-ring. \"]
;; ")))
;;     (insert "          )\n        \"-\"\n")
;;   (switch-to-buffer (current-buffer))
;;   (emacs-lisp-mode))

(defun py--emen (&optional symbol)
  "Provide menu draft. "
  (interactive "*")
  (let* ((orig (copy-marker (point)))
	 (erg (or symbol (car kill-ring)))
         (name (intern-soft erg))
         (doku (if (functionp name)
                   (documentation name)
                 (documentation-property name 'variable-documentation)))
	 (cui (current-indentation))
	 origline end line)
    ;; (goto-char (point-max))
    ;; (switch-to-buffer (current-buffer))
    (indent-according-to-mode)
    (insert (concat "\[\"" (replace-regexp-in-string "-" " " (replace-regexp-in-string "^py-" "" erg)) "\" " erg "
 :help \" `" erg "'"))
    (beginning-of-line)
    (indent-according-to-mode)
    ;; (insert (make-string cui ? ))
    (save-excursion
      (goto-char orig)
      (skip-chars-forward "[[:punct:]]")
      (capitalize-word 1))
    (end-of-line)
    (when doku
      (setq doku (substring doku 0 (string-match "\n" doku)))
      ;; (setq origline (py-count-lines))
      (newline)
      ;; (insert (regexp-quote doku))
      (insert doku)
      (setq end (copy-marker (point)))
      (goto-char orig)
      (when (search-forward ":help" end t)
	(end-of-line)
	(py--escape-doublequotes (point) end))
      ;; (when (< 5 (- (setq line (py-count-lines)) origline))
      ;; (py--emen-curb-docu line))
      )
    (goto-char (point-max))
    (skip-chars-backward " \t\r\n\f")
    (insert "\"]\n")))
  ;; (goto-char orig)

(defun py--create-menu-insert-intern (ele)
  (save-excursion (py--emen ele))
  (let ((orig (point)))
    (forward-list 1)
    (indent-region orig (point))
    (newline)))

(defun py--create-menu-insert (liste &optional prefix suffix exclude)
  (dolist (ele liste)
    (unless (stringp ele) (setq ele (prin1-to-string ele)))
    ;; Can't shift left top-level
    (unless (or (string= "" ele) (string= exclude ele))
      (when (string= "top-level" ele)
	(message "%s" exclude))
      (when prefix (setq ele (concat prefix ele)))
      (when suffix (setq ele (concat ele suffix)))
      (insert (concat "\n" (make-string 10 ? )))
      (save-excursion (py--emen ele))
      (forward-list)
      (newline))))

(defun py--create-menu-minor-fixes ()
  (newline)
  (delete-region (point) (point-max))
  (goto-char (point-min))
  (search-forward "(and (ignore-errors (require 'easymenu) t)")
  ;; (switch-to-buffer (current-buffer))
  )

(defun py-create-menu ()
  "Re-create the menu. "
  (interactive)
  (when py-verbose-p (message "%s" "Initiating the menu"))
  (with-current-buffer (get-buffer-create "python-components-menu.el")
    (erase-buffer)
    (when (called-interactively-p 'any) (switch-to-buffer (current-buffer))) 
    (insert py-menu-head)
    (newline)
    (insert "(and (ignore-errors (require 'easymenu) t)
     ;; (easy-menu-define py-menu map \"Python Tools\"
     ;;           `(\"PyTools\"
     (easy-menu-define
       py-menu python-mode-map \"Python Mode menu\"
       `(\"Python\"
	 (\"Interpreter\"")
    (emacs-lisp-mode)
    ;; (switch-to-buffer (current-buffer))
    ;; (py--create-menu-insert py-checks-symbols)

    ;; (py--create-menu-insert (list 'import-or-reload) "py-execute-")
    (py--create-menu-insert py-shells)
    (insert (concat (make-string 10 ? )")\n"))
    (insert (concat (make-string 9 ? )"(\"Edit\"\n"))

    (insert (concat (make-string 10 ? )"(\"Shift\"\n"))

    (insert (concat (make-string 11 ? )"(\"Shift right\""))
    (py--create-menu-insert py-shift-forms "py-shift-" "-right")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 11 ? )"(\"Shift left\""))
    (py--create-menu-insert py-shift-forms "py-shift-" "-left" "top-level")
    (insert (concat (make-string 12 ? )"))\n"))

    (insert (concat (make-string 10 ? )"(\"Mark\""))
    (py--create-menu-insert py-menu-forms "py-mark-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Copy\""))
    (py--create-menu-insert py-menu-forms "py-copy-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Kill\""))
    (py--create-menu-insert py-menu-forms "py-kill-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Delete\""))
    (py--create-menu-insert py-menu-forms "py-delete-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Comment\""))
    (py--create-menu-insert py-comment-forms "py-comment-")

    ;; Edit end
    (insert (concat (make-string 11 ? ) "))\n"))

    (insert (concat (make-string 9 ? )"(\"Move\"\n"))

    (insert (concat (make-string 10 ? )"(\"Backward\""))
    (py--create-menu-insert py-navigate-forms "py-backward-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Forward\""))
    (py--create-menu-insert py-navigate-forms "py-forward-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"BOL-forms\"\n"))

    (insert (concat (make-string 11 ? )"(\"Backward\""))
    (py--create-menu-insert py-navigate-forms "py-backward-" "-bol" "top-level")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 11 ? )"(\"Forward\""))
    (py--create-menu-insert py-navigate-forms "py-forward-" "-bol")
    ;; BOL forms end
    (insert (concat (make-string 12 ? )"))\n"))

    (insert (concat (make-string 10 ? )"(\"Up/Down\""))
    (py--create-menu-insert (list 'up) "py-")
    (py--create-menu-insert (list 'down) "py-")

    ;; Move ends
    (insert (concat (make-string 11 ? )"))\n"))

    (insert (concat (make-string 9 ? )"(\"Send\""))
    (py--create-menu-insert py-execute-forms "py-execute-")

    (insert (concat (make-string 11 ? )"(\"Other\"\n"))
    (dolist (ele py-shells)
      (unless (string= "" ele)
      (setq ele (prin1-to-string ele))
      ;; Shell forms
      (insert (concat (make-string 12 ? ))"(\"")
      (cond ((string-match "ipython" ele)
	     (insert (concat "IP" (substring ele 2))))
	    (t (insert (capitalize ele))))
      (insert "\"")
      (setq ele (concat "-" ele))
      (py--create-menu-insert py-execute-forms "py-execute-" ele)
      (insert (concat (make-string 13 ? )")\n"))))
    (insert (make-string 12 ? ))
    (insert "(\"Ignoring defaults \"\n")
    (insert (concat (make-string 13 ? )":help \"`M-x py-execute-statement- TAB' for example list commands ignoring defaults\n\n of `py-switch-buffers-on-execute-p' and `py-split-window-on-execute'\"\n"))
    (insert (concat (make-string 13 ? ) ")))\n"))

    (insert (concat (make-string 9 ? )"(\"Hide-Show\"\n"))

    (insert (concat (make-string 10 ? )"(\"Hide\""))
    (py--create-menu-insert py-hide-forms "py-hide-")
    (insert (concat (make-string 11 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Show\""))
    (py--create-menu-insert py-hide-forms "py-show-")

    ;; Hide-show ends
    (insert (concat (make-string 11 ? )"))\n"))

    (insert (concat (make-string 9 ? )"(\"Fast process\""))
    (py--create-menu-insert py-fast-core "py-execute-" "-fast")
    (insert (concat (make-string 10 ? )")\n"))

    (insert (concat (make-string 9 ? )"(\"Virtualenv\""))
    (py--create-menu-insert py-virtualenv-symbols "virtualenv-")
    (insert (concat (make-string 10 ? )")\n"))

    (py--create-menu-insert (list 'import-or-reload) "py-execute-")
    (insert (concat (make-string 9 ? )"(\"Help\""))
    (py--create-menu-insert py-help-symbols)
    (insert (concat (make-string 10 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Debugger\""))
    (py--create-menu-insert py-debugger-symbols)
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Checks\""))
    (py--create-menu-insert py-checks-symbols)

    (insert (concat (make-string 10 ? )"(\"Pylint\""))
    (py--create-menu-insert py-pylint-symbols)
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Pep8\""))
    (py--create-menu-insert py-pep8-symbols)
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Pyflakes\""))
    (py--create-menu-insert py-pyflakes-symbols)
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Flake8\""))
    (py--create-menu-insert py-flake8-symbols)

    (insert (concat (make-string 10 ? )"(\"Pyflakes-pep8\""))
    (py--create-menu-insert py-pyflakes-pep8-symbols)

    ;; close Pyflakes
    ;; close Checks
    (insert (concat (make-string 12 ? ) ")))\n"))
    (insert py-menu-custom-forms)
    (newline)
    (insert (concat (make-string 9 ? )"(\"Other\""))
    (py--create-menu-insert py-other-symbols "py-")

    (insert (concat (make-string 10 ? )"(\"Electric\""))
    (py--create-menu-insert py-electric-symbols "py-")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Filling\""))
    (py--create-menu-insert py-filling-symbols "py-")
    (insert (concat (make-string 12 ? )")\n"))

    (insert (concat (make-string 10 ? )"(\"Abbrevs\""))
    (insert py-menu-abbrev-form)
    (insert (concat (make-string 12 ? )")\n"))
    (py--create-menu-insert (list 'py-add-abbrev))

    (insert (concat (make-string 10 ? )"(\"Completion\""))
    (py--create-menu-insert py-completion-symbols "py-")
    (insert (concat (make-string 12 ? )")\n"))

    (py--create-menu-insert (list 'py-find-function))

    ;; nicht vorhanden
    ;; (insert (concat (make-string 10 ? )"(\"Skeletons\""))
    ;; (py--create-menu-insert py-skeletons)
    ;; (insert (concat (make-string 12 ? )")\n"))

    ;; Close Other
    (insert (concat (make-string 12 ? )")\n"))

    ;; final
    (insert (concat (make-string 12 ? ) ")))\n\n"))
    (insert "(provide 'python-components-menu)\n;;; python-components-menu.el ends here\n\n")
    (write-file (concat py-install-directory "/python-components-menu.el"))
    ))

(provide 'python-components-create-menu)
;;; python-components-menu.el ends here
