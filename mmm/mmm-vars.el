;;; mmm-vars.el --- Variables for MMM Mode

;; Copyright (C) 2000 by Michael Abraham Shulman

;; Author: Michael Abraham Shulman <mas@kurukshetra.cjb.net>
;; Version: $Id$

;;{{{ GPL

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;}}}

;;; Commentary:

;; This file provides the definitions for the variables used by MMM
;; Mode, as well as several functions to manipulate them. It also
;; defines the errors that MMM Mode can signal.

;;; Code:

(require 'mmm-compat)

;; MISCELLANEOUS
;;{{{ Shut up the Byte Compiler

;; Otherwise it complains about undefined variables.
(eval-when-compile
  (defvar mmm-save-local-variables)
  (defvar mmm-mode-string)
  (defvar mmm-submode-mode-line-format)
  (defvar mmm-mode-ext-classes-alist)
  (defvar mmm-mode-prefix-key)
  (defvar mmm-global-mode)
  (defvar mmm-primary-mode)
  (defvar mmm-classes-alist))

;;}}}
;;{{{ Error Conditions

;; Signalled when we try to put a submode region inside one where it
;; isn't meant to go.
(put 'mmm-invalid-parent
     'error-conditions
     '(mmm-invalid-parent mmm-error error))
(put 'mmm-invalid-parent
     'error-message
     "Invalid submode region parent")

;; Signalled when we try to apply a submode class that doesn't exist.
(put 'mmm-invalid-submode-class
     'error-conditions
     '(mmm-invalid-submode-class mmm-error error))
(put 'mmm-invalid-submode-class
     'error-message
     "Invalid or undefined submode class")

;; Signalled by :match-submode functions when they are unable to
;; resolve a submode.  Should always be caught and never seen by the
;; user.
(put 'mmm-no-matching-submode
     'error-conditions
     '(mmm-no-matching-submode mmm-error error))
(put 'mmm-no-matching-submode
     'error-message
     "Internal error: no matching submode.")

;;}}}

;; USER VARIABLES
;;{{{ Customization Group

(defgroup mmm nil
  "Multiple Major Modes in one buffer."
  :group 'tools)

;;}}}
;;{{{ Save Local Variables

(defvar mmm-c-derived-modes
  '(c-mode c++-mode objc-mode pike-mode java-mode jde-mode javascript-mode))

(defvar mmm-save-local-variables 
  `(;; Don't use `function' (#') here!!  We're already inside `quote'!
    major-mode
    comment-start
    comment-end
    (comment-line-start-skip buffer (fortran-mode))
    comment-start-skip
    (comment-column buffer)
    comment-indent-function
    comment-line-break-function
    sentence-end
    ,@(when mmm-xemacs
        '(mode-popup-menu
          (((lambda () current-menubar) . set-buffer-menubar))
          ))
    font-lock-keywords
    font-lock-keywords-only
    font-lock-keywords-case-fold-search
    font-lock-syntax-table
    font-lock-mark-block-function       ; Override this?
    font-lock-syntactic-keywords
    indent-line-function
    parse-sexp-ignore-comments  ; Fixes indentation in PHP-mode?
    ;; Can be different in different buffers
    (c-basic-offset
     buffer (c-mode c++-mode objc-mode pike-mode java-mode jde-mode))
    ;; These are necessary for C syntax parsing
    (c-class-key nil ,mmm-c-derived-modes)
    (c-extra-toplevel-key nil ,mmm-c-derived-modes)
    (c-inexpr-class-key nil ,mmm-c-derived-modes)
    (c-conditional-key nil ,mmm-c-derived-modes)
    ;; User indentation style control
    (((lambda () c-indentation-style) . c-set-style)
     nil ,mmm-c-derived-modes)
    ;; XEmacs makes this a local variable
    ,@(when mmm-xemacs
        '((c-offsets-alist nil ,mmm-c-derived-modes)))
    ;; Skeleton insertion
    skeleton-transformation
    ;; Abbrev mode
    abbrev-mode
    local-abbrev-table
    ;; And finally the syntax table and local map.
    ((syntax-table . set-syntax-table))
    ((current-local-map . use-local-map) buffer)
    )
  "Which local variables to save for major mode regions.
Each element has the form \(VARIABLE [TYPE [MODES]]), causing VARIABLE
to be saved for all major modes in the list MODES.  If MODES is t or
absent, the variable is saved for all major modes.  MODES can also be
a function of no arguments which returns non-nil whenever the variable
should be saved.

TYPE should be either the symbol `global', meaning to save the
variable globally, the symbol `buffer', meaning to save it per buffer,
or the symbol `region', meaning to save it for each submode region.
If TYPE has any other value, such as nil, or is absent, the variable
is saved globally.  If all optional parameters are omitted, the
element may be simply VARIABLE instead of \(VARIABLE).

It is possible for VARIABLE to be not a symbol but a cons cell of the
form \(GETTER . SETTER), thus specifying special functions to set and
get the value of the \"variable\".  This is used for objects like
local maps, syntax tables, etc. which need to be installed in a
special way.  GETTER should be a function of no arguments, and SETTER
a function of one.  In this case, even if TYPE and MODES are omitted,
the list cannot be flattened--it must be \((GETTER . SETTER)).
\"Variables\" of this type cannot be seen with `mmm-get-saved-local'.

A single variable may appear more than once in this list, with
different modes and/or types.  If the same mode appears more than once
for the same variable with different types, the behavior is undefined.
Changing the value of this variable after MMM Mode has been activated
in some buffer may produce unpredictable results.

Globally saved variables are saved in the mmm-local-variables property
of the mode symbol.  Buffer saved variables are saved in the alist
`mmm-buffer-saved-locals'.  Region saved variables are saved in the
mmm-local-variables property of the overlay.")

(defvar mmm-buffer-saved-locals ()
  "Stores saved local variables for this buffer, by mode.
Each element looks like \(MODE \(VAR VALUE) ...).")
(make-variable-buffer-local 'mmm-buffer-saved-locals)

(defvar mmm-region-saved-locals-defaults ()
  "Stores saved defaults for region-saved locals, by mode.
Each element looks like \(MODE \(VAR VALUE) ...).  Used to initialize
new submode regions.")
(make-variable-buffer-local 'mmm-region-saved-locals-defaults)

(defvar mmm-region-saved-locals-for-dominant ()
  "Stores saved region locals for the dominant major mode.
The dominant major mode is considered to be one region for purposes of
saving region variables.  Region-saved variables for submode regions
are saved as overlay properties.")
(make-variable-buffer-local 'mmm-region-saved-locals-for-dominant)

;;}}}
;;{{{ Submode Faces

(defgroup mmm-faces nil
  "Faces and coloring for submode regions.
In general, only background colors should be set, to avoid interfering
with font-lock."
  :group 'mmm)

(defcustom mmm-submode-decoration-level 1
  "*Amount of coloring to use in submode regions.
Should be either 0, 1, or 2, representing None, Low, and High amounts
of coloring.  None means to use no coloring at all.  Low means to use
a single face \(`mmm-default-submode-face') for all submode regions,
\(except for \"non-submode\" regions).  High means to use different
faces for different types of submode regions, such as initialization
code, expressions that are output, declarations, and so on.  The
default face is still used for regions that do not specify a face."
  :group 'mmm-faces
  :type '(choice (const :tag "None" 0)
                 (const :tag "Low" 1)
                 (const :tag "High" 2)))

(defface mmm-init-submode-face '((t (:background "Pink")))
  "Face used for submodes containing initialization code."
  :group 'mmm-faces)

(defface mmm-cleanup-submode-face '((t (:background "Wheat")))
  "Face used for submodes containing cleanup code."
  :group 'mmm-faces)

(defface mmm-declaration-submode-face '((t (:background "Aquamarine")))
  "Face used for submodes containing declarations."
  :group 'mmm-faces)

(defface mmm-comment-submode-face '((t (:background "SkyBlue")))
  "Face used for submodes containing comments and documentation."
  :group 'mmm-faces)

(defface mmm-output-submode-face '((t (:background "Plum")))
  "Face used for submodes containing expression that are output."
  :group 'mmm-faces)

(defface mmm-special-submode-face '((t (:background "MediumSpringGreen")))
  "Face used for special submodes not fitting any other category."
  :group 'mmm-faces)

(defface mmm-code-submode-face '((t (:background "LightGray")))
  "Face used for submodes containing ordinary code."
  :group 'mmm-faces)

(defface mmm-default-submode-face '((t (:background "gray85")))
  "Face used for all submodes at decoration level 1.
Also used at decoration level 2 for submodes not specifying a type."
  :group 'mmm-faces)

;;}}}
;;{{{ Mode Line Format

(defcustom mmm-mode-string " MMM"
  "*String to display in mode line as MMM minor mode indicator."
  :group 'mmm
  :type 'string)

(defcustom mmm-submode-mode-line-format "~M[~m]"
  "*Format of the Major Mode Mode-line display when point is in a
submode region. ~M means the name of the default major mode, ~m means
the name of the submode."
  :group 'mmm
  :type 'string)

;;}}}
;;{{{ Submode Classes

(defvar mmm-classes nil
  "*List of submode classes that apply to a buffer.
Generally set in a file local variables list.  Can either be one
symbol, or a list of symbols.  Automatically buffer-local.")
(make-variable-buffer-local 'mmm-classes)

(defvar mmm-global-classes '(universal)
  "*List of submode classes that apply to all buffers.
Can be overridden in a file local variables list.")

;;}}}
;;{{{ Modes and Extensions

(defcustom mmm-mode-ext-classes-alist nil
  "Alist of submode classes for major modes and/or file extensions.
This variable can now be directly modified.

Elements look like \(MODE EXT CLASS), where MODE is a major mode, EXT
is a regexp to match a filename such as in `auto-mode-alist', and
CLASS is a submode class. CLASS is activated in all buffers in mode
MODE \(if non-nil) and whose filenames match EXT \(if non-nil). If
both MODE and EXT are nil, CLASS is activated in all buffers. If CLASS
is the symbol t, MMM Mode is turned on in all buffers matching MODE
and EXT, but no classes are activated.

See `mmm-global-mode'."
  :group 'mmm
  :type '(repeat (list (symbol :tag "Major Mode")
                       (string :tag "Filename Regexp")
                       (symbol :tag "Class")))
  :require 'mmm-mode)

(defun mmm-add-mode-ext-class (mode ext class)
  "Add an element to `mmm-mode-ext-classes-alist', which see.
That variable can now be directly modified, so this function is
unnecessary. It probably won't go away, though."
  (add-to-list 'mmm-mode-ext-classes-alist (list mode ext class)))

;;}}}
;;{{{ Preferred Major Modes

(defcustom mmm-major-mode-preferences
  '((perl cperl-mode perl-mode)
    (javascript javascript-mode c++-mode)
    (java jde-mode java-mode c++-mode)
    (css css-mode c++-mode))
  "User preferences about what major modes to use.
Each element has the form \(LANGUAGE . MODES) where LANGUAGE is the
name of a programming language such as `perl' as a symbol, and MODES
is a list of possible major modes to use, such as `cperl-mode' or
`perl-mode'.  The first element of MODES which is `fboundp' is used
for submodes of LANGUAGE.  The last element of MODES should be a mode
which will always be available."
  :group 'mmm
  :type '(repeat (cons symbol
                       (repeat
                        (restricted-sexp :match-alternatives
                                         (fboundp))))))

(defun mmm-add-to-major-mode-preferences (language mode &optional default)
  "Set the preferred major mode for LANGUAGE to MODE.
This sets the value of `mmm-major-mode-preferences'.  If DEFAULT is
nil or unsupplied, MODE is added at the front of the list of modes for
LANGUAGE.  If DEFAULT is non-nil, then it is added at the end.  This
may be used by packages to ensure that some mode is present, but not
override any user-specified mode."
  (let ((pair (assq language mmm-major-mode-preferences)))
    (if pair
        ;; Existing mode preferences
        (if default
            (setcdr pair (cons mode (cdr pair)))
          (setcdr pair (append (cdr pair) (list mode))))
      ;; No existing mode preference
      (add-to-list 'mmm-major-mode-preferences (list language mode)))))

(defun mmm-ensure-modename (symbol)
  "Return SYMBOL if it is a valid submode name, else nil.
Valid submode names are either `fboundp' or present as the `car' of an
element in `mmm-major-mode-preferences'."
  (if (or (fboundp symbol)
          (assq symbol mmm-major-mode-preferences))
      symbol
    nil))

(defun mmm-modename->function (mode)
  "Convert MODE to a mode function, nil if impossible.
Valid submode names are either `fboundp' or present as the `car' of an
element in `mmm-major-mode-preferences'.  In the latter case, the
first `fboundp' element of the `cdr' is returned, or nil if none."
  (if (fboundp mode)
      mode
    (car (remove-if-not
          #'fboundp
          (cdr (assq mode mmm-major-mode-preferences))))))

;;}}}
;;{{{ Key Bindings

(defcustom mmm-mode-prefix-key [(control ?c) ?%]
  "Prefix key for the MMM Minor Mode Keymap."
  :group 'mmm
  :type 'vector)

(defcustom mmm-command-modifiers '(control)
  "List of key modifiers for MMM command keys.
The MMM commands in the MMM Mode map, after `mmm-mode-prefix-key',
are bound to default keys with these modifiers added. This variable
must be set before MMM Mode is loaded to have an effect.

It is suggested that the value of this variable be either nil or
\(control), as the default keys are either plain keys or have only a
meta modifier. The shift modifier is not particularly portable between
Emacsen. The values of this variable and `mmm-insert-modifiers' should
be disjoint."
  :group 'mmm
  :type '(repeat (symbol :tag "Modifier")))

(defcustom mmm-insert-modifiers '()
  "List of key modifiers for MMM submode insertion keys.
When a key pressed after `mmm-mode-prefix-key' has no MMM Mode command
binding, and its modifiers include these, then its basic type, plus any
modifiers in addition to these, is looked up in classes' :insert
specifications.

It is suggested that the value of this variable be either nil or
\(control), allowing submode classes to specify the presence or
absence of the meta modifier. The shift modifier is not particularly
portable between Emacsen. The values of `mmm-command-modifiers' and
this variable should be disjoint."
  :group 'mmm
  :type '(repeat (symbol :tag "Modifier")))

(defcustom mmm-use-old-command-keys nil
  "Non-nil means to Use the old command keys for MMM Mode.
MMM Mode commands then have no modifier while insertion commands have
a control modifier, i.e. `mmm-command-modifiers' is set to nil and
`mmm-insert-modifiers' is set to \(control). If nil, the values of
these variables are as the default, or whatever the user has set them
to. This variable must be set before MMM Mode is loaded."
  :group 'mmm
  :type 'boolean)

(defun mmm-use-old-command-keys ()
  "Use the old command keys \(no control modifer) in MMM Mode."
  (setq mmm-command-modifiers '()
        mmm-insert-modifiers '(control)))

;;}}}
;;{{{ MMM Hooks

(defcustom mmm-mode-hook ()
  "Hook run when MMM Mode is enabled in a buffer.

A hook named mmm-<major-mode>-hook is also run, if it exists. For
example, `mmm-html-mode-hook' is run whenever MMM Mode is entered with
HTML mode the dominant mode.

A hook named mmm-<submode>-submode-hook is run when a submode region
of a given mode is created. For example, `mmm-cperl-mode-submode-hook'
is run whenever a CPerl mode submode region is created, in any buffer.
When submode hooks are run, point is guaranteed to be at the start of
the newly created submode region.

Finally, a hook named mmm-<class>-class-hook is run whenever a buffer
is first mmm-ified with a given submode class. For example,
`mmm-mason-class-hook' is run whenever the `mason' class is first
applied in a buffer."
  :group 'mmm
  :type 'hook)

(defun mmm-run-constructed-hook (body &optional suffix)
  "Run the hook named `mmm-<BODY>-<SUFFIX>-hook', if it exists.
If SUFFIX is nil or unsupplied, run `mmm-<BODY>-hook' instead."
  (let ((hook (intern-soft (if suffix
                               (format "mmm-%s-%s-hook" body suffix)
                             (format "mmm-%s-hook" body)))))
    (if hook (run-hooks hook))))

(defun mmm-run-major-hook ()
  (mmm-run-constructed-hook mmm-primary-mode))

(defun mmm-run-submode-hook (submode)
  (mmm-run-constructed-hook submode "submode"))

(defvar mmm-class-hooks-run ()
  "List of submode classes for which hooks have already been run in
the current buffer.")
(make-variable-buffer-local 'mmm-class-hooks-run)

(defun mmm-run-class-hook (class)
  (unless (member class mmm-class-hooks-run)
    (mmm-run-constructed-hook class "class")
    (add-to-list 'mmm-class-hooks-run class)))

;;}}}
;;{{{ Major Mode Hook

(defcustom mmm-major-mode-hook ()
  "Hook run whenever a new major mode is finished starting up.
MMM Mode implements this with a hack \(see comments in the source) so
that `mmm-global-mode' will function correctly, but makes this hook
available so that others can take advantage of the hack as well.

Note that file local variables have *not* been processed by the time
this hook is run. If a function needs to inspect them, it should also
be added to `find-file-hooks'. However, `find-file-hooks' is not run
when creating a non-file-based buffer, or when changing major modes in
an existing buffer."
  :group 'mmm
  :type 'hook)

(defun mmm-run-major-mode-hook ()
  (dolist (func mmm-major-mode-hook)
    (ignore-errors (funcall func))))

;;}}}
;;{{{ MMM Global Mode

(defcustom mmm-global-mode nil
  "*Specify in which buffers to turn on MMM Mode automatically.

- If nil, MMM Mode is never enabled automatically.
- If t, MMM Mode is enabled automatically in all buffers.
- If any other symbol, MMM mode is enabled only in those buffers that
  have submode classes associated with them. See `mmm-classes' and
  `mmm-mode-ext-classes-alist' for more information."
  :group 'mmm
  :type '(choice (const :tag "Always" t)
                 (const :tag "Never" nil)
                 (other :tag "Maybe" maybe))
  :require 'mmm-mode)

;;}}}
;;{{{ "Never" Modes

(defcustom mmm-never-modes
  '(
    help-mode
    Info-mode
    dired-mode
    comint-mode
    telnet-mode
    shell-mode
    eshell-mode
    forms-mode
    )
  "List of modes in which MMM Mode is never activated."
  :group 'mmm
  :type '(repeat (symbol :tag "Mode")))

;;}}}
;;{{{ Buffer File Name

(defvar mmm-set-file-name-for-modes '(mew-draft-mode)
  "List of modes for which temporary buffers have a file name.
If so, it is the same as that of the parent buffer.  In general, this
has been found to cause more problems than it solves, but some modes
require it.")

;;}}}

;; NON-USER VARIABLES
;;{{{ Mode Variable

(defvar mmm-mode nil
  "Non-nil means MMM Mode is turned on in this buffer.
Do not set this variable directly; use the function `mmm-mode'.")
(make-variable-buffer-local 'mmm-mode)

;;}}}
;;{{{ Primary Mode

(defvar mmm-primary-mode nil
  "The primary major mode in the current buffer.")
(make-variable-buffer-local 'mmm-primary-mode)

;;}}}
;;{{{ Classes Alist

;; :parent could be an all-class argument.  Same with :keymap.
(defvar mmm-classes-alist nil
  "Alist containing all defined mmm submode classes.
Each element looks like \(CLASS . ARGS) where CLASS is a symbol
representing the submode class and ARGS is a list of keyword
arguments, called a \"class specifier\". There are a large number of
accepted keyword arguments.

The argument CLASSES, if supplied, must be a list of other submode
classes \(or class specifiers), representing other classes to call.
FACE, if supplied, overrides FACE arguments to these classes, but all
other arguments to this class are ignored.

The argument HANDLER, if supplied, overrides any other processing. It
must be a function, and all the arguments are passed to it as
keywords, and it must do everything. See `mmm-ify' for what sorts of
things it must do. This back-door interface should be cleaned up.

The argument FACE, if supplied, specifies the display face of the
submode regions under decoration level 2.  It must be a valid face.
The standard faces used for submode regions are `mmm-*-submode-face'
where * is one of `init', `cleanup', `declaration', `comment',
`output', `special', or `code'.  A more flexible alternative is the
argument MATCH-FACE.  MATCH-FACE can be a function, which is called
with one argument, the form of the front delimiter \(found from
FRONT-FORM, below), and should return the face to use.  It can also be
an alist, each element of the form \(DELIM . FACE).

If neither CLASSES nor HANDLER are supplied, either SUBMODE or
MATCH-SUBMODE must be.  SUBMODE specifies the submode to use for the
submode regions, a symbol such as `cperl-mode' or `emacs-lisp-mode',
while MATCH-SUBMODE must be a function to be called immediately after
a match is found for FRONT, which is passed one argument, the form of
the front delimiter \(found from FRONT-FORM, below), and return a
symbol such as SUBMODE would be set to.  If MATCH-SUBMODE detects an
invalid match--for example a specified mode which is not `fboundp'--it
should \(signal 'mmm-no-matching-submode nil).

FRONT and BACK are the means to find the submode regions, and can be
either buffer positions \(number-or-markers), regular expressions, or
functions. If they are absolute buffer positions, only one submode
region is created, from FRONT to BACK. This is generally not used in
named classes. \(Unnamed classes are created by interactive commands
in `mmm-interactive-history').

If FRONT is a regexp, then that regexp is searched for, and the end of
its match \(or the beginning, if INCLUDE-FRONT is non-nil), plus
FRONT-OFFSET, becomes the beginning of the submode region.  If FRONT
is a function, that function is called instead, and must act somewhat
like a search, in that it should start at point, take one argument as
a search bound, and set the match data.  A similar pattern is followed
for BACK \(the search starts at the beginning of the submode region),
save that the beginning of its match \(or the end, if INCLUDE-BACK is
non-nil) becomes the end of the submode region, plus BACK-OFFSET.

FRONT-MATCH and BACK-MATCH default to zero.  They specify which
sub-match of the FRONT and BACK regexps to treat as the delimiter.
This number will be passed to any calls to `match-beginning' and
company.

FRONT- and BACK-OFFSET default to 0.  In addition to numbers, they can
also be functions to call which should move point to the correct
position for the beginning or end of the submode region.  Common
choices include `beginning-of-line' and `end-of-line', and new
functions can of course be written.  They can also be lists which will
be applied in sequence, such as \(end-of-line 1) meaning move to end
of line and then forward one character.

FRONT-VERIFY and BACK-VERIFY, if supplied, must be functions that
inspect the match data to see if a match found by FRONT or BACK
respectively is valid.

If SAVE-MATCHES is non-nil, BACK, if it is a regexp, is formatted by
replacing strings of the form \"~N\" by the corresponding value of
\(match-string n) after matching FRONT.

FRONT-FORM and BACK-FORM, if given, must supply a regexp used to match
the *actual* delimiter.  If they are strings, they are used as-is.  If
they are functions, they are called and must inspect the match data.
If they are lists, their `car' is taken as the delimiter.  The default
for both is \(regexp-quote \(match-string 0)).

The last case--them being a list--is usually used to set the delimiter
to a function.  Such a function must take 1-2 arguments, the first
being the overlay in question, and the second meaning to insert the
delimiter and adjust the overlay rather than just matching the
delimiter.  See `mmm-match-front', `mmm-match-back', and
`mmm-end-current-region'.

CASE-FOLD-SEARCH, if specified, controls whether the search is
case-insensitive. See `case-fold-search'. It defaults to `t'.

CREATION-HOOK, if specified, should be a function which is run
whenever a submode region is created, with point at the beginning of
the new region.  One use for it is to set region-saved local variables
\(see `mmm-save-local-variables').

INSERT specifies the keypress insertion spec for such submode regions.
INSERT's value should be list of elements of the form \(KEY NAME .
SPEC). Each KEY should be either a character, a function key symbol,
or a dotted list \(MOD . KEY) where MOD is a symbol for a modifier
key. The use of any other modifier than meta is discouraged, as
`mmm-insert-modifiers' is sometimes set to \(control), and other
modifiers are not very portable. Each NAME should be a symbol
representing the insertion for that key. Each SPEC can be either a
skeleton, suitable for passing to `skeleton-insert' to create a
submode region, or a dotted pair \(OTHER-KEY . ARG) meaning to use the
skeleton defined for OTHER-KEY but pass it the argument ARG as the
`str' variable, possible replacing a prompt string. Skeletons for
insertion should have the symbol `_' where point \(or wrapped text)
should go, and the symbol `@' in four different places: at the
beginning of the front delimiter, the beginning of the submode region,
the end of the submode region, and the end of the back delimiter.

If END-NOT-BEGIN is non-nil, it specifies that a BACK delimiter cannot
begin a new submode region.

PRIVATE, if supplied and non-nil, means that this class is a private
or internal class, usually one invoked by another class via :classes,
and is not for the user to see.")

(defun mmm-add-classes (classes)
  "Add the submode classes CLASSES to `mmm-classes-alist'."
  (dolist (class classes)
    (add-to-list 'mmm-classes-alist class)))

(defun mmm-add-group (group classes)
  "Add CLASSES and a group named GROUP containing them all.
The CLASSES are all made private, i.e. non-user-visible."
  (mmm-add-classes (mapcar #'(lambda (class)
                               (append class
                                       '(:private t)))
                           classes))
  (add-to-list 'mmm-classes-alist
               (list group :classes (mapcar #'first classes))))

;;}}}
;;{{{ Version Number

(defconst mmm-version "0.4.7"
  "Current version of MMM Mode.")

(defun mmm-version ()
  (interactive)
  (message "MMM Mode version %s by Michael Abraham Shulman" mmm-version))

;;}}}
;;{{{ Temp Buffer Name

(defvar mmm-temp-buffer-name " *mmm-temp*"
  "Name for temporary buffers created by MMM Mode.")

;;}}}
;;{{{ Interactive History

(defvar mmm-interactive-history nil
  "History of interactive mmm-ification in the current buffer.
Elements are either submode class symbols or class specifications. See
`mmm-classes-alist' for more information.")
(make-variable-buffer-local 'mmm-interactive-history)

(defun mmm-add-to-history (class)
  (add-to-list 'mmm-interactive-history class))

(defun mmm-clear-history ()
  "Clears history of interactive mmm-ification in current buffer."
  (interactive)
  (setq mmm-interactive-history nil))

;;}}}
;;{{{ Mode/Ext Manipulation

(defvar mmm-mode-ext-classes ()
  "List of classes associated with current buffer by mode and filename.
Set automatically from `mmm-mode-ext-classes-alist'.")
(make-variable-buffer-local 'mmm-mode-ext-classes)

(defun mmm-get-mode-ext-classes ()
  "Return classes for current buffer from major mode and filename.
Uses `mmm-mode-ext-classes-alist' to find submode classes."
  (or mmm-mode-ext-classes
      (setq mmm-mode-ext-classes
            (mapcar #'third
                    (remove-if-not #'mmm-mode-ext-applies
                                   mmm-mode-ext-classes-alist)))))

(defun mmm-clear-mode-ext-classes ()
  "Clear classes added by major mode and filename."
  (setq mmm-mode-ext-classes nil))

(defun mmm-mode-ext-applies (element)
  (destructuring-bind (mode ext class) element
    (and (if mode
             (eq mode
                 ;; If MMM is on in this buffer, use the primary mode,
                 ;; otherwise use the normal indicator.
                 (or mmm-primary-mode major-mode))
           t)
         (if ext
             (and (buffer-file-name)
                  (save-match-data
                    (string-match ext (buffer-file-name))))
           t))))

(defun mmm-get-all-classes (global)
  "Return a list of all classes applicable to the current buffer.
These come from mode/ext associations, `mmm-classes', and interactive
history, as well as `mmm-global-classes' if GLOBAL is non-nil."
  (append mmm-interactive-history
          (if (listp mmm-classes) mmm-classes (list mmm-classes))
          (if global mmm-global-classes ())
          (mmm-get-mode-ext-classes)))

;;}}}

(provide 'mmm-vars)

;;; mmm-vars.el ends here
