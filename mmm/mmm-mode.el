;;; mmm-mode.el --- Allow Multiple Major Modes in a buffer

;; Copyright (C) 1999 by Michael Abraham Shulman

;; Emacs Lisp Archive Entry
;; Package: mmm-mode
;; Author: Michael Abraham Shulman <viritrilbia@users.sourceforge.net>
;; Keywords: convenience, faces, languages, tools
;; Version: 0.4.7

;; Revision: $Id$

;;{{{ GPL

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 2, or (at your
;; option) any later version.

;; This file is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING. If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;}}}

;;; Commentary:

;;; MMM Mode is a minor mode that allows multiple major modes to
;;; coexist in a single buffer. Refer to the documentation of the
;;; function `mmm-mode' for more detailed information. This file
;;; contains mode on/off functions and the mode keymap, but mostly
;;; just loads all the subsidiary files.

;;{{{ Parameter Naming

;;; Since version 0.3.7, I've tried to use a uniform scheme for naming
;;; parameters. Here's a brief summary.

;;; BEG and END refer to the beginning and end of a region.
;;; FRONT and BACK refer to the respective delimiters of a region.
;;; FRONT- and BACK-OFFSET are the offsets from delimiter matches.
;;; FRONT-BEG through BACK-END are the endings of the delimiters.
;;; START and STOP bound actions, like searching, fontification, etc.

;;}}}
;;{{{ CL and Parameters

;;; Keyword parameters can be nice because it makes it easier to see
;;; what's getting passed as what. But I try not to use them in user
;;; functions, because CL doesn't make good documentation strings.
;;; Similarly, any hook or callback function can't take keywords,
;;; since Emacs as a whole doesn't use them. And for small parameter
;;; lists, they are overkill. So I use them only for a large number of
;;; optional parameters, such as `mmm-make-region'.

;;; An exception is the various submode class application functions,
;;; which all take all their arguments as keywords, for consistency
;;; and so the classes alist looks nice.

;;; When using keyword arguments, defaults should *always* be supplied
;;; in all arglists. (This pertains mostly to :start and :stop
;;; arguments, usually defaulting to (point-min) and (point-max)
;;; respectively.) `mmm-save-keywords' should only be used for lists
;;; with more than four arguments, such as in `mmm-ify-by-regexp'.

;;; In general, while I have no qualms about using things from CL like
;;; `mapl', `loop' and `destructuring-bind', I try not to use `defun*'
;;; more than I have to. For one, it sometimes makes bad documentation
;;; strings. Furthermore, to a `defun'ned function, a nil argument is
;;; the same as no argument, so it will use its (manual) default, but
;;; to a `defun*'ned function, a nil argument *is* the argument, so
;;; any default specified in the arglist will be ignored. Confusion of
;;; this type should be avoided when at all possible.

;;; By the way, in Elisp CL, there is no reason to use `mapc' over
;;; `mapcar' unless you need keyword parameters, in which case you
;;; might as well use `mapcar*'. `mapcar' is an Elisp primitive, so
;;; it's fast, and `mapc' uses it internally anyway.

;;}}}

;;; Code:

(require 'cl)
;; If we don't load font-lock now, but it is loaded later, the
;; necessary mmm-font-lock-* properties may not be there.
(require 'font-lock)
(require 'mmm-compat)
(require 'mmm-utils)
(require 'mmm-vars)
(require 'mmm-auto)
(require 'mmm-region)
(require 'mmm-class)
;; This file is set up to autoload by `mmm-auto.el'.
;; (require 'mmm-cmds)
(require 'mmm-univ)

;;{{{ Toggle Function

(defun mmm-mode (&optional arg)
  "Minor mode to allow multiple major modes in one buffer.
Without ARG, toggle MMM Mode. With ARG, turn MMM Mode on iff ARG is
positive and off otherwise.

Commands Available:
\\<mmm-mode-map>
\\{mmm-mode-map}

BASIC CONCEPTS

The idea of MMM Mode is to allow multiple major modes to coexist in
the same buffer. There is one \"dominant\" or \"default\" major mode
that controls most of the buffer, and a number of \"submodes\" that
each hold sway over certain regions. While the point is in a submode
region, the following changes occur:

1. The local keymap is that of the submode.
2. The mode line changes to show what submode region is active.
3. The major mode menu and popup are that of the submode.
4. Some local variables of the submode shadow the default mode's.
5. The syntax table and indentation are those of the submode.
6. Font-lock fontifies correctly for the submode.
7. The submode regions are highlighted by a background color.

These changes are accomplished by adding Emacs Lisp objects called
\"overlays\" to the buffer to mark the submode regions, and adding a
`post-command-hook' to update the submode changes that Emacs won't do
automatically. There are two ways to create the submode regions:
interactively and automatically. Creating submode regions is referred
to as \"mmm-ification.\"


THE MMM MINOR MODE

The MMM Minor Mode must be on in a buffer for submode regions to be
effective. Fortunately, it is automagically turned on by any
mmm-ification, interactive or automatic. When activated, it is denoted
by \"MMM\" in the mode line. You can also turn it on manually with the
function `mmm-mode', in which case it mmm-ifies the buffer
automatically. Do not set the variable `mmm-mode' directly. Turning
MMM Mode off automatically removes all submode regions from the
buffer.

MMM Mode has its own keymap, which is bound by default to the prefix
key \"\\C-c%\". This is a good mnemonic for me since I use MMM Mode to
edit HTML files with embedded languages such as HTML::Mason, which
uses the character \"%\" to introduce server-side code. You can
customize this with the variable `mmm-prefix-key'. When MMM Mode is
activated, many of the functions discussed below have keyboard
equivalents, given in parentheses after their name.


GETTING STARTED

There are six sample submode classes that come with MMM Mode: Embedded
CSS in HTML \(requires `css-mode'), Embedded Javascript in HTML
\(requires `javascript-mode'), HTML in Perl here-documents, the
HTML::Mason syntax for server-side Perl in HTML, Emacs Lisp in
\"eval\" file variables, and HTML in PL/SQL \(helpful to have some
PL/SQL mode).

If one of these is what you need, then all that's necessary is to put
a line containing \"-*- mmm-classes: CLASS -*-\" at the top of each
file you want to use MMM Mode in, where CLASS is one of embedded-css,
javascript, html-here, mason, eval-elisp, or htp-p. After this edit
you can type M-x normal-mode \(in order to re-parse the file
variables) and then M-x mmm-mode to activate the appropriate submode
regions \(assuming MMM Mode is loaded).

I suggest reading my comments on whatever classes you are using. These
can be found in the file \"mmm-mode\" at the bottom in the appropriate
section. Hopefully in the future, these will become doc-strings.

If you want to use more than one class in a file, simply set
`mmm-classes' to a list of symbols rather than a single symbol. If you
want MMM Mode to be activated automatically whenever you find a file
with `mmm-classes' set, call `mmm-add-find-file-hook' in your Emacs
initialization file. \(See \"Loading MMM Mode \", below)

If you want to use one of these submode classes in all buffers with a
certain major mode or file extension, call `mmm-add-mode-ext-class' in
your Emacs initialization file. For example, if you want all files
with the extension .mason to be in html-mode with the MMM class mason
activated, try this:

\(add-to-list 'auto-mode-alist '(\"\\\\.mason\\\\'\" . html-mode))
\(mmm-add-mode-ext-class 'html-mode \"\\\\.mason\\\\'\" 'mason)

If none of the supplied classes is what you need, you'll have to write
your own. Reading through the documentation and looking at the
supplied classes should help you. You may want to try interactive
mmm-ification until your regexps or functions are perfected. If your
class works well and you think others might find it useful, send it to
me and maybe I'll include it in the next release.


INTERACTIVE MMM-IFICATION

There are four functions that create regions interactively:
`mmm-ify-region' \(\\[mmm-ify-region]), `mmm-ify-by-regexp' \(\\[mmm-ify-by-regexp]),
`mmm-ify-by-function' \(\\[mmm-ify-by-function]), and `mmm-ify-by-class' \(\\[mmm-ify-by-class]).
The first adds a region between point and mark. The second adds
regions throughout the file delimited by regexps. The third adds
regions as computed by a user-defined function. The fourth adds
regions as appropriate for a submode class. For more info, see the
documentation for these functions.


AUTOMATIC MMM-IFICATION

Automatic mmm-ification is done by means of \"submode classes.\" A
submode class is a set of submodes along with methods of adding
regions for them. These methods can be either a set of regexps
analogous to the arguments of `mmm-ify-by-regexp', a function which
could be passed to `mmm-ify-by-function', or another submode class to
invoke. Whenever automatic mmm-ification takes place \(see below for
when this occurs), three things happen:

1. All existing submode regions are removed.
2. All recent interactive mmm-ification is reapplied.
3. The buffer-local variables `mmm-classes' and `mmm-mode-ext-classes'
   are inspected for classes to mmm-ify the buffer with.

Each class found in the third step is looked up in `mmm-classes-alist'
to find its associated submode(s), method(s), and face(s), and
appropriate submode regions are added. To create a class, simply add
an element to `mmm-classes-alist'. See the documentation for that
variable for the correct format of elements. The variable
`mmm-classes' is suitable for setting in a file variables list.

Automatic mmm-ification is done by the functions `mmm-parse-buffer'
\(\\[mmm-parse-buffer]) and `mmm-parse-region'. These functions can be called
interactively, and the first has a default key binding. The function
`mmm-ify-by-all' sets `mmm-mode-ext-classes' appropriately for the
current buffer by looking in `mmm-mode-ext-classes-alist'. The
function `mmm-add-find-file-hook' adds `mmm-ify-by-all' to
`find-file-hooks' for which it is well suited.


LOADING MMM MODE

Suggested lines for a .emacs file are:

\(require 'mmm-mode)
\(mmm-add-find-file-hook)

Autoloading MMM Mode is not particularly useful if you want Automatic
MMM-ification by classes to occur whenever you find a file which has
the local variable `mmm-classes' set or a mode/extension in
`mmm-mode-ext-classes-alist', since MMM Mode would have to be loaded
as soon as you find a file. But if you only activate MMM Mode
interactively, you can autoload it as follows:

\(autoload 'mmm-mode \"mmm-mode\" \"Multiple Major Modes\" t)
\(autoload 'mmm-parse-buffer \"mmm-mode\" \"Automatic MMM-ification\" t)

and similar lines for any other functions you want to call directly.


MISCELLANY

After you type a new region that should be a submode, you can run the
function `mmm-parse-block' \(\\[mmm-parse-block]) to detect it with automatic
mmm-ification.

The function `mmm-clear-overlays' \(\\[mmm-clear-overlays]) removes all submode regions
in the current buffer, without turning off MMM Mode. It clears the
history of interactive mmm-ification, but does not change the value of
`mmm-classes'.


CUSTOMIZATION

Besides those already discussed, there are a number of variables that
can be used to customize MMM Mode. The appearance can be customized
with the variables `mmm-default-submode-face', `mmm-mode-string', and
`mmm-submode-mode-line-format', which see for further information.

The variable `mmm-save-local-variables' controls what buffer-local
variables are saved for submodes.  This is how comments are handled,
for instance.  You can add variable names to this list--see its
documentation for details.  Often something that seems like a problem
with MMM Mode can be solved by simply saving an extra variable.

When entering MMM Mode, the hook `mmm-mode-hook' is run. A hook named
<major-mode>-mmm-hook is also run, if it exists. For example,
`html-mode-mmm-hook' is run whenever MMM Mode is entered in HTML mode.

Furhermore, a hook named <submode>-submode-hook is run whenever a
submode region of a given mode is created. For example,
`cperl-mode-submode-hook' is run whenever a CPerl mode submode region
is created, in any buffer. When submode hooks are run, point is
guaranteed to be at the start of the newly created submode region.

All these, and some others, can be reached through M-x customize under
Programming | Tools | Mmm, except the major mode and submode hooks
\(obviously)."
  (interactive "P")
  (if (if arg (> (prefix-numeric-value arg) 0) (not mmm-mode))
      (mmm-mode-on)
    (mmm-mode-off)))

;;}}}
;;{{{ Mode On

(defun mmm-mode-on ()
  "Turn on MMM Mode. See `mmm-mode'."
  (interactive)
  ;; This function is called from mode hooks, so we need to make sure
  ;; we're not in a temporary buffer.  We don't need to worry about
  ;; recursively ending up in ourself, however, since by that time the
  ;; variable `mmm-mode' will already be set.
  (mmm-valid-buffer
   (unless mmm-mode
     (setq mmm-primary-mode major-mode)
     (mmm-update-mode-info major-mode)
     (setq mmm-region-saved-locals-for-dominant
           (list* (list 'font-lock-cache-state nil)
                  (list 'font-lock-cache-position (make-marker))
                  (copy-tree (cdr (assq major-mode mmm-region-saved-locals-defaults)))))
     ;; Without the next line, the (make-marker) above gets replaced
     ;; with the starting value of nil, and all comes to naught.
     (mmm-set-local-variables major-mode)
     (mmm-add-hooks)
     (mmm-fixup-skeleton)
     (make-local-variable 'font-lock-fontify-region-function)
     (make-local-variable 'font-lock-beginning-of-syntax-function)
     (setq font-lock-fontify-region-function 'mmm-fontify-region
           font-lock-beginning-of-syntax-function 'mmm-beginning-of-syntax)
     (setq mmm-mode t)
     (condition-case err
         (mmm-apply-all)
       (mmm-invalid-submode-class
        ;; Complain, but don't die, since we want files to go ahead
        ;; and be opened anyway, and the mode to go ahead and be
        ;; turned on. Should we delete all previously made submode
        ;; regions when we find an invalid one?
        (message "%s" (error-message-string err))))
     (mmm-update-current-submode)
     (run-hooks 'mmm-mode-hook)
     (mmm-run-major-hook))))

;;}}}
;;{{{ Mode Off

(defun mmm-mode-off ()
  "Turn off MMM Mode. See `mmm-mode'."
  (interactive)
  (when mmm-mode
    (mmm-remove-hooks)
    (mmm-clear-overlays)
    (mmm-clear-history)
    (mmm-clear-mode-ext-classes)
    (mmm-clear-local-variables)
    (mmm-update-submode-region)
    (setq font-lock-fontify-region-function
          (get mmm-primary-mode 'mmm-fontify-region-function)
          font-lock-beginning-of-syntax-function
          (get mmm-primary-mode 'mmm-beginning-of-syntax-function))
    (mmm-update-font-lock-buffer)
    (mmm-refontify-maybe)
    (setq mmm-mode nil)))

(add-to-list 'minor-mode-alist (list 'mmm-mode mmm-mode-string))

;;}}}
;;{{{ Mode Keymap

(defvar mmm-mode-map (make-sparse-keymap)
  "Keymap for MMM Minor Mode.")

(defvar mmm-mode-prefix-map (make-sparse-keymap)
  "Keymap for MMM Minor Mode after `mmm-mode-prefix-key'.")

(defvar mmm-mode-menu-map (make-sparse-keymap "MMM")
  "Keymap for MMM Minor Mode menu.")

(defun mmm-define-key (key binding)
  (define-key mmm-mode-prefix-map
    (vector (append mmm-command-modifiers (list key)))
    binding))

(when mmm-use-old-command-keys
  (mmm-use-old-command-keys))

(mmm-define-key ?c 'mmm-ify-by-class)
(mmm-define-key ?x 'mmm-ify-by-regexp)
(mmm-define-key ?r 'mmm-ify-region)

(mmm-define-key ?b 'mmm-parse-buffer)
(mmm-define-key ?g 'mmm-parse-region)
(mmm-define-key ?% 'mmm-parse-block)
(mmm-define-key ?5 'mmm-parse-block)

(mmm-define-key ?k 'mmm-clear-current-region)
(mmm-define-key ?\  'mmm-reparse-current-region)
(mmm-define-key ?e 'mmm-end-current-region)

;; This one is exact, since C-h is (usually) already used for help.
(define-key mmm-mode-prefix-map [?h] 'mmm-insertion-help)

;; Default bindings to do insertion (dynamic)
(mmm-set-keymap-default mmm-mode-prefix-map 'mmm-insert-region)

;; Set up the prefix help command, since otherwise the default binding
;; overrides it.
(define-key mmm-mode-prefix-map (vector help-char) prefix-help-command)

;; And put it all onto the prefix key
(define-key mmm-mode-map mmm-mode-prefix-key mmm-mode-prefix-map)

;; Order matters for the menu bar.
(define-key mmm-mode-menu-map [off]
  '("MMM Mode Off" . mmm-mode-off))
(define-key mmm-mode-menu-map [sep0] '(menu-item "----"))

(define-key mmm-mode-menu-map [clhist]
  '("Clear History" . mmm-clear-history))
(define-key mmm-mode-menu-map [end]
  '("End Current" . mmm-end-current-region))
(define-key mmm-mode-menu-map [clear]
  '("Clear Current" . mmm-clear-current-region))
(define-key mmm-mode-menu-map [reparse]
  '("Reparse Current" . mmm-reparse-current-region))

(define-key mmm-mode-menu-map [sep10] '(menu-item "----"))

(define-key mmm-mode-menu-map [ins-help]
  '("List Insertion Keys" . mmm-insertion-help))

(define-key mmm-mode-menu-map [sep20] '(menu-item "----"))

(define-key mmm-mode-menu-map [region]
  '(menu-item "MMM-ify Region" mmm-ify-region :enable mark-active))
(define-key mmm-mode-menu-map [regexp]
  '("MMM-ify by Regexp" . mmm-ify-by-regexp))
(define-key mmm-mode-menu-map [class]
  '("Apply Submode Class" . mmm-ify-by-class))

(define-key mmm-mode-menu-map [sep30] '(menu-item "----"))

(define-key mmm-mode-menu-map [parse-region]
  '(menu-item "Parse Region" mmm-parse-region :enable mark-active))
(define-key mmm-mode-menu-map [parse-buffer]
  '("Parse Buffer" . mmm-parse-buffer))
(define-key mmm-mode-menu-map [parse-block]
  '("Parse Block" . mmm-parse-block))

(define-key mmm-mode-map [menu-bar mmm] (cons "MMM" mmm-mode-menu-map))

(add-to-list 'minor-mode-map-alist (cons 'mmm-mode mmm-mode-map))

;;}}}

(provide 'mmm-mode)

;;; mmm-mode.el ends here