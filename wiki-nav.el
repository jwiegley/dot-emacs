;;; wiki-nav.el --- Simple file navigation using [[WikiStrings]]
;;
;; Copyright (c) 2011-2015 Roland Walker
;;
;; Author: Roland Walker <walker@pobox.com>
;; Homepage: http://github.com/rolandwalker/button-lock
;; URL: http://raw.githubusercontent.com/rolandwalker/button-lock/master/wiki-nav.el
;; Version: 1.0.2
;; Last-Updated: 23 Feb 2015
;; EmacsWiki: WikiNavMode
;; Keywords: mouse, button, hypermedia, navigation
;; Package-Requires: ((button-lock "1.0.2") (nav-flash "1.0.0"))
;;
;; Simplified BSD License
;;
;;; Commentary:
;;
;;;;;;;;;;;;;;;;;;;
;;
;; Table of Contents
;;
;; [[Quickstart]]
;; [[Explanation]]
;; [[Example usage]]
;; [[See Also]]
;; [[Prior Art]]
;; [[Notes]]
;; [[Bugs]]
;; [[Compatibility and Requirements]]
;; [[Todo]]
;; [[License]]
;; [[Code]]
;;
;;;;;;;;;;;;;;;;;;;
;;
;; [[<Quickstart]]
;;
;;     (require 'wiki-nav)
;;
;;     (global-wiki-nav-mode 1)
;;
;;     Sprinkle double-bracketed [[links]] in your code comments
;;
;; [[<Explanation]]
;;
;; Wiki-nav.el is a minor mode which recognizes [[wiki-style]]
;; double-bracketed navigation links in any type of file, providing
;; the ability to jump between sections, between files, or open
;; external links.
;;
;; Wiki-nav.el requires button-lock.el, which in turn requires
;; font-lock.el.  Font-lock.el is provided with Emacs.
;; Button-lock.el is available here
;;
;;     http://github.com/rolandwalker/button-lock
;;
;; [[<Example usage]]
;;
;;     Add the following to your ~/.emacs
;;
;;         (require 'wiki-nav)
;;         (global-wiki-nav-mode 1)
;;
;;     and sprinkle
;;
;;         [[links]]
;;
;;     throughout your files.  That's it.  There's more functionality,
;;     but simple [[links]] may be all you need.
;;
;;     Clicking a [[link]] will invoke a text search for the next
;;     matching link.  Double-clicking a link will search for matching
;;     links in all open buffers.
;;
;;     Text-matching between links is always case-insensitive.
;;
;;     To navigate upward to a previous matching link, add a '<'
;;     symbol before the search text
;;
;;         [[<links]]
;;
;;     You can insert the '>' symbol, too, but that simply indicates
;;     the default forward-search navigation.
;;
;;     Both forward and backward navigation will wrap around the ends
;;     of the file without prompting.
;;
;;     Leading and trailing space inside a link is ignored.
;;
;;     From the keyboard:
;;
;;         control-c control-w
;;
;;                       skip forward in the buffer to the next link
;;
;;         control-c control-W
;;
;;                       skip backward in the buffer to the previous link
;;
;;         return        if positioned on a link, activate it
;;
;;         tab           if positioned on a link, skip forward in the
;;                       buffer to the next link of any kind (need not
;;                       match the current link)
;;
;;         S-tab         if positioned on a link, skip backward in the
;;                       buffer to the previous link of any kind (need not
;;                       not match the current link)
;;
;; Advanced usage:
;;
;;     Bracketed links may contain external URLs
;;
;;         [[http://google.com]]
;;
;;     Or they may use various internally-recognized URI schemes:
;;
;;     visit: navigates to another file
;;
;;         [[visit:/etc/hosts]]
;;
;;         [[visit:/path/to/another/file:NameOfLink]]
;;
;;     func: navigates to the definition of a function
;;
;;         [[func:main]]
;;
;;     line: navigates to a line number
;;
;;         [[line:12]]
;;
;;     visit: may be combined with other schemes:
;;
;;         [[visit:/path/to/another/file:func:main]]
;;
;;         [[visit:/etc/hosts:line:5]]
;;
;;     Path names and similar strings are subjected to URI-style
;;     unescaping before lookup.  To link a filename which contains a
;;     colon, substitute "%3A" for the colon character.
;;
;;     See the documentation for the function wiki-nav for more
;;     information.
;;
;; [[<See Also]]
;;
;;     M-x customize-group RET wiki-nav RET
;;     M-x customize-group RET nav-flash RET
;;
;; [[<Prior Art]]
;;
;;     linkd.el
;;     David O'Toole <dto@gnu.org>
;;
;;     org-mode
;;     Carsten Dominik <carsten at orgmode dot org>
;;
;; [[<Notes]]
;;
;;     wiki-nav uses industry-standard left-clicks rather than
;;     Emacs-traditional middle clicks.
;;
;;     It is difficult to edit the text inside a link using the
;;     mouse.  To make a link inactive, position the point after the
;;     link and backspace into it.  Once the trailing delimiters have
;;     been modified, the link reverts to ordinary text.
;;
;; [[<Bugs]]
;;
;;     Only highlights first match on each comment line.
;;
;;     Double-square-brackets represent a valid construct in some
;;     programming languages (especially shell), and may be mistakenly
;;     linked.  Workaround: don't click.  Second workaround: add mode to
;;     wiki-nav-comment-only-modes via customize.  Third workaround:
;;     change delimiters triple-square-brackets via customize.
;;
;;     Newlines are not escaped in regexp fields in customize.
;;
;;     Case-sensitivity on matching the delimiters is unknown because
;;     it depends on how font-lock-defaults was called for the current
;;     mode.  However, this is not an issue unless the default delimiters
;;     are changed to use alphabetical characters.
;;
;;     Auto-complete interacts and causes keyboard interaction
;;     problems.  Auto-complete should be suppressed if the point is
;;     on a link?
;;
;;     Difficult to reproduce: keystrokes sometimes leaking through to
;;     the editor during keyboard navigation.  Tends to happen on first
;;     navigation, when key is pressed quickly?
;;
;;     The global minor mode causes button-lock to be turned off/back
;;     on for every buffer.
;;
;;     This package is generally incompatible with interactive modes
;;     such as `comint-mode' and derivatives, due conflicting uses
;;     of the rear-nonsticky text property.  To change this, set
;;     customizable variable wiki-nav-rear-nonsticky.
;;
;; [[<Compatibility and Requirements]]
;;
;;     GNU Emacs version 24.5-devel     : not tested
;;     GNU Emacs version 24.4           : yes
;;     GNU Emacs version 24.3           : yes
;;     GNU Emacs version 23.3           : yes
;;     GNU Emacs version 22.2           : yes, with some limitations
;;     GNU Emacs version 21.x and lower : unknown
;;
;;     Requires button-lock.el
;;
;;     Uses if present: nav-flash.el, back-button.el
;;
;; [[<Todo]]
;;
;;     ido support - document and provide default bindings
;;
;;     instead of comment-only modes, check if comment syntax is present
;;     in buffer as is done in fixmee-mode, and use syntax-ppss rather
;;     than regexp to detect comment context
;;
;;     support kbd-help property
;;
;;     follow the doc for defgroup to find link functions which are
;;     built-in to Emacs
;;
;;     these and other widgets are used in customize/help
;;     wiki-nav should reuse the widget functions (wid-edit.el and others)
;;         emacs-commentary-link
;;         emacs-library-link
;;     and the xref functions in help-mode.el
;;
;;     use a function matcher in font-lock keywords instead of regexp to
;;     get comment-only matches to work perfectly.  fixmee.el has correct
;;     code to match in comment
;;
;;     wiki-nav-external-link-pattern might be replaced with functions
;;     from url-util
;;
;;     visit:-1 counts from end of file
;;
;;     keyboard analog for double-click
;;
;;     right-click context menu
;;
;;     link any string <<<text>>> together within a file
;;     like org-mode radio links
;;
;;     patch font-lock to support keyword searching in comment only,
;;     like 'keep, only different - maybe not needed if using a func
;;     instead of a regexp in keyword
;;
;;     raised button style option
;;
;;     break down monolithic dispatch function wiki-nav-action-1
;;
;;     schemes to add
;;         search:
;;         regexp:
;;         elisp:
;;
;;     wiki-nav-links can be optimized by tracking which buffers are
;;     completely fontified - doesn't font-lock do that?
;;
;;     similarly, speed up wiki-nav-find-any-link by remembering if
;;     the buffer is fontified, or switch to searching by regexp
;;
;;     version of wiki-nav-find-any-link that does not wrap
;;
;;     wiki-nav-ido can only go to one occurrence of a duplicate -
;;     may not always be first
;;
;;     toggle key for switching to all buffers within wiki-nav-ido
;;     prompt
;;
;;     sort recently-used items first in wiki-nav-ido - see
;;     yas/insert-snippet for example
;;
;; [[<License]]
;;
;; Simplified BSD License
;;
;; Redistribution and use in source and binary forms, with or
;; without modification, are permitted provided that the following
;; conditions are met:
;;
;;    1. Redistributions of source code must retain the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer.
;;
;;    2. Redistributions in binary form must reproduce the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer in the documentation and/or other materials
;;       provided with the distribution.
;;
;; This software is provided by Roland Walker "AS IS" and any express
;; or implied warranties, including, but not limited to, the implied
;; warranties of merchantability and fitness for a particular
;; purpose are disclaimed.  In no event shall Roland Walker or
;; contributors be liable for any direct, indirect, incidental,
;; special, exemplary, or consequential damages (including, but not
;; limited to, procurement of substitute goods or services; loss of
;; use, data, or profits; or business interruption) however caused
;; and on any theory of liability, whether in contract, strict
;; liability, or tort (including negligence or otherwise) arising in
;; any way out of the use of this software, even if advised of the
;; possibility of such damage.
;;
;; The views and conclusions contained in the software and
;; documentation are those of the authors and should not be
;; interpreted as representing official policies, either expressed
;; or implied, of Roland Walker.
;;
;; [[<Code]]
;;; Code:
;;

;;; requirements

;; for callf, intersection
(require 'cl)

(require 'font-lock)
(require 'nav-flash nil t)
(require 'back-button nil t)

(autoload 'button-lock-mode "button-lock" "Toggle button-lock-mode, a minor mode for making text clickable.")

;;; declarations

(declare-function back-button-push-mark                   "back-button.el")
(declare-function back-button-push-mark-local-and-global  "back-button.el")
(declare-function button-lock-unset-button                "button-lock.el")
(declare-function button-lock-set-button                  "button-lock.el")
(declare-function button-lock-extend-binding              "button-lock.el")
(declare-function button-lock-find-extent                 "button-lock.el")
(declare-function button-lock-parent-modes                "button-lock.el")

(eval-when-compile
  (defvar button-lock-exclude-modes)
  (defvar button-lock-mode))

;;; customizable variables

;;;###autoload
(defgroup wiki-nav nil
  "Simple file navigation using [[WikiStrings]]."
  :version "1.0.2"
  :link '(emacs-commentary-link :tag "Commentary" "wiki-nav")
  :link '(url-link :tag "GitHub" "http://github.com/rolandwalker/button-lock")
  :link '(url-link :tag "EmacsWiki" "http://emacswiki.org/emacs/WikiNavMode")
  :prefix "wiki-nav-"
  :group 'navigation
  :group 'mouse
  :group 'convenience)

(defcustom wiki-nav-less-feedback nil
  "Give less echo area feedback."
  :type 'boolean
  :group 'wiki-nav)

(defcustom wiki-nav-mode-lighter " wikn"
  "This string appears in the mode-line when `wiki-nav-mode' is active.

Set to nil or the empty string to disable the mode-line
lighter for `wiki-nav-mode'."
  :group 'wiki-nav
  :type 'string)
(put 'wiki-nav-mode-lighter 'risky-local-variable t)

(defcustom wiki-nav-comment-only-modes '(
                                         cperl-mode
                                         emacs-lisp-mode
                                         lisp-mode
                                         perl-mode
                                         prog-mode
                                         python-mode
                                         ruby-mode
                                         sh-mode
                                         prog-mode
                                         )
  "List of major modes for which to constrain navigation links to comments only.

The constraint also applies to any major mode which is derived
from one of these modes.

Because the comment-only search is not built into font-lock, the
search must be less exact and/or less efficient.  This method is
particularly inexact, but avoids being slow.

It will not work for `c-mode' and many other modes which have
multi-line comments or multi-character comment delimiters."
  :type '(repeat symbol)
  :group 'wiki-nav)

(defcustom wiki-nav-rear-nonsticky t
  "Whether to set the 'rear-nonsticky property on wiki-nav buttons.

This value may be unset to stop `wiki-nav-mode' from attempting
to manage the 'rear-nonsticky text property, which may improve
compatibility with other modes that depend on setting the same
property (Example: ielm).

The default, t, is better for most users, because it keeps the
properties of the button from spuriously attaching to other
text."
  :type 'boolean
  :group 'wiki-nav)

(defcustom wiki-nav-multi-action-function 'wiki-nav-default-multi-action
  "Function to run on double-click of a wiki-nav link."
  :type 'function
  :group 'wiki-nav)

;;;###autoload
(defgroup wiki-nav-keys nil
  "Keyboard bindings used by wiki-nav"
  :group 'wiki-nav)

(defcustom wiki-nav-find-any-link-keys '("C-c C-w")
  "List of key sequences to search forward for the next defined wiki-nav link.

The search will automatically wrap past the end of the buffer.
The key binding is in effect anywhere in the buffer when wiki-nav
mode is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'wiki-nav-keys)

(defcustom wiki-nav-find-any-previous-link-keys '("C-c C-W")
  "List of key sequences to search backward for the previous wiki-nav link.

The search will automatically wrap past the beginning of the
buffer.  The key binding is in effect anywhere in the buffer when
wiki-nav mode is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'wiki-nav-keys)

(defcustom wiki-nav-activate-keys '("RET")
  "List of key sequences to activate a wiki-nav link under the point.

The key binding is active only when the point is on a wiki-nav link.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'wiki-nav-keys)

(defcustom wiki-nav-skip-to-next-keys '("<tab>")
  "List of key sequences to skip forward from a wiki-nav link to the next link.

The key binding is active only when the point is on a wiki-nav link.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'wiki-nav-keys)

(defcustom wiki-nav-skip-to-previous-keys '("S-TAB" "S-<tab>" "<backtab>" "S-<iso-lefttab>")
  "List of key sequences to skip back from a wiki-nav link to the previous link.

The key binding is active only when the point is on a wiki-nav link.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'wiki-nav-keys)

;;;###autoload
(defgroup wiki-nav-faces nil
  "Faces used by wiki-nav."
  :group 'wiki-nav)

(defface wiki-nav-link-face
   '((t (:inherit link)))
  "Face to show wiki-nav links"
  :group 'wiki-nav-faces)

(defface wiki-nav-mouse-face
   '((t (:inherit button-lock-mouse-face)))
  "Face to highlight wiki-nav link mouseovers"
  :group 'wiki-nav-faces)

;;;###autoload
(defgroup wiki-nav-parsing nil
  "Strings and regular expressions used by wiki-nav to define links."
  :group 'wiki-nav)

(defcustom wiki-nav-link-start   "[["
  "A string (not a regular expression) which open a wiki-style navigation link.

Since the construct [[text]] can show up for other reasons, you
might change this to \"[[[\"."
  :type 'string
  :group 'wiki-nav-parsing)

(defcustom wiki-nav-link-stop   "]]"
  "A string (not a regexp) which closes a wiki-style navigation link.

Since the construct [[text]] can show up for other reasons, you
might change this to \"]]]\"."
  :type 'string
  :group 'wiki-nav-parsing)

(defcustom wiki-nav-link-text  "[^][\n]+"
  "A regular expression defining the text inside wiki-style navigation links.

The value should exclude newlines and start/stop delimiters."
  :type 'regexp
  :group 'wiki-nav-parsing)

(defcustom wiki-nav-external-link-pattern "\\`[a-zA-Z]+:[^[:space:]]+"
  "A regular expression for recognizing URLs inside wiki-style navigation links.

The default is very permissive.  To be more strict, try

   \"\\\\`[a-zA-Z]+://[^[:space:]]+\",
or

   \"\\\\`http://[^[:space:]]+\".

Setting the value to the empty string will disable the feature
entirely, suppressing the recognition of external URLs."
  :type 'regexp
  :group 'wiki-nav-parsing)

(defcustom wiki-nav-visit-link-pattern "\\`visit:\\([^:\n]+?\\)\\(?:\\|:\\([^\n]*\\)\\)\\'"
  "A regular expression for recognizing wiki-nav links outside the current file.

The format defined by the default expression is delimited by colons

   visit:/posix/path/to/another/file

      or

   visit:/posix/path/to/another/file:WikiString

Other internally recognized link schemes may be substituted for
the WikiString

   visit:/posix/path/to/another/file:line:10

Set this value to the empty string to disable the feature entirely."
  :type 'regexp
  :group 'wiki-nav-parsing)

(defcustom wiki-nav-function-link-pattern "\\`func\\(?:tion\\)?:\\([^\n]+\\)\\'"
  "A regexp identifying wiki-nav links which point to function definitions.

The format defined by the default expression is delimited by colons

   func:function_name

Imenu is used to find the function definition.

Set this value to the empty string to disable the feature entirely."
  :type 'regexp
  :group 'wiki-nav-parsing)

(defcustom wiki-nav-line-number-link-pattern "\\`line:\\([0-9]+\\)\\'"
  "A regexp for identifying wiki-nav links which point to line numbers.

The format defined by the default expression is delimited by colons

   line:111

Set this value to the empty string to disable the feature entirely."
  :type 'regexp
  :group 'wiki-nav-parsing)

;;;###autoload
(defgroup wiki-nav-global nil
  "Settings for `global-wiki-nav-mode'."
  :group 'wiki-nav)

(defcustom wiki-nav-exclude-modes  '(
                                     fundamental-mode
                                     org-mode
                                     )
  "List of major modes in which global wiki-nav will not be activated.

A buffer will also be excluded if its major mode is derived from a mode in
this list.

This is in addition to any modes listed in `button-lock-exclude-modes'.

Modes may be excluded for reasons of security (since buttons can
execute arbitrary functions), efficiency, or to avoid conflicts
with modes that provide similar functionality."
  :type '(repeat symbol)
  :group 'wiki-nav-global)

(defcustom wiki-nav-buffer-name-exclude-pattern "\\`[* ]"
  "Do not activate minor made in buffers matching this regular expression.

Buffers may be excluded for reasons of security (since buttons
can execute arbitrary functions), efficiency, or to avoid
conflicts with modes that provide similar functionality.

The default pattern is designed to match buffers which are
programatically generated or internal to Emacs."
  :type 'regexp
  :group 'wiki-nav-global)

(defcustom wiki-nav-buffer-include-functions '()
  "Do not activate minor mode in a buffer unless all functions evaluate non-nil.

Each function should take a single argument (a buffer).

Set this value to nil to disable."
  :type '(repeat function)
  :group 'wiki-nav-global)

(defcustom wiki-nav-buffer-exclude-functions '()
  "Do not activate minor mode in a buffer if any function evaluates non-nil.

Each function should take a single argument (a buffer).

Set this value to nil to disable."
  :type '(repeat function)
  :group 'wiki-nav-global)

;;; variables

(defvar wiki-nav-mode nil "Mode variable for wiki-nav.")
(make-variable-buffer-local 'wiki-nav-mode)

(defvar wiki-nav-button nil "Holds the buffer-local button definition when the mode is active.")
(make-variable-buffer-local 'wiki-nav-button)

(defvar wiki-nav-mode-keymap
  (let ((map (make-sparse-keymap)))
    (dolist (key wiki-nav-find-any-link-keys)
      (define-key map (read-kbd-macro key)  'wiki-nav-find-any-link))
    (dolist (key wiki-nav-find-any-previous-link-keys)
      (define-key map (read-kbd-macro key) 'wiki-nav-find-any-previous-link))
    map))

;;; macros

(defmacro wiki-nav-called-interactively-p (&optional kind)
  "A backward-compatible version of `called-interactively-p'.

Optional KIND is as documented at `called-interactively-p'
in GNU Emacs 24.1 or higher."
  (cond
    ((not (fboundp 'called-interactively-p))
     '(interactive-p))
    ((condition-case nil
         (progn (called-interactively-p 'any) t)
       (error nil))
     `(called-interactively-p ,kind))
    (t
     '(called-interactively-p))))

;;; compatibility functions

(unless (fboundp 'back-button-push-mark-local-and-global)
  (fset 'back-button-push-mark (symbol-function 'push-mark))
  (defun back-button-push-mark-local-and-global (&optional location nomsg activate consecutives)
  "Push mark at LOCATION, and unconditionally add to `global-mark-ring'.

This function differs from `push-mark' in that `global-mark-ring'
is always updated.

LOCATION is optional, and defaults to the current point.

NOMSG and ACTIVATE are as documented at `push-mark'.

When CONSECUTIVES is set to 'limit and the new mark is in the same
buffer as the first entry in `global-mark-ring', the first entry
in `global-mark-ring' will be replaced.  Otherwise, a new entry
is pushed onto `global-mark-ring'.

When CONSECUTIVES is set to 'allow-dupes, it is possible to push
an exact duplicate of the current topmost mark onto `global-mark-ring'."
  (callf or location (point))
  (back-button-push-mark location nomsg activate)
  (when (or (eq consecutives 'allow-dupes)
            (not (equal (mark-marker)
                        (car global-mark-ring))))
    (when (and (eq consecutives 'limit)
               (eq (marker-buffer (car global-mark-ring)) (current-buffer)))
      (move-marker (car global-mark-ring) nil)
      (pop global-mark-ring))
    (push (copy-marker (mark-marker)) global-mark-ring)
    (when (> (length global-mark-ring) global-mark-ring-max)
      (move-marker (car (nthcdr global-mark-ring-max global-mark-ring)) nil)
      (setcdr (nthcdr (1- global-mark-ring-max) global-mark-ring) nil)))))

;;; utility functions

;; generic utility functions
(defun wiki-nav-point-before ()
  "Return the position before the current point.

Returns `point-min' if the point is at the minimum."
  (max (point-min) (1- (point))))

(defun wiki-nav-comment-only-mode-p ()
  "Return true if links should be constrained to comments in the current mode."
  (delq nil (mapcar 'derived-mode-p wiki-nav-comment-only-modes)))

(defun wiki-nav-alist-flatten (list)
  "Flatten LIST which may contain other lists.  Do not flatten cons cells."
  (cond
    ((null list)
     nil)
    ((and (consp list)
          (nthcdr (safe-length list) list))
     (list list))
    ((and (listp list)
          (consp (car list)))
     (append (wiki-nav-alist-flatten (car list)) (wiki-nav-alist-flatten (cdr list))))
    ((listp list)
     (cons (car list) (wiki-nav-alist-flatten (cdr list))))
    (t
     (list list))))

;; buffer functions

(defun wiki-nav-buffer-included-p (buf)
  "Return BUF if global wiki-nav should enable wiki-nav in BUF."
  (when (and (not noninteractive)
             (bufferp buf)
             (buffer-name buf))
    (require 'button-lock)
    (with-current-buffer buf
      (when (and (not (minibufferp buf))
                 (not (eq (aref (buffer-name) 0) ?\s))           ; overlaps with exclude-pattern
                 (not (memq major-mode button-lock-exclude-modes))
                 (not (memq major-mode wiki-nav-exclude-modes))
                 (not (intersection (button-lock-parent-modes) button-lock-exclude-modes))
                 (not (intersection (button-lock-parent-modes) wiki-nav-exclude-modes))
                 (not (string-match-p wiki-nav-buffer-name-exclude-pattern (buffer-name buf)))
                 (catch 'success
                   (dolist (filt wiki-nav-buffer-exclude-functions)
                     (when (funcall filt buf)
                       (throw 'success nil)))
                   t)
                 (catch 'failure
                   (dolist (filt wiki-nav-buffer-include-functions)
                     (unless (funcall filt buf)
                       (throw 'failure nil)))
                   t))
        buf))))

;; link functions
(defun wiki-nav-link-set (&optional arg)
  "Use `button-lock-mode' to set up wiki-nav links in a buffer.

If called with negative ARG, remove the links."
  (callf or arg 1)
  (when (and (>= arg 0)
             (or (not (boundp 'button-lock-mode))
                 (not button-lock-mode)))
    (button-lock-mode 1))

  (if (< arg 0)
      (button-lock-unset-button wiki-nav-button)
    (setq wiki-nav-button (button-lock-set-button (concat (if (wiki-nav-comment-only-mode-p) "\\s<\\S>*?" "")
                                                          (regexp-quote wiki-nav-link-start)
                                                          "\\(" wiki-nav-link-text "\\)"
                                                          (regexp-quote wiki-nav-link-stop))
                                                  'wiki-nav-mouse-action
                                                  :double-mouse-1 wiki-nav-multi-action-function
                                                  :face 'wiki-nav-link-face :mouse-face 'wiki-nav-mouse-face :face-policy 'prepend
                                                  :additional-property 'wiki-nav
                                                  :rear-sticky wiki-nav-rear-nonsticky
                                                  :grouping 1))
    (dolist (key wiki-nav-activate-keys)
      (button-lock-extend-binding wiki-nav-button 'wiki-nav-keyboard-action         nil key))
    (dolist (key wiki-nav-skip-to-next-keys)
      (button-lock-extend-binding wiki-nav-button 'wiki-nav-find-any-link           nil key))
    (dolist (key wiki-nav-skip-to-previous-keys)
      (button-lock-extend-binding wiki-nav-button 'wiki-nav-find-any-previous-link  nil key))))

(defun wiki-nav-links (&optional buffer)
  "Return an alist of all wiki-nav links in BUFFER (defaults to current buffer).

The return value is an alist of cells in the form (\"text\" buffer . start-pos)."
  (callf or buffer (current-buffer))
  (with-current-buffer buffer
    (when wiki-nav-mode
      (let ((font-lock-fontify-buffer-function 'font-lock-default-fontify-buffer)
            (pos nil)
            (links nil))
        (font-lock-fontify-buffer)
        (setq pos (next-single-property-change (point-min) 'wiki-nav))
        (while (and pos
                    (< pos (point-max)))
          (when (get-text-property pos 'wiki-nav)
            (let ((start pos))
              (while (and pos
                          (< pos (point-max))
                          (get-text-property pos 'wiki-nav))
                (callf next-single-property-change pos 'wiki-nav))
              (when (not (get-text-property pos 'wiki-nav))
                (push (cons (buffer-substring-no-properties start pos) (cons buffer start)) links))))
          (callf next-single-property-change pos 'wiki-nav))
        links))))

(defun wiki-nav-links-all-buffers ()
  "Return an alist of wiki-nav links in all buffers.  See `wiki-nav-links'.

Note that this function fontifies every buffer, which can take
seconds to complete."
  (let ((reporter (make-progress-reporter "Searching ..." 0 (length (buffer-list))))
        (counter 0)
        (l-alist nil))
    (dolist (buf (buffer-list))
      (unless wiki-nav-less-feedback
        (progress-reporter-update reporter (incf counter)))
      (push (wiki-nav-links buf) l-alist))
    (progress-reporter-done reporter)
    (delq nil (wiki-nav-alist-flatten l-alist))))

;; bindable action dispatch commands
;;;###autoload
(defun wiki-nav-default-multi-action (event)
  "Dispatch the default double-click navigation action.

The link used is that identified by the position at EVENT, a
mouse event."
  (interactive "e")
  (let ((bounds (button-lock-find-extent (posn-point (event-end event)) 'wiki-nav))
        (str-val nil)
        (case-fold-search t)
        (search-upper-case nil))
    (when bounds
      (setq str-val (replace-regexp-in-string "\\(^[[:space:]<>]*\\|[[:space:]]*\\'\\)" ""
                                             (buffer-substring-no-properties (car bounds) (cdr bounds))))
      (when (fboundp 'multi-occur-in-matching-buffers)
        (multi-occur-in-matching-buffers "\\`[^ *]"
                                         (concat
                                          (regexp-quote wiki-nav-link-start)
                                          "[[:space:]<>]*" str-val "[[:space:]]*"
                                          (regexp-quote wiki-nav-link-stop))
                                          t)))))

;; Monolithic function to dispatch any link action.
(defun wiki-nav-action-1 (pos)
  "Dispatch the default navigation action for the wiki-nav link at POS."
  (let ((bounds (button-lock-find-extent pos 'wiki-nav))
        (str-val nil)
        (found nil)
        (visit nil)
        (search-function 're-search-forward)
        (wrap-point (point-min))
        (wrap-message "Search wrapped past end of file")
        (buffer-start (current-buffer))
        (point-start (point))
        (new-point nil)
        (case-fold-search t)
        (search-upper-case nil))
    (when bounds
      (setq str-val (buffer-substring-no-properties (car bounds) (cdr bounds)))
      (when (string-match-p "^[[:space:]]*<" str-val)
        (setq search-function 're-search-backward)
        (setq wrap-point (point-max))
        (setq wrap-message "Search wrapped past beginning of file"))
      (setq str-val (replace-regexp-in-string "\\(^[[:space:]<>]*\\|[[:space:]]*\\'\\)" "" str-val))
      (if (and wiki-nav-external-link-pattern
               (and (> (length wiki-nav-visit-link-pattern) 0)
                    (not (string-match-p wiki-nav-visit-link-pattern str-val)))
               (and (> (length wiki-nav-function-link-pattern) 0)
                    (not (string-match-p wiki-nav-function-link-pattern str-val)))
               (and (> (length wiki-nav-line-number-link-pattern) 0)
                    (not (string-match-p wiki-nav-line-number-link-pattern str-val)))
               (and (> (length wiki-nav-external-link-pattern) 0)
                    (string-match-p wiki-nav-external-link-pattern str-val)))
          (progn
            (message "browsing to external URL...")
            (browse-url str-val))
        (save-match-data
          (when (and (> (length wiki-nav-visit-link-pattern) 0)
                     (string-match wiki-nav-visit-link-pattern str-val))
            (let ((tmp ""))
              (setq tmp (match-string-no-properties 2 str-val))
              (switch-to-buffer (find-file (expand-file-name (url-unhex-string (match-string-no-properties 1 str-val)))))
              (setq str-val tmp))
            (back-button-push-mark-local-and-global point-start t)
            (when (and (= (length str-val) 0)
                       (fboundp 'nav-flash-show))
              (nav-flash-show))
            (setq visit t))
          (when (> (length str-val) 0)
            (cond
              ((and (> (length wiki-nav-function-link-pattern) 0)
                    (string-match wiki-nav-function-link-pattern str-val))
               ;; imenu return value is not helpful.  It also sometimes changes the mark. Wrap it in an excursion
               (when (and (setq new-point (save-excursion (imenu (url-unhex-string (match-string-no-properties 1 str-val))) (point)))
                          (not (= new-point (point))))
                 (back-button-push-mark-local-and-global point-start t)
                 (goto-char new-point)
                 (when (fboundp 'nav-flash-show)
                   (nav-flash-show))
                 (setq found :func))
               ;; return to the original buffer on failure
               (unless found
                 (when (and visit
                            (> (length str-val) 0))
                   (switch-to-buffer buffer-start)
                   (setq visit nil))
                 (goto-char point-start)))
              ((and (> (length wiki-nav-line-number-link-pattern) 0)
                    (string-match wiki-nav-line-number-link-pattern str-val))
               ;; For line-number scheme, go as far as possible, but don't set found unless successful.
               ;; Don't worry about returning to original buffer on failure.
               (let ((ln (string-to-number (match-string-no-properties 1 str-val))))
                 (widen)
                 (back-button-push-mark-local-and-global point-start t)
                 (goto-char (point-min))
                 (forward-line (1- ln))
                 (when (fboundp 'nav-flash-show)
                   (nav-flash-show))
                 (if (= (line-number-at-pos) ln)
                     (setq found :line))))
              (t
               (setq str-val (regexp-quote (url-unhex-string str-val)))
               (deactivate-mark)
               (if (funcall search-function (concat (if (wiki-nav-comment-only-mode-p) "\\s<\\S>*?" "")
                                                    "\\("
                                                    (regexp-quote wiki-nav-link-start)
                                                    "\\("
                                                    "[[:space:]<>]*" str-val "[[:space:]]*"
                                                    "\\)"
                                                    (regexp-quote wiki-nav-link-stop)
                                                    "\\)")
                            nil t)
                   (progn
                     (setq found :jump)
                     (back-button-push-mark-local-and-global point-start t)
                     (goto-char (match-beginning 2))
                     (when (fboundp 'nav-flash-show)
                       (nav-flash-show)))
                 ;; else
                 (goto-char wrap-point)
                 (deactivate-mark)
                 (if (funcall search-function (concat (if (wiki-nav-comment-only-mode-p) "\\s<\\S>*?" "")
                                                      "\\("
                                                      (regexp-quote wiki-nav-link-start)
                                                      "\\("
                                                      "[[:space:]<>]*" str-val "[[:space:]]*"
                                                      "\\)"
                                                      (regexp-quote wiki-nav-link-stop)
                                                      "\\)")
                              nil t)
                     (progn
                       (setq found :wrap)
                       (back-button-push-mark-local-and-global point-start t)
                       (goto-char (match-beginning 2))
                       (when (fboundp 'nav-flash-show)
                         (nav-flash-show)))))
               ;; return to the original buffer on failure
               (unless found
                 (when (and visit
                            (> (length str-val) 0))
                   (switch-to-buffer buffer-start)
                   (setq visit nil))
                 (goto-char point-start))))
            (cond
              (visit
               (unless wiki-nav-less-feedback
                 (message "followed link to new file")))
              ((or (not found)
                   (and (>= (point) (- (car bounds) (length wiki-nav-link-start)))
                        (<= (point) (+ (cdr bounds) (length wiki-nav-link-stop)))))
               ;; give failure message even when wiki-nav-less-feedback is set
               (message "no matching link found"))
              ((eq found :wrap)
               (unless wiki-nav-less-feedback
                 (message wrap-message))))))))
    found))

;;;###autoload
(defun wiki-nav-mouse-action (event)
  "Dispatch the default action for the wiki-nav link at the mouse location.

Mouse location is defined by the mouse event EVENT."
  (interactive "e")
  (wiki-nav-action-1 (posn-point (event-end event))))

;;;###autoload
(defun wiki-nav-keyboard-action ()
  "Dispatch the default navigation action for the wiki-nav link under the point."
  (interactive)
  (wiki-nav-action-1 (point)))

;;; minor mode definition

;;;###autoload
(define-minor-mode wiki-nav-mode
  "Turn on navigation by bracketed [[WikiStrings]] within a document.

When wiki-nav links are activated, clicking on a bracketed link
causes emacs to search the document for another link with text
matching the inner string.  If a match is found, the cursor is
moved to the location of the match.

If the string looks like it might be a URL (starts with
alphabetical characters followed by a colon), an external browser
will be spawned on the URL.  This behavior can be controlled by the
customizable variable `wiki-nav-external-link-pattern'.

If `multi-occur' is installed (standard with recent Emacs),
double-clicking a wiki-nav link will search for matching links in
all open file buffers.

If the link follows the form

   visit:/path/name:WikiString

Emacs will visit the named file, and search for the navigation
string there.  This behavior can be controlled by the customizable
variable `wiki-nav-visit-link-pattern'.

If the link follows the form

   func:FunctionName

the link will lead to the definition of the given function, as
defined by imenu. This behavior can be controlled by the
customizable variable `wiki-nav-function-link-pattern'.

If the link follows the form

   line:<digits>

the link will lead to the given line number.  This behavior can
be controlled by the customizable variable
`wiki-nav-line-number-link-pattern'.

The leading and trailing delimiters which define the navigation
links may be customized, as may the regular expressions that
match URLs and non-URL inner text.

With no argument, this command toggles the mode.  Non-null prefix
argument turns on the mode.  Null prefix argument turns off the
mode."
  nil wiki-nav-mode-lighter wiki-nav-mode-keymap
  (cond
    ((and wiki-nav-mode
          (or noninteractive                    ; never turn on wiki-nav where
              (eq (aref (buffer-name) 0) ?\s))) ; there can be no font-lock
     (setq wiki-nav-mode nil))
    (wiki-nav-mode
     (wiki-nav-link-set)
     (when (wiki-nav-called-interactively-p 'interactive)
       (message "wiki-nav mode enabled")))
    (t
     (wiki-nav-link-set -1)
     (when (wiki-nav-called-interactively-p 'interactive)
       (message "wiki-nav mode disabled")))))

;;; global minor-mode definition

(defun wiki-nav-maybe-turn-on (&optional arg)
  "Called by `global-wiki-nav-mode' to activate `wiki-nav-mode' in a buffer.

`wiki-nav-mode' will be activated in every buffer, except

   minibuffers
   buffers with names that begin with space
   buffers excluded by `wiki-nav-exclude-modes'
   buffers excluded by `button-lock-exclude-modes'
   buffers excluded by `wiki-nav-buffer-name-exclude-pattern'
   buffers excluded by `button-lock-buffer-name-exclude-pattern'

If called with a negative ARG, deactivate `wiki-nav-mode' in the buffer."
  (callf or arg 1)
  (when (or (< arg 0)
            (wiki-nav-buffer-included-p (current-buffer)))
    (wiki-nav-mode arg)))

;;;###autoload
(define-globalized-minor-mode global-wiki-nav-mode wiki-nav-mode wiki-nav-maybe-turn-on
  :group 'wiki-nav)

;;; interactive commands

;;;###autoload
(defun wiki-nav-find-any-link (&optional arg)
  "Skip forward to the next defined wiki-nav link.

Automatically wraps past the end of the buffer.

With a negative prefix argument ARG, skip backward to the
previous defined wiki-nav link."
  (interactive "p")
  (when wiki-nav-mode
    (let ((font-lock-fontify-buffer-function 'font-lock-default-fontify-buffer)
          (newpos nil)
          (orig-pos (point))
          (skip-function 'next-single-property-change)
          (search-function 're-search-forward)
          (look-function 'point)
          (wrap-point (point-min))
          (bounds nil))

      ;; This is slow, but otherwise links get missed.  There
      ;; must be a better way.
      (font-lock-fontify-buffer)

      (when (and arg
                 (< arg 0))
        (setq skip-function 'previous-single-property-change)
        (setq search-function 're-search-backward)
        (setq wrap-point (point-max))
        (setq look-function 'wiki-nav-point-before))
      ;; get out of the current link if we are in one
      (when (and (get-text-property (funcall look-function) 'wiki-nav)
                 (setq newpos (funcall skip-function (point) 'wiki-nav)))
        (goto-char newpos))
      ;; find the next link
      (deactivate-mark)
      (if (funcall search-function (concat (if (wiki-nav-comment-only-mode-p) "\\s<\\S>*?" "")
                                           "\\("
                                           (regexp-quote wiki-nav-link-start)
                                           "\\("
                                           wiki-nav-link-text
                                           "\\)"
                                           (regexp-quote wiki-nav-link-stop)
                                           "\\)")
                   nil t)

          (progn
            (back-button-push-mark-local-and-global orig-pos t)
            (goto-char (match-beginning 2))
            (when (fboundp 'nav-flash-show)
              (nav-flash-show)))
        ;; else
        (goto-char wrap-point)
        (deactivate-mark)
        (when (funcall search-function (concat (if (wiki-nav-comment-only-mode-p) "\\s<\\S>*?" "")
                                               "\\("
                                               (regexp-quote wiki-nav-link-start)
                                               "\\("
                                               wiki-nav-link-text
                                               "\\)"
                                               (regexp-quote wiki-nav-link-stop)
                                               "\\)")
                       nil t)
          (back-button-push-mark-local-and-global orig-pos t)
          (goto-char (match-beginning 2))
          (when (fboundp 'nav-flash-show)
            (nav-flash-show)))))))

;;;###autoload
(defun wiki-nav-find-any-previous-link ()
  "Skip backward to the previous defined wiki-nav link.

Automatically wraps past the beginning of the buffer.

With a negative prefix argument ARG, skip backward to the
previous defined wiki-nav link."
  (interactive)
  (wiki-nav-find-any-link -1))

;;;###autoload
(defun wiki-nav-ido (arg)
  "Navigate to wiki-nav strings using `ido-completing-read'.

With universal prefix ARG, navigate to wiki-nav strings in all
buffers."
  (interactive "P")
  (let* ((links (if (consp arg) (wiki-nav-links-all-buffers) (wiki-nav-links)))
         (str-list (delete-dups (mapcar 'car links)))
         (choice nil)
         (ido-mode t))
     (setq choice (ido-completing-read "WikiString: " str-list))
     (when (and choice (assoc choice links))
       (back-button-push-mark-local-and-global nil t)
       (setq choice (cdr (assoc choice links)))
       (switch-to-buffer (car choice))
       (goto-char (cdr choice))
       (when (fboundp 'nav-flash-show)
         (nav-flash-show)))))

(provide 'wiki-nav)

;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions redefine)
;; End:
;;

;;; wiki-nav.el ends here
