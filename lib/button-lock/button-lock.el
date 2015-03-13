;;; button-lock.el --- Clickable text defined by regular expression
;;
;; Copyright (c) 2011-2015 Roland Walker
;;
;; Author: Roland Walker <walker@pobox.com>
;; Homepage: http://github.com/rolandwalker/button-lock
;; URL: http://raw.githubusercontent.com/rolandwalker/button-lock/master/button-lock.el
;; Version: 1.0.2
;; Last-Updated: 21 Feb 2015
;; EmacsWiki: ButtonLockMode
;; Keywords: mouse, button, hypermedia, extensions
;;
;; Simplified BSD License
;;
;;; Commentary:
;;
;; Quickstart
;;
;;     (require 'button-lock)
;;
;;     (global-button-lock-mode 1)
;;
;;     (setq url-button (button-lock-set-button
;;                       "\\<http://[^[:space:]\n]+"
;;                       'browse-url-at-mouse
;;                       :face 'link :face-policy 'prepend))
;;
;; Explanation
;;
;; Button-lock is a minor mode which provides simple facilities to
;; define clickable text based on regular expressions.  Button-lock.el
;; piggybacks on font-lock.el, and is efficient.  Overlays are not
;; used.
;;
;; Button-lock buttons (links) can execute any function.
;;
;; There is little user-level interface for button-lock.el, which is
;; intended to be used from Emacs Lisp.  For a user-friendly library
;; built on top of button-lock.el, see wiki-nav.el or fixmee.el
;;
;;     http://github.com/rolandwalker/button-lock/blob/master/wiki-nav.el
;;     http://github.com/rolandwalker/fixmee
;;
;; Example usage
;;
;;     (require 'button-lock)
;;     (global-button-lock-mode 1)
;;
;;     ;; add a mouseable button to all occurrences of a word
;;     (button-lock-set-button "hello" 'beginning-of-line)
;;
;;     ;; to remove that button later, pass all the same arguments to
;;     ;; button-lock-unset-button
;;     (button-lock-unset-button "hello" 'beginning-of-line)
;;
;;     ;; or, save the result and pass it back to the unset function
;;     (setq mybutton (button-lock-set-button "hello" 'beginning-of-line))
;;     (button-lock-unset-button mybutton)
;;
;;     ;; create a fancy raised button
;;     (require 'cus-edit)
;;     (button-lock-set-button "hello" #'(lambda ()
;;                                               (interactive)
;;                                               (save-match-data
;;                                                 (deactivate-mark)
;;                                                 (if (re-search-forward "hello" nil t)
;;                                                     (goto-char (match-beginning 0))
;;                                                   (goto-char (point-min))
;;                                                   (deactivate-mark)
;;                                                   (if (re-search-forward "hello" nil t)
;;                                                       (goto-char (match-beginning 0))))))
;;                             :face 'custom-button-face :mouse-face 'custom-button-mouse)
;;
;;     ;; activate hyperlinks
;;     (button-lock-set-button "\\<http://[^[:space:]\n]+"
;;                             'browse-url-at-mouse
;;                             :face 'link :face-policy 'prepend)
;;
;;     ;; activate hyperlinks only in lines that begin with a comment character
;;     (button-lock-set-button "^\\s-*\\s<.*?\\<\\(http://[^[:space:]\n]+\\)"
;;                             'browse-url-at-mouse
;;                             :face 'link :face-policy 'prepend :grouping 1)
;;
;;     ;; turn folding-mode delimiters into mouseable buttons
;;     (add-hook 'folding-mode-hook  #'(lambda ()
;;                                       (button-lock-mode 1)
;;                                       (button-lock-set-button
;;                                        (concat "^" (regexp-quote (car (folding-get-mode-marks))))
;;                                        'folding-toggle-show-hide)
;;                                       (button-lock-set-button
;;                                        (concat "^" (regexp-quote (cadr (folding-get-mode-marks))))
;;                                        'folding-toggle-show-hide)))
;;
;;     ;; create a button that responds to the keyboard, but not the mouse
;;     (button-lock-set-button "\\<http://[^[:space:]\n]+"
;;                             'browse-url-at-point
;;                             :mouse-binding     nil
;;                             :mouse-face        nil
;;                             :face             'link
;;                             :face-policy      'prepend
;;                             :keyboard-binding "RET")
;;
;;     ;; define a global button, to be set whenever the minor mode is activated
;;     (button-lock-register-global-button "hello" 'beginning-of-line)
;;
;; Interface
;;
;; Button-lock is intended to be used via the following functions
;;
;;     `button-lock-set-button'
;;     `button-lock-unset-button'
;;     `button-lock-extend-binding'
;;     `button-lock-clear-all-buttons'
;;     `button-lock-register-global-button'
;;     `button-lock-unregister-global-button'
;;     `button-lock-unregister-all-global-buttons'
;;
;; See Also
;;
;;     M-x customize-group RET button-lock RET
;;
;; Prior Art
;;
;;     hi-lock.el
;;     David M. Koppelman <koppel@ece.lsu.edu>
;;
;;     buttons.el
;;     Miles Bader <miles@gnu.org>
;;
;; Notes
;;
;;     By default, button-lock uses newfangled left-clicks rather than
;;     Emacs-traditional middle clicks.
;;
;;     Font lock is very efficient, but it is still possible to bog
;;     things down if you feed it expensive regular expressions.  Use
;;     anchored expressions, and be careful about backtracking.  See
;;     `regexp-opt'.
;;
;;     Some differences between button-lock.el and hi-lock.el:
;;
;;         * The purpose of hi-lock.el is to change the _appearance_
;;           of keywords.  The purpose of button-lock is to change the
;;           _bindings_ on keywords.
;;
;;         * Hi-lock also supports embedding new keywords in files,
;;           which is too risky of an approach for button-lock.
;;
;;         * Hi-lock supports overlays and can work without font-lock.
;;
;;     Some differences between button-lock.el and buttons.el
;;
;;         * Buttons.el is for inserting individually defined
;;           buttons.  Button-lock.el is for changing all matching text
;;           into a button.
;;
;; Compatibility and Requirements
;;
;;     GNU Emacs version 24.5-devel     : not tested
;;     GNU Emacs version 24.4           : yes
;;     GNU Emacs version 24.3           : yes
;;     GNU Emacs version 23.3           : yes
;;     GNU Emacs version 22.2           : yes, with some limitations
;;     GNU Emacs version 21.x and lower : unknown
;;
;;     No external dependencies
;;
;; Bugs
;;
;;     Case-sensitivity of matches depends on how font-lock-defaults
;;     was called for the current mode (setting
;;     font-lock-keywords-case-fold-search).  So, it is safest to
;;     assume that button-lock pattern matches are case-sensitive --
;;     though they might not be.
;;
;;     Return value for button-lock-register-global-button is inconsistent
;;     with button-lock-set-button.  The global function does not
;;     return a button which could be later passed to
;;     button-lock-extend-binding, nor are the arguments parsed and
;;     checked for validity.  Any errors for global buttons are also
;;     deferred until the mode is activated.
;;
;;     This package is generally incompatible with interactive modes
;;     such as `comint-mode' and derivatives, due conflicting uses
;;     of the rear-nonsticky text property.  To change this, :rear-sticky
;;     can be set when `calling button-lock-set-button'.  See also
;;     https://github.com/rolandwalker/fixmee/issues/8#issuecomment-75397467 .
;;
;; TODO
;;
;;     Validate arguments to button-lock-register-global-button.
;;     maybe split set-button into create/set functions, where
;;     the create function does all validation and returns a
;;     button object.  Pass in button object to unset as well.
;;
;;     Why are mouse and keyboard separate, can't mouse be passed
;;     through kbd macro?  The issue may have been just surrounding
;;     mouse events with "<>" before passing to kbd.
;;
;;     Look into new syntax-propertize-function variable (Emacs 24.x).
;;
;;     A refresh function to toggle every buffer?
;;
;;     Peek into font-lock-keywords and deduplicate based on the
;;     stored patterns.
;;
;;     Substitute a function for regexp to make properties invisible
;;     unless button-lock mode is on - esp for keymaps.
;;
;;     Add predicate argument to button-set where predicate is
;;     evaluated during matcher.  This could be used to test for
;;     comment-only.
;;
;;     Consider defining mode-wide button locks (pass the mode as the
;;     first argument of font-lock-add-keywords).  Could use functions
;;     named eg button-lock-set-modal-button.
;;
;;     Add a language-specific navigation library (header files in C,
;;     etc).
;;
;;     Example of exchanging text values on wheel event.
;;
;;     Convenience parameters for right-click menus.
;;
;;     Button-down visual effects as with Emacs widgets.
;;
;; License
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
;; Ths software is provided by Roland Walker "AS IS" and any express
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
;;; Change Log:
;;
;; 22 Aug 2012
;; Rewrite.  Incompatible changes:
;;
;;     * `button-lock-pop-button' removed, replaced with the ability to
;;        pass a button "object" to `button-lock-unset-button'.
;;
;;     * `button-lock-unset-all-buttons' replaced by
;;       `button-lock-clear-all-buttons'.
;;
;;     * `button-lock-set-global-button' and `button-lock-unset-global-button'
;;       replaced by `button-lock-register-global-button' and
;;       `button-lock-unregister-global-button'.
;;
;;     * `button-lock-unset-all-global-buttons' replaced by
;;       `button-lock-unregister-all-global-buttons'.
;;
;;     * `button-lock-pop-global-button' removed.
;;
;;     * lighter variable name and content changed.
;;
;;; Code:
;;

;;; requirements

;; for callf, callf2, defun*, union, intersection
(require 'cl)

(require 'font-lock)

;;; customizable variables

;;;###autoload
(defgroup button-lock nil
  "Clickable text defined by regular expression."
  :version "1.0.2"
  :link '(emacs-commentary-link :tag "Commentary" "button-lock")
  :link '(url-link :tag "GitHub" "http://github.com/rolandwalker/button-lock")
  :link '(url-link :tag "EmacsWiki" "http://emacswiki.org/emacs/ButtonLockMode")
  :prefix "button-lock-"
  :group 'navigation
  :group 'mouse
  :group 'extensions)

(defcustom button-lock-exclude-modes '(
                                       fundamental-mode
                                       Buffer-menu-mode
                                       bm-show-mode
                                       dired-mode
                                       wdired-mode
                                       gnus-article-mode
                                       mime/viewer-mode
                                       rmail-mode
                                       term-mode
                                       comint-mode
                                       shell-mode
                                       eshell-mode
                                       inferior-emacs-lisp-mode
                                       )
  "Modes for which global button-lock will not be activated.

A buffer will also be excluded if its major mode is derived from
a mode in this list.

Modes may be excluded for reasons of security (since buttons can
execute arbitrary functions), efficiency, or to avoid conflicts
with modes that provide similar functionality."
  :type '(repeat symbol)
  :group 'button-lock)

(defcustom button-lock-buffer-name-exclude-pattern "\\`[* ]"
  "Do not activate minor made in buffers matching this regular expression.

Buffers may be excluded for reasons of security (since buttons
can execute arbitrary functions), efficiency, or to avoid
conflicts with modes that provide similar functionality.

The default pattern is designed to match buffers which are
programatically generated or internal to Emacs."
  :type 'regexp
  :group 'button-lock)

(defcustom button-lock-buffer-include-functions '()
  "Do not activate minor mode in a buffer unless all functions evaluate non-nil.

Each function should take a single argument (a buffer).

Set this value to nil to disable."
  :type '(repeat function)
  :group 'button-lock)

(defcustom button-lock-buffer-exclude-functions '()
  "Do not activate minor mode in a buffer if any function evaluates non-nil.

Each function should take a single argument (a buffer).

Set this value to nil to disable."
  :type '(repeat function)
  :group 'button-lock)

(defcustom button-lock-mode-lighter " b-loc"
  "This string appears in the mode-line when `button-lock-mode' is active.

Set to nil or the empty string to disable the mode-line
lighter for `button-lock-mode'."
  :type 'string
  :group 'button-lock)
(put 'button-lock-mode-lighter 'risky-local-variable t)

;;; faces

(defface button-lock-button-face
    '((t nil))
    "Face used to show active button-lock buttons.

The default is for buttons to inherit whatever properties are
already provided by font-lock."
    :group 'button-lock)

(defface button-lock-mouse-face
   '((t (:inherit highlight)))
   "Face used to highlight button-lock buttons when the mouse hovers over."
   :group 'button-lock)

;;; variables

(defvar button-lock-global-button-list nil
  "Global button definitions added to every button-lock buffer.

The form is a list of lists, each member being a set of arguments
to `button-lock-set-button'.

This variable should be set by calling
`button-lock-register-global-button' and friends.")

(defvar button-lock-button-list nil
  "An internal variable used to keep track of button-lock buttons.")

(defvar button-lock-parent-modes-hash (make-hash-table)
  "A hash for memoizing `button-lock-parent-modes'.")

(defvar button-lock-mode nil
  "Mode variable for `button-lock-mode'.")

(make-variable-buffer-local 'button-lock-mode)
(make-variable-buffer-local 'button-lock-button-list)
(put 'button-lock-button-list 'permanent-local t)

;;; macros

(defmacro button-lock-called-interactively-p (&optional kind)
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

;; string-match-p is new in 23.x and above
(unless (fboundp 'string-match-p)
  (defsubst string-match-p (regexp string &optional start)
    "Same as `string-match' except this function does not change the match data."
    (let ((inhibit-changing-match-data t))
      (string-match regexp string start))))

;;; utility functions

;; general functions

(defun button-lock-parent-modes ()
  "Return all parent modes for the current major mode.

Returns nil if the current major mode is not a derived mode."
  (let ((this-mode major-mode)
        (parent-modes nil))
    (unless (setq parent-modes (gethash major-mode button-lock-parent-modes-hash))
      (while (setq this-mode (get this-mode 'derived-mode-parent))
        (push this-mode parent-modes))
      (puthash major-mode (if parent-modes parent-modes :none) button-lock-parent-modes-hash))
    (if (eql parent-modes :none) nil parent-modes)))

;; buffer functions

(defun button-lock-buffer-included-p (buf)
  "Return BUF if global button-lock should enable button-lock in BUF."
  (when (and (not noninteractive)
             (bufferp buf)
             (buffer-name buf))
    (with-current-buffer buf
      (when (and (not (minibufferp buf))
                 (not (eq (aref (buffer-name) 0) ?\s))           ; overlaps with exclude-pattern
                 (not (memq major-mode button-lock-exclude-modes))
                 (not (intersection (button-lock-parent-modes) button-lock-exclude-modes))
                 (not (string-match-p button-lock-buffer-name-exclude-pattern (buffer-name buf)))
                 (catch 'success
                   (dolist (filt button-lock-buffer-exclude-functions)
                     (when (funcall filt buf)
                       (throw 'success nil)))
                   t)
                 (catch 'failure
                   (dolist (filt button-lock-buffer-include-functions)
                     (unless (funcall filt buf)
                       (throw 'failure nil)))
                   t))
        buf))))

(defun button-lock-maybe-unbuttonify-buffer ()
  "This is a workaround for cperl mode, which clobbers `font-lock-unfontify-region-function'."
  (when (and (boundp 'font-lock-fontified)
             font-lock-fontified
             (not (eq font-lock-unfontify-region-function 'font-lock-default-unfontify-region)))
    (font-lock-default-unfontify-region (point-min) (point-max))))

(defun button-lock-maybe-fontify-buffer ()
  "Fontify, but only if font-lock is already on.

This is to avoid turning on font-lock if we are in the process of
disabling button-lock."
  (when (and (boundp 'font-lock-fontified)
             font-lock-fontified)
    (font-lock-fontify-buffer)))

;; button functions

;;;###autoload
(defun button-lock-button-properties (button)
  "Return list of properties for BUTTON."
  (when (listp button)
    (cadr (cadr (cadr button)))))

;;;###autoload
(defun button-lock-button-p (button)
  "Return t if BUTTON is a button-lock button."
  (ignore-errors
    (car (memq 'button-lock (button-lock-button-properties button)))))

;;;###autoload
(defun button-lock-button-pattern (button)
  "Return pattern for BUTTON."
  (when (listp button)
    (car button)))

;;;###autoload
(defun button-lock-button-grouping (button)
  "Return grouping for BUTTON."
  (when (listp button)
    (car (cadr button))))

;;;###autoload
(defun button-lock-find-extent (&optional pos property)
  "Find the extent of a button-lock property around some point.

POS defaults to the current point.  PROPERTY defaults to
'button-lock.

Returns a cons in the form (START . END), or nil if there
is no such PROPERTY around POS."
  (callf or pos (point))
  (callf or property 'button-lock)
  (when (get-text-property pos property)
    (cons (if (and (> pos (point-min)) (get-text-property (1- pos) property)) (previous-single-property-change pos property) pos)
          (next-single-property-change pos property))))

;; font-lock functions

(defun button-lock-tell-font-lock (&optional forget)
  "Tell `font-lock-keywords' about the buttons in `button-lock-button-list'.

When FORGET is set, tell `font-lock-keywords' to forget about
the buttons in `button-lock-button-list', as well as any other
keywords with the 'button-lock property."
  (if forget
      (let ((keywords (copy-tree font-lock-keywords)))
        (when (eq t (car keywords))
          ;; get uncompiled keywords
          (setq keywords (cadr keywords)))
        (dolist (kw (union keywords button-lock-button-list))
          (when (button-lock-button-p kw)
            (font-lock-remove-keywords nil (list kw)))))
  (unless button-lock-mode
    (error "Button-lock mode is not in effect"))
  (dolist (button button-lock-button-list)
    (font-lock-remove-keywords nil (list button))
    (font-lock-add-keywords nil (list button)))))

(defun button-lock-do-tell ()
  "Run `button-lock-tell-font-lock' appropriately in hooks."
  (when button-lock-mode
    (if font-lock-mode
        (button-lock-tell-font-lock)
      (button-lock-tell-font-lock 'forget))))

;; internal driver for local buttons

(defun button-lock-remove-from-button-list (button)
  "Remove BUTTON from `button-lock-button-list' and `font-lock-keywords'."
  (when button-lock-mode
    (font-lock-remove-keywords nil (list button))
    (button-lock-maybe-unbuttonify-buffer)     ; cperl-mode workaround
    (button-lock-maybe-fontify-buffer))
  (callf2 delete button button-lock-button-list)
  nil)

(defun button-lock-add-to-button-list (button &optional no-replace)
  "Add BUTTON to `button-lock-button-list' and `font-lock-keywords'.

The regexp used by the button is checked against the existing
data structure.  If the regexp duplicates that of an existing button,
the existing duplicate is replaced.

If NO-REPLACE is set, no replacement is made for a duplicate button."
  (let ((conflict (catch 'hit
                    (dolist (b button-lock-button-list)
                      (when (equal (car b) (car button))
                        (throw 'hit b))))))
    (if (and conflict no-replace)
        conflict
      (when (and conflict (not no-replace))
        (button-lock-remove-from-button-list conflict))
      (add-to-list 'button-lock-button-list button)
      (when button-lock-mode
        (font-lock-add-keywords nil (list button))
        (button-lock-maybe-fontify-buffer))
      button)))

;; internal driver for global buttons

(defun button-lock-remove-from-global-button-list (button)
  "Remove BUTTON from `button-lock-global-button-list'."
  (callf2 delete button button-lock-global-button-list))

(defun button-lock-add-to-global-button-list (button &optional no-replace)
  "Add BUTTON to `button-lock-global-button-list'.

The regexp used by the button is checked against the existing
data structure.  If the regexp duplicates that of an existing button,
the existing duplicate is replaced.

If NO-REPLACE is set, no replacement is made for a duplicate button."
  (let ((conflict (catch 'hit
                    (dolist (b button-lock-global-button-list)
                      (when (equal (car b) (car button))
                        (throw 'hit b))))))
    (unless (and conflict no-replace)
      (when (and conflict (not no-replace))
        (button-lock-remove-from-global-button-list conflict))
      (add-to-list 'button-lock-global-button-list button))))

(defun button-lock-merge-global-buttons-to-local ()
  "Add predefined, non-conflicting global buttons to the local list."
  (dolist (button button-lock-global-button-list)
    (unless (member button button-lock-button-list)
      (apply 'button-lock-set-button (append button '(:no-replace t))))))

;;; minor-mode definition

;;;###autoload
(define-minor-mode button-lock-mode
  "Toggle button-lock-mode, a minor mode for making text clickable.

Button-lock uses `font-lock-mode' to create and maintain its text
properties.  Therefore this mode can only be used where
`font-lock-mode' is active.

`button-lock-set-button' may be called to create a new button.
`button-lock-clear-all-buttons' may be called to clear all button
definitions in a buffer.

When called interactively with no prefix argument, this command
toggles the mode. When called interactively, with a prefix
argument, it enables the mode if the argument is positive and
otherwise disables it.  When called from Lisp, it enables the
mode if the argument is omitted or nil, and toggles the mode if
the argument is 'toggle."
  nil button-lock-mode-lighter nil
  (cond
    ((and button-lock-mode
          (or noninteractive                    ; never turn on button-lock where
              (eq (aref (buffer-name) 0) ?\s))) ; there can be no font-lock
     (setq button-lock-mode nil))
    (button-lock-mode
     (font-lock-mode 1)
     (make-local-variable 'font-lock-extra-managed-props)
     (button-lock-merge-global-buttons-to-local)
     (add-hook 'font-lock-mode-hook 'button-lock-do-tell nil t)
     (button-lock-tell-font-lock)
     (button-lock-maybe-fontify-buffer)
     (when (button-lock-called-interactively-p 'interactive)
       (message "button-lock mode enabled")))
    (t
     (kill-local-variable 'font-lock-extra-managed-props)
     (button-lock-tell-font-lock 'forget)
     (button-lock-maybe-unbuttonify-buffer)   ; cperl-mode workaround
     (button-lock-maybe-fontify-buffer)
     (when (button-lock-called-interactively-p 'interactive)
       (message "button-lock mode disabled")))))

;;; global minor-mode definition

(defun button-lock-maybe-turn-on (&optional arg)
  "Activate `button-lock-mode' in a buffer if appropriate.

button-lock mode will be activated in every buffer, except

   minibuffers
   buffers with names that begin with space
   buffers excluded by `button-lock-exclude-modes'
   buffers excluded by `button-lock-buffer-name-exclude-pattern'

If called with a negative ARG, deactivate button-lock mode in the
buffer."
  (callf or arg 1)
  (when (or (< arg 0)
            (button-lock-buffer-included-p (current-buffer)))
    (button-lock-mode arg)))

;;;###autoload
(define-globalized-minor-mode global-button-lock-mode button-lock-mode button-lock-maybe-turn-on
  :group 'button-lock)

;;; principal external interface

;;;###autoload
(defun* button-lock-set-button (pattern action &key

                                 (face 'button-lock-face)
                                 (mouse-face 'button-lock-mouse-face)
                                 (face-policy 'append)
                                 help-echo
                                 help-text
                                 kbd-help
                                 kbd-help-multiline

                                 (grouping 0)

                                 (mouse-binding 'mouse-1)
                                 keyboard-binding
                                 keyboard-action
                                 additional-property
                                 rear-sticky

                                 remove
                                 no-replace

                                 mouse-2
                                 mouse-3
                                 mouse-4
                                 mouse-5
                                 wheel-down
                                 wheel-up

                                 down-mouse-1
                                 down-mouse-2
                                 down-mouse-3
                                 down-mouse-4
                                 down-mouse-5

                                 double-mouse-1
                                 double-mouse-2
                                 double-mouse-3
                                 double-mouse-4
                                 double-mouse-5

                                 triple-mouse-1
                                 triple-mouse-2
                                 triple-mouse-3
                                 triple-mouse-4
                                 triple-mouse-5

                                 A-mouse-1
                                 A-mouse-2
                                 A-mouse-3
                                 A-mouse-4
                                 A-mouse-5
                                 A-wheel-down
                                 A-wheel-up

                                 C-mouse-1
                                 C-mouse-2
                                 C-mouse-3
                                 C-mouse-4
                                 C-mouse-5
                                 C-wheel-down
                                 C-wheel-up

                                 M-mouse-1
                                 M-mouse-2
                                 M-mouse-3
                                 M-mouse-4
                                 M-mouse-5
                                 M-wheel-down
                                 M-wheel-up

                                 S-mouse-1
                                 S-mouse-2
                                 S-mouse-3
                                 S-mouse-4
                                 S-mouse-5
                                 S-wheel-down
                                 S-wheel-up

                                 s-mouse-1
                                 s-mouse-2
                                 s-mouse-3
                                 s-mouse-4
                                 s-mouse-5
                                 s-wheel-down
                                 s-wheel-up)

"Attach mouse actions to text via `font-lock-mode'.

Required argument PATTERN is a regular expression to match.

Required argument ACTION is a function to call when the matching
text is clicked.  A quoted function name or a lambda expression
may be given.  The function called by ACTION must be interactive.
If ACTION is not valid the user may experience a silent failure.

If the function called by ACTION uses (interactive \"e\") it may
receive the relevant mouse event.  Note that you may wish to use
the mouse event to reposition the point.

ACTION may alternatively contain a prepared keymap, in which case
the convenience parameters :MOUSE-BINDING, :KEYBOARD-BINDING,
and :KEYBOARD-ACTION will be ignored.

Following PATTERN and ACTION is a Common Lisp-style series of
keyword/value arguments:

Setting :NO-REPLACE causes the function to have no effect when
a button already exists using the given PATTERN.  By default,
any existing button using PATTERN will be replaced.

:FACE is a font face to set on matching text, like hi-lock mode.
By default, :FACE has no properties, and :FACE-POLICY is :APPEND.
This means that other, existing text properties will take
priority, and that clickable text will not be distinguished
without a mouseover.  To change this, try adding the arguments
\":face 'link :face-policy 'prepend.\" Alternatively,
`button-lock-face' may be customized.

:MOUSE-FACE is the font face to set on mouseovers.  It defaults
to `button-lock-mouse-face'.

:FACE-POLICY sets the override policy for button faces.  Useful
values are nil, 'keep, 'prepend, and 'append (the default).  See
the documentation for OVERRIDE in `font-lock-keywords'.

:HELP-ECHO is applied to the 'help-echo text property, and may
become visible in a tooltip depending on your Emacs setup.
:HELP-TEXT is a deprecated synonym.

:KBD-HELP is applied to the 'kbd-help text property, accessible
to the user via `display-local-help',

:KBD-HELP-MULTILINE is applied to the non-standard
'kbd-help-multiline text property.

:GROUPING designates a subgroup in the pattern match to receive
the new text properties.  Subgroups, delimited by parentheses,
are numbered from 1.  The default :GROUPING is 0, indicating the
entire match.

:MOUSE-BINDING sets the mouse event which will invoke ACTION.
The default is 'mouse-1.

:KEYBOARD-BINDING sets a keyboard event which will invoke ACTION.
The format is as accepted by `kbd'.  The default is nil, meaning
no keyboard binding is in effect.  If this is set, it might also
be wise to alert the user by setting :FACE.  Note, the only
difference between :MOUSE-BINDING and :KEYBOARD-BINDING is
that :KEYBOARD-BINDING is interpreted by `kbd'.  It is possible
to pass keyboard events into :MOUSE-BINDING and vice versa.

:KEYBOARD-ACTION is an alternate event to be run by
:KEYBOARD-BINDING.  The default is nil, meaning that
:KEYBOARD-BINDING will invoke ACTION.  This is intended for cases
where ACTION is dependent on the position of the mouse.

:ADDITIONAL-PROPERTY defines an arbitrary text property which
will be set to t in for text which matches PATTERN, as optionally
modified by :GROUPING. The property 'button-lock will always be
set.

As a convenience, :MOUSE-2 through :MOUSE-5 can be used to attach
an alternate ACTION, as can :M-MOUSE-1 ..., :A-MOUSE-1 ...,
:DOUBLE-MOUSE-1 ..., :WHEEL-UP..., and :WHEEL-DOWN... The list is not
exhaustive.  For a general method of adding alternate bindings, pass
a keymap for :ACTION or use `button-lock-extend-binding'.

If :REAR-STICKY is non-nil, the rear-nonsticky text property will
not be added, as it is by default.  Changing this setting is not
recommended.

If :REMOVE is non-nil, any existing button using PATTERN will
be removed and forgotten by font-lock.

If successful, this function returns the button which was added
or removed from `font-lock-keywords'. Otherwise it returns nil.
The button value can be passed to `button-lock-extend-binding'."

  (let ((map (make-sparse-keymap))
        (properties nil)
        (fl-keyword nil))

    (if (keymapp action)
        (setq map (copy-sequence action))

      ;; else
      (define-key map `[,mouse-binding] action)

      (dolist (var '(
                     mouse-2
                     mouse-3
                     mouse-4
                     mouse-5
                     wheel-down
                     wheel-up

                     down-mouse-1
                     down-mouse-2
                     down-mouse-3
                     down-mouse-4
                     down-mouse-5

                     double-mouse-1
                     double-mouse-2
                     double-mouse-3
                     double-mouse-4
                     double-mouse-5

                     triple-mouse-1
                     triple-mouse-2
                     triple-mouse-3
                     triple-mouse-4
                     triple-mouse-5

                     A-mouse-1
                     A-mouse-2
                     A-mouse-3
                     A-mouse-4
                     A-mouse-5
                     A-wheel-down
                     A-wheel-up

                     C-mouse-1
                     C-mouse-2
                     C-mouse-3
                     C-mouse-4
                     C-mouse-5
                     C-wheel-down
                     C-wheel-up

                     M-mouse-1
                     M-mouse-2
                     M-mouse-3
                     M-mouse-4
                     M-mouse-5
                     M-wheel-down
                     M-wheel-up

                     S-mouse-1
                     S-mouse-2
                     S-mouse-3
                     S-mouse-4
                     S-mouse-5
                     S-wheel-down
                     S-wheel-up

                     s-mouse-1
                     s-mouse-2
                     s-mouse-3
                     s-mouse-4
                     s-mouse-5
                     s-wheel-down
                     s-wheel-up))

        (when (symbol-value var)
          (define-key map `[,var] (symbol-value var))))

      (when keyboard-binding
        (define-key map (read-kbd-macro keyboard-binding) (or keyboard-action action))))

    (setq properties `(face ,face keymap ,map button-lock t))
    (add-to-list 'font-lock-extra-managed-props 'keymap)
    (add-to-list 'font-lock-extra-managed-props 'button-lock)

    (when additional-property
      (callf append properties `(,additional-property t))
      (add-to-list 'font-lock-extra-managed-props additional-property))

    (when mouse-face
      (callf append properties `(mouse-face ,mouse-face))
      (add-to-list 'font-lock-extra-managed-props 'mouse-face))

    (when (or help-echo help-text)
      (callf append properties `(help-echo ,(or help-echo help-text)))
      (add-to-list 'font-lock-extra-managed-props 'help-echo))

    (when kbd-help
      (callf append properties `(kbd-help ,kbd-help))
      (add-to-list 'font-lock-extra-managed-props 'kbd-help))

    (when kbd-help-multiline
      (callf append properties `(kbd-help-multiline ,kbd-help-multiline))
      (add-to-list 'font-lock-extra-managed-props 'kbd-help-multiline))

    (unless rear-sticky
      (callf append properties `(rear-nonsticky t))
      (add-to-list 'font-lock-extra-managed-props 'rear-nonsticky))

    (setq fl-keyword `(,pattern (,grouping ',properties ,face-policy)))

    (if remove
        (button-lock-remove-from-button-list fl-keyword)
      (button-lock-add-to-button-list fl-keyword no-replace))))

;;;###autoload
(defun button-lock-unset-button (&rest button)
  "Equivalent to running `button-lock-set-button' with :REMOVE set to true.

The syntax is otherwise identical to `button-lock-set-button',
which see.

A single argument BUTTON object may also be passed, which was returned
from `button-lock-set-button'."
  (if (and (= 1 (length button))
           (button-lock-button-p (car button)))
      (button-lock-remove-from-button-list (car button))
    (apply 'button-lock-set-button (append button '(:remove t)))))

;;;###autoload
(defun button-lock-extend-binding (existing-button action mouse-binding &optional keyboard-binding)
  "Add a binding to an existing button.

The principal button creation function `button-lock-set-button'
accepts only a limited subset of mouse bindings when binding
multiple actions.  This function supports arbitrary key bindings
for binding additional actions on a button.

EXISTING-BUTTON is a button value as returned by
`button-lock-set-button'.

ACTION, MOUSE-BINDING and KEYBOARD-BINDING are as documented in
`button-lock-set-button'.  It is possible to pass a nil
MOUSE-BINDING in order to set only a KEYBOARD-BINDING.

When passing a prepared keymap for ACTION, set MOUSE-BINDING
to nil."
  (when (not (member existing-button button-lock-button-list))
    (error "No such button"))
  (let ((map (cadr (memq 'keymap (button-lock-button-properties (car (member existing-button button-lock-button-list)))))))
    (when button-lock-mode
      (font-lock-remove-keywords nil (list existing-button)))
    (if (keymapp action)
        (dolist (cell (cdr action))
          (define-key map (vector (car cell)) (cdr cell)))
      ;; else
      (when mouse-binding
        (define-key map `[,mouse-binding] action))
      (when keyboard-binding
        (define-key map (read-kbd-macro keyboard-binding) action)))
    (when button-lock-mode
      (font-lock-add-keywords nil (list existing-button)))))

;;;###autoload
(defun button-lock-clear-all-buttons ()
  "Remove and deactivate all button-lock buttons in the buffer.

If FORCE is non-nil, try to remove buttons even when the minor
mode is not active."
  (interactive)
  (let ((num (length button-lock-button-list)))
    (button-lock-tell-font-lock 'forget)
    (setq button-lock-button-list nil)
    (button-lock-maybe-unbuttonify-buffer)   ; cperl-mode workaround
    (button-lock-maybe-fontify-buffer)
    (when (and
           (button-lock-called-interactively-p 'interactive)
           (> num 0))
      (message "removed %d button patterns" num))
    num))

;;;###autoload
(defun button-lock-register-global-button (&rest button)
  "Register a global button-lock button definition.

Arguments follow the form of `button-lock-set-button'.

The BUTTON defined here will applied each time the button-lock
minor mode is activated in a buffer.

To see an effect in any given buffer, button-lock mode must be
deactivated and reactivated."
  (button-lock-add-to-global-button-list button))

;;;###autoload
(defun button-lock-unregister-global-button (&rest button)
  "Remove global button-lock BUTTON.

Arguments follow the form of `button-lock-set-button'.

To see an effect in any given buffer, button-lock mode must be
deactivated and reactivated."
  (button-lock-remove-from-global-button-list button))

;;;###autoload
(defun button-lock-unregister-all-global-buttons ()
  "Remove all global button-lock buttons definitions.

To see an effect in any given buffer, button-lock mode must be
deactivated and reactivated."
  (interactive)
  (setq button-lock-global-button-list nil)
  t)

(provide 'button-lock)

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
;; LocalWords: ButtonLockMode mouseable mybutton keymap propertize
;; LocalWords: callf cperl nonsticky setq fixmee devel uncompiled
;; LocalWords: MULTILINE multiline Koppelman Bader
;;

;;; button-lock.el ends here
