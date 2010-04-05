;;; session.el --- use variables, registers and buffer places across sessions

;; Copyright 1996-1999, 2001-2002 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Version: 2.1x
;; Keywords: session, session management, desktop, data, tools
;; X-URL: http://emacs-session.sourceforge.net/

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; When you start Emacs, package Session restores various variables (e.g.,
;; input histories) from your last session.  It also provides a menu
;; containing recently changed/visited files and restores the places (e.g.,
;; point) of such a file when you revisit it.

;; For details, check <http://emacs-session.sourceforge.net/> or, if you prefer
;; the manual style, the documentation of functions \\[session-save-session]
;; and `session-store-buffer-places'.

;; Bug fixes, bug reports, improvements, and suggestions for the newest version
;; are strongly appreciated.

;;; To-do:

;; One could imaging a combination of desktop.el and session.el.  IMHO it is
;; easier to include the remaining features of desktop.el (load some files at
;; startup) into session.el, but desktop.el is already part of Emacs...
;; Anyway, here are some ideas for the combined desktop/session:
;;
;;  * Using contexts for buffer positions (idea from bookmark and vc).
;;  * Define common code with bookmark to restore buffers from a
;;    file-representation (for files, dired, info buffers).
;;  * Saving window-configurations?

;;; Installation:

;; This file requires Emacs-20.2, XEmacs-20.2 or higher.

;; Put this file into your load-path and the following into your ~/.emacs:
;;   (require 'session)
;;   (add-hook 'after-init-hook 'session-initialize)

;; If you want to use both desktop and session, use:
;;   (setq desktop-globals-to-save '(desktop-missing-file-warning))

;; To customize, use `M-x customize-group RET session RET' or the customize
;; entry in menu Options.

;;; Code:

(provide 'session)
(require 'custom)

(eval-when-compile
  (require 'cl)
  (defvar current-menubar)
  (defvar put-buffer-names-in-file-menu)
  (defvar menu-bar-files-menu)
  (defvar yank-menu)
  (defvar minibuffer-local-ns-map))

(eval-and-compile
  (if (string-match "XEmacs" emacs-version)
      (progn
	;; the XEmacs version should have an optional NOT-HACK-HOMEDIR
	(defun session-abbreviate-file-name (filename)
	  (abbreviate-file-name filename t))
	(defalias 'session-display-completion-list 'display-completion-list))
    (defalias 'session-abbreviate-file-name 'abbreviate-file-name)
    (defun session-display-completion-list (completions &rest cl-keys)
      (display-completion-list completions)))
  (defalias 'session-subst-char-in-string
    (if (fboundp 'subst-char-in-string) 'subst-char-in-string
      'session-subst-char-in-string-0))
  (defalias 'session-minibuffer-message
    (if (fboundp 'minibuffer-message) 'minibuffer-message
      (if (fboundp 'temp-minibuffer-message) 'temp-minibuffer-message
	'ignore))))



;;;;##########################################################################
;;;;  User options, configuration variables
;;;;##########################################################################


(defconst session-version "2.1b"
  "Current version of package session.
Check <http://emacs-session.sourceforge.net/> for the newest.")


;;;===========================================================================
;;;  Customization and initialization
;;;===========================================================================

(defgroup session nil
  "Use variables, registers and buffer places across sessions."
  :group 'data
  :link '(emacs-commentary-link "session.el")
  :link '(url-link "http://emacs-session.sourceforge.net/")
  :prefix "session-")

(defgroup session-globals nil
  "Which variables and registers to save across sessions."
  :group 'session
  :prefix "session-")

(defgroup session-places nil
  "Which places are stored for which buffers."
  :group 'session
  :prefix "session-")

(defgroup session-miscellaneous nil
  "Miscellaneous configurations of package session."
  :group 'session
  :prefix "session-")

;; I could imagine that a future version of package custom could make this
;; `PACKAGE-initialize' stuff easier
(defcustom session-use-package nil
  "Pseudo variable.  Used to initialize session in custom buffer.
Put `(session-initialize)' into your ~/.emacs to initialize package
session in future sessions.  See variable `session-initialize'."
  :group 'session
  :type '(boolean :format "%{%t%}: %[(session-initialize)%], %v\n"
		  :on "in use" :off "not yet initialized"
		  :help-echo "Initialize package Session."
		  :action session-initialize))

(defcustom session-initialize t
  "Whether/what to initialize with `session-initialize'.
If t, do full initialization.  Otherwise, the value should be a list
with element.  To enable, include

 * `de-saveplace' to de-install package saveplace (is redundant),
 * `session' to load and save the session file,
 * `places' to store and use places for files/buffers,
 * `keys' to setup the default key and mouse bindings,
 * `menus' to setup the menus."
  :group 'session-miscellaneous
  :type '(choice (const :tag "All" t)
		 (set :value (de-saveplace session places keys menus)
		      (const :tag "De-install saveplace" de-saveplace)
		      (const :tag "Load/Save Session" session)
		      (const :tag "Store/Use Places" places)
		      (const :tag "Setup Key/Mouse Bindings" keys)
		      (const :tag "Setup Menus" menus))))


;;;===========================================================================
;;;  User Options and Configuration: Menu
;;;===========================================================================

(defcustom session-menu-max-size 30
  "*Max number of entries which may appear in the session menus."
  :group 'session-miscellaneous
  :type 'integer)

(defcustom session-file-menu-max-string
  (if (if (boundp 'put-buffer-names-in-file-menu)
	  put-buffer-names-in-file-menu	; XEmacs
	t)				; Emacs
      (cons 50 20)
    50)
  "*Max length of strings in submenus of the File menu.
Value has the form MAX or (MAX . NAME-THRESHOLD).  If the second form is
used and the length returned by `buffer-name' is longer than
NAME-THRESHOLD, the maximum length will be shortened accordingly.

Deprecated: a negative number -MAX stands for (MAX . 0)."
  :group 'session-miscellaneous
  :type '(choice (cons (integer :tag "Max. length" 50)
		       (integer :tag "Name threshold" 20))
		 (integer 50)))

(defcustom session-edit-menu-max-string 50
  "*Max length of strings in submenus of the Edit menu.
See also `session-compact-yank-gap-regexp'.

When running under Emacs, customize `yank-menu-length' instead."
  :group 'session-miscellaneous
  :type 'integer)

(defcustom session-compact-yank-gap-regexp "\\(\n\\|[ \t][ \t][ \t]\\)[ \t\n]*"
  "*Regexp used when trying to find a gap in a long compact string.
If non-nil, leading and trailing whitespaces are not shown, and we try
to find a gap consisting matched by this regexp if we have to split the
string according to `session-edit-menu-max-string'.

This variable has no effect when running under Emacs."
  :group 'session-miscellaneous
  :type 'string)

(defcustom session-menu-permanent-string " *"
  "*Marker for permanent files in menu \"File >> Open...recently changed\".
A file can set as permanent with prefix argument 3 for a command in
`session-kill-buffer-commands'.  It can be set as non-permanent with
prefix argument -1."
  :group 'session-miscellaneous
  :type 'string)

(defcustom session-set-file-name-exclude-regexp
  "/\\.overview\\|.session\\|News/"
  "*Regexp matching file names not to be stored in `file-name-history'.
This is used by `session-set-file-name-history'.  Value nil means, do
not exclude any file."
  :group 'session-miscellaneous
  :type '(choice (const nil) regexp))

(defvar session-menu-accelerator-support
  (and (featurep 'menu-accelerator-support)
       (fboundp 'submenu-generate-accelerator-spec))
  "*Non-nil if menu accelerators are supported.")

;; calling `abbrev-file-name' on remote files opens the connection!
(defvar session-abbrev-inhibit-function
  (cond ((fboundp 'file-remote-p) 'file-remote-p)
	;; maybe I should define my own `file-remote-p', doesn't exist in Emacs
	((fboundp 'efs-ftp-path) 'efs-ftp-path)
	((fboundp 'ange-ftp-ftp-name) 'ange-ftp-ftp-name)
	((fboundp 'ange-ftp-ftp-path) 'ange-ftp-ftp-path))
  "Function used to determine whether to abbreviate file name.
A file name is not abbreviated if this function returns non-nil when
called with the file name.")

(defvar session-directory-sep-char    ; directory-sep-char is not set
  (if (memq system-type '(ms-dos windows-nt)) ?\\ ?\/)
  "Directory separator character for session menus.")

(defvar session-save-file-coding-system
  (if (featurep 'xemacs)
      (and (featurep 'mule) 'escape-quoted)
    ;; used `emacs-mule' but this fails with X-Symbol characters...
    'iso-latin-1-with-esc)
  "Coding system to use when writing `session-save-file' if non-nil.")


;;;===========================================================================
;;;  User Options and Configuration: save global variables between sessions
;;;===========================================================================

(defcustom session-globals-max-size 50
  "*Maximal number of elements in the global variables.
Global variables are only saved if they are non-empty lists.  This value
can be shadowed by some element in `session-globals-include'.  If an
element appears more than once in the list, only the first appearance
will be stored."
  :group 'session-globals
  :type 'integer)

(defcustom session-globals-max-string 1024
  "*Maximal length of string elements in global variables."
  :group 'session-globals
  :type 'integer)

(defcustom session-registers-max-string 1024
  "*Maximal length of string elements in registers."
  :group 'session-globals
  :type 'integer)

(defcustom session-save-file (expand-file-name "~/.session")
  "File to save global variables and registers into.
It is saved with coding system `session-save-file-coding-system' at the
end of an Emacs session and loaded at the beginning.  Used for variables
which are typically changed by editing operations, e.g., history and
ring variables.  See \\[session-save-session] for details."
  :group 'session-globals
  :type 'file)

(defvar session-before-save-hook nil
  "Hook to be run before `session-save-file' is saved.
The functions are called after the global variables are written,
directly before the file is actually saved.")

(defvar session-after-load-save-file-hook
  (if (and (default-boundp 'yank-menu)
	   (fboundp 'menu-bar-update-yank-menu))
      '(session-refresh-yank-menu))
  "Hook to be run after `session-save-file' has been loaded.
The functions are called when the file has been successfully loaded.")

(defcustom session-globals-regexp "-\\(ring\\|history\\)\\'"
  "Regexp matching global variables to be saved between sessions.
Variables in `session-globals-exclude' are not saved, but variables in
`session-globals-include' are always saved."
  :group 'session-globals
  :type 'regexp)

(defcustom session-globals-exclude
  '(load-history register-alist vc-comment-ring flyspell-auto-correct-ring)
  "Global variables not to be saved between sessions.
It affects `session-globals-regexp' but not `session-globals-include'."
  :group 'session-globals
  :type '(repeat variable))

(defcustom session-globals-include '((kill-ring 10)
				     (session-file-alist 100 t)
				     (file-name-history 200))
  "Global variables to be saved between sessions.
Each element has one of the following forms:
  NAME,
  (NAME MAX-SIZE), or
  (NAME MAX-SIZE ASSOC-P).
where NAME is the symbol name of the variable, whose value must be a
non-empty list and string elements in this list must be smaller than
`session-globals-max-string'.  MAX-SIZE (default is
`session-globals-max-size') is the maximal number of elements to be
saved for this symbol where only the first of equal elements are saved,
and ASSOC-P (default is nil) non-nil means that the variable is an alist
where the equality of elements is checked on the `car'.

If MAX-SIZE or ASSOC-P is non-nil, it can be useful to include a
variable in this list even if it matches `session-globals-regexp'.
`session-globals-exclude' has no effect on these variables.

Do not use this variable to customize your Emacs.  Package custom is the
appropriate choice for this!"
  :group 'session-globals
  :type '(repeat (group :value '(nil 50)
			variable
			(integer :tag "Max size")
			(option :value t (boolean :tag "Alist")))))


;;;===========================================================================
;;;  Configuration: registers and local variables
;;;===========================================================================

(defcustom session-registers '((?0 . ?9) ?- ?= ?\\ ?` region (?a . ?z))
  "*Registers to be saved in `session-save-file'.
Valid elements in this list are:
  CHAR or (FROM . TO) or `file' or `region' or t.
CHAR is a register to save, (FROM . TO) represents a list of registers
from FROM to TO.  `file' means, only save the following registers in
this list if they contain file or file-query references.  `region'
means, only save registers if they contain a region which has less then
`session-registers-max-string' characters.  t means, allow both content
types.  Processing of this list starts with type `file'.

Before saving the session files, markers in registers are turned into
file references, see `session-register-swap-out'."
  :group 'session-globals
  :type '(repeat (choice (const :tag "File registers:" file)
			 (const :tag "String registers:" region)
			 (const :tag "Any register type:" t)
			 (character :tag "Register")
			 (cons :tag "Registers"
			       (character :tag "From")
			       (character :tag "To")))))

(defcustom session-locals-include '(overwrite-mode)
  "Local variables to be stored for specific buffers.
See also `session-locals-predicate'.

Do not add variables to this list which are more appropriate for local
variables in files, i.e., variables which are related to the contents of
the file, e.g. `major-mode'!"
  :group 'session-places
  :type '(repeat variable))

(defcustom session-locals-predicate 'local-variable-p
  "Function which must return non-nil for a local variable to be stored.
This function is called on all variables in `session-locals-include'
with the variable as the first and the current buffer as the second
argument.  Good values are nil (do not store any variable),
`local-variable-p' for local variables, `local-variable-if-set-p' for
variables which become local when set, and t (store all variables in
`session-locals-include')."
  :group 'session-places
  :type '(choice (const :tag "none" nil)
		 (const :tag "All" t)
		 (function-item local-variable-p)
		 (function-item local-variable-if-set-p)
		 (function :tag "Other function")))

(defvar session-register-swap-out (if (fboundp 'register-swap-out)
				      'register-swap-out
				    'session-register-swap-out)
  "Function processing markers in registers when a buffer is killed.
If non-nil, this function is added to `kill-buffer-hook'.")


;;;===========================================================================
;;;  User Options and Configuration: buffer check--undo, mode+name
;;;===========================================================================

(defcustom session-jump-undo-threshold 240
  "*Number of character positions the undo position must be different.
Used by `session-jump-to-last-change' with positive prefix argument."
  :group 'session-places
  :type 'integer)

;; Problem if homedir is a symlink (/bar/home -> /net/bar.home) & tmp-mounted
;;   (file-truename "~/foo") => "/tmp_mnt/net/bar.home/foo"
;;   (abbreviate-file-name "/tmp_mnt/net/bar.home/foo") => "/net/bar.home/foo"
;; I.e., there is a bug in `abbreviate-file-name' on both Emacs and XEmacs
;; (with 2nd arg t).  Workaround: use the following in your ~/.emacs:

;;(unless (string= (abbreviate-file-name (file-truename "~") t) "~") ; XEmacs
;;  (setq abbreviated-home-dir
;;	(let ((abbreviated-home-dir "$foo"))
;;	  (concat "\\`\\(?:"
;;		  (regexp-quote (abbreviate-file-name (expand-file-name "~")))
;;		  "\\|"
;;		  (regexp-quote (abbreviate-file-name (file-truename "~")))
;;		  "\\)\\(/\\|\\'\\)"))))

(defcustom session-use-truenames
  (and (string= (session-abbreviate-file-name (file-truename "~")) "~")
       (if (and (string-match "XEmacs" emacs-version)
		(boundp 'system-type)
		(eq system-type 'windows-nt))
	   'session-xemacs-buffer-local-mswindows-file-p
	 t))
  "*Whether to use the canonical file names when saving/restoring places.
If a function, it is called with no argument and returns whether to use
the canonical names of files.  If non-nil, store and check file names
returned by `file-truename'."
  :group 'session-places
  :type '(choice (const :tag "No" nil)
		 (const :tag "Yes" t)
		 (function-item :tag "If not starting with \\\\"
				session-xemacs-buffer-local-mswindows-file-p)
		 (function :tag "Other function")))

(defcustom session-auto-store t
  "*Determines whether a buffer to be killed passes the mode/name check.
This boolean is used by `session-default-buffer-check-p', see
`session-buffer-check-function'.

A buffer passes the mode/name check, if it passes the mode check, see
below, and its file name is not matched by
`session-name-disable-regexp', or if fails the mode check and its file
name is matched by `session-name-enable-regexp'.

A buffer passes the mode check, if this variable is non-nil and its
major mode is not a member of `session-mode-disable-list', or if this
variable is nil and its major mode is a member of
`session-mode-enable-list'."
  :group 'session-places
  :type 'boolean)

(defcustom session-undo-check 1
  "*Determines how a buffer to be killed passes the undo check.
Its value is MIN or (MIN . LAST) where MIN is a number.  Used by
`session-default-buffer-check-p', see `session-buffer-check-function'.

To pass the undo check
 * the length of `buffer-undo-list', assumed to be -1 if no undo
   information is recorded, must be higher or equal to MIN,
 * the first form is used or LAST is nil: no further requirement
 * LAST is `and': additionally, `session-last-change' must be non-nil,
   i.e., the buffer has been changed previously,
 * LAST is `or': alternatively, `session-last-change' is non-nil."
  :group 'session-places
  :type '(choice (integer :tag "Min no of Changes")
		 (cons (integer :tag "Min no of Changes")
		       (choice :tag "Previous and New Changes"
			       (const :tag "Only consider New Changes" nil)
			       (const :tag "AND previously changed" and)
			       (const :tag "OR previously changed" or)))))

(defcustom session-kill-buffer-commands '(kill-this-buffer)
  "*Commands which kill a buffer.
If a prefix argument was provided to any of these commands, it will
influence the decision whether to store places for the buffer, see
`session-store-buffer-places'.  Using commands which use the minibuffer
for input, is useless."
  :group 'session-places
  :type '(repeat (function :tag "Command")))

(defcustom session-buffer-check-function 'session-default-buffer-check-p
  "Function which return non-nil if buffer places should be stored.
Used by `session-store-buffer-places'.  This function is called with the
buffer to check as argument.  You can also assume that the current
buffer is the buffer to check.

The default value `session-default-buffer-check-p' returns non-nil, if
the buffer
 * visits an existing readable file,
 * passes the mode/name check, see `session-auto-store', and
 * passes the undo check, see `session-undo-check', its default value 1
   means: the buffer must have been changed during the session."
  :group 'session-globals
  :type '(choice (function-item :tag "Default check"
				session-default-buffer-check-p)
		 (function :tag "Other function")))

(defcustom session-mode-disable-list
  '(vm-mode gnus-score-mode message-mode tar-mode)
  "*Major modes of buffers for which no places are stored.
See `session-buffer-check-function'."
  :group 'session-globals
  :type '(repeat (function :tag "Major mode")))

(defcustom session-mode-enable-list nil
  "*Major modes of buffers for which places are stored.
See `session-buffer-check-function'."
  :group 'session-globals
  :type '(repeat (function :tag "Major mode")))

(defcustom session-name-disable-regexp
  (concat "\\`" (regexp-quote
		 (if (fboundp 'temp-directory) (temp-directory) "/tmp")))
  "*File names of buffers for which no places are stored.
See `session-buffer-check-function'."
  :group 'session-places
  :type '(choice (const nil) regexp))

(defcustom session-name-enable-regexp nil
  "*File names of buffers for which places are stored.
See `session-buffer-check-function'."
  :group 'session-places
  :type '(choice (const nil) regexp))




;;;;##########################################################################
;;;;  Store buffer places and local variables, change register contents
;;;;##########################################################################


(defvar session-last-change nil
  "Position of last change in current buffer.
This variable is set by `session-find-file-hook' if the buffer was
changed in a previous session.  It can also be set by providing an
prefix argument to `session-jump-to-last-change'.")
(make-variable-buffer-local 'session-last-change)

(defvar session-file-alist nil
  "Alist for places and local variables for some files.
It has the form
  (NAME POINT MARK POINT-MIN POINT-MAX PERMANENT LAST-CHANGE
   (SYMBOL . VAR) ...)

NAME is the file name, POINT is the point position, MARK is the mark
position, POINT-MIN and POINT-MAX determine the narrow part if non-nil,
PERMANENT is the permanent marker (see `session-buffer-check-function'),
LAST-CHANGE is the position of the last change in the previous session
or was explicitly set with prefix argument 0 for command
\\[session-jump-to-last-change].  Optional pairs (SYMBOL . VAR) are
local variables with their values.")


;;;===========================================================================
;;;  Position of last change
;;;===========================================================================

(defun session-undo-position (pos undo-list)
  "Return position of first real element in UNDO-LIST.
POS should be nil."
  (while (and (null pos) undo-list)
    (setq pos (pop undo-list))
    (if (consp pos)
	(setq pos (if (stringp (car pos)) (cdr pos) (car pos))))
    (setq pos (and (integerp pos) (abs pos))))
  (cons pos undo-list))

(defun session-jump-to-last-change (&optional arg)
  "Jump to position of abs(ARG)'th last change.
With positive argument, two changes are considered different if their
positions differ by at least `session-jump-undo-threshold' character
positions.  With negative argument, two changes are considered different
if there is an undo boundary in the `buffer-undo-list' between them.

In both cases, use position in `session-last-change' as oldest position.
With prefix argument ARG=0, set `point' as oldest position."
  (interactive "p")
  (if (zerop arg)
      (progn
	(setq session-last-change (point))
	(message "Store %d as special last-change position (%s %d %s)"
		 session-last-change
		 (substitute-command-keys "\\[universal-argument]")
		 (let ((list (and (consp buffer-undo-list) buffer-undo-list)))
		   (while list
		     (or (car list) (setq arg (1- arg)))
		     (setq list (cdr list)))
		   (1- arg))
		 (substitute-command-keys "\\[session-jump-to-last-change]")))
    (let* ((undo-list (session-undo-position nil (and (consp buffer-undo-list)
						      buffer-undo-list)))
	   (pos (car undo-list)))
      (if (< arg 0)
	  (unless (zerop (setq arg (1+ arg)))
	    (setq undo-list (cdr undo-list))
	    (while (and (< arg 0) undo-list)
	      (or (pop undo-list)
		  (setq arg (1+ arg))))
	    (setq pos (car (session-undo-position nil undo-list))))
	(setq arg (1- arg))
	(while (and (> arg 0)
		    (car (setq undo-list
			       (session-undo-position nil (cdr undo-list)))))
	  (if (>= (abs (- (car undo-list) pos)) session-jump-undo-threshold)
	      (setq pos (car undo-list)
		    arg (1- arg))))
	(or (zerop arg) (setq pos nil)))
      (or pos (setq pos session-last-change))
      (if pos
	  (goto-char pos)
	(message "Do not know position of last change")))))


;;;===========================================================================
;;;  Yank menu (Emacs: refresh existing menu, XEmacs: do our own)
;;;===========================================================================

;; this function should be defined in menu-bar.el...
(defun session-refresh-yank-menu ()
  "Refresh `yank-menu' according to `kill-ring'."
  (when (and (default-boundp 'yank-menu)
	     (fboundp 'menu-bar-update-yank-menu))
    (let ((killed (reverse (default-value 'kill-ring))))
      (while killed
	(menu-bar-update-yank-menu (pop killed) nil)))))

(defun session-yank (arg)
  "Reinsert the last stretch of killed text, like \\[yank].
Calls `yank' with argument ARG and with `interprogram-paste-function'
bound to nil."
  (interactive "*p")
  (let ((interprogram-paste-function nil)) ;#dynamic
    (yank arg)))

(defun session-no-selection-hook ()
  "XEmacs menubar bug workaround in `menu-no-selection-hook'."
  (if (eq this-command 'run-hooks)	; without breaks menubar
      (setq this-command last-command)))

(defun session-popup-yank-menu (event)
  ;; checkdoc-params: (event)
  "Pop up a menu for inserting items in `kill-ring'."
  (interactive "e")
  (when kill-ring
    (setq this-command last-command)
    (popup-menu '("Select and Paste"
		  :filter session-yank-menu-filter))))

(defun session-yank-menu-filter (menu-items)
  ;; checkdoc-params: (menu-items)
  "Return a menu for inserting items in `kill-ring'."
  (let ((menu nil)
	(ring nil)
	(max session-menu-max-size)
	(len (length kill-ring))
	(half-str-len (/ (- session-edit-menu-max-string 4) 2))
	(i 0)
	(active (not buffer-read-only))
	elem
	(interprogram-paste-function nil)) ;#dynamic
    ;; Traversing (append kill-ring-yank-pointer kill-ring) instead indexing
    ;; (current-kill INDEX) would be probably more efficient, but would be a
    ;; very low-level hack
    (while (and (< i len) (> max 0))
      (setq elem (current-kill i t)
	    i (1+ i))
      (unless (or (assoc elem ring) (string-match "\\`[ \t\n]*\\'" elem))
	(push (cons elem i) ring)
	(setq max (1- max))))
    (while ring
      (setq elem (car ring)
	    ring (cdr ring))
      (push (session-yank-string (car elem) half-str-len
				 (list 'session-yank (cdr elem))
				 active)
	    menu))
    (session-menu-maybe-accelerator menu-items menu)))

(defun session-yank-string (string half-len-str callback active)
  "Return menu item STRING with callback CALLBACK.
If ACTIVE is non-nil, the item is active.  HALF-LEN-STR is the length of
the two parts of a abbreviated menu item name."
  (let ((beg (or (and session-compact-yank-gap-regexp
		      (string-match "\\`[ \t\n]+" string)
		      (match-end 0))
		 0))
	(end (or (and session-compact-yank-gap-regexp
		      (string-match "[ \t\n]+\\'" string))
		 (length string))))
    (vector (if (> (- end beg) session-edit-menu-max-string)
		(let ((gap (and session-compact-yank-gap-regexp
				(string-match session-compact-yank-gap-regexp

				 string (- end half-len-str))
				(match-end 0))))
		  (if (and gap (< gap (- end 3)))
		      (setq half-len-str (- (+ half-len-str half-len-str gap)
					    end))
		    (setq gap (- end half-len-str)))
		  (concat (session-subst-char-in-string
			   ?\t ?\ (substring string beg (+ beg half-len-str)) t)
			  " ... "
			  (session-subst-char-in-string
			   ?\t ?\ (substring string gap end) t)))
	      (session-subst-char-in-string ?\t ?\
					    (substring string beg end) t))
	    callback
	    active)))

;; from EMACS-20.4/lisp/subr.el:
(defun session-subst-char-in-string-0 (fromchar tochar string
						&optional inplace)
  "Replace FROMCHAR with TOCHAR in STRING each time it occurs.
Unless optional argument INPLACE is non-nil, return a new string."
  (let ((i (length string))
	(newstr (if inplace string (copy-sequence string))))
    (while (> i 0)
      (setq i (1- i))
      (if (eq (aref newstr i) fromchar)
	  (aset newstr i tochar)))
    newstr))


;;;===========================================================================
;;;  Menu filters (XEmacs only)
;;;===========================================================================

(defun session-file-opened-menu-filter (menu-items)
  ;; checkdoc-params: (menu-items)
  "This is the menu filter for \"File >> Open...recently visited\".
See `session-file-changed-menu-filter'."
  (session-file-changed-menu-filter menu-items file-name-history))

(defun session-file-changed-menu-filter (menu-items &optional files find-fn)
  ;; checkdoc-params: (menu-items)
  "This is the menu filter for \"File >> Open...recently changed\".
It dynamically creates a list of files to use as the contents of the
menu.  The files are taken from FILES or `session-file-alist'.  It
doesn't show the same name twice and shows `session-menu-max-size' names
at most.  FIND-FN or \\[find-file] is the function to use when selecting
a file in the menu."
  (let ((excl nil)
	(menu nil)
	(i session-menu-max-size)
	(max-string (max (cond ((natnump session-file-menu-max-string)
				session-file-menu-max-string)
			       ((integerp session-file-menu-max-string)
				(- 0 session-file-menu-max-string
				   (length (buffer-name))))
			       ((consp session-file-menu-max-string)
				(- (car session-file-menu-max-string)
				   (max (- (length (buffer-name))
					   (cdr session-file-menu-max-string))
					0)))
			       (t 50))
			 16))
	elem desc name)
    (or files (setq files session-file-alist))
    (or find-fn (setq find-fn 'find-file))
    (while (and files (> i 0))
      (setq elem (car files)
	    desc (and (consp elem) elem)
	    files (cdr files))
      (if (consp elem) (setq elem (car elem)))
      (setq elem (session-abbrev-file-name (directory-file-name elem)))
      (or (member elem excl)
	  (progn
	    (setq i (1- i))
	    (push elem excl)
	    (setq name elem)
	    (and (> (length elem) max-string)
		 (fboundp 'split-path)
		 (let* ((path-separator (char-to-string
					 session-directory-sep-char))
			(components (split-path elem)))
		   (or (cdr components)
		       (eq session-directory-sep-char ?\/) ; the right one
		       (setq path-separator "/"
			     components (split-path elem)))
		   (let* ((prefix (if (< (length (car components)) 2)
				      (concat (pop components) path-separator
					      (pop components))
				    (pop components)))
			  (len (+ (length prefix) 5))
			  postfix)
		     (setq components (nreverse components))
		     (while (and (cdr components)
				 (< (incf len (length (car components)))
				    max-string))
		       (push (pop components) postfix))
		     (if (or postfix (cdr components))
			 (setq name
			       (concat prefix path-separator
				       " ... " path-separator
				       (if postfix
					   (mapconcat 'identity postfix
						      path-separator)
					 (car components))))))))
	    (push (vector name (list find-fn elem)
			  :keys (and (sixth desc)
				     session-menu-permanent-string))
		  menu))))
    (session-menu-maybe-accelerator menu-items (nreverse menu))))

(defun session-menu-maybe-accelerator (menu-items menu)
  "Return menu consisting of items in MENU-ITEMS and MENU.
MENU-ITEMS have the usual format of elements in a menu, except that the
name always starts with a accelerator specification \"%_. \".  Also, a
:keys specification will be evaluated if :keys is the first keyword.

The items in MENU will be modified to add accelerator specifications if
`session-menu-accelerator-support' is non-nil."
  (nconc (mapcar 'session-change-menu-item menu-items)
	 (if session-menu-accelerator-support
	     (submenu-generate-accelerator-spec menu)
	   menu)))

(defun session-change-menu-item (item)
  "Change ITEM according to `session-menu-maybe-accelerator'."
  (if (vectorp item)
      (let ((keys (and (eq (aref item 2) :keys)
		       (not (stringp (aref item 3))))))
	(if (if session-menu-accelerator-support keys t)
	    (prog1 (setq item (copy-sequence item))
	      (if keys
		  (aset item 3 (eval (aref item 3))))
	      (or session-menu-accelerator-support
		  (aset item 0 (substring (aref item 0) 4))))
	  item))
    item))

(defun session-abbrev-file-name (name)
  "Return a version of NAME shortened using `directory-abbrev-alist'.
This function does not consider remote file names (see
`session-abbrev-inhibit-function') and substitutes \"~\" for the user's
home directory."
  (if (and session-abbrev-inhibit-function
	   (or (not (fboundp session-abbrev-inhibit-function))
	       (funcall session-abbrev-inhibit-function name)))
      name
    (session-abbreviate-file-name name)))


;;;===========================================================================
;;;  Functions in hooks
;;;===========================================================================

(defun session-set-file-name-history ()
  "Add file-name of current buffer to `file-name-history'.
Don't add the file name if it does not visit an existing readable file,
if it matches `session-set-file-name-exclude-regexp', or if it is
already at the front of `file-name-history'.  This function is useful in
`find-file-hooks'."
  (and buffer-file-name
       (file-exists-p buffer-file-name) (file-readable-p buffer-file-name)
       (let ((name (session-abbrev-file-name buffer-file-name)))
	 (or (string= (car file-name-history) name)
	     (string= (car file-name-history) buffer-file-name)
	     (and session-set-file-name-exclude-regexp
		  (string-match session-set-file-name-exclude-regexp name))
	     (push name file-name-history)))))

(defun session-find-file-hook ()
  "Function in `find-file-hooks'.  See `session-file-alist'."
  (let* ((ass (assoc (session-buffer-file-name) session-file-alist))
	 (point (second ass))
	 (mark (third ass))
	 (min (fourth ass))
	 (max (fifth ass))
	 (alist (nthcdr 7 ass)))
    (condition-case nil
	(while alist
	  (if (local-variable-if-set-p (caar alist) (current-buffer))
	      (set (caar alist) (cdar alist)))
	  (setq alist (cdr alist)))
      (error nil))
    (setq session-last-change (seventh ass))
    (and mark
	 (<= (point-min) mark) (<= mark (point-max))
	 ;; I had `set-mark' but this function activates mark in Emacs, but not
	 ;; in XEmacs.  `push-mark' is also OK and doesn't activate in both
	 ;; Emacsen which is better if we use `pending-delete-mode'.
	 (push-mark mark))
    (and min max
	 (<= (point-min) min) (<= max (point-max))
	 (narrow-to-region min max))
    (and point
	 (<= (point-min) point) (<= point (point-max))
	 (goto-char point))))

(defun session-kill-buffer-hook ()
  "Function in `kill-buffer-hook'.
See `session-file-alist' and `session-registers'."
  (if buffer-file-name
      (condition-case nil
	  (session-store-buffer-places
	   (if (memq this-command session-kill-buffer-commands)
	       (prefix-numeric-value current-prefix-arg)
	     1))
	(error nil))))


;;;===========================================================================
;;;  Change register contents from marker to file
;;;===========================================================================

(defun session-register-swap-out ()
  "Turn markers in registers into file references when a buffer is killed."
  (and buffer-file-name
       (let ((tail register-alist))
	 (while tail
	   (and (markerp (cdr (car tail)))
		(eq (marker-buffer (cdr (car tail))) (current-buffer))
		(setcdr (car tail)
			(cons 'file buffer-file-name)))
	   (setq tail (cdr tail))))))

(if session-register-swap-out
    (add-hook 'kill-buffer-hook session-register-swap-out))



;;;;##########################################################################
;;;;  Save global variables, add functions to hooks
;;;;##########################################################################


(defvar session-successful-p nil
  "Whether the file `session-save-file' has been loaded successfully.")


;;;===========================================================================
;;;  The buffer file name
;;;===========================================================================

(defun session-xemacs-buffer-local-mswindows-file-p ()
  "Return t if the current buffer visits a local file on MS-Windows.
Also returns t if the current buffer does not visit a file.  Return nil
of the current buffer visits a file starting with \"\\\\\".  Workaround
for XEmacs bug in `file-truename' for file names starting with
\"\\\\\"."
  (or (< (length buffer-file-name) 2)
      (not (string= (substring buffer-file-name 0 2) "\\\\"))))

(defun session-buffer-file-name ()
  "Return the buffer file name according to `session-use-truenames'."
  (if (if (functionp session-use-truenames)
	  (funcall session-use-truenames)
	session-use-truenames)
      buffer-file-truename
    buffer-file-name))


;;;===========================================================================
;;;  Store places and local variables for buffer to be killed
;;;===========================================================================

(defun session-toggle-permanent-flag (arg &optional check)
  "Toggle the permanent flag of the current buffer.
With ARG, set permanent flag if and only if ARG is positive.  If the
permanent flag is set, the places are stored as well.  If CHECK is
non-nil, just return the status of the permanent flag: either nil if it
is unset or `session-menu-permanent-string' if it is set."
  (interactive "P")
  (if buffer-file-name
      (let ((permanent (if arg
			   (> (prefix-numeric-value arg) 0)
			 (not (nth 5 (assoc (session-buffer-file-name)
					    session-file-alist))))))
	(if check
	    (if permanent nil session-menu-permanent-string)
	  (session-store-buffer-places (if permanent 3 -1))
	  (message (if permanent
		       "Permanent flag is set and places are stored"
		     "Permanent flag has been unset"))))
    (if check nil (error "Buffer is not visiting a file"))))

(defun session-store-buffer-places (arg)
  "Store places and local variables in current buffer.
An entry for the current buffer and its places is added to the front of
`session-file-alist' if the buffer is visiting a file and if it is
mentioned in the list below.  ARG is the prefix argument to a command in
`session-kill-buffer-commands' or 1 for any other command.

ARG=-1: delete PERMANENT flag for buffer,
ARG=0: do nothing,
ARG=1: store buffer places, if the PERMANENT flag is set or the buffer
  passes the function in `session-buffer-check-function',
ARG=2: always store buffer places,
ARG=3: set PERMANENT flag and store buffer places.

See also `session-last-change' and `session-locals-include'.

Note that not storing buffer places does not mean deleting an old entry
for the same file.  It means that there is the danger of the entry
becoming too old to be saved across session.  By default, only the first
100 entries of `session-file-alist' are saved, see
`session-globals-include'."
  (let ((file-name (session-buffer-file-name)))
    (when file-name
      (let ((permanent (nthcdr 5 (assoc file-name session-file-alist))))
	(and (< arg 0) (car permanent)
	     (setcar permanent nil))	; reset permanent in existing entry
	(setq permanent (or (car permanent) (> arg 2)))
	(if (or (and permanent (> arg 0))
		(> arg 1)
		(and (= arg 1)
		     (funcall session-buffer-check-function (current-buffer))))
	    (let ((locals session-locals-include)
		  (store nil))
	      (while locals
		(if (if (functionp session-locals-include)
			(funcall session-locals-predicate
				 (car locals) (current-buffer))
		      session-locals-predicate)
		    (push (cons (car locals)
				(symbol-value (car locals)))
			  store))
		(setq locals (cdr locals)))
	      (setq store
		    (nconc (list file-name
				 (point) (mark t)
				 (point-min)
				 (and (<= (point-max) (buffer-size))
				      (point-max))
				 permanent
				 (or (car (session-undo-position
					   nil (and (consp buffer-undo-list)
						    buffer-undo-list)))
				     session-last-change))
			   store))
	      (if (equal (caar session-file-alist) file-name)
		  (setcar session-file-alist store)
		(push store session-file-alist))))))))

(defun session-find-file-not-found-hook ()
  "Query the user to delete the permanent flag for a non-existent file.
Always return nil."
  (let ((file-name (session-buffer-file-name)))
    (when file-name
      (let ((permanent (nthcdr 5 (assoc file-name session-file-alist))))
	(and (car permanent)
	     (y-or-n-p "Delete permanent flag for non-existent file? ")
	     (setcar permanent nil))))))


;;;===========================================================================
;;;  Default standard check for buffers to be killed
;;;===========================================================================

(defun session-default-buffer-check-p (buffer)
  "Default function for `session-buffer-check-function'.
Argument BUFFER should be the current buffer."
  (and
   ;; undo check -------------------------------------------------------------
   (or (and (eq (cdr-safe session-undo-check) 'or)
	    session-last-change)
       (and (or (not (eq (cdr-safe session-undo-check) 'and))
		session-last-change)
	    (>= (if (listp buffer-undo-list) (length buffer-undo-list) -1)
		(if (consp session-undo-check)
		    (car session-undo-check)
		  session-undo-check))))
   ;; mode and name check ----------------------------------------------------
   (let ((file (buffer-file-name buffer)))
     (and (file-exists-p file) (file-readable-p file)
	  (if (if session-auto-store
		  (not (memq major-mode session-mode-disable-list))
		(memq major-mode session-mode-enable-list))
	      (not (and session-name-disable-regexp
			(string-match session-name-disable-regexp file)))
	    (and session-name-enable-regexp
		 (string-match session-name-enable-regexp file)))))))


;;;===========================================================================
;;;  Save session file
;;;===========================================================================

(defun session-save-session ()
  "Save session: file places, *-ring, *-history, registers.
Save some global variables and registers into file `session-save-file'
with coding system `session-save-file-coding-system'.  Run functions in
`session-before-save-hook' before writing the file.

See also `session-globals-regexp', `session-globals-include' and
`session-registers'.

This command is executed when using \\[save-buffers-kill-emacs] without
prefix argument 0.  See `kill-emacs-hook'."
  (interactive)
  (and session-save-file
       (not (and (eq this-command 'save-buffers-kill-emacs)
		 (equal current-prefix-arg 0)))
       (or session-successful-p
	   (not (file-exists-p session-save-file))
	   (y-or-n-p "Overwrite old session file (not loaded)? "))
       (save-excursion
	 ;; `kill-emacs' doesn't kill the buffers ----------------------------
	 (let ((buffers (nreverse (buffer-list))))
	   (while buffers
	     (set-buffer (car buffers))
	     (when buffer-file-name
	       (session-store-buffer-places 1)
	       (if session-register-swap-out
		   (funcall session-register-swap-out)))
	     (setq buffers (cdr buffers))))
	 ;; create header of session file ------------------------------------
	 (set-buffer (get-buffer-create " session "))
	 (erase-buffer)
	 (let ((s-excl session-globals-exclude)
	       (slist (append session-globals-include
			      (apropos-internal session-globals-regexp
						'boundp)))
	       ;;(print-readably t) ; no way!
	       symbol val vlist len ass-p
	       coding-system-for-write)
	   (if session-save-file-coding-system
	       (condition-case nil
		   (progn
		     (setq coding-system-for-write
			   (check-coding-system
			    session-save-file-coding-system))
		     (insert (format ";;; -*- coding: %S; -*-\n"
				     session-save-file-coding-system)))
		 (error nil)))
	   (insert ";;; Automatically generated on "
		   (current-time-string)
		   "\n;;; Invoked by "
		   (user-login-name)
		   "@"
		   (system-name)
		   " using "
		   emacs-version
		   "\n")
	   ;; save global variables ------------------------------------------
	   (while slist
	     (setq symbol (car slist)
		   slist  (cdr slist)
		   len session-globals-max-size
		   ass-p nil)
	     (if (consp symbol)
		 (setq ass-p (third symbol)
		       len (or (second symbol) session-globals-max-size)
		       symbol  (first symbol)))
	     (and (default-boundp symbol)
		  (setq val (default-value symbol))
		  (consp val)
		  (not (memq symbol s-excl))
		  (condition-case nil
		      (progn
			(push symbol s-excl)
			;; only takes first of same elements, cut length
			(setq vlist nil)
			(while val
			  (or (and (stringp (car val))
				   (> (length (car val))
				      session-globals-max-string))
			      (if ass-p
				  (assoc (caar val) vlist)
				(member (car val) vlist))
			      (progn
				(push (car val) vlist)
				(>= (setq len (1- len)) 0))
			      (setq val nil))
			  (setq val (cdr val)))
			;; print (the tricky part (read/load isn't clever)):
			;; check each elem
			(while vlist
			  (condition-case nil
			      (push (read (prin1-to-string (car vlist))) val)
			    (error nil))
			  (setq vlist (cdr vlist)))
			(insert (format "(setq-default %S '%S)\n" symbol val)))
		    (error nil))))
	   (session-save-registers)
	   (run-hooks 'session-before-save-hook)
	   (condition-case var
	       (progn
		 (if (file-exists-p session-save-file)
		     (delete-file session-save-file))
		 (make-directory (file-name-directory session-save-file) t)
		 (write-region (point-min) (point-max) session-save-file))
	     (error			; efs would signal `ftp-error'
	      (or (y-or-n-p "Could not write session file.  Exit anyway? ")
		  (while t		; XEmacs: `signal-error'
		    (signal (car var) (cdr var))))))
	   (kill-buffer (current-buffer))))))

(defun session-save-registers ()
  "Save registers in `session-registers'."
  (let ((chars session-registers)
	(type 'file)
	register from to)
    (while chars
      (if (symbolp (car chars))
	  (setq type  (car chars)
		chars (cdr chars))
	(setq from (car chars)
	      chars (cdr chars))
	(if (consp from)
	    (setq to   (cdr from)
		  from (car from))
	  (setq to from))
	(while (<= from to)
	  (and (fboundp 'int-to-char) (numberp from)
	       (setq from (int-to-char from)))
	  (setq register (get-register from))
	  (cond ((null register))
		((and (memq type '(file t))
		      (consp register)
		      (memq (car register) '(file file-query)))
		 (insert (if (eq (car register) 'file)
			     (format "(set-register %S '(file . %S))\n"
				     from (cdr register))
			   (format "(set-register %S '(file-query %S %d))\n"
				   from (cadr register) (caddr register)))))
		((and (memq type '(region t))
		      (stringp register)
		      (< (length register) session-registers-max-string))
		 (insert (format "(set-register %S %S)\n" from register))))
	  (setq from (1+ from)))))))


;;;===========================================================================
;;;  Minibuffer history completion, see XEmacs' list-mode
;;;===========================================================================


(defvar session-history-help-string
  '(concat (if (device-on-window-system-p)
	       (substitute-command-keys "Click \\<list-mode-map>\\[list-mode-item-mouse-selected] on a history element to select it.\n") "")
	   (substitute-command-keys "In this buffer, type RET to select the element near point.\n\n"))
  "Form the evaluate to get a help string for history elements.")

(defun session-minibuffer-history-help ()
  "List history of current minibuffer type.
In Emacs, the *History* buffer talks about \"completions\" instead
\"history elements\".  In XEmacs before 21.4.7, selecting an entry might
not work if the minibuffer is non-empty."
  (interactive)
  (let ((history (symbol-value minibuffer-history-variable)))
    (message nil)
    (if history
	(with-output-to-temp-buffer "*History*"
	  (session-display-completion-list
	   (sort history #'string-lessp)
	   :help-string session-history-help-string
	   :completion-string
	   "Elements in the history are:")
	  (save-excursion
	    (set-buffer standard-output)
	    (setq completion-base-size 0)))
      (ding)
      (session-minibuffer-message " [Empty history]"))))


;;;===========================================================================
;;;  Set hooks, load session file
;;;===========================================================================

;; easymenu.el is for top-level menus only...
(defun session-add-submenu (menu)
  "Add the menu MENU to the beginning of the File menu in the menubar.
If the \"File\" menu does not exist, no submenu is added.  See
`easy-menu-define' for the format of MENU."
  (when menu
    (if (string-match "XEmacs" emacs-version)
	(and (featurep 'menubar)
	     (find-menu-item default-menubar '("File"))
	     (let ((current-menubar default-menubar)) ;#dynamic
	       ;; XEmacs-20.4 `add-submenu' does not have 4th arg IN-MENU
	       (add-submenu '("File") menu "Open...")))
      (and (>= emacs-major-version 21)
	   (boundp 'menu-bar-files-menu)
	   (let ((keymap (easy-menu-create-menu (car menu) (cdr menu))))
	     ;; `easy-menu-get-map' doesn't get the right one => use hard-coded
	     (define-key menu-bar-files-menu (vector (intern (car menu)))
	       (cons 'menu-item
		     (cons (car menu)
			   (if (not (symbolp keymap))
			       (list keymap)
			     (cons (symbol-function keymap)
				   (get keymap 'menu-prop)))))))))))

;;;###autoload
(defun session-initialize (&rest dummies)
  ;; checkdoc-params: (dummies)
  "Initialize package session and read previous session file.
Setup hooks and load `session-save-file', see `session-initialize'.  At
best, this function is called at the end of the Emacs startup, i.e., add
this function to `after-init-hook'."
  (interactive)
  (setq session-use-package t)
  (when (or (eq session-initialize t)
	    (memq 'de-saveplace session-initialize))
    ;; Features of package saveplace, which has an auto-init, are covered by
    ;; this package.
    (when (functionp 'eval-after-load)
      (eval-after-load "saveplace"
	'(progn
	   (remove-hook 'find-file-hooks 'save-place-find-file-hook)
	   (remove-hook 'kill-emacs-hook 'save-place-kill-emacs-hook)
	   (remove-hook 'kill-buffer-hook 'save-place-to-alist)))))
  (when (or (eq session-initialize t)
	    (memq 'places session-initialize))
    ;; `session-find-file-hook' should be *very* late in `find-file-hooks',
    ;; esp. if some package, e.g. crypt or iso-cvt, change the buffer contents:
    (add-hook 'find-file-hooks 'session-find-file-hook t)
    (add-hook 'find-file-not-found-hooks 'session-find-file-not-found-hook t)
    (add-hook 'kill-buffer-hook 'session-kill-buffer-hook))
  (when (or (eq session-initialize t)
	    (memq 'keys session-initialize))
    (condition-case nil
	(progn
	  (define-key ctl-x-map [(undo)] 'session-jump-to-last-change)
	  (define-key ctl-x-map [(control ?\/)] 'session-jump-to-last-change)
	  (define-key minibuffer-local-map [(meta ?\?)]
	    'session-minibuffer-history-help)
	  (if (string-match "XEmacs" emacs-version)
	      ;; C-down-mouse-3 pops up mode menu under Emacs
	      (define-key global-map [(control button3)]
		'session-popup-yank-menu)
	    ;; Emacs doesn't seem to have keymap inheritance...
	    (define-key minibuffer-local-completion-map [(meta ?\?)]
	      'session-minibuffer-history-help)
	    (define-key minibuffer-local-must-match-map [(meta ?\?)]
	      'session-minibuffer-history-help)
	    (define-key minibuffer-local-ns-map [(meta ?\?)]
	      'session-minibuffer-history-help)))
      (error nil)))
  (when (or (eq session-initialize t)
	    (memq 'menus session-initialize))
    (add-hook 'find-file-hooks 'session-set-file-name-history)
    (session-add-submenu '("Open...recently changed"
			   :included session-file-alist
			   :filter session-file-changed-menu-filter
			   ["%_* Toggle Permanent Flag of Current Buffer"
			    session-toggle-permanent-flag
			    ;; :keys must be at third position!
			    :keys (session-toggle-permanent-flag nil t)
			    :active buffer-file-name]
			   "---"))
    (session-add-submenu '("Open...recently visited"
			   :included file-name-history
			   :filter session-file-opened-menu-filter))
    (and (string-match "XEmacs" emacs-version)	; Emacs uses own one
	 (featurep 'menubar)
	 (find-menu-item default-menubar '("Edit"))
	 (let ((current-menubar default-menubar))
	   ;; XEmacs-20.4 `add-submenu' does not have 4th arg IN-MENU
	   (add-submenu '("Edit")
			'("Select and Paste"
			  :included kill-ring
			  :filter session-yank-menu-filter)
			(cond ((find-menu-item default-menubar
					       '("Edit" "Delete"))
			       "Delete") ; why just BEFORE, not AFTER...
			      ((find-menu-item default-menubar
					       '("Edit" "Paste"))
			       "Paste")
			      ((find-menu-item default-menubar
					       '("Edit" "Undo"))
			       "Undo"))))))
  (when (or (eq session-initialize t)
	    (memq 'session session-initialize))
    (add-hook 'kill-emacs-hook 'session-save-session)
    (or session-successful-p
	(setq session-successful-p
	      (and session-save-file
		   (condition-case nil
		       (progn
			 ;; load might fail with coding-system = emacs-mule
			 (load session-save-file t nil t)
			 (run-hooks 'session-after-load-save-file-hook)
			 t)
		     (error nil)))))))

;;; Local IspellPersDict: .ispell_session
;;; session.el ends here
