;;; cus-edit+.el --- Enhancements to `cus-edit.el'.
;;
;; Filename: cus-edit+.el
;; Description: Enhancements to cus-edit.el.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2000-2011, Drew Adams, all rights reserved.
;; Created: Thu Jun 29 13:19:36 2000
;; Version: 21.1
;; Last-Updated: Thu Mar 31 07:57:07 2011 (-0700)
;;           By: dradams
;;     Update #: 1274
;; URL: http://www.emacswiki.org/cgi-bin/wiki/cus-edit+.el
;; Keywords: help, customize, help, faces
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;;
;; Features that might be required by this library:
;;
;;   `assoc', `autofit-frame', `cus-edit', `cus-face', `cus-load',
;;   `cus-start', `custom', `easymenu', `fit-frame', `misc-fns',
;;   `speedbar', `strings', `thingatpt', `thingatpt+', `wid-edit',
;;   `wid-edit+', `widget'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; Enhancements to `cus-edit.el'.
;;
;;  Terminology
;;  -----------
;;
;;  Most of the enhancements here basically try to make Customize play
;;  a little better with Emacs.  Customize deals with user
;;  preferences, which are faces and variables.  User variables are
;;  also called "user options"; they are defined by `user-variable-p'.
;;  All faces are user preferences.
;;
;;  Note: The Customize source code sometimes refers to both faces and
;;  user variables (what I am calling "user preferences") as "user
;;  options".  The latter term has traditionally been used in Emacs for
;;  user variables only.
;;
;;  Contents
;;  --------
;;
;;  The enhancements to standard library `cus-edit.el' provided by
;;  `cus-edit+.el' include miscellaneous enhancements, such as
;;  formatting the Customize buffer better, and enhancements to make
;;  Customize play better with the rest of Emacs.  Most of the
;;  description here is about the latter.
;;
;;  Customizing Options of a Particular Type
;;  ----------------------------------------
;;
;;  Command `customize-apropos-options-of-type' is similar to the
;;  standard command `customize-apropos-options', but it also lets you
;;  specify the type of the options to find.
;;
;;  To use `customize-apropos-options-of-type', you specify a
;;  `defcustom' type and a regexp.  The command opens a Customize
;;  buffer for all options that are defined with the specified type
;;  and whose names match the specified regexp.
;;
;;  With a prefix argument, the matching options need not be defined
;;  with exactly the same `defcustom' type.  They need only have their
;;  current value be compatible with the type you specify.
;;
;;  Enhancements to Make Customize Play Better with Emacs
;;  -----------------------------------------------------
;;
;;  There are various ways to change preferences outside of Customize,
;;  and Customize unfortunately doesn't recognize these changes as
;;  preference settings - it considers them to be "changed outside the
;;  customize buffer", which really means that it just throws up its
;;  hands.
;;
;;  The main idea here is to let Customize know about changes made
;;  outside it, to make Customize think that they were made inside
;;  Customize.  In this way, there is no such outside/inside
;;  distinction (for user preferences), and it doesn't matter where or
;;  how a preference is changed.
;;
;;  When this is the case, you can use command `customize-customized'
;;  to check all preferences that have been changed from their
;;  standard or saved settings, and it will take all changes into
;;  account, no matter how or where the changes were made.
;;
;;  Because this is useful, `customize-customized' has been modified
;;  to be used as a hook in `kill-emacs-query-functions'.  That way,
;;  before you quit Emacs, you are notified of all preference changes
;;  you have made and given a chance to save them (individually or
;;  collectively).  This is analogous to Emacs asking you about files
;;  you've changed but not saved, before letting you exit. (If you
;;  also use another hook to confirm exit from Emacs, then `C-x C-c'
;;  becomes, in effect, a key binding for `customize-customized' -
;;  just say `n' to exiting Emacs.)
;;
;;  Updating Customize with External Changes
;;  ----------------------------------------
;;
;;  In order to keep Customize synched with changes made outside it,
;;  command `customize-update-all' can be used automatically during
;;  idle moments to tell Customize that all user options and faces
;;  that have been changed outside it are now set - just as if they
;;  were set in Customize.  You can turn this automatic updating on
;;  and off with command `customize-toggle-outside-change-updates'.
;;
;;  Read This If You Use Frame-Specific Faces
;;  -----------------------------------------
;;
;;  The automatic updating that you turn on (or off) with
;;  `customize-toggle-outside-change-updates' uses internal variable
;;  `custom-update-timer' to periodically run command
;;  `customize-update-all'.  That command in turn uses commands
;;  `customize-update-all-vars' to update variables and
;;  `customize-update-all-faces' to updated faces.  It thus updates
;;  Customize with respect to face changes as well as variable
;;  changes.
;;
;;  Unlike user options (variables), faces can be specific to
;;  individual frames.  The face updating code used here assumes that
;;  you do not use different versions of a face on different frames,
;;  that, for example, face `foo' has the same attributes on all
;;  frames.  If that is not the way you use faces and frames, then you
;;  might not want to automatically update Customize to recognize face
;;  changes made outside Customize.  In that case, change the value of
;;  `custom-update-timer' in your init file (~/.emacs) to use
;;  `customize-update-all-vars' instead of `customize-update-all':
;;
;;  (defvar custom-update-timer
;;    (run-with-idle-timer custom-check-for-changes-interval
;;                         t 'customize-update-all-vars) ; <======
;;    "Timer used to automatically tell Customize of outside changes
;;  to preferences when idle.")
;;
;;  The automatic face updating works like this: The current-frame
;;  definition of each face is compared with the face's definition
;;  according to Customize.  If these are different, then the
;;  Customize definition is updated to the current-frame definition.
;;  Since there is no way to know which frame will be current when
;;  updating takes place, if you 1) use automatic updating and 2) use
;;  different definitions of a given face on different frames, then
;;  you probably do not want to update faces automatically.
;;
;;  Dealing with Spurious Changes, 1: Save
;;  --------------------------------------
;;
;;  Even if you don't change any preferences yourself, when you quit
;;  Emacs the first time you are informed that there are lots of
;;  changed preferences, and you are given a chance to save those
;;  changes.  What are those changes? They represent all of the user
;;  preferences that Emacs and various Emacs libraries have changed
;;  behind Customize's back - even before you did anything.
;;
;;  You'll see user options like `baud-rate' that are set in Emacs C
;;  code without informing Customize to mark their settings as
;;  `standard' (= installed).  There shouldn't be any such apparent
;;  "changes", since this is part of standard Emacs, but that's the
;;  way it is, for now.  Customize is still fairly new, and lots of
;;  Emacs libraries still define and change user preferences without
;;  going through Customize and, in effect, telling it not to consider
;;  such preference changes as changes.
;;
;;  If you choose to save these preference changes, you will never
;;  again be bothered by being informed that they have changed (unless
;;  you change them).  So, that's one solution to this bother, which
;;  makes it a one-time only nuisance: just say "save all".
;;
;;  Dealing with Spurious Changes, 2: Ignore
;;  ----------------------------------------
;;
;;  Another solution is also possible.  Some user preferences, like
;;  `case-fold-search' and `debug-on-error' are really the kind of
;;  thing that you change often and temporarily - you don't really
;;  care about saving their changes, and you certainly don't want to
;;  be asked whether or not you want to save them each you quit Emacs.
;;
;;  To deal with that, a list of ignored preferences,
;;  `customize-customized-ignore', is defined here.  Its preferences
;;  (symbols) are not used by `customize-customized' at all (you can
;;  override that interactively with a prefix arg).  So, the other way
;;  to deal with the legacy Emacs preferences, besides just saving
;;  them in your custom file, is to add them to
;;  `customize-customized-ignore' so `customize-customized' will
;;  ignore them.
;;
;;  To make it easy for you to add preferences to this ignore list,
;;  `Ignore Unsaved Changes' menu items and buttons have been
;;  added.  You can choose to ignore specific preferences or all
;;  preferences in a Customize buffer - in particular, all preferences
;;  in the Customize buffer from `customize-customized' (all changed
;;  preferences).
;;
;;  Dealing with Spurious Changes, 3: Consider Unchanged
;;  ----------------------------------------------------
;;
;;  There is also a third way to treat preference changes that you are
;;  not responsible for, as an alternative to saving them to your
;;  custom file or having Customize always ignore them: tell Customize
;;  to consider the current changes as unchanged.  This essentially
;;  treats them as having been saved, but without saving them.  You can
;;  do this using the `Consider Unchanged' menu items and buttons
;;  added here.
;;
;;  For instance, after starting Emacs, you can examine the current
;;  preference changes (using `customize-customized') from Emacs
;;  itself and loaded libraries, and choose `Consider Unchanged' to
;;  let Customize know that the current values are to be treated as if
;;  they were saved, but without actually saving them to your custom
;;  file.  That way, your custom file is not polluted with things that
;;  you are not really concerned with, yet you are not bothered by
;;  seeing such fictitious changes show up each time you check for
;;  changes.
;;
;;  However, unlike ignoring changes to certain preferences, and
;;  really saving current preference values, `Consider Unchanged' is
;;  not a persistent change.  You can use it at any time to "reset" the
;;  change counter for given preferences, so that the current change
;;  is considered the new base value (as if it were saved), and any
;;  further changes you make to them will show up as changes, using
;;  `customize-customize'.
;;
;;  Updating, Revisited
;;  -------------------
;;
;;  Finally, there is one more additional menu item and button
;;  provided here, `Set from External Changes', which just executes
;;  the appropriate `customize-update-all*' command (depending on the
;;  menu/button location).  It is useful if you do not choose to use
;;  automatic updating of preferences that are changed outside of
;;  Customize.
;;
;;  Conclusion & Future
;;  -------------------
;;
;;  The changes in Customize behavior provided by this library are
;;  important, because they can encourage library authors to explore
;;  other ways of changing preference values, and still let users save
;;  the changes using Customize.  For instance in my library
;;  `doremi-frm.el' I have defined several commands that let you
;;  directly manipulate frame and face properties (e.g. incremental
;;  color changes).
;;
;;  By making Customize aware of such "outside" changes, you can
;;  easily save them in Customize.  There are lots of preferences that
;;  would be amenable to such "direct-manipulation", which I think
;;  would be an improvement in ease of customization.
;;
;;  In sum, this library in effect gets rid of the useless "changed
;;  outside Customize" state.  User preferences have only the
;;  `standard', `saved', or `set' (= unsaved) state, regardless of how
;;  they are set.  Someday, Customize will be more integrated with the
;;  rest of Emacs, and "changed outside Customize" will make no more
;;  sense than "changed outside of Emacs".  Customize will then be
;;  just one possible way to access the space of user preferences, the
;;  same preference space that other parts of Emacs can access
;;  differently.  If we're writing on the same blackboard, you can see
;;  what I erase, and I can see what you write.
;;
;;  That's the goal.  This tries to be a step on the way.
;;
;;  How To Use
;;  ----------
;;
;;  To use this library, put this in your init file (.emacs):
;;
;;    (require cus-edit+)
;;
;;  To update Customize once, manually, so that it learns about stuff
;;  that was customized outside it, use any of these commands:
;;  `customize-update-all-faces', `customize-update-all-vars',
;;  `customize-update-all' (which is both faces and variables).
;;
;;  To do the same updating automatically, add this to your init file
;;  (automatic updating is off by default):
;;
;;    (customize-toggle-outside-change-updates 99)
;;
;;  To turn automatic updating on/off, use command
;;  `customize-toggle-outside-change-updates'.
;;
;;  To change the number of idle seconds before automatically updating
;;  Customize, use command `customize-set-auto-update-timer-period'.
;;
;;  To *not* have `customize-customized' check for unsaved preference
;;  changes when you quit Emacs, add this also:
;;
;;    (remove-hook 'kill-emacs-query-functions 'customize-customized)
;;
;;
;;
;;  Options (variables) defined here:
;;
;;    `customp-buffer-create-hook', `customize-customized-ignore'.
;;
;;    Emacs 20 only: `custom-buffer-verbose-help'.
;;
;;
;;  Commands defined here:
;;
;;    `Custom-consider-unchanged', `Custom-ignore-unsaved',
;;    `customize-apropos-options-of-type',
;;    `customize-consider-all-faces-unchanged',
;;    `customize-consider-all-unchanged',
;;    `customize-consider-all-vars-unchanged',
;;    `customize-other-window',
;;    `customize-set-auto-update-timer-period',
;;    `customize-toggle-outside-change-updates',
;;    `customize-update-all', `customize-update-all-faces',
;;    `customize-update-all-vars'.
;;
;;  Functions defined here:
;;
;;    `custom-consider-face-unchanged',
;;    `custom-consider-variable-unchanged',
;;    `custom-ignore-unsaved-preference', `custom-type',
;;    `custom-update-face', `custom-update-variable',
;;    `custom-value-satisfies-type-p', `custom-var-inherits-type-p',
;;    `custom-var-is-of-type-p', `custom-var-matches-type-p',
;;    `custom-var-val-satisfies-type-p'.
;;
;;  Internal variables defined here:
;;
;;    `custom-check-for-changes-interval',
;;    `custom-check-for-changes-when-idle-p', `custom-update-timer'.
;;
;;
;;  ***** NOTE: The following variables defined in `cus-edit.el' have
;;              been REDEFINED HERE:
;;
;;    `custom-face-menu', `Custom-mode-menu', `custom-variable-menu'.
;;
;;
;;  ***** NOTE: The following functions defined in `cus-edit.el' have
;;              been REDEFINED HERE:
;;
;;    `custom-add-parent-links', `custom-buffer-create-internal',
;;    `customize-customized', `customize-group-other-window'.
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change log:
;;
;; 2011/03/31 dadams
;;     custom-var-(matches|inherits)-type-p: Wrap string-match with save-match-data.
;; 2011/01/03 dadams
;;     Removed autoload cookies on remove-hook and non-interactive functions.
;;     Added some missing autoload cookies for commands.
;; 2010/07/22 dadams
;;     custom-variable-menu: Sync with Emacs 24 dev code.
;; 2008/04/24 dadams
;;     custom-add-parent-links: Added new optional arg (Emacs 22.2).
;; 2007/12/28 dadams
;;     Added: custom-add-parent-links.
;; 2007/12/24 dadams
;;     custom-var-inherits-type-p: Recheck type match after set var-type to its car.
;;     Added: custom-type.
;; 2007/12/23 dadams
;;     custom-var-is-of-type-p:
;;       Added MODE arg.  Use custom-var-inherits-type-p, custom-var-val-satisfies-type-p.
;;       Redefined as MODE choice, not just a simple or.  Treat more cases.
;;     Added: custom-var-inherits-type-p, custom-var-val-satisfies-type-p,
;;            custom-value-satisfies-type-p.
;; 2007/12/22 dadams
;;     custom-var-is-of-type-p:
;;       Check supertypes also.  Use both :validate and :match.
;;       Wrap type check in condition-case. Use widget-put instead of plist-put.
;;     Added soft require of wid-edit+.el.
;; 2007/12/21 dadams
;;     custom-var-is-of-type-p: Use :validate, not :match, for the test.
;; 2007/12/15 dadams
;;     Added: customize-apropos-options-of-type, custom-var-is-of-type-p.
;; 2007/11/12 dadams
;;     kill-emacs-query-functions: Wrap customize-customized in condition-case.
;; 2007/03/31 dadams
;;     customize-customized-ignore: Include savehist-minibuffer-history-variables.
;;     custom-check-for-changes-interval: Changed default from 10 to 60.
;; 2006/09/17 dadams
;;     custom-buffer-verbose-help: Updated versions for defining it.
;; 2006/04/07 dadams
;;     customize-update-all-faces: Don't use face `default'.
;; 2006/01/07 dadams
;;     Added :link for sending bug report.
;; 2006/01/06 dadams
;;     Added defgroup.  Added :link.
;;     Renamed custom stuff defined here to use prefix customp.
;; 2005/05/15 dadams
;;     Don't turn speed-bar on and off; just require it.
;; 2005/05/03 dadams
;;     custom-browse-visibility-action: fit-frame upon [+]/[-] node expand/contract.
;; 2005/01/29 dadams
;;     customize-update-all*: call custom-redraw.
;;     custom-face-menu, custom-variable-menu, custom-buffer-create-internal:
;;         Removed restriction (not custom-check-for-changes-when-idle-p)
;;         for Set from External Changes.
;;     Added: widget-get-tag-or-value.
;; 2005/01/28 dadams
;;     Bug fixes:
;;     1. speedbar-use-imenu-flag, face-valid-attribute-values:
;;        Hacks to suppress periodic superfluous messages.
;;     2. (S. Taylor reported): define custom-buffer-verbose-help for pre-21.3.50.
;; 2005/01/25 dadams
;;     Added: custom-consider-face-unchanged, custom-consider-variable-unchanged,
;;            Custom-consider-unchanged, custom-update-face, custom-update-variable,
;;            custom-variable-p.
;;     Added menu items/buttons: Consider Unchanged, Ignore Unsaved Changes,
;;                               Set from External Changes.
;;     custom-*-menu: Use defconst, so *Help* links will bring user here.
;;     Only turn off customize-toggle-outside-change-updates on first load.
;; 2005/01/24 dadams
;;     Added: custom-buffer-create-hook.  Use it in custom-buffer-create-internal.
;; 2005/01/22 dadams
;;     Removed: check-unsaved-customizations-flag.
;;     Renamed: check-unsaved-customizations -> customize-customized,
;;              check-unsaved-customizations-ignore -> customize-customized-ignore.
;;     Added: custom-buffer-verbose-help, custom-check-for-changes-interval,
;;            custom-check-for-changes-when-idle-p, customize-customized,
;;            custom-update-timer, custom-raised-buttons, customize-update-all*,
;;            customize-toggle-outside-change-updates,
;;            customize-set-auto-update-timer-period, Custom-ignore-unsaved,
;;            custom-ignore-unsaved-preference, Custom-mode-menu,
;;            custom-buffer-create-internal, custom-face-menu, custom-variable-menu.
;;     Bound: `q' to quit-window.
;; 2005/01/20 dadams
;;     Added: check-unsaved-customizations, check-unsaved-customizations-flag,
;;            check-unsaved-customizations-ignore.
;;            Added check-unsaved-customizations to kill-emacs-query-functions.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'cus-edit)

(and (< emacs-major-version 21)         ;; dolist, push
     (eval-when-compile (require 'cl))) ;; (plus, for Emacs <20: when, unless)

(require 'wid-edit+ nil t)     ;; (no error if not found):
                               ;; redefined color widget (for custom-var-is-of-type-p)
(require 'autofit-frame nil t) ;; (no error if not found): fit-frame-if-one-window

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;





;;; KEYS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; REPLACES ORIGINAL binding in `cus-edit.el'.
;; Don't use the silly `Custom-buffer-done' of Emacs 21 (until it is fixed),
;; and don't use `bury-buffer' (Emacs 20), since it doesn't work with
;; dedicated windows.  Use `quit-window': DTRT.
;;
(define-key custom-mode-map "q" 'quit-window)




;;; USER OPTIONS (VARIABLES) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgroup Custom-Plus nil
  "Enhancements to Customize."
  :prefix "customp-" :group 'customize
  :link `(url-link :tag "Send Bug Report"
          ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
cus-edit+.el bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Other Libraries by Drew"
          "http://www.emacswiki.org/cgi-bin/wiki/DrewsElispLibraries")
  :link '(url-link :tag "Download" "http://www.emacswiki.org/cgi-bin/wiki/cus-edit+.el")
  :link '(url-link :tag "Description"
          "http://www.emacswiki.org/cgi-bin/wiki/CustomizingAndSaving#CustomizePlus")
  :link '(emacs-commentary-link :tag "Commentary" "cus-edit+")
  )

(defcustom customize-customized-ignore
  (append (and (boundp 'savehist-minibuffer-history-variables)
               savehist-minibuffer-history-variables)
          '(case-fold-search debug-on-error))
  "*User preferences to ignore in `customize-customized'.
Items in this list are symbols naming faces or variables."
  :type '(repeat symbol) :group 'Custom-Plus
  :link '(url-link :tag "Other Libraries by Drew"
          "http://www.emacswiki.org/cgi-bin/wiki/DrewsElispLibraries")
  :link '(url-link :tag "Download"
          "http://www.emacswiki.org/cgi-bin/wiki/cus-edit+.el")
  :link '(url-link :tag "Description"
          "http://www.emacswiki.org/cgi-bin/wiki/CustomizingAndSaving#CustomizePlus")
  :link '(emacs-commentary-link :tag "Commentary" "cus-edit+")
  )

(unless (or (>= emacs-major-version 22)
            (and (= emacs-major-version 21) (= emacs-minor-version 4)))
  (defcustom custom-buffer-verbose-help t
    "*If non-nil, include explanatory text in the customization buffer."
    :type 'boolean :group 'custom-buffer))

(defcustom customp-buffer-create-hook (and (fboundp 'fit-frame-if-one-window)
                                           'fit-frame-if-one-window)
  "*Hook called when creating a Customize buffer."
  :type 'hook
  :group 'Custom-Plus)


;; Speedbar BUG fix: The original code called `locate-library', which caused
;; message `Library is "imenu"' to be displayed every
;; `custom-check-for-changes-interval'.
;; BUG reported 01/27/2005 (but it won't be fixed, because it's an Emacs 20 bug.)
;;
;; Note: This must be a `defcustom'; `defvar', `setq', and `setq-default'
;;       won't cut the mustard.
;;
(when (< emacs-major-version 21)
  (require 'speedbar)  ;; Let speedbar's defcustom give the wrong definition.
  (defcustom speedbar-use-imenu-flag (fboundp 'imenu) ; Now give the right definition.
    "*Non-nil means use imenu for file parsing.  nil to use etags.
XEmacs prior to 20.4 doesn't support imenu, therefore the default is to
use etags instead.  Etags support is not as robust as imenu support."
    :tag "User Imenu" :group 'speedbar :type 'boolean))


;; REPLACES ORIGINAL in `cus-edit.el'.
;; Changed text for saved, to not give impression that preference
;; was necessarily set and saved.
;;
(defconst custom-magic-alist '((nil "#" underline "\
uninitialized, you should not see this.")
                               (unknown "?" italic "\
unknown, you should not see this.")
                               (hidden "-" default "\
hidden, invoke \"Show\" in the previous line to show." "\
group now hidden, invoke \"Show\", above, to show contents.")
                               (invalid "x" custom-invalid-face "\
the value displayed for this %c is invalid and cannot be set.")
                               (modified "*" custom-modified-face "\
you have edited the value as text, but you have not set the %c." "\
you have edited something in this group, but not set it.")
                               (set "+" custom-set-face "\
you have set this %c, but not saved it for future sessions." "\
something in this group has been set, but not saved.")
                               (changed ":" custom-changed-face "\
this %c has been changed outside the customize buffer." "\
something in this group has been changed outside customize.")
                               (saved "!" custom-saved-face "\
this %c is unchanged from the saved (startup) setting." "\
something in this group is unchanged from the saved (startup) setting.")
                               (rogue "@" custom-rogue-face "\
this %c has not been changed with customize." "\
something in this group is not prepared for customization.")
                               (standard " " nil "\
this %c is unchanged from its standard setting." "\
visible group members are all at standard settings."))
  "Alist of customize option states.
Each entry is of the form (STATE MAGIC FACE ITEM-DESC [ GROUP-DESC ]), where

STATE is one of the following symbols:

`nil'
   For internal use, should never occur.
`unknown'
   For internal use, should never occur.
`hidden'
   This item is not being displayed.
`invalid'
   This item is modified, but has an invalid form.
`modified'
   This item is modified, and has a valid form.
`set'
   This item has been set but not saved.
`changed'
   The current value of this item has been changed temporarily.
`saved'
   This item is marked for saving.
`rogue'
   This item has no customization information.
`standard'
   This item is unchanged from the standard setting.

MAGIC is a string used to present that state.

FACE is a face used to present the state.

ITEM-DESC is a string describing the state for options.

GROUP-DESC is a string describing the state for groups.  If this is
left out, ITEM-DESC will be used.

The string %c in either description will be replaced with the
category of the item.  These are `group'. `option', and `face'.

The list should be sorted most significant first.")


;; REPLACES ORIGINAL in `cus-edit.el'.
;; Rename `Parent groups:' to `Groups:' and `Parent documentation:' to `See Also:'
;; Fill `See Also:' links list.
;;
(defun custom-add-parent-links (widget &optional initial-string
                                doc-initial-string)
  "Add \"Groups: ...\" to WIDGET if WIDGET has groups.
The value is non-nil if any groups were found.
If INITIAL-STRING is non-nil, use that rather than \"Groups:\"."
  (let ((name (widget-value widget))
	(type (widget-type widget))
	(buttons (widget-get widget :buttons))
	(start (point))
	(parents nil))
    (insert (or initial-string "\nGroups:"))
    (mapatoms (lambda (symbol)
		(when (member (list name type) (get symbol 'custom-group))
		  (insert " ")
		  (push (widget-create-child-and-convert
			 widget 'custom-group-link
			 :tag (custom-unlispify-tag-name symbol)
			 symbol)
			buttons)
		  (setq parents (cons symbol parents)))))
    (and (null (get name 'custom-links)) ;No links of its own.
         (= (length parents) 1)         ;A single parent.
         (let* ((links (delq nil (mapcar (lambda (w)
					   (unless (eq (widget-type w)
						       'custom-group-link)
					     w))
					 (get (car parents) 'custom-links))))
                (many (> (length links) 2)))
           (when links
             (let ((pt (point))
                   (left-margin (+ left-margin 2)))
               (insert "\n" (or doc-initial-string "See Also:") " ")
               (while links
                 (push (widget-create-child-and-convert
                        widget (car links)
                        :button-face 'custom-link
                        :mouse-face 'highlight
                        :pressed-face 'highlight)
                       buttons)
                 (setq links (cdr links))
                 (cond ((null links)
                        (insert ".\n"))
                       ((null (cdr links))
                        (if many
                            (insert ", and ")
                          (insert " and ")))
                       (t
                        (insert ", "))))
               (fill-region-as-paragraph pt (point))
               (delete-to-left-margin (1+ pt) (+ pt 2))))))
    (if parents
        (insert "\n")
      (delete-region start (point)))
    (widget-put widget :buttons buttons)
    parents))



;;; INTERNAL VARIABLES ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar custom-check-for-changes-interval 60
  "Number of seconds to wait before checking for preference changes.
Do NOT change this yourself to change the wait period; instead, use
`\\[customize-set-auto-update-timer-period]'.")

(defvar custom-check-for-changes-when-idle-p nil
  "If non-`nil', then automatically tell Customize of outside changes
when Emacs is idle for `custom-check-for-changes-interval' seconds.
Do NOT change this yourself; instead, use
`\\[customize-toggle-outside-change-updates]'.")

(defvar custom-update-timer
  (run-with-idle-timer custom-check-for-changes-interval t 'customize-update-all)
  "Timer used to automatically tell Customize of outside changes
to preferences when idle.")


;; REPLACES ORIGINAL in `cus-edit.el'.
;; Added `Consider Unchanged', `Ignore Unsaved Changes', `Set from External Changes'.
;;
(defconst custom-face-menu
  '(("Set for Current Session" custom-face-set)
    ("Save for Future Sessions" custom-face-save-command)
    ("Consider Unchanged" custom-consider-face-unchanged
     (lambda (widget) (not (get (widget-get-tag-or-value widget) 'saved-face))))
    ("Ignore Unsaved Changes" custom-ignore-unsaved-preference
     (lambda (widget) (eq (widget-get widget :custom-state) 'set)))
    ("Set from External Changes" custom-update-face
     (lambda (widget) (let* ((symbol (widget-get-tag-or-value widget))
                             (cface (or (get symbol 'customized-face)
                                        (get symbol 'saved-face)
                                        (get symbol 'face-defface-spec))))
                        (and cface
                             (custom-facep symbol)
                             (not (face-spec-match-p symbol cface))))))
    ("Reset to Saved" custom-face-reset-saved
     (lambda (widget)
       (or (get (widget-value widget) 'saved-face)
           (get (widget-value widget) 'saved-face-comment))))
    ("Reset to Standard Setting" custom-face-reset-standard
     (lambda (widget)
       (get (widget-value widget) 'face-defface-spec)))
    ("---" ignore ignore)
    ("Add Comment" custom-comment-show
     (lambda (widget)
       (and (boundp 'custom-comment-invisible-p)
            custom-comment-invisible-p)))
    ("---" ignore ignore)
    ("Show all display specs" custom-face-edit-all
     (lambda (widget)
       (not (eq (widget-get widget :custom-form) 'all))))
    ("Just current attributes" custom-face-edit-selected
     (lambda (widget)
       (not (eq (widget-get widget :custom-form) 'selected))))
    ("Show as Lisp expression" custom-face-edit-lisp
     (lambda (widget)
       (not (eq (widget-get widget :custom-form) 'lisp)))))
  "Alist of actions for the `custom-face' widget.
Each entry has the form (NAME ACTION FILTER) where NAME is the name of
the menu entry, ACTION is the function to call on the widget when the
menu is selected, and FILTER is a predicate which takes a `custom-face'
widget as an argument, and returns non-nil if ACTION is valid on that
widget.  If FILTER is nil, ACTION is always valid.")


;; REPLACES ORIGINAL in `cus-edit.el'.
;; Added `Consider Unchanged', `Ignore Unsaved Changes', `Set from External Changes'.
;;
(defconst custom-variable-menu
  `(("Set for Current Session"
     custom-variable-set
     (lambda (widget)
       (eq (widget-get widget :custom-state) 'modified)))
    ;; Note that in all the backquoted code in this file, we test
    ;; init-file-user rather than user-init-file.  This is in case
    ;; cus-edit is loaded by something in site-start.el, because
    ;; user-init-file is not set at that stage.
    ;; http://lists.gnu.org/archive/html/emacs-devel/2007-10/msg00310.html
    ,@(when
       (or custom-file init-file-user)
       '(("Save for Future Sessions" custom-variable-save
          (lambda (widget)
            (memq (widget-get widget :custom-state)
                  '(modified set changed rogue))))))
    ("Consider Unchanged"
     custom-consider-variable-unchanged
     (lambda (widget) (not (get (widget-get-tag-or-value widget) 'saved-value))))
    ("Ignore Unsaved Changes"
     custom-ignore-unsaved-preference
     (lambda (widget) (eq (widget-get widget :custom-state) 'set)))
    ("Set from External Changes"
     custom-update-variable
     (lambda (widget)
       (let* ((symbol (widget-get-tag-or-value widget))
              (cval (or (get symbol 'customized-value)
                        (get symbol 'saved-value)
                        (get symbol 'standard-value))))
         (and cval                    ; Declared with defcustom.
              (default-boundp symbol)
              (not (equal (eval (car cval)) ; But does not match customize.
                          (default-value symbol)))))))
    ("Reset to Current"
     custom-redraw
     (lambda (widget)
       (and (default-boundp (widget-value widget))
            (memq (widget-get widget :custom-state) '(modified changed)))))
    ("Reset to Saved"
     custom-variable-reset-saved
     (lambda (widget)
       (and (or (get (widget-value widget) 'saved-value)
                (get (widget-value widget) 'saved-variable-comment))
            (memq (widget-get widget :custom-state)
                  '(modified set changed rogue)))))
    ,@(when (or custom-file init-file-user)
            '(("Reset to Standard Setting" custom-variable-reset-standard
               (lambda (widget)
                 (and (get (widget-value widget) 'standard-value)
                      (memq (widget-get widget :custom-state)
                            '(modified set changed saved rogue)))))))
    ,@(when (>= emacs-major-version 21)
            '(("Use Backup Value" custom-variable-reset-backup
               (lambda (widget)
                 (get (widget-value widget) 'backup-value)))))
    ,@(when (boundp 'custom-comment-invisible-p)
            '(("---" ignore ignore)
              ("Add Comment" custom-comment-show
               (lambda (widget) custom-comment-invisible-p))))
    ("---" ignore ignore)
    ("Don't show as Lisp expression"
     custom-variable-edit
     (lambda (widget)
       (eq (widget-get widget :custom-form) 'lisp)))
    ("Show initial Lisp expression"
     custom-variable-edit-lisp
     (lambda (widget)
       (eq (widget-get widget :custom-form) 'edit))))
  "Alist of actions for the `custom-variable' widget.
Each entry has the form (NAME ACTION FILTER) where NAME is the name of
the menu entry, ACTION is the function to call on the widget when the
menu is selected, and FILTER is a predicate which takes a `custom-variable'
widget as an argument, and returns non-nil if ACTION is valid on that
widget.  If FILTER is nil, ACTION is always valid.")


(when (< emacs-major-version 21) (defvar custom-raised-buttons nil))





;;; FUNCTIONS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(defun customize-apropos-options-of-type (type regexp &optional arg)
  "Customize all loaded customizable options of type TYPE that match REGEXP.
With no prefix arg, each option is defined with `defcustom' type TYPE.
With a prefix arg, either each option is defined with `defcustom' type
 TYPE or its current value is compatible with TYPE.

If TYPE is nil (the default value) then all `defcustom' variables are
potential candidates."
  (interactive
   (list (car (condition-case err
                  (read-from-string
                   (let ((types ()))
                     (mapatoms
                      (lambda (cand)
                        (when (custom-variable-p cand)
                          (push (list (format "%s" (format "%S" (get cand 'custom-type))))
                                types))))
                     (completing-read "Customize all options of type: "
                                      (help-remove-duplicates types)
                                      nil nil nil nil "nil")))
                (end-of-file (error "No such custom type"))))
         (read-string "Customize options matching (regexp): ")
         current-prefix-arg))
  (let ((found ()))
    (mapatoms (lambda (symb)
                (when (and (string-match regexp (symbol-name symb))
                           (boundp symb)
                           (or (not (fboundp 'indirect-variable))
                               (eq (indirect-variable symb) symb))
                           (or (get symb 'saved-value)
                               (custom-variable-p symb))
                           (or (not type) ; Options of all types if requested type = nil.
                               (if arg                               
                                   (custom-var-is-of-type-p symb (list type))
                                 (equal (get symb 'custom-type) type))))
                  (push (list symb 'custom-variable) found))))
    (unless found (error "No options of type `%S' matching regexp `%s'" type regexp))
    (custom-buffer-create (custom-sort-items found t "*Customize Apropos*"))))

;; Same as `icicle-var-is-of-type-p' and `help-var-is-of-type-p'.
(defun custom-var-is-of-type-p (variable types &optional mode)
  "Return non-nil if VARIABLE satisfies one of the custom types in TYPES.
TYPES is a list of `defcustom' type sexps or a list of regexp strings.
TYPES are matched, in order, against VARIABLE's type definition or
VARIABLE's current value, until one is satisfied or all are tried.

If TYPES is a list of regexps, then each is regexp-matched against
VARIABLE's custom type.

Otherwise, TYPES is a list of type sexps, each of which is a
definition acceptable for `defcustom' :type or the first symbol of
such a definition (e.g. `choice').  In this case, two kinds of type
comparison are possible:

1. VARIABLE's custom type, or its first symbol, is matched using
  `equal' against each type in TYPES.

2. VARIABLE's current value is checked against each type in TYPES to
   see if it satisfies one of them.  In this case, VARIABLE's own type
   is not used; VARIABLE might not even be typed - it could be a
   variable not defined using `defcustom'.

For any of the comparisons against VARIABLE's type, either that type
can be checked directly or its supertypes (inherited types) can also
be checked.

These different type-checking possibilities depend on the value of
argument MODE, as follows, and they determine the meaning of the
returned value:

`direct':   VARIABLE's type matches a member of list TYPES
`inherit':  VARIABLE's type matches or is a subtype of a TYPES member
`value':    VARIABLE is bound, and its value satisfies a type in TYPES
`inherit-or-value': `inherit' or `value', tested in that order
`direct-or-value':  `direct' or `value', tested in that order
anything else (default): `inherit'

VARIABLE's current value cannot satisfy a regexp type: it is
impossible to know which concrete types a value must match."
  (case mode
    ((nil inherit)     (custom-var-inherits-type-p variable types))
    (inherit-or-value  (or (custom-var-inherits-type-p variable types)
                           (custom-var-val-satisfies-type-p variable types)))
    (value             (custom-var-val-satisfies-type-p variable types))
    (direct            (custom-var-matches-type-p variable types))
    (direct-or-value   (or (member (get variable 'custom-type) types)
                           (custom-var-val-satisfies-type-p variable types)))
    (otherwise         (custom-var-inherits-type-p variable types))))

(defun custom-var-matches-type-p (variable types)
  "VARIABLE's type matches a member of TYPES."
  (catch 'custom-type-matches
    (let ((var-type (get variable 'custom-type)))
      (dolist (type types)
        (when (if (stringp type)
                  (save-match-data (string-match type (format "%s" (format "%S" var-type))))
                (equal var-type type))
          (throw 'custom-type-matches t))))
    nil))  

(defun custom-var-inherits-type-p (variable types)
  "VARIABLE's type matches or is a subtype of a member of list TYPES."
  (catch 'custom-type-inherits
    (let ((var-type (get variable 'custom-type)))
      (dolist (type types)
        (while var-type
          (when (or (and (stringp type)
                         (save-match-data
                           (string-match type (format "%s" (format "%S" var-type)))))
                    (equal type var-type))
            (throw 'custom-type-inherits t))
          (when (consp var-type) (setq var-type (car var-type)))
          (when (or (and (stringp type)
                         (save-match-data
                           (string-match type (format "%s" (format "%S" var-type)))))
                    (equal type var-type))
            (throw 'custom-type-inherits t))
          (setq var-type (car (get var-type 'widget-type))))
        (setq var-type (get variable 'custom-type))))
    nil))

(defun custom-var-val-satisfies-type-p (variable types)
  "VARIABLE is bound, and its value satisfies a type in the list TYPES."
  (and (boundp variable)
       (let ((val (symbol-value variable)))
         (and (widget-convert (get variable 'custom-type))
              (custom-value-satisfies-type-p val types)))))

(defun custom-value-satisfies-type-p (value types)
  "Return non-nil if VALUE satisfies a type in the list TYPES."
  (catch 'custom-type-value-satisfies
    (dolist (type types)
      (unless (stringp type)            ; Skip, for regexp type.
        (setq type (widget-convert type))
        ;; Satisfies if either :match or :validate.
        (when (condition-case nil
                  (progn (when (and (widget-get type :match)
                                    (widget-apply type :match value))
                           (throw 'custom-type-value-satisfies t))
                         (when (and (widget-get type :validate)
                                    (progn (widget-put type :value value)
                                           (not (widget-apply type :validate))))
                           (throw 'custom-type-value-satisfies t)))
                (error nil))
          (throw 'custom-type-value-satisfies t))))
    nil))

(defun custom-type (variable)
  "Returns the `defcustom' type of VARIABLE.
Returns nil if VARIABLE is not a user option.

Note: If the library that defines VARIABLE has not yet been loaded,
then `custom-type' loads it.  Be sure you want to do that before you
call this function."
  (and (custom-variable-p variable)
       (or (get variable 'custom-type) (progn (custom-load-symbol variable)
                                              (get variable 'custom-type)))))

;; Helper function for Emacs 21.3 bugs (< 21.3.50): widgets that don't have `:tag'.
(defun widget-get-tag-or-value (widget)
  "Return :tag or :value of WIDGET, as a symbol."
  (let ((tag (widget-get widget :tag)))
    (if tag
        (intern tag)
      (widget-get widget :value))))


;; REPLACES ORIGINAL in `faces.el'.
;; TEMPORARY BUG fix.  We wrap call to `x-defined-colors' with non-`nil' binding of
;; `executing-kbd-macro' to suppress messages.  Redefining `message' with an `flet'
;; (flet ((message (arg) nil)) might be a bit cleaner, but this is OK.
;; BUG reported 01/21/2005. $$$$$$$
;;
(when (>= emacs-major-version 21)
  (defun face-valid-attribute-values (attribute &optional frame)
    "Return valid values for face attribute ATTRIBUTE.
The optional argument FRAME is used to determine available fonts
and colors.  If it is nil or not specified, the selected frame is
used.  Value is an alist of (NAME . VALUE) if ATTRIBUTE expects a value
out of a set of discrete values.  Value is `integerp' if ATTRIBUTE expects
an integer value."
    (let ((valid
           (case attribute
             (:family
              (if window-system
                  (mapcar #'(lambda (x) (cons (car x) (car x)))
                          (x-font-family-list))
                ;; Only one font on TTYs.
                (list (cons "default" "default"))))
             ((:width :weight :slant :inverse-video)
              (mapcar #'(lambda (x) (cons (symbol-name x) x))
                      (internal-lisp-face-attribute-values attribute)))
             ((:underline :overline :strike-through :box)
              (if window-system
                  (nconc (mapcar #'(lambda (x) (cons (symbol-name x) x))
                                 (internal-lisp-face-attribute-values attribute))
                         (let ((executing-kbd-macro t)) ; TEMPORARY BUG FIX $$$$$
                           (mapcar #'(lambda (c) (cons c c))
                                   (x-defined-colors frame))))
                (mapcar #'(lambda (x) (cons (symbol-name x) x))
                        (internal-lisp-face-attribute-values attribute))))
             ((:foreground :background)
              (mapcar #'(lambda (c) (cons c c))
                      (defined-colors frame)))
             ((:height)
              'integerp)
             (:stipple
              (and (memq window-system '(x w32 mac))
                   (mapcar #'list
                           (apply #'nconc
                                  (mapcar (lambda (dir)
                                            (and (file-readable-p dir)
                                                 (file-directory-p dir)
                                                 (directory-files dir)))
                                          x-bitmap-file-path)))))
             (:inherit
              (cons '("none" . nil)
                    (mapcar #'(lambda (c) (cons (symbol-name c) c))
                            (face-list))))
             (t
              (error "Internal error")))))
      (if (and (listp valid) (not (memq attribute '(:inherit))))
          (nconc (list (cons "unspecified" 'unspecified)) valid)
        valid))))


;; REPLACES ORIGINAL in `cus-edit.el'.
;; 1. Ignores preferences in `customize-customized-ignore'.
;; 2. Added prefix arg to override `customize-customized-ignore'.
;; 3. When not interactive and there are changes, ask for confirmation.
;; 4. Always returns `t', so it can be used as a `kill-emacs-query-functions' hook.
;;
;;;###autoload
(defun customize-customized (&optional check-all-p)
  "Open Customize to check all preferences currently set but not saved.
This is useful in `kill-emacs-query-functions' to check changes you
have made (and possibly saving them) before exiting Emacs.

Changes to preferences listed in `customize-customized-ignore'
are normally ignored here.  However, with non-`nil' CHECK-ALL-P (prefix
argument), all changes are checked.

Changes to preferences that you have declared \"unchanged\" (using,
for example, `Consider Unchanged') are always ignored here."
  ;; Return value must be appropriate for use in `kill-emacs-query-functions'.
  (interactive "P")
  (condition-case failure
      (progn
        (let ((found nil))
          (mapatoms
           (lambda (symbol)
             (and (or check-all-p (not (memq symbol customize-customized-ignore)))
                  (or (get symbol 'customized-face)
                      (get symbol 'customized-face-comment))
                  (custom-facep symbol)
                  (push (list symbol 'custom-face) found))
             (and (or check-all-p (not (memq symbol customize-customized-ignore)))
                  (or (get symbol 'customized-value)
                      (get symbol 'customized-variable-comment))
                  (boundp symbol)
                  (push (list symbol 'custom-variable) found))))
          (if (not found)
              (error "No unsaved customizations (faces or variables)")
            (when (or (interactive-p)
                      (y-or-n-p
                       "You have unsaved preferences.  Do you want to check them? "))
              (custom-buffer-create (custom-sort-items found t nil)
                                    "*Customize - Unsaved Changes*"))))
        t)
    (error (message "%s" (error-message-string failure)) t)))


(add-hook 'kill-emacs-query-functions
          (lambda () (condition-case nil (customize-customized) (error t))))

(remove-hook 'same-window-regexps "\\`\\*Customiz.*\\*\\'")

;;;###autoload
(defun customize-update-all ()
  "Tell Customize that all preferences changed outside it are now set.
This means all changes to all preferences (faces and user variables).
This is suitable to be run automatically as a hook or with a timer,
to keep Customize synched with Emacs changes.
When interactive, call `custom-redraw' on each Customize widget."
  (interactive)
  (when (interactive-p)
    (message "Updating Customize to recognize external settings..."))
  (customize-update-all-vars)
  (customize-update-all-faces)
  (dolist (widget custom-options) (custom-redraw widget))
  (when (interactive-p)
    (message "Updating Customize to recognize external settings...done")))


;;;###autoload
(defun customize-update-all-vars ()
  "Tell customize that all variables changed outside it are now set.
This is suitable to be run automatically as a hook or with a timer,
to keep Customize synched with Emacs changes.
When interactive, call `custom-redraw' on each Customize widget."
  (interactive)
  (when (interactive-p)
    (message "Updating Customize to recognize external variable settings..."))
  (mapatoms
   (lambda (symbol)
     (let ((cval (or (get symbol 'customized-value)
                     (get symbol 'saved-value)
                     (get symbol 'standard-value))))
       (when (and cval                  ; It is declared with defcustom.
                  (default-boundp symbol) ; It has a value.
                  (not (equal (eval (car cval)) ; Value does not match customize's.
                              (default-value symbol))))
         (put symbol 'customized-value (list (custom-quote (eval symbol))))))))
  (when (interactive-p)
    (dolist (widget custom-options) (custom-redraw widget))
    (message
     "Updating Customize to recognize external variable settings...done")))

;;;###autoload
(defun customize-update-all-faces ()
  "Tell Customize that all faces changed outside it are now set.
When interactive, call `custom-redraw' on each Customize widget.
This is suitable to be run automatically as a hook or with a timer,
to keep Customize synched with Emacs changes."
  (interactive)
  (when (interactive-p)
    (message "Updating Customize to recognize external face settings..."))
  (mapatoms
   (lambda (symbol)
     (let ((cface (or (get symbol 'customized-face)
                      (get symbol 'saved-face)
                      (get symbol 'face-defface-spec))))
       (when (and cface                 ; It is declared with defcustom.
                  (custom-facep symbol) ; It is a face.
                  (not (eq 'default symbol)) ; It is not the frame's default face.
                  ;; Face spec does not match customize's.
                  (not (face-spec-match-p symbol cface)))
         (put symbol 'customized-face (list (list 't (face-attr-construct symbol))))
         (unless (< emacs-major-version 21)
           (put symbol 'customized-face-comment (get symbol 'face-comment))
           (put symbol 'face-modified nil))))))
  (when (interactive-p)
    (dolist (widget custom-options) (custom-redraw widget))
    (message "Updating Customize to recognize external face settings...done")))

(defun custom-update-variable (widget)
  "Tell Customize that this variable, changed outside Customize, is now set."
  (let* ((symbol (widget-get-tag-or-value widget)))
    (put symbol 'customized-value (list (custom-quote (eval symbol))))
    (custom-redraw widget)
    (message "Variable `%s' is now set (but not saved)." symbol)))

(defun custom-update-face (widget)
  "Tell Customize that this face, changed outside Customize, is now set.
The definition of the face for the *current frame* is used."
  (let* ((symbol (widget-get-tag-or-value widget)))
    (put symbol 'customized-face (list (list 't (face-attr-construct symbol))))
    (unless (< emacs-major-version 21)
      (put symbol 'customized-face-comment (get symbol 'face-comment))
      (put symbol 'face-modified nil))
    (custom-redraw widget)
    (message "Face `%s' is now set (but NOT saved)." symbol)))


(defalias 'toggle-customize-outside-change-updates
  'customize-toggle-outside-change-updates)

;;;###autoload
(defun customize-toggle-outside-change-updates (&optional arg)
"Turn on or off automatically telling Customize of outside changes.
When on, Customize is told about any preference changes made outside
of Customize, so that it considers them to have been made inside.
With prefix argument, turn on if ARG > 0; else turn off."
  (interactive "p")
  (cond ((or (and arg (< arg 0)) custom-check-for-changes-when-idle-p)
         (cancel-timer custom-update-timer)
         (setq custom-check-for-changes-when-idle-p nil)
         (message "Turned OFF automatically telling Customize of outside changes."))
        (t
         (timer-activate-when-idle custom-update-timer)
         (setq custom-check-for-changes-when-idle-p t)
         (message "Turned ON automatically telling Customize of outside changes."))))

;; Turn it off, by default.
(unless (featurep 'cus-edit+) (customize-toggle-outside-change-updates -99))

;;;###autoload
(defun customize-set-auto-update-timer-period (secs)
  "Set wait until automatically tell Customize of outside changes to SECS
seconds after Emacs is idle.  Whenever Emacs is idle for this many
seconds it will check for user preferences that have been changed
outside of Customize.  All user preference (variable and face) changes
are reported to Customize, so that it recognizes them as if they had
been made within Customize itself.

To turn on or off automatically telling Customize of outside changes,
use `\\[toggle-customize-update-changes]."
  (interactive
   "nSeconds to idle, before telling Customize of outside changes to preferences: ")
  (timer-set-idle-time custom-update-timer
                       (setq custom-check-for-changes-interval secs)
                       t))

;;;###autoload
(defun Custom-ignore-unsaved ()
  "Ignore all currently customized but unsaved preferences.
The preferences that are currently customized but not saved are added
to the list of preferences that `customize-customized' will ignore
when checking for unsaved changes.

NOTE: This list of preferences that `customize-customized' ignores is
      updated here and saved to your customizations file.  To undo
      this change, use `\\[Custom-reset-standard]' on variable
      `customize-customized-ignore'."
  (interactive)
  (if (not (y-or-n-p
            "Unsaved changes to all of these preferences will be IGNORED \
from now on.  Continue? "))
      (message nil)
    (let ((children custom-options))
      (mapc (lambda (child)
              (let ((symbol (widget-get-tag-or-value child)))
                (when (or (get symbol 'customized-value) (get symbol 'customized-face))
                  (message "Changes to `%s' will be IGNORED from now on." symbol))
                (sit-for 0)
                (push symbol customize-customized-ignore)))
            children))
    (customize-save-variable 'customize-customized-ignore customize-customized-ignore)
    (message
     (substitute-command-keys "Changes to all of these preferences will be ignored. \
Use `\\[Custom-reset-standard]' to undo."))))


;; NOTE: There is currently a bug in Emacs 21.3.50, that makes this
;;       not work - the `y-or-n-p' does not ask you anything, and it
;;       assumes `n'.
;;
(defun custom-ignore-unsaved-preference (widget)
  "Ignore any unsaved changes to this preference.
Add it to the list of preferences that `customize-customized' will
ignore when checking for unsaved changes.  Save that list in your
custom file."
  (let ((symbol (widget-get-tag-or-value widget)))
    (unless (or (get symbol 'customized-value) (get symbol 'customized-face))
      (error "No unsaved changes to `%s'" symbol))
    (if (not (y-or-n-p
              (format "Unsaved changes to `%s' will be IGNORED from now on.  Continue? "
                      symbol)))
        (message nil)
      (message "Changes to `%s' will be ignored from now on."
               (widget-get-tag-or-value widget))
      (sit-for 0)
      (push symbol customize-customized-ignore)
      (customize-save-variable 'customize-customized-ignore
                               customize-customized-ignore))))

;;;###autoload
(defun Custom-consider-unchanged ()
  "Consider all preferences here as being unchanged now.
This does not save the current values; it just considers them to be
unchanged values.  If no further changes are made to any of these
preferences, then after doing this, `customize-customize' will not
display any of these preferences, since they were considered
unchanged."
  (interactive)
  (if (not (y-or-n-p
            "All of these values will be considered unchanged now, \
without being saved.  Continue? "))
      (message nil)
    (message "Please wait...")
    (let ((children custom-options))
      (mapc
       (lambda (child)
         (let ((symbol (widget-get-tag-or-value child)))
           (cond ((custom-facep symbol)
                  (custom-consider-face-unchanged child))
                 ((custom-variable-p symbol)
                  (custom-consider-variable-unchanged child)))))
       children))
    (message
     "Current values here are now considered unchanged.  They were not saved.")))


;; Define this for Emacs 20 and 21
(unless (fboundp 'custom-variable-p)
  (defun custom-variable-p (variable)
    "Return non-nil if VARIABLE is a custom variable."
    (or (get variable 'standard-value) (get variable 'custom-autoload))))


;; Inspired from `custom-face-save'.
;; Due to a `cus-edit.el' bug (hidden widgets are not saved), we need to temporarily
;; show hidden widgets.
;;
(defun custom-consider-face-unchanged (widget)
  "Consider this face as being unchanged now.
This does not save the current face properties; it just considers the
face to be unchanged.  If no further changes are made to this face,
then after doing this, `customize-customize' will not display this
face, since it was considered unchanged."
  (message "Please wait...")
  (let ((symbol (widget-value widget))
        (hidden-p (eq 'hidden (widget-get widget :custom-state))))
    (when hidden-p                      ; Show it.
      (widget-put widget :custom-state 'unknown)
      (custom-redraw widget))
    (let* ((child (car (widget-get widget :children)))
           (value (if (< emacs-major-version 21)
                      (widget-value child)
                    (custom-post-filter-face-spec (widget-value child)))))
      (unless (eq (widget-get widget :custom-state) 'standard)
        (put symbol 'saved-face value)))
    (put symbol 'customized-face nil)
    (widget-put widget :custom-state 'saved)
    (when hidden-p                      ; Hide it again.
      (widget-put widget :documentation-shown nil)
      (widget-put widget :custom-state 'hidden)
      (custom-redraw widget)))
  (custom-redraw-magic widget)
  (message "Current face setting is now considered unchanged.  It was not saved."))


;; Inspired from `custom-variable-save'.
;; Due to a `cus-edit.el' bug (hidden widgets are not saved), we need to temporarily
;; show hidden widgets.
;;
;; Should we (put symbol 'saved-value...) only if not
;; (eq (widget-get widget :custom-state) 'standard), as in `custom-face-save'?
;;
(defun custom-consider-variable-unchanged (widget)
  "Consider this variable as being unchanged now.
This does not save the current value; it just considers the value to
be unchanged.  If no further changes are made to this variable, then
after doing this, `customize-customize' will not display this
variable, since it was considered unchanged."
  (message "Please wait...")
  (let* ((form (widget-get widget :custom-form))
         (hidden-p (eq (widget-get widget :custom-state) 'hidden)))
    (when hidden-p                      ; Show it.
      (widget-put widget :custom-state 'unknown)
      (custom-redraw widget)
      (setq form (widget-get widget :custom-form)))
    (let ((child (car (widget-get widget :children)))
          (symbol (widget-value widget)))
      (cond ((memq form '(lisp mismatch))
             (put symbol 'saved-value (list (widget-value child))))
            (t
             (put symbol 'saved-value (list (custom-quote (widget-value child))))))
      (put symbol 'customized-value nil)
      (put symbol 'customized-variable-comment nil))
    (widget-put widget :custom-state 'saved)
    (when hidden-p                      ; Hide it again.
      (widget-put widget :documentation-shown nil)
      (widget-put widget :custom-state 'hidden)
      (custom-redraw widget)))
  (custom-redraw-magic widget)
  (message "Current variable value is now considered unchanged.  It was not saved."))


;;; $$$$$$$$ INLINE THE CONTENTS, TO ONLY LOOP THROUGH SYMBOLS ONCE $$$$$$$$$$$$

;;; $$$$$$$$ PBS FOR EMACS 21 - MAYBE FIRST CALL UPDATE-ALL, THEN DO THIS? $$$$$$$

;;;###autoload
(defun customize-consider-all-unchanged ()
  "Consider all customizable preferences as saved, without saving them."
  (interactive)
  (when (interactive-p) (message "Please wait..."))
  (customize-consider-all-faces-unchanged)
  (customize-consider-all-vars-unchanged)
  (message
   "All current preference values are now considered unchanged.  They were not saved."))

;; (defun customize-consider-all-vars-unchanged ()
;;   "Consider all customized variables as saved, without saving them."
;;   (interactive)
;;   (when (interactive-p) (message "Please wait..."))
;;   (mapatoms
;;    (lambda (symbol)
;;      (when (and (get symbol 'customized-value) ; The set value != standard value.
;;                 (not (equal (get symbol 'customized-value)
;;                             (get symbol 'standard-value))))
;;        (put symbol 'saved-value (get symbol 'customized-value))
;;        (put symbol 'customized-value nil))
;;      (when (get symbol 'customized-value) ; The set value = standard value.
;;        (put symbol 'customized-value nil))
;;      (when (get symbol 'customized-variable-comment) ; Value comment.
;;        (put symbol 'saved-variable-comment (get symbol 'customized-variable-comment))
;;        (put symbol 'customized-variable-comment nil))

;;      ;; Take care of vars changed outside custom.
;;      (let ((cval (or (get symbol 'saved-value) ; (customized-value is nil now)
;;                      (get symbol 'standard-value))))
;;        (when (and cval                  ; Was declared with defcustom.
;;                   (default-boundp symbol) ; Has a value.
;;                   (not (equal (eval (car cval)) ; Which does not match customize.
;;                               (default-value symbol))))
;;          (put symbol 'saved-value (list (custom-quote (default-value symbol))))))))
;;   (message
;;    "All current variable values are now considered unchanged.  They were not saved."))


;; (defun customize-consider-all-vars-unchanged ()
;;   "Consider all customizable variables as saved, without saving them."
;;   (interactive)
;;   (when (interactive-p) (message "Please wait..."))
;;   (mapatoms
;;    (lambda (symbol)
;;      (when (and (or (custom-variable-p symbol) (user-variable-p symbol))
;;                 (default-boundp symbol) ; Has a value.
;;                 (not (member (default-value symbol) ; Value is not saved or standard.
;;                              (list (get symbol 'saved-value)
;;                                    (get symbol 'standard-value)))))
;;        ;; Pretend the current value has been saved.
;;        (put symbol 'saved-value (list (custom-quote (default-value symbol)))))
;;      (put symbol 'customized-value nil)
;;      (when (get symbol 'customized-variable-comment) ; Do same with a custom comment.
;;        (put symbol 'saved-variable-comment (get symbol 'customized-variable-comment)))
;;      (put symbol 'customized-variable-comment nil)))
;;   (message
;;    "All variables are now considered unchanged (\"saved\"), but they were not saved."))

;;;###autoload
(defun customize-consider-all-vars-unchanged ()
  "Consider all customizable variables as saved, without saving them."
  (interactive)
  (when (interactive-p) (message "Please wait..."))
  (mapatoms
   (lambda (symbol)
     (when (and (or (custom-variable-p symbol) (user-variable-p symbol))
                (default-boundp symbol) ; Has a value that is neither saved nor standard.
                (not (member (list (custom-quote (default-value symbol)))
                             (list (get symbol 'saved-value)
                                   (get symbol 'standard-value)))))
       ;; Pretend the current value has been saved.
       (put symbol 'saved-value (list (custom-quote (default-value symbol)))))
     (put symbol 'customized-value nil)
     (when (get symbol 'customized-variable-comment) ; Do same with a custom comment.
       (put symbol 'saved-variable-comment (get symbol 'customized-variable-comment)))
     (put symbol 'customized-variable-comment nil)))
  (message
   "All variables are now considered unchanged (\"saved\"), but they were not saved."))

;;;###autoload
(defun customize-consider-all-faces-unchanged ()
  "Consider all customizable faces as saved, without saving them."
  (interactive)
  (when (interactive-p) (message "Please wait..."))
  (mapatoms
   (lambda (symbol)
     (when (and (custom-facep symbol)   ; Customizable face that is neither saved nor std.
                (not (face-spec-match-p symbol (get symbol 'saved-face)))
                (not (face-spec-match-p symbol (get symbol 'face-defface-spec))))
       ;; Pretend the current face has been saved. ; $$$$ NEED CUSTOM-QUOTE?
       (put symbol 'saved-face (list (list t (custom-face-attributes-get symbol nil)))))
     (put symbol 'customized-face nil)
     (let ((c-face-comment (get symbol 'customized-face-comment))) ; Face comment.
       (when (and c-face-comment (>= emacs-major-version 21))
         (put symbol 'saved-face-comment c-face-comment)
         (put symbol 'face-comment c-face-comment)))
     (put symbol 'customized-face-comment nil)))
  (message
   "All faces are now considered unchanged (\"saved\"), but they were not saved."))

;; (defun customize-consider-all-faces-unchanged ()
;;   "Consider all customized faces as saved, without saving them."
;;   (interactive)
;;   (when (interactive-p) (message "Please wait..."))
;;   (mapatoms
;;    (lambda (symbol)
;;      (when (and (get symbol 'customized-face) ; Set face.
;;                 (not (equal (get symbol 'customized-face)
;;                             (get symbol 'face-defface-spec))))
;;        (put symbol 'saved-face (get symbol 'customized-face))
;;        (put symbol 'customized-face nil))
;;      (when (get symbol 'customized-face) ; Set face = standard face.
;;        (put symbol 'customized-face nil))
;;      (let ((c-face-comment (get symbol 'customized-face-comment))) ; Face comment.
;;        (when (and c-face-comment (>= emacs-major-version 21))
;;          (put symbol 'saved-face-comment c-face-comment)
;;          (put symbol 'face-comment c-face-comment)
;;          (put symbol 'customized-face-comment nil)))))
;;   (message
;;    "All current face values are now considered unchanged.  They were not saved."))



;; REPLACES ORIGINAL in `cus-edit.el'.
;; Added `Consider Unchanged', `Ignore Unsaved Changes', `Set from External Changes'.
;;
(easy-menu-define
 Custom-mode-menu
 custom-mode-map
 "Menu used in customization buffers."
 `("Custom"
   ,(customize-menu-create 'customize)
   ["Set" Custom-set t]
   ["Save" Custom-save t]
   ["Consider Unchanged" Custom-consider-unchanged t]
   ["Ignore Unsaved Changes" Custom-ignore-unsaved t]
   ["Set from External Changes" customize-update-all t]
   ["Reset to Current" Custom-reset-current t]
   ["Reset to Saved" Custom-reset-saved t]
   ["Reset to Standard Settings" Custom-reset-standard t]
   ["Info" (Info-goto-node "(emacs)Easy Customization") t]))


;; REPLACES ORIGINAL in `cus-edit.el'.
;; 1. Added items `Consider Unchanged' and `Ignore Unsaved Changes'.
;; 2. Hard-code `quit-window' as `Finish' action.
;; 3. Run hook `customp-buffer-create-hook' at end.
;;
(defun custom-buffer-create-internal (options &optional description)
  (message "Creating customization buffer...")
  (custom-mode)
  (if custom-buffer-verbose-help
      (progn
        (widget-insert "This is a customization buffer")
        (if description
            (widget-insert description))
        (widget-insert (format ".
%s show active fields; type RET or click mouse-1
on an active field to invoke its action.  Editing an option value
changes the text in the buffer; invoke the State button and
choose the Set operation to set the option value.
Invoke " (if custom-raised-buttons
             "`Raised' buttons"
             "Square brackets")))
        (widget-create 'info-link
                       :tag "Help"
                       :help-echo "Read the online help."
                       "(emacs)Easy Customization")
        (widget-insert " for more information.\n\n")
        (message "Creating customization buttons...")
        (widget-insert "Operate on everything in this buffer:\n "))
    (widget-insert " "))
  (widget-create 'push-button
                 :tag "Set for Current Session"
                 :help-echo "\
Make your editing in this buffer take effect for this session."
                 :action (lambda (widget &optional event)
                           (Custom-set)))
  (widget-insert " ")
  (widget-create 'push-button
                 :tag "Save for Future Sessions"
                 :help-echo "\
Make your editing in this buffer take effect for future Emacs sessions."
                 :action (lambda (widget &optional event)
                           (Custom-save)))
  (widget-insert "\n ")
  (widget-create 'push-button
                 :tag "Consider Unchanged"
                 :help-echo "\
Treat changed preferences as if they were unchanged, without saving them."
                 :action (lambda (widget &optional event)
                           (Custom-consider-unchanged)))
  (widget-insert " ")
  (widget-create 'push-button
                 :tag "Ignore Unsaved Changes"
                 :help-echo "\
Add to the `customize-customized-ignore' preferences, whose changes \
are ignored by `customize-customized'."
                 :action (lambda (widget &optional event)
                           (Custom-ignore-unsaved)))
  (widget-insert " ")
  (widget-create 'push-button
                 :tag "Set from External Changes"
                 :help-echo "\
Tell Customize that all preferences changed outside it are now set."
                 :action (lambda (widget &optional event)
                           (customize-update-all)
                           (message "Updating Customize to recognize external \
settings...done")))
  (if custom-reset-button-menu
      (progn
        (widget-insert " ")
        (widget-create 'push-button
                       :tag "Reset"
                       :help-echo "Show a menu with reset operations."
                       :mouse-down-action (lambda (&rest junk) t)
                       :action (lambda (widget &optional event)
                                 (custom-reset event))))
    (widget-insert "\n ")
    (widget-create 'push-button
                   :tag "Reset"
                   :help-echo "\
Reset all edited text in this buffer to reflect current values."
                   :action 'Custom-reset-current)
    (widget-insert " ")
    (widget-create 'push-button
                   :tag "Reset to Saved"
                   :help-echo "\
Reset all values in this buffer to their saved settings."
                   :action 'Custom-reset-saved)
    (widget-insert " ")
    (widget-create 'push-button
                   :tag "Reset to Standard"
                   :help-echo "\
Reset all values in buffer to standard settings, updating your custom file."
                   :action 'Custom-reset-standard))
  (if (not custom-buffer-verbose-help)
      (progn
        (widget-insert " ")
        (widget-create 'info-link
                       :tag "Help"
                       :help-echo "Read the online help."
                       "(emacs)Easy Customization")))
  (widget-insert "   ")
  (widget-create 'push-button
                 :tag "Finish"
                 :help-echo "Finish with this buffer"
                 :action (lambda (widget &optional event)
                           (quit-window)))
  (widget-insert "\n\n")
  (message "Creating customization items...")
  (buffer-disable-undo)
  (setq custom-options
        (if (= (length options) 1)
            (mapcar (lambda (entry)
                      (widget-create (nth 1 entry)
                                     :documentation-shown t
                                     :custom-state 'unknown
                                     :tag (custom-unlispify-tag-name
                                           (nth 0 entry))
                                     :value (nth 0 entry)))
                    options)
          (let ((count 0)
                (length (length options)))
            (mapcar (lambda (entry)
                      (prog2
                          (message "Creating customization items...%2d%%"
                                   (/ (* 100.0 count) length))
                          (widget-create (nth 1 entry)
                                         :tag (custom-unlispify-tag-name
                                               (nth 0 entry))
                                         :value (nth 0 entry))
                        (setq count (1+ count))
                        (unless (eq (preceding-char) ?\n)
                          (widget-insert "\n"))
                        (widget-insert "\n")))
                    options))))
  (unless (eq (preceding-char) ?\n)
    (widget-insert "\n"))
  (message "Creating customization items...done")
  (unless (eq custom-buffer-style 'tree)
    (mapc 'custom-magic-reset custom-options))
  (message "Creating customization setup...")
  (widget-setup)
  (buffer-enable-undo)
  (goto-char (point-min))
  (message "Creating customization buffer...done")
  (run-hooks 'customp-buffer-create-hook))



;; REPLACES ORIGINAL in `cus-edit.el'.
;; Fit frame expanding and collapsing tree nodes.
;;
(when (fboundp 'fit-frame-if-one-window)
  (defadvice custom-browse-visibility-action
    (after customize-toggle-tree-node-fit-frame activate)
    "Fit frame to buffer if only one window."
    (fit-frame-if-one-window)))



;; REPLACES ORIGINAL in `cus-edit.el'.
;; Fit frame afterward.
;;
;; NOTE: GNU Emacs bug (which will be fixed in next release) causes
;;       this not to work yet - the buffer isn't selected! This will
;;       work when the bug is fixed.
;;
(when (fboundp 'fit-frame-if-one-window)
  (defadvice customize-group-other-window (after customize-group-fit-frame activate)
    "Fit frame to buffer if only one window."
    (fit-frame-if-one-window)))

;;;###autoload
(defun customize-other-window ()
  "Select a customization buffer which you can use to set user options
in a different window.
User options are structured into \"groups\".
Initially the top-level group `Emacs' and its immediate subgroups
are shown; the contents of those subgroups are initially hidden."
  (interactive)
  (customize-group-other-window 'emacs))

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'cus-edit+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; cus-edit+.el ends here
