;;; .loaddefs.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (customize-other-window customize-consider-all-faces-unchanged
;;;;;;  customize-consider-all-vars-unchanged customize-consider-all-unchanged
;;;;;;  Custom-consider-unchanged Custom-ignore-unsaved customize-set-auto-update-timer-period
;;;;;;  customize-toggle-outside-change-updates customize-update-all-faces
;;;;;;  customize-update-all-vars customize-update-all customize-customized
;;;;;;  customize-apropos-options-of-type) "cus-edit_2b" "cus-edit%2b/cus-edit_2b.el"
;;;;;;  (20051 14690))
;;; Generated autoloads from cus-edit%2b/cus-edit_2b.el

(autoload 'customize-apropos-options-of-type "cus-edit_2b" "\
Customize all loaded customizable options of type TYPE that match REGEXP.
With no prefix arg, each option is defined with `defcustom' type TYPE.
With a prefix arg, either each option is defined with `defcustom' type
 TYPE or its current value is compatible with TYPE.

If TYPE is nil (the default value) then all `defcustom' variables are
potential candidates.

\(fn TYPE REGEXP &optional ARG)" t nil)

(autoload 'customize-customized "cus-edit_2b" "\
Open Customize to check all preferences currently set but not saved.
This is useful in `kill-emacs-query-functions' to check changes you
have made (and possibly saving them) before exiting Emacs.

Changes to preferences listed in `customize-customized-ignore'
are normally ignored here.  However, with non-`nil' CHECK-ALL-P (prefix
argument), all changes are checked.

Changes to preferences that you have declared \"unchanged\" (using,
for example, `Consider Unchanged') are always ignored here.

\(fn &optional CHECK-ALL-P)" t nil)

(autoload 'customize-update-all "cus-edit_2b" "\
Tell Customize that all preferences changed outside it are now set.
This means all changes to all preferences (faces and user variables).
This is suitable to be run automatically as a hook or with a timer,
to keep Customize synched with Emacs changes.
When interactive, call `custom-redraw' on each Customize widget.

\(fn)" t nil)

(autoload 'customize-update-all-vars "cus-edit_2b" "\
Tell customize that all variables changed outside it are now set.
This is suitable to be run automatically as a hook or with a timer,
to keep Customize synched with Emacs changes.
When interactive, call `custom-redraw' on each Customize widget.

\(fn)" t nil)

(autoload 'customize-update-all-faces "cus-edit_2b" "\
Tell Customize that all faces changed outside it are now set.
When interactive, call `custom-redraw' on each Customize widget.
This is suitable to be run automatically as a hook or with a timer,
to keep Customize synched with Emacs changes.

\(fn)" t nil)

(autoload 'customize-toggle-outside-change-updates "cus-edit_2b" "\
Turn on or off automatically telling Customize of outside changes.
When on, Customize is told about any preference changes made outside
of Customize, so that it considers them to have been made inside.
With prefix argument, turn on if ARG > 0; else turn off.

\(fn &optional ARG)" t nil)

(autoload 'customize-set-auto-update-timer-period "cus-edit_2b" "\
Set wait until automatically tell Customize of outside changes to SECS
seconds after Emacs is idle.  Whenever Emacs is idle for this many
seconds it will check for user preferences that have been changed
outside of Customize.  All user preference (variable and face) changes
are reported to Customize, so that it recognizes them as if they had
been made within Customize itself.

To turn on or off automatically telling Customize of outside changes,
use `\\[toggle-customize-update-changes].

\(fn SECS)" t nil)

(autoload 'Custom-ignore-unsaved "cus-edit_2b" "\
Ignore all currently customized but unsaved preferences.
The preferences that are currently customized but not saved are added
to the list of preferences that `customize-customized' will ignore
when checking for unsaved changes.

NOTE: This list of preferences that `customize-customized' ignores is
      updated here and saved to your customizations file.  To undo
      this change, use `\\[Custom-reset-standard]' on variable
      `customize-customized-ignore'.

\(fn)" t nil)

(autoload 'Custom-consider-unchanged "cus-edit_2b" "\
Consider all preferences here as being unchanged now.
This does not save the current values; it just considers them to be
unchanged values.  If no further changes are made to any of these
preferences, then after doing this, `customize-customize' will not
display any of these preferences, since they were considered
unchanged.

\(fn)" t nil)

(autoload 'customize-consider-all-unchanged "cus-edit_2b" "\
Consider all customizable preferences as saved, without saving them.

\(fn)" t nil)

(autoload 'customize-consider-all-vars-unchanged "cus-edit_2b" "\
Consider all customizable variables as saved, without saving them.

\(fn)" t nil)

(autoload 'customize-consider-all-faces-unchanged "cus-edit_2b" "\
Consider all customizable faces as saved, without saving them.

\(fn)" t nil)

(autoload 'customize-other-window "cus-edit_2b" "\
Select a customization buffer which you can use to set user options
in a different window.
User options are structured into \"groups\".
Initially the top-level group `Emacs' and its immediate subgroups
are shown; the contents of those subgroups are initially hidden.

\(fn)" t nil)

;;;***

;;;### (autoloads nil nil ("el-get/el-get-install.el" "el-get/el-get.el"
;;;;;;  "package/package.el" "yaoddmuse/yaoddmuse.el") (20051 14690
;;;;;;  697364))

;;;***

(provide '.loaddefs)
;; Local Variables:
;; version-control: never
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; .loaddefs.el ends here
