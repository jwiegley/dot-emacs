(provide 'ee-autoloads)

;;;### (autoloads (ee) "ee" "ee.el" (19285 24054))
;;; Generated autoloads from ee.el

(autoload 'ee "ee" "\
Enter top-level index of all available ee extensions.
Optional argument FILE specifies the file to examine;
the default is the top-level mode list.
In interactive use, a prefix argument directs this command
to read a root file name from the minibuffer.

\(fn &optional FILE)" t nil)

;;;***

;;;### (autoloads (ee-bbdb) "ee-bbdb" "ee-bbdb.el" (19285 24054))
;;; Generated autoloads from ee-bbdb.el

(autoload 'ee-bbdb "ee-bbdb" "\
Summary mode for BBDB.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-buffers) "ee-buffers" "ee-buffers.el" (19285
;;;;;;  24054))
;;; Generated autoloads from ee-buffers.el

(autoload 'ee-buffers "ee-buffers" "\
Display and manipulate Emacs buffers.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-commands) "ee-commands" "ee-commands.el" (19285
;;;;;;  24054))
;;; Generated autoloads from ee-commands.el

(autoload 'ee-commands "ee-commands" "\
Categorized menu of Emacs commands.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-customize) "ee-customize" "ee-customize.el"
;;;;;;  (19285 24054))
;;; Generated autoloads from ee-customize.el

(autoload 'ee-customize "ee-customize" "\
Browse Emacs customization groups.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-datafile ee-datafile-mode) "ee-datafile" "ee-datafile.el"
;;;;;;  (19285 24054))
;;; Generated autoloads from ee-datafile.el
 (add-to-list 'auto-mode-alist '("\\.ee\\'" . emacs-lisp-mode))

(autoload 'ee-datafile-mode "ee-datafile" "\
Datafile view mode.
The purpose of this function is to create the view buffer,
when user visits a file with -*- mode: ee-datafile -*-.

\(fn &optional ARG)" t nil)

(autoload 'ee-datafile "ee-datafile" "\
Display and edit data files.

\(fn &optional ARG FILE)" t nil)

;;;***

;;;### (autoloads (ee-dired) "ee-dired" "ee-dired.el" (19285 24054))
;;; Generated autoloads from ee-dired.el

(autoload 'ee-dired "ee-dired" "\
Categorized directory listings.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-dselect) "ee-dselect" "ee-dselect.el" (19285
;;;;;;  24054))
;;; Generated autoloads from ee-dselect.el

(autoload 'ee-dselect "ee-dselect" "\
Debian package handling frontend.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-edb) "ee-edb" "ee-edb.el" (19285 24054))
;;; Generated autoloads from ee-edb.el

(autoload 'ee-edb "ee-edb" "\
Summary mode for EDB.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-ell) "ee-ell" "ee-ell.el" (19285 24054))
;;; Generated autoloads from ee-ell.el

(autoload 'ee-ell "ee-ell" "\
Browse the categorized Emacs Lisp List.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-example) "ee-example" "ee-example.el" (19285
;;;;;;  24054))
;;; Generated autoloads from ee-example.el

(autoload 'ee-example "ee-example" "\
Accompanying example for demonstration of ee capabilities.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-fields) "ee-fields" "ee-fields.el" (19285 24054))
;;; Generated autoloads from ee-fields.el

(autoload 'ee-fields "ee-fields" "\
Display and edit fields of the current record.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-finder) "ee-finder" "ee-finder.el" (19285 24054))
;;; Generated autoloads from ee-finder.el

(autoload 'ee-finder "ee-finder" "\
Keyword-based Emacs code finder.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-gnus) "ee-gnus" "ee-gnus.el" (19285 24054))
;;; Generated autoloads from ee-gnus.el

(autoload 'ee-gnus "ee-gnus" "\
Summary and topic mode for Gnus.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-history-shell-command ee-history-extended-command
;;;;;;  ee-history-command) "ee-history" "ee-history.el" (19285 24054))
;;; Generated autoloads from ee-history.el

(autoload 'ee-history-command "ee-history" "\
Display list from Emacs variable `command-history'.

\(fn &optional ARG)" t nil)

(autoload 'ee-history-extended-command "ee-history" "\
Display list from Emacs variable `extended-command-history'.

\(fn &optional ARG)" t nil)

(autoload 'ee-history-shell-command "ee-history" "\
Display list from Emacs variable `shell-command-history'.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-imenu) "ee-imenu" "ee-imenu.el" (19285 24054))
;;; Generated autoloads from ee-imenu.el

(autoload 'ee-imenu "ee-imenu" "\
Categorized mode-specific buffer indexes.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-info) "ee-info" "ee-info.el" (19285 24054))
;;; Generated autoloads from ee-info.el

(autoload 'ee-info "ee-info" "\
Enter ee-info, the documentation browser.
Optional argument FILE specifies the file to examine;
the default is the top-level directory of Info.

In interactive use, a prefix argument directs this command
to read a file name from the minibuffer.

The search path for Info files is in the variable `Info-directory-list'.
The top-level Info directory is made by combining all the files named `dir'
in all the directories in that path.

\(fn &optional FILE)" t nil)

;;;***

;;;### (autoloads (ee-marks) "ee-marks" "ee-marks.el" (19285 24054))
;;; Generated autoloads from ee-marks.el

(autoload 'ee-marks "ee-marks" "\
Display and go to marked lines in the current Emacs buffer.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-menubar) "ee-menubar" "ee-menubar.el" (19285
;;;;;;  24054))
;;; Generated autoloads from ee-menubar.el

(autoload 'ee-menubar "ee-menubar" "\
Categorized access to Emacs menu-bar.

\(fn &optional ARG)" t nil)
 (defalias 'ee-tmm 'ee-menubar)

;;;***

;;;### (autoloads (ee-outline) "ee-outline" "ee-outline.el" (19285
;;;;;;  24053))
;;; Generated autoloads from ee-outline.el

(autoload 'ee-outline "ee-outline" "\
Manipulate outlines collected from outline-mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-processes) "ee-processes" "ee-processes.el"
;;;;;;  (19285 24053))
;;; Generated autoloads from ee-processes.el

(autoload 'ee-processes "ee-processes" "\
Display and manipulate Emacs processes.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-programs) "ee-programs" "ee-programs.el" (19285
;;;;;;  24053))
;;; Generated autoloads from ee-programs.el

(autoload 'ee-programs "ee-programs" "\
Categorized program menu.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-ps) "ee-ps" "ee-ps.el" (19285 24053))
;;; Generated autoloads from ee-ps.el

(autoload 'ee-ps "ee-ps" "\
Display CPU processes.

\(fn &optional ARG)" t nil)
 (fset 'ee-top 'ee-ps)

;;;***

;;;### (autoloads (ee-tags) "ee-tags" "ee-tags.el" (19285 24053))
;;; Generated autoloads from ee-tags.el

(autoload 'ee-tags "ee-tags" "\
Etags facility.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-textfile-apachelog ee-textfile-changelog) "ee-textfile"
;;;;;;  "ee-textfile.el" (19285 24053))
;;; Generated autoloads from ee-textfile.el

(autoload 'ee-textfile-changelog "ee-textfile" "\
Organize information from ChangeLog files.

\(fn &optional ARG)" t nil)

(autoload 'ee-textfile-apachelog "ee-textfile" "\
Organize information from Apache log files.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-variables) "ee-variables" "ee-variables.el"
;;;;;;  (19285 24053))
;;; Generated autoloads from ee-variables.el

(autoload 'ee-variables "ee-variables" "\
Categorized menu of Emacs variables.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-views) "ee-views" "ee-views.el" (19285 24053))
;;; Generated autoloads from ee-views.el

(autoload 'ee-views "ee-views" "\
Display, edit and switch views.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-windows ee-windows-add ee-windows-and-add-current)
;;;;;;  "ee-windows" "ee-windows.el" (19285 24053))
;;; Generated autoloads from ee-windows.el

(autoload 'ee-windows-and-add-current "ee-windows" "\
Not documented

\(fn &optional ARG)" t nil)

(autoload 'ee-windows-add "ee-windows" "\
Add current Emacs window configuration.

\(fn)" t nil)

(autoload 'ee-windows "ee-windows" "\
Display and switch Emacs window configurations.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("ee-xemacs.el") (19285 24989 160122))

;;;***

