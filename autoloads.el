;;; -*-emacs-lisp-*-
;;; autoloads.in --- define autoloads for a lisp directory

(require 'cl)

(defun generate-autoloads ()
  (interactive)
  (require 'autoload)
  (setq generated-autoload-file (car command-line-args-left))
  (setq command-line-args-left (cdr command-line-args-left))
  (batch-update-autoloads))

;;; Load in customization dependencies:

(unless (fboundp 'package-provide)
  (defalias 'package-provide 'ignore))

;;; Manually create autoloads for some packages

(autoload 'ange-ftp-get-passwd "ange-ftp")

(autoload 'auto-capitalize-mode "auto-capitalize" nil t)
(autoload 'turn-on-auto-capitalize-mode "auto-capitalize" nil t)
(autoload 'enable-auto-capitalize-mode "auto-capitalize" nil t)

(autoload 'browse-kill-ring "browse-kill-ring")

(autoload 'mc-install-read-mode "mailcrypt")
(autoload 'mc-install-write-mode "mailcrypt")

(defalias 'define-minor-mode 'easy-mmode-define-minor-mode)

(autoload 'highlight-line "highlight-line" nil t)

(autoload 'inform-mode "inform-mode" "Inform editing mode." t)
(autoload 'inform-maybe-mode "inform-mode" "Inform/C header editing mode.")

(autoload 'insert-patterned "repeat-insert" nil t)
(autoload 'insert-patterned-2 "repeat-insert" nil t)
(autoload 'insert-patterned-3 "repeat-insert" nil t)
(autoload 'insert-patterned-4 "repeat-insert" nil t)

(autoload 'move-chop-up "chop" nil t)
(autoload 'move-chop-down "chop" nil t)

(autoload 'debian-changelog-mode "debian-changelog" nil t)
(autoload 'deb-view "deb-view" nil t)

(autoload 'dictionary "dictionary" nil t)
(autoload 'dictionary-lookup-definition "dictionary" nil t)

(autoload 'dismal-mode "dismal" nil t)

(autoload 'dot-mode "dot-mode" nil t)
(autoload 'dot-mode-on "dot-mode" nil t)

(autoload 'edit-env "edit-env" nil t)

(autoload 'remem-toggle "remem" nil t)

(autoload 'balance-mode "balance" nil t)

(autoload 'css-mode "css-mode" nil t)

(autoload 'fm-start "fm" nil t)

(autoload 'glimpse-list-hits "glimpse" nil t)
(autoload 'glimpse-dired "glimpse" nil t)
(autoload 'glimpse-find-file "glimpse" nil t)
(autoload 'glimpse "glimpse" nil t)
(autoload 'glimpse-in-files "glimpse" nil t)

(autoload 'ics "ics" nil t)

(autoload 'thumbs-show-all-from-dir "thumbs" nil t)

(autoload 'unscroll "unscroll")

(autoload 'uptimes-float-time "uptimes")

(autoload 'sawmill-mode "sawmill")

(autoload 'session-save-session "session")

(autoload 'visit-url "visit-url")

(autoload 'vkill "vkill" nil t)
(autoload 'list-unix-processes "vkill" nil t)

(autoload 'wcount-mode "wcount" nil t)

(autoload 'outdent-mode "outdent" nil t)

(autoload 'manued-minor-mode "manued" nil t)

(autoload 'refill-mode "refill" nil t)

(autoload 'tnt-open "tnt" nil t)

(autoload 'make-password "make-password")

(autoload 'fancy-schedule-display-desk-calendar "cal-desk-calendar")

(autoload 'debian-bug "debian-bug" nil t)
(autoload 'report-debian-bug "debian-bug" nil t)

(autoload 'thing-at-point-url-regexp "thingatpt")

(autoload 'w3m-browse-url "w3m" nil t)
(autoload 'w3m-find-file "w3m" nil t)
(autoload 'w3m-region "w3m" nil t)
(autoload 'w3m-search "w3m" nil t)
(autoload 'w3m-download "w3m" nil t)
(autoload 'w3m "w3m" nil t)

;;; Generated autoloads follow (made by autoload.el).

;;;### (autoloads (all) "all" "site-lisp/all.el" (13250 5268))
;;; Generated autoloads from site-lisp/all.el

(autoload (quote all) "all" "\
Show all lines in the current buffer containing a match for REGEXP.

If a match spreads across multiple lines, all those lines are shown.

Each line is displayed with NLINES lines before and after, or -NLINES
before if NLINES is negative.
NLINES defaults to `list-matching-lines-default-context-lines'.
Interactively it is the prefix arg.

The lines are shown in a buffer named `*All*'.
Any changes made in that buffer will be propagated to this buffer." t nil)

;;;***

;;;### (autoloads (ascii-off ascii-on ascii-display ascii-customize)
;;;;;;  "ascii" "site-lisp/ascii.el" (18084 9489))
;;; Generated autoloads from site-lisp/ascii.el

(autoload (quote ascii-customize) "ascii" "\
Customize ASCII options." t nil)

(autoload (quote ascii-display) "ascii" "\
Toggle ASCII code display.

If ARG is null, toggle ASCII code display.
If ARG is a number and is greater than zero, turn on display; otherwise, turn
off display.
If ARG is anything else, turn on display." t nil)

(autoload (quote ascii-on) "ascii" "\
Turn on ASCII code display." t nil)

(autoload (quote ascii-off) "ascii" "\
Turn off ASCII code display." t nil)

;;;***

;;;### (autoloads (check-mail) "check-mail" "check-mail.el" (18205
;;;;;;  36835))
;;; Generated autoloads from check-mail.el

(autoload (quote check-mail) "check-mail" "\
Check all of the boxes listed in `mail-boxes-to-check' for new mail." t nil)

;;;***

;;;### (autoloads (chop-move-down chop-move-up) "chop" "site-lisp/chop.el"
;;;;;;  (18084 9489))
;;; Generated autoloads from site-lisp/chop.el

(autoload (quote chop-move-up) "chop" "\
Move by one 'chop' into the upper half of the remaining space." t nil)

(autoload (quote chop-move-down) "chop" "\
Move by one 'chop' into the lower half of the remaining space." t nil)

;;;***

;;;### (autoloads (turn-on-cldoc-mode cldoc-mode cldoc-minor-mode-string
;;;;;;  cldoc-mode) "cldoc" "site-lisp/cldoc.el" (18195 62488))
;;; Generated autoloads from site-lisp/cldoc.el

(defvar cldoc-mode nil "\
*If non-nil, show the defined parameters for the elisp function near point.

For the emacs lisp function at the beginning of the sexp which point is
within, show the defined parameters for the function in the echo area.
This information is extracted directly from the function or macro if it is
in pure lisp.  If the emacs function is a subr, the parameters are obtained
from the documentation string if possible.

If point is over a documented variable, print that variable's docstring
instead.

This variable is buffer-local.")

(defvar cldoc-minor-mode-string " Cldoc" "\
*String to display in mode line when Cldoc Mode is enabled.")

(cond ((fboundp (quote add-minor-mode)) (add-minor-mode (quote cldoc-mode) (quote cldoc-minor-mode-string))) ((assq (quote cldoc-mode) (default-value (quote minor-mode-alist)))) (t (setq-default minor-mode-alist (append (default-value (quote minor-mode-alist)) (quote ((cldoc-mode cldoc-minor-mode-string)))))))

(autoload (quote cldoc-mode) "cldoc" "\
*Enable or disable cldoc mode.
See documentation for the variable of the same name for more details.

If called interactively with no prefix argument, toggle current condition
of the mode.
If called with a positive or negative prefix argument, enable or disable
the mode, respectively." t nil)

(autoload (quote turn-on-cldoc-mode) "cldoc" "\
Unequivocally turn on cldoc-mode (see variable documentation)." t nil)

;;;***

;;;### (autoloads (diminished-modes diminish-undo diminish) "diminish"
;;;;;;  "site-lisp/diminish.el" (18084 9489))
;;; Generated autoloads from site-lisp/diminish.el

(autoload (quote diminish) "diminish" "\
Diminish mode-line display of minor mode MODE to TO-WHAT (default \"\").

Interactively, enter (with completion) the name of any minor mode, followed
on the next line by what you want it diminished to (default empty string).
The response to neither prompt should be quoted.  However, in Lisp code,
both args must be quoted, the first as a symbol, the second as a string,
as in (diminish 'jiggle-mode \" Jgl\").

The mode-line displays of minor modes usually begin with a space, so
the modes' names appear as separate words on the mode line.  However, if
you're having problems with a cramped mode line, you may choose to use single
letters for some modes, without leading spaces.  Capitalizing them works
best; if you then diminish some mode to \"X\" but have abbrev-mode enabled as
well, you'll get a display like \"AbbrevX\".  This function prepends a space
to TO-WHAT if it's > 1 char long & doesn't already begin with a space." t nil)

(autoload (quote diminish-undo) "diminish" "\
Restore mode-line display of diminished mode MODE to its minor-mode value.
Do nothing if the arg is a minor mode that hasn't been diminished.

Interactively, enter (with completion) the name of any diminished mode (a
mode that was formerly a minor mode on which you invoked M-x diminish).
To restore all diminished modes to minor status, answer `diminished-modes'.
The response to the prompt shouldn't be quoted.  However, in Lisp code,
the arg must be quoted as a symbol, as in (diminish-undo 'diminished-modes)." t nil)

(autoload (quote diminished-modes) "diminish" "\
Echo all active diminished or minor modes as if they were minor.
The display goes in the echo area; if it's too long even for that,
you can see the whole thing in the *Messages* buffer.
This doesn't change the status of any modes; it just lets you see
what diminished modes would be on the mode-line if they were still minor." t nil)

;;;***

;;;### (autoloads (dired-tar-pack-unpack) "dired-tar" "site-lisp/dired-tar.el"
;;;;;;  (18084 9489))
;;; Generated autoloads from site-lisp/dired-tar.el

(autoload (quote dired-tar-pack-unpack) "dired-tar" "\
Create or unpack a tar archive for the file on the current line.

If the file on the current line is a directory, make a gzipped tar
file out of its contents.

If the file on the current line is a tar archive, unpack it.  If the
archive appears to be gzipped or compressed, expand it first.  With a
prefix argument, just list the tar archive's contents, and don't
unpack it.  The file's name must end in \".tar\", \".tar.gz\", or
\".tar.Z\" or else this command will assume it's not a tar file." t nil)

(add-hook (quote dired-mode-hook) (function (lambda nil (define-key dired-mode-map "T" (quote dired-tar-pack-unpack)))))

;;;***

;;;### (autoloads (dvc-about) "dvc-about" "site-lisp/dvc-snapshot/lisp/dvc-about.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-about.el

(autoload (quote dvc-about) "dvc-about" "\
Displays a welcome message." t nil)

;;;***

;;;### (autoloads (dvc-bookmarks) "dvc-bookmarks" "site-lisp/dvc-snapshot/lisp/dvc-bookmarks.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-bookmarks.el

(autoload (quote dvc-bookmarks) "dvc-bookmarks" "\
Display the *dvc-bookmarks* buffer.
With prefix argument ARG, reload the bookmarks file from disk." t nil)

;;;***

;;;### (autoloads (dvc-submit-bug-report) "dvc-bug" "site-lisp/dvc-snapshot/lisp/dvc-bug.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-bug.el

(autoload (quote dvc-submit-bug-report) "dvc-bug" "\
Submit a bug report, with pertinent information to the dvc-dev list." t nil)

;;;***

;;;### (autoloads (dvc-current-file-list) "dvc-core" "site-lisp/dvc-snapshot/lisp/dvc-core.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-core.el

(autoload (quote dvc-current-file-list) "dvc-core" "\
Return a list of currently active files.

The following sources are tried (in that order) and used if they are non nil:

* `dvc-buffer-marked-file-list'
* `dvc-current-file-list'
* When in dired mode, return the marked files or the file where point is
* SELECTION-MODE provides a way to select the file list that should be returned.
  - When SELECTION-MODE is 'nil-if-none-marked, return nil, if no files are explicitely marked.
  - When SELECTION-MODE is 'all-if-none-marked, return all files from that buffer. That is not yet implemented. Just returns nil at the moment..
* Otherwise call the function `dvc-get-file-info-at-point'." nil nil)

;;;***

;;;### (autoloads (dvc-dvc-file-diff dvc-file-ediff-revisions dvc-file-ediff)
;;;;;;  "dvc-diff" "site-lisp/dvc-snapshot/lisp/dvc-diff.el" (18148
;;;;;;  40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-diff.el

(autoload (quote dvc-file-ediff) "dvc-diff" "\
Run ediff of FILE (defaut current buffer file) against last revision." t nil)

(autoload (quote dvc-file-ediff-revisions) "dvc-diff" "\
View changes in FILE between BASE and MODIFIED using ediff." nil nil)

(autoload (quote dvc-dvc-file-diff) "dvc-diff" "\
View changes in FILE between BASE (default last-revision) and
MODIFIED (default workspace version)." nil nil)

;;;***

;;;### (autoloads (dvc-insinuate-gnus) "dvc-gnus" "site-lisp/dvc-snapshot/lisp/dvc-gnus.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-gnus.el

(autoload (quote dvc-insinuate-gnus) "dvc-gnus" "\
Insinuate Gnus for each registered DVC back-end.

Runs (<backend>-insinuate-gnus) for each registered back-end having
this function.

Additionally the following key binding is defined for the gnus summary mode map:
K t l `dvc-gnus-article-extract-log-message'
K t v `dvc-gnus-article-view-patch'
K t m `dvc-gnus-article-view-missing'
K t a `dvc-gnus-article-apply-patch'" t nil)

;;;***

;;;### (autoloads (dvc-add-log-entry dvc-dvc-log-edit dvc-log-edit-mode)
;;;;;;  "dvc-log" "site-lisp/dvc-snapshot/lisp/dvc-log.el" (18148
;;;;;;  40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-log.el

(autoload (quote dvc-log-edit-mode) "dvc-log" "\
Major Mode to edit DVC log messages.
Commands:
\\{dvc-log-edit-mode-map}
" t nil)

(autoload (quote dvc-dvc-log-edit) "dvc-log" "\
Edit the log file before a commit.

If  invoked from  a buffer  containing marked  files,  only those
files  will be  taken  into  account when  you  will commit  with
<dvc-log-edit-mode-map>[dvc-log-edit-done] (dvc-log-edit-done)." t nil)

(autoload (quote dvc-add-log-entry) "dvc-log" "\
Add new DVC log ChangeLog style entry." t nil)

;;;***

;;;### (autoloads (dvc-apply) "dvc-register" "site-lisp/dvc-snapshot/lisp/dvc-register.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-register.el

(autoload (quote dvc-apply) "dvc-register" "\
Apply ARGS to the `dvc-current-active-dvc' concated with POSTFIX." nil nil)

;;;***

;;;### (autoloads (dvc-tips-popup) "dvc-tips" "site-lisp/dvc-snapshot/lisp/dvc-tips.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-tips.el

(autoload (quote dvc-tips-popup) "dvc-tips" "\
Pop up a buffer with a tip message.

Don't use this function from Xtla. Use `dvc-tips-popup-maybe'
instead." t nil)

;;;***

;;;### (autoloads (dvc-prefix-key) "dvc-ui" "site-lisp/dvc-snapshot/lisp/dvc-ui.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-ui.el

(eval-and-compile (require (quote easymenu)))

(defvar dvc-key-help 63)

(defvar dvc-key-diff 61)

(defvar dvc-key-status 115)

(defvar dvc-key-show-bookmark 98)

(defvar dvc-key-file-diff 100)

(defvar dvc-key-tree-lint 108)

(defvar dvc-key-logs 76)

(defvar dvc-key-ediff 101)

(defvar dvc-key-log-entry 97)

(defvar dvc-key-inventory 105)

(defvar dvc-key-kill-ring-prefix 119)

(defvar dvc-key-commit 99)

(defvar dvc-key-update 117)

(defvar dvc-key-missing 109)

(defvar dvc-key-buffer-prefix 66)

(defvar dvc-key-file-prefix 102)

(defun dvc-key-group (prefix &rest keys) (apply (quote vector) prefix keys))

(defun dvc-prefix-file (&rest keys) (dvc-key-group dvc-key-file-prefix keys))

(defun dvc-prefix-kill-ring (&rest keys) (dvc-key-group dvc-key-kill-ring-prefix keys))

(defun dvc-prefix-buffer (&rest keys) (dvc-key-group dvc-key-buffer-prefix keys))

(defvar dvc-keyvec-help (vector dvc-key-help))

(defvar dvc-keyvec-ediff (vector dvc-key-ediff))

(defvar dvc-keyvec-tree-lint (vector dvc-key-tree-lint))

(defvar dvc-keyvec-logs (vector dvc-key-logs))

(defvar dvc-keyvec-log-entry (vector dvc-key-log-entry))

(defvar dvc-keyvec-diff (vector dvc-key-diff))

(defvar dvc-keyvec-status (vector dvc-key-status))

(defvar dvc-keyvec-file-diff (vector dvc-key-file-diff))

(defvar dvc-keyvec-file-diff (vector dvc-key-file-diff))

(defvar dvc-keyvec-commit (vector dvc-key-commit))

(defvar dvc-keyvec-update (vector dvc-key-update))

(defvar dvc-keyvec-missing (vector dvc-key-missing))

(defvar dvc-keyvec-inventory (vector dvc-key-inventory))

(defvar dvc-keyvec-show-bookmark (vector dvc-key-show-bookmark))

(defvar dvc-global-keymap (let ((map (make-sparse-keymap))) (define-key map [85] (quote tla-undo)) (define-key map [82] (quote tla-redo)) (define-key map [112] (quote dvc-submit-patch)) (define-key map dvc-keyvec-log-entry (quote dvc-add-log-entry)) (define-key map [65] (quote tla-archives)) (define-key map dvc-keyvec-file-diff (quote dvc-file-diff)) (define-key map dvc-keyvec-ediff (quote dvc-file-ediff)) (define-key map [111] (quote tla-file-view-original)) (define-key map dvc-keyvec-diff (quote dvc-diff)) (define-key map dvc-keyvec-status (quote dvc-status)) (define-key map dvc-keyvec-commit (quote dvc-log-edit)) (define-key map [116] (quote tla-tag-insert)) (define-key map dvc-keyvec-inventory (quote dvc-inventory)) (define-key map [114] (quote tla-tree-revisions)) (define-key map dvc-keyvec-logs (quote dvc-log)) (define-key map [108] (quote dvc-changelog)) (define-key map [(meta 108)] (quote tla-tree-lint)) (define-key map dvc-keyvec-update (quote dvc-update)) (define-key map [109] (quote dvc-missing)) (define-key map dvc-keyvec-show-bookmark (quote tla-bookmarks)) (define-key map dvc-keyvec-help (quote tla-help)) (define-key map (dvc-prefix-file 97) (quote dvc-add-files)) (define-key map (dvc-prefix-file 68) (quote dvc-remove-files)) (define-key map (dvc-prefix-file 82) (quote dvc-revert-files)) (define-key map (dvc-prefix-file 77) (quote dvc-rename)) (define-key map (dvc-prefix-file 88) (quote dvc-purge-files)) (define-key map (dvc-prefix-buffer dvc-key-diff) (quote tla-changes-goto)) (define-key map (dvc-prefix-buffer dvc-key-status) (quote baz-status-goto)) (define-key map (dvc-prefix-buffer dvc-key-inventory) (quote tla-inventory-goto)) (define-key map (dvc-prefix-buffer dvc-key-tree-lint) (quote tla-tree-lint-goto)) (define-key map (dvc-prefix-buffer 114) (quote tla-tree-revisions-goto)) (define-key map (dvc-prefix-kill-ring 97) (quote tla-save-archive-to-kill-ring)) (define-key map (dvc-prefix-kill-ring 118) (quote tla-save-version-to-kill-ring)) (define-key map (dvc-prefix-kill-ring 114) (quote tla-save-revision-to-kill-ring)) map) "\
Global keymap used by DVC.")

(defvar dvc-prefix-key [(control x) 86] "\
Prefix key for the DVC commands in the global keymap.")

(global-set-key dvc-prefix-key dvc-global-keymap)

(define-key ctl-x-4-map [84] (quote dvc-add-log-entry))

(easy-menu-add-item (or (dvc-do-in-gnu-emacs menu-bar-tools-menu) nil) (or (dvc-do-in-xemacs (quote ("Tools"))) nil) (quote ("DVC" ["Browse Archives" tla-archives t] ["Show Bookmarks" tla-bookmarks t] ["Start New Project" tla-start-project t] "---" "Tree Commands:" ["View Diff" dvc-diff t] ["View Status" dvc-status t] ["View Inventory" tla-inventory t] ["View Tree Lint" tla-tree-lint t] ["Show Tree Revisions" tla-tree-revisions t] ["Edit Arch Log" dvc-log-edit t] "---" "File Commands:" ["Insert Arch Tag" tla-tag-insert t] ["Add Log Entry" dvc-add-log-entry t] ["View File Diff" tla-file-diff t] ["View File Ediff" tla-file-ediff t] ["View Original" tla-file-view-original t] ["View Conflicts" tla-view-conflicts t] "---" ("Goto Buffer" ["View Changes" tla-changes-goto t] ["View Status" baz-status-goto t] ["View Inventory" tla-inventory-goto t] ["View Tree Lint" tla-tree-lint-goto t] ["Show Tree Revisions" tla-tree-revisions-goto t]) ("Quick Configuration" ["Three Way Merge" tla-toggle-three-way-merge :style toggle :selected tla-three-way-merge] ["Show Ancestor in Conflicts" tla-toggle-show-ancestor :style toggle :selected tla-show-ancestor] ["Non Recursive Inventory" tla-toggle-non-recursive-inventory :style toggle :selected tla-non-recursive-inventory] ["Use --skip-present" tla-toggle-use-skip-present-option :style toggle :selected tla-use-skip-present-option]))) "PCL-CVS")

;;;***

;;;### (autoloads (dvc-ignore-file-extensions-in-dir dvc-ignore-file-extensions
;;;;;;  dvc-log-edit dvc-tree-root dvc-command-version dvc-log dvc-status
;;;;;;  define-dvc-unified-command dvc-remove-files dvc-revert-files
;;;;;;  dvc-add-files) "dvc-unified" "site-lisp/dvc-snapshot/lisp/dvc-unified.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-unified.el

(autoload (quote dvc-add-files) "dvc-unified" "\
Add FILES to the currently active dvc. FILES is a list of
strings including path from root; interactive defaults
to (dvc-current-file-list)." t nil)

(autoload (quote dvc-revert-files) "dvc-unified" "\
Revert FILES for the currently active dvc." t nil)

(autoload (quote dvc-remove-files) "dvc-unified" "\
Remove FILES for the currently active dvc." t nil)

(autoload (quote define-dvc-unified-command) "dvc-unified" nil nil (quote macro))

(define-dvc-unified-command dvc-diff (&optional against path dont-switch base-rev) "Display the changes from BASE-REV to AGAINST.\nBASE-REV (a revision-id) defaults to base revision of current\ntree; AGAINST (a revision-id) defaults to current tree." (interactive (list nil nil current-prefix-arg)))

(define-dvc-unified-command dvc-delta (&optional base modified dont-switch) "Display from revision BASE to MODIFIED.\n\nBASE and MODIFIED must be revision ID.\n\nIf DONT-SWITCH is nil, switch to the newly created buffer.")

(define-dvc-unified-command dvc-file-diff (file &optional base modified dont-switch) "Display the changes in FILE (default current buffer file) for\nthe actual dvc." (interactive (list buffer-file-name)))

(autoload (quote dvc-status) "dvc-unified" "\
Display the status in optional PATH tree." t nil)

(autoload (quote dvc-log) "dvc-unified" "\
Display the log for PATH (default entire tree), LAST-N
entries (default `dvc-log-last-n'; all if nil)." t nil)

(define-dvc-unified-command dvc-changelog (&optional arg) "Display the changelog in this tree for the actual dvc." (interactive))

(define-dvc-unified-command dvc-add (file) "Adds FILE to the repository." (interactive))

(autoload (quote dvc-command-version) "dvc-unified" "\
Returns and/or shows the version identity string of backend command." t nil)

(autoload (quote dvc-tree-root) "dvc-unified" "\
Get the tree root for PATH or the current `default-directory'.

When called interactively, print a message including the tree root and
the current active back-end." t nil)

(autoload (quote dvc-log-edit) "dvc-unified" "\
Edit the log before commiting. Optional user prefix puts log
edit buffer in a separate frame." t nil)

(define-dvc-unified-command dvc-log-edit-done nil "Commit and close the log buffer." (interactive))

(define-dvc-unified-command dvc-edit-ignore-files nil "Edit the ignored file list." (interactive))

(define-dvc-unified-command dvc-ignore-files (file-list) "Ignore the marked files." (interactive (list (dvc-current-file-list))))

(autoload (quote dvc-ignore-file-extensions) "dvc-unified" "\
Ignore the file extensions of the marked files, in all
directories of the workspace." t nil)

(autoload (quote dvc-ignore-file-extensions-in-dir) "dvc-unified" "\
Ignore the file extensions of the marked files, only in the
directories containing the files, and recursively below them." t nil)

(define-dvc-unified-command dvc-missing (&optional other) "Show the missing changesets for this working copy in regard to other." (interactive))

(define-dvc-unified-command dvc-inventory nil "Show the inventory for this working copy." (interactive))

(define-dvc-unified-command dvc-save-diff (file) "Store the diff from the working copy against the repository in a file." (interactive (list (read-file-name "Save the diff to: "))))

(define-dvc-unified-command dvc-update nil "Update this working copy." (interactive))

(define-dvc-unified-command dvc-pull nil "Pull changes from the remote source to the working copy or\nlocal database, as appropriate for the current back-end." (interactive))

(define-dvc-unified-command dvc-merge (&optional other) "Merge with other" (interactive))

(define-dvc-unified-command dvc-submit-patch nil "Submit a patch for the current project under DVC control." (interactive))

(define-dvc-unified-command dvc-send-commit-notification nil "Send a commit notification for the changeset at point." (interactive))

;;;***

;;;### (autoloads (dvc-reload dvc-trace) "dvc-utils" "site-lisp/dvc-snapshot/lisp/dvc-utils.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/dvc-utils.el

(defmacro dvc-do-in-gnu-emacs (&rest body) "\
Execute BODY if in GNU/Emacs." (unless (featurep (quote xemacs)) (\` (progn (\,@ body)))))

(defmacro dvc-do-in-xemacs (&rest body) "\
Execute BODY if in XEmacs." (when (featurep (quote xemacs)) (\` (progn (\,@ body)))))

(autoload (quote dvc-trace) "dvc-utils" "\
Display the trace message MSG.
Same as `message' if `dvc-debug' is non-nil.
Does nothing otherwise.  Please use it for your debug messages." nil nil)

(autoload (quote dvc-reload) "dvc-utils" "\
Reload DVC (usually for debugging purpose).

With prefix arg, prompts for the DIRECTORY in which DVC should be
loaded.  Useful to switch from one branch to the other.

If a Makefile is present in the directory where DVC is to be loaded,
run \"make\"." t nil)

;;;***

;;;### (autoloads (edit-variable) "edit-var" "site-lisp/edit-var.el"
;;;;;;  (18084 9491))
;;; Generated autoloads from site-lisp/edit-var.el

(autoload (quote edit-variable) "edit-var" "\
Edit the value of VARIABLE." t nil)

;;;***

;;;### (autoloads (epa-sign-keys epa-insert-keys epa-export-keys
;;;;;;  epa-import-armor-in-region epa-import-keys-region epa-import-keys
;;;;;;  epa-delete-keys epa-encrypt-region epa-sign-region epa-verify-cleartext-in-region
;;;;;;  epa-verify-region epa-decrypt-armor-in-region epa-decrypt-region
;;;;;;  epa-encrypt-file epa-sign-file epa-verify-file epa-decrypt-file
;;;;;;  epa-select-keys epa-list-secret-keys epa-list-keys) "epa"
;;;;;;  "site-lisp/epg/epa.el" (18092 2960))
;;; Generated autoloads from site-lisp/epg/epa.el

(autoload (quote epa-list-keys) "epa" "\
List all keys matched with NAME from the public keyring." t nil)

(autoload (quote epa-list-secret-keys) "epa" "\
List all keys matched with NAME from the private keyring." t nil)

(autoload (quote epa-select-keys) "epa" "\
Display a user's keyring and ask him to select keys.
CONTEXT is an epg-context.
PROMPT is a string to prompt with.
NAMES is a list of strings to be matched with keys.  If it is nil, all
the keys are listed.
If SECRET is non-nil, list secret keys instead of public keys." nil nil)

(autoload (quote epa-decrypt-file) "epa" "\
Decrypt FILE." t nil)

(autoload (quote epa-verify-file) "epa" "\
Verify FILE." t nil)

(autoload (quote epa-sign-file) "epa" "\
Sign FILE by SIGNERS keys selected." t nil)

(autoload (quote epa-encrypt-file) "epa" "\
Encrypt FILE for RECIPIENTS." t nil)

(autoload (quote epa-decrypt-region) "epa" "\
Decrypt the current region between START and END.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-decrypt-armor-in-region) "epa" "\
Decrypt OpenPGP armors in the current region between START and END.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-verify-region) "epa" "\
Verify the current region between START and END.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-verify-cleartext-in-region) "epa" "\
Verify OpenPGP cleartext signed messages in the current region
between START and END.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-sign-region) "epa" "\
Sign the current region between START and END by SIGNERS keys selected.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-encrypt-region) "epa" "\
Encrypt the current region between START and END for RECIPIENTS.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-delete-keys) "epa" "\
Delete selected KEYS.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-import-keys) "epa" "\
Import keys from FILE.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-import-keys-region) "epa" "\
Import keys from the region.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-import-armor-in-region) "epa" "\
Import keys in the OpenPGP armor format in the current region
between START and END.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-export-keys) "epa" "\
Export selected KEYS to FILE.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-insert-keys) "epa" "\
Insert selected KEYS after the point.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-sign-keys) "epa" "\
Sign selected KEYS.
If a prefix-arg is specified, the signature is marked as non exportable.

Don't use this command in Lisp programs!" t nil)

;;;***

;;;### (autoloads (epa-file-disable epa-file-enable) "epa-file" "site-lisp/epg/epa-file.el"
;;;;;;  (18076 8990))
;;; Generated autoloads from site-lisp/epg/epa-file.el

(put (quote epa-file-encrypt-to) (quote safe-local-variable) (lambda (val) (or (stringp val) (and (listp val) (catch (quote safe) (mapc (lambda (elt) (unless (stringp elt) (throw (quote safe) nil))) val) t)))))

(put (quote epa-file-encrypt-to) (quote permanent-local) t)

(autoload (quote epa-file-enable) "epa-file" nil t nil)

(autoload (quote epa-file-disable) "epa-file" nil t nil)

;;;***

;;;### (autoloads (epa-mail-import-keys epa-mail-encrypt epa-mail-sign
;;;;;;  epa-mail-verify epa-mail-decrypt) "epa-mail" "site-lisp/epg/epa-mail.el"
;;;;;;  (17903 32178))
;;; Generated autoloads from site-lisp/epg/epa-mail.el

(autoload (quote epa-mail-decrypt) "epa-mail" "\
Decrypt OpenPGP armors in the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-mail-verify) "epa-mail" "\
Verify OpenPGP cleartext signed messages in the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-mail-sign) "epa-mail" "\
Sign the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-mail-encrypt) "epa-mail" "\
Encrypt the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!" t nil)

(autoload (quote epa-mail-import-keys) "epa-mail" "\
Import keys in the OpenPGP armor format in the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!" t nil)

;;;***

;;;### (autoloads (epg-generate-key-from-string epg-generate-key-from-file
;;;;;;  epg-start-generate-key epg-sign-keys epg-start-sign-keys
;;;;;;  epg-delete-keys epg-start-delete-keys epg-receive-keys epg-start-receive-keys
;;;;;;  epg-import-keys-from-string epg-import-keys-from-file epg-start-import-keys
;;;;;;  epg-export-keys-to-string epg-export-keys-to-file epg-start-export-keys
;;;;;;  epg-encrypt-string epg-encrypt-file epg-start-encrypt epg-sign-string
;;;;;;  epg-sign-file epg-start-sign epg-verify-string epg-verify-file
;;;;;;  epg-start-verify epg-decrypt-string epg-decrypt-file epg-start-decrypt
;;;;;;  epg-cancel epg-list-keys) "epg" "site-lisp/epg/epg.el" (17968
;;;;;;  18206))
;;; Generated autoloads from site-lisp/epg/epg.el

(autoload (quote epg-list-keys) "epg" "\
Return a list of epg-key objects matched with NAME.
If MODE is nil or 'public, only public keyring should be searched.
If MODE is t or 'secret, only secret keyring should be searched. 
Otherwise, only public keyring should be searched and the key
signatures should be included.
NAME is either a string or a list of strings." nil nil)

(autoload (quote epg-cancel) "epg" nil nil nil)

(autoload (quote epg-start-decrypt) "epg" "\
Initiate a decrypt operation on CIPHER.
CIPHER must be a file data object.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-decrypt-file' or `epg-decrypt-string' instead." nil nil)

(autoload (quote epg-decrypt-file) "epg" "\
Decrypt a file CIPHER and store the result to a file PLAIN.
If PLAIN is nil, it returns the result as a string." nil nil)

(autoload (quote epg-decrypt-string) "epg" "\
Decrypt a string CIPHER and return the plain text." nil nil)

(autoload (quote epg-start-verify) "epg" "\
Initiate a verify operation on SIGNATURE.
SIGNATURE and SIGNED-TEXT are a data object if they are specified.

For a detached signature, both SIGNATURE and SIGNED-TEXT should be set.
For a normal or a cleartext signature, SIGNED-TEXT should be nil.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-verify-file' or `epg-verify-string' instead." nil nil)

(autoload (quote epg-verify-file) "epg" "\
Verify a file SIGNATURE.
SIGNED-TEXT and PLAIN are also a file if they are specified.

For a detached signature, both SIGNATURE and SIGNED-TEXT should be
string.  For a normal or a cleartext signature, SIGNED-TEXT should be
nil.  In the latter case, if PLAIN is specified, the plaintext is
stored into the file after successful verification." nil nil)

(autoload (quote epg-verify-string) "epg" "\
Verify a string SIGNATURE.
SIGNED-TEXT is a string if it is specified.

For a detached signature, both SIGNATURE and SIGNED-TEXT should be
string.  For a normal or a cleartext signature, SIGNED-TEXT should be
nil.  In the latter case, this function returns the plaintext after
successful verification." nil nil)

(autoload (quote epg-start-sign) "epg" "\
Initiate a sign operation on PLAIN.
PLAIN is a data object.

If optional 3rd argument MODE is t or 'detached, it makes a detached signature.
If it is nil or 'normal, it makes a normal signature.
Otherwise, it makes a cleartext signature.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-sign-file' or `epg-sign-string' instead." nil nil)

(autoload (quote epg-sign-file) "epg" "\
Sign a file PLAIN and store the result to a file SIGNATURE.
If SIGNATURE is nil, it returns the result as a string.
If optional 3rd argument MODE is t or 'detached, it makes a detached signature.
If it is nil or 'normal, it makes a normal signature.
Otherwise, it makes a cleartext signature." nil nil)

(autoload (quote epg-sign-string) "epg" "\
Sign a string PLAIN and return the output as string.
If optional 3rd argument MODE is t or 'detached, it makes a detached signature.
If it is nil or 'normal, it makes a normal signature.
Otherwise, it makes a cleartext signature." nil nil)

(autoload (quote epg-start-encrypt) "epg" "\
Initiate an encrypt operation on PLAIN.
PLAIN is a data object.
If RECIPIENTS is nil, it performs symmetric encryption.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-encrypt-file' or `epg-encrypt-string' instead." nil nil)

(autoload (quote epg-encrypt-file) "epg" "\
Encrypt a file PLAIN and store the result to a file CIPHER.
If CIPHER is nil, it returns the result as a string.
If RECIPIENTS is nil, it performs symmetric encryption." nil nil)

(autoload (quote epg-encrypt-string) "epg" "\
Encrypt a string PLAIN.
If RECIPIENTS is nil, it performs symmetric encryption." nil nil)

(autoload (quote epg-start-export-keys) "epg" "\
Initiate an export keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-export-keys-to-file' or `epg-export-keys-to-string' instead." nil nil)

(autoload (quote epg-export-keys-to-file) "epg" "\
Extract public KEYS." nil nil)

(autoload (quote epg-export-keys-to-string) "epg" "\
Extract public KEYS and return them as a string." nil nil)

(autoload (quote epg-start-import-keys) "epg" "\
Initiate an import keys operation.
KEYS is a data object.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-import-keys-from-file' or `epg-import-keys-from-string' instead." nil nil)

(autoload (quote epg-import-keys-from-file) "epg" "\
Add keys from a file KEYS." nil nil)

(autoload (quote epg-import-keys-from-string) "epg" "\
Add keys from a string KEYS." nil nil)

(autoload (quote epg-start-receive-keys) "epg" "\
Initiate a receive key operation.
KEY-ID-LIST is a list of key IDs.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-generate-key-from-file' or `epg-generate-key-from-string' instead." nil nil)

(autoload (quote epg-receive-keys) "epg" "\
Add keys from server.
KEYS is a list of key IDs" nil nil)

(defalias (quote epg-import-keys-from-server) (quote epg-receive-keys))

(autoload (quote epg-start-delete-keys) "epg" "\
Initiate an delete keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-delete-keys' instead." nil nil)

(autoload (quote epg-delete-keys) "epg" "\
Delete KEYS from the key ring." nil nil)

(autoload (quote epg-start-sign-keys) "epg" "\
Initiate an sign keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-sign-keys' instead." nil nil)

(autoload (quote epg-sign-keys) "epg" "\
Sign KEYS from the key ring." nil nil)

(autoload (quote epg-start-generate-key) "epg" "\
Initiate a key generation.
PARAMETERS specifies parameters for the key.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-generate-key-from-file' or `epg-generate-key-from-string' instead." nil nil)

(autoload (quote epg-generate-key-from-file) "epg" "\
Generate a new key pair.
PARAMETERS is a file which tells how to create the key." nil nil)

(autoload (quote epg-generate-key-from-string) "epg" "\
Generate a new key pair.
PARAMETERS is a string which tells how to create the key." nil nil)

;;;***

;;;### (autoloads (epg-expand-group epg-check-configuration epg-configuration)
;;;;;;  "epg-config" "site-lisp/epg/epg-config.el" (17853 29144))
;;; Generated autoloads from site-lisp/epg/epg-config.el

(autoload (quote epg-configuration) "epg-config" "\
Return a list of internal configuration parameters of `epg-gpg-program'." nil nil)

(autoload (quote epg-check-configuration) "epg-config" "\
Verify that a sufficient version of GnuPG is installed." nil nil)

(autoload (quote epg-expand-group) "epg-config" "\
Look at CONFIG and try to expand GROUP." nil nil)

;;;***

;;;### (autoloads (eshell-toggle eshell-toggle-cd) "esh-toggle" "esh-toggle.el"
;;;;;;  (15542 40456))
;;; Generated autoloads from esh-toggle.el

(autoload (quote eshell-toggle-cd) "esh-toggle" "\
Calls `eshell-toggle' with a prefix argument.
See the command `eshell-toggle'" t nil)

(autoload (quote eshell-toggle) "esh-toggle" "\
Toggles between the *eshell* buffer and the current buffer.
With a prefix ARG also insert a \"cd DIR\" command into the eshell,
where DIR is the directory of the current buffer.

Call twice in a row to get a full screen window for the *eshell*
buffer.

When called in the *eshell* buffer returns you to the buffer you were
editing before caling the first time.

Options: `eshell-toggle-goto-eob'" t nil)

;;;***

;;;### (autoloads (eval-expr eval-expr-install) "eval-expr" "site-lisp/eval-expr.el"
;;;;;;  (18084 9489))
;;; Generated autoloads from site-lisp/eval-expr.el

(defvar eval-expr-error-message-delay 3 "\
*Amount of time, in seconds, to display in echo area before continuing.")

(defvar eval-expr-prompt "Eval: " "\
*Prompt used by eval-expr.")

(defvar eval-expr-honor-debug-on-error t "\
*If non-nil, do not trap evaluation errors.
Instead, allow errors to throw user into the debugger, provided
debug-on-error specifies that the particular error is a debuggable condition.")

(defvar eval-expr-use-echo-area-or-buffer 1 "\
*Preference for when to use echo area of a temporary buffer for results.

If set to t or `buffer', always put results into a temporary buffer.
If set to `nil' or `echo-area', always display results in echo area.
If an integer N, use the echo area unless the results would require more
than N lines to display; in that case, use a temporary buffer.

Some versions of emacs can display arbitrarily large output in the echo
area by dynamically resizing it, so a temporary buffer is not necessary
unless you expect the output to exceed the limits of the resize thresholds
or want to be able to edit the results.")

(defvar eval-expr-print-level (cond ((boundp (quote eval-expression-print-level)) (default-value (quote eval-expression-print-level))) ((boundp (quote print-level)) (default-value (quote print-level)))) "\
*Like print-level, but affect results printed by `eval-expr' only.")

(defvar eval-expr-print-length (cond ((boundp (quote eval-expression-print-length)) (default-value (quote eval-expression-print-length))) ((boundp (quote print-length)) (default-value (quote print-length)))) "\
*Like print-length, but affect results printed by `eval-expr' only.")

(defvar eval-expr-print-function (quote prin1) "\
*Function to use for printing objects.
This can be set to e.g. `pp' to generate pretty-printed results.")

(autoload (quote eval-expr-install) "eval-expr" "\
Replace standard eval-expression command with enhanced eval-expr." t nil)

(autoload (quote eval-expr) "eval-expr" "\
Evaluate EXPRESSION and print value in minibuffer, temp, or current buffer.
A temp output buffer is used if there is more than one line in the
evaluated result.
If invoked with a prefix arg, or second lisp argument EE::INSERT-VALUE is
non-nil, then insert final value into the current buffer at point.

Value is also consed on to front of the variable `values'." t nil)

;;;***

;;;### (autoloads (find-and-load-library find-library) "find-library"
;;;;;;  "site-lisp/find-library.el" (18084 9489))
;;; Generated autoloads from site-lisp/find-library.el

(autoload (quote find-library) "find-library" "\
Find a library file with completion." t nil)

(autoload (quote find-and-load-library) "find-library" "\
Find a library file with completion." t nil)

;;;***

;;;### (autoloads (redo-footnotes) "footnote-ext" "footnote-ext.el"
;;;;;;  (18085 9074))
;;; Generated autoloads from footnote-ext.el

(autoload (quote redo-footnotes) "footnote-ext" "\
Redo all footnotes in a buffer, renumbering and redefining them.
This is useful for resuming work on an article, or for renumbering
after lots of editing has occurred.

If a textual footnote references a non-existent definition, the
footnote mark is removed.  If a definition is no longer referenced, it
is also deleted." t nil)

;;;***

;;;### (autoloads (groovy-mode) "groovy-mode" "site-lisp/groovy-mode.el"
;;;;;;  (18084 9490))
;;; Generated autoloads from site-lisp/groovy-mode.el

(autoload (quote groovy-mode) "groovy-mode" "\
Major mode for editing groovy scripts.
\\[groovy-indent-command] properly indents subexpressions of multi-line
class, module, def, if, while, for, do, and case statements, taking
nesting into account.

The variable groovy-indent-level controls the amount of indentation.
\\{groovy-mode-map}" t nil)

;;;***

;;;### (autoloads (mew-shimbun-expire mew-shimbun-expire-all mew-shimbun-re-retrieve-all
;;;;;;  mew-shimbun-re-retrieve mew-shimbun-retrieve-all mew-shimbun-retrieve
;;;;;;  mew-shimbun-goto-folder mew-shimbun-goto-unseen-folder) "mew-shimbun"
;;;;;;  "site-lisp/emacs-w3m/shimbun/mew-shimbun.el" (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/shimbun/mew-shimbun.el

(autoload (quote mew-shimbun-goto-unseen-folder) "mew-shimbun" "\
Goto folder for SHIMBUN to have a few new messages." t nil)

(autoload (quote mew-shimbun-goto-folder) "mew-shimbun" "\
Goto folder for SHIMBUN.
If called with '\\[universal-argument]', goto folder to have a few new messages." t nil)

(autoload (quote mew-shimbun-retrieve) "mew-shimbun" "\
Retrieve articles via SHIMBUN on this folder." t nil)

(autoload (quote mew-shimbun-retrieve-all) "mew-shimbun" "\
Retrieve all articles via SHIMBUN." t nil)

(autoload (quote mew-shimbun-re-retrieve) "mew-shimbun" "\
Re-retrieve this message.
If called with '\\[universal-argument]', re-retrieve messages marked with
'mew-shimbun-mark-re-retrieve'." t nil)

(autoload (quote mew-shimbun-re-retrieve-all) "mew-shimbun" "\
Re-retrieve all messages in this folder.
If called with '\\[universal-argument]', re-retrieve messages in the region." t nil)

(autoload (quote mew-shimbun-expire-all) "mew-shimbun" "\
Expire all shimbun folder." t nil)

(autoload (quote mew-shimbun-expire) "mew-shimbun" "\
Expire this shimbun folder." t nil)

;;;***

;;;### (autoloads (mime-w3m-preview-text/html) "mime-w3m" "site-lisp/emacs-w3m/mime-w3m.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/mime-w3m.el

(autoload (quote mime-w3m-preview-text/html) "mime-w3m" nil nil nil)

;;;***

;;;### (autoloads (nnml-generate-nov-databases) "nnml" "nnml.el"
;;;;;;  (18107 29913))
;;; Generated autoloads from nnml.el

(autoload (quote nnml-generate-nov-databases) "nnml" "\
Generate NOV databases in all nnml directories." t nil)

;;;***

;;;### (autoloads (gnus-group-make-shimbun-group gnus-summary-refer-shimbun-article)
;;;;;;  "nnshimbun" "site-lisp/emacs-w3m/shimbun/nnshimbun.el" (18090
;;;;;;  5606))
;;; Generated autoloads from site-lisp/emacs-w3m/shimbun/nnshimbun.el

(autoload (quote gnus-summary-refer-shimbun-article) "nnshimbun" "\
Show a shimbun article pointed to by the given URL." t nil)

(autoload (quote gnus-group-make-shimbun-group) "nnshimbun" "\
Create a new nnshimbun group.
The user will be prompted for a SERVER name and a GROUP name." t nil)

;;;***

;;;### (autoloads (nxml-glyph-display-string) "nxml-glyph" "site-lisp/nxml-mode/nxml-glyph.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/nxml-glyph.el

(autoload (quote nxml-glyph-display-string) "nxml-glyph" "\
Return a string that can display a glyph for Unicode code-point N.
FACE gives the face that will be used for displaying the string.
Return nil if the face cannot display a glyph for N." nil nil)

;;;***

;;;### (autoloads (nxml-mode) "nxml-mode" "site-lisp/nxml-mode/nxml-mode.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/nxml-mode.el

(autoload (quote nxml-mode) "nxml-mode" "\
Major mode for editing XML.

Syntax highlighting is performed unless the variable
`nxml-syntax-highlight-flag' is nil.

\\[nxml-finish-element] finishes the current element by inserting an end-tag.
C-c C-i closes a start-tag with `>' and then inserts a balancing end-tag
leaving point between the start-tag and end-tag. 
\\[nxml-balanced-close-start-tag-block] is similar but for block rather than inline elements:
the start-tag, point, and end-tag are all left on separate lines.
If `nxml-slash-auto-complete-flag' is non-nil, then inserting a `</'
automatically inserts the rest of the end-tag.

\\[nxml-complete] performs completion on the symbol preceding point.

\\[nxml-dynamic-markup-word] uses the contents of the current buffer
to choose a tag to put around the word preceding point.

Sections of the document can be displayed in outline form.  The
variable `nxml-section-element-name-regexp' controls when an element
is recognized as a section.  The same key sequences that change
visibility in outline mode are used except that they start with C-c C-o
instead of C-c.

Validation is provided by the related minor-mode `rng-validate-mode'.
This also makes completion schema- and context- sensitive.  Element
names, attribute names, attribute values and namespace URIs can all be
completed. By default, `rng-validate-mode' is automatically enabled by
`rng-nxml-mode-init' which is normally added to `nxml-mode-hook'. You
can toggle it using \\[rng-validate-mode].

\\[indent-for-tab-command] indents the current line appropriately.
This can be customized using the variable `nxml-child-indent'
and the variable `nxml-attribute-indent'.

\\[nxml-insert-named-char] inserts a character reference using
the character's name (by default, the Unicode name). \\[universal-argument] \\[nxml-insert-named-char]
inserts the character directly.

The Emacs commands that normally operate on balanced expressions will
operate on XML markup items.  Thus \\[forward-sexp] will move forward
across one markup item; \\[backward-sexp] will move backward across
one markup item; \\[kill-sexp] will kill the following markup item;
\\[mark-sexp] will mark the following markup item.  By default, each
tag each treated as a single markup item; to make the complete element
be treated as a single markup item, set the variable
`nxml-sexp-element-flag' to t.  For more details, see the function
`nxml-forward-balanced-item'.

\\[nxml-backward-up-element] and \\[nxml-down-element] move up and down the element structure.

Many aspects this mode can be customized using
\\[customize-group] nxml RET." t nil)

;;;***

;;;### (autoloads (nxml-enable-unicode-char-name-sets) "nxml-uchnm"
;;;;;;  "site-lisp/nxml-mode/nxml-uchnm.el" (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/nxml-uchnm.el

(autoload (quote nxml-enable-unicode-char-name-sets) "nxml-uchnm" "\
Enable the use of Unicode standard names for characters.
The Unicode blocks for which names are enabled is controlled by
the variable `nxml-enabled-unicode-blocks'." t nil)

;;;***

;;;### (autoloads (octet-mime-setup mime-view-octet mime-preview-octet
;;;;;;  octet-find-file octet-buffer) "octet" "site-lisp/emacs-w3m/octet.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/octet.el

(autoload (quote octet-buffer) "octet" "\
View octet-stream content according to `octet-type-filter-alist'.
Optional NAME is the filename.
If optional CONTENT-TYPE is specified, it is used for type guess." t nil)

(autoload (quote octet-find-file) "octet" "\
Find FILE with octet-stream decoding." t nil)

(autoload (quote mime-preview-octet) "octet" "\
A method for mime-view to preview octet message." nil nil)

(autoload (quote mime-view-octet) "octet" "\
A method for mime-view to display octet message." nil nil)

(autoload (quote octet-mime-setup) "octet" "\
Octet setting for MIME module." nil nil)

;;;***

;;;### (autoloads (svn-status) "psvn" "site-lisp/psvn.el" (18084
;;;;;;  9489))
;;; Generated autoloads from site-lisp/psvn.el
 (defalias 'svn-examine 'svn-status)

(autoload (quote svn-status) "psvn" "\
Examine the status of Subversion working copy in directory DIR.
If ARG is -, allow editing of the parameters. One could add -N to
run the status command non recursively to make it faster.
For every other non nil ARG, then also update the working copy,
if supported by the backend.

If the directory DIR is not supported by any psvn backend,
examine if there is CVS and run `cvs-examine'. Otherwise ask if
to run `dired'." t nil)

;;;***

;;;### (autoloads (svn-svk-status) "psvn-svk" "site-lisp/psvn-svk.el"
;;;;;;  (18084 9489))
;;; Generated autoloads from site-lisp/psvn-svk.el

(autoload (quote svn-svk-status) "psvn-svk" "\
Implementation of `svn-status' for the SVK backend." nil nil)

;;;***

;;;### (autoloads (svn-svn-status) "psvn-svn" "site-lisp/psvn-svn.el"
;;;;;;  (18084 9490))
;;; Generated autoloads from site-lisp/psvn-svn.el

(autoload (quote svn-svn-status) "psvn-svn" "\
Implementation of `svn-status' for the SVN backend." nil nil)

;;;***

;;;### (autoloads (pydb-pydbtrack-overlay-arrow pydb) "pydb" "site-lisp/pydb/emacs/pydb.el"
;;;;;;  (17894 15827))
;;; Generated autoloads from site-lisp/pydb/emacs/pydb.el

(autoload (quote pydb) "pydb" "\
Run pydb on program FILE in buffer `*gud-FILE*'.
The directory containing FILE becomes the initial working directory
and source-file directory for your debugger." t nil)

(autoload (quote pydb-pydbtrack-overlay-arrow) "pydb" "\
Activate or de arrow at beginning-of-line in current buffer." nil nil)

;;;***

;;;### (autoloads (regexp-opt-depth regexp-opt) "regexp-opt" "site-lisp/emacs-w3m/attic/regexp-opt.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/attic/regexp-opt.el

(autoload (quote regexp-opt) "regexp-opt" "\
Return a regexp to match a string in STRINGS.
Each string should be unique in STRINGS and should not contain any regexps,
quoted or not.  If optional PAREN is non-nil, ensure that the returned regexp
is enclosed by at least one regexp grouping construct.
The returned regexp is typically more efficient than the equivalent regexp:

 (let ((open-paren (if PAREN \"\\\\(\" \"\")) (close-paren (if PAREN \"\\\\)\" \"\")))
   (concat open-paren (mapconcat 'regexp-quote STRINGS \"\\\\|\") close-paren))

but typically contains more regexp grouping constructs.
Use `regexp-opt-depth' to count them." nil nil)

(autoload (quote regexp-opt-depth) "regexp-opt" "\
Return the depth of REGEXP.
This means the number of regexp grouping constructs (parenthesised expressions)
in REGEXP." nil nil)

;;;***

;;;### (autoloads (remember-destroy remember-buffer remember-clipboard
;;;;;;  remember-region remember-other-frame remember) "remember"
;;;;;;  "site-lisp/remember/remember.el" (18144 32674))
;;; Generated autoloads from site-lisp/remember/remember.el

(autoload (quote remember) "remember" "\
Remember an arbitrary piece of data.
With a prefix, uses the region as INITIAL." t nil)

(autoload (quote remember-other-frame) "remember" nil t nil)

(autoload (quote remember-region) "remember" "\
Remember the data from BEG to END.
If called from within the remember buffer, BEG and END are ignored,
and the entire buffer will be remembered.

This function is meant to be called from the *Remember* buffer.
If you want to remember a region, supply a universal prefix to
`remember' instead. For example: C-u M-x remember." t nil)

(autoload (quote remember-clipboard) "remember" "\
Remember the contents of the current clipboard.
Most useful for remembering things from Netscape or other X Windows
application." t nil)

(autoload (quote remember-buffer) "remember" "\
Remember the contents of the current buffer." t nil)

(autoload (quote remember-destroy) "remember" "\
Destroy the current *Remember* buffer." t nil)

;;;***

;;;### (autoloads (remember-bbdb-store-in-mailbox) "remember-bbdb"
;;;;;;  "site-lisp/remember/remember-bbdb.el" (18090 5625))
;;; Generated autoloads from site-lisp/remember/remember-bbdb.el

(autoload (quote remember-bbdb-store-in-mailbox) "remember-bbdb" "\
Store remember data as if it were incoming mail.
In which case `remember-mailbox' should be the name of the mailbox.
Each piece of psuedo-mail created will have an `X-Todo-Priority'
field, for the purpose of appropriate splitting." nil nil)

;;;***

;;;### (autoloads (remember-location remember-url) "remember-bibl"
;;;;;;  "site-lisp/remember/remember-bibl.el" (18090 5625))
;;; Generated autoloads from site-lisp/remember/remember-bibl.el

(autoload (quote remember-url) "remember-bibl" "\
Remember a URL in `bibl-mode' that is being visited with w3." t nil)

(autoload (quote remember-location) "remember-bibl" "\
Remember a bookmark location in `bibl-mode'." t nil)

;;;***

;;;### (autoloads (remember-blosxom) "remember-blosxom" "site-lisp/remember/remember-blosxom.el"
;;;;;;  (18090 5625))
;;; Generated autoloads from site-lisp/remember/remember-blosxom.el

(autoload (quote remember-blosxom) "remember-blosxom" "\
Remember this text to a blosxom story.
This function can be added to `remember-handler-functions'." nil nil)

;;;***

;;;### (autoloads (remember-emacs-wiki-journal-add-entry-maybe remember-emacs-wiki-journal-add-entry-auto
;;;;;;  remember-emacs-wiki-journal-add-entry) "remember-emacs-wiki-journal"
;;;;;;  "site-lisp/remember/remember-emacs-wiki-journal.el" (18090
;;;;;;  5625))
;;; Generated autoloads from site-lisp/remember/remember-emacs-wiki-journal.el

(autoload (quote remember-emacs-wiki-journal-add-entry) "remember-emacs-wiki-journal" "\
Prompt for category and heading and add entry." nil nil)

(autoload (quote remember-emacs-wiki-journal-add-entry-auto) "remember-emacs-wiki-journal" "\
Add entry where the category is the first word and the heading the
rest of the words on the first line." nil nil)

(autoload (quote remember-emacs-wiki-journal-add-entry-maybe) "remember-emacs-wiki-journal" "\
Like `remember-emacs-wiki-journal-add-entry-auto' but only adds
entry if the first line matches `emacs-wiki-journal-category-regexp'." nil nil)

;;;***

;;;### (autoloads (rfcview-mode rfcview-customize) "rfcview" "site-lisp/rfcview.el"
;;;;;;  (18084 9490))
;;; Generated autoloads from site-lisp/rfcview.el

(autoload (quote rfcview-customize) "rfcview" nil t nil)

(autoload (quote rfcview-mode) "rfcview" "\
Major mode for viewing Internet RFCs.

http://www.neilvandyke.org/rfcview/

Key bindings:
\\{rfcview-mode-map}" t nil)

;;;***

;;;### (autoloads (rng-c-load-schema) "rng-cmpct" "site-lisp/nxml-mode/rng-cmpct.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/rng-cmpct.el

(autoload (quote rng-c-load-schema) "rng-cmpct" "\
Load a schema in RELAX NG compact syntax from FILENAME.
Return a pattern." nil nil)

;;;***

;;;### (autoloads (rng-write-version rng-format-manual rng-byte-compile-load
;;;;;;  rng-update-autoloads) "rng-maint" "site-lisp/nxml-mode/rng-maint.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/rng-maint.el

(autoload (quote rng-update-autoloads) "rng-maint" "\
Update the autoloads in rng-auto.el." t nil)

(autoload (quote rng-byte-compile-load) "rng-maint" "\
Byte-compile and load all of the RELAX NG library in an appropriate order." t nil)

(autoload (quote rng-format-manual) "rng-maint" "\
Create manual.texi from manual.xml." t nil)

(autoload (quote rng-write-version) "rng-maint" nil nil nil)

;;;***

;;;### (autoloads (rng-nxml-mode-init) "rng-nxml" "site-lisp/nxml-mode/rng-nxml.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/rng-nxml.el

(autoload (quote rng-nxml-mode-init) "rng-nxml" "\
Initialize `nxml-mode' to take advantage of `rng-validate-mode'.
This is typically called from `nxml-mode-hook'.
Validation will be enabled if `rng-nxml-auto-validate-flag' is non-nil." t nil)

;;;***

;;;### (autoloads (rng-validate-mode) "rng-valid" "site-lisp/nxml-mode/rng-valid.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/rng-valid.el

(autoload (quote rng-validate-mode) "rng-valid" "\
Minor mode performing continual validation against a RELAX NG schema.

Checks whether the buffer is a well-formed XML 1.0 document,
conforming to the XML Namespaces Recommendation and valid against a
RELAX NG schema. The mode-line indicates whether it is or not.  Any
parts of the buffer that cause it not to be are considered errors and
are highlighted with `rng-error-face'. A description of each error is
available as a tooltip.  \\[rng-next-error] goes to the next error
after point. Clicking mouse-1 on the word `Invalid' in the mode-line
goes to the first error in the buffer. If the buffer changes, then it
will be automatically rechecked when Emacs becomes idle; the
rechecking will be paused whenever there is input pending..

By default, uses a vacuous schema that allows any well-formed XML
document. A schema can be specified explictly using
\\[rng-set-schema-file-and-validate], or implicitly based on the buffer's
file name or on the root element name.  In each case the schema must
be a RELAX NG schema using the compact schema (such schemas
conventionally have a suffix of `.rnc').  The variable
`rng-schema-locating-files' specifies files containing rules
to use for finding the schema." t nil)

;;;***

;;;### (autoloads (rng-xsd-compile) "rng-xsd" "site-lisp/nxml-mode/rng-xsd.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/rng-xsd.el

(put (quote http://www\.w3\.org/2001/XMLSchema-datatypes) (quote rng-dt-compile) (quote rng-xsd-compile))

(autoload (quote rng-xsd-compile) "rng-xsd" "\
Provides W3C XML Schema as a RELAX NG datatypes library. NAME is a
symbol giving the local name of the datatype.  PARAMS is a list of
pairs (PARAM-NAME . PARAM-VALUE) where PARAM-NAME is a symbol giving
the name of the parameter and PARAM-VALUE is a string giving its
value.  If NAME or PARAMS are invalid, it calls rng-dt-error passing
it arguments in the same style as format; the value from rng-dt-error
will be returned.  Otherwise, it returns a list.  The first member of
the list is t if any string is a legal value for the datatype and nil
otherwise.  The second argument is a symbol; this symbol will be
called as a function passing it a string followed by the remaining
members of the list.  The function must return an object representing
the value of the datatype that was represented by the string, or nil
if the string is not a representation of any value. The object
returned can be any convenient non-nil value, provided that, if two
strings represent the same value, the returned objects must be equal." nil nil)

;;;***

;;;### (autoloads (schedule-completion-time) "schedule" "schedule.el"
;;;;;;  (18205 36835))
;;; Generated autoloads from schedule.el

(autoload (quote schedule-completion-time) "schedule" "\
Advance THEN by COUNT seconds, skipping the weekends and holidays.
THEN must not already be in a holiday or non-worktime.  Make sure that
`schedule-align-now' is called at least once before this function ever
gets called." nil nil)

;;;***

;;;### (autoloads (session-initialize) "session" "site-lisp/session.el"
;;;;;;  (18084 9489))
;;; Generated autoloads from site-lisp/session.el

(autoload (quote session-initialize) "session" "\
Initialize package session and read previous session file.
Setup hooks and load `session-save-file', see `session-initialize'.  At
best, this function is called at the end of the Emacs startup, i.e., add
this function to `after-init-hook'." t nil)

;;;***

;;;### (autoloads (ssh) "ssh" "site-lisp/ssh.el" (18084 9489))
;;; Generated autoloads from site-lisp/ssh.el
 (add-hook 'same-window-regexps "^\\*ssh-.*\\*\\(\\|<[0-9]+>\\)")

(autoload (quote ssh) "ssh" "\
Open a network login connection via `ssh' with args INPUT-ARGS.
INPUT-ARGS should start with a host name; it may also contain
other arguments for `ssh'.

Input is sent line-at-a-time to the remote connection.

Communication with the remote host is recorded in a buffer `*ssh-HOST*'
\(or `*ssh-USER@HOST*' if the remote username differs).
If a prefix argument is given and the buffer `*ssh-HOST*' already exists,
a new buffer with a different connection will be made.

When called from a program, if the optional second argument BUFFER is
a string or buffer, it specifies the buffer to use.

The variable `ssh-program' contains the name of the actual program to
run.  It can be a relative or absolute path.

The variable `ssh-explicit-args' is a list of arguments to give to
the ssh when starting.  They are prepended to any arguments given in
INPUT-ARGS.

If the default value of `ssh-directory-tracking-mode' is t, then the
default directory in that buffer is set to a remote (FTP) file name to
access your home directory on the remote machine.  Occasionally this causes
an error, if you cannot access the home directory on that machine.  This
error is harmless as long as you don't try to use that default directory.

If `ssh-directory-tracking-mode' is neither t nor nil, then the default
directory is initially set up to your (local) home directory.
This is useful if the remote machine and your local machine
share the same files via NFS.  This is the default.

If you wish to change directory tracking styles during a session, use the
function `ssh-directory-tracking-mode' rather than simply setting the
variable." t nil)

;;;***

;;;### (autoloads (tla-submit-patch-done tla-prepare-patch-submission
;;;;;;  tla-insert-location tla-tree-lint tla-ediff-add-log-entry
;;;;;;  tla-tag-regenerate tla-tag-insert tla-tag-string tla-inventory-file-mode
;;;;;;  tla-revlog-any tla-log-edit-mode tla-revlog tla-file-has-conflict-p
;;;;;;  tla-get tla-missing tla-revisions tla-tree-revisions tla-tree-revisions-goto
;;;;;;  tla-make-archive tla-register-archive tla-archives tla-bookmarks
;;;;;;  tla-tag tla-export tla-switch tla-star-merge tla-id-tagging-method
;;;;;;  tla-my-revision-library tla-tree-id tla-my-id tla-tree-version
;;;;;;  tla-help tla-logs tla-changelog tla-rm tla-start-project
;;;;;;  tla-commit tla-revision-get-last-revision tla-file-view-original
;;;;;;  tla-file-ediff tla-view-conflicts tla-resolved tla-file-diff
;;;;;;  tla-file-ediff-against tla-apply-changeset tla-get-changeset
;;;;;;  tla-delta tla-changes-last-revision tla-changes-against tla-update
;;;;;;  tla-changes tla-edit-log tla-inventory) "tla" "site-lisp/dvc-snapshot/lisp/tla.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/tla.el

(autoload (quote tla-inventory) "tla" "\
Show a tla inventory at DIRECTORY.
When called with a prefix arg, pop to the inventory buffer.
DIRECTORY defaults to the current one when within an arch managed tree,
unless prefix argument ARG is non-nil." t nil)

(autoload (quote tla-edit-log) "tla" "\
Edit the tla log file.

With an optional prefix argument INSERT-CHANGELOG, insert the last
group of entries from the ChangeLog file.  SOURCE-BUFFER, if non-nil,
is the buffer from which the function was called.  It is used to get
the list of marked files, and potentially run a selected file commit." t nil)

(autoload (quote tla-changes) "tla" "\
Run \"tla changes\".

When called without a prefix argument: show the detailed diffs also.
When called with a prefix argument SUMMARY: do not show detailed
diffs. When AGAINST is non-nil, use it as comparison tree.

DONT-SWITCH is necessary for DVC, but currently ignored." t nil)

(autoload (quote tla-update) "tla" "\
Run tla update in TREE.

Also runs update recursively for subdirectories.
After running update, execute HANDLE (function taking no argument)." t nil)

(autoload (quote tla-changes-against) "tla" "\
Wrapper for `tla-changes'.

When called interactively, SUMMARY is the prefix arg, and AGAINST is
read from the user." t nil)

(autoload (quote tla-changes-last-revision) "tla" "\
Run `tla-changes' against the last but one revision.

The idea is that running this command just after a commit should be
equivalent to running `tla-changes' just before the commit.

SUMMARY is passed to `tla-changes'." t nil)

(autoload (quote tla-delta) "tla" "\
Run tla delta BASE MODIFIED.
If DIRECTORY is a non-empty string, the delta is stored to it.
If DIRECTORY is ask, a symbol, ask the name of directory.
If DIRECTORY is nil or an empty string, just show the delta using --diffs." t nil)

(autoload (quote tla-get-changeset) "tla" "\
Gets the changeset corresponding to REVISION.

When JUSTSHOW is non-nil (no prefix arg), just show the diff.
Otherwise, store changeset in DESTINATION.
If WITHOUT-DIFF is non-nil, don't use the --diff option to show the
changeset." t nil)

(autoload (quote tla-apply-changeset) "tla" "\
Call \"tla apply-changeset\".

CHANGESET is the changeset to apply, TARGET is the directory in which
to apply the changeset. If REVERSE is non-nil, apply the changeset in
reverse." t nil)

(autoload (quote tla-file-ediff-against) "tla" "\
View changes in FILE between BASE and MODIFIED using ediff." t nil)

(autoload (quote tla-file-diff) "tla" "\
Run \"tla file-diff\" on file FILE.

In interactive mode, the file is the current buffer's file.
If REVISION is specified, it must be a string representing a revision
name, and the file will be diffed according to this revision." t nil)

(autoload (quote tla-resolved) "tla" "\
Command to delete .rej file after conflicts resolution.
Asks confirmation if the file still has diff3 markers.

If \"resolved\" command is available, also run it." t nil)

(autoload (quote tla-view-conflicts) "tla" "\
*** WARNING: semi-deprecated function.
Use this function if you like, but M-x smerge-mode RET is actually
better for the same task ****

Graphical view of conflicts after tla star-merge --three-way. The
buffer given as an argument must be the content of a file with
conflicts markers like.

    <<<<<<< TREE
    my text
    =======
    his text
    >>>>>>> MERGE-SOURCE

Priority is given to your file by default. (This means all conflicts
will be rejected if you do nothing)." t nil)

(autoload (quote tla-file-ediff) "tla" "\
Interactive view of differences in FILE with ediff.

Changes are computed since last commit (or REVISION if specified)." t nil)

(autoload (quote tla-file-view-original) "tla" "\
Get the last-committed version of FILE in a buffer.

If REVISION is specified, it must be a cons representing the revision
for which to get the original." t nil)

(autoload (quote tla-revision-get-last-revision) "tla" "\
Insert the content of FILE in LAST-REVISION, in current buffer.

LAST-REVISION looks like
\(\"path\" NUM)." nil nil)

(autoload (quote tla-commit) "tla" "\
Run tla commit.

Optional argument HANDLER is the process handler for the commit
command. `nil' or a symbol(`seal' or `fix') is acceptable as
VERSION-FLAG.
When the commit finishes successful, `tla-commit-done-hook' is called." t nil)

(autoload (quote tla-start-project) "tla" "\
Start a new project.
Prompts for the root directory of the project and the fully
qualified version name to use.  Sets up and imports the tree and
displays an inventory buffer to allow the project's files to be
added and committed.
If ARCHIVE is given, use it when reading version.
Return a cons pair: its car is the new version name string, and
its cdr is imported location.
If SYNCHRONOUSLY is non-nil, run \"tla import\" synchronously.
Else run it asynchronously." t nil)

(autoload (quote tla-rm) "tla" "\
Call tla rm on file FILE.  Prompts for confirmation before." nil nil)

(autoload (quote tla-changelog) "tla" "\
Run \"tla changelog\".

display the result in an improved ChangeLog mode.
If NAME is given, name is passed to \"tla changelog\"
as the place where changelog is got." t nil)

(autoload (quote tla-logs) "tla" "\
Run tla logs." t nil)

(autoload (quote tla-help) "tla" "\
Run tla COMMAND -H." t nil)

(autoload (quote tla-tree-version) "tla" "\
Equivalent of tla tree-version (but implemented in pure elisp).

Optional argument LOCATION is the directory in which the command must
be ran.  If NO-ERROR is non-nil, don't raise errors if ran outside an
arch managed tree." t nil)

(autoload (quote tla-my-id) "tla" "\
Run tla my-id.

When called without a prefix argument ARG, just print the my-id from
tla and return it.  If MY-ID is not set yet, return an empty string.
When called with a prefix argument, ask for a new my-id.

The my-id should have the following format:

Your id is recorded in various archives and log messages as you use
arch.  It must consist entirely of printable characters and fit on one
line.  By convention, it should have the form of an email address, as
in this example:

Jane Hacker <jane.hacker@gnu.org>" t nil)

(autoload (quote tla-tree-id) "tla" "\
Call either 'baz tree-id' or 'tla logs -f -r' to get the tree-id." t nil)

(autoload (quote tla-my-revision-library) "tla" "\
Run tla my-revision-library.

When called without a prefix argument ARG, just print the
my-revision-library from tla.  When called with a prefix argument, ask
for a new my-revision-library.

my-revision-library specifies a path, where the revision library is
stored to speed up tla.  For example ~/tmp/arch-lib.

You can configure the parameters for the library via
`tla-library-config'." t nil)

(autoload (quote tla-id-tagging-method) "tla" "\
View (and return) or change the id-tagging method.
When called without prefix argument ARG: show the actual tagging method.
When called with prefix argument ARG: Ask the user for the new tagging method." t nil)

(autoload (quote tla-star-merge) "tla" "\
Star merge from version/revision FROM to local tree TO-TREE." t nil)

(autoload (quote tla-switch) "tla" "\
Run tla switch to VERSION in TREE.

After running update, execute HANDLE (function taking no argument)." t nil)

(autoload (quote tla-export) "tla" "\
Run tla export to export REVISION to DIR." t nil)

(autoload (quote tla-tag) "tla" "\
Create a tag from SOURCE-REVISION to TAG-VERSION.
Run tla tag --setup.
If SYNCHRONOUSLY is non-nil, the process for tagging runs synchronously.
Else it runs asynchronously." t nil)

(autoload (quote tla-bookmarks) "tla" "\
Display xtla bookmarks in a buffer.
With prefix argument ARG, reload the bookmarks file from disk." t nil)

(autoload (quote tla-archives) "tla" "\
Start the archive browser." t nil)

(autoload (quote tla-register-archive) "tla" "\
Call `tla--register-archive' interactively and `tla-archives' on success." t nil)

(autoload (quote tla-make-archive) "tla" "\
Call `tla--make-archive' interactively  then call `tla-archives'." t nil)

(autoload (quote tla-tree-revisions-goto) "tla" "\
Goto tree revisions buffer or call `tla-tree-revisions'." t nil)

(autoload (quote tla-tree-revisions) "tla" "\
Call `tla-revisions' in the current tree." t nil)

(autoload (quote tla-revisions) "tla" "\
List the revisions of ARCHIVE/CATEGORY--BRANCH--VERSION.

UNUSED is left here to keep the position of FROM-REVLIB" t nil)

(autoload (quote tla-missing) "tla" "\
Search in directory LOCAL-TREE for missing patches from LOCATION.
If the current buffers default directory is in an arch managed tree use that
one unless called with a prefix arg.  In all other cases prompt for the local
tree and the location." t nil)

(autoload (quote tla-get) "tla" "\
Run tla get in DIRECTORY.
If RUN-DIRED-P is non-nil, display the new tree in dired.
ARCHIVE, CATEGORY, BRANCH, VERSION and REVISION make up the revision to be
fetched.
If SYNCHRONOUSLY is non-nil, run the process synchronously.
Else, run the process asynchronously." t nil)

(autoload (quote tla-file-has-conflict-p) "tla" "\
Return non-nil if FILE-NAME has conflicts." nil nil)

(autoload (quote tla-revlog) "tla" "\
Show the log for REVISION-SPEC." t nil)

(add-to-list (quote auto-mode-alist) (quote ("\\+\\+log\\." . tla-log-edit-mode)))

(autoload (quote tla-log-edit-mode) "tla" "\
Major Mode to edit xtla log messages.
Commands:
\\{tla-log-edit-mode-map}
" t nil)

(autoload (quote tla-revlog-any) "tla" "\
Show the log entry for REVISION (a string)." t nil)

(autoload (quote tla-inventory-file-mode) "tla" "\
Major mode to edit tla inventory files (=tagging-method, .arch-inventory)." t nil)

(autoload (quote tla-tag-string) "tla" "\
Return a suitable string for an arch-tag.
Actually calls `tla-tag-function', which defaults to `tla-tag-uuid' to generate
string (and possibly add a comment-end after).

Interactively, you should call `tla-tag-insert', but this function can
be usefull to write template files." nil nil)

(autoload (quote tla-tag-insert) "tla" "\
Insert a unique arch-tag in the current file.
Actually calls `tla-tag-function', which defaults to `tla-tag-uuid' to generate
string (and possibly add a comment-end after)" t nil)

(autoload (quote tla-tag-regenerate) "tla" "\
Find an arch tag in the current buffer and regenerates it.
This means changing the ID of the file, which will usually be done after
copying a file in the same tree to avoid duplicates ID.

Raises an error when multiple tags are found or when no tag is found." t nil)

(autoload (quote tla-ediff-add-log-entry) "tla" "\
Add a log entry." t nil)

(autoload (quote tla-tree-lint) "tla" "\
Run tla tree-lint in directory ROOT." t nil)

(autoload (quote tla-insert-location) "tla" "\
Prompts an archive location and insert it on the current point location." t nil)

(autoload (quote tla-prepare-patch-submission) "tla" "\
Submit a patch to a tla working copy (at TLA-TREE-ROOT) via email.
With this feature it is not necessary to tag an tla archive.
You simply edit your checked out copy from your project and call this function.
The function will create a patch as *.tar.gz file (based on TARBALL-BASE-NAME)
and send it to the given email address EMAIL.
VERSION-STRING should indicate the version of tla that the patch applies to.
DESCRIPTION is a brief descsription of the patch.
SUBJECT is the subject for the email message.
For an example, how to use this function see: `tla-submit-patch'." t nil)

(autoload (quote tla-submit-patch-done) "tla" "\
Clean up after sending a patch via mail.
That function is usually called via `message-sent-hook'. Its purpose is to revert
the sent changes or to delete sent changeset tarball (see: `tla-patch-sent-action'." nil nil)

;;;***

;;;### (autoloads (tla-bconfig-mode) "tla-bconfig" "site-lisp/dvc-snapshot/lisp/tla-bconfig.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/tla-bconfig.el

(autoload (quote tla-bconfig-mode) "tla-bconfig" "\
Major mode to edit GNU arch's build config files." t nil)

(add-to-list (quote auto-mode-alist) (quote ("\\.arch$" . tla-bconfig-mode)))

;;;***

;;;### (autoloads (tla-browse) "tla-browse" "site-lisp/dvc-snapshot/lisp/tla-browse.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/tla-browse.el

(autoload (quote tla-browse) "tla-browse" "\
Browse registered archives as trees within one buffer.
You can specify the node should be opened by alist,
INITIAL-OPEN-LIST.  If APPEND is nil, the nodes not in
INITIAL-OPEN-LIST are made closed.  If non-nil, the nodes
already opened are kept open." t nil)

;;;***

;;;### (autoloads (tla-make-name-regexp tla-tree-root) "tla-core"
;;;;;;  "site-lisp/dvc-snapshot/lisp/tla-core.el" (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/tla-core.el

(autoload (quote tla-tree-root) "tla-core" "\
Return the tree root for LOCATION, nil if not in a local tree.
Computation is done from withing Emacs, by looking at an {arch}
directory in a parent buffer of LOCATION.  This is therefore very
fast.

If LOCATION is nil, the tree root is returned, and it is
guaranteed to end in a \"/\" character.

If NO-ERROR is non-nil, don't raise an error if LOCATION is not an
arch managed tree (but return nil)." t nil)

(autoload (quote tla-make-name-regexp) "tla-core" "\
Make a regexp for an Arch name (archive, category, ...).

LEVEL can be 0 (archive), 1 (category), 2 (branch), 3 (version)
or 4 (revision).

If SLASH-MANDATORY is non-nil, the '/' after the archive name is
mandatory. (allows to distinguish between Arch archives and emails.

If EXACT is non-nil, match exactly LEVEL." nil nil)

;;;***

;;;### (autoloads (tla-toggle-non-recursive-inventory tla-toggle-show-ancestor
;;;;;;  tla-toggle-three-way-merge tla-use-skip-present-option tla-non-recursive-inventory
;;;;;;  tla-show-ancestor tla-three-way-merge) "tla-defs" "site-lisp/dvc-snapshot/lisp/tla-defs.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/tla-defs.el

(eval-and-compile (require (quote easymenu)) (require (quote dvc-core)))

(defgroup xtla nil "Arch interface for emacs." :group (quote dvc) :prefix "tla-")

(defvar tla-three-way-merge t "\
*If non-nil, merge operations are invoked with --three-way.
\(or without --two-way for branches of arch in which --three-way is the
default).")

(defvar tla-show-ancestor nil "\
*If non-nil, merge operations are invoked with --show-ancestor.

With this option, conflicts markers will include TREE, MERGE-SOURCE,
and ancestor versions. `smerge-ediff' allows you to view the ancestor
with `ediff-show-ancestor' (usually bound to `/').

Unfortunately, this will also report more conflicts: Conflicts will be
reported even when TREE and MERGE-SOURCE are identical, if they differ
from ANCESTOR.")

(defvar tla-non-recursive-inventory t "\
*If non-nil, inventory is run with --no-recursion (if available).")

(defvar tla-use-skip-present-option nil "\
*If non-nil, use --skip-present with commands that allow it.")

(autoload (quote tla-toggle-three-way-merge) "tla-defs" "\
Toggle the value of `tla-three-way-merge'." t nil)

(autoload (quote tla-toggle-show-ancestor) "tla-defs" "\
Toggle the value of `tla-show-ancestor'." t nil)

(autoload (quote tla-toggle-non-recursive-inventory) "tla-defs" "\
Toggle the value of `tla-toggle-non-recursive-inventory'." t nil)

(add-to-list (quote auto-mode-alist) (quote ("/\\(=tagging-method\\|\\.arch-inventory\\)$" . tla-inventory-file-mode)))

;;;***

;;;### (autoloads nil "tla-dvc" "site-lisp/dvc-snapshot/lisp/tla-dvc.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/tla-dvc.el

(dvc-register-dvc (quote tla) "GNU Arch")

(defalias (quote tla-dvc-command-version) (quote tla-command-version))

(defalias (quote tla-dvc-file-has-conflict-p) (quote tla-file-has-conflict-p))

;;;***

;;;### (autoloads (tla-insinuate-gnus) "tla-gnus" "site-lisp/dvc-snapshot/lisp/tla-gnus.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/tla-gnus.el

(autoload (quote tla-insinuate-gnus) "tla-gnus" "\
Integrate the tla backend of DVC into Gnus.
Add the `tla-submit-patch-done' function to the
`message-sent-hook'.

The archives/categories/branches/version/revision names are buttonized
in the *Article* buffers." t nil)

;;;***

;;;### (autoloads (tla-tests-run tla-tests-batch) "tla-tests" "site-lisp/dvc-snapshot/lisp/tla-tests.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/tla-tests.el

(autoload (quote tla-tests-batch) "tla-tests" "\
Run all the available test-cases in batch mode." t nil)

(autoload (quote tla-tests-run) "tla-tests" "\
Run the testcase TEST.

Switch HOME to the test directory, clear the log buffer, call the
function TEST, and check that the list of tla commands ran by calling
TEST is the same as the one expected, stored in
`tla-tests-command-alist'" t nil)

;;;***

;;;### (autoloads nil "vc-svk" "site-lisp/vc-svk.el" (18085 16352))
;;; Generated autoloads from site-lisp/vc-svk.el
 (add-to-list 'vc-handled-backends 'SVK)
 (defun vc-svk-registered (file)
  (when (string-match
         "^Checkout Path:"
         (shell-command-to-string (concat "svk info "
                                          (expand-file-name file))))
    (setq file nil)
    (load "vc-svk")
    (vc-svk-registered file)))

;;;***

;;;### (autoloads (visit-url) "visit-url" "visit-url.el" (15179 41965))
;;; Generated autoloads from visit-url.el

(autoload (quote visit-url) "visit-url" nil t nil)

;;;***

;;;### (autoloads (w3m-region w3m-find-file w3m-browse-url w3m w3m-gohome
;;;;;;  w3m-goto-url-new-session w3m-goto-url w3m-download w3m-retrieve)
;;;;;;  "w3m" "site-lisp/emacs-w3m/w3m.el" (18090 5606))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m.el

(autoload (quote w3m-retrieve) "w3m" "\
Retrieve web contents pointed to by URL.
It will put the retrieved contents into the current buffer.

If HANDLER is nil, this function will retrieve web contents, return
the content type of the retrieved data, and then come to an end.  This
behavior is what is called a synchronous operation.  You have to
specify HANDLER in order to make this function show its real ability,
which is called an asynchronous operation.

If HANDLER is a function, this function will come to an end in no time.
In this case, contents will be retrieved by the asynchronous process
after a while.  And after finishing retrieving contents successfully,
HANDLER will be called on the buffer where this function starts.  The
content type of the retrieved data will be passed to HANDLER as a
string argument.

NO-DECODE specifies whether this function should not decode contents.
NO-CACHE specifies whether this function should not use cached contents.
POST-DATA and REFERER will be sent to the web server with a request." nil nil)

(autoload (quote w3m-download) "w3m" nil t nil)

(autoload (quote w3m-goto-url) "w3m" "\
Visit World Wide Web pages.  This is the primitive function of `w3m'.
If the second argument RELOAD is non-nil, reload a content of URL.
Except that if it is 'redisplay, re-display the page without reloading.
The third argument CHARSET specifies a charset to be used for decoding
a content.
The fourth argument POST-DATA should be a string or a cons cell.  If
it is a string, it makes this function request a body as if the
content-type is \"x-www-form-urlencoded\".  If it is a cons cell, the
car of a cell is used as the content-type and the cdr of a cell is
used as the body.
If the fifth argument REFERER is specified, it is used for a Referer:
field for this request.
The remaining HANDLER and ELEMENT[1] are for the internal operations
of emacs-w3m.
You can also use \"quicksearch\" url schemes such as \"gg:emacs\" which
would search for the term \"emacs\" with the Google search engine.  See
the `w3m-search' function and the variable `w3m-uri-replace-alist'.

[1] A note for the developers: ELEMENT is a history element which has
already been registered in the `w3m-history-flat' variable.  It is
corresponding to URL to be retrieved at this time, not for the url of
the current page." t nil)

(autoload (quote w3m-goto-url-new-session) "w3m" "\
Visit World Wide Web pages in a new session.
If you invoke this command in the emacs-w3m buffer, the new session
will be created by copying the current session.  Otherwise, the new
session will start afresh." t nil)

(autoload (quote w3m-gohome) "w3m" "\
Go to the Home page." t nil)

(autoload (quote w3m) "w3m" "\
Visit World Wide Web pages using the external w3m command.

When you invoke this command interactively for the first time, it will
visit a page which is pointed to by a string like url around the
cursor position or the home page specified by the `w3m-home-page'
variable, but you will be prompted for a URL if `w3m-quick-start' is
nil (default t) or `w3m-home-page' is nil.

The variables `w3m-pop-up-windows' and `w3m-pop-up-frames' control
whether this command should pop to a window or a frame up for the
session.

When emacs-w3m sessions have already been opened, this command will
pop to the existing window or frame up, but if `w3m-quick-start' is
nil, (default t), you will be prompted for a URL (which defaults to
`popup' meaning to pop to an existing emacs-w3m buffer up).

In addition, if the prefix argument is given or you enter the empty
string for the prompt, it will visit the home page specified by the
`w3m-home-page' variable or the \"about:\" page.

You can also run this command in the batch mode as follows:

  emacs -f w3m http://emacs-w3m.namazu.org/ &

In that case, or if this command is called non-interactively, the
variables `w3m-pop-up-windows' and `w3m-pop-up-frames' will be ignored
\(treated as nil) and it will run emacs-w3m at the current (or the
initial) window.

If the optional NEW-SESSION is non-nil, this function makes a new
emacs-w3m buffer.  Besides that, it also makes a new emacs-w3m buffer
if `w3m-make-new-session' is non-nil and a user specifies a url string.

The optional INTERACTIVE-P is for the internal use; it is mainly used
to check whether Emacs 22 or later calls this function as an
interactive command in the batch mode." t nil)

(autoload (quote w3m-browse-url) "w3m" "\
Ask emacs-w3m to browse URL.
NEW-SESSION specifies whether to create a new emacs-w3m session.  URL
defaults to the string looking like a url around the cursor position.
Pop to a window or a frame up according to `w3m-pop-up-windows' and
`w3m-pop-up-frames'." t nil)

(autoload (quote w3m-find-file) "w3m" "\
Function used to open FILE whose name is expressed in ordinary format.
The file name will be converted into the file: scheme." t nil)

(autoload (quote w3m-region) "w3m" "\
Render the region of the current buffer between START and END.
URL specifies the address where the contents come from.  It can be
omitted or nil when the address is not identified.  CHARSET is used
for decoding the contents.  If it is nil, this function attempts to
parse the meta tag to extract the charset." t nil)

;;;***

;;;### (autoloads (w3m-antenna w3m-about-antenna) "w3m-antenna" "site-lisp/emacs-w3m/w3m-antenna.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-antenna.el

(autoload (quote w3m-about-antenna) "w3m-antenna" nil nil nil)

(autoload (quote w3m-antenna) "w3m-antenna" "\
Report changes of WEB sites, which is specified in `w3m-antenna-sites'." t nil)

;;;***

;;;### (autoloads (w3m-about-bookmark w3m-bookmark-view w3m-bookmark-add-current-url-group
;;;;;;  w3m-bookmark-add-current-url w3m-bookmark-add-this-url) "w3m-bookmark"
;;;;;;  "site-lisp/emacs-w3m/w3m-bookmark.el" (18090 5606))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-bookmark.el

(autoload (quote w3m-bookmark-add-this-url) "w3m-bookmark" "\
Add link under cursor to bookmark." t nil)

(autoload (quote w3m-bookmark-add-current-url) "w3m-bookmark" "\
Add link of current page to bookmark.
With prefix, ask new url to add instead of current page." t nil)

(autoload (quote w3m-bookmark-add-current-url-group) "w3m-bookmark" "\
Add link of the group of current urls to the bookmark." t nil)

(autoload (quote w3m-bookmark-view) "w3m-bookmark" nil t nil)

(autoload (quote w3m-about-bookmark) "w3m-bookmark" nil nil nil)

;;;***

;;;### (autoloads (w3m-about-cookie w3m-cookie w3m-cookie-get w3m-cookie-set
;;;;;;  w3m-cookie-shutdown) "w3m-cookie" "site-lisp/emacs-w3m/w3m-cookie.el"
;;;;;;  (18090 5606))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-cookie.el

(autoload (quote w3m-cookie-shutdown) "w3m-cookie" "\
Save cookies." t nil)

(autoload (quote w3m-cookie-set) "w3m-cookie" "\
Register cookies which correspond to URL.
BEG and END should be an HTTP response header region on current buffer." nil nil)

(autoload (quote w3m-cookie-get) "w3m-cookie" "\
Get a cookie field string which corresponds to the URL." nil nil)

(autoload (quote w3m-cookie) "w3m-cookie" "\
Display cookies and enable you to manage them." t nil)

(autoload (quote w3m-about-cookie) "w3m-cookie" "\
Make the html contents to display and to enable you to manage cookies." nil nil)

;;;***

;;;### (autoloads (w3m-dtree w3m-about-dtree) "w3m-dtree" "site-lisp/emacs-w3m/w3m-dtree.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-dtree.el

(autoload (quote w3m-about-dtree) "w3m-dtree" nil nil nil)

(autoload (quote w3m-dtree) "w3m-dtree" "\
Display directory tree on local file system.
If called with 'prefix argument', display all directorys and files." t nil)

;;;***

;;;### (autoloads (w3m-filter) "w3m-filter" "site-lisp/emacs-w3m/w3m-filter.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-filter.el

(autoload (quote w3m-filter) "w3m-filter" "\
Apply filtering rule of URL against a content in this buffer." nil nil)

;;;***

;;;### (autoloads (w3m-fontify-forms) "w3m-form" "site-lisp/emacs-w3m/w3m-form.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-form.el

(autoload (quote w3m-fontify-forms) "w3m-form" "\
Process half-dumped data and fontify forms in this buffer." nil nil)

;;;***

;;;### (autoloads (w3m-link-numbering-mode) "w3m-lnum" "site-lisp/emacs-w3m/w3m-lnum.el"
;;;;;;  (18090 5606))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-lnum.el

(autoload (quote w3m-link-numbering-mode) "w3m-lnum" "\
Minor mode to enable operations using link numbers." t nil)

;;;***

;;;### (autoloads (w3m-namazu w3m-about-namazu) "w3m-namazu" "site-lisp/emacs-w3m/w3m-namazu.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-namazu.el

(autoload (quote w3m-about-namazu) "w3m-namazu" nil nil nil)

(autoload (quote w3m-namazu) "w3m-namazu" "\
Search indexed files with Namazu." t nil)

;;;***

;;;### (autoloads (w3m-perldoc w3m-about-perldoc) "w3m-perldoc" "site-lisp/emacs-w3m/w3m-perldoc.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-perldoc.el

(autoload (quote w3m-about-perldoc) "w3m-perldoc" nil nil nil)

(autoload (quote w3m-perldoc) "w3m-perldoc" "\
View Perl documents." t nil)

;;;***

;;;### (autoloads (w3m-search-uri-replace w3m-search) "w3m-search"
;;;;;;  "site-lisp/emacs-w3m/w3m-search.el" (18090 5606))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-search.el

(autoload (quote w3m-search) "w3m-search" "\
Search QUERY using SEARCH-ENGINE.
When called interactively with a prefix argument, you can choose one of
the search engines defined in `w3m-search-engine-alist'.  Otherwise use
`w3m-search-default-engine'.
If Transient Mark mode, use the region as an initial string of query
and deactivate the mark." t nil)

(autoload (quote w3m-search-uri-replace) "w3m-search" "\
Generate query string for ENGINE from URI matched by last search." nil nil)

;;;***

;;;### (autoloads (w3m-replace-symbol) "w3m-symbol" "site-lisp/emacs-w3m/w3m-symbol.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-symbol.el

(autoload (quote w3m-replace-symbol) "w3m-symbol" nil nil nil)

;;;***

;;;### (autoloads (w3m-about-weather w3m-weather) "w3m-weather" "site-lisp/emacs-w3m/w3m-weather.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-weather.el

(autoload (quote w3m-weather) "w3m-weather" "\
Display weather report." t nil)

(autoload (quote w3m-about-weather) "w3m-weather" nil nil nil)

;;;***

;;;### (autoloads (xdarcs-revision-get-last-revision xdarcs-whatsnew)
;;;;;;  "xdarcs" "site-lisp/dvc-snapshot/lisp/xdarcs.el" (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xdarcs.el

(autoload (quote xdarcs-whatsnew) "xdarcs" "\
Run darcs whatsnew." t nil)

(autoload (quote xdarcs-revision-get-last-revision) "xdarcs" "\
Insert the content of FILE in LAST-REVISION, in current buffer.

LAST-REVISION looks like
\(\"path\" NUM)" nil nil)

;;;***

;;;### (autoloads (xdarcs-tree-root) "xdarcs-core" "site-lisp/dvc-snapshot/lisp/xdarcs-core.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xdarcs-core.el

(autoload (quote xdarcs-tree-root) "xdarcs-core" "\
Return the tree root for LOCATION, nil if not in a local tree.
Computation is done from withing Emacs, by looking at an _darcs/
directory in a parent buffer of LOCATION.  This is therefore very
fast.

If NO-ERROR is non-nil, don't raise an error if LOCATION is not a
git managed tree (but return nil)." nil nil)

;;;***

;;;### (autoloads nil "xdarcs-dvc" "site-lisp/dvc-snapshot/lisp/xdarcs-dvc.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xdarcs-dvc.el

(dvc-register-dvc (quote xdarcs) "Darcs")

(defalias (quote xdarcs-dvc-tree-root) (quote xdarcs-tree-root))

(defalias (quote xdarcs-dvc-command-version) (quote xdarcs-command-version))

(defalias (quote xdarcs-dvc-status) (quote xdarcs-whatsnew))

;;;***

;;;### (autoloads (xgit-revision-get-last-revision xgit-apply-mbox
;;;;;;  xgit-add-all-files xgit-add xgit-clone xgit-init) "xgit"
;;;;;;  "site-lisp/dvc-snapshot/lisp/xgit.el" (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xgit.el

(autoload (quote xgit-init) "xgit" "\
Run git init." t nil)

(autoload (quote xgit-clone) "xgit" "\
Run git clone." t nil)

(autoload (quote xgit-add) "xgit" "\
Add FILE to the current git project." t nil)

(autoload (quote xgit-add-all-files) "xgit" "\
Run 'git add .' to add all files to git.

Normally run 'git add -n .' to simulate the operation to see
which files will be added.

Only when called with a prefix argument, add the files." t nil)

(autoload (quote xgit-apply-mbox) "xgit" "\
Run git am to apply the contents of MBOX as one or more patches." t nil)

(autoload (quote xgit-revision-get-last-revision) "xgit" "\
Insert the content of FILE in LAST-REVISION, in current buffer.

LAST-REVISION looks like
\(\"path\" NUM)" nil nil)

;;;***

;;;### (autoloads (xgit-prepare-environment xgit-tree-root) "xgit-core"
;;;;;;  "site-lisp/dvc-snapshot/lisp/xgit-core.el" (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xgit-core.el

(autoload (quote xgit-tree-root) "xgit-core" "\
Return the tree root for LOCATION, nil if not in a local tree.
Computation is done from withing Emacs, by looking at an .git/
directory in a parent buffer of LOCATION.  This is therefore very
fast.

If NO-ERROR is non-nil, don't raise an error if LOCATION is not a
git managed tree (but return nil)." nil nil)

(autoload (quote xgit-prepare-environment) "xgit-core" "\
Prepare the environment to run git." nil nil)

;;;***

;;;### (autoloads (xgit-dvc-log xgit-dvc-status) "xgit-dvc" "site-lisp/dvc-snapshot/lisp/xgit-dvc.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xgit-dvc.el

(dvc-register-dvc (quote xgit) "git")

(defalias (quote xgit-dvc-tree-root) (quote xgit-tree-root))

(autoload (quote xgit-dvc-status) "xgit-dvc" nil nil nil)

(defalias (quote xgit-dvc-command-version) (quote xgit-command-version))

(autoload (quote xgit-dvc-log) "xgit-dvc" "\
Shows the changelog in the current git tree.
ARG is passed as prefix argument" nil nil)

;;;***

;;;### (autoloads (xgit-insinuate-gnus) "xgit-gnus" "site-lisp/dvc-snapshot/lisp/xgit-gnus.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xgit-gnus.el

(autoload (quote xgit-insinuate-gnus) "xgit-gnus" "\
Integrate Xgit into Gnus.
The following keybindings are installed for gnus-summary:
K t s `xgit-gnus-article-view-status-for-apply-patch'
K t v `xgit-gnus-article-view-patch'

The following keybindings are ignored:
K t l" t nil)

;;;***

;;;### (autoloads (xgit-log) "xgit-log" "site-lisp/dvc-snapshot/lisp/xgit-log.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xgit-log.el

(autoload (quote xgit-log) "xgit-log" "\
Run git log for DIR.
DIR is a directory controlled by Git/Cogito.
CNT is max number of log to print.  If not specified, uses git-log-max-count.
LOG-REGEXP is regexp to filter logs by matching commit logs.
DIFF-MATCH is string to filter logs by matching commit diffs.
REV is revision to show.
FILE is filename in repostory to filter logs by matching filename." t nil)

;;;***

;;;### (autoloads (xhg-missing xhg-revision-get-last-revision xhg-update
;;;;;;  xhg-undo xhg-import xhg-export xhg-view xhg-annotate xhg-tags
;;;;;;  xhg-paths xhg-showconfig xhg-verify xhg-identify xhg-parents
;;;;;;  xhg-heads xhg-tip xhg-incoming xhg-clone xhg-pull xhg-status
;;;;;;  xhg-diff xhg-log xhg-add-all-files xhg-forget xhg-rename
;;;;;;  xhg-addremove xhg-init) "xhg" "site-lisp/dvc-snapshot/lisp/xhg.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xhg.el

(autoload (quote xhg-init) "xhg" "\
Run hg init." t nil)

(autoload (quote xhg-addremove) "xhg" "\
Run hg addremove." t nil)

(autoload (quote xhg-rename) "xhg" "\
Run hg rename." t nil)

(autoload (quote xhg-forget) "xhg" "\
Run hg forget." t nil)

(autoload (quote xhg-add-all-files) "xhg" "\
Run 'hg add' to add all files to mercurial.
Normally run 'hg add -n' to simulate the operation to see which files will be added.
Only when called with a prefix argument, add the files." t nil)

(autoload (quote xhg-log) "xhg" "\
Run hg log.
When run interactively, the prefix argument decides, which parameters are queried from the user.
C-u      : Show patches also, use all revisions
C-u C-u  : Show patches also, ask for revisions
positive : Don't show patches, ask for revisions.
negative : Don't show patches, limit to n revisions." t nil)

(autoload (quote xhg-diff) "xhg" "\
Run hg diff.
If DONT-SWITCH, don't switch to the diff buffer" t nil)

(autoload (quote xhg-status) "xhg" "\
Run hg status." t nil)

(autoload (quote xhg-pull) "xhg" "\
Run hg pull." t nil)

(autoload (quote xhg-clone) "xhg" "\
Run hg clone." t nil)

(autoload (quote xhg-incoming) "xhg" "\
Run hg incoming." t nil)

(autoload (quote xhg-tip) "xhg" "\
Run hg tip." t nil)

(autoload (quote xhg-heads) "xhg" "\
Run hg heads." t nil)

(autoload (quote xhg-parents) "xhg" "\
Run hg parents." t nil)

(autoload (quote xhg-identify) "xhg" "\
Run hg identify." t nil)

(autoload (quote xhg-verify) "xhg" "\
Run hg verify." t nil)

(autoload (quote xhg-showconfig) "xhg" "\
Run hg showconfig." t nil)

(autoload (quote xhg-paths) "xhg" "\
Run hg paths.
When called interactive, display them in an *xhg-info* buffer.
Otherwise the return value depends on TYPE:
'alias:    Return only alias names
'path:     Return only the paths
'both      Return the aliases and the paths in a flat list
otherwise: Return a list of two element sublists containing alias, path" t nil)

(autoload (quote xhg-tags) "xhg" "\
Run hg tags." t nil)

(autoload (quote xhg-annotate) "xhg" "\
Run hg annotate." t nil)

(autoload (quote xhg-view) "xhg" "\
Run hg view." t nil)

(autoload (quote xhg-export) "xhg" "\
Run hg export.
`xhg-export-git-style-patches' determines, if git style patches are created." t nil)

(autoload (quote xhg-import) "xhg" "\
Run hg import." t nil)

(autoload (quote xhg-undo) "xhg" "\
Run hg undo." t nil)

(autoload (quote xhg-update) "xhg" "\
Run hg update." t nil)

(autoload (quote xhg-revision-get-last-revision) "xhg" "\
Insert the content of FILE in LAST-REVISION, in current buffer.

LAST-REVISION looks like
\(\"path\" NUM)" nil nil)

(autoload (quote xhg-missing) "xhg" "\
Shows the logs of the new arrived changesets after a pull and before an update." t nil)

;;;***

;;;### (autoloads (xhg-tree-root) "xhg-core" "site-lisp/dvc-snapshot/lisp/xhg-core.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xhg-core.el

(autoload (quote xhg-tree-root) "xhg-core" "\
Return the tree root for LOCATION, nil if not in a local tree.
Computation is done from withing Emacs, by looking at an .hg/
directory in a parent buffer of LOCATION.  This is therefore very
fast.

If NO-ERROR is non-nil, don't raise an error if LOCATION is not a
mercurial managed tree (but return nil)." nil nil)

;;;***

;;;### (autoloads (xhg-dvc-status) "xhg-dvc" "site-lisp/dvc-snapshot/lisp/xhg-dvc.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xhg-dvc.el

(dvc-register-dvc (quote xhg) "Mercurial")

(defalias (quote xhg-dvc-tree-root) (quote xhg-tree-root))

(defalias (quote xhg-dvc-diff) (quote xhg-diff))

(defalias (quote xhg-dvc-save-diff) (quote xhg-save-diff))

(autoload (quote xhg-dvc-status) "xhg-dvc" nil nil nil)

(defalias (quote xhg-dvc-command-version) (quote xhg-command-version))

;;;***

;;;### (autoloads (xhg-insinuate-gnus) "xhg-gnus" "site-lisp/dvc-snapshot/lisp/xhg-gnus.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xhg-gnus.el

(autoload (quote xhg-insinuate-gnus) "xhg-gnus" "\
Integrate Xhg into Gnus.
The following keybindings are installed for gnus-summary:
K t s `xhg-gnus-article-view-status-for-import-patch'" t nil)

;;;***

;;;### (autoloads (xhg-mq-show-stack xhg-mq-export-via-mail xhg-qheader
;;;;;;  xhg-qprev xhg-qnext xhg-qtop xhg-qversion xhg-qrename xhg-qdelete
;;;;;;  xhg-qdiff xhg-qseries xhg-qunapplied xhg-qapplied xhg-qpush
;;;;;;  xhg-qpop xhg-qrefresh xhg-qnew xhg-qinit) "xhg-mq" "site-lisp/dvc-snapshot/lisp/xhg-mq.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xhg-mq.el

(autoload (quote xhg-qinit) "xhg-mq" "\
Run hg qinit.
When called without a prefix argument run hg qinit -c, otherwise hg qinit." t nil)

(autoload (quote xhg-qnew) "xhg-mq" "\
Run hg qnew.
Asks for the patch name and an optional commit description.
If the commit description is not empty, run hg qnew -m \"commit description\"
When called with a prefix argument run hg qnew -f." t nil)

(autoload (quote xhg-qrefresh) "xhg-mq" "\
Run hg qrefresh." t nil)

(autoload (quote xhg-qpop) "xhg-mq" "\
Run hg qpop.
When called with a prefix argument run hg qpop -a." t nil)

(autoload (quote xhg-qpush) "xhg-mq" "\
Run hg qpush.
When called with a prefix argument run hg qpush -a." t nil)

(autoload (quote xhg-qapplied) "xhg-mq" "\
Run hg qapplied." t nil)

(autoload (quote xhg-qunapplied) "xhg-mq" "\
Run hg qunapplied." t nil)

(autoload (quote xhg-qseries) "xhg-mq" "\
Run hg qseries." t nil)

(autoload (quote xhg-qdiff) "xhg-mq" "\
Run hg qdiff." t nil)

(autoload (quote xhg-qdelete) "xhg-mq" "\
Run hg qdelete" t nil)

(autoload (quote xhg-qrename) "xhg-mq" "\
Run hg qrename" t nil)

(autoload (quote xhg-qversion) "xhg-mq" "\
Run hg qversion." t nil)

(autoload (quote xhg-qtop) "xhg-mq" "\
Run hg qtop." t nil)

(autoload (quote xhg-qnext) "xhg-mq" "\
Run hg qnext." t nil)

(autoload (quote xhg-qprev) "xhg-mq" "\
Run hg qprev." t nil)

(autoload (quote xhg-qheader) "xhg-mq" "\
Run hg qheader." t nil)

(autoload (quote xhg-mq-export-via-mail) "xhg-mq" "\
Prepare an email that contains a mq patch.
`xhg-submit-patch-mapping' is honored for the destination email address and the project name
that is used in the generated email." t nil)

(autoload (quote xhg-mq-show-stack) "xhg-mq" "\
Show the mq stack." t nil)

;;;***

;;;### (autoloads (xhg-dvc-log) "xhg-revision" "site-lisp/dvc-snapshot/lisp/xhg-revision.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xhg-revision.el

(autoload (quote xhg-dvc-log) "xhg-revision" "\
Show a dvc formatted log for xhg." t nil)

;;;***

;;;### (autoloads (xmltok-get-declared-encoding-position) "xmltok"
;;;;;;  "site-lisp/nxml-mode/xmltok.el" (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/xmltok.el

(autoload (quote xmltok-get-declared-encoding-position) "xmltok" "\
Return the position of the encoding in the XML declaration at point.
If there is a well-formed XML declaration starting at point and it
contains an encoding declaration, then return (START . END)
where START and END are the positions of the start and the end
of the encoding name; if there is no encoding declaration return
the position where and encoding declaration could be inserted.
If there is XML that is not well-formed that looks like an XML declaration,
return nil.  Otherwise, return t.
If LIMIT is non-nil, then do not consider characters beyond LIMIT." nil nil)

;;;***

;;;### (autoloads (xmtn-dvc-revision-nth-ancestor xmtn-dvc-file-diff
;;;;;;  xmtn-revision-get-file-revision xmtn-revision-get-last-revision
;;;;;;  xmtn-revision-get-previous-revision xmtn-dvc-files-to-commit
;;;;;;  xmtn-dvc-revert-files xmtn-dvc-pull xmtn-dvc-update xmtn-send-enter-to-subprocess
;;;;;;  xmtn-dvc-rename xmtn-dvc-remove-files xmtn-dvc-add xmtn-dvc-add-files
;;;;;;  xmtn-dvc-backend-ignore-file-extensions-in-dir xmtn-dvc-backend-ignore-file-extensions
;;;;;;  xmtn-dvc-ignore-files xmtn-dvc-edit-ignore-files xmtn-dvc-name-construct
;;;;;;  xmtn-dvc-revision-direct-ancestor xmtn-dvc-status xmtn-dvc-command-version
;;;;;;  xmtn-dvc-diff xmtn-dvc-search-file-in-diff xmtn-show-base-revision
;;;;;;  xmtn-dvc-log-edit-done xmtn-dvc-log-edit xmtn-dvc-log-edit-file-name-func)
;;;;;;  "xmtn-dvc" "site-lisp/dvc-snapshot/lisp/xmtn-dvc.el" (18148
;;;;;;  40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xmtn-dvc.el

(dvc-register-dvc (quote xmtn) "monotone")

(autoload (quote xmtn-dvc-log-edit-file-name-func) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-log-edit) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-log-edit-done) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-show-base-revision) "xmtn-dvc" "\
Show the base revision of the current monotone tree in the minibuffer." t nil)

(autoload (quote xmtn-dvc-search-file-in-diff) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-diff) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-command-version) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-status) "xmtn-dvc" "\
Display status of monotone tree ROOT (default current tree)." nil nil)

(autoload (quote xmtn-dvc-revision-direct-ancestor) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-name-construct) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-edit-ignore-files) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-ignore-files) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-backend-ignore-file-extensions) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-backend-ignore-file-extensions-in-dir) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-add-files) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-add) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-remove-files) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-rename) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-send-enter-to-subprocess) "xmtn-dvc" "\
Send an \"enter\" keystroke to a monotone subprocess.

To be used in an xmtn process buffer.  Useful when monotone
spawns an external merger and asks you to hit enter when
finished." t nil)

(autoload (quote xmtn-dvc-update) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-pull) "xmtn-dvc" "\
Implement `dvc-pull' for xmtn." nil nil)

(autoload (quote xmtn-dvc-revert-files) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-files-to-commit) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-revision-get-previous-revision) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-revision-get-last-revision) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-revision-get-file-revision) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-file-diff) "xmtn-dvc" nil nil nil)

(autoload (quote xmtn-dvc-revision-nth-ancestor) "xmtn-dvc" nil nil nil)

;;;***

;;;### (autoloads (xmtn-match--test) "xmtn-match" "site-lisp/dvc-snapshot/lisp/xmtn-match.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xmtn-match.el

(autoload (quote xmtn-match--test) "xmtn-match" nil nil nil)

;;;***

;;;### (autoloads (xmtn-tree-root) "xmtn-minimal" "site-lisp/dvc-snapshot/lisp/xmtn-minimal.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xmtn-minimal.el

(autoload (quote xmtn-tree-root) "xmtn-minimal" nil nil nil)

;;;***

;;;### (autoloads (xmtn-dvc-revlog-mode xmtn-dvc-delta xmtn-dvc-revlog-get-revision
;;;;;;  xmtn-view-revlist-for-selector xmtn-list-revisions-modifying-file
;;;;;;  xmtn-view-heads-revlist xmtn-dvc-missing xmtn-dvc-changelog
;;;;;;  xmtn-dvc-log xmtn-revision-list-entry-patch-printer xmtn-revision-refresh-maybe)
;;;;;;  "xmtn-revlist" "site-lisp/dvc-snapshot/lisp/xmtn-revlist.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xmtn-revlist.el

(autoload (quote xmtn-revision-refresh-maybe) "xmtn-revlist" nil nil nil)

(autoload (quote xmtn-revision-list-entry-patch-printer) "xmtn-revlist" nil nil nil)

(autoload (quote xmtn-dvc-log) "xmtn-revlist" nil nil nil)

(autoload (quote xmtn-dvc-changelog) "xmtn-revlist" nil nil nil)

(autoload (quote xmtn-dvc-missing) "xmtn-revlist" nil nil nil)

(autoload (quote xmtn-view-heads-revlist) "xmtn-revlist" "\
Display a revlist buffer showing the heads of the current branch." t nil)

(autoload (quote xmtn-list-revisions-modifying-file) "xmtn-revlist" "\
Display a revlist buffer showing the revisions that modify FILE.

Only ancestors of revision LAST-BACKEND-ID will be considered.
FILE is a file name in revision LAST-BACKEND-ID, which defaults
to the base revision of the current tree." t nil)

(autoload (quote xmtn-view-revlist-for-selector) "xmtn-revlist" "\
Display a revlist buffer showing the revisions matching SELECTOR." t nil)

(autoload (quote xmtn-dvc-revlog-get-revision) "xmtn-revlist" nil nil nil)

(autoload (quote xmtn-dvc-delta) "xmtn-revlist" nil nil nil)

(autoload (quote xmtn-dvc-revlog-mode) "xmtn-revlist" nil nil nil)

;;;***

;;;### (autoloads (xmtn-check-command-version) "xmtn-run" "site-lisp/dvc-snapshot/lisp/xmtn-run.el"
;;;;;;  (18148 40140))
;;; Generated autoloads from site-lisp/dvc-snapshot/lisp/xmtn-run.el

(autoload (quote xmtn-check-command-version) "xmtn-run" "\
Check and display the version identifier of the mtn command.

This command resets xmtn's command version cache." t nil)

;;;***

;;;### (autoloads (c-includes c-includes-current-file c-includes-add-binding)
;;;;;;  "c-includes" "c-includes.el" (14822 57866))
;;; Generated autoloads from c-includes.el

(autoload (quote c-includes-add-binding) "c-includes" "\
Set binding for C-c C-i in cc-mode." nil nil)

(autoload (quote c-includes-current-file) "c-includes" "\
Find all of the header file included by the current file." t nil)

(autoload (quote c-includes) "c-includes" "\
Find all of the header files included by FILENAME.
REGEXP, if non-nil, is a regular expression to search for within
FILENAME and the files that it includes.  The output will be
structured in the same order that the compiler will see it, enabling
you determine order of occurrence." t nil)

;;;***
