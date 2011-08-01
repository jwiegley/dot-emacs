;;; -*-emacs-lisp-*-
;;; autoloads.in --- define autoloads for a lisp directory

(eval-when-compile
  (require 'cl))

(defvar generated-autoload-file)

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

;;;### (autoloads nil "_pkg" "site-lisp/eshell/_pkg.el" (18807 50473))
;;; Generated autoloads from site-lisp/eshell/_pkg.el

(if (fboundp 'package-provide) (package-provide 'eshell :version 2.5 :type 'regular))

;;;***

;;;### (autoloads (vassoc set-modified-alist modify-alist remove-alist
;;;;;;  set-alist del-alist put-alist) "alist" "site-lisp/apel/alist.el"
;;;;;;  (19385 28150))
;;; Generated autoloads from site-lisp/apel/alist.el

(autoload 'put-alist "alist" "\
Set cdr of an element (KEY . ...) in ALIST to VALUE and return ALIST.
If there is no such element, create a new pair (KEY . VALUE) and
return a new alist whose car is the new pair and cdr is ALIST.

\(fn KEY VALUE ALIST)" nil nil)

(autoload 'del-alist "alist" "\
Delete an element whose car equals KEY from ALIST.
Return the modified ALIST.

\(fn KEY ALIST)" nil nil)

(autoload 'set-alist "alist" "\
Set cdr of an element (KEY . ...) in the alist bound to SYMBOL to VALUE.

\(fn SYMBOL KEY VALUE)" nil nil)

(autoload 'remove-alist "alist" "\
Delete an element whose car equals KEY from the alist bound to SYMBOL.

\(fn SYMBOL KEY)" nil nil)

(autoload 'modify-alist "alist" "\
Store elements in the alist MODIFIER in the alist DEFAULT.
Return the modified alist.

\(fn MODIFIER DEFAULT)" nil nil)

(autoload 'set-modified-alist "alist" "\
Store elements in the alist MODIFIER in an alist bound to SYMBOL.
If SYMBOL is not bound, set it to nil at first.

\(fn SYMBOL MODIFIER)" nil nil)

(autoload 'vassoc "alist" "\
Search AVLIST for an element whose first element equals KEY.
AVLIST is a list of vectors.
See also `assoc'.

\(fn KEY AVLIST)" nil nil)

;;;***

;;;### (autoloads (all) "all" "site-lisp/all.el" (18429 49075))
;;; Generated autoloads from site-lisp/all.el

(autoload 'all "all" "\
Show all lines in the current buffer containing a match for REGEXP.

If a match spreads across multiple lines, all those lines are shown.

Each line is displayed with NLINES lines before and after, or -NLINES
before if NLINES is negative.
NLINES defaults to `list-matching-lines-default-context-lines'.
Interactively it is the prefix arg.

The lines are shown in a buffer named `*All*'.
Any changes made in that buffer will be propagated to this buffer.

\(fn REGEXP &optional NLINES)" t nil)

;;;***

;;;### (autoloads (anything-other-buffer anything-at-point anything)
;;;;;;  "anything" "site-lisp/anything/anything.el" (20019 11640))
;;; Generated autoloads from site-lisp/anything/anything.el

(autoload 'anything "anything" "\
Select anything. In Lisp program, some optional arguments can be used.

PLIST is a list like (:key1 val1 :key2 val2 ...) or
 (&optional sources input prompt resume preselect buffer keymap).

Basic keywords are the following:

- :sources

  Temporary value of `anything-sources'.  It also accepts a
  symbol, interpreted as a variable of an anything source.  It
  also accepts an alist representing an anything source, which is
  detected by (assq 'name ANY-SOURCES)

- :input

  Temporary value of `anything-pattern', ie. initial input of minibuffer.

- :prompt

  Prompt other than \"pattern: \".

- :resume

  If t, Resurrect previously instance of `anything'. Skip the initialization.
  If 'noresume, this instance of `anything' cannot be resumed.

- :preselect

  Initially selected candidate. Specified by exact candidate or a regexp.
  Note that it is not working with delayed sources.

- :buffer

  `anything-buffer' instead of *anything*.

- :keymap

  `anything-map' for current `anything' session.


Of course, conventional arguments are supported, the two are same.

 (anything :sources sources :input input :prompt prompt :resume resume
           :preselect preselect :buffer buffer :keymap keymap)
 (anything sources input prompt resume preselect buffer keymap)
           

Other keywords are interpreted as local variables of this anything session.
The `anything-' prefix can be omitted. For example,

 (anything :sources 'anything-c-source-buffers
           :buffer \"*buffers*\" :candidate-number-limit 10)

means starting anything session with `anything-c-source-buffers'
source in *buffers* buffer and set
`anything-candidate-number-limit' to 10 as session local variable. 

\(fn &rest PLIST)" t nil)

(autoload 'anything-at-point "anything" "\
Same as `anything' except when C-u is pressed, the initial input is the symbol at point.

\(fn &optional ANY-SOURCES ANY-INPUT ANY-PROMPT ANY-RESUME ANY-PRESELECT ANY-BUFFER)" t nil)

(autoload 'anything-other-buffer "anything" "\
Simplified interface of `anything' with other `anything-buffer'

\(fn ANY-SOURCES ANY-BUFFER)" nil nil)

;;;***

;;;### (autoloads (anything-c-reset-adaptative-history anything-c-set-variable
;;;;;;  anything-c-call-interactively w32-shell-execute-open-file
;;;;;;  anything-ratpoison-commands anything-c-run-external-command
;;;;;;  anything-c-complete-file-name-at-point anything-lisp-completion-at-point-or-indent
;;;;;;  anything-lisp-completion-at-point anything-esh-pcomplete
;;;;;;  anything-completion-mode anything-c-shell-command-if-needed
;;;;;;  anything-apt anything-world-time anything-select-xfont anything-top
;;;;;;  anything-create anything-execute-anything-command anything-call-source
;;;;;;  anything-surfraw anything-calcul-expression anything-eval-expression-with-eldoc
;;;;;;  anything-eval-expression anything-yaoddmuse-emacswiki-post-library
;;;;;;  anything-yaoddmuse-emacswiki-edit-or-view anything-yaoddmuse-cache-pages
;;;;;;  anything-all-mark-rings anything-global-mark-ring anything-mark-ring
;;;;;;  anything-simple-call-tree anything-bookmark-ext anything-manage-advice
;;;;;;  anything-M-x anything-filelist+ anything-filelist anything-etags-help
;;;;;;  anything-yank-text-at-point anything-pdfgrep-help anything-grep-help
;;;;;;  anything-c-goto-next-file anything-c-goto-precedent-file
;;;;;;  anything-do-zgrep anything-do-grep anything-dired-mode anything-dired-hardlink-file
;;;;;;  anything-dired-symlink-file anything-dired-copy-file anything-dired-rename-file
;;;;;;  anything-insert-file anything-write-file anything-find-files
;;;;;;  anything-ff-run-kill-buffer-persistent anything-ff-properties-persistent
;;;;;;  anything-ff-run-print-file anything-ff-run-gnus-attach-files
;;;;;;  anything-ff-run-open-file-externally anything-ff-run-switch-other-frame
;;;;;;  anything-ff-run-switch-other-window anything-ff-run-switch-to-eshell
;;;;;;  anything-ff-run-complete-fn-at-point anything-ff-run-delete-file
;;;;;;  anything-ff-run-symlink-file anything-ff-run-ediff-merge-file
;;;;;;  anything-ff-run-ediff-file anything-ff-run-eshell-command-on-file
;;;;;;  anything-ff-run-load-file anything-ff-run-byte-compile-file
;;;;;;  anything-ff-run-rename-file anything-ff-run-copy-file anything-ff-run-zgrep
;;;;;;  anything-ff-run-pdfgrep anything-ff-run-grep anything-ff-run-switch-to-history
;;;;;;  anything-ff-run-toggle-auto-update anything-buffer-switch-to-elscreen
;;;;;;  anything-buffer-switch-other-frame anything-buffer-switch-other-window
;;;;;;  anything-buffer-run-query-replace anything-buffer-run-query-replace-regexp
;;;;;;  anything-buffer-run-zgrep anything-buffer-run-grep anything-buffer-run-kill-buffers
;;;;;;  anything-buffer-save-persistent anything-buffer-revert-persistent
;;;;;;  anything-buffer-diff-persistent anything-toggle-all-marks
;;;;;;  anything-unmark-all anything-mark-all anything-regexp anything-kill-buffers
;;;;;;  anything-info-gnus anything-org-headlines anything-browse-code
;;;;;;  anything-occur anything-list-emacs-process anything-timers
;;;;;;  anything-bm-list anything-eev-anchors anything-emms anything-org-keywords
;;;;;;  anything-man-woman anything-register anything-c-insert-latex-math
;;;;;;  anything-c-pp-bookmarks anything-bookmarks anything-colors
;;;;;;  anything-firefox-bookmarks anything-w3m-bookmarks anything-locate
;;;;;;  anything-bbdb anything-buffers+ anything-for-buffers anything-yahoo-suggest
;;;;;;  anything-google-suggest anything-imenu anything-gentoo anything-minibuffer-history
;;;;;;  anything-show-kill-ring anything-info-emacs anything-info-at-point
;;;;;;  anything-recentf anything-for-files anything-mini anything-configuration)
;;;;;;  "anything-config" "site-lisp/anything/anything-config.el"
;;;;;;  (20019 11640))
;;; Generated autoloads from site-lisp/anything/anything-config.el

(autoload 'anything-configuration "anything-config" "\
Customize `anything'.

\(fn)" t nil)

(defvar anything-command-map)

(autoload 'anything-mini "anything-config" "\
Preconfigured `anything' lightweight version (buffer -> recentf).

\(fn)" t nil)

(autoload 'anything-for-files "anything-config" "\
Preconfigured `anything' for opening files.
ffap -> recentf -> buffer -> bookmark -> file-cache -> files-in-current-dir -> locate

\(fn)" t nil)

(autoload 'anything-recentf "anything-config" "\
Preconfigured `anything' for `recentf'.

\(fn)" t nil)

(autoload 'anything-info-at-point "anything-config" "\
Preconfigured `anything' for searching info at point.
With a prefix-arg insert symbol at point.

\(fn ARG)" t nil)

(autoload 'anything-info-emacs "anything-config" "\
Preconfigured anything for Emacs manual index.

\(fn)" t nil)

(autoload 'anything-show-kill-ring "anything-config" "\
Preconfigured `anything' for `kill-ring'.
It is drop-in replacement of `yank-pop'.
You may bind this command to M-y.
First call open the kill-ring browser, next calls move to next line.

\(fn)" t nil)

(autoload 'anything-minibuffer-history "anything-config" "\
Preconfigured `anything' for `minibuffer-history'.

\(fn)" t nil)

(autoload 'anything-gentoo "anything-config" "\
Preconfigured `anything' for gentoo linux.

\(fn)" t nil)

(autoload 'anything-imenu "anything-config" "\
Preconfigured `anything' for `imenu'.

\(fn)" t nil)

(autoload 'anything-google-suggest "anything-config" "\
Preconfigured `anything' for google search with google suggest.

\(fn)" t nil)

(autoload 'anything-yahoo-suggest "anything-config" "\
Preconfigured `anything' for Yahoo searching with Yahoo suggest.

\(fn)" t nil)

(autoload 'anything-for-buffers "anything-config" "\
Preconfigured `anything' for buffer.

\(fn)" t nil)

(autoload 'anything-buffers+ "anything-config" "\
Enhanced preconfigured `anything' for buffer.

\(fn)" t nil)

(autoload 'anything-bbdb "anything-config" "\
Preconfigured `anything' for BBDB.

Needs BBDB.

http://bbdb.sourceforge.net/

\(fn)" t nil)

(autoload 'anything-locate "anything-config" "\
Preconfigured `anything' for Locate.
Note: you can add locate options after entering pattern.
See 'man locate' for valid options.

You can specify a specific database with prefix argument ARG (C-u).
Many databases can be used: navigate and mark them.
See also `anything-locate-with-db'.

To create a user specific db, use
\"updatedb -l 0 -o db_path -U directory\".
Where db_path is a filename matched by
`anything-locate-db-file-regexp'.

\(fn ARG)" t nil)

(autoload 'anything-w3m-bookmarks "anything-config" "\
Preconfigured `anything' for w3m bookmark.

Needs w3m and emacs-w3m.

http://w3m.sourceforge.net/
http://emacs-w3m.namazu.org/

\(fn)" t nil)

(autoload 'anything-firefox-bookmarks "anything-config" "\
Preconfigured `anything' for firefox bookmark.
You will have to enable html bookmarks in firefox:
open about:config in firefox and double click on this line to enable value to true:

user_pref(\"browser.bookmarks.autoExportHTML\", false);

You should have now:

user_pref(\"browser.bookmarks.autoExportHTML\", true);

After closing firefox, you will be able to browse you bookmarks.

\(fn)" t nil)

(autoload 'anything-colors "anything-config" "\
Preconfigured `anything' for color.

\(fn)" t nil)

(autoload 'anything-bookmarks "anything-config" "\
Preconfigured `anything' for bookmarks.

\(fn)" t nil)

(autoload 'anything-c-pp-bookmarks "anything-config" "\
Preconfigured `anything' for bookmarks (pretty-printed).

\(fn)" t nil)

(autoload 'anything-c-insert-latex-math "anything-config" "\
Preconfigured anything for latex math symbols completion.

\(fn)" t nil)

(autoload 'anything-register "anything-config" "\
Preconfigured `anything' for Emacs registers.

\(fn)" t nil)

(autoload 'anything-man-woman "anything-config" "\
Preconfigured `anything' for Man and Woman pages.

\(fn)" t nil)

(autoload 'anything-org-keywords "anything-config" "\
Preconfigured `anything' for org keywords.

\(fn)" t nil)

(autoload 'anything-emms "anything-config" "\
Preconfigured `anything' for emms sources.

\(fn)" t nil)

(autoload 'anything-eev-anchors "anything-config" "\
Preconfigured `anything' for eev anchors.

\(fn)" t nil)

(autoload 'anything-bm-list "anything-config" "\
Preconfigured `anything' for visible bookmarks.

Needs bm.el

http://cvs.savannah.gnu.org/viewvc/*checkout*/bm/bm/bm.el

\(fn)" t nil)

(autoload 'anything-timers "anything-config" "\
Preconfigured `anything' for timers.

\(fn)" t nil)

(autoload 'anything-list-emacs-process "anything-config" "\
Preconfigured `anything' for emacs process.

\(fn)" t nil)

(autoload 'anything-occur "anything-config" "\
Preconfigured Anything for Occur source.

\(fn)" t nil)

(autoload 'anything-browse-code "anything-config" "\
Preconfigured anything to browse code.

\(fn)" t nil)

(autoload 'anything-org-headlines "anything-config" "\
Preconfigured anything to show org headlines.

\(fn)" t nil)

(autoload 'anything-info-gnus "anything-config" "\
Preconfigured anything to browse Gnus Manual.

\(fn)" t nil)

(autoload 'anything-kill-buffers "anything-config" "\
Preconfigured `anything' to kill buffer you selected.

\(fn)" t nil)

(autoload 'anything-regexp "anything-config" "\
Preconfigured anything to build regexps and run query-replace-regexp against.

\(fn)" t nil)

(autoload 'anything-mark-all "anything-config" "\
Mark all visible unmarked candidates in current source.

\(fn)" t nil)

(autoload 'anything-unmark-all "anything-config" "\
Unmark all candidates in all sources of current anything session.

\(fn)" t nil)

(autoload 'anything-toggle-all-marks "anything-config" "\
Toggle all marks.
Mark all visible candidates of current source or unmark all candidates
visible or invisible in all sources of current anything session

\(fn)" t nil)

(autoload 'anything-buffer-diff-persistent "anything-config" "\
Toggle diff buffer without quitting anything.

\(fn)" t nil)

(autoload 'anything-buffer-revert-persistent "anything-config" "\
Revert buffer without quitting anything.

\(fn)" t nil)

(autoload 'anything-buffer-save-persistent "anything-config" "\
Save buffer without quitting anything.

\(fn)" t nil)

(autoload 'anything-buffer-run-kill-buffers "anything-config" "\
Run kill buffer action from `anything-c-source-buffer+'.

\(fn)" t nil)

(autoload 'anything-buffer-run-grep "anything-config" "\
Run Grep action from `anything-c-source-buffer+'.

\(fn)" t nil)

(autoload 'anything-buffer-run-zgrep "anything-config" "\
Run Grep action from `anything-c-source-buffer+'.

\(fn)" t nil)

(autoload 'anything-buffer-run-query-replace-regexp "anything-config" "\
Run Query replace regexp action from `anything-c-source-buffer+'.

\(fn)" t nil)

(autoload 'anything-buffer-run-query-replace "anything-config" "\
Run Query replace action from `anything-c-source-buffer+'.

\(fn)" t nil)

(autoload 'anything-buffer-switch-other-window "anything-config" "\
Run switch to other window action from `anything-c-source-buffer+'.

\(fn)" t nil)

(autoload 'anything-buffer-switch-other-frame "anything-config" "\
Run switch to other frame action from `anything-c-source-buffer+'.

\(fn)" t nil)

(autoload 'anything-buffer-switch-to-elscreen "anything-config" "\
Run switch to elscreen  action from `anything-c-source-buffer+'.

\(fn)" t nil)

(autoload 'anything-ff-run-toggle-auto-update "anything-config" "\
Not documented

\(fn)" t nil)

(autoload 'anything-ff-run-switch-to-history "anything-config" "\
Run Switch to history action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-grep "anything-config" "\
Run Grep action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-pdfgrep "anything-config" "\
Run Pdfgrep action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-zgrep "anything-config" "\
Run Grep action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-copy-file "anything-config" "\
Run Copy file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-rename-file "anything-config" "\
Run Rename file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-byte-compile-file "anything-config" "\
Run Byte compile file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-load-file "anything-config" "\
Run Load file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-eshell-command-on-file "anything-config" "\
Run eshell command on file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-ediff-file "anything-config" "\
Run Ediff file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-ediff-merge-file "anything-config" "\
Run Ediff merge file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-symlink-file "anything-config" "\
Run Symlink file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-delete-file "anything-config" "\
Run Delete file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-complete-fn-at-point "anything-config" "\
Run complete file name action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-switch-to-eshell "anything-config" "\
Run switch to eshell action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-switch-other-window "anything-config" "\
Run switch to other window action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-switch-other-frame "anything-config" "\
Run switch to other frame action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-open-file-externally "anything-config" "\
Run open file externally command action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-gnus-attach-files "anything-config" "\
Run gnus attach files command action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-run-print-file "anything-config" "\
Run Print file action from `anything-c-source-find-files'.

\(fn)" t nil)

(autoload 'anything-ff-properties-persistent "anything-config" "\
Show properties without quitting anything.

\(fn)" t nil)

(autoload 'anything-ff-run-kill-buffer-persistent "anything-config" "\
Execute `anything-ff-kill-buffer-fname' whitout quitting.

\(fn)" t nil)

(autoload 'anything-find-files "anything-config" "\
Preconfigured `anything' for anything implementation of `find-file'.
Called with a prefix arg show history if some.
Don't call it from programs, use `anything-find-files1' instead.
This is the starting point for nearly all actions you can do on files.

\(fn ARG)" t nil)

(autoload 'anything-write-file "anything-config" "\
Preconfigured `anything' providing completion for `write-file'.

\(fn)" t nil)

(autoload 'anything-insert-file "anything-config" "\
Preconfigured `anything' providing completion for `insert-file'.

\(fn)" t nil)

(autoload 'anything-dired-rename-file "anything-config" "\
Preconfigured `anything' to rename files from dired.

\(fn)" t nil)

(autoload 'anything-dired-copy-file "anything-config" "\
Preconfigured `anything' to copy files from dired.

\(fn)" t nil)

(autoload 'anything-dired-symlink-file "anything-config" "\
Preconfigured `anything' to symlink files from dired.

\(fn)" t nil)

(autoload 'anything-dired-hardlink-file "anything-config" "\
Preconfigured `anything' to hardlink files from dired.

\(fn)" t nil)

(defvar anything-dired-mode "Enable anything completion in Dired functions.\nBindings affected are C, R, S, H." "\
Non-nil if Anything-Dired mode is enabled.
See the command `anything-dired-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `anything-dired-mode'.")

(custom-autoload 'anything-dired-mode "anything-config" nil)

(autoload 'anything-dired-mode "anything-config" "\
Toggle Anything-Dired mode on or off.
Interactively, with no prefix argument, toggle the mode.
With universal prefix ARG turn mode on.
With zero or negative ARG turn mode off.
\\{anything-dired-mode-map}

\(fn &optional ARG)" t nil)

(autoload 'anything-do-grep "anything-config" "\
Preconfigured anything for grep.
Contrarily to Emacs `grep' no default directory is given, but
the full path of candidates in ONLY.
That allow to grep different files not only in `default-directory' but anywhere
by marking them (C-<SPACE>). If one or more directory is selected
grep will search in all files of these directories.
You can use also wildcard in the base name of candidate.
If a prefix arg is given use the -r option of grep.
The prefix arg can be passed before or after start.
See also `anything-do-grep1'.

\(fn)" t nil)

(autoload 'anything-do-zgrep "anything-config" "\
Preconfigured anything for zgrep.

\(fn CANDIDATE)" nil nil)

(autoload 'anything-c-goto-precedent-file "anything-config" "\
Go to precedent file in anything grep/etags buffers.

\(fn)" t nil)

(autoload 'anything-c-goto-next-file "anything-config" "\
Go to precedent file in anything grep/etags buffers.

\(fn)" t nil)

(autoload 'anything-grep-help "anything-config" "\
Not documented

\(fn)" t nil)

(autoload 'anything-pdfgrep-help "anything-config" "\
Not documented

\(fn)" t nil)

(autoload 'anything-yank-text-at-point "anything-config" "\
Yank text at point in minibuffer.

\(fn)" t nil)

(autoload 'anything-etags-help "anything-config" "\
Not documented

\(fn)" t nil)

(autoload 'anything-filelist "anything-config" "\
Preconfigured `anything' to open files instantly.

See `anything-c-filelist-file-name' docstring for usage.

\(fn)" t nil)

(autoload 'anything-filelist+ "anything-config" "\
Preconfigured `anything' to open files/buffers/bookmarks instantly.

This is a replacement for `anything-for-files'.
See `anything-c-filelist-file-name' docstring for usage.

\(fn)" t nil)

(autoload 'anything-M-x "anything-config" "\
Preconfigured `anything' for Emacs commands.
It is `anything' replacement of regular `M-x' `execute-extended-command'.

\(fn)" t nil)

(autoload 'anything-manage-advice "anything-config" "\
Preconfigured `anything' to disable/enable function advices.

\(fn)" t nil)

(autoload 'anything-bookmark-ext "anything-config" "\
Preconfigured `anything' for bookmark-extensions sources.
Needs bookmark-ext.el:
<http://mercurial.intuxication.org/hg/emacs-bookmark-extension>.
Contain also `anything-c-source-google-suggest'.

\(fn)" t nil)

(autoload 'anything-simple-call-tree "anything-config" "\
Preconfigured `anything' for simple-call-tree. List function relationships.

Needs simple-call-tree.el.
http://www.emacswiki.org/cgi-bin/wiki/download/simple-call-tree.el

\(fn)" t nil)

(autoload 'anything-mark-ring "anything-config" "\
Preconfigured `anything' for `anything-c-source-mark-ring'.

\(fn)" t nil)

(autoload 'anything-global-mark-ring "anything-config" "\
Preconfigured `anything' for `anything-c-source-global-mark-ring'.

\(fn)" t nil)

(autoload 'anything-all-mark-rings "anything-config" "\
Preconfigured `anything' for `anything-c-source-global-mark-ring' and `anything-c-source-mark-ring'.

\(fn)" t nil)

(autoload 'anything-yaoddmuse-cache-pages "anything-config" "\
Fetch the list of files on emacswiki and create cache file.
If load is non--nil load the file and feed `yaoddmuse-pages-hash'.

\(fn &optional LOAD)" t nil)

(autoload 'anything-yaoddmuse-emacswiki-edit-or-view "anything-config" "\
Preconfigured `anything' to edit or view EmacsWiki page.

Needs yaoddmuse.el.

http://www.emacswiki.org/emacs/download/yaoddmuse.el

\(fn)" t nil)

(autoload 'anything-yaoddmuse-emacswiki-post-library "anything-config" "\
Preconfigured `anything' to post library to EmacsWiki.

Needs yaoddmuse.el.

http://www.emacswiki.org/emacs/download/yaoddmuse.el

\(fn)" t nil)

(autoload 'anything-eval-expression "anything-config" "\
Preconfigured anything for `anything-c-source-evaluation-result'.

\(fn ARG)" t nil)

(autoload 'anything-eval-expression-with-eldoc "anything-config" "\
Preconfigured anything for `anything-c-source-evaluation-result' with `eldoc' support. 

\(fn)" t nil)

(autoload 'anything-calcul-expression "anything-config" "\
Preconfigured anything for `anything-c-source-calculation-result'.

\(fn)" t nil)

(autoload 'anything-surfraw "anything-config" "\
Preconfigured `anything' to search PATTERN with search ENGINE.

\(fn PATTERN ENGINE)" t nil)

(autoload 'anything-call-source "anything-config" "\
Preconfigured `anything' to call anything source.

\(fn)" t nil)

(autoload 'anything-execute-anything-command "anything-config" "\
Preconfigured `anything' to execute preconfigured `anything'.

\(fn)" t nil)

(autoload 'anything-create "anything-config" "\
Preconfigured `anything' to do many create actions from STRING.
See also `anything-create--actions'.

\(fn &optional STRING INITIAL-INPUT)" t nil)

(autoload 'anything-top "anything-config" "\
Preconfigured `anything' for top command.

\(fn)" t nil)

(autoload 'anything-select-xfont "anything-config" "\
Preconfigured `anything' to select Xfont.

\(fn)" t nil)

(autoload 'anything-world-time "anything-config" "\
Preconfigured `anything' to show world time.

\(fn)" t nil)

(autoload 'anything-apt "anything-config" "\
Preconfigured `anything' : frontend of APT package manager.

\(fn QUERY)" t nil)

(autoload 'anything-c-shell-command-if-needed "anything-config" "\
Not documented

\(fn COMMAND)" t nil)

(defvar anything-completion-mode nil "\
Non-nil if Anything-Completion mode is enabled.
See the command `anything-completion-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `anything-completion-mode'.")

(custom-autoload 'anything-completion-mode "anything-config" nil)

(autoload 'anything-completion-mode "anything-config" "\
Toggle generic anything completion.

\(fn &optional ARG)" t nil)

(autoload 'anything-esh-pcomplete "anything-config" "\
Preconfigured anything to provide anything completion in eshell.

\(fn)" t nil)

(autoload 'anything-lisp-completion-at-point "anything-config" "\
Anything lisp symbol completion at point.

\(fn)" t nil)

(autoload 'anything-lisp-completion-at-point-or-indent "anything-config" "\
First call indent and second call complete lisp symbol.
The second call should happen before `anything-lisp-completion-or-indent-delay',
after this delay, next call will indent again.
After completion, next call is always indent.
See that like click and double mouse click.
One hit indent, two quick hits maybe indent and complete.

\(fn ARG)" t nil)

(autoload 'anything-c-complete-file-name-at-point "anything-config" "\
Complete file name at point.

\(fn)" t nil)

(autoload 'anything-c-run-external-command "anything-config" "\
Preconfigured `anything' to run External PROGRAM asyncronously from Emacs.
If program is already running exit with error.
You can set your own list of commands with
`anything-c-external-commands-list'.

\(fn PROGRAM)" t nil)

(autoload 'anything-ratpoison-commands "anything-config" "\
Preconfigured `anything' to execute ratpoison commands.

\(fn)" t nil)

(autoload 'w32-shell-execute-open-file "anything-config" "\
Not documented

\(fn FILE)" t nil)

(autoload 'anything-c-call-interactively "anything-config" "\
Execute CMD-OR-NAME as Emacs command.
It is added to `extended-command-history'.
`anything-current-prefix-arg' is used as the command's prefix argument.

\(fn CMD-OR-NAME)" nil nil)

(autoload 'anything-c-set-variable "anything-config" "\
Set value to VAR interactively.

\(fn VAR)" t nil)

(autoload 'anything-c-reset-adaptative-history "anything-config" "\
Delete all `anything-c-adaptive-history' and his file.
Useful when you have a old or corrupted `anything-c-adaptive-history-file'.

\(fn)" t nil)

;;;***

;;;### (autoloads (ascii-off ascii-on ascii-display ascii-customize)
;;;;;;  "ascii" "site-lisp/ascii.el" (18429 49075))
;;; Generated autoloads from site-lisp/ascii.el

(autoload 'ascii-customize "ascii" "\
Customize ASCII options.

\(fn)" t nil)

(autoload 'ascii-display "ascii" "\
Toggle ASCII code display.

If ARG is null, toggle ASCII code display.
If ARG is a number and is greater than zero, turn on display; otherwise, turn
off display.
If ARG is anything else, turn on display.

\(fn &optional ARG)" t nil)

(autoload 'ascii-on "ascii" "\
Turn on ASCII code display.

\(fn)" t nil)

(autoload 'ascii-off "ascii" "\
Turn off ASCII code display.

\(fn)" t nil)

;;;***

;;;### (autoloads (bookmark-w3m-bookmark-jump) "bookmark-w3m" "site-lisp/emacs-w3m/bookmark-w3m.el"
;;;;;;  (20015 29800))
;;; Generated autoloads from site-lisp/emacs-w3m/bookmark-w3m.el

(autoload 'bookmark-w3m-bookmark-jump "bookmark-w3m" "\
Default bookmark handler for w3m buffers.

\(fn BOOKMARK)" nil nil)

;;;***

;;;### (autoloads (browse-kill-ring browse-kill-ring-default-keybindings)
;;;;;;  "browse-kill-ring" "site-lisp/browse-kill-ring.el" (18429
;;;;;;  49075))
;;; Generated autoloads from site-lisp/browse-kill-ring.el

(autoload 'browse-kill-ring-default-keybindings "browse-kill-ring" "\
Set up M-y (`yank-pop') so that it can invoke `browse-kill-ring'.
Normally, if M-y was not preceeded by C-y, then it has no useful
behavior.  This function sets things up so that M-y will invoke
`browse-kill-ring'.

\(fn)" t nil)

(autoload 'browse-kill-ring "browse-kill-ring" "\
Display items in the `kill-ring' in another buffer.

\(fn)" t nil)

;;;***

;;;### (autoloads (chess-create-display chess) "chess" "site-lisp/chess/chess.el"
;;;;;;  (18621 1424))
;;; Generated autoloads from site-lisp/chess/chess.el

(autoload 'chess "chess" "\
Start a game of chess, playing against ENGINE (a module name).

\(fn &optional ENGINE DISABLE-POPUP ENGINE-RESPONSE-HANDLER &rest ENGINE-CTOR-ARGS)" t nil)

(defalias 'chess-session 'chess)

(autoload 'chess-create-display "chess" "\
Create a display, letting the user's customization decide the style.
If MODULES-TOO is non-nil, also create and associate the modules
listed in `chess-default-modules'.

\(fn PERSPECTIVE &optional MODULES-TOO)" nil nil)

;;;***

;;;### (autoloads (chess-ics) "chess-ics" "site-lisp/chess/chess-ics.el"
;;;;;;  (18621 4541))
;;; Generated autoloads from site-lisp/chess/chess-ics.el

(autoload 'chess-ics "chess-ics" "\
Connect to an Internet Chess Server.

\(fn SERVER PORT &optional HANDLE PASSWORD-OR-FILENAME HELPER &rest HELPER-ARGS)" t nil)

;;;***

;;;### (autoloads (chess-link) "chess-link" "site-lisp/chess/chess-link.el"
;;;;;;  (18615 28794))
;;; Generated autoloads from site-lisp/chess/chess-link.el

(autoload 'chess-link "chess-link" "\
Play out a game between two engines, and watch the progress.
If you want to run an engine as a bot, make the transport the first
engine, and the computer the second engine.

\(fn FIRST-ENGINE-TYPE SECOND-ENGINE-TYPE)" t nil)

;;;***

;;;### (autoloads (chess-pgn-mode chess-pgn-read) "chess-pgn" "site-lisp/chess/chess-pgn.el"
;;;;;;  (18621 4159))
;;; Generated autoloads from site-lisp/chess/chess-pgn.el

(autoload 'chess-pgn-read "chess-pgn" "\
Read and display a PGN game after point.

\(fn &optional FILE)" t nil)

(autoload 'chess-pgn-mode "chess-pgn" "\
A mode for editing chess PGN files.

\(fn)" t nil)

(defalias 'pgn-mode 'chess-pgn-mode)

(add-to-list 'auto-mode-alist '("\\.pgn\\'" . chess-pgn-mode))

;;;***

;;;### (autoloads (chess-puzzle) "chess-puzzle" "site-lisp/chess/chess-puzzle.el"
;;;;;;  (18619 23413))
;;; Generated autoloads from site-lisp/chess/chess-puzzle.el

(autoload 'chess-puzzle "chess-puzzle" "\
Pick a random puzzle from FILE, and solve it against the default engine.
The spacebar in the display buffer is bound to `chess-puzzle-next',
making it easy to go on to the next puzzle once you've solved one.

\(fn FILE &optional INDEX)" t nil)

;;;***

;;;### (autoloads (chess-fischer-random-position) "chess-random"
;;;;;;  "site-lisp/chess/chess-random.el" (18615 28794))
;;; Generated autoloads from site-lisp/chess/chess-random.el

(autoload 'chess-fischer-random-position "chess-random" "\
Generate a Fischer Random style position.

\(fn)" nil nil)

;;;***

;;;### (autoloads (chess-tutorial) "chess-tutorial" "site-lisp/chess/chess-tutorial.el"
;;;;;;  (18615 28794))
;;; Generated autoloads from site-lisp/chess/chess-tutorial.el

(autoload 'chess-tutorial "chess-tutorial" "\
A simple chess training display.

\(fn)" t nil)

;;;***

;;;### (autoloads (cl-info) "cl-info" "cl-info.el" (18429 49044))
;;; Generated autoloads from cl-info.el

(autoload 'cl-info "cl-info" "\
Not documented

\(fn SYMBOL-NAME)" t nil)

;;;***

;;;### (autoloads (turn-on-cldoc-mode cldoc-mode cldoc-minor-mode-string
;;;;;;  cldoc-mode) "cldoc" "site-lisp/cldoc.el" (18429 49075))
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

(custom-autoload 'cldoc-mode "cldoc" t)

(defvar cldoc-minor-mode-string " Cldoc" "\
*String to display in mode line when Cldoc Mode is enabled.")

(custom-autoload 'cldoc-minor-mode-string "cldoc" t)

(cond ((fboundp 'add-minor-mode) (add-minor-mode 'cldoc-mode 'cldoc-minor-mode-string)) ((assq 'cldoc-mode (default-value 'minor-mode-alist))) (t (setq-default minor-mode-alist (append (default-value 'minor-mode-alist) '((cldoc-mode cldoc-minor-mode-string))))))

(autoload 'cldoc-mode "cldoc" "\
*Enable or disable cldoc mode.
See documentation for the variable of the same name for more details.

If called interactively with no prefix argument, toggle current condition
of the mode.
If called with a positive or negative prefix argument, enable or disable
the mode, respectively.

\(fn &optional PREFIX)" t nil)

(autoload 'turn-on-cldoc-mode "cldoc" "\
Unequivocally turn on cldoc-mode (see variable documentation).

\(fn)" t nil)

;;;***

;;;### (autoloads nil "column-marker" "site-lisp/column-marker.el"
;;;;;;  (18429 49075))
;;; Generated autoloads from site-lisp/column-marker.el

(autoload 'column-marker-1 "column-marker" "\
Highlight a column." t)

;;;***

;;;### (autoloads (diminished-modes diminish-undo diminish) "diminish"
;;;;;;  "site-lisp/diminish.el" (18429 49075))
;;; Generated autoloads from site-lisp/diminish.el

(autoload 'diminish "diminish" "\
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
to TO-WHAT if it's > 1 char long & doesn't already begin with a space.

\(fn MODE &optional TO-WHAT)" t nil)

(autoload 'diminish-undo "diminish" "\
Restore mode-line display of diminished mode MODE to its minor-mode value.
Do nothing if the arg is a minor mode that hasn't been diminished.

Interactively, enter (with completion) the name of any diminished mode (a
mode that was formerly a minor mode on which you invoked M-x diminish).
To restore all diminished modes to minor status, answer `diminished-modes'.
The response to the prompt shouldn't be quoted.  However, in Lisp code,
the arg must be quoted as a symbol, as in (diminish-undo 'diminished-modes).

\(fn MODE)" t nil)

(autoload 'diminished-modes "diminish" "\
Echo all active diminished or minor modes as if they were minor.
The display goes in the echo area; if it's too long even for that,
you can see the whole thing in the *Messages* buffer.
This doesn't change the status of any modes; it just lets you see
what diminished modes would be on the mode-line if they were still minor.

\(fn)" t nil)

;;;***

;;;### (autoloads (dired-tar-pack-unpack) "dired-tar" "site-lisp/dired-tar.el"
;;;;;;  (19516 50789))
;;; Generated autoloads from site-lisp/dired-tar.el

(autoload 'dired-tar-pack-unpack "dired-tar" "\
Create or unpack a tar archive for the file on the current line.

If the file on the current line is a directory, make a gzipped tar
file out of its contents.

If the file on the current line is a tar archive, unpack it.  If the
archive appears to be gzipped or compressed, expand it first.  With a
prefix argument, just list the tar archive's contents, and don't
unpack it.  The file's name must end in \".tar\", \".tar.gz\", or
\".tar.Z\" or else this command will assume it's not a tar file.

\(fn PREFIX-ARG)" t nil)

(add-hook 'dired-mode-hook #'(lambda nil (define-key dired-mode-map "T" 'dired-tar-pack-unpack)))

;;;***

;;;### (autoloads (doctest-mode doctest-register-mmm-classes) "doctest-mode"
;;;;;;  "site-lisp/python-mode/doctest-mode.el" (19891 49430))
;;; Generated autoloads from site-lisp/python-mode/doctest-mode.el

(autoload 'doctest-register-mmm-classes "doctest-mode" "\
Register doctest's mmm classes, allowing doctest to be used as a
submode region in other major modes, such as python-mode and rst-mode.
Two classes are registered:

`doctest-docstring'

    Used to edit docstrings containing doctest examples in python-
    mode.  Docstring submode regions start and end with triple-quoted
    strings (\"\"\").  In order to avoid confusing start-string
    markers and end-string markers, all triple-quote strings in the
    buffer are treated as submode regions (even if they're not
    actually docstrings).  Use (C-c % C-d) to insert a new doctest-
    docstring region.  When `doctest-execute' (C-c C-c) is called
    inside a doctest-docstring region, it executes just the current
    docstring.  The globals for this execution are constructed by
    importing the current buffer's contents in Python.

`doctest-example'

    Used to edit doctest examples in text-editing modes, such as
    `rst-mode' or `text-mode'.  Docstring submode regions start with
    optionally indented prompts (>>>) and end with blank lines.  Use
    (C-c % C-e) to insert a new doctest-example region.  When
    `doctest-execute' (C-c C-c) is called inside a doctest-example
    region, it executes all examples in the buffer.

If ADD-MODE-EXT-CLASSES is true, then register the new classes in
`mmm-mode-ext-classes-alist', which will cause them to be used by
default in the following modes:

    doctest-docstring:  python-mode
    doctest-example:    rst-mode

If FIX-MMM-FONTIFY-REGION-BUG is true, then register a hook that will
fix a bug in `mmm-fontify-region' that affects some (but not all)
versions of emacs.  (See `doctest-fixed-mmm-fontify-region' for more
info.)

\(fn &optional ADD-MODE-EXT-CLASSES FIX-MMM-FONTIFY-REGION-BUG)" t nil)

(add-to-list 'auto-mode-alist '("\\.doctest$" . doctest-mode))

(autoload 'doctest-mode "doctest-mode" "\
A major mode for editing text files that contain Python
doctest examples.  Doctest is a testing framework for Python that
emulates an interactive session, and checks the result of each
command.  For more information, see the Python library reference:
<http://docs.python.org/lib/module-doctest.html>

`doctest-mode' defines three kinds of line, each of which is
treated differently:

  - 'Source lines' are lines consisting of a Python prompt
    ('>>>' or '...'), followed by source code.  Source lines are
    colored (similarly to `python-mode') and auto-indented.

  - 'Output lines' are non-blank lines immediately following
    source lines.  They are colored using several doctest-
    specific output faces.

  - 'Text lines' are any other lines.  They are not processed in
    any special way.

\\{doctest-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads (ee) "ee" "site-lisp/ee/ee.el" (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee.el

(autoload 'ee "ee" "\
Enter top-level index of all available ee extensions.
Optional argument FILE specifies the file to examine;
the default is the top-level mode list.
In interactive use, a prefix argument directs this command
to read a root file name from the minibuffer.

\(fn &optional FILE)" t nil)

;;;***

;;;### (autoloads (ee-bbdb) "ee-bbdb" "site-lisp/ee/ee-bbdb.el" (20019
;;;;;;  11309))
;;; Generated autoloads from site-lisp/ee/ee-bbdb.el

(autoload 'ee-bbdb "ee-bbdb" "\
Summary mode for BBDB.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-buffers) "ee-buffers" "site-lisp/ee/ee-buffers.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-buffers.el

(autoload 'ee-buffers "ee-buffers" "\
Display and manipulate Emacs buffers.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-commands) "ee-commands" "site-lisp/ee/ee-commands.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-commands.el

(autoload 'ee-commands "ee-commands" "\
Categorized menu of Emacs commands.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-customize) "ee-customize" "site-lisp/ee/ee-customize.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-customize.el

(autoload 'ee-customize "ee-customize" "\
Browse Emacs customization groups.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-datafile ee-datafile-mode) "ee-datafile" "site-lisp/ee/ee-datafile.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-datafile.el
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

;;;### (autoloads (ee-dired) "ee-dired" "site-lisp/ee/ee-dired.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-dired.el

(autoload 'ee-dired "ee-dired" "\
Categorized directory listings.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-dselect) "ee-dselect" "site-lisp/ee/ee-dselect.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-dselect.el

(autoload 'ee-dselect "ee-dselect" "\
Debian package handling frontend.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-edb) "ee-edb" "site-lisp/ee/ee-edb.el" (20019
;;;;;;  11309))
;;; Generated autoloads from site-lisp/ee/ee-edb.el

(autoload 'ee-edb "ee-edb" "\
Summary mode for EDB.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-ell) "ee-ell" "site-lisp/ee/ee-ell.el" (20019
;;;;;;  11309))
;;; Generated autoloads from site-lisp/ee/ee-ell.el

(autoload 'ee-ell "ee-ell" "\
Browse the categorized Emacs Lisp List.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-example) "ee-example" "site-lisp/ee/ee-example.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-example.el

(autoload 'ee-example "ee-example" "\
Accompanying example for demonstration of ee capabilities.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-fields) "ee-fields" "site-lisp/ee/ee-fields.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-fields.el

(autoload 'ee-fields "ee-fields" "\
Display and edit fields of the current record.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-finder) "ee-finder" "site-lisp/ee/ee-finder.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-finder.el

(autoload 'ee-finder "ee-finder" "\
Keyword-based Emacs code finder.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-gnus) "ee-gnus" "site-lisp/ee/ee-gnus.el" (20019
;;;;;;  11309))
;;; Generated autoloads from site-lisp/ee/ee-gnus.el

(autoload 'ee-gnus "ee-gnus" "\
Summary and topic mode for Gnus.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-history-shell-command ee-history-extended-command
;;;;;;  ee-history-command) "ee-history" "site-lisp/ee/ee-history.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-history.el

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

;;;### (autoloads (ee-imenu) "ee-imenu" "site-lisp/ee/ee-imenu.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-imenu.el

(autoload 'ee-imenu "ee-imenu" "\
Categorized mode-specific buffer indexes.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-info) "ee-info" "site-lisp/ee/ee-info.el" (20019
;;;;;;  11309))
;;; Generated autoloads from site-lisp/ee/ee-info.el

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

;;;### (autoloads (ee-marks) "ee-marks" "site-lisp/ee/ee-marks.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-marks.el

(autoload 'ee-marks "ee-marks" "\
Display and go to marked lines in the current Emacs buffer.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-menubar) "ee-menubar" "site-lisp/ee/ee-menubar.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-menubar.el

(autoload 'ee-menubar "ee-menubar" "\
Categorized access to Emacs menu-bar.

\(fn &optional ARG)" t nil)
 (defalias 'ee-tmm 'ee-menubar)

;;;***

;;;### (autoloads (ee-outline) "ee-outline" "site-lisp/ee/ee-outline.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-outline.el

(autoload 'ee-outline "ee-outline" "\
Manipulate outlines collected from outline-mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-processes) "ee-processes" "site-lisp/ee/ee-processes.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-processes.el

(autoload 'ee-processes "ee-processes" "\
Display and manipulate Emacs processes.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-programs) "ee-programs" "site-lisp/ee/ee-programs.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-programs.el

(autoload 'ee-programs "ee-programs" "\
Categorized program menu.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-ps) "ee-ps" "site-lisp/ee/ee-ps.el" (20019
;;;;;;  11309))
;;; Generated autoloads from site-lisp/ee/ee-ps.el

(autoload 'ee-ps "ee-ps" "\
Display CPU processes.

\(fn &optional ARG)" t nil)
 (fset 'ee-top 'ee-ps)

;;;***

;;;### (autoloads (ee-tags) "ee-tags" "site-lisp/ee/ee-tags.el" (20019
;;;;;;  11309))
;;; Generated autoloads from site-lisp/ee/ee-tags.el

(autoload 'ee-tags "ee-tags" "\
Etags facility.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-textfile-apachelog ee-textfile-changelog) "ee-textfile"
;;;;;;  "site-lisp/ee/ee-textfile.el" (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-textfile.el

(autoload 'ee-textfile-changelog "ee-textfile" "\
Organize information from ChangeLog files.

\(fn &optional ARG)" t nil)

(autoload 'ee-textfile-apachelog "ee-textfile" "\
Organize information from Apache log files.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-variables) "ee-variables" "site-lisp/ee/ee-variables.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-variables.el

(autoload 'ee-variables "ee-variables" "\
Categorized menu of Emacs variables.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-views) "ee-views" "site-lisp/ee/ee-views.el"
;;;;;;  (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-views.el

(autoload 'ee-views "ee-views" "\
Display, edit and switch views.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ee-windows ee-windows-add ee-windows-and-add-current)
;;;;;;  "ee-windows" "site-lisp/ee/ee-windows.el" (20019 11309))
;;; Generated autoloads from site-lisp/ee/ee-windows.el

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

;;;### (autoloads (setenv) "env" "site-lisp/apel/env.el" (19385 28150))
;;; Generated autoloads from site-lisp/apel/env.el

(autoload 'setenv "env" "\
Set the value of the environment variable named VARIABLE to VALUE.
VARIABLE should be a string.  VALUE is optional; if not provided or is
`nil', the environment variable VARIABLE will be removed.  

Interactively, a prefix argument means to unset the variable.
Interactively, the current value (if any) of the variable
appears at the front of the history list when you type in the new value.

This function works by modifying `process-environment'.

\(fn VARIABLE &optional VALUE UNSET)" t nil)

;;;***

;;;### (autoloads (epa-sign-keys epa-insert-keys epa-export-keys
;;;;;;  epa-import-armor-in-region epa-import-keys-region epa-import-keys
;;;;;;  epa-delete-keys epa-encrypt-region epa-sign-region epa-verify-cleartext-in-region
;;;;;;  epa-verify-region epa-decrypt-armor-in-region epa-decrypt-region
;;;;;;  epa-encrypt-file epa-sign-file epa-verify-file epa-decrypt-file
;;;;;;  epa-select-keys epa-list-secret-keys epa-list-keys) "epa"
;;;;;;  "site-lisp/epg/epa.el" (19385 29670))
;;; Generated autoloads from site-lisp/epg/epa.el

(autoload 'epa-list-keys "epa" "\
List all keys matched with NAME from the public keyring.

\(fn &optional NAME)" t nil)

(autoload 'epa-list-secret-keys "epa" "\
List all keys matched with NAME from the private keyring.

\(fn &optional NAME)" t nil)

(autoload 'epa-select-keys "epa" "\
Display a user's keyring and ask him to select keys.
CONTEXT is an epg-context.
PROMPT is a string to prompt with.
NAMES is a list of strings to be matched with keys.  If it is nil, all
the keys are listed.
If SECRET is non-nil, list secret keys instead of public keys.

\(fn CONTEXT PROMPT &optional NAMES SECRET)" nil nil)

(autoload 'epa-decrypt-file "epa" "\
Decrypt FILE.

\(fn FILE)" t nil)

(autoload 'epa-verify-file "epa" "\
Verify FILE.

\(fn FILE)" t nil)

(autoload 'epa-sign-file "epa" "\
Sign FILE by SIGNERS keys selected.

\(fn FILE SIGNERS MODE)" t nil)

(autoload 'epa-encrypt-file "epa" "\
Encrypt FILE for RECIPIENTS.

\(fn FILE RECIPIENTS)" t nil)

(autoload 'epa-decrypt-region "epa" "\
Decrypt the current region between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload 'epa-decrypt-armor-in-region "epa" "\
Decrypt OpenPGP armors in the current region between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload 'epa-verify-region "epa" "\
Verify the current region between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload 'epa-verify-cleartext-in-region "epa" "\
Verify OpenPGP cleartext signed messages in the current region
between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload 'epa-sign-region "epa" "\
Sign the current region between START and END by SIGNERS keys selected.

Don't use this command in Lisp programs!

\(fn START END SIGNERS MODE)" t nil)

(autoload 'epa-encrypt-region "epa" "\
Encrypt the current region between START and END for RECIPIENTS.

Don't use this command in Lisp programs!

\(fn START END RECIPIENTS SIGN SIGNERS)" t nil)

(autoload 'epa-delete-keys "epa" "\
Delete selected KEYS.

Don't use this command in Lisp programs!

\(fn KEYS &optional ALLOW-SECRET)" t nil)

(autoload 'epa-import-keys "epa" "\
Import keys from FILE.

Don't use this command in Lisp programs!

\(fn FILE)" t nil)

(autoload 'epa-import-keys-region "epa" "\
Import keys from the region.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload 'epa-import-armor-in-region "epa" "\
Import keys in the OpenPGP armor format in the current region
between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload 'epa-export-keys "epa" "\
Export selected KEYS to FILE.

Don't use this command in Lisp programs!

\(fn KEYS FILE)" t nil)

(autoload 'epa-insert-keys "epa" "\
Insert selected KEYS after the point.

Don't use this command in Lisp programs!

\(fn KEYS)" t nil)

(autoload 'epa-sign-keys "epa" "\
Sign selected KEYS.
If a prefix-arg is specified, the signature is marked as non exportable.

Don't use this command in Lisp programs!

\(fn KEYS &optional LOCAL)" t nil)

;;;***

;;;### (autoloads (epa-file-disable epa-file-enable) "epa-file" "site-lisp/epg/epa-file.el"
;;;;;;  (19385 29670))
;;; Generated autoloads from site-lisp/epg/epa-file.el

(put 'epa-file-encrypt-to 'safe-local-variable (lambda (val) (or (stringp val) (and (listp val) (catch 'safe (mapc (lambda (elt) (unless (stringp elt) (throw 'safe nil))) val) t)))))

(put 'epa-file-encrypt-to 'permanent-local t)

(autoload 'epa-file-enable "epa-file" "\
Not documented

\(fn)" t nil)

(autoload 'epa-file-disable "epa-file" "\
Not documented

\(fn)" t nil)

;;;***

;;;### (autoloads (epa-mail-import-keys epa-mail-encrypt epa-mail-sign
;;;;;;  epa-mail-verify epa-mail-decrypt) "epa-mail" "site-lisp/epg/epa-mail.el"
;;;;;;  (19385 29670))
;;; Generated autoloads from site-lisp/epg/epa-mail.el

(autoload 'epa-mail-decrypt "epa-mail" "\
Decrypt OpenPGP armors in the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn)" t nil)

(autoload 'epa-mail-verify "epa-mail" "\
Verify OpenPGP cleartext signed messages in the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn)" t nil)

(autoload 'epa-mail-sign "epa-mail" "\
Sign the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn START END SIGNERS MODE)" t nil)

(autoload 'epa-mail-encrypt "epa-mail" "\
Encrypt the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn START END RECIPIENTS SIGN SIGNERS)" t nil)

(autoload 'epa-mail-import-keys "epa-mail" "\
Import keys in the OpenPGP armor format in the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn)" t nil)

;;;***

;;;### (autoloads (epg-generate-key-from-string epg-generate-key-from-file
;;;;;;  epg-start-generate-key epg-sign-keys epg-start-sign-keys
;;;;;;  epg-delete-keys epg-start-delete-keys epg-receive-keys epg-start-receive-keys
;;;;;;  epg-import-keys-from-string epg-import-keys-from-file epg-start-import-keys
;;;;;;  epg-export-keys-to-string epg-export-keys-to-file epg-start-export-keys
;;;;;;  epg-encrypt-string epg-encrypt-file epg-start-encrypt epg-sign-string
;;;;;;  epg-sign-file epg-start-sign epg-verify-string epg-verify-file
;;;;;;  epg-start-verify epg-decrypt-string epg-decrypt-file epg-start-decrypt
;;;;;;  epg-cancel epg-list-keys) "epg" "site-lisp/epg/epg.el" (19385
;;;;;;  29670))
;;; Generated autoloads from site-lisp/epg/epg.el

(autoload 'epg-list-keys "epg" "\
Return a list of epg-key objects matched with NAME.
If MODE is nil or 'public, only public keyring should be searched.
If MODE is t or 'secret, only secret keyring should be searched. 
Otherwise, only public keyring should be searched and the key
signatures should be included.
NAME is either a string or a list of strings.

\(fn CONTEXT &optional NAME MODE)" nil nil)

(autoload 'epg-cancel "epg" "\
Not documented

\(fn CONTEXT)" nil nil)

(autoload 'epg-start-decrypt "epg" "\
Initiate a decrypt operation on CIPHER.
CIPHER must be a file data object.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-decrypt-file' or `epg-decrypt-string' instead.

\(fn CONTEXT CIPHER)" nil nil)

(autoload 'epg-decrypt-file "epg" "\
Decrypt a file CIPHER and store the result to a file PLAIN.
If PLAIN is nil, it returns the result as a string.

\(fn CONTEXT CIPHER PLAIN)" nil nil)

(autoload 'epg-decrypt-string "epg" "\
Decrypt a string CIPHER and return the plain text.

\(fn CONTEXT CIPHER)" nil nil)

(autoload 'epg-start-verify "epg" "\
Initiate a verify operation on SIGNATURE.
SIGNATURE and SIGNED-TEXT are a data object if they are specified.

For a detached signature, both SIGNATURE and SIGNED-TEXT should be set.
For a normal or a cleartext signature, SIGNED-TEXT should be nil.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-verify-file' or `epg-verify-string' instead.

\(fn CONTEXT SIGNATURE &optional SIGNED-TEXT)" nil nil)

(autoload 'epg-verify-file "epg" "\
Verify a file SIGNATURE.
SIGNED-TEXT and PLAIN are also a file if they are specified.

For a detached signature, both SIGNATURE and SIGNED-TEXT should be
string.  For a normal or a cleartext signature, SIGNED-TEXT should be
nil.  In the latter case, if PLAIN is specified, the plaintext is
stored into the file after successful verification.

\(fn CONTEXT SIGNATURE &optional SIGNED-TEXT PLAIN)" nil nil)

(autoload 'epg-verify-string "epg" "\
Verify a string SIGNATURE.
SIGNED-TEXT is a string if it is specified.

For a detached signature, both SIGNATURE and SIGNED-TEXT should be
string.  For a normal or a cleartext signature, SIGNED-TEXT should be
nil.  In the latter case, this function returns the plaintext after
successful verification.

\(fn CONTEXT SIGNATURE &optional SIGNED-TEXT)" nil nil)

(autoload 'epg-start-sign "epg" "\
Initiate a sign operation on PLAIN.
PLAIN is a data object.

If optional 3rd argument MODE is t or 'detached, it makes a detached signature.
If it is nil or 'normal, it makes a normal signature.
Otherwise, it makes a cleartext signature.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-sign-file' or `epg-sign-string' instead.

\(fn CONTEXT PLAIN &optional MODE)" nil nil)

(autoload 'epg-sign-file "epg" "\
Sign a file PLAIN and store the result to a file SIGNATURE.
If SIGNATURE is nil, it returns the result as a string.
If optional 3rd argument MODE is t or 'detached, it makes a detached signature.
If it is nil or 'normal, it makes a normal signature.
Otherwise, it makes a cleartext signature.

\(fn CONTEXT PLAIN SIGNATURE &optional MODE)" nil nil)

(autoload 'epg-sign-string "epg" "\
Sign a string PLAIN and return the output as string.
If optional 3rd argument MODE is t or 'detached, it makes a detached signature.
If it is nil or 'normal, it makes a normal signature.
Otherwise, it makes a cleartext signature.

\(fn CONTEXT PLAIN &optional MODE)" nil nil)

(autoload 'epg-start-encrypt "epg" "\
Initiate an encrypt operation on PLAIN.
PLAIN is a data object.
If RECIPIENTS is nil, it performs symmetric encryption.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-encrypt-file' or `epg-encrypt-string' instead.

\(fn CONTEXT PLAIN RECIPIENTS &optional SIGN ALWAYS-TRUST)" nil nil)

(autoload 'epg-encrypt-file "epg" "\
Encrypt a file PLAIN and store the result to a file CIPHER.
If CIPHER is nil, it returns the result as a string.
If RECIPIENTS is nil, it performs symmetric encryption.

\(fn CONTEXT PLAIN RECIPIENTS CIPHER &optional SIGN ALWAYS-TRUST)" nil nil)

(autoload 'epg-encrypt-string "epg" "\
Encrypt a string PLAIN.
If RECIPIENTS is nil, it performs symmetric encryption.

\(fn CONTEXT PLAIN RECIPIENTS &optional SIGN ALWAYS-TRUST)" nil nil)

(autoload 'epg-start-export-keys "epg" "\
Initiate an export keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-export-keys-to-file' or `epg-export-keys-to-string' instead.

\(fn CONTEXT KEYS)" nil nil)

(autoload 'epg-export-keys-to-file "epg" "\
Extract public KEYS.

\(fn CONTEXT KEYS FILE)" nil nil)

(autoload 'epg-export-keys-to-string "epg" "\
Extract public KEYS and return them as a string.

\(fn CONTEXT KEYS)" nil nil)

(autoload 'epg-start-import-keys "epg" "\
Initiate an import keys operation.
KEYS is a data object.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-import-keys-from-file' or `epg-import-keys-from-string' instead.

\(fn CONTEXT KEYS)" nil nil)

(autoload 'epg-import-keys-from-file "epg" "\
Add keys from a file KEYS.

\(fn CONTEXT KEYS)" nil nil)

(autoload 'epg-import-keys-from-string "epg" "\
Add keys from a string KEYS.

\(fn CONTEXT KEYS)" nil nil)

(autoload 'epg-start-receive-keys "epg" "\
Initiate a receive key operation.
KEY-ID-LIST is a list of key IDs.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-generate-key-from-file' or `epg-generate-key-from-string' instead.

\(fn CONTEXT KEY-ID-LIST)" nil nil)

(autoload 'epg-receive-keys "epg" "\
Add keys from server.
KEYS is a list of key IDs

\(fn CONTEXT KEYS)" nil nil)

(defalias 'epg-import-keys-from-server 'epg-receive-keys)

(autoload 'epg-start-delete-keys "epg" "\
Initiate an delete keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-delete-keys' instead.

\(fn CONTEXT KEYS &optional ALLOW-SECRET)" nil nil)

(autoload 'epg-delete-keys "epg" "\
Delete KEYS from the key ring.

\(fn CONTEXT KEYS &optional ALLOW-SECRET)" nil nil)

(autoload 'epg-start-sign-keys "epg" "\
Initiate a sign keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-sign-keys' instead.

\(fn CONTEXT KEYS &optional LOCAL)" nil nil)

(autoload 'epg-sign-keys "epg" "\
Sign KEYS from the key ring.

\(fn CONTEXT KEYS &optional LOCAL)" nil nil)

(autoload 'epg-start-generate-key "epg" "\
Initiate a key generation.
PARAMETERS specifies parameters for the key.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-generate-key-from-file' or `epg-generate-key-from-string' instead.

\(fn CONTEXT PARAMETERS)" nil nil)

(autoload 'epg-generate-key-from-file "epg" "\
Generate a new key pair.
PARAMETERS is a file which tells how to create the key.

\(fn CONTEXT PARAMETERS)" nil nil)

(autoload 'epg-generate-key-from-string "epg" "\
Generate a new key pair.
PARAMETERS is a string which tells how to create the key.

\(fn CONTEXT PARAMETERS)" nil nil)

;;;***

;;;### (autoloads (epg-expand-group epg-check-configuration epg-configuration)
;;;;;;  "epg-config" "site-lisp/epg/epg-config.el" (19385 29670))
;;; Generated autoloads from site-lisp/epg/epg-config.el

(autoload 'epg-configuration "epg-config" "\
Return a list of internal configuration parameters of `epg-gpg-program'.

\(fn)" nil nil)

(autoload 'epg-check-configuration "epg-config" "\
Verify that a sufficient version of GnuPG is installed.

\(fn CONFIG &optional MINIMUM-VERSION)" nil nil)

(autoload 'epg-expand-group "epg-config" "\
Look at CONFIG and try to expand GROUP.

\(fn CONFIG GROUP)" nil nil)

;;;***

;;;### (autoloads (eshell-mode) "esh-mode" "site-lisp/eshell/esh-mode.el"
;;;;;;  (18807 50728))
;;; Generated autoloads from site-lisp/eshell/esh-mode.el

(autoload 'eshell-mode "esh-mode" "\
Emacs shell interactive mode.

\\{eshell-mode-map}

\(fn)" nil nil)

;;;***

;;;### (autoloads (eshell-test) "esh-test" "site-lisp/eshell/esh-test.el"
;;;;;;  (18807 50540))
;;; Generated autoloads from site-lisp/eshell/esh-test.el

(autoload 'eshell-test "esh-test" "\
Test Eshell to verify that it works as expected.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (eshell-toggle eshell-toggle-cd) "esh-toggle" "esh-toggle.el"
;;;;;;  (18807 50473))
;;; Generated autoloads from esh-toggle.el

(autoload 'eshell-toggle-cd "esh-toggle" "\
Calls `eshell-toggle' with a prefix argument.
See the command `eshell-toggle'

\(fn)" t nil)

(autoload 'eshell-toggle "esh-toggle" "\
Toggles between the *eshell* buffer and the current buffer.
With a prefix ARG also insert a \"cd DIR\" command into the eshell,
where DIR is the directory of the current buffer.

Call twice in a row to get a full screen window for the *eshell*
buffer.

When called in the *eshell* buffer returns you to the buffer you were
editing before caling the first time.

Options: `eshell-toggle-goto-eob'

\(fn MAKE-CD)" t nil)

;;;***

;;;### (autoloads (eshell-command-result eshell-command eshell) "eshell"
;;;;;;  "site-lisp/eshell/eshell.el" (18807 50540))
;;; Generated autoloads from site-lisp/eshell/eshell.el

(autoload 'eshell "eshell" "\
Create an interactive Eshell buffer.
The buffer used for Eshell sessions is determined by the value of
`eshell-buffer-name'.  If there is already an Eshell session active in
that buffer, Emacs will simply switch to it.  Otherwise, a new session
will begin.  A numeric prefix arg (as in `C-u 42 M-x eshell RET')
switches to the session with that number, creating it if necessary.  A
nonnumeric prefix arg means to create a new session.  Returns the
buffer selected (or created).

\(fn &optional ARG)" t nil)

(autoload 'eshell-command "eshell" "\
Execute the Eshell command string COMMAND.
With prefix ARG, insert output into the current buffer at point.

\(fn &optional COMMAND ARG)" t nil)

(autoload 'eshell-command-result "eshell" "\
Execute the given Eshell COMMAND, and return the result.
The result might be any Lisp object.
If STATUS-VAR is a symbol, it will be set to the exit status of the
command.  This is the only way to determine whether the value returned
corresponding to a successful execution.

\(fn COMMAND &optional STATUS-VAR)" nil nil)

(define-obsolete-function-alias 'eshell-report-bug 'report-emacs-bug "23.1")

;;;***

;;;### (autoloads (eval-expr eval-expr-install) "eval-expr" "site-lisp/eval-expr.el"
;;;;;;  (18429 49075))
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

(defvar eval-expr-print-level (cond ((boundp 'eval-expression-print-level) (default-value 'eval-expression-print-level)) ((boundp 'print-level) (default-value 'print-level))) "\
*Like print-level, but affect results printed by `eval-expr' only.")

(defvar eval-expr-print-length (cond ((boundp 'eval-expression-print-length) (default-value 'eval-expression-print-length)) ((boundp 'print-length) (default-value 'print-length))) "\
*Like print-length, but affect results printed by `eval-expr' only.")

(defvar eval-expr-print-function 'prin1 "\
*Function to use for printing objects.
This can be set to e.g. `pp' to generate pretty-printed results.")

(autoload 'eval-expr-install "eval-expr" "\
Replace standard eval-expression command with enhanced eval-expr.

\(fn)" t nil)

(autoload 'eval-expr "eval-expr" "\
Evaluate EXPRESSION and print value in minibuffer, temp, or current buffer.
A temp output buffer is used if there is more than one line in the
evaluated result.
If invoked with a prefix arg, or second lisp argument EE::INSERT-VALUE is
non-nil, then insert final value into the current buffer at point.

Value is also consed on to front of the variable `values'.

\(fn EE::EXPRESSION &optional EE::INSERT-VALUE)" t nil)

;;;***

;;;### (autoloads (find-and-load-library find-library) "find-library"
;;;;;;  "site-lisp/find-library.el" (18429 49075))
;;; Generated autoloads from site-lisp/find-library.el

(autoload 'find-library "find-library" "\
Find a library file with completion.

\(fn)" t nil)

(autoload 'find-and-load-library "find-library" "\
Find a library file with completion.

\(fn)" t nil)

;;;***

;;;### (autoloads (fit-frame-or-mouse-drag-vertical-line fit-frame-to-image
;;;;;;  fit-frame fit-frame-skip-header-lines-alist fit-frame-fill-column-margin
;;;;;;  fit-frame-empty-special-display-height fit-frame-empty-special-display-width
;;;;;;  fit-frame-empty-height fit-frame-empty-width fit-frame-max-height-percent
;;;;;;  fit-frame-max-height fit-frame-min-height fit-frame-max-width-percent
;;;;;;  fit-frame-max-width fit-frame-min-width fit-frame-crop-end-blank-flag
;;;;;;  fit-frame-inhibit-fitting-flag fit-frame) "fit-frame" "site-lisp/fit-frame.el"
;;;;;;  (19859 45203))
;;; Generated autoloads from site-lisp/fit-frame.el

(let ((loads (get 'fit-frame 'custom-loads))) (if (member '"fit-frame" loads) nil (put 'fit-frame 'custom-loads (cons '"fit-frame" loads))))

(defvar fit-frame-inhibit-fitting-flag nil "\
*Non-nil means command `fit-frame' does nothing.
You can bind this to non-`nil' to temporarily inhibit frame fitting:
    (let ((fit-frame-inhibit-fitting-flag  t))...)")

(custom-autoload 'fit-frame-inhibit-fitting-flag "fit-frame" t)

(defvar fit-frame-crop-end-blank-flag nil "\
*Non-nil means `fit-frame' doesn't count blank lines at end of buffer.
If nil, then fitting leaves room for such blank lines.")

(custom-autoload 'fit-frame-crop-end-blank-flag "fit-frame" t)

(defvar fit-frame-min-width window-min-width "\
*Minimum width, in characters, that `fit-frame' gives to a frame.
The actual minimum is at least the greater of this and `window-min-width'.")

(custom-autoload 'fit-frame-min-width "fit-frame" t)

(defvar fit-frame-max-width nil "\
*Maximum width, in characters, that `fit-frame' gives to a frame.
If nil, then the function `fit-frame-max-width' is used instead.")

(custom-autoload 'fit-frame-max-width "fit-frame" t)

(defvar fit-frame-max-width-percent 94 "\
*Maximum percent of display width that `fit-frame' gives to a frame'.
See function `fit-frame-max-width'.
Not used unless `fit-frame-max-width' is nil.")

(custom-autoload 'fit-frame-max-width-percent "fit-frame" t)

(defvar fit-frame-min-height window-min-height "\
*Minimum height, in lines, that `fit-frame' gives to a frame.
The actual minimum is at least the greater of this and `window-min-height'.")

(custom-autoload 'fit-frame-min-height "fit-frame" t)

(defvar fit-frame-max-height nil "\
*Maximum height, in lines, that `fit-frame' gives to a frame.
If nil, then the function `fit-frame-max-height' is used instead.")

(custom-autoload 'fit-frame-max-height "fit-frame" t)

(defvar fit-frame-max-height-percent 82 "\
*Maximum percent of display height that `fit-frame' gives to a frame.
See function `fit-frame-max-height'.
Not used unless `fit-frame-max-height' is nil.")

(custom-autoload 'fit-frame-max-height-percent "fit-frame" t)

(defvar fit-frame-empty-width (or (cdr (assq 'width default-frame-alist)) 80) "\
*Width, in characters, that `fit-frame' gives to an empty frame.")

(custom-autoload 'fit-frame-empty-width "fit-frame" t)

(defvar fit-frame-empty-height (or (cdr (assq 'height default-frame-alist)) 35) "\
*Height, in lines, that `fit-frame' gives to an empty frame.")

(custom-autoload 'fit-frame-empty-height "fit-frame" t)

(defvar fit-frame-empty-special-display-width 80 "\
*Width, in chars, that `fit-frame' gives to an empty special-display frame.
If this is nil, it is ignored.")

(custom-autoload 'fit-frame-empty-special-display-width "fit-frame" t)

(defvar fit-frame-empty-special-display-height 9 "\
*Height, in lines, that `fit-frame' gives to an empty special-display frame.
If this is nil, it is ignored.")

(custom-autoload 'fit-frame-empty-special-display-height "fit-frame" t)

(defvar fit-frame-fill-column-margin 7 "\
*Difference between `fill-column' and frame width after fitting a frame.
Used when `fit-frame' fits a frame, if the prefix arg is negative.
Depending on the average word length of the language used in the
selected window, you might want different values for this.  This
variable is buffer-local.")

(custom-autoload 'fit-frame-fill-column-margin "fit-frame" t)

(defvar fit-frame-skip-header-lines-alist '((Info-mode . 1) (dired-mode . 2) (compilation-mode . 2)) "\
*Alist of major-modes and header lines to ignore.

When `fit-frame' calculates the width of the current buffer, it can
first skip some lines at the buffer beginning, ignoring their
widths.  For example, Info, Dired, and compilation buffers sometimes
have a long header line at the top.  You can use this alist to tell
`fit-frame' to ignore the width of these header lines.

Each item in the alist is of form (MODE . LINES).
 MODE is a major-mode name.
 LINES is the number of lines to skip at the beginning of the buffer.")

(custom-autoload 'fit-frame-skip-header-lines-alist "fit-frame" t)

(autoload 'fit-frame "fit-frame" "\
Resize FRAME to fit its buffer(s).
Does nothing if `fit-frame-inhibit-fitting-flag' is non-nil.

FRAME defaults to the current (i.e. selected) frame.

If non-nil, WIDTH and HEIGHT specify the frame width and height.  To
define them interactively, use a non-negative prefix arg (e.g. `C-9').

To set the width to `fill-column' + `fit-frame-fill-column-margin',
use a negative prefix arg (e.g. `M--').

To fit the frame to all of its displayed buffers, use no prefix arg.
To fit it to just the current buffer, use a plain prefix arg (`C-u').

Fitting a non-empty buffer means resizing the frame to the smallest
size such that the following are both true:

 * The width is at least `fit-frame-min-width' and `window-min-width'.
   The width is at most `fit-frame-max-width(-percent)' and the
   longest line length.

   (However, extra width is allowed for fringe, if shown.)

 * The height is at least `fit-frame-min-height' and
   `window-min-height'.  The height is at most
   `fit-frame-max-height(-percent)' and the number of lines.

You can thus use those user variables to control the maximum and
minimum frame sizes.  The `*-percent' options let you specify the
maximum as a percentage of your display size.

See also options `fit-frame-skip-header-lines-alist' and
`fit-frame-crop-end-blank-flag'.

The following user options control how an empty frame is fit.
An empty frame is a one-window frame displaying an empty buffer.

 * `fit-frame-empty-width', `fit-frame-empty-height' (normal buffer)
 * `fit-frame-empty-special-display-width',
   `fit-frame-empty-special-display-height' (special-display buffer)

Note: `fit-frame' does not take into account wrapping of a menu-bar
line.  There is no easy way to calculate the number of display lines
from such wrapping.

\(fn &optional FRAME WIDTH HEIGHT ALL-WINDOWS-P)" t nil)

(autoload 'fit-frame-to-image "fit-frame" "\
Fit FRAME to the current image.
If FRAME is not the selected frame, fit it to its first image.
Interactively, if frame has already been fit to the image, then
 restore the size from before it was fit.
This function assumes that FRAME has only one window.

\(fn INTERACTIVEP &optional FRAME)" t nil)

(autoload 'fit-frame-or-mouse-drag-vertical-line "fit-frame" "\
If only window in frame, `fit-frame'; else `mouse-drag-vertical-line'.

\(fn START-EVENT)" t nil)

;;;***

;;;### (autoloads (redo-footnotes) "footnote-ext" "footnote-ext.el"
;;;;;;  (18429 49044))
;;; Generated autoloads from footnote-ext.el

(autoload 'redo-footnotes "footnote-ext" "\
Redo all footnotes in a buffer, renumbering and redefining them.
This is useful for resuming work on an article, or for renumbering
after lots of editing has occurred.

If a textual footnote references a non-existent definition, the
footnote mark is removed.  If a definition is no longer referenced, it
is also deleted.

\(fn)" t nil)

;;;***

;;;### (autoloads (ghc-core-mode ghc-core-create-core) "ghc-core"
;;;;;;  "site-lisp/haskell-mode/ghc-core.el" (19501 55706))
;;; Generated autoloads from site-lisp/haskell-mode/ghc-core.el

(autoload 'ghc-core-create-core "ghc-core" "\
Compiled and load the current buffer as tidy core

\(fn)" t nil)

(add-to-list 'auto-mode-alist '("\\.hcr\\'" . ghc-core-mode))

(autoload 'ghc-core-mode "ghc-core" "\
Major mode for GHC Core files.

\(fn)" t nil)

;;;***

;;;### (autoloads (gist-fetch gist-list gist-region-or-buffer-private
;;;;;;  gist-region-or-buffer gist-buffer-private gist-buffer gist-region-private
;;;;;;  gist-region) "gist" "site-lisp/gist/gist.el" (19516 48467))
;;; Generated autoloads from site-lisp/gist/gist.el

(autoload 'gist-region "gist" "\
Post the current region as a new paste at gist.github.com
Copies the URL into the kill ring.

With a prefix argument, makes a private paste.

\(fn BEGIN END &optional PRIVATE &optional CALLBACK)" t nil)

(autoload 'gist-region-private "gist" "\
Post the current region as a new private paste at gist.github.com
Copies the URL into the kill ring.

\(fn BEGIN END)" t nil)

(autoload 'gist-buffer "gist" "\
Post the current buffer as a new paste at gist.github.com.
Copies the URL into the kill ring.

With a prefix argument, makes a private paste.

\(fn &optional PRIVATE)" t nil)

(autoload 'gist-buffer-private "gist" "\
Post the current buffer as a new private paste at gist.github.com.
Copies the URL into the kill ring.

\(fn)" t nil)

(autoload 'gist-region-or-buffer "gist" "\
Post either the current region, or if mark is not set, the current buffer as a new paste at gist.github.com
Copies the URL into the kill ring.

With a prefix argument, makes a private paste.

\(fn &optional PRIVATE)" t nil)

(autoload 'gist-region-or-buffer-private "gist" "\
Post either the current region, or if mark is not set, the current buffer as a new private paste at gist.github.com
Copies the URL into the kill ring.

\(fn)" t nil)

(autoload 'gist-list "gist" "\
Displays a list of all of the current user's gists in a new buffer.

\(fn)" t nil)

(autoload 'gist-fetch "gist" "\
Fetches a Gist and inserts it into a new buffer
If the Gist already exists in a buffer, switches to it

\(fn ID)" t nil)

;;;***

;;;### (autoloads (gnuplot-make-buffer gnuplot-mode) "gnuplot" "site-lisp/gnuplot.el"
;;;;;;  (15866 21475))
;;; Generated autoloads from site-lisp/gnuplot.el

(autoload 'gnuplot-mode "gnuplot" "\
Major mode for editing and executing GNUPLOT scripts.
This was written with version 3.7 of gnuplot in mind but it should
work fine with version 3.5 and the various 3.6 beta versions.

Report bugs in `gnuplot-mode' using \\[gnuplot-bug-report].

			    ------O------

The help functions, keyword completion, and several other features
depend upon having the info file properly installed.  The info file
can be made in the document directory of the gnuplot distribution or
is available at the `gnuplot-mode' web page:
    http://feff.phys.washington.edu/~ravel/software/gnuplot-mode/

If the help function does not work properly, you may have an older
version of the gnuplot info file.  Try the suggestion in the document
string for the variable `gnuplot-info-hook'.  See the `gnuplot-mode'
web page for more details.

			    ------O------

There are several known shortcomings of `gnuplot-mode', version 0.5g
and up.  Many of the shortcomings involve the graphical interface
\(refered to as the GUI) to setting arguments to plot options.  Here is
a list:

 1.  Currently there is no way for `gnuplot-mode' to know if information
     sent to gnuplot was correctly plotted.
 2.  Indentation is sometimes a bit flaky.
 3.  \"plot\", \"splot\", and \"fit\" are handled in the GUI, but are
     a bit flaky.  Their arguments may not be read correctly from
     existing text, and continuation lines (common for plot and splot)
     are not supported.
 4.  The GUI does not know how to read from continuation lines.
 5.  Comma separated position arguments to plot options are
     unsupported in the GUI.  Colon separated datafile modifiers (used
     for plot, splot, and fit) are not supported either.  Arguments
     not yet supported by the GUI generate messages printed in grey
     text.
 6.  The GUI handling of \"hidden3d\" is flaky and \"cntrparam\" is
     unsupported.

			    ------O------

 Key bindings:
 \\{gnuplot-mode-map}

\(fn)" t nil)

(autoload 'gnuplot-make-buffer "gnuplot" "\
Open a new buffer in `gnuplot-mode'.
When invoked, it switches to a new, empty buffer visiting no file
and then starts `gnuplot-mode'.

It is convenient to bind this function to a global key sequence.  For
example, to make the F10 key open a gnuplot script buffer, put the
following in your .emacs file:
     (autoload 'gnuplot-make-buffer \"gnuplot\"
               \"open a buffer in gnuplot mode\" t)
     (global-set-key [(f10)] 'gnuplot-make-buffer)

\(fn)" t nil)

;;;***

;;;### (autoloads (haskell-c-mode) "haskell-c" "site-lisp/haskell-mode/haskell-c.el"
;;;;;;  (19501 55706))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-c.el

(add-to-list 'auto-mode-alist '("\\.hsc\\'" . haskell-c-mode))

(autoload 'haskell-c-mode "haskell-c" "\
Major mode for Haskell FFI files.

\(fn)" t nil)

;;;***

;;;### (autoloads (haskell-cabal-mode) "haskell-cabal" "site-lisp/haskell-mode/haskell-cabal.el"
;;;;;;  (19501 55706))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-cabal.el

(add-to-list 'auto-mode-alist '("\\.cabal\\'" . haskell-cabal-mode))

(autoload 'haskell-cabal-mode "haskell-cabal" "\
Major mode for Cabal package description files.

\(fn)" t nil)

;;;***

;;;### (autoloads (haskell-decl-scan-mode) "haskell-decl-scan" "site-lisp/haskell-mode/haskell-decl-scan.el"
;;;;;;  (19501 55706))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-decl-scan.el

(autoload 'haskell-decl-scan-mode "haskell-decl-scan" "\
Minor mode for declaration scanning for Haskell mode.
Top-level declarations are scanned and listed in the menu item \"Declarations\".
Selecting an item from this menu will take point to the start of the
declaration.

\\[haskell-ds-forward-decl] and \\[haskell-ds-backward-decl] move forward and backward to the start of a declaration.

Under XEmacs, the following keys are also defined:

\\[fume-list-functions] lists the declarations of the current buffer,
\\[fume-prompt-function-goto] prompts for a declaration to move to, and
\\[fume-mouse-function-goto] moves to the declaration whose name is at point.

This may link with `haskell-doc' (only for Emacs currently).

For non-literate and LaTeX-style literate scripts, we assume the
common convention that top-level declarations start at the first
column.  For Bird-style literate scripts, we assume the common
convention that top-level declarations start at the third column,
ie. after \"> \".

Anything in `font-lock-comment-face' is not considered for a
declaration.  Therefore, using Haskell font locking with comments
coloured in `font-lock-comment-face' improves declaration scanning.

To turn on declaration scanning for all Haskell buffers, add this to
.emacs:

  (add-hook 'haskell-mode-hook 'turn-on-haskell-decl-scan)

To turn declaration scanning on for the current buffer, call
`turn-on-haskell-decl-scan'.

Literate Haskell scripts are supported: If the value of
`haskell-literate' (automatically set by the Haskell mode of
Moss&Thorn) is `bird', a Bird-style literate script is assumed.  If it
is nil or `tex', a non-literate or LaTeX-style literate script is
assumed, respectively.

Invokes `haskell-decl-scan-mode-hook'.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (haskell-doc-show-type haskell-doc-mode) "haskell-doc"
;;;;;;  "site-lisp/haskell-mode/haskell-doc.el" (19501 55706))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-doc.el

(autoload 'haskell-doc-mode "haskell-doc" "\
Enter `haskell-doc-mode' for showing fct types in the echo area.
See variable docstring.

\(fn &optional ARG)" t nil)

(defalias 'turn-on-haskell-doc-mode 'haskell-doc-mode)

(autoload 'haskell-doc-show-type "haskell-doc" "\
Show the type of the function near point.
For the function under point, show the type in the echo area.
This information is extracted from the `haskell-doc-prelude-types' alist
of prelude functions and their types, or from the local functions in the
current buffer.

\(fn &optional SYM)" t nil)

;;;***

;;;### (autoloads (haskell-indent-mode) "haskell-indent" "site-lisp/haskell-mode/haskell-indent.el"
;;;;;;  (19501 55706))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-indent.el

(autoload 'haskell-indent-mode "haskell-indent" "\
``Intelligent'' Haskell indentation mode.
This deals with the layout rule of Haskell.
\\[haskell-indent-cycle] starts the cycle which proposes new
possibilities as long as the TAB key is pressed.  Any other key
or mouse click terminates the cycle and is interpreted except for
RET which merely exits the cycle.
Other special keys are:
    \\[haskell-indent-insert-equal]
      inserts an =
    \\[haskell-indent-insert-guard]
      inserts an |
    \\[haskell-indent-insert-otherwise]
      inserts an | otherwise =
these functions also align the guards and rhs of the current definition
    \\[haskell-indent-insert-where]
      inserts a where keyword
    \\[haskell-indent-align-guards-and-rhs]
      aligns the guards and rhs of the region
    \\[haskell-indent-put-region-in-literate]
      makes the region a piece of literate code in a literate script

Invokes `haskell-indent-hook' if not nil.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (haskell-hayoo haskell-hoogle literate-haskell-mode
;;;;;;  haskell-mode) "haskell-mode" "site-lisp/haskell-mode/haskell-mode.el"
;;;;;;  (19501 55706))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-mode.el

(add-to-list 'load-path (or (file-name-directory load-file-name) (car load-path)))

(autoload 'haskell-mode "haskell-mode" "\
Major mode for editing Haskell programs.
Blank lines separate paragraphs, comments start with `-- '.
\\<haskell-mode-map>
Literate scripts are supported via `literate-haskell-mode'.
The variable `haskell-literate' indicates the style of the script in the
current buffer.  See the documentation on this variable for more details.

Modules can hook in via `haskell-mode-hook'.  The following modules
are supported with an `autoload' command:

   `haskell-decl-scan', Graeme E Moss
     Scans top-level declarations, and places them in a menu.

   `haskell-doc', Hans-Wolfgang Loidl
     Echoes types of functions or syntax of keywords when the cursor is idle.

   `haskell-indentation', Kristof Bastiaensen
     Intelligent semi-automatic indentation Mk2

   `haskell-indent', Guy Lapalme
     Intelligent semi-automatic indentation.

   `haskell-simple-indent', Graeme E Moss and Heribert Schuetz
     Simple indentation.

Module X is activated using the command `turn-on-X'.  For example,
`haskell-indent' is activated using `turn-on-haskell-indent'.
For more information on a module, see the help for its `X-mode'
function.  Some modules can be deactivated using `turn-off-X'.  (Note
that `haskell-doc' is irregular in using `turn-(on/off)-haskell-doc-mode'.)

Use `haskell-version' to find out what version this is.

Invokes `haskell-mode-hook'.

\(fn)" t nil)

(autoload 'literate-haskell-mode "haskell-mode" "\
As `haskell-mode' but for literate scripts.

\(fn)" t nil)
(add-to-list 'auto-mode-alist        '("\\.\\(?:[gh]s\\|hi\\)\\'" . haskell-mode))
(add-to-list 'auto-mode-alist        '("\\.l[gh]s\\'" . literate-haskell-mode))
(add-to-list 'interpreter-mode-alist '("runghc" . haskell-mode))
(add-to-list 'interpreter-mode-alist '("runhaskell" . haskell-mode))

(autoload 'haskell-hoogle "haskell-mode" "\
Do a Hoogle search for QUERY.

\(fn QUERY)" t nil)

(defalias 'hoogle 'haskell-hoogle)

(autoload 'haskell-hayoo "haskell-mode" "\
Do a Hayoo search for QUERY.

\(fn QUERY)" t nil)

(defalias 'hayoo 'haskell-hayoo)

;;;***

;;;### (autoloads (ido-completing-read ido-read-directory-name ido-read-file-name
;;;;;;  ido-read-buffer ido-dired ido-insert-file ido-write-file
;;;;;;  ido-find-file-other-frame ido-display-file ido-find-file-read-only-other-frame
;;;;;;  ido-find-file-read-only-other-window ido-find-file-read-only
;;;;;;  ido-find-alternate-file ido-find-file-other-window ido-find-file
;;;;;;  ido-find-file-in-dir ido-switch-buffer-other-frame ido-insert-buffer
;;;;;;  ido-kill-buffer ido-display-buffer ido-switch-buffer-other-window
;;;;;;  ido-switch-buffer ido-mode ido-mode) "ido" "ido.el" (20011
;;;;;;  17574))
;;; Generated autoloads from ido.el

(defvar ido-mode nil "\
Determines for which functional group (buffer and files) ido behavior
should be enabled.  The following values are possible:
- `buffer': Turn only on ido buffer behavior (switching, killing,
  displaying...)
- `file': Turn only on ido file behavior (finding, writing, inserting...)
- `both': Turn on ido buffer and file behavior.
- `nil': Turn off any ido switching.

Setting this variable directly does not take effect;
use either \\[customize] or the function `ido-mode'.")

(custom-autoload 'ido-mode "ido" nil)

(autoload 'ido-mode "ido" "\
Toggle ido speed-ups on or off.
With ARG, turn ido speed-up on if arg is positive, off otherwise.
Turning on ido-mode will remap (via a minor-mode keymap) the default
keybindings for the `find-file' and `switch-to-buffer' families of
commands to the ido versions of these functions.
However, if ARG arg equals 'files, remap only commands for files, or
if it equals 'buffers, remap only commands for buffer switching.
This function also adds a hook to the minibuffer.

\(fn &optional ARG)" t nil)

(autoload 'ido-switch-buffer "ido" "\
Switch to another buffer.
The buffer is displayed according to `ido-default-buffer-method' -- the
default is to show it in the same window, unless it is already visible
in another frame.

As you type in a string, all of the buffers matching the string are
displayed if substring-matching is used (default).  Look at
`ido-enable-prefix' and `ido-toggle-prefix'.  When you have found the
buffer you want, it can then be selected.  As you type, most keys have
their normal keybindings, except for the following: \\<ido-buffer-completion-map>

RET Select the buffer at the front of the list of matches.  If the
list is empty, possibly prompt to create new buffer.

\\[ido-select-text] Select the current prompt as the buffer.
If no buffer is found, prompt for a new one.

\\[ido-next-match] Put the first element at the end of the list.
\\[ido-prev-match] Put the last element at the start of the list.
\\[ido-complete] Complete a common suffix to the current string that
matches all buffers.  If there is only one match, select that buffer.
If there is no common suffix, show a list of all matching buffers
in a separate window.
\\[ido-edit-input] Edit input string.
\\[ido-fallback-command] Fallback to non-ido version of current command.
\\[ido-toggle-regexp] Toggle regexp searching.
\\[ido-toggle-prefix] Toggle between substring and prefix matching.
\\[ido-toggle-case] Toggle case-sensitive searching of buffer names.
\\[ido-completion-help] Show list of matching buffers in separate window.
\\[ido-enter-find-file] Drop into `ido-find-file'.
\\[ido-kill-buffer-at-head] Kill buffer at head of buffer list.
\\[ido-toggle-ignore] Toggle ignoring buffers listed in `ido-ignore-buffers'.

\(fn)" t nil)

(autoload 'ido-switch-buffer-other-window "ido" "\
Switch to another buffer and show it in another window.
The buffer name is selected interactively by typing a substring.
For details of keybindings, see `ido-switch-buffer'.

\(fn)" t nil)

(autoload 'ido-display-buffer "ido" "\
Display a buffer in another window but don't select it.
The buffer name is selected interactively by typing a substring.
For details of keybindings, see `ido-switch-buffer'.

\(fn)" t nil)

(autoload 'ido-kill-buffer "ido" "\
Kill a buffer.
The buffer name is selected interactively by typing a substring.
For details of keybindings, see `ido-switch-buffer'.

\(fn)" t nil)

(autoload 'ido-insert-buffer "ido" "\
Insert contents of a buffer in current buffer after point.
The buffer name is selected interactively by typing a substring.
For details of keybindings, see `ido-switch-buffer'.

\(fn)" t nil)

(autoload 'ido-switch-buffer-other-frame "ido" "\
Switch to another buffer and show it in another frame.
The buffer name is selected interactively by typing a substring.
For details of keybindings, see `ido-switch-buffer'.

\(fn)" t nil)

(autoload 'ido-find-file-in-dir "ido" "\
Switch to another file starting from DIR.

\(fn DIR)" t nil)

(autoload 'ido-find-file "ido" "\
Edit file with name obtained via minibuffer.
The file is displayed according to `ido-default-file-method' -- the
default is to show it in the same window, unless it is already
visible in another frame.

The file name is selected interactively by typing a substring.  As you
type in a string, all of the filenames matching the string are displayed
if substring-matching is used (default).  Look at `ido-enable-prefix' and
`ido-toggle-prefix'.  When you have found the filename you want, it can
then be selected.  As you type, most keys have their normal keybindings,
except for the following: \\<ido-file-completion-map>

RET Select the file at the front of the list of matches.  If the
list is empty, possibly prompt to create new file.

\\[ido-select-text] Select the current prompt as the buffer or file.
If no buffer or file is found, prompt for a new one.

\\[ido-next-match] Put the first element at the end of the list.
\\[ido-prev-match] Put the last element at the start of the list.
\\[ido-complete] Complete a common suffix to the current string that
matches all files.  If there is only one match, select that file.
If there is no common suffix, show a list of all matching files
in a separate window.
\\[ido-edit-input] Edit input string (including directory).
\\[ido-prev-work-directory] or \\[ido-next-work-directory] go to previous/next directory in work directory history.
\\[ido-merge-work-directories] search for file in the work directory history.
\\[ido-forget-work-directory] removes current directory from the work directory history.
\\[ido-prev-work-file] or \\[ido-next-work-file] cycle through the work file history.
\\[ido-wide-find-file-or-pop-dir] and \\[ido-wide-find-dir-or-delete-dir] prompts and uses find to locate files or directories.
\\[ido-make-directory] prompts for a directory to create in current directory.
\\[ido-fallback-command] Fallback to non-ido version of current command.
\\[ido-toggle-regexp] Toggle regexp searching.
\\[ido-toggle-prefix] Toggle between substring and prefix matching.
\\[ido-toggle-case] Toggle case-sensitive searching of file names.
\\[ido-toggle-vc] Toggle version control for this file.
\\[ido-toggle-literal] Toggle literal reading of this file.
\\[ido-completion-help] Show list of matching files in separate window.
\\[ido-toggle-ignore] Toggle ignoring files listed in `ido-ignore-files'.

\(fn)" t nil)

(autoload 'ido-find-file-other-window "ido" "\
Switch to another file and show it in another window.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-find-alternate-file "ido" "\
Switch to another file and show it in another window.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-find-file-read-only "ido" "\
Edit file read-only with name obtained via minibuffer.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-find-file-read-only-other-window "ido" "\
Edit file read-only in other window with name obtained via minibuffer.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-find-file-read-only-other-frame "ido" "\
Edit file read-only in other frame with name obtained via minibuffer.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-display-file "ido" "\
Display a file in another window but don't select it.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-find-file-other-frame "ido" "\
Switch to another file and show it in another frame.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-write-file "ido" "\
Write current buffer to a file.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-insert-file "ido" "\
Insert contents of file in current buffer.
The file name is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-dired "ido" "\
Call `dired' the ido way.
The directory is selected interactively by typing a substring.
For details of keybindings, see `ido-find-file'.

\(fn)" t nil)

(autoload 'ido-read-buffer "ido" "\
Ido replacement for the built-in `read-buffer'.
Return the name of a buffer selected.
PROMPT is the prompt to give to the user.  DEFAULT if given is the default
buffer to be selected, which will go to the front of the list.
If REQUIRE-MATCH is non-nil, an existing buffer must be selected.

\(fn PROMPT &optional DEFAULT REQUIRE-MATCH)" nil nil)

(autoload 'ido-read-file-name "ido" "\
Ido replacement for the built-in `read-file-name'.
Read file name, prompting with PROMPT and completing in directory DIR.
See `read-file-name' for additional parameters.

\(fn PROMPT &optional DIR DEFAULT-FILENAME MUSTMATCH INITIAL PREDICATE)" nil nil)

(autoload 'ido-read-directory-name "ido" "\
Ido replacement for the built-in `read-directory-name'.
Read directory name, prompting with PROMPT and completing in directory DIR.
See `read-directory-name' for additional parameters.

\(fn PROMPT &optional DIR DEFAULT-DIRNAME MUSTMATCH INITIAL)" nil nil)

(autoload 'ido-completing-read "ido" "\
Ido replacement for the built-in `completing-read'.
Read a string in the minibuffer with ido-style completion.
PROMPT is a string to prompt with; normally it ends in a colon and a space.
CHOICES is a list of strings which are the possible completions.
PREDICATE is currently ignored; it is included to be compatible
 with `completing-read'.
If REQUIRE-MATCH is non-nil, the user is not allowed to exit unless
 the input is (or completes to) an element of CHOICES or is null.
 If the input is null, `ido-completing-read' returns DEF, or an empty
 string if DEF is nil, regardless of the value of REQUIRE-MATCH.
If INITIAL-INPUT is non-nil, insert it in the minibuffer initially,
 with point positioned at the end.
HIST, if non-nil, specifies a history list.
DEF, if non-nil, is the default value.

\(fn PROMPT CHOICES &optional PREDICATE REQUIRE-MATCH INITIAL-INPUT HIST DEF)" nil nil)

;;;***

;;;### (autoloads (inferior-haskell-find-haddock inferior-haskell-find-definition
;;;;;;  inferior-haskell-info inferior-haskell-type inferior-haskell-load-and-run
;;;;;;  inferior-haskell-load-file switch-to-haskell) "inf-haskell"
;;;;;;  "site-lisp/haskell-mode/inf-haskell.el" (19501 55706))
;;; Generated autoloads from site-lisp/haskell-mode/inf-haskell.el

(defalias 'run-haskell 'switch-to-haskell)

(autoload 'switch-to-haskell "inf-haskell" "\
Show the inferior-haskell buffer.  Start the process if needed.

\(fn &optional ARG)" t nil)

(autoload 'inferior-haskell-load-file "inf-haskell" "\
Pass the current buffer's file to the inferior haskell process.
If prefix arg \\[universal-argument] is given, just reload the previous file.

\(fn &optional RELOAD)" t nil)

(autoload 'inferior-haskell-load-and-run "inf-haskell" "\
Pass the current buffer's file to haskell and then run a COMMAND.

\(fn COMMAND)" t nil)

(autoload 'inferior-haskell-type "inf-haskell" "\
Query the haskell process for the type of the given expression.
If optional argument `insert-value' is non-nil, insert the type above point
in the buffer.  This can be done interactively with the \\[universal-argument] prefix.
The returned info is cached for reuse by `haskell-doc-mode'.

\(fn EXPR &optional INSERT-VALUE)" t nil)

(autoload 'inferior-haskell-info "inf-haskell" "\
Query the haskell process for the info of the given expression.

\(fn SYM)" t nil)

(autoload 'inferior-haskell-find-definition "inf-haskell" "\
Attempt to locate and jump to the definition of the given expression.

\(fn SYM)" t nil)

(autoload 'inferior-haskell-find-haddock "inf-haskell" "\
Find and open the Haddock documentation of SYM.
Make sure to load the file into GHCi or Hugs first by using C-c C-l.
Only works for functions in a package installed with ghc-pkg, or
whatever the value of `haskell-package-manager-name' is.

This function needs to find which package a given module belongs
to.  In order to do this, it computes a module-to-package lookup
alist, which is expensive to compute (it takes upwards of five
seconds with more than about thirty installed packages).  As a
result, we cache it across sessions using the cache file
referenced by `inferior-haskell-module-alist-file'. We test to
see if this is newer than `haskell-package-conf-file' every time
we load it.

\(fn SYM)" t nil)

;;;***

;;;### (autoloads (global-linum-mode linum-mode linum-format) "linum"
;;;;;;  "site-lisp/linum.el" (19516 48981))
;;; Generated autoloads from site-lisp/linum.el

(defvar linum-format 'dynamic "\
Format used to display line numbers. Either a format string
like \"%7d\", 'dynamic to adapt the width as needed, or a
function that is called with a line number as its argument and
should evaluate to a string to be shown on that line. See also
`linum-before-numbering-hook'.")

(custom-autoload 'linum-format "linum" t)

(autoload 'linum-mode "linum" "\
Toggle display of line numbers in the left marginal area.

\(fn &optional ARG)" t nil)

(defvar global-linum-mode nil "\
Non-nil if Global-Linum mode is enabled.
See the command `global-linum-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `global-linum-mode'.")

(custom-autoload 'global-linum-mode "linum" nil)

(autoload 'global-linum-mode "linum" "\
Toggle Linum mode in every possible buffer.
With prefix ARG, turn Global-Linum mode on if and only if
ARG is positive.
Linum mode is enabled in all buffers where
`linum-on' would do it.
See `linum-mode' for more information on Linum mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (magit-status) "magit" "site-lisp/magit/magit.el"
;;;;;;  (19989 63556))
;;; Generated autoloads from site-lisp/magit/magit.el

(autoload 'magit-status "magit" "\
Not documented

\(fn DIR)" t nil)

;;;***

;;;### (autoloads (markdown-mode) "markdown-mode" "site-lisp/markdown-mode.el"
;;;;;;  (19585 42905))
;;; Generated autoloads from site-lisp/markdown-mode.el

(autoload 'markdown-mode "markdown-mode" "\
Major mode for editing Markdown files.

\(fn)" t nil)

;;;***

;;;### (autoloads (mime-w3m-preview-text/html) "mime-w3m" "site-lisp/emacs-w3m/mime-w3m.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/mime-w3m.el

(autoload 'mime-w3m-preview-text/html "mime-w3m" "\
Not documented

\(fn ENTITY SITUATION)" nil nil)

;;;***

;;;### (autoloads (mo-git-blame-current mo-git-blame-file) "mo-git-blame"
;;;;;;  "site-lisp/mo-git-blame/mo-git-blame.el" (19606 18898))
;;; Generated autoloads from site-lisp/mo-git-blame/mo-git-blame.el

(autoload 'mo-git-blame-file "mo-git-blame" "\
Calls `git blame' for REVISION of FILE-NAME or `HEAD' if
REVISION is not given. Initializes the two windows that will show
the output of 'git blame' and the content.

If FILE-NAME is missing it will be read with `find-file' in
interactive mode.

ORIGINAL-FILE-NAME defaults to FILE-NAME if not given. This is
used for tracking renaming and moving of files during iterative
re-blaming.

With a numeric prefix argument or with NUM-LINES-TO-BLAME only
the NUM-LINES-TO-BLAME lines before and after point are blamed by
using git blame's `-L' option. Otherwise the whole file is
blamed.

\(fn &optional FILE-NAME REVISION ORIGINAL-FILE-NAME NUM-LINES-TO-BLAME)" t nil)

(autoload 'mo-git-blame-current "mo-git-blame" "\
Calls `mo-git-blame-file' for HEAD for the current buffer.

\(fn)" t nil)

;;;***

;;;### (autoloads (nxhtml-byte-recompile-file nxhtml-byte-compile-file
;;;;;;  nxhtml-get-missing-files nxhtml-update-existing-files nxhtml-setup-download-all
;;;;;;  nxhtml-setup-auto-download nxhtml-setup-install) "nxhtml-web-vcs"
;;;;;;  "site-lisp/nxhtml/nxhtml-web-vcs.el" (19385 29876))
;;; Generated autoloads from site-lisp/nxhtml/nxhtml-web-vcs.el

(autoload 'nxhtml-setup-install "nxhtml-web-vcs" "\
Setup and start nXhtml installation.

This is for installation and updating directly from the nXhtml
development sources.

There are two different ways to install:

  (1) Download all at once: `nxhtml-setup-download-all'
  (2) Automatically download part by part: `nxhtml-setup-auto-download'

You can convert between those ways by calling this function again.
You can also do this by setting the option `nxhtml-autoload-web' yourself.

When you have nXhtml installed you can update it:

  (3) Update new files in nXhtml: `nxhtml-update-existing-files'

To learn more about nXhtml visit its home page at URL
`http://www.emacswiki.com/NxhtmlMode/'.

If you want to test auto download (but not use it further) there
is a special function for that, you answer T here:

   (T) Test automatic download part by part: `nxhtml-setup-test-auto-download'

======
*Note*
If you want to download a zip file with latest released version instead then
please see URL `http://ourcomments.org/Emacs/nXhtml/doc/nxhtml.html'.

\(fn WAY)" t nil)

(autoload 'nxhtml-setup-auto-download "nxhtml-web-vcs" "\
Set up to autoload nXhtml files from the web.

This function will download some initial files and then setup to
download the rest when you need them.

Files will be downloaded under the directory root you specify in
DL-DIR.

Note that files will not be upgraded automatically.  The auto
downloading is just for files you are missing. (This may change a
bit in the future.) If you want to upgrade those files that you
have downloaded you can just call `nxhtml-update-existing-files'.

You can easily switch between this mode of downloading or
downloading the whole of nXhtml by once.  To switch just call the
command `nxhtml-setup-install'.

See also the command `nxhtml-setup-download-all'.

Note: If your nXhtml is to old you can't use this function
      directly.  You have to upgrade first, se the function
      above. Version 2.07 or above is good for this.

\(fn DL-DIR)" t nil)

(autoload 'nxhtml-setup-download-all "nxhtml-web-vcs" "\
Download or update all of nXhtml.

You can download all if nXhtml with this command.

To update existing files use `nxhtml-update-existing-files'.

If you want to download only those files you are actually using
then call `nxhtml-setup-auto-download' instead.

See the command `nxhtml-setup-install' for a convenient way to
call these commands.

For more information about auto download of nXhtml files see
`nxhtml-setup-auto-download'.

\(fn DL-DIR)" t nil)

(autoload 'nxhtml-update-existing-files "nxhtml-web-vcs" "\
Update existing nXhtml files from the development sources.
Only files you already have will be updated.

Note that this works both if you have setup nXhtml to auto
download files as you need them or if you have downloaded all of
nXhtml at once.

For more information about installing and updating nXhtml see the
command `nxhtml-setup-install'.

\(fn)" t nil)

(autoload 'nxhtml-get-missing-files "nxhtml-web-vcs" "\
Not documented

\(fn SUB-DIR FILE-NAME-LIST)" nil nil)

(autoload 'nxhtml-byte-compile-file "nxhtml-web-vcs" "\
Not documented

\(fn FILE &optional LOAD)" nil nil)

(autoload 'nxhtml-byte-recompile-file "nxhtml-web-vcs" "\
Byte recompile FILE file if necessary.
For more information see `nxhtml-byte-compile-file'.
Loading is done if recompiled and LOAD is t.

\(fn FILE &optional LOAD)" t nil)

;;;***

;;;### (autoloads (nxhtmlmaint-byte-uncompile-all nxhtmlmaint-byte-recompile
;;;;;;  nxhtmlmaint-start-byte-compilation) "nxhtmlmaint" "site-lisp/nxhtml/nxhtmlmaint.el"
;;;;;;  (19385 29876))
;;; Generated autoloads from site-lisp/nxhtml/nxhtmlmaint.el

(autoload 'nxhtmlmaint-start-byte-compilation "nxhtmlmaint" "\
Start byte compilation of nXhtml in new Emacs instance.
Byte compiling in general makes elisp code run 5-10 times faster
which is quite noticeable when you use nXhtml.

This will also update the file nxhtml-loaddefs.el.

You must restart Emacs to use the byte compiled files.

If for some reason the byte compiled files does not work you can
remove then with `nxhtmlmaint-byte-uncompile-all'.

\(fn)" t nil)

(autoload 'nxhtmlmaint-byte-recompile "nxhtmlmaint" "\
Recompile or compile all nXhtml files in current Emacs.

\(fn)" t nil)

(autoload 'nxhtmlmaint-byte-uncompile-all "nxhtmlmaint" "\
Delete byte compiled files in nXhtml.
This will also update the file nxhtml-loaddefs.el.

See `nxhtmlmaint-start-byte-compilation' for byte compiling.

\(fn)" t nil)

;;;***

;;;### (autoloads (octet-mime-setup mime-view-octet mime-preview-octet
;;;;;;  octet-find-file octet-buffer) "octet" "site-lisp/emacs-w3m/octet.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/octet.el

(autoload 'octet-buffer "octet" "\
View octet-stream content according to `octet-type-filter-alist'.
Optional NAME is the filename.
If optional CONTENT-TYPE is specified, it is used for type guess.

\(fn &optional NAME CONTENT-TYPE)" t nil)

(autoload 'octet-find-file "octet" "\
Find FILE with octet-stream decoding.

\(fn FILE)" t nil)

(autoload 'mime-preview-octet "octet" "\
A method for mime-view to preview octet message.

\(fn ENTITY SITUATION)" nil nil)

(autoload 'mime-view-octet "octet" "\
A method for mime-view to display octet message.

\(fn ENTITY SITUATION)" nil nil)

(autoload 'octet-mime-setup "octet" "\
Octet setting for MIME module.

\(fn)" nil nil)

;;;***

;;;### (autoloads (module-installed-p exec-installed-p file-installed-p
;;;;;;  get-latest-path add-latest-path add-path) "path-util" "site-lisp/apel/path-util.el"
;;;;;;  (19385 28150))
;;; Generated autoloads from site-lisp/apel/path-util.el

(autoload 'add-path "path-util" "\
Add PATH to `load-path' if it exists under `default-load-path'
directories and it does not exist in `load-path'.

You can use following PATH styles:
	load-path relative: \"PATH/\"
			(it is searched from `default-load-path')
	home directory relative: \"~/PATH/\" \"~USER/PATH/\"
	absolute path: \"/HOO/BAR/BAZ/\"

You can specify following OPTIONS:
	'all-paths	search from `load-path'
			instead of `default-load-path'
	'append		add PATH to the last of `load-path'

\(fn PATH &rest OPTIONS)" nil nil)

(autoload 'add-latest-path "path-util" "\
Add latest path matched by PATTERN to `load-path'
if it exists under `default-load-path' directories
and it does not exist in `load-path'.

If optional argument ALL-PATHS is specified, it is searched from all
of load-path instead of default-load-path.

\(fn PATTERN &optional ALL-PATHS)" nil nil)

(autoload 'get-latest-path "path-util" "\
Return latest directory in default-load-path
which is matched to regexp PATTERN.
If optional argument ALL-PATHS is specified,
it is searched from all of load-path instead of default-load-path.

\(fn PATTERN &optional ALL-PATHS)" nil nil)

(autoload 'file-installed-p "path-util" "\
Return absolute-path of FILE if FILE exists in PATHS.
If PATHS is omitted, `load-path' is used.

\(fn FILE &optional PATHS)" nil nil)

(defvar exec-suffix-list '("") "\
*List of suffixes for executable.")

(autoload 'exec-installed-p "path-util" "\
Return absolute-path of FILE if FILE exists in PATHS.
If PATHS is omitted, `exec-path' is used.
If suffixes is omitted, `exec-suffix-list' is used.

\(fn FILE &optional PATHS SUFFIXES)" nil nil)

(autoload 'module-installed-p "path-util" "\
Return t if module is provided or exists in PATHS.
If PATHS is omitted, `load-path' is used.

\(fn MODULE &optional PATHS)" nil nil)

;;;***

;;;### (autoloads (svn-status svn-checkout) "psvn" "site-lisp/psvn.el"
;;;;;;  (18429 49078))
;;; Generated autoloads from site-lisp/psvn.el

(autoload 'svn-checkout "psvn" "\
Run svn checkout REPOS-URL PATH.

\(fn REPOS-URL PATH)" t nil)
 (defalias 'svn-examine 'svn-status)

(autoload 'svn-status "psvn" "\
Examine the status of Subversion working copy in directory DIR.
If ARG is -, allow editing of the parameters. One could add -N to
run svn status non recursively to make it faster.
For every other non nil ARG pass the -u argument to `svn status', which
asks svn to connect to the repository and check to see if there are updates
there.

If there is no .svn directory, examine if there is CVS and run
`cvs-examine'. Otherwise ask if to run `dired'.

\(fn DIR &optional ARG)" t nil)

;;;***

;;;### (autoloads (puppet-mode) "puppet-mode" "site-lisp/puppet-mode.el"
;;;;;;  (18888 14284))
;;; Generated autoloads from site-lisp/puppet-mode.el

(autoload 'puppet-mode "puppet-mode" "\
Major mode for editing puppet manifests.

The variable puppet-indent-level controls the amount of indentation.
\\{puppet-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads (py-shell python-mode empty-line-p) "python-mode"
;;;;;;  "site-lisp/python-mode/python-mode.el" (20008 23912))
;;; Generated autoloads from site-lisp/python-mode/python-mode.el

(autoload 'empty-line-p "python-mode" "\
Returns t if cursor is at an empty line, nil otherwise.

\(fn &optional IACT)" t nil)

(autoload 'python-mode "python-mode" "\
Major mode for editing Python files.
To submit a problem report, enter `\\[py-submit-bug-report]' from a
`python-mode' buffer.  Do `\\[py-describe-mode]' for detailed
documentation.  To see what version of `python-mode' you are running,
enter `\\[py-version]'.

This mode knows about Python indentation, tokens, comments and
continuation lines.  Paragraphs are separated by blank lines only.

COMMANDS
\\{py-mode-map}
VARIABLES

py-indent-offset		indentation increment
py-block-comment-prefix		comment string used by `comment-region'
py-python-command		shell command to invoke Python interpreter
py-temp-directory		directory used for temp files (if needed)
py-beep-if-tab-change		ring the bell if `tab-width' is changed

\(fn)" t nil)

(let ((modes '(("jython" . jython-mode) ("python" . python-mode) ("python3" . python-mode)))) (while modes (when (not (assoc (car modes) interpreter-mode-alist)) (push (car modes) interpreter-mode-alist)) (setq modes (cdr modes))))

(when (not (or (rassq 'python-mode auto-mode-alist) (rassq 'jython-mode auto-mode-alist))) (push '("\\.py$" . python-mode) auto-mode-alist))

(autoload 'py-shell "python-mode" "\
Start an interactive Python interpreter in another window.
This is like Shell mode, except that Python is running in the window
instead of a shell.  See the `Interactive Shell' and `Shell Mode'
sections of the Emacs manual for details, especially for the key
bindings active in the `*Python*' buffer.

With optional \\[universal-argument], the user is prompted for the
flags to pass to the Python interpreter.  This has no effect when this
command is used to switch to an existing process, only when a new
process is started.  If you use this, you will probably want to ensure
that the current arguments are retained (they will be included in the
prompt).  This argument is ignored when this function is called
programmatically, or when running in Emacs 19.34 or older.

Note: You can toggle between using the CPython interpreter and the
Jython interpreter by hitting \\[py-toggle-shells].  This toggles
buffer local variables which control whether all your subshell
interactions happen to the `*Jython*' or `*Python*' buffers (the
latter is the name used for the CPython buffer).

Warning: Don't use an interactive Python if you change sys.ps1 or
sys.ps2 from their default values, or if you're running code that
prints `>>> ' or `... ' at the start of a line.  `python-mode' can't
distinguish your output from Python's output, and assumes that `>>> '
at the start of a line is a prompt from Python.  Similarly, the Emacs
Shell mode code assumes that both `>>> ' and `... ' at the start of a
line are Python prompts.  Bad things can happen if you fool either
mode.

Warning:  If you do any editing *in* the process buffer *while* the
buffer is accepting output from Python, do NOT attempt to `undo' the
changes.  Some of the output (nowhere near the parts you changed!) may
be lost if you do.  This appears to be an Emacs bug, an unfortunate
interaction between undo and process filters; the same problem exists in
non-Python process buffers using the default (Emacs-supplied) process
filter.

\(fn &optional ARGPROMPT)" t nil)

;;;***

;;;### (autoloads (rebase-mode) "rebase-mode" "site-lisp/magit/rebase-mode.el"
;;;;;;  (19989 63405))
;;; Generated autoloads from site-lisp/magit/rebase-mode.el

(autoload 'rebase-mode "rebase-mode" "\
Major mode for editing of a Git rebase file.

Rebase files are generated when you run 'git rebase -i' or run
`magit-interactive-rebase'.  They describe how Git should perform
the rebase.  See the documentation for git-rebase (e.g., by
running 'man git-rebase' at the command line) for details.

\(fn)" t nil)

(add-to-list 'auto-mode-alist '("git-rebase-todo" . rebase-mode))

;;;***

;;;### (autoloads (richtext-decode richtext-encode) "richtext" "site-lisp/apel/richtext.el"
;;;;;;  (19385 28150))
;;; Generated autoloads from site-lisp/apel/richtext.el

(autoload 'richtext-encode "richtext" "\
Not documented

\(fn FROM TO)" nil nil)

(autoload 'richtext-decode "richtext" "\
Not documented

\(fn FROM TO)" nil nil)

;;;***

;;;### (autoloads (ruby-mode) "ruby-mode" "site-lisp/ruby-mode/ruby-mode.el"
;;;;;;  (19385 30190))
;;; Generated autoloads from site-lisp/ruby-mode/ruby-mode.el

(autoload 'ruby-mode "ruby-mode" "\
Major mode for editing ruby scripts.
\\[ruby-indent-command] properly indents subexpressions of multi-line
class, module, def, if, while, for, do, and case statements, taking
nesting into account.

The variable ruby-indent-level controls the amount of indentation.
\\{ruby-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads (rubydb) "rubydb2x" "site-lisp/ruby-mode/rubydb2x.el"
;;;;;;  (19385 30190))
;;; Generated autoloads from site-lisp/ruby-mode/rubydb2x.el

(autoload 'rubydb "rubydb2x" "\
Run rubydb on program FILE in buffer *gud-FILE*.
The directory containing FILE becomes the initial working directory
and source-file directory for your debugger.

\(fn COMMAND-LINE)" t nil)

;;;***

;;;### (autoloads (rubydb) "rubydb3x" "site-lisp/ruby-mode/rubydb3x.el"
;;;;;;  (19385 30190))
;;; Generated autoloads from site-lisp/ruby-mode/rubydb3x.el

(autoload 'rubydb "rubydb3x" "\
Run rubydb on program FILE in buffer *gud-FILE*.
The directory containing FILE becomes the initial working directory
and source-file directory for your debugger.

\(fn COMMAND-LINE)" t nil)

;;;***

;;;### (autoloads (session-initialize) "session" "site-lisp/session.el"
;;;;;;  (18429 49078))
;;; Generated autoloads from site-lisp/session.el

(autoload 'session-initialize "session" "\
Initialize package session and read previous session file.
Setup hooks and load `session-save-file', see `session-initialize'.  At
best, this function is called at the end of the Emacs startup, i.e., add
this function to `after-init-hook'.

\(fn &rest DUMMIES)" t nil)

;;;***

;;;### (autoloads (smex-initialize) "smex" "site-lisp/smex.el" (19383
;;;;;;  542))
;;; Generated autoloads from site-lisp/smex.el

(autoload 'smex-initialize "smex" "\
Not documented

\(fn)" t nil)

;;;***

;;;### (autoloads (sr-dired sunrise-cd sunrise) "sunrise-commander"
;;;;;;  "site-lisp/sunrise-commander/sunrise-commander.el" (20016
;;;;;;  40695))
;;; Generated autoloads from site-lisp/sunrise-commander/sunrise-commander.el

(autoload 'sunrise "sunrise-commander" "\
Start the Sunrise Commander.
If LEFT-DIRECTORY is given, the left window will display that
directory (same for RIGHT-DIRECTORY). Specifying nil for any of
these values uses the default, ie. $HOME.

\(fn &optional LEFT-DIRECTORY RIGHT-DIRECTORY FILENAME)" t nil)

(autoload 'sunrise-cd "sunrise-commander" "\
Run Sunrise but give it the current directory to use.

\(fn)" t nil)

(autoload 'sr-dired "sunrise-commander" "\
Visit the given directory in `sr-mode'.

\(fn DIRECTORY &optional SWITCHES)" t nil)

;;;***

;;;### (autoloads nil "sunrise-x-buttons" "site-lisp/sunrise-commander/sunrise-x-buttons.el"
;;;;;;  (20015 24445))
;;; Generated autoloads from site-lisp/sunrise-commander/sunrise-x-buttons.el
 (require 'sunrise-x-buttons)

;;;***

;;;### (autoloads nil "sunrise-x-loop" "site-lisp/sunrise-commander/sunrise-x-loop.el"
;;;;;;  (20015 24445))
;;; Generated autoloads from site-lisp/sunrise-commander/sunrise-x-loop.el
 (require 'sunrise-x-loop)

;;;***

;;;### (autoloads nil "sunrise-x-mirror" "site-lisp/sunrise-commander/sunrise-x-mirror.el"
;;;;;;  (20015 24445))
;;; Generated autoloads from site-lisp/sunrise-commander/sunrise-x-mirror.el
 (require 'sunrise-x-mirror)

;;;***

;;;### (autoloads nil "sunrise-x-modeline" "site-lisp/sunrise-commander/sunrise-x-modeline.el"
;;;;;;  (20015 31664))
;;; Generated autoloads from site-lisp/sunrise-commander/sunrise-x-modeline.el
 (require 'sunrise-x-modeline)

;;;***

;;;### (autoloads nil "sunrise-x-popviewer" "site-lisp/sunrise-commander/sunrise-x-popviewer.el"
;;;;;;  (20015 24445))
;;; Generated autoloads from site-lisp/sunrise-commander/sunrise-x-popviewer.el
 (require 'sunrise-x-popviewer)

;;;***

;;;### (autoloads nil "sunrise-x-tabs" "site-lisp/sunrise-commander/sunrise-x-tabs.el"
;;;;;;  (20015 24445))
;;; Generated autoloads from site-lisp/sunrise-commander/sunrise-x-tabs.el
 (require 'sunrise-x-tabs)

;;;***

;;;### (autoloads nil "sunrise-x-tree" "site-lisp/sunrise-commander/sunrise-x-tree.el"
;;;;;;  (20015 24445))
;;; Generated autoloads from site-lisp/sunrise-commander/sunrise-x-tree.el
 (require 'sunrise-x-tree)

;;;***

;;;### (autoloads (visit-url) "visit-url" "visit-url.el" (18429 49044))
;;; Generated autoloads from visit-url.el

(autoload 'visit-url "visit-url" "\
Not documented

\(fn &optional URL)" t nil)

;;;***

;;;### (autoloads (w3m-buffer w3m-region w3m-find-file w3m-browse-url
;;;;;;  w3m w3m-gohome w3m-goto-url-new-session w3m-goto-url w3m-download
;;;;;;  w3m-retrieve) "w3m" "site-lisp/emacs-w3m/w3m.el" (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m.el

(autoload 'w3m-retrieve "w3m" "\
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

NO-UNCOMPRESS specifies whether this function should not uncompress contents.
NO-CACHE specifies whether this function should not use cached contents.
POST-DATA and REFERER will be sent to the web server with a request.

\(fn URL &optional NO-UNCOMPRESS NO-CACHE POST-DATA REFERER HANDLER)" nil nil)

(autoload 'w3m-download "w3m" "\
Download contents of URL to a file named FILENAME.
NO-CHACHE (which the prefix argument gives when called interactively)
specifies not using the cached data.

\(fn URL &optional FILENAME NO-CACHE HANDLER POST-DATA)" t nil)

(autoload 'w3m-goto-url "w3m" "\
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
The remaining HANDLER, ELEMENT[1], and NO-POPUP are for the
internal operations of emacs-w3m.
You can also use \"quicksearch\" url schemes such as \"gg:emacs\" which
would search for the term \"emacs\" with the Google search engine.  See
the `w3m-search' function and the variable `w3m-uri-replace-alist'.

\[1] A note for the developers: ELEMENT is a history element which has
already been registered in the `w3m-history-flat' variable.  It is
corresponding to URL to be retrieved at this time, not for the url of
the current page.

\(fn URL &optional RELOAD CHARSET POST-DATA REFERER HANDLER ELEMENT NO-POPUP)" t nil)

(autoload 'w3m-goto-url-new-session "w3m" "\
Visit World Wide Web pages in a new session.
If you invoke this command in the emacs-w3m buffer, the new session
will be created by copying the current session.  Otherwise, the new
session will start afresh.

\(fn URL &optional RELOAD CHARSET POST-DATA REFERER)" t nil)

(autoload 'w3m-gohome "w3m" "\
Go to the Home page.

\(fn)" t nil)

(autoload 'w3m "w3m" "\
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
interactive command in the batch mode.

\(fn &optional URL NEW-SESSION INTERACTIVE-P)" t nil)

(autoload 'w3m-browse-url "w3m" "\
Ask emacs-w3m to browse URL.
NEW-SESSION specifies whether to create a new emacs-w3m session.  URL
defaults to the string looking like a url around the cursor position.
Pop to a window or a frame up according to `w3m-pop-up-windows' and
`w3m-pop-up-frames'.

\(fn URL &optional NEW-SESSION)" t nil)

(autoload 'w3m-find-file "w3m" "\
Function used to open FILE whose name is expressed in ordinary format.
The file name will be converted into the file: scheme.

\(fn FILE)" t nil)

(autoload 'w3m-region "w3m" "\
Render the region of the current buffer between START and END.
URL specifies the address where the contents come from.  It can be
omitted or nil when the address is not identified.  CHARSET is used
for decoding the contents.  If it is nil, this function attempts to
parse the meta tag to extract the charset.

\(fn START END &optional URL CHARSET)" t nil)

(autoload 'w3m-buffer "w3m" "\
Render the current buffer.
See `w3m-region' for the optional arguments.

\(fn &optional URL CHARSET)" t nil)

;;;***

;;;### (autoloads (w3m-antenna w3m-about-antenna) "w3m-antenna" "site-lisp/emacs-w3m/w3m-antenna.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-antenna.el

(autoload 'w3m-about-antenna "w3m-antenna" "\
Not documented

\(fn URL &optional NO-DECODE NO-CACHE POST-DATA REFERER HANDLER)" nil nil)

(autoload 'w3m-antenna "w3m-antenna" "\
Report changes of WEB sites, which is specified in `w3m-antenna-sites'.

\(fn &optional NO-CACHE)" t nil)

;;;***

;;;### (autoloads (w3m-setup-bookmark-menu w3m-about-bookmark w3m-bookmark-view-new-session
;;;;;;  w3m-bookmark-view w3m-bookmark-add-current-url-group w3m-bookmark-add-all-urls
;;;;;;  w3m-bookmark-add-current-url w3m-bookmark-add-this-url) "w3m-bookmark"
;;;;;;  "site-lisp/emacs-w3m/w3m-bookmark.el" (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-bookmark.el

(autoload 'w3m-bookmark-add-this-url "w3m-bookmark" "\
Add link under cursor to bookmark.

\(fn)" t nil)

(autoload 'w3m-bookmark-add-current-url "w3m-bookmark" "\
Add a url of the current page to the bookmark.
With prefix, ask for a new url instead of the present one.

\(fn &optional ARG)" t nil)

(autoload 'w3m-bookmark-add-all-urls "w3m-bookmark" "\
Add urls of all pages being visited to the bookmark.

\(fn)" t nil)

(autoload 'w3m-bookmark-add-current-url-group "w3m-bookmark" "\
Add link of the group of current urls to the bookmark.

\(fn)" t nil)

(autoload 'w3m-bookmark-view "w3m-bookmark" "\
Display the bookmark.

\(fn &optional RELOAD)" t nil)

(autoload 'w3m-bookmark-view-new-session "w3m-bookmark" "\
Display the bookmark on a new session.

\(fn &optional RELOAD)" t nil)

(autoload 'w3m-about-bookmark "w3m-bookmark" "\
Not documented

\(fn &rest ARGS)" nil nil)

(autoload 'w3m-setup-bookmark-menu "w3m-bookmark" "\
Setup w3m bookmark items in menubar.

\(fn)" nil nil)

;;;***

;;;### (autoloads (w3m-about-cookie w3m-cookie w3m-cookie-get w3m-cookie-set
;;;;;;  w3m-cookie-shutdown) "w3m-cookie" "site-lisp/emacs-w3m/w3m-cookie.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-cookie.el

(autoload 'w3m-cookie-shutdown "w3m-cookie" "\
Save cookies, and reset cookies' data.

\(fn)" t nil)

(autoload 'w3m-cookie-set "w3m-cookie" "\
Register cookies which correspond to URL.
BEG and END should be an HTTP response header region on current buffer.

\(fn URL BEG END)" nil nil)

(autoload 'w3m-cookie-get "w3m-cookie" "\
Get a cookie field string which corresponds to the URL.

\(fn URL)" nil nil)

(autoload 'w3m-cookie "w3m-cookie" "\
Display cookies and enable you to manage them.

\(fn &optional NO-CACHE)" t nil)

(autoload 'w3m-about-cookie "w3m-cookie" "\
Make the html contents to display and to enable you to manage cookies.

\(fn URL &optional NO-DECODE NO-CACHE POST-DATA &rest ARGS)" nil nil)

;;;***

;;;### (autoloads (w3m-dtree w3m-about-dtree) "w3m-dtree" "site-lisp/emacs-w3m/w3m-dtree.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-dtree.el

(autoload 'w3m-about-dtree "w3m-dtree" "\
Not documented

\(fn URL &optional NODECODE ALLFILES &rest ARGS)" nil nil)

(autoload 'w3m-dtree "w3m-dtree" "\
Display directory tree on local file system.
If called with 'prefix argument', display all directorys and files.

\(fn ALLFILES PATH)" t nil)

;;;***

;;;### (autoloads (w3m-fb-mode) "w3m-fb" "site-lisp/emacs-w3m/w3m-fb.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-fb.el

(defvar w3m-fb-mode nil "\
Non-nil if W3m-Fb mode is enabled.
See the command `w3m-fb-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `w3m-fb-mode'.")

(custom-autoload 'w3m-fb-mode "w3m-fb" nil)

(autoload 'w3m-fb-mode "w3m-fb" "\
Toggle W3M Frame Buffer mode.
This allows frame-local lists of buffers (tabs).

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (w3m-filter) "w3m-filter" "site-lisp/emacs-w3m/w3m-filter.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-filter.el

(autoload 'w3m-filter "w3m-filter" "\
Apply filtering rule of URL against a content in this buffer.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (w3m-fontify-forms) "w3m-form" "site-lisp/emacs-w3m/w3m-form.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-form.el

(autoload 'w3m-fontify-forms "w3m-form" "\
Process half-dumped data and fontify forms in this buffer.

\(fn)" nil nil)

;;;***

;;;### (autoloads (w3m-linknum-bookmark-add-this-url w3m-linknum-download-this-url
;;;;;;  w3m-linknum-print-this-url w3m-linknum-edit-this-url w3m-linknum-external-view-this-url
;;;;;;  w3m-linknum-save-image w3m-linknum-view-image w3m-linknum-toggle-inline-image
;;;;;;  w3m-linknum-follow w3m-go-to-linknum w3m-link-numbering-mode)
;;;;;;  "w3m-lnum" "site-lisp/emacs-w3m/w3m-lnum.el" (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-lnum.el

(autoload 'w3m-link-numbering-mode "w3m-lnum" "\
Minor mode to extend point commands by using Conkeror style number selection.
With prefix ARG 0 disable battery included point functions, otherwise
enable them.  With no prefix ARG - toggle.

\(fn &optional ARG)" t nil)

(autoload 'w3m-go-to-linknum "w3m-lnum" "\
Turn on link, image and form numbers and ask for one to go to.
With prefix ARG don't highlight current link.
0 corresponds to location url.

\(fn ARG)" t nil)

(autoload 'w3m-linknum-follow "w3m-lnum" "\
Turn on link numbers, ask for one and execute appropriate action on it.
When link - visit it, when button - press, when input - activate it,
when image - toggle it.
With prefix ARG visit link in new session or don't move over
field/button/image on activation/push/toggle.
With `-' ARG, for link image - go to it and toggle it.
With -4 ARG, for link image - toggle it.
With double prefix ARG, prompt for url to visit.
With triple prefix ARG, prompt for url to visit in new session.

\(fn ARG)" t nil)

(autoload 'w3m-linknum-toggle-inline-image "w3m-lnum" "\
If image at point, toggle it.
Otherwise turn on link numbers and toggle selected image.
With prefix ARG open url under image in new session.
If no such url, move over image and toggle it.

\(fn &optional ARG)" t nil)

(autoload 'w3m-linknum-view-image "w3m-lnum" "\
Display the image under point in the external viewer.
If no image at poing, turn on image numbers and display selected.
The viewer is defined in `w3m-content-type-alist' for every type of an
image.

\(fn)" t nil)

(autoload 'w3m-linknum-save-image "w3m-lnum" "\
Save the image under point to a file.
If no image at poing, turn on image numbers and save selected.
The default name will be the original name of the image.

\(fn)" t nil)

(autoload 'w3m-linknum-external-view-this-url "w3m-lnum" "\
Launch the external browser and display the link at point.
If no link at point, turn on link numbers and open selected externally.

\(fn)" t nil)

(autoload 'w3m-linknum-edit-this-url "w3m-lnum" "\
Edit the page linked from the anchor under the cursor.
If no such, turn on link numbers and edit selected.

\(fn)" t nil)

(autoload 'w3m-linknum-print-this-url "w3m-lnum" "\
Display the url under point in the echo area and put it into `kill-ring'.
If no url under point, activate numbering and select one.

\(fn)" t nil)

(autoload 'w3m-linknum-download-this-url "w3m-lnum" "\
Download the file or the page pointed to by the link under point.
If no point, activate numbering and select andchor to download.

\(fn)" t nil)

(autoload 'w3m-linknum-bookmark-add-this-url "w3m-lnum" "\
Add link under cursor to bookmark.
If no link under point, activate numbering and ask for one.

\(fn)" t nil)

;;;***

;;;### (autoloads (w3m-namazu w3m-about-namazu) "w3m-namazu" "site-lisp/emacs-w3m/w3m-namazu.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-namazu.el

(autoload 'w3m-about-namazu "w3m-namazu" "\
Not documented

\(fn URL &optional NO-DECODE NO-CACHE &rest ARGS)" nil nil)

(autoload 'w3m-namazu "w3m-namazu" "\
Search indexed files with Namazu.

\(fn INDEX QUERY &optional RELOAD)" t nil)

;;;***

;;;### (autoloads (w3m-perldoc w3m-about-perldoc) "w3m-perldoc" "site-lisp/emacs-w3m/w3m-perldoc.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-perldoc.el

(autoload 'w3m-about-perldoc "w3m-perldoc" "\
Not documented

\(fn URL &optional NO-DECODE NO-CACHE &rest ARGS)" nil nil)

(autoload 'w3m-perldoc "w3m-perldoc" "\
View Perl documents.

\(fn DOCNAME)" t nil)

;;;***

;;;### (autoloads (w3m-search-uri-replace w3m-search-new-session
;;;;;;  w3m-search) "w3m-search" "site-lisp/emacs-w3m/w3m-search.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-search.el

(autoload 'w3m-search "w3m-search" "\
Search QUERY using SEARCH-ENGINE.
When called interactively with a prefix argument, you can choose one of
the search engines defined in `w3m-search-engine-alist'.  Otherwise use
`w3m-search-default-engine'.
If Transient Mark mode, use the region as an initial string of query
and deactivate the mark.

\(fn SEARCH-ENGINE QUERY)" t nil)

(autoload 'w3m-search-new-session "w3m-search" "\
Like `w3m-search', but do the search in a new session.

\(fn SEARCH-ENGINE QUERY)" t nil)

(autoload 'w3m-search-uri-replace "w3m-search" "\
Generate query string for ENGINE from URI matched by last search.

\(fn URI ENGINE)" nil nil)

;;;***

;;;### (autoloads (w3m-session-last-crashed-session w3m-session-last-autosave-session
;;;;;;  w3m-setup-session-menu w3m-session-select w3m-session-crash-recovery-remove
;;;;;;  w3m-session-save) "w3m-session" "site-lisp/emacs-w3m/w3m-session.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-session.el

(autoload 'w3m-session-save "w3m-session" "\
Save list of displayed session.

\(fn)" t nil)

(autoload 'w3m-session-crash-recovery-remove "w3m-session" "\
Remove crash recovery session set.

\(fn)" nil nil)

(autoload 'w3m-session-select "w3m-session" "\
Select session from session list.

\(fn)" t nil)

(autoload 'w3m-setup-session-menu "w3m-session" "\
Setup w3m session items in menubar.

\(fn)" nil nil)

(autoload 'w3m-session-last-autosave-session "w3m-session" "\
Not documented

\(fn)" nil nil)

(autoload 'w3m-session-last-crashed-session "w3m-session" "\
Not documented

\(fn)" nil nil)

;;;***

;;;### (autoloads (w3m-replace-symbol) "w3m-symbol" "site-lisp/emacs-w3m/w3m-symbol.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-symbol.el

(autoload 'w3m-replace-symbol "w3m-symbol" "\
Not documented

\(fn)" nil nil)

;;;***

;;;### (autoloads (w3m-about-weather w3m-weather) "w3m-weather" "site-lisp/emacs-w3m/w3m-weather.el"
;;;;;;  (20015 29801))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-weather.el

(autoload 'w3m-weather "w3m-weather" "\
Display weather report.

\(fn AREA)" t nil)

(autoload 'w3m-about-weather "w3m-weather" "\
Not documented

\(fn URL NO-DECODE NO-CACHE POST-DATA REFERER HANDLER)" nil nil)

;;;***

;;;### (autoloads (web-vcs-investigate-elisp-file web-vcs-byte-compile-file
;;;;;;  web-vcs-message-with-face web-vcs-get-files-from-root web-vcs-log-edit
;;;;;;  web-vcs-default-download-directory) "web-vcs" "site-lisp/nxhtml/web-vcs.el"
;;;;;;  (19385 29876))
;;; Generated autoloads from site-lisp/nxhtml/web-vcs.el

(autoload 'web-vcs-default-download-directory "web-vcs" "\
Try to find a suitable place.
Considers site-start.el, site-

\(fn)" nil nil)

(autoload 'web-vcs-log-edit "web-vcs" "\
Open log file.

\(fn)" t nil)

(autoload 'web-vcs-get-files-from-root "web-vcs" "\
Download a file tree from VCS system using the web interface.
Use WEB-VCS entry in variable `web-vcs-links-regexp' to download
files via http from URL to directory DL-DIR.

Show URL first and offer to visit the page.  That page will give
you information about version control system (VCS) system used
etc.

\(fn WEB-VCS URL DL-DIR)" nil nil)

(autoload 'web-vcs-message-with-face "web-vcs" "\
Display a colored message at the bottom of the string.
FACE is the face to use for the message.
FORMAT-STRING and ARGS are the same as for `message'.

Also put FACE on the message in *Messages* buffer.

\(fn FACE FORMAT-STRING &rest ARGS)" nil nil)

(autoload 'web-vcs-byte-compile-file "web-vcs" "\
Byte compile FILE in a new Emacs sub process.
EXTRA-LOAD-PATH is added to the front of `load-path' during
compilation.

FILE is set to `buffer-file-name' when called interactively.
If LOAD

\(fn FILE &optional LOAD EXTRA-LOAD-PATH COMP-DIR)" t nil)

(autoload 'web-vcs-investigate-elisp-file "web-vcs" "\
Not documented

\(fn FILE-OR-BUFFER)" t nil)

;;;***

;;;### (autoloads (whole-line-or-region-comment-dwim-2 whole-line-or-region-comment-dwim
;;;;;;  whole-line-or-region-delete whole-line-or-region-yank whole-line-or-region-kill-ring-save
;;;;;;  whole-line-or-region-kill-region whole-line-or-region-copy-region-as-kill
;;;;;;  whole-line-or-region-mode) "whole-line-or-region" "site-lisp/whole-line-or-region.el"
;;;;;;  (20015 32334))
;;; Generated autoloads from site-lisp/whole-line-or-region.el

(autoload 'whole-line-or-region-mode "whole-line-or-region" "\
Toggle use of whole-line-or-region minor mode.

This minor mode allows functions to operate on the current line if
they would normally operate on a region and region is currently
undefined.

Optional ARG turns mode on iff ARG is a positive integer.

\(fn &optional ARG)" t nil)

(autoload 'whole-line-or-region-copy-region-as-kill "whole-line-or-region" "\
Copy region or PREFIX whole lines.

\(fn PREFIX)" t nil)

(autoload 'whole-line-or-region-kill-region "whole-line-or-region" "\
Kill (cut) region or PREFIX whole lines.

\(fn PREFIX)" t nil)

(autoload 'whole-line-or-region-kill-ring-save "whole-line-or-region" "\
Copy region or PREFIX whole lines.

\(fn PREFIX)" t nil)

(autoload 'whole-line-or-region-yank "whole-line-or-region" "\
Yank (paste) previously killed text.

If the text to be yanked was killed with a whole-line-or-region
function *as* a whole-line, then paste it as a whole line (i.e. do not
break up the current line, and do not force the user to move point).

RAW-PREFIX is used to determine which string to yank, just as `yank'
would normally use it.

Optionally, pass in string to be \"yanked\" via STRING-IN.

\(fn RAW-PREFIX &optional STRING-IN)" t nil)

(autoload 'whole-line-or-region-delete "whole-line-or-region" "\
Delete region or PREFIX whole lines.

\(fn PREFIX)" t nil)

(autoload 'whole-line-or-region-comment-dwim "whole-line-or-region" "\
Call `comment-dwim' on current region or current line.

See `comment-dwim' for details of RAW-PREFIX usage.

\(fn RAW-PREFIX)" t nil)

(autoload 'whole-line-or-region-comment-dwim-2 "whole-line-or-region" "\
Call `comment-dwim' on region or PREFIX whole lines.

\(fn PREFIX)" t nil)

;;;***

;;;### (autoloads (xray-features xray-hooks xray-faces xray-screen
;;;;;;  xray-overlay xray-marker xray-frame xray-window xray-buffer
;;;;;;  xray-position xray-symbol xray-click/key xray-on-mode-line-click
;;;;;;  xray-on-click xray-customize) "xray" "site-lisp/xray.el"
;;;;;;  (18429 49078))
;;; Generated autoloads from site-lisp/xray.el

(autoload 'xray-customize "xray" "\
Customize xray group.

\(fn)" t nil)

(autoload 'xray-on-click "xray" "\
Give help on an object clicked with the mouse.

\(fn CLICK)" t nil)

(autoload 'xray-on-mode-line-click "xray" "\
Give help on the mode line.

\(fn CLICK)" t nil)

(autoload 'xray-click/key "xray" "\
Give help on a key/menu sequence or object clicked with the mouse.

The object can be any part of an Emacs window or a name appearing in a buffer.
You can do any of the following:

    type a key sequence (e.g. `C-M-s')
    choose a menu item (e.g. [menu-bar files open-file])
    click on a scroll bar
    click on the mode line
    click in the minibuffer
    click on a name in a buffer: `xray-symbol' is called
    click anywhere else in a buffer: `xray-buffer' is called

Help is generally provided using `describe-key' and the Emacs online manual
\(via `Info-goto-emacs-key-command-node').  If no entry is found in the index of
the Emacs manual, then the manual is searched from the beginning for literal
occurrences of KEY.

For example, the KEY `C-g' is not in the index (for some reason), so the manual
is searched.  (Once an occurrence is found, you can repeatedly type `s' in
*Info* to search for additional occurrences.)

\(fn KEY)" t nil)

(autoload 'xray-symbol "xray" "\
Display SYMBOL internal cells in a temporary buffer.

That is, displays the symbol name cell, the symbol function cell, the symbol
value cell and the symbol property list cell.  It's also displayed the key
bindings associated with symbol (if any), from which file it was loaded and
some apropos information.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-symbol' (non-nil)
or `xray-help-symbol' (nil).

See `xray-customize' for customization.

\(fn SYMBOL &optional BUFFER)" t nil)

(autoload 'xray-position "xray" "\
Display POSITION internal cells in a temporary buffer.

If POSITION is nil, it's used (point).
If BUFFER is nil, it's used (current-buffer).

That is, displays the frame, the window, the buffer, the word (if any) around
POSITION (also some apropos information), the character width, the character at
POSITION, the charset, the text property list, the default text property list
and the overlay list.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-position'
\(non-nil) or `xray-help-position' (nil).

See `xray-customize' for customization.

\(fn &optional POSITION BUFFER)" t nil)

(autoload 'xray-buffer "xray" "\
Display BUFFER internal cells in a temporary buffer.

If BUFFER is nil, it's used (current-buffer).

That is, displays the frame, the window, the base buffer (if it's an indirect
buffer), buffer name, buffer size, minimum point, point, maximum point, the
mark, the mark active flag, file name visited (if any), file modification time,
the modified flag, the read only flag, multibyte flag, inhibit read flag,
display table, active modes, window list, buffer list, hooks related to
buffers, mark ring, overlay list and local variables.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-buffer'
\(non-nil) or `xray-help-buffer' (nil).

See `xray-customize' for customization.

\(fn &optional BUFFER)" t nil)

(autoload 'xray-window "xray" "\
Display WINDOW internal cells in a temporary buffer.

If WINDOW is nil, it's used (selected-window).

That is, displays the associated frame, the associated buffer, the window, the
height, the width, the edges, the buffer position, the window start, the window
end, the liveness flag, the dedicated flag, the minibuffer flag, the horizontal
scrolling amount, display table, some window related variables, the hooks, the
window least recently selected, the largest window area and the window list.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-window'
\(non-nil) or `xray-help-window' (nil).

See `xray-customize' for customization.

\(fn &optional WINDOW)" t nil)

(autoload 'xray-frame "xray" "\
Display FRAME internal cells in a temporary buffer.

If FRAME is nil, it's used (selected-frame).

That is, displays the frame, frame height, frame width, pixel frame height,
pixel frame width, pixel char height, pixel char width, liveness flag,
visibility flag, the first window on frame, the selected window, the root
window, some variables related to frame, the frame parameters, the hooks, the
frame list, the visible frame list and display list.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-frame'
\(non-nil) or `xray-help-frame' (nil).

See `xray-customize' for customization.

\(fn &optional FRAME)" t nil)

(autoload 'xray-marker "xray" "\
Display MARKER internal cells in a temporary buffer.

If MARKER is nil, it's used (mark t).

That is, displays the associated buffer, the position, the insertion type, the
mark, the beginning of region, the end of region, some variable related to
marker, hooks and the mark ring.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-marker'
\(non-nil) or `xray-help-marker' (nil).

See `xray-customize' for customization.

\(fn &optional MARKER)" t nil)

(autoload 'xray-overlay "xray" "\
Display OVERLAY internal cells in a temporary buffer.

If OVERLAY is nil, try to use the overlay on current buffer position (if any).

That is, displays the buffer associated, the start position, the end position,
the overlay list and the property list.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-overlay'
\(non-nil) or `xray-help-overlay' (nil).

See `xray-customize' for customization.

\(fn &optional OVERLAY)" t nil)

(autoload 'xray-screen "xray" "\
Display SCREEN capabilities in a temporary buffer.

If SCREEN is nil, use the first screen given by `x-display-list'.

That's, displays SCREEN capabilities, some variables and hooks related to
screen, and the display list.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-screen'
\(non-nil) or `xray-help-screen' (nil).

See `xray-customize' for customization.

\(fn &optional SCREEN)" t nil)

(autoload 'xray-faces "xray" "\
Display all defined faces.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-faces'
\(non-nil) or `xray-help-faces' (nil).

See `xray-customize' for customization.

\(fn)" t nil)

(autoload 'xray-hooks "xray" "\
Display all standard hooks and other defined hooks.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-hooks'
\(non-nil) or `xray-help-hooks' (nil).

See `xray-customize' for customization.

\(fn)" t nil)

(autoload 'xray-features "xray" "\
Display all features loaded.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-features'
\(non-nil) or `xray-help-features' (nil).

See `xray-customize' for customization.

\(fn)" t nil)

;;;***

;;;### (autoloads (yas/minor-mode yas/snippet-dirs) "yasnippet" "site-lisp/yasnippet/yasnippet.el"
;;;;;;  (19563 19707))
;;; Generated autoloads from site-lisp/yasnippet/yasnippet.el

(defvar yas/snippet-dirs nil "\
Directory or list of snippet dirs for each major mode.

The directory where user-created snippets are to be stored. Can
also be a list of directories. In that case, when used for
bulk (re)loading of snippets (at startup or via
`yas/reload-all'), directories appearing earlier in the list
shadow other dir's snippets. Also, the first directory is taken
as the default for storing the user's new snippets.")

(custom-autoload 'yas/snippet-dirs "yasnippet" nil)

(autoload 'yas/minor-mode "yasnippet" "\
Toggle YASnippet mode.

When YASnippet mode is enabled, the `tas/trigger-key' key expands
snippets of code depending on the mode.

With no argument, this command toggles the mode.
positive prefix argument turns on the mode.
Negative prefix argument turns off the mode.

You can customize the key through `yas/trigger-key'.

Key bindings:
\\{yas/minor-mode-map}

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (zencoding-preview zencoding-expand-yas zencoding-mode
;;;;;;  zencoding-expand-line) "zencoding-mode" "site-lisp/zencoding/zencoding-mode.el"
;;;;;;  (20019 13517))
;;; Generated autoloads from site-lisp/zencoding/zencoding-mode.el

(autoload 'zencoding-expand-line "zencoding-mode" "\
Replace the current line's zencode expression with the corresponding expansion.
If prefix ARG is given or region is visible call `zencoding-preview' to start an
interactive preview.

Otherwise expand line directly.

For more information see `zencoding-mode'.

\(fn ARG)" t nil)

(autoload 'zencoding-mode "zencoding-mode" "\
Minor mode for writing HTML and CSS markup.
With zen coding for HTML and CSS you can write a line like

  ul#name>li.item*2

and have it expanded to

  <ul id=\"name\">
    <li class=\"item\"></li>
    <li class=\"item\"></li>
  </ul>

This minor mode defines keys for quick access:

\\{zencoding-mode-keymap}

Home page URL `http://www.emacswiki.org/emacs/ZenCoding'.

See also `zencoding-expand-line'.

\(fn &optional ARG)" t nil)

(autoload 'zencoding-expand-yas "zencoding-mode" "\
Not documented

\(fn)" t nil)

(autoload 'zencoding-preview "zencoding-mode" "\
Expand zencode between BEG and END interactively.
This will show a preview of the expanded zen code and you can
accept it or skip it.

\(fn BEG END)" t nil)

;;;***

;;;### (autoloads nil nil ("circe-ext.el" "cus-dirs.el" "flyspell-ext.el"
;;;;;;  "org-crypt.el" "org-devonthink.el" "org-ext.el" "org-redmine.el"
;;;;;;  "site-lisp/all.el" "site-lisp/anything/anything-match-plugin.el"
;;;;;;  "site-lisp/anything/anything-rubikitch.el" "site-lisp/anything/anything-startup.el"
;;;;;;  "site-lisp/apel/apel-ver.el" "site-lisp/apel/atype.el" "site-lisp/apel/broken.el"
;;;;;;  "site-lisp/apel/calist.el" "site-lisp/apel/emu-mule.el" "site-lisp/apel/emu.el"
;;;;;;  "site-lisp/apel/file-detect.el" "site-lisp/apel/filename.el"
;;;;;;  "site-lisp/apel/install.el" "site-lisp/apel/inv-18.el" "site-lisp/apel/inv-19.el"
;;;;;;  "site-lisp/apel/inv-23.el" "site-lisp/apel/inv-xemacs.el"
;;;;;;  "site-lisp/apel/invisible.el" "site-lisp/apel/localhook.el"
;;;;;;  "site-lisp/apel/mcharset.el" "site-lisp/apel/mcs-20.el" "site-lisp/apel/mcs-e20.el"
;;;;;;  "site-lisp/apel/mcs-ltn1.el" "site-lisp/apel/mcs-nemacs.el"
;;;;;;  "site-lisp/apel/mcs-om.el" "site-lisp/apel/mcs-xm.el" "site-lisp/apel/mcs-xmu.el"
;;;;;;  "site-lisp/apel/mule-caesar.el" "site-lisp/apel/pccl-20.el"
;;;;;;  "site-lisp/apel/pccl-om.el" "site-lisp/apel/pccl.el" "site-lisp/apel/pces-20.el"
;;;;;;  "site-lisp/apel/pces-e20.el" "site-lisp/apel/pces-e20_2.el"
;;;;;;  "site-lisp/apel/pces-nemacs.el" "site-lisp/apel/pces-om.el"
;;;;;;  "site-lisp/apel/pces-raw.el" "site-lisp/apel/pces-xfc.el"
;;;;;;  "site-lisp/apel/pces-xm.el" "site-lisp/apel/pces.el" "site-lisp/apel/pcustom.el"
;;;;;;  "site-lisp/apel/poe-18.el" "site-lisp/apel/poe-xemacs.el"
;;;;;;  "site-lisp/apel/poe.el" "site-lisp/apel/poem-e20.el" "site-lisp/apel/poem-e20_2.el"
;;;;;;  "site-lisp/apel/poem-e20_3.el" "site-lisp/apel/poem-ltn1.el"
;;;;;;  "site-lisp/apel/poem-nemacs.el" "site-lisp/apel/poem-om.el"
;;;;;;  "site-lisp/apel/poem-xm.el" "site-lisp/apel/poem.el" "site-lisp/apel/product.el"
;;;;;;  "site-lisp/apel/pym.el" "site-lisp/apel/static.el" "site-lisp/apel/timezone.el"
;;;;;;  "site-lisp/apel/tinycustom.el" "site-lisp/apel/tinyrich.el"
;;;;;;  "site-lisp/archive-region.el" "site-lisp/archive-region.el"
;;;;;;  "site-lisp/ascii.el" "site-lisp/breadcrumb.el" "site-lisp/breadcrumb.el"
;;;;;;  "site-lisp/browse-kill-ring+.el" "site-lisp/browse-kill-ring+.el"
;;;;;;  "site-lisp/browse-kill-ring.el" "site-lisp/chess/auto-autoloads.el"
;;;;;;  "site-lisp/chess/chess-ai.el" "site-lisp/chess/chess-algebraic.el"
;;;;;;  "site-lisp/chess/chess-announce.el" "site-lisp/chess/chess-auto.el"
;;;;;;  "site-lisp/chess/chess-autosave.el" "site-lisp/chess/chess-chat.el"
;;;;;;  "site-lisp/chess/chess-clock.el" "site-lisp/chess/chess-common.el"
;;;;;;  "site-lisp/chess/chess-crafty.el" "site-lisp/chess/chess-database.el"
;;;;;;  "site-lisp/chess/chess-display.el" "site-lisp/chess/chess-eco.el"
;;;;;;  "site-lisp/chess/chess-engine.el" "site-lisp/chess/chess-epd.el"
;;;;;;  "site-lisp/chess/chess-fen.el" "site-lisp/chess/chess-file.el"
;;;;;;  "site-lisp/chess/chess-game.el" "site-lisp/chess/chess-german.el"
;;;;;;  "site-lisp/chess/chess-gnuchess.el" "site-lisp/chess/chess-ics1.el"
;;;;;;  "site-lisp/chess/chess-images.el" "site-lisp/chess/chess-input.el"
;;;;;;  "site-lisp/chess/chess-irc.el" "site-lisp/chess/chess-kibitz.el"
;;;;;;  "site-lisp/chess/chess-log.el" "site-lisp/chess/chess-maint.el"
;;;;;;  "site-lisp/chess/chess-message.el" "site-lisp/chess/chess-module.el"
;;;;;;  "site-lisp/chess/chess-network.el" "site-lisp/chess/chess-none.el"
;;;;;;  "site-lisp/chess/chess-phalanx.el" "site-lisp/chess/chess-plain.el"
;;;;;;  "site-lisp/chess/chess-ply.el" "site-lisp/chess/chess-pos.el"
;;;;;;  "site-lisp/chess/chess-scid.el" "site-lisp/chess/chess-sjeng.el"
;;;;;;  "site-lisp/chess/chess-sound.el" "site-lisp/chess/chess-test.el"
;;;;;;  "site-lisp/chess/chess-transport.el" "site-lisp/chess/chess-ucb.el"
;;;;;;  "site-lisp/chess/chess-var.el" "site-lisp/cldoc.el" "site-lisp/column-marker.el"
;;;;;;  "site-lisp/crypt++.el" "site-lisp/crypt++.el" "site-lisp/css-mode.el"
;;;;;;  "site-lisp/css-mode.el" "site-lisp/csv-mode.el" "site-lisp/csv-mode.el"
;;;;;;  "site-lisp/diminish.el" "site-lisp/dired-tar.el" "site-lisp/ee/ee-autoloads.el"
;;;;;;  "site-lisp/emacs-w3m/mew-w3m.el" "site-lisp/emacs-w3m/w3m-bug.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-ccl.el" "site-lisp/emacs-w3m/w3m-ems.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-favicon.el" "site-lisp/emacs-w3m/w3m-hist.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-image.el" "site-lisp/emacs-w3m/w3m-load.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-mail.el" "site-lisp/emacs-w3m/w3m-proc.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-rss.el" "site-lisp/emacs-w3m/w3m-tabmenu.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-ucs.el" "site-lisp/emacs-w3m/w3m-util.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-xmas.el" "site-lisp/emacs-w3m/w3mhack.el"
;;;;;;  "site-lisp/epg/epa-dired.el" "site-lisp/epg/epa-setup.el"
;;;;;;  "site-lisp/epg/epg-package-info.el" "site-lisp/epg/pgg-epg.el"
;;;;;;  "site-lisp/escreen.el" "site-lisp/escreen.el" "site-lisp/eshell/auto-autoloads.el"
;;;;;;  "site-lisp/eshell/em-alias.el" "site-lisp/eshell/em-banner.el"
;;;;;;  "site-lisp/eshell/em-basic.el" "site-lisp/eshell/em-cmpl.el"
;;;;;;  "site-lisp/eshell/em-dirs.el" "site-lisp/eshell/em-glob.el"
;;;;;;  "site-lisp/eshell/em-hist.el" "site-lisp/eshell/em-ls.el"
;;;;;;  "site-lisp/eshell/em-pred.el" "site-lisp/eshell/em-prompt.el"
;;;;;;  "site-lisp/eshell/em-rebind.el" "site-lisp/eshell/em-script.el"
;;;;;;  "site-lisp/eshell/em-smart.el" "site-lisp/eshell/em-term.el"
;;;;;;  "site-lisp/eshell/em-unix.el" "site-lisp/eshell/em-xtra.el"
;;;;;;  "site-lisp/eshell/esh-arg.el" "site-lisp/eshell/esh-cmd.el"
;;;;;;  "site-lisp/eshell/esh-ext.el" "site-lisp/eshell/esh-groups.el"
;;;;;;  "site-lisp/eshell/esh-io.el" "site-lisp/eshell/esh-maint.el"
;;;;;;  "site-lisp/eshell/esh-module.el" "site-lisp/eshell/esh-opt.el"
;;;;;;  "site-lisp/eshell/esh-proc.el" "site-lisp/eshell/esh-toggle.el"
;;;;;;  "site-lisp/eshell/esh-util.el" "site-lisp/eshell/esh-var.el"
;;;;;;  "site-lisp/eshell/eshell-auto.el" "site-lisp/eval-expr.el"
;;;;;;  "site-lisp/find-library.el" "site-lisp/fit-frame.el" "site-lisp/fm.el"
;;;;;;  "site-lisp/fm.el" "site-lisp/gnuplot-gui.el" "site-lisp/gnuplot-gui.el"
;;;;;;  "site-lisp/gnuplot.el" "site-lisp/grep-ed.el" "site-lisp/grep-ed.el"
;;;;;;  "site-lisp/haskell-mode/haskell-font-lock.el" "site-lisp/haskell-mode/haskell-ghci.el"
;;;;;;  "site-lisp/haskell-mode/haskell-hugs.el" "site-lisp/haskell-mode/haskell-simple-indent.el"
;;;;;;  "site-lisp/haskell-mode/haskell-site-file.el" "site-lisp/hide-search.el"
;;;;;;  "site-lisp/hide-search.el" "site-lisp/hs-lint.el" "site-lisp/hs-lint.el"
;;;;;;  "site-lisp/idomenu.el" "site-lisp/idomenu.el" "site-lisp/indirect.el"
;;;;;;  "site-lisp/indirect.el" "site-lisp/initsplit/initsplit-test.el"
;;;;;;  "site-lisp/initsplit/initsplit.el" "site-lisp/linum.el" "site-lisp/magit/50magit.el"
;;;;;;  "site-lisp/magit/magit-bisect.el" "site-lisp/magit/magit-key-mode.el"
;;;;;;  "site-lisp/magit/magit-pkg.el" "site-lisp/magit/magit-stgit.el"
;;;;;;  "site-lisp/magit/magit-svn.el" "site-lisp/magit/magit-topgit.el"
;;;;;;  "site-lisp/markdown-mode.el" "site-lisp/mdfind.el" "site-lisp/mdfind.el"
;;;;;;  "site-lisp/message-x.el" "site-lisp/message-x.el" "site-lisp/muse/muse-markdown.el"
;;;;;;  "site-lisp/nxhtml/autostart.el" "site-lisp/nxhtml/autostart22.el"
;;;;;;  "site-lisp/nxhtml/nxhtml-base.el" "site-lisp/nxhtml/nxhtml-loaddefs.el"
;;;;;;  "site-lisp/nxhtml/web-autoload.el" "site-lisp/paredit.el"
;;;;;;  "site-lisp/paredit.el" "site-lisp/parenface.el" "site-lisp/parenface.el"
;;;;;;  "site-lisp/po-mode.el" "site-lisp/po-mode.el" "site-lisp/psvn.el"
;;;;;;  "site-lisp/puppet-mode.el" "site-lisp/python-mode/highlight-indentation.el"
;;;;;;  "site-lisp/python-mode/pars-part-output.el" "site-lisp/python-mode/py-bug-numbered-tests.el"
;;;;;;  "site-lisp/python-mode/pycomplete.el" "site-lisp/python-mode/python-components-test.el"
;;;;;;  "site-lisp/python-mode/python-mode-test.el" "site-lisp/redmine/redmine.el"
;;;;;;  "site-lisp/redshank.el" "site-lisp/redshank.el" "site-lisp/regex-tool/regex-tool.el"
;;;;;;  "site-lisp/repeat-insert.el" "site-lisp/repeat-insert.el"
;;;;;;  "site-lisp/ruby-mode/inf-ruby.el" "site-lisp/ruby-mode/rdoc-mode.el"
;;;;;;  "site-lisp/ruby-mode/ruby-electric.el" "site-lisp/ruby-mode/ruby-style.el"
;;;;;;  "site-lisp/session.el" "site-lisp/smex.el" "site-lisp/sunrise-commander/sunrise-x-checkpoints.el"
;;;;;;  "site-lisp/sunrise-commander/sunrise-x-old-checkpoints.el"
;;;;;;  "site-lisp/sunrise-commander/sunrise-x-w32-addons.el" "site-lisp/vkill.el"
;;;;;;  "site-lisp/vkill.el" "site-lisp/wcount.el" "site-lisp/wcount.el"
;;;;;;  "site-lisp/whole-line-or-region.el" "site-lisp/xcscope/xcscope.el"
;;;;;;  "site-lisp/xml-rpc.el" "site-lisp/xml-rpc.el" "site-lisp/xray.el"
;;;;;;  "site-lisp/yasnippet/dropdown-list.el" "site-lisp/yasnippet/yasnippet-debug.el"
;;;;;;  "untabify.el") (20021 55203 372794))

;;;***

;;;### (autoloads (c-includes c-includes-current-file c-includes-add-binding)
;;;;;;  "c-includes" "c-includes.el" (18429 49044))
;;; Generated autoloads from c-includes.el

(autoload 'c-includes-add-binding "c-includes" "\
Set binding for C-c C-i in cc-mode.

\(fn)" nil nil)

(autoload 'c-includes-current-file "c-includes" "\
Find all of the header file included by the current file.

\(fn &optional REGEXP)" t nil)

(autoload 'c-includes "c-includes" "\
Find all of the header files included by FILENAME.
REGEXP, if non-nil, is a regular expression to search for within
FILENAME and the files that it includes.  The output will be
structured in the same order that the compiler will see it, enabling
you determine order of occurrence.

\(fn FILENAME &optional REGEXP)" t nil)

;;;***
