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

;;; Autoloads for packages that lack them

(mapc #'(lambda (entry)
          (autoload (cdr entry) (car entry) nil t))
      '(
        ("breadcrumb"    . bc-goto-current)
        ("breadcrumb"    . bc-list)
        ("breadcrumb"    . bc-local-next)
        ("breadcrumb"    . bc-local-previous)
        ("breadcrumb"    . bc-next)
        ("breadcrumb"    . bc-previous)
        ("breadcrumb"    . bc-set)
        ("css-mode"      . css-mode)
        ("ess-site"      . R)
        ("eval-expr"     . eval-expr)
        ("fm"            . fm-start)
        ("indirect"      . indirect-region)
        ("ldg-new"       . ledger-mode)
        ("puppet-mode"   . puppet-mode)
        ("repeat-insert" . insert-patterned)
        ("repeat-insert" . insert-patterned-2)
        ("repeat-insert" . insert-patterned-3)
        ("repeat-insert" . insert-patterned-4)
        ("session"       . session-save-session)
        ("tex-site"      . latex-mode)
        ("tex-site"      . texinfo-mode)
        ("vkill"         . list-unix-processes)
        ("vkill"         . vkill)
        ("wcount"        . wcount-mode)
        ("whitespace"    . whitespace-cleanup)
        ))

;;; Generated autoloads follow (made by autoload.el).

;;;### (autoloads nil "_pkg" "site-lisp/eshell/_pkg.el" (18807 50473))
;;; Generated autoloads from site-lisp/eshell/_pkg.el

(if (fboundp 'package-provide) (package-provide 'eshell :version 2.5 :type 'regular))

;;;***

;;;### (autoloads (ace-jump-mode) "ace-jump-mode" "site-lisp/ace-jump-mode/ace-jump-mode.el"
;;;;;;  (20035 24581))
;;; Generated autoloads from site-lisp/ace-jump-mode/ace-jump-mode.el

(autoload 'ace-jump-mode "ace-jump-mode" "\
AceJump mode is a minor mode for you to quick jump to a
position in the curret view.
   There is three submode now:
     `ace-jump-char-mode'
     `ace-jump-word-mode'
     `ace-jump-line-mode'

You can specify the sequence about which mode should enter
by customize `ace-jump-mode-submode-list'.

If you do not want to query char for word mode, you can change
`ace-jump-word-mode-use-query-char' to nil.

If you don't like the default move keys, you can change it by
setting `ace-jump-mode-move-keys'.

You can constrol whether use the case sensitive via
`ace-jump-mode-case-sensitive-search'.

\(fn &optional PREFIX)" t nil)

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
;;;;;;  "anything" "site-lisp/anything/anything.el" (20029 58378))
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
;;;;;;  anything-lisp-completion-at-point anything-eshell-history
;;;;;;  anything-esh-pcomplete anything-completion-mode anything-c-shell-command-if-needed
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
;;;;;;  anything-ff-run-print-file anything-ff-run-etags anything-ff-run-gnus-attach-files
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
;;;;;;  (20029 58378))
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

(autoload 'anything-ff-run-etags "anything-config" "\
Run Etags command action from `anything-c-source-find-files'.

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
The help function for etags.

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

(autoload 'anything-eshell-history "anything-config" "\
Preconfigured anything for eshell history.

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

;;;### (autoloads (turn-on-bib-cite bib-cite-minor-mode) "bib-cite"
;;;;;;  "site-lisp/auctex/bib-cite.el" (18341 54637))
;;; Generated autoloads from site-lisp/auctex/bib-cite.el

(autoload 'bib-cite-minor-mode "bib-cite" "\
Toggle bib-cite mode.
When bib-cite mode is enabled, citations, labels and refs are highlighted
when the mouse is over them.  Clicking on these highlights with [mouse-2]
runs bib-find, and [mouse-3] runs bib-display.

\(fn ARG)" t nil)

(autoload 'turn-on-bib-cite "bib-cite" "\
Unconditionally turn on Bib Cite mode.

\(fn)" nil nil)

;;;***

;;;### (autoloads (bmkp-version) "bookmark+" "site-lisp/bookmark+/bookmark+.el"
;;;;;;  (20022 52774))
;;; Generated autoloads from site-lisp/bookmark+/bookmark+.el

(defconst bmkp-version-number "3.2.2")

(autoload 'bmkp-version "bookmark+" "\
Show version number of library `bookmark+.el'.

\(fn)" t nil)

;;;***

;;;### (autoloads (bmkp-delete-bookmarks bmkp-delete-all-autonamed-for-this-buffer
;;;;;;  bmkp-set-autonamed-regexp-region bmkp-set-autonamed-regexp-buffer
;;;;;;  bmkp-set-autonamed-bookmark-at-line bmkp-set-autonamed-bookmark
;;;;;;  bmkp-toggle-autonamed-bookmark-set/delete bmkp-previous-bookmark-w32-repeat
;;;;;;  bmkp-next-bookmark-w32-repeat bmkp-previous-bookmark-w32
;;;;;;  bmkp-next-bookmark-w32 bmkp-previous-bookmark-this-buffer-repeat
;;;;;;  bmkp-next-bookmark-this-buffer-repeat bmkp-previous-bookmark-this-buffer
;;;;;;  bmkp-next-bookmark-this-buffer bmkp-previous-bookmark-repeat
;;;;;;  bmkp-next-bookmark-repeat bmkp-previous-bookmark bmkp-next-bookmark
;;;;;;  bmkp-cycle-this-buffer-other-window bmkp-cycle-this-buffer
;;;;;;  bmkp-cycle-other-window bmkp-cycle bmkp-jump-in-navlist-other-window
;;;;;;  bmkp-jump-in-navlist bmkp-file-this-dir-some-tags-regexp-jump-other-window
;;;;;;  bmkp-file-this-dir-some-tags-regexp-jump bmkp-file-this-dir-some-tags-jump-other-window
;;;;;;  bmkp-file-this-dir-some-tags-jump bmkp-file-this-dir-all-tags-regexp-jump-other-window
;;;;;;  bmkp-file-this-dir-all-tags-regexp-jump bmkp-file-this-dir-all-tags-jump-other-window
;;;;;;  bmkp-file-this-dir-all-tags-jump bmkp-file-some-tags-regexp-jump-other-window
;;;;;;  bmkp-file-some-tags-regexp-jump bmkp-file-some-tags-jump-other-window
;;;;;;  bmkp-file-some-tags-jump bmkp-file-all-tags-regexp-jump-other-window
;;;;;;  bmkp-file-all-tags-regexp-jump bmkp-file-all-tags-jump-other-window
;;;;;;  bmkp-file-all-tags-jump bmkp-some-tags-regexp-jump-other-window
;;;;;;  bmkp-some-tags-regexp-jump bmkp-some-tags-jump-other-window
;;;;;;  bmkp-some-tags-jump bmkp-all-tags-regexp-jump-other-window
;;;;;;  bmkp-all-tags-regexp-jump bmkp-all-tags-jump-other-window
;;;;;;  bmkp-all-tags-jump bmkp-w3m-jump-other-window bmkp-w3m-jump
;;;;;;  bmkp-url-jump-other-window bmkp-url-jump bmkp-variable-list-jump
;;;;;;  bmkp-this-buffer-jump-other-window bmkp-this-buffer-jump
;;;;;;  bmkp-specific-files-jump-other-window bmkp-specific-files-jump
;;;;;;  bmkp-specific-buffers-jump-other-window bmkp-specific-buffers-jump
;;;;;;  bmkp-remote-file-jump-other-window bmkp-remote-file-jump
;;;;;;  bmkp-region-jump-other-window bmkp-region-jump bmkp-non-file-jump-other-window
;;;;;;  bmkp-non-file-jump bmkp-man-jump-other-window bmkp-man-jump
;;;;;;  bmkp-local-file-jump-other-window bmkp-local-file-jump bmkp-info-jump-other-window
;;;;;;  bmkp-info-jump bmkp-gnus-jump-other-window bmkp-gnus-jump
;;;;;;  bmkp-file-this-dir-jump-other-window bmkp-file-this-dir-jump
;;;;;;  bmkp-file-jump-other-window bmkp-file-jump bmkp-dired-this-dir-jump-other-window
;;;;;;  bmkp-dired-this-dir-jump bmkp-dired-jump-other-window bmkp-dired-jump
;;;;;;  bmkp-desktop-jump bmkp-bookmark-list-jump bmkp-autonamed-this-buffer-jump-other-window
;;;;;;  bmkp-autonamed-this-buffer-jump bmkp-autonamed-jump-other-window
;;;;;;  bmkp-autonamed-jump bmkp-jump-to-type-other-window bmkp-jump-to-type
;;;;;;  bmkp-dired-subdirs bmkp-set-variable-list-bookmark bmkp-desktop-delete
;;;;;;  bmkp-desktop-read bmkp-desktop-change-dir bmkp-set-desktop-bookmark
;;;;;;  bmkp-bookmark-file-jump bmkp-set-bookmark-file-bookmark bmkp-list-defuns-in-commands-file
;;;;;;  bmkp-describe-bookmark-internals bmkp-describe-bookmark bmkp-purge-notags-autofiles
;;;;;;  bmkp-autofile-remove-tags bmkp-autofile-add-tags bmkp-autofile-set
;;;;;;  bmkp-file-target-set bmkp-url-target-set bmkp-paste-replace-tags
;;;;;;  bmkp-paste-add-tags bmkp-copy-tags bmkp-rename-tag bmkp-remove-tags-from-all
;;;;;;  bmkp-remove-tags bmkp-set-tag-value bmkp-set-tag-value-for-navlist
;;;;;;  bmkp-add-tags bmkp-remove-all-tags bmkp-list-all-tags bmkp-unomit-all
;;;;;;  bmkp-navlist-bmenu-list bmkp-this-buffer-bmenu-list bmkp-choose-navlist-of-type
;;;;;;  bmkp-choose-navlist-from-bookmark-list bmkp-crosshairs-highlight
;;;;;;  bmkp-empty-file bmkp-use-bookmark-file-create bmkp-switch-to-last-bookmark-file
;;;;;;  bmkp-switch-bookmark-file bmkp-make-function-bookmark bmkp-toggle-saving-bookmark-file
;;;;;;  bmkp-save-menu-list-state bmkp-toggle-saving-menu-list-state
;;;;;;  bmkp-toggle-bookmark-set-refreshes bmkp-send-bug-report bmkp-edit-tags-send
;;;;;;  bmkp-edit-tags bmkp-edit-bookmark-record-send bmkp-edit-bookmark-record
;;;;;;  bmkp-edit-bookmark bookmark-load bookmark-save bookmark-delete
;;;;;;  bookmark-insert bookmark-rename bookmark-insert-location
;;;;;;  bookmark-relocate bookmark-jump-other-window bookmark-jump
;;;;;;  bookmark-yank-word bookmark-set bookmark-edit-annotation
;;;;;;  bookmark-send-edited-annotation bookmark-edit-annotation-mode
;;;;;;  bmkp-w3m-allow-multi-tabs bmkp-use-region bmkp-this-buffer-cycle-sort-comparer
;;;;;;  bmkp-su-or-sudo-regexp bmkp-sort-comparer bmkp-show-end-of-region
;;;;;;  bmkp-sequence-jump-display-function bmkp-save-new-location-flag
;;;;;;  bmkp-region-search-size bmkp-prompt-for-tags-flag bmkp-other-window-pop-to-flag
;;;;;;  bmkp-menu-popup-max-length bmkp-incremental-filter-delay
;;;;;;  bmkp-handle-region-function bmkp-desktop-no-save-vars bmkp-default-handler-associations
;;;;;;  bmkp-default-bookmark-name bmkp-crosshairs-flag bmkp-bookmark-name-length-max
;;;;;;  bmkp-autoname-format bmkp-autoname-bookmark-function) "bookmark+-1"
;;;;;;  "site-lisp/bookmark+/bookmark+-1.el" (19910 59079))
;;; Generated autoloads from site-lisp/bookmark+/bookmark+-1.el

(defvar bmkp-autoname-bookmark-function 'bmkp-autoname-bookmark "\
*Function to automatically name a bookmark at point (cursor position).")

(custom-autoload 'bmkp-autoname-bookmark-function "bookmark+-1" t)

(defvar bmkp-autoname-format (if (> emacs-major-version 21) "^[0-9]\\{9\\} %s" "^[0-9]+ %s") "\
*Format string to match an autonamed bookmark name.
It must have a single `%s' that to accept the buffer name.")

(custom-autoload 'bmkp-autoname-format "bookmark+-1" t)

(defvar bmkp-bookmark-name-length-max 70 "\
*Max number of chars for default name for a bookmark with a region.")

(custom-autoload 'bmkp-bookmark-name-length-max "bookmark+-1" t)

(defvar bmkp-crosshairs-flag (> emacs-major-version 21) "\
*Non-nil means highlight with crosshairs when you visit a bookmark.
The highlighting is temporary - until your next action.
You need library `crosshairs.el' for this feature, and you need Emacs
22 or later.

If you use this option in Lisp code, you will want to add/remove
`bmkp-crosshairs-highlight' to/from `bookmark-after-jump-hook'.")

(custom-autoload 'bmkp-crosshairs-flag "bookmark+-1" nil)

(defvar bmkp-default-bookmark-name 'highlighted "\
*Default bookmark name preference.
In `*Bookmark List*' use the name of the current line's bookmark.
Otherwise, if `bookmark+-lit.el' is not loaded then use the name of
 the last-used bookmark in the current file.

Otherwise, use this option to determine the default, by preferring one
of the following, if available:

* a highlighted bookmark at point
* the last-used bookmark in the current file")

(custom-autoload 'bmkp-default-bookmark-name "bookmark+-1" t)

(defvar bmkp-default-handler-associations (and (require 'dired-x) (let ((assns nil)) (dolist (shell-assn dired-guess-shell-alist-user) (push (cons (car shell-assn) `(lambda (bmk) (dired-run-shell-command (dired-shell-stuff-it ,(cadr shell-assn) (list (bookmark-get-filename bmk)) nil nil)))) assns)) assns)) "\
*File associations for bookmark handlers used for indirect bookmarks.
Each element of the alist is (REGEXP . COMMAND).
REGEXP matches a file name.
COMMAND is a sexp that evaluates to either a shell command (a string)
 or an Emacs function (a symbol or a lambda form).

Example value:

 ((\"\\.pdf$\" . \"AcroRd32.exe\") ; Adobe Acrobat Reader
  (\"\\.ps$\" . \"gsview32.exe\")) ; Ghostview (PostScript viewer)

When you change this option using Customize, if you want to use a
literal string as COMMAND then you must double-quote the text:
\"...\".  (But do not use double-quotes for the REGEXP.)  If you want
to use a symbol as COMMAND, then single-quote it - e.g. 'foo.

This option is used by `bmkp-default-handler-user'.  If an association
for a given file name is not found using this option, then
`bmkp-default-handler-for-file' looks for an association in
`dired-guess-shell-alist-user', `dired-guess-shell-alist-default', and
in mailcap entries (Emacs 23+), in that order.")

(custom-autoload 'bmkp-default-handler-associations "bookmark+-1" t)

(defvar bmkp-desktop-no-save-vars '(search-ring regexp-search-ring kill-ring) "\
*List of variables not to save when creating a desktop bookmark.
They are removed from `desktop-globals-to-save' for the duration of
the save (only).")

(custom-autoload 'bmkp-desktop-no-save-vars "bookmark+-1" t)

(defvar bmkp-handle-region-function 'bmkp-handle-region-default "\
*Function to handle a bookmarked region.")

(custom-autoload 'bmkp-handle-region-function "bookmark+-1" t)

(defvar bmkp-incremental-filter-delay 0.6 "\
*Seconds to wait before updating display when filtering bookmarks.")

(custom-autoload 'bmkp-incremental-filter-delay "bookmark+-1" t)

(defvar bmkp-menu-popup-max-length 20 "\
*Max number of bookmarks for `bookmark-completing-read' to use a menu.
When choosing a bookmark from a list of bookmarks using
`bookmark-completing-read', this controls whether to use a menu or
minibuffer input with completion.
If t, then always use a menu.
If nil, then never use a menu.
If an integer, then use a menu only if there are fewer bookmark
 choices than the value.")

(custom-autoload 'bmkp-menu-popup-max-length "bookmark+-1" t)

(defvar bmkp-other-window-pop-to-flag t "\
*Non-nil means other-window bookmark jumping uses `pop-to-buffer'.
Use nil if you want the vanilla Emacs behavior, which uses
`switch-to-buffer-other-window'.  That creates a new window even if
there is already another window showing the buffer.")

(custom-autoload 'bmkp-other-window-pop-to-flag "bookmark+-1" t)

(defvar bmkp-prompt-for-tags-flag nil "\
*Non-nil means `bookmark-set' prompts for tags (when called interactively).")

(custom-autoload 'bmkp-prompt-for-tags-flag "bookmark+-1" t)

(defvar bmkp-region-search-size 40 "\
*Same as `bookmark-search-size', but specialized for bookmark regions.")

(custom-autoload 'bmkp-region-search-size "bookmark+-1" t)

(defvar bmkp-save-new-location-flag t "\
*Non-nil means save automatically relocated bookmarks.
If nil, then the new bookmark location is visited, but it is not saved
as part of the bookmark definition.")

(custom-autoload 'bmkp-save-new-location-flag "bookmark+-1" t)

(defvar bmkp-sequence-jump-display-function 'pop-to-buffer "\
*Function used to display the bookmarks in a bookmark sequence.")

(custom-autoload 'bmkp-sequence-jump-display-function "bookmark+-1" t)

(defvar bmkp-show-end-of-region t "\
*Show end of region with `exchange-point-and-mark' when activating a region.
If nil show only beginning of region.")

(custom-autoload 'bmkp-show-end-of-region "bookmark+-1" t)

(defvar bmkp-sort-comparer '((bmkp-info-cp bmkp-gnus-cp bmkp-url-cp bmkp-local-file-type-cp) bmkp-alpha-p) "\
*Predicate or predicates for sorting (comparing) bookmarks.
This defines the default sort for bookmarks in the bookmark list.

Various sorting commands, such as \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-sort-by-bookmark-visit-frequency]', change the value of this
option dynamically (but they do not save the changed value).

The value must be one of the following:

* nil, meaning do not sort

* a predicate that takes two bookmarks as args

* a list of the form ((PRED...) FINAL-PRED), where each PRED and
  FINAL-PRED are predicates that take two bookmarks as args

If the value is a list of predicates, then each PRED is tried in turn
until one returns a non-nil value.  In that case, the result is the
car of that value.  If no non-nil value is returned by any PRED, then
FINAL-PRED is used and its value is the result.

Each PRED should return `(t)' for true, `(nil)' for false, or nil for
undecided.  A nil value means that the next PRED decides (or
FINAL-PRED, if there is no next PRED).

Thus, a PRED is a special kind of predicate that indicates either a
boolean value (as a singleton list) or \"I cannot decide - let the
next guy else decide\".  (Essentially, each PRED is a hook function
that is run using `run-hook-with-args-until-success'.)

Examples:

 nil           - No sorting.

 string-lessp  - Single predicate that returns nil or non-nil.

 ((p1 p2))     - Two predicates `p1' and `p2', which each return
                 (t) for true, (nil) for false, or nil for undecided.

 ((p1 p2) string-lessp)
               - Same as previous, except if both `p1' and `p2' return
                 nil, then the return value of `string-lessp' is used.

Note that these two values are generally equivalent, in terms of their
effect (*):

 ((p1 p2))
 ((p1) p2-plain) where p2-plain is (bmkp-make-plain-predicate p2)

Likewise, these three values generally act equivalently (*):

 ((p1))
 (() p1-plain)
 p1-plain        where p1-plain is (bmkp-make-plain-predicate p1)

The PRED form lets you easily combine predicates: use `p1' unless it
cannot decide, in which case try `p2', and so on.  The value ((p2 p1))
tries the predicates in the opposite order: first `p2', then `p1' if
`p2' returns nil.

Using a single predicate or FINAL-PRED makes it easy to reuse an
existing predicate that returns nil or non-nil.

You can also convert a PRED-type predicate (which returns (t), (nil),
or nil) into an ordinary predicate, by using function
`bmkp-make-plain-predicate'.  That lets you reuse elsewhere, as
ordinary predicates, any PRED-type predicates you define.

For example, this defines a plain predicate to compare by URL:
 (defalias 'bmkp-url-p (bmkp-make-plain-predicate 'bmkp-url-cp))

Note: As a convention, predefined Bookmark+ PRED-type predicate names
have the suffix `-cp' (for \"component predicate\") instead of `-p'.

--
* If you use `\\[bmkp-reverse-multi-sort-order]', then there is a difference in behavior between

   (a) using a plain predicate as FINAL-PRED and
   (b) using the analogous PRED-type predicate (and no FINAL-PRED).

  In the latter case, `\\[bmkp-reverse-multi-sort-order]' affects when the predicate is tried and
  its return value.  See `bmkp-reverse-multi-sort-order'.")

(custom-autoload 'bmkp-sort-comparer "bookmark+-1" t)

(defvar bmkp-su-or-sudo-regexp "\\(/su:\\|/sudo:\\)" "\
*Regexp to recognize `su' or `sudo' Tramp bookmarks.")

(custom-autoload 'bmkp-su-or-sudo-regexp "bookmark+-1" t)

(defvar bmkp-this-buffer-cycle-sort-comparer '((bmkp-position-cp)) "\
*`bmkp-sort-comparer' value for cycling this-buffer bookmarks.
Some values you might want to use: ((bmkp-position-cp)),
 ((bmkp-bookmark-creation-cp)), ((bmkp-visited-more-cp)).
See `bmkp-sort-comparer'.")

(custom-autoload 'bmkp-this-buffer-cycle-sort-comparer "bookmark+-1" t)

(defvar bmkp-use-region t "\
*Non-nil means visiting a bookmark activates its recorded region.")

(custom-autoload 'bmkp-use-region "bookmark+-1" t)

(defvar bmkp-w3m-allow-multi-tabs t "\
*Non-nil means jump to W3M bookmarks in a new session.")

(custom-autoload 'bmkp-w3m-allow-multi-tabs "bookmark+-1" t)

(autoload 'bookmark-edit-annotation-mode "bookmark+-1" "\
Mode for editing the annotation of bookmark BOOKMARK.
When you have finished composing, type \\[bookmark-send-annotation].
BOOKMARK is a bookmark name or a bookmark record.

\\{bookmark-edit-annotation-mode-map}

\(fn BOOKMARK)" t nil)

(autoload 'bookmark-send-edited-annotation "bookmark+-1" "\
Use buffer contents as annotation for a bookmark.
Lines beginning with `#' are ignored.

\(fn)" t nil)

(autoload 'bookmark-edit-annotation "bookmark+-1" "\
Pop up a buffer for editing bookmark BOOKMARK's annotation.
BOOKMARK is a bookmark name or a bookmark record.

\(fn BOOKMARK)" t nil)

(autoload 'bookmark-set "bookmark+-1" "\
Set a bookmark named NAME, then run `bmkp-after-set-hook'.
If the region is active (`transient-mark-mode') and nonempty, then
record the region limits in the bookmark.

If NAME is nil, then prompt for the bookmark name.  The default name
for prompting is as follows (in order of priority):

 * If the region is active and nonempty, then the buffer name followed
   by \": \" and the region prefix (up to
   `bmkp-bookmark-name-length-max' chars).

 * If in W3M mode, then the current W3M title.

 * If in a Gnus mode, then the Gnus summary article header.

 * If on a `man' page, then the page name (command and section).

 * Otherwise, the current buffer name.

While entering a bookmark name at the prompt:

 * You can use (lax) completion against bookmarks in the same buffer.
   If there are no bookmarks in the current buffer, then all bookmarks
   are completion candidates.  (See also below, about a numeric prefix
   argument.)

 * You can use `C-w' to yank words from the buffer to the minibuffer.
   Repeating `C-w' yanks successive words.

 * You can use `C-u' to insert the name of the last bookmark used in
   the buffer.  This can be useful as an aid to track your progress
   through a large file.  (If no bookmark has yet been used, then
   `C-u' inserts the name of the visited file.)

A prefix argument changes the behavior as follows:

 * Numeric prefix arg: Use all bookmarks as completion candidates,
   instead of just the bookmarks for the current buffer.

 * Plain prefix arg (`C-u'): Do not overwrite a bookmark that has the
   same name as NAME, if such a bookmark already exists.  Instead,
   push the new bookmark onto the bookmark alist.

   The most recently set bookmark named NAME is thus the one in effect
   at any given time, but any others named NAME are still available,
   should you decide to delete the most recent one.

Use `\\[bookmark-delete]' to remove bookmarks (you give it a name, and it removes
only the first instance of a bookmark with that name from the list of
bookmarks).

\(fn &optional NAME PARG INTERACTIVEP)" t nil)

(autoload 'bookmark-yank-word "bookmark+-1" "\
Yank the word at point in `bookmark-current-buffer'.
Repeat to yank subsequent words from the buffer, appending them.
Newline characters are stripped out.

\(fn)" t nil)

(autoload 'bookmark-jump "bookmark+-1" "\
Jump to bookmark BOOKMARK.
You may have a problem using this function if the value of variable
`bookmark-alist' is nil.  If that happens, you need to load in some
bookmarks.  See function `bookmark-load' for more about this.

If the file pointed to by BOOKMARK no longer exists, you are asked if
you wish to give the bookmark a new location.  If so, `bookmark-jump'
jumps to the new location and saves it.

If the bookmark defines a region, then the region is activated if
`bmkp-use-region' is not-nil or it is nil and you use a prefix
argument.  A prefix arg temporarily flips the value of
`bmkp-use-region'.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.

In Lisp code:
BOOKMARK is a bookmark name or a bookmark record.
Non-nil DISPLAY-FUNCTION is a function to display the bookmark.  By
 default, `switch-to-buffer' is used.
Non-nil USE-REGION-P flips the value of `bmkp-use-region'.

\(fn BOOKMARK &optional DISPLAY-FUNCTION USE-REGION-P)" t nil)

(autoload 'bookmark-jump-other-window "bookmark+-1" "\
Jump to bookmark BOOKMARK in another window.
See `bookmark-jump', in particular for info about using a prefix arg.

\(fn BOOKMARK &optional USE-REGION-P)" t nil)

(autoload 'bookmark-relocate "bookmark+-1" "\
Relocate the bookmark named BOOKMARK-NAME to another file.
You are prompted for the new file name.
Changes the file associated with the bookmark.
Useful when a file has been renamed after a bookmark was set in it.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bookmark-insert-location "bookmark+-1" "\
Insert file or buffer name for the bookmark named BOOKMARK-NAME.
If a file is bookmarked, insert the recorded file name.
If a non-file buffer is bookmarked, insert the recorded buffer name.

Optional second arg NO-HISTORY means do not record this in the
minibuffer history list `bookmark-history'.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.

\(fn BOOKMARK-NAME &optional NO-HISTORY)" t nil)

(autoload 'bookmark-rename "bookmark+-1" "\
Change bookmark's name from OLD to NEW.
Interactively:
 If called from the keyboard, then prompt for OLD.
 If called from the menubar, select OLD from a menu.
If NEW is nil, then prompt for its string value.

If BATCH is non-nil, then do not rebuild the bookmark list.

While the user enters the new name, repeated `C-w' inserts consecutive
words from the buffer into the new bookmark name.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.

\(fn OLD &optional NEW BATCH)" t nil)

(autoload 'bookmark-insert "bookmark+-1" "\
Insert the text of a bookmarked file.
BOOKMARK-NAME is the name of the bookmark.
You may have a problem using this function if the value of variable
`bookmark-alist' is nil.  If that happens, you need to load in some
bookmarks.  See function `bookmark-load' for more about this.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bookmark-delete "bookmark+-1" "\
Delete the BOOKMARK from the bookmark list.
BOOKMARK is a bookmark name or a bookmark record.
Interactively, default to the \"current\" bookmark (that is, the one
most recently used in this file), if it exists.

If BOOKMARK is a name and it has property `bmkp-full-record' then use
that property along with the name to find the bookmark to delete.
If it is a name without property `bmkp-full-record' then delete (only)
the first bookmark in `bookmark-alist' with that name.

Optional second arg BATCH means do not update the bookmark list buffer
\(probably because we were called from there).

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.  In this way, you can delete multiple bookmarks.

\(fn BOOKMARK &optional BATCH)" t nil)

(autoload 'bookmark-save "bookmark+-1" "\
Save currently defined bookmarks.
Save by default in the file named by variable
`bmkp-current-bookmark-file'.  With a prefix arg, you are prompted for
the file to save to.

To load bookmarks from a specific file, use `\\[bookmark-load]'
\(`bookmark-load').

If called from Lisp:
 Witn nil PARG, use file `bmkp-current-bookmark-file'.
 With non-nil PARG and non-nil FILE, use file FILE.
 With non-nil PARG and nil FILE, prompt the user for the file to use.

\(fn &optional PARG FILE)" t nil)

(autoload 'bookmark-load "bookmark+-1" "\
Load bookmarks from FILE (which must be in the standard format).
Without a prefix argument (argument OVERWRITE is nil), add the newly
loaded bookmarks to those already current.  They will be saved to the
current bookmark file when bookmarks are saved.  If you have never
switched bookmark files, then this is the default file,
`bookmark-default-file'.

If you do not use a prefix argument, then no existing bookmarks are
overwritten.  If you load some bookmarks that have the same names as
bookmarks already defined in your Emacs session, numeric suffixes
\"<2>\", \"<3>\",... are appended as needed to the names of those new
bookmarks to distinguish them.

With a prefix argument, switch the bookmark file currently used,
*replacing* all currently existing bookmarks with the newly loaded
bookmarks.  The value of `bmkp-current-bookmark-file' is changed to
FILE, so bookmarks will subsequently be saved to FILE.  The value
`bookmark-default-file' is unaffected, so your next Emacs session will
still use the same default set of bookmarks.

When called from Lisp, non-nil NO-MSG means do not display any
messages while loading.

You do not need to manually load your default bookmark file
\(`bookmark-default-file') - it is loaded automatically by Emacs the
first time you use bookmarks in a session.  Use `bookmark-load' only
to load extra bookmarks (with no prefix arg) or an alternative set of
bookmarks (with a prefix arg).

If you use `bookmark-load' to load a file that does not contain a
proper bookmark alist, then when bookmarks are saved the current
bookmark file will likely become corrupted.  You should load only
bookmark files that were created using the bookmark functions.

\(fn FILE &optional OVERWRITE NO-MSG)" t nil)

(autoload 'bmkp-edit-bookmark "bookmark+-1" "\
Edit BOOKMARK's name and file name, and maybe save them.
BOOKMARK is a bookmark name (a string) or a bookmark record.
With a prefix argument, edit the complete bookmark record (the
internal, Lisp form).
Return a list of the new bookmark name and new file name.

\(fn BOOKMARK &optional INTERNALP)" t nil)

(autoload 'bmkp-edit-bookmark-record "bookmark+-1" "\
Edit the internal record for bookmark BOOKMARK.
When you have finished, Use `\\[bmkp-edit-bookmark-record-send]'.
BOOKMARK is a bookmark name (a string) or a bookmark record.

\(fn BOOKMARK)" t nil)

(autoload 'bmkp-edit-bookmark-record-send "bookmark+-1" "\
Use buffer contents as a bookmark record.
Lines beginning with `;;' are ignored.
With a prefix argument, do not update `time' or `visits' entries.

\(fn ARG &optional FORCE)" t nil)

(autoload 'bmkp-edit-tags "bookmark+-1" "\
Edit BOOKMARK's tags, and maybe save the result.
The edited value must be a list each of whose elements is either a
 string or a cons whose key is a string.
BOOKMARK is a bookmark name (a string) or a bookmark record.

\(fn BOOKMARK)" t nil)

(autoload 'bmkp-edit-tags-send "bookmark+-1" "\
Use buffer contents as the internal form of a bookmark's tags.
DO NOT MODIFY the header comment lines, which begin with `;;'.

\(fn)" t nil)

(autoload 'bmkp-send-bug-report "bookmark+-1" "\
Send a bug report about a Bookmark+ problem.

\(fn)" t nil)

(autoload 'bmkp-toggle-bookmark-set-refreshes "bookmark+-1" "\
Toggle `bookmark-set' refreshing `bmkp-latest-bookmark-alist'.
Add/remove `bmkp-refresh-latest-bookmark-list' to/from
`bmkp-after-set-hook'.

\(fn)" t nil)

(autoload 'bmkp-toggle-saving-menu-list-state "bookmark+-1" "\
Toggle the value of option `bmkp-bmenu-state-file'.
Tip: You can use this before quitting Emacs, to not save the state.
If the initial value of `bmkp-bmenu-state-file' is nil, then this
command has no effect.

\(fn)" t nil)

(autoload 'bmkp-save-menu-list-state "bookmark+-1" "\
Save menu-list state, unless not saving or list has not yet been shown.
The state is saved to the value of `bmkp-bmenu-state-file'.

\(fn)" t nil)

(autoload 'bmkp-toggle-saving-bookmark-file "bookmark+-1" "\
Toggle the value of option `bookmark-save-flag'.
If the initial value of `bookmark-save-flag' is nil, then this
command has no effect.

\(fn)" t nil)

(autoload 'bmkp-make-function-bookmark "bookmark+-1" "\
Create a bookmark that invokes FUNCTION when \"jumped\" to.
You are prompted for the bookmark name and the name of the function.
Returns the new bookmark (internal record).

\(fn BOOKMARK-NAME FUNCTION)" t nil)

(autoload 'bmkp-switch-bookmark-file "bookmark+-1" "\
Switch to a different bookmark file, FILE.
Replace all currently existing bookmarks with the newly loaded
bookmarks.  Change the value of `bmkp-current-bookmark-file' to FILE,
so bookmarks will subsequently be saved to FILE.

`bookmark-default-file' is unaffected, so your next Emacs session will
still use `bookmark-default-file' for the initial set of bookmarks.

\(fn FILE &optional NO-MSG)" t nil)

(autoload 'bmkp-switch-to-last-bookmark-file "bookmark+-1" "\
Switch back to the last-used bookmarkfile.
Replace all currently existing bookmarks with those newly loaded from
the last-used file.  Swap the values of `bmkp-last-bookmark-file' and
`bmkp-current-bookmark-file'.

\(fn &optional NO-MSG)" t nil)

(autoload 'bmkp-use-bookmark-file-create "bookmark+-1" "\
Switch current bookmark file to FILE, creating it if it does not exist.
Interactively, you are prompted for the file name.  The default is
`.emacs.bmk' in the current directory, but you can enter any file
name, anywhere.

If there is no file with the name you provide then a new, an empty
bookmark file with that name is created.

You are prompted to confirm the bookmark-file switch.

Returns FILE.

\(fn FILE)" t nil)

(autoload 'bmkp-empty-file "bookmark+-1" "\
Empty the bookmark file FILE, or create FILE (empty) if it does not exist.
In either case, FILE will become an empty bookmark file.  Return FILE.

NOTE: If FILE already exists and you confirm emptying it, no check is
      made that it is in fact a bookmark file before emptying it.
      It is simply replaced by an empty bookmark file and saved.

This does NOT also make FILE the current bookmark file.  To do that,
use `\\[bmkp-switch-bookmark-file]' (`bmkp-switch-bookmark-file').

\(fn FILE)" t nil)

(autoload 'bmkp-crosshairs-highlight "bookmark+-1" "\
Call `crosshairs-highlight', unless the region is active.
You can add this to hook `bookmark-after-jump-hook'.
You need library `crosshairs.el' to use this command.

\(fn)" t nil)

(autoload 'bmkp-choose-navlist-from-bookmark-list "bookmark+-1" "\
Choose a bookmark-list bookmark and set the bookmark navigation list.
The navigation-list variable, `bmkp-nav-alist', is set to the list of
bookmarks that would be displayed by `bookmark-bmenu-list' (`C-x r l')
for the chosen bookmark-list bookmark, sorted and filtered as
appropriate.

Instead of choosing a bookmark-list bookmark, you can choose the
pseudo-bookmark `CURRENT *Bookmark List*'.  The bookmarks used for the
navigation list are those that would be currently shown in the
`*Bookmark List*' (even if the list is not currently displayed).

\(fn BOOKMARK-NAME &optional ALIST)" t nil)

(autoload 'bmkp-choose-navlist-of-type "bookmark+-1" "\
Set the bookmark navigation list to the bookmarks of a type you choose.
The pseudo-type `any' sets the navigation list to all bookmarks.
This sets variable `bmkp-nav-alist'.

\(fn TYPE)" t nil)

(autoload 'bmkp-this-buffer-bmenu-list "bookmark+-1" "\
Show the bookmark list just for bookmarks for the current buffer.
Set `bmkp-last-specific-buffer' to the current buffer name.

\(fn)" t nil)

(autoload 'bmkp-navlist-bmenu-list "bookmark+-1" "\
Show the bookmark list just for bookmarks from the navigation list.

\(fn)" t nil)

(autoload 'bmkp-unomit-all "bookmark+-1" "\
Remove all bookmarks from the list of omitted bookmarks.
All bookmarks will henceforth be available for display.

\(fn)" t nil)

(autoload 'bmkp-list-all-tags "bookmark+-1" "\
List all tags used for any bookmarks.
With a prefix argument, list the full alist of tags.
Otherwise, list only the tag names.

Note that when the full alist is shown, the same tag name will appear
once for each of its different values.

Show list in minibuffer or, if not enough space, buffer `*All Tags*'.

\(fn FULLP)" t nil)

(autoload 'bmkp-remove-all-tags "bookmark+-1" "\
Remove all tags from BOOKMARK.
Non-nil optional arg MSGP means display a message about the removal.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.

\(fn BOOKMARK &optional MSGP NO-CACHE-UPDATE-P)" t nil)

(autoload 'bmkp-add-tags "bookmark+-1" "\
Add TAGS to BOOKMARK.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
Completion for the bookmark name is strict.
Completion for tags is lax: you are not limited to existing tags.

TAGS is a list of strings.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags added.

\(fn BOOKMARK TAGS &optional MSGP NO-CACHE-UPDATE-P)" t nil)

(autoload 'bmkp-set-tag-value-for-navlist "bookmark+-1" "\
Set the value of TAG to VALUE, for each bookmark in the navlist.
If any of the bookmarks has no tag named TAG, then add one with VALUE.

\(fn TAG VALUE)" t nil)

(autoload 'bmkp-set-tag-value "bookmark+-1" "\
For BOOKMARK's TAG, set the value to VALUE.
If BOOKMARK has no tag named TAG, then add one with value VALUE.

\(fn BOOKMARK TAG VALUE &optional MSGP)" t nil)

(autoload 'bmkp-remove-tags "bookmark+-1" "\
Remove TAGS from BOOKMARK.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

TAGS is a list of strings.  The corresponding tags are removed.
Non-nil MSGP means display messages.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags removed.

\(fn BOOKMARK TAGS &optional MSGP NO-CACHE-UPDATE-P)" t nil)

(autoload 'bmkp-remove-tags-from-all "bookmark+-1" "\
Remove TAGS from all bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag.
This affects all bookmarks, even those not showing in bookmark list.

TAGS is a list of strings.  The corresponding tags are removed.
Non-nil optional arg MSGP means display a message about the deletion.

\(fn TAGS &optional MSGP)" t nil)

(autoload 'bmkp-rename-tag "bookmark+-1" "\
Rename TAG to NEWNAME in all bookmarks, even those not showing.
Non-nil optional arg MSGP means display a message about the deletion.

\(fn TAG NEWNAME &optional MSGP)" t nil)

(autoload 'bmkp-copy-tags "bookmark+-1" "\
Copy tags from BOOKMARK, so you can paste them to another bookmark.
Note that you can copy from a BOOKMARK that has no tags or has an
empty tags list.  In that case, the copied-tags list is empty, so if
you paste it as a replacement then the recipient bookmark will end up
with no tags.

Non-nil optional arg MSGP means display a message about the number of
tags copied.

\(fn BOOKMARK &optional MSGP)" t nil)

(autoload 'bmkp-paste-add-tags "bookmark+-1" "\
Add tags to BOOKMARK that were previously copied from another bookmark.
The tags are copied from `bmkp-copied-tags'.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags added.

\(fn BOOKMARK &optional MSGP NO-CACHE-UPDATE-P)" t nil)

(autoload 'bmkp-paste-replace-tags "bookmark+-1" "\
Replace tags for BOOKMARK with those copied from another bookmark.
The tags are copied from `bmkp-copied-tags'.
Any previously existing tags for BOOKMARK are lost.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags.

\(fn BOOKMARK &optional MSGP NO-CACHE-UPDATE-P)" t nil)

(autoload 'bmkp-url-target-set "bookmark+-1" "\
Set a bookmark for a URL.  Return the bookmark.
Interactively you are prompted for the URL.  Completion is available.
Use `M-n' to pick up the url at point as the default.

You are also prompted for the bookmark name.  But with a prefix arg,
you are prompted only for a bookmark-name prefix.  In that case, the
bookmark name is the prefix followed by the URL.

\(fn URL &optional PREFIX-ONLY-P NAME/PREFIX)" t nil)

(autoload 'bmkp-file-target-set "bookmark+-1" "\
Set a bookmark for FILE.  Return the bookmark.
The bookmarked position is the beginning of the file.
Interactively you are prompted for FILE.  Completion is available.
You can use `M-n' to pick up the file name at point, or if none then
the visited file.

You are also prompted for the bookmark name.  But with a prefix arg,
you are prompted only for a bookmark-name prefix.  In that case, the
bookmark name is the prefix followed by the non-directory part of
FILE.

From Lisp code, optional arg NO-OVERWRITE is passed to
`bookmark-store': non-nil means do not overwrite an existing bookmark
that has the same name.

\(fn FILE &optional PREFIX-ONLY-P NAME/PREFIX NO-OVERWRITE MSGP)" t nil)

(defalias 'bmkp-bookmark-a-file 'bmkp-autofile-set)

(autoload 'bmkp-autofile-set "bookmark+-1" "\
Set a bookmark for FILE, autonaming the bookmark for the file.
Return the bookmark.
Interactively, you are prompted for FILE.  You can use `M-n' to pick
up the file name at point, or if none then the visited file.

The bookmark name is the non-directory part of FILE, but with a prefix
arg you are also prompted for a PREFIX string to prepend to the
bookmark name.  The bookmarked position is the beginning of the file.

Note that if you provide PREFIX then the bookmark will not satisfy
`bmkp-autofile-bookmark-p' unless you provide the same PREFIX to that
predicate.

The bookmark's file name is FILE if absolute.  If relative then it is
FILE expanded in DIR, if non-nil, or in the current directory
\(`default-directory').

If a bookmark with the same name already exists for the same file name
then do nothing.

Otherwise, create a new bookmark for the file, even if a bookmark with
the same name already exists.  This means that you can have more than
one autofile bookmark with the same bookmark name and the same
relative file name (non-directory part), but with different absolute
file names.

\(fn FILE &optional DIR PREFIX MSGP)" t nil)

(defalias 'bmkp-tag-a-file 'bmkp-autofile-add-tags)

(autoload 'bmkp-autofile-add-tags "bookmark+-1" "\
Add TAGS to autofile bookmark for FILE.
Interactively, you are prompted for FILE and then TAGS.
When prompted for FILE you can use `M-n' to pick up the file name at
point, or if none then the visited file.

When prompted for tags, hit `RET' to enter each tag, then hit `RET'
again after the last tag.  You can use completion to enter each tag.
Completion is lax: you are not limited to existing tags.

TAGS is a list of strings. DIR, PREFIX are as for `bmkp-autofile-set'.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags added.

\(fn FILE TAGS &optional DIR PREFIX MSGP NO-CACHE-UPDATE-P)" t nil)

(defalias 'bmkp-untag-a-file 'bmkp-autofile-remove-tags)

(autoload 'bmkp-autofile-remove-tags "bookmark+-1" "\
Remove TAGS from autofile bookmark for FILE.
Interactively, you are prompted for TAGS and then FILE.
With Emacs 22 and later, only files with at least one of the given
tags are candidates.

When prompted for tags, hit `RET' to enter each tag to be removed,
then hit `RET' again after the last tag.  You can use completion to
enter each tag.

When prompted for FILE you can use `M-n' to pick up the file name at
point, or if none then the visited file.

TAGS is a list of strings. DIR, PREFIX are as for `bmkp-autofile-set'.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags removed.

\(fn FILE TAGS &optional DIR PREFIX MSGP NO-CACHE-UPDATE-P)" t nil)

(autoload 'bmkp-purge-notags-autofiles "bookmark+-1" "\
Delete all autofile bookmarks that have no tags.
With a prefix arg, you are prompted for a PREFIX for the bookmark name.

\(fn &optional PREFIX)" t nil)

(autoload 'bmkp-describe-bookmark "bookmark+-1" "\
Describe BOOKMARK.
With a prefix argument, show the internal definition of the bookmark.
BOOKMARK is a bookmark name or a bookmark record.

Starting with Emacs 22, if the file is an image file then:
* Show a thumbnail of the image as well.
* If you have command-line tool `exiftool' installed and in your
  `$PATH' or `exec-path', then show EXIF data (metadata) about the
  image.  See standard Emacs library `image-dired.el' for more
  information about `exiftool'

\(fn BOOKMARK &optional DEFN)" t nil)

(autoload 'bmkp-describe-bookmark-internals "bookmark+-1" "\
Show the internal definition of the bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.

\(fn BOOKMARK)" t nil)

(autoload 'bmkp-list-defuns-in-commands-file "bookmark+-1" "\
List the functions defined in `bmkp-bmenu-commands-file'.
Typically, these are all commands.

\(fn)" t nil)

(autoload 'bmkp-set-bookmark-file-bookmark "bookmark+-1" "\
Create a bookmark that loads bookmark-file FILE when \"jumped\" to.
You are prompted for the names of the bookmark file and the bookmark.

\(fn FILE &optional MSGP)" t nil)

(autoload 'bmkp-bookmark-file-jump "bookmark+-1" "\
Jump to a bookmark-file bookmark, which means load its bookmark file.
With a prefix argument, switch to the new bookmark file.
Otherwise, load it to supplement the current bookmark list.

\(fn BOOKMARK-NAME &optional SWITCHP NO-MSG)" t nil)

(autoload 'bmkp-set-desktop-bookmark "bookmark+-1" "\
Save the desktop as a bookmark.
You are prompted for the desktop-file location and the bookmark name.

\(fn DESKTOP-FILE)" t nil)

(autoload 'bmkp-desktop-change-dir "bookmark+-1" "\
Change to desktop saved in DESKTOP-FILE.
Kill the desktop as specified by variables `desktop-save-mode' and
 `desktop-save' (starting with Emacs 22).
Clear the desktop and load DESKTOP-FILE DIRNAME.

\(fn DESKTOP-FILE)" t nil)

(autoload 'bmkp-desktop-read "bookmark+-1" "\
Load desktop-file FILE, then run `desktop-after-read-hook'.
Return t if FILE was loaded, nil otherwise.

\(fn FILE)" t nil)

(autoload 'bmkp-desktop-delete "bookmark+-1" "\
Delete desktop bookmark BOOKMARK-NAME, and delete its desktop file.
Release the lock file in that desktop's directory.
\(This means that if you currently have locked a different desktop
in the same directory, then you will need to relock it.)

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bmkp-set-variable-list-bookmark "bookmark+-1" "\
Save a list of variables as a bookmark.
Interactively, read the variables to save, using
`bmkp-read-variables-completing'.

\(fn VARIABLES)" t nil)

(autoload 'bmkp-dired-subdirs "bookmark+-1" "\
Alist of inserted subdirectories, without their positions (markers).
This is like `dired-subdir-alist' but without the top-level dir and
without subdir positions (markers).

\(fn)" t nil)

(autoload 'bmkp-jump-to-type "bookmark+-1" "\
Jump to a bookmark of a given type.  You are prompted for the type.
Otherwise, this is the same as `bookmark-jump' - see that, in
particular, for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-jump-to-type-other-window "bookmark+-1" "\
`bmkp-jump-to-type', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-autonamed-jump "bookmark+-1" "\
Jump to an autonamed bookmark.
This is a specialization of `bookmark-jump'.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bmkp-autonamed-jump-other-window "bookmark+-1" "\
`bmkp-autonamed-jump', but in another window.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bmkp-autonamed-this-buffer-jump "bookmark+-1" "\
Jump to an autonamed bookmark in the current buffer.
This is a specialization of `bookmark-jump'.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bmkp-autonamed-this-buffer-jump-other-window "bookmark+-1" "\
`bmkp-autonamed-this-buffer-jump', but in another window.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bmkp-bookmark-list-jump "bookmark+-1" "\
Jump to a bookmark-list bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-desktop-jump "bookmark+-1" "\
Jump to a desktop bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-dired-jump "bookmark+-1" "\
Jump to a Dired bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-dired-jump-other-window "bookmark+-1" "\
`bmkp-dired-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-dired-this-dir-jump "bookmark+-1" "\
Jump to a Dired bookmark for the `default-directory'.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-dired-this-dir-jump-other-window "bookmark+-1" "\
`bmkp-dired-this-dir-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-file-jump "bookmark+-1" "\
Jump to a file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-file-jump-other-window "bookmark+-1" "\
`bmkp-file-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-file-this-dir-jump "bookmark+-1" "\
Jump to a bookmark for a file or subdir in the `default-directory'.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-file-this-dir-jump-other-window "bookmark+-1" "\
`bmkp-file-this-dir-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-gnus-jump "bookmark+-1" "\
Jump to a Gnus bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-gnus-jump-other-window "bookmark+-1" "\
`bmkp-gnus-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-info-jump "bookmark+-1" "\
Jump to an Info bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-info-jump-other-window "bookmark+-1" "\
`bmkp-info-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-local-file-jump "bookmark+-1" "\
Jump to a local file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-local-file-jump-other-window "bookmark+-1" "\
`bmkp-local-file-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-man-jump "bookmark+-1" "\
Jump to a `man'-page bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-man-jump-other-window "bookmark+-1" "\
`bmkp-man-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-non-file-jump "bookmark+-1" "\
Jump to a non-file (buffer) bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-non-file-jump-other-window "bookmark+-1" "\
`bmkp-non-file-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-region-jump "bookmark+-1" "\
Jump to a region bookmark.
This is a specialization of `bookmark-jump', but without a prefix arg.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bmkp-region-jump-other-window "bookmark+-1" "\
`bmkp-region-jump', but in another window.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bmkp-remote-file-jump "bookmark+-1" "\
Jump to a remote file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-remote-file-jump-other-window "bookmark+-1" "\
`bmkp-remote-file-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-specific-buffers-jump "bookmark+-1" "\
Jump to a bookmark for a buffer in list BUFFERS.
Interactively, read buffer names and bookmark name, with completion.

This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BUFFERS BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-specific-buffers-jump-other-window "bookmark+-1" "\
`bmkp-specific-buffers-jump', but in another window.

\(fn BUFFERS BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-specific-files-jump "bookmark+-1" "\
Jump to a bookmark for a file in list FILES.
Interactively, read file names and bookmark name, with completion.

This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn FILES BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-specific-files-jump-other-window "bookmark+-1" "\
`bmkp-specific-files-jump', but in another window.

\(fn FILES BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-this-buffer-jump "bookmark+-1" "\
Jump to a bookmark for the current buffer.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-this-buffer-jump-other-window "bookmark+-1" "\
`bmkp-this-buffer-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-variable-list-jump "bookmark+-1" "\
Jump to a variable-list bookmark.
This is a specialization of `bookmark-jump'.

\(fn BOOKMARK-NAME)" t nil)

(autoload 'bmkp-url-jump "bookmark+-1" "\
Jump to a URL bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-url-jump-other-window "bookmark+-1" "\
`bmkp-url-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-w3m-jump "bookmark+-1" "\
Jump to a W3M bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-w3m-jump-other-window "bookmark+-1" "\
`bmkp-w3m-jump', but in another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-all-tags-jump "bookmark+-1" "\
Jump to a BOOKMARK that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-all-tags-jump-other-window "bookmark+-1" "\
`bmkp-all-tags-jump', but in another window.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-all-tags-regexp-jump "bookmark+-1" "\
Jump to a BOOKMARK that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion).

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-all-tags-regexp-jump-other-window "bookmark+-1" "\
`bmkp-all-tags-regexp-jump', but in another window.

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-some-tags-jump "bookmark+-1" "\
Jump to a BOOKMARK that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-some-tags-jump-other-window "bookmark+-1" "\
`bmkp-some-tags-jump', but in another window.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-some-tags-regexp-jump "bookmark+-1" "\
Jump to a BOOKMARK that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion).

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-some-tags-regexp-jump-other-window "bookmark+-1" "\
`bmkp-some-tags-regexp-jump', but in another window.

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-file-all-tags-jump "bookmark+-1" "\
Jump to a file or directory BOOKMARK that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-file-all-tags-jump-other-window "bookmark+-1" "\
`bmkp-file-all-tags-jump', but in another window.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-file-all-tags-regexp-jump "bookmark+-1" "\
Jump to a file or directory BOOKMARK that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion).

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-file-all-tags-regexp-jump-other-window "bookmark+-1" "\
`bmkp-file-all-tags-regexp-jump', but in another window.

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-file-some-tags-jump "bookmark+-1" "\
Jump to a file or directory BOOKMARK that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-file-some-tags-jump-other-window "bookmark+-1" "\
`bmkp-file-some-tags-jump', but in another window.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-file-some-tags-regexp-jump "bookmark+-1" "\
Jump to a file or directory BOOKMARK that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion).

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-file-some-tags-regexp-jump-other-window "bookmark+-1" "\
`bmkp-file-some-tags-regexp-jump', but in another window.

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-file-this-dir-all-tags-jump "bookmark+-1" "\
Jump to a file BOOKMARK in this dir that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-file-this-dir-all-tags-jump-other-window "bookmark+-1" "\
`bmkp-file-this-dir-all-tags-jump', but in another window.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-file-this-dir-all-tags-regexp-jump "bookmark+-1" "\
Jump to a file BOOKMARK in this dir that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion).

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-file-this-dir-all-tags-regexp-jump-other-window "bookmark+-1" "\
`bmkp-file-this-dir-all-tags-regexp-jump', but in another window.

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-file-this-dir-some-tags-jump "bookmark+-1" "\
Jump to a file BOOKMARK in this dir that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-file-this-dir-some-tags-jump-other-window "bookmark+-1" "\
`bmkp-file-this-dir-some-tags-jump', but in another window.

\(fn TAGS BOOKMARK)" t nil)

(autoload 'bmkp-file-this-dir-some-tags-regexp-jump "bookmark+-1" "\
Jump to a file BOOKMARK in this dir that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion).

\(fn REGEXP BOOKMARK)" t nil)

(autoload 'bmkp-file-this-dir-some-tags-regexp-jump-other-window "bookmark+-1" "\
`bmkp-file-this-dir-some-tags-regexp-jump', but in another window.

\(fn REGEXP BOOKMARK)" t nil)

(when (> emacs-major-version 21) (defun bmkp-find-file-all-tags-regexp-other-window (regexp) "`bmkp-find-file-all-tags-regexp', but in another window." (interactive (list (read-string "Regexp for tags: "))) (let ((use-file-dialog nil) (pred #'(lambda (ff) (let* ((bmk (bmkp-get-autofile-bookmark ff)) (btgs (and bmk (bmkp-get-tags bmk)))) (and btgs (bmkp-every #'(lambda (tag) (string-match regexp (bmkp-tag-name tag))) btgs)))))) (find-file-other-window (read-file-name "Find file: " nil nil t nil pred)))))

(when (> emacs-major-version 21) (defun bmkp-find-file-some-tags (tags) "Visit a file or directory that has at least one of the TAGS.\nHit `RET' to enter each tag, then hit `RET' again after the last tag.\nYou can use completion." (interactive (list (bmkp-read-tags-completing))) (let ((use-file-dialog nil) (pred #'(lambda (ff) (let* ((bmk (bmkp-get-autofile-bookmark ff)) (btgs (and bmk (bmkp-get-tags bmk)))) (and btgs (bmkp-some #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags)))))) (find-file (read-file-name "Find file: " nil nil t nil pred)))))

(when (> emacs-major-version 21) (defun bmkp-find-file-some-tags-other-window (tags) "`bmkp-find-file-some-tags', but in another window." (interactive (list (bmkp-read-tags-completing))) (let ((use-file-dialog nil) (pred #'(lambda (ff) (let* ((bmk (bmkp-get-autofile-bookmark ff)) (btgs (and bmk (bmkp-get-tags bmk)))) (and btgs (bmkp-some #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags)))))) (find-file-other-window (read-file-name "Find file: " nil nil t nil pred)))))

(when (> emacs-major-version 21) (defun bmkp-find-file-some-tags-regexp (regexp) "Visit a file or directory that has a tag matching REGEXP.\nYou are prompted for the REGEXP." (interactive (list (read-string "Regexp for tags: "))) (let ((use-file-dialog nil) (pred #'(lambda (ff) (let* ((bmk (bmkp-get-autofile-bookmark ff)) (btgs (and bmk (bmkp-get-tags bmk)))) (and btgs (bmkp-some #'(lambda (tag) (string-match regexp (bmkp-tag-name tag))) btgs)))))) (find-file (read-file-name "Find file: " nil nil t nil pred)))))

(when (> emacs-major-version 21) (defun bmkp-find-file-some-tags-regexp-other-window (regexp) "`bmkp-find-file-some-tags-regexp', but in another window." (interactive (list (read-string "Regexp for tags: "))) (let ((use-file-dialog nil) (pred #'(lambda (ff) (let* ((bmk (bmkp-get-autofile-bookmark ff)) (btgs (and bmk (bmkp-get-tags bmk)))) (and btgs (bmkp-some #'(lambda (tag) (string-match regexp (bmkp-tag-name tag))) btgs)))))) (find-file-other-window (read-file-name "Find file: " nil nil t nil pred)))))

(autoload 'bmkp-jump-in-navlist "bookmark+-1" "\
Jump to a bookmark, choosing from those in the navigation list.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-jump-in-navlist-other-window "bookmark+-1" "\
Same as `bmkp-jump-in-navlist', but use another window.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-cycle "bookmark+-1" "\
Cycle through bookmarks in the navlist by INCREMENT (default: 1).
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value

Plain `C-u' also means start over at first bookmark.

You can set the navigation list using commands
 `bmkp-choose-navlist-from-bookmark-list' and
 `bmkp-choose-navlist-of-type'.

You can cycle among bookmarks in the current buffer using
 `bmkp-cycle-this-buffer' and
 `bmkp-cycle-this-buffer-other-window.'

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist.

\(fn INCREMENT &optional OTHER-WINDOW STARTOVERP)" t nil)

(autoload 'bmkp-cycle-other-window "bookmark+-1" "\
Same as `bmkp-cycle' but uses another window.

\(fn INCREMENT &optional STARTOVERP)" t nil)

(autoload 'bmkp-cycle-this-buffer "bookmark+-1" "\
Cycle through bookmarks in this buffer by INCREMENT (default: 1).
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value 

Plain `C-u' also means start over at first bookmark.

You can cycle among bookmarks beyond the current buffer using
`bmkp-cycle' and `bmkp-cycle-other-window.'

You can set your preferred sort order for this-buffer bookmarks by
customizing option `bmkp-this-buffer-cycle-sort-comparer'.

To change the sort order without customizing, you can use `\\[bmkp-this-buffer-bmenu-list]' to
show the `*Bookmark List*' with only this buffer's bookmarks, sort
them there, and use `\\[bmkp-choose-navlist-from-bookmark-list]', choosing `CURRENT *Bookmark List*' as
the navigation list.

Then you can cycle the bookmarks using `bmkp-cycle'
\(`\\[bmkp-next-bookmark-repeat]' etc.), instead of `bmkp-cycle-this-buffer'.

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist.

\(fn INCREMENT &optional OTHER-WINDOW STARTOVERP)" t nil)

(autoload 'bmkp-cycle-this-buffer-other-window "bookmark+-1" "\
Same as `bmkp-cycle-this-buffer' but use other window.

\(fn INCREMENT &optional STARTOVERP)" t nil)

(autoload 'bmkp-next-bookmark "bookmark+-1" "\
Jump to the Nth next bookmark in the bookmark navigation list.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at first bookmark.
See also `bmkp-cycle'.

\(fn N &optional STARTOVERP)" t nil)

(autoload 'bmkp-previous-bookmark "bookmark+-1" "\
Jump to the Nth previous bookmark in the bookmark navigation list.
See `bmkp-next-bookmark'.

\(fn N &optional STARTOVERP)" t nil)

(autoload 'bmkp-next-bookmark-repeat "bookmark+-1" "\
Jump to the Nth-next bookmark in the bookmark navigation list.
This is a repeatable version of `bmkp-next-bookmark'.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at the first bookmark (and no repeat).

\(fn ARG)" t nil)

(autoload 'bmkp-previous-bookmark-repeat "bookmark+-1" "\
Jump to the Nth-previous bookmark in the bookmark navigation list.
See `bmkp-next-bookmark-repeat'.

\(fn ARG)" t nil)

(autoload 'bmkp-next-bookmark-this-buffer "bookmark+-1" "\
Jump to the Nth-next bookmark in the current buffer.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle-this-buffer'.

\(fn N &optional STARTOVERP)" t nil)

(autoload 'bmkp-previous-bookmark-this-buffer "bookmark+-1" "\
Jump to the Nth-previous bookmark in the current buffer.
See `bmkp-next-bookmark-this-buffer'.

\(fn N &optional STARTOVERP)" t nil)

(autoload 'bmkp-next-bookmark-this-buffer-repeat "bookmark+-1" "\
Jump to the Nth next bookmark in the current buffer.
This is a repeatable version of `bmkp-next-bookmark-this-buffer'.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one (and no repeat).

\(fn ARG)" t nil)

(autoload 'bmkp-previous-bookmark-this-buffer-repeat "bookmark+-1" "\
Jump to the Nth previous bookmark in the current buffer.
See `bmkp-next-bookmark-this-buffer-repeat'.

\(fn ARG)" t nil)

(autoload 'bmkp-next-bookmark-w32 "bookmark+-1" "\
Windows `Open' the Nth next bookmark in the bookmark navigation list.
MS Windows only.  Invokes the program associated with the file type.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle'.

\(fn N &optional STARTOVERP)" t nil)

(autoload 'bmkp-previous-bookmark-w32 "bookmark+-1" "\
Windows `Open' the Nth previous bookmark in the bookmark navlist.
See `bmkp-next-bookmark-w32'.

\(fn N &optional STARTOVERP)" t nil)

(autoload 'bmkp-next-bookmark-w32-repeat "bookmark+-1" "\
Windows `Open' the Nth next bookmark in the bookmark navigation list.
This is a repeatable version of `bmkp-next-bookmark'.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at the first one (and no repeat).

\(fn ARG)" t nil)

(autoload 'bmkp-previous-bookmark-w32-repeat "bookmark+-1" "\
Windows `Open' the Nth previous bookmark in the bookmark navlist.
See `bmkp-next-bookmark-w32-repeat'.

\(fn ARG)" t nil)

(autoload 'bmkp-toggle-autonamed-bookmark-set/delete "bookmark+-1" "\
If there is an autonamed bookmark at point, delete it, else create one.
The bookmark created has no region.  Its name is formatted according
to option `bmkp-autoname-bookmark-function'.

With a prefix arg, delete *ALL* autonamed bookmarks for this buffer.

Non-interactively, act at POSITION, not point.

\(fn POSITION &optional ALLP)" t nil)

(autoload 'bmkp-set-autonamed-bookmark "bookmark+-1" "\
Set an autonamed bookmark at point.
The bookmark created has no region.  Its name is formatted according
to option `bmkp-autoname-bookmark-function'.
Non-interactively, act at POSITION, not point.

\(fn POSITION &optional MSGP)" t nil)

(autoload 'bmkp-set-autonamed-bookmark-at-line "bookmark+-1" "\
Set an autonamed bookmark at the beginning of the given line NUMBER.

\(fn NUMBER)" t nil)

(autoload 'bmkp-set-autonamed-regexp-buffer "bookmark+-1" "\
Set autonamed bookmarks at matches for REGEXP in the buffer.

\(fn REGEXP &optional MSGP)" t nil)

(autoload 'bmkp-set-autonamed-regexp-region "bookmark+-1" "\
Set autonamed bookmarks at matches for REGEXP in the region.

\(fn REGEXP BEG END &optional MSGP)" t nil)

(autoload 'bmkp-delete-all-autonamed-for-this-buffer "bookmark+-1" "\
Delete all autonamed bookmarks for the current buffer.
To be deleted, a bookmark name must be an autonamed bookmark whose
buffer part names the current buffer.

\(fn)" t nil)

(autoload 'bmkp-delete-bookmarks "bookmark+-1" "\
Delete some bookmarks at point or all bookmarks in the buffer.
With no prefix argument, delete some bookmarks at point.
If there is more than one, require confirmation for each.

With a prefix argument, delete *ALL* bookmarks in the current buffer.

Non-interactively, delete at POSITION.
Optional arg ALIST is the alist of bookmarks.  It defaults to
`bookmark-alist'.

\(fn POSITION ALLP &optional ALIST)" t nil)

;;;***

;;;### (autoloads (bmkp-bmenu-mouse-3-menu bmkp-bmenu-describe-marked
;;;;;;  bmkp-bmenu-describe-this-bookmark bmkp-bmenu-describe-this+move-up
;;;;;;  bmkp-bmenu-describe-this+move-down bmkp-reverse-multi-sort-order
;;;;;;  bmkp-reverse-sort-order bmkp-bmenu-change-sort-order bmkp-bmenu-change-sort-order-repeat
;;;;;;  bmkp-bmenu-quit bmkp-bmenu-edit-tags bmkp-bmenu-edit-bookmark
;;;;;;  bmkp-define-tags-sort-command bmkp-bmenu-define-full-snapshot-command
;;;;;;  bmkp-bmenu-define-command bmkp-bmenu-define-jump-marked-command
;;;;;;  bmkp-bmenu-mode-status-help bmkp-bmenu-w32-open-select bmkp-bmenu-w32-open-with-mouse
;;;;;;  bmkp-bmenu-w32-open bmkp-bmenu-paste-replace-tags-for-marked
;;;;;;  bmkp-bmenu-paste-add-tags-to-marked bmkp-bmenu-paste-replace-tags
;;;;;;  bmkp-bmenu-paste-add-tags bmkp-bmenu-copy-tags bmkp-bmenu-unmark-bookmarks-tagged-not-all
;;;;;;  bmkp-bmenu-unmark-bookmarks-tagged-some bmkp-bmenu-unmark-bookmarks-tagged-none
;;;;;;  bmkp-bmenu-unmark-bookmarks-tagged-all bmkp-bmenu-unmark-bookmarks-tagged-regexp
;;;;;;  bmkp-bmenu-mark-bookmarks-tagged-not-all bmkp-bmenu-mark-bookmarks-tagged-some
;;;;;;  bmkp-bmenu-mark-bookmarks-tagged-none bmkp-bmenu-mark-bookmarks-tagged-all
;;;;;;  bmkp-bmenu-mark-bookmarks-tagged-regexp bmkp-bmenu-remove-tags-from-marked
;;;;;;  bmkp-bmenu-add-tags-to-marked bmkp-bmenu-remove-tags bmkp-bmenu-set-tag-value-for-marked
;;;;;;  bmkp-bmenu-set-tag-value bmkp-bmenu-add-tags bmkp-bmenu-remove-all-tags
;;;;;;  bmkp-bmenu-show-only-tagged bmkp-bmenu-query-replace-marked-bookmarks-regexp
;;;;;;  bmkp-bmenu-search-marked-bookmarks-regexp bmkp-bmenu-show-only-omitted
;;;;;;  bmkp-bmenu-unomit-marked bmkp-bmenu-omit-marked bmkp-bmenu-omit/unomit-marked
;;;;;;  bmkp-bmenu-omit bmkp-bmenu-make-sequence-from-marked bmkp-bmenu-delete-marked
;;;;;;  bmkp-bmenu-dired-marked bmkp-bmenu-toggle-marks bmkp-bmenu-mark-bookmarks-satisfying
;;;;;;  bmkp-bmenu-mark-w3m-bookmarks bmkp-bmenu-mark-url-bookmarks
;;;;;;  bmkp-bmenu-mark-specific-file-bookmarks bmkp-bmenu-mark-specific-buffer-bookmarks
;;;;;;  bmkp-bmenu-mark-region-bookmarks bmkp-bmenu-mark-non-file-bookmarks
;;;;;;  bmkp-bmenu-mark-man-bookmarks bmkp-bmenu-mark-info-bookmarks
;;;;;;  bmkp-bmenu-mark-gnus-bookmarks bmkp-bmenu-mark-file-bookmarks
;;;;;;  bmkp-bmenu-mark-dired-bookmarks bmkp-bmenu-mark-desktop-bookmarks
;;;;;;  bmkp-bmenu-mark-bookmark-file-bookmarks bmkp-bmenu-mark-autofile-bookmarks
;;;;;;  bmkp-bmenu-regexp-mark bmkp-bmenu-unmark-all bmkp-bmenu-mark-all
;;;;;;  bmkp-bmenu-toggle-show-only-marked bmkp-bmenu-toggle-show-only-unmarked
;;;;;;  bmkp-bmenu-filter-tags-incrementally bmkp-bmenu-filter-annotation-incrementally
;;;;;;  bmkp-bmenu-filter-file-name-incrementally bmkp-bmenu-filter-bookmark-name-incrementally
;;;;;;  bmkp-bmenu-refresh-menu-list bmkp-bmenu-show-all bmkp-bmenu-show-only-w3m-urls
;;;;;;  bmkp-bmenu-show-only-urls bmkp-bmenu-show-only-specific-file
;;;;;;  bmkp-bmenu-show-only-specific-buffer bmkp-bmenu-show-only-variable-lists
;;;;;;  bmkp-bmenu-show-only-regions bmkp-bmenu-show-only-man-pages
;;;;;;  bmkp-bmenu-show-only-info-nodes bmkp-bmenu-show-only-gnus
;;;;;;  bmkp-bmenu-show-only-non-files bmkp-bmenu-show-only-files
;;;;;;  bmkp-bmenu-show-only-dired bmkp-bmenu-show-only-desktops
;;;;;;  bmkp-bmenu-show-only-bookmark-files bmkp-bmenu-show-only-autonamed
;;;;;;  bmkp-bmenu-show-only-autofiles bookmark-bmenu-rename bookmark-bmenu-execute-deletions
;;;;;;  bookmark-bmenu-show-annotation bookmark-bmenu-other-window-with-mouse
;;;;;;  bookmark-bmenu-switch-other-window bookmark-bmenu-other-window
;;;;;;  bookmark-bmenu-this-window bookmark-bmenu-2-window bookmark-bmenu-1-window
;;;;;;  bookmark-bmenu-list bookmark-bmenu-delete bookmark-bmenu-unmark
;;;;;;  bookmark-bmenu-mark bmkp-bmenu-state-file bmkp-bmenu-commands-file
;;;;;;  bmkp-bmenu-omitted-bookmarks) "bookmark+-bmu" "site-lisp/bookmark+/bookmark+-bmu.el"
;;;;;;  (19982 16931))
;;; Generated autoloads from site-lisp/bookmark+/bookmark+-bmu.el

(defvar bmkp-bmenu-omitted-bookmarks nil "\
*List of names of omitted bookmarks.
They are generally not available for display in the bookmark list.
You can, however, use \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-show-only-omitted]' to see them.
You can then mark some of them and use `\\[bmkp-bmenu-omit/unomit-marked]'
 to make those that are marked available again for the bookmark list.")

(custom-autoload 'bmkp-bmenu-omitted-bookmarks "bookmark+-bmu" t)

(defvar bmkp-bmenu-commands-file (convert-standard-filename "~/.emacs-bmk-bmenu-commands.el") "\
*File for saving user-defined bookmark-list commands.
This must be an absolute file name (possibly containing `~') or nil
\(it is not expanded).

You can use `\\[bmkp-list-defuns-in-commands-file]' to list the
commands defined in the file and how many times each is defined.

NOTE: Each time you define a command using \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-define-command]', `\\[bmkp-bmenu-define-full-snapshot-command]', `\\[bmkp-bmenu-define-jump-marked-command], or `\\[bmkp-define-tags-sort-command]',
it is saved in the file.  The new definition is simply appended to the
file - old definitions of the same command are not overwritten.  So
you might want to clean up the file occasionally, to remove any old,
unused definitions.  This is especially advisable if you used `\\[bmkp-bmenu-define-full-snapshot-command]',
because such command definitions can be very large.")

(custom-autoload 'bmkp-bmenu-commands-file "bookmark+-bmu" t)

(defvar bmkp-bmenu-state-file (convert-standard-filename "~/.emacs-bmk-bmenu-state.el") "\
*File for saving `*Bookmark List*' state when you quit bookmark list.
This must be an absolute file name (possibly containing `~') or nil
\(it is not expanded).

The state is also saved when you quit Emacs, even if you don't quit
the bookmark list first (using \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-quit]').

Set this to nil if you do not want to restore the bookmark list as it
was the last time you used it.")

(custom-autoload 'bmkp-bmenu-state-file "bookmark+-bmu" t)

(autoload 'bookmark-bmenu-mark "bookmark+-bmu" "\
Mark the bookmark on this line, using mark `>'.

\(fn)" t nil)

(autoload 'bookmark-bmenu-unmark "bookmark+-bmu" "\
Unmark the bookmark on this line, then move down to the next.
Optional BACKUP means move up instead.

\(fn &optional BACKUP)" t nil)

(autoload 'bookmark-bmenu-delete "bookmark+-bmu" "\
Flag this bookmark for deletion, using mark `D'.
Use `\\<bookmark-bmenu-mode-map>\\[bookmark-bmenu-execute-deletions]' to carry out the deletions.

\(fn)" t nil)

(defalias 'list-bookmarks 'bookmark-bmenu-list)

(autoload 'bookmark-bmenu-list "bookmark+-bmu" "\
Display a list of existing bookmarks, in buffer `*Bookmark List*'.
The leftmost column of a bookmark entry shows `D' if the bookmark is
 flagged for deletion, or `>' if it is marked normally.
The second column shows `t' if the bookmark has tags.
The third  column shows `a' if the bookmark has an annotation.

The following faces are used for the list entries.
Use `customize-face' if you want to change the appearance.

 `bmkp-bad-bookmark', `bmkp-bookmark-list', `bmkp-buffer',
 `bmkp-desktop', `bmkp-function', `bmkp-gnus', `bmkp-info',
 `bmkp-local-directory', `bmkp-local-file-without-region',
 `bmkp-local-file-with-region', `bmkp-man', `bmkp-non-file',
 `bmkp-remote-file', `bmkp-sequence', `bmkp-su-or-sudo', `bmkp-url',
 `bmkp-variable-list'.

If option `bmkp-bmenu-state-file' is non-nil then the state of the
displayed bookmark-list is saved when you quit it, and it is restored
when you next use this command.  That saved state is not restored,
however, if it represents a different file from the current bookmark
file.

If you call this interactively when buffer `*Bookmark List*' exists,
that buffer is refreshed to show all current bookmarks, and any
markings are removed.  If you instead want to show the buffer in its
latest state then just do that: use `C-x b' or similar.  If you want
to refresh the displayed buffer, to show the latest state, reflecting
any additions, deletions, renamings, and so on, use \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-refresh-menu-list]'.

In Lisp code, non-nil optional argument FILTEREDP means the bookmark
list has been filtered, which means:
 * Use `bmkp-bmenu-title' not the default menu-list title.
 * Do not reset `bmkp-latest-bookmark-alist' to `bookmark-alist'.

\(fn &optional FILTEREDP)" t nil)

(autoload 'bookmark-bmenu-1-window "bookmark+-bmu" "\
Select this line's bookmark, alone, in full frame.
See `bookmark-jump' for info about the prefix arg.

\(fn &optional USE-REGION-P)" t nil)

(autoload 'bookmark-bmenu-2-window "bookmark+-bmu" "\
Select this line's bookmark, with previous buffer in second window.
See `bookmark-jump' for info about the prefix arg.

\(fn &optional USE-REGION-P)" t nil)

(autoload 'bookmark-bmenu-this-window "bookmark+-bmu" "\
Select this line's bookmark in this window.
See `bookmark-jump' for info about the prefix arg.

\(fn &optional USE-REGION-P)" t nil)

(autoload 'bookmark-bmenu-other-window "bookmark+-bmu" "\
Select this line's bookmark in other window.  Show `*Bookmark List*' still.
See `bookmark-jump' for info about the prefix arg.

\(fn &optional USE-REGION-P)" t nil)

(autoload 'bookmark-bmenu-switch-other-window "bookmark+-bmu" "\
Make the other window select this line's bookmark.
The current window remains selected.
See `bookmark-jump' for info about the prefix arg.

\(fn &optional USE-REGION-P)" t nil)

(autoload 'bookmark-bmenu-other-window-with-mouse "bookmark+-bmu" "\
Select clicked bookmark in other window.  Show `*Bookmark List*' still.

\(fn EVENT &optional USE-REGION-P)" t nil)

(autoload 'bookmark-bmenu-show-annotation "bookmark+-bmu" "\
Show the annotation for the current bookmark in another window.

\(fn MSGP)" t nil)

(autoload 'bookmark-bmenu-execute-deletions "bookmark+-bmu" "\
Delete (visible) bookmarks flagged `D'.
With a prefix argument, delete the bookmarks marked `>' instead, after
confirmation.

\(fn &optional MARKEDP)" t nil)

(autoload 'bookmark-bmenu-rename "bookmark+-bmu" "\
Rename bookmark on current line.  Prompts for a new name.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-autofiles "bookmark+-bmu" "\
Display (only) the autofile bookmarks.
This means bookmarks whose names are the same as their (non-directory)
file names.  But with a prefix arg you are prompted for a prefix that
each bookmark name must have.

\(fn &optional ARG)" t nil)

(autoload 'bmkp-bmenu-show-only-autonamed "bookmark+-bmu" "\
Display (only) the autonamed bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-bookmark-files "bookmark+-bmu" "\
Display (only) the bookmark-file bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-desktops "bookmark+-bmu" "\
Display (only) the desktop bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-dired "bookmark+-bmu" "\
Display (only) the Dired bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-files "bookmark+-bmu" "\
Display a list of file and directory bookmarks (only).
With a prefix argument, do not include remote files or directories.

\(fn ARG)" t nil)

(autoload 'bmkp-bmenu-show-only-non-files "bookmark+-bmu" "\
Display (only) the non-file bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-gnus "bookmark+-bmu" "\
Display (only) the Gnus bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-info-nodes "bookmark+-bmu" "\
Display (only) the Info bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-man-pages "bookmark+-bmu" "\
Display (only) the `man' page bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-regions "bookmark+-bmu" "\
Display (only) the bookmarks that record a region.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-variable-lists "bookmark+-bmu" "\
Display (only) the variable-list bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-specific-buffer "bookmark+-bmu" "\
Display (only) the bookmarks for BUFFER.
Interactively, read the BUFFER name.
If BUFFER is non-nil, set `bmkp-last-specific-buffer' to it.

\(fn &optional BUFFER)" t nil)

(autoload 'bmkp-bmenu-show-only-specific-file "bookmark+-bmu" "\
Display (only) the bookmarks for FILE, an absolute file name.
Interactively, read the FILE name.
If FILE is non-nil, set `bmkp-last-specific-file' to it.

\(fn &optional FILE)" t nil)

(autoload 'bmkp-bmenu-show-only-urls "bookmark+-bmu" "\
Display (only) the URL bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-w3m-urls "bookmark+-bmu" "\
Display (only) the W3M URL bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-all "bookmark+-bmu" "\
Show all bookmarks known to the bookmark list (aka \"menu list\").
Omitted bookmarks are not shown, however.
Also, this does not revert the bookmark list, to bring it up to date.
To revert the list, use `\\<bookmark-bmenu-mode-map>\\[bmkp-bmenu-refresh-menu-list]'.

\(fn)" t nil)

(autoload 'bmkp-bmenu-refresh-menu-list "bookmark+-bmu" "\
Refresh (revert) the bookmark list (\"menu list\").
This brings the displayed list up to date.  It does not change the
current filtering or sorting of the displayed list.

If you want setting a bookmark to refresh the list automatically, you
can use command `bmkp-toggle-bookmark-set-refreshes'.

\(fn)" t nil)

(autoload 'bmkp-bmenu-filter-bookmark-name-incrementally "bookmark+-bmu" "\
Incrementally filter bookmarks by bookmark name using a regexp.

\(fn)" t nil)

(autoload 'bmkp-bmenu-filter-file-name-incrementally "bookmark+-bmu" "\
Incrementally filter bookmarks by file name using a regexp.

\(fn)" t nil)

(autoload 'bmkp-bmenu-filter-annotation-incrementally "bookmark+-bmu" "\
Incrementally filter bookmarks by their annotations using a regexp.

\(fn)" t nil)

(autoload 'bmkp-bmenu-filter-tags-incrementally "bookmark+-bmu" "\
Incrementally filter bookmarks by tags using a regexp.

\(fn)" t nil)

(autoload 'bmkp-bmenu-toggle-show-only-unmarked "bookmark+-bmu" "\
Hide all marked bookmarks.  Repeat to toggle, showing all.

\(fn)" t nil)

(autoload 'bmkp-bmenu-toggle-show-only-marked "bookmark+-bmu" "\
Hide all unmarked bookmarks.  Repeat to toggle, showing all.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-all "bookmark+-bmu" "\
Mark all bookmarks, using mark `>'.

\(fn)" t nil)

(autoload 'bmkp-bmenu-unmark-all "bookmark+-bmu" "\
Remove a mark from each bookmark.
Hit the mark character (`>' or `D') to remove those marks,
 or hit `RET' to remove all marks (both `>' and `D').
With a prefix arg, you are queried to unmark each marked bookmark.
Use `\\[help-command]' during querying for help.

\(fn MARK &optional ARG)" t nil)

(autoload 'bmkp-bmenu-regexp-mark "bookmark+-bmu" "\
Mark bookmarks that match REGEXP.
The entire bookmark line is tested: bookmark name and possibly file name.

\(fn REGEXP)" t nil)

(autoload 'bmkp-bmenu-mark-autofile-bookmarks "bookmark+-bmu" "\
Mark autofile bookmarks: those whose names are the same as their files.
With a prefix arg you are prompted for a prefix that each bookmark
name must have.

\(fn &optional ARG)" t nil)

(autoload 'bmkp-bmenu-mark-bookmark-file-bookmarks "bookmark+-bmu" "\
Mark bookmark-file bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-desktop-bookmarks "bookmark+-bmu" "\
Mark desktop bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-dired-bookmarks "bookmark+-bmu" "\
Mark Dired bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-file-bookmarks "bookmark+-bmu" "\
Mark file bookmarks.
With a prefix argument, do not mark remote files or directories.

\(fn ARG)" t nil)

(autoload 'bmkp-bmenu-mark-gnus-bookmarks "bookmark+-bmu" "\
Mark Gnus bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-info-bookmarks "bookmark+-bmu" "\
Mark Info bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-man-bookmarks "bookmark+-bmu" "\
Mark `man' page bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-non-file-bookmarks "bookmark+-bmu" "\
Mark non-file bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-region-bookmarks "bookmark+-bmu" "\
Mark bookmarks that record a region.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-specific-buffer-bookmarks "bookmark+-bmu" "\
Mark bookmarks for BUFFER.
Interactively, read the name of the buffer.
If BUFFER is non-nil, set `bmkp-last-specific-buffer' to it.

\(fn &optional BUFFER)" t nil)

(autoload 'bmkp-bmenu-mark-specific-file-bookmarks "bookmark+-bmu" "\
Mark bookmarks for FILE, an absolute file name.
Interactively, read the file name.
If FILE is non-nil, set `bmkp-last-specific-file' to it.

\(fn &optional FILE)" t nil)

(autoload 'bmkp-bmenu-mark-url-bookmarks "bookmark+-bmu" "\
Mark URL bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-w3m-bookmarks "bookmark+-bmu" "\
Mark W3M (URL) bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mark-bookmarks-satisfying "bookmark+-bmu" "\
Mark bookmarks that satisfy predicate PRED.
If you use this interactively, you are responsible for entering a
symbol that names a unnary predicate.  The function you provide is not
checked - it is simply applied to each bookmark to test it.

\(fn PRED)" t nil)

(autoload 'bmkp-bmenu-toggle-marks "bookmark+-bmu" "\
Toggle marks: Unmark all marked bookmarks; mark all unmarked bookmarks.
This affects only the `>' mark, not the `D' flag.

\(fn)" t nil)

(autoload 'bmkp-bmenu-dired-marked "bookmark+-bmu" "\
Dired in another window for the marked file and directory bookmarks.

Absolute file names are used for the entries in the Dired buffer.
The only entries are for the marked files and directories.  These can
be located anywhere.  (In Emacs versions prior to release 23.2, remote
bookmarks are ignored, because of Emacs bug #5478.)

You are prompted for the Dired buffer name.  The `default-directory'
of the buffer is the same as that of buffer `*Bookmark List*'.

\(fn DIRBUFNAME)" t nil)

(autoload 'bmkp-bmenu-delete-marked "bookmark+-bmu" "\
Delete all (visible) bookmarks that are marked `>', after confirmation.

\(fn)" t nil)

(autoload 'bmkp-bmenu-make-sequence-from-marked "bookmark+-bmu" "\
Create or update a sequence bookmark from the visible marked bookmarks.
The bookmarks that are currently marked are recorded as a sequence, in
their current order in buffer `*Bookmark List*'.
When you \"jump\" to the sequence bookmark, the bookmarks in the
sequence are processed in order.

By default, omit the marked bookmarks, after creating the sequence.
With a prefix arg, do not omit them.

If a bookmark with the specified name already exists, it is
overwritten.  If a sequence bookmark with the name already exists,
then you are prompted whether to add the marked bookmarks to the
beginning of the existing sequence (or simply replace it).

Note that another existing sequence bookmark can be marked, and thus
included in the sequence bookmark created or updated.  That is, you
can include other sequences within a sequence bookmark.

Returns the bookmark (internal record) created or updated.

\(fn BOOKMARK-NAME &optional DONT-OMIT-P)" t nil)

(autoload 'bmkp-bmenu-omit "bookmark+-bmu" "\
Omit this bookmark.

\(fn)" t nil)

(autoload 'bmkp-bmenu-omit/unomit-marked "bookmark+-bmu" "\
Omit all marked bookmarks or, if showing only omitted ones, unomit.

\(fn)" t nil)

(autoload 'bmkp-bmenu-omit-marked "bookmark+-bmu" "\
Omit all marked bookmarks.
They will henceforth be invisible to the bookmark list.
You can, however, use \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-show-only-omitted]' to see them.
You can then mark some of them and use `\\[bmkp-bmenu-omit/unomit-marked]' to make those marked
 available again for the bookmark list.

\(fn)" t nil)

(autoload 'bmkp-bmenu-unomit-marked "bookmark+-bmu" "\
Remove all marked bookmarks from the list of omitted bookmarks.
They will henceforth be available for display in the bookmark list.
\(In order to see and then mark omitted bookmarks you must use \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-show-only-omitted]'.)

\(fn)" t nil)

(autoload 'bmkp-bmenu-show-only-omitted "bookmark+-bmu" "\
Show only the omitted bookmarks.
You can then mark some of them and use `bmkp-bmenu-unomit-marked' to
 make those that are marked available again for the bookmark list.

\(fn)" t nil)

(autoload 'bmkp-bmenu-search-marked-bookmarks-regexp "bookmark+-bmu" "\
Search the marked file bookmarks, in their current order, for REGEXP.
Use `\\[tags-loop-continue]' to advance among the search hits.
Marked directory and non-file bookmarks are ignored.

\(fn REGEXP)" t nil)

(autoload 'bmkp-bmenu-query-replace-marked-bookmarks-regexp "bookmark+-bmu" "\
`query-replace-regexp' FROM with TO, for all marked file bookmarks.
DELIMITED (prefix arg) means replace only word-delimited matches.
If you exit (`\\[keyboard-quit]', `RET' or `q'), you can use `\\[tags-loop-continue]' to resume where
you left off.

\(fn FROM TO &optional DELIMITED)" t nil)

(autoload 'bmkp-bmenu-show-only-tagged "bookmark+-bmu" "\
Display (only) the bookmarks that have tags.

\(fn)" t nil)

(autoload 'bmkp-bmenu-remove-all-tags "bookmark+-bmu" "\
Remove all tags from this bookmark.
Interactively, you are required to confirm.

\(fn &optional MUST-CONFIRM-P)" t nil)

(autoload 'bmkp-bmenu-add-tags "bookmark+-bmu" "\
Add some tags to this bookmark.

\(fn)" t nil)

(autoload 'bmkp-bmenu-set-tag-value "bookmark+-bmu" "\
Set the value of one of this bookmark's tags.

\(fn)" t nil)

(autoload 'bmkp-bmenu-set-tag-value-for-marked "bookmark+-bmu" "\
Set the value of TAG to VALUE, for each of the marked bookmarks.
If any of the bookmarks has no tag named TAG, then add one with VALUE.

\(fn TAG VALUE &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-remove-tags "bookmark+-bmu" "\
Remove some tags from this bookmark.

\(fn &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-add-tags-to-marked "bookmark+-bmu" "\
Add TAGS to each of the marked bookmarks.
TAGS is a list of strings.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag, but you are not limited to
choosing existing tags.

\(fn TAGS &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-remove-tags-from-marked "bookmark+-bmu" "\
Remove TAGS from each of the marked bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag.

\(fn TAGS &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-mark-bookmarks-tagged-regexp "bookmark+-bmu" "\
Mark bookmarks any of whose tags match REGEXP.
With a prefix arg, mark all that are tagged but have no matching tags.

\(fn REGEXP &optional NOTP)" t nil)

(autoload 'bmkp-bmenu-mark-bookmarks-tagged-all "bookmark+-bmu" "\
Mark all visible bookmarks that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all (i.e., at least one tag).

With a prefix arg, mark all that are *not* tagged with *any* TAGS.

\(fn TAGS &optional NONE-P MSGP)" t nil)

(autoload 'bmkp-bmenu-mark-bookmarks-tagged-none "bookmark+-bmu" "\
Mark all visible bookmarks that are not tagged with *any* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.

With a prefix arg, mark all that are tagged with *each* tag in TAGS.

\(fn TAGS &optional ALLP MSGP)" t nil)

(autoload 'bmkp-bmenu-mark-bookmarks-tagged-some "bookmark+-bmu" "\
Mark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all.

With a prefix arg, mark all that are *not* tagged with *all* TAGS.

Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag.

\(fn TAGS &optional SOMENOTP MSGP)" t nil)

(autoload 'bmkp-bmenu-mark-bookmarks-tagged-not-all "bookmark+-bmu" "\
Mark all visible bookmarks that are *not* tagged with *all* TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.

With a prefix arg, mark all that are tagged with *some* tag in TAGS.

\(fn TAGS &optional SOMEP MSGP)" t nil)

(autoload 'bmkp-bmenu-unmark-bookmarks-tagged-regexp "bookmark+-bmu" "\
Unmark bookmarks any of whose tags match REGEXP.
With a prefix arg, mark all that are tagged but have no matching tags.

\(fn REGEXP &optional NOTP)" t nil)

(autoload 'bmkp-bmenu-unmark-bookmarks-tagged-all "bookmark+-bmu" "\
Unmark all visible bookmarks that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
any tags at all.

With a prefix arg, unmark all that are *not* tagged with *any* TAGS.

\(fn TAGS &optional NONE-P MSGP)" t nil)

(autoload 'bmkp-bmenu-unmark-bookmarks-tagged-none "bookmark+-bmu" "\
Unmark all visible bookmarks that are *not* tagged with *any* TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
no tags at all.

With a prefix arg, unmark all that are tagged with *each* tag in TAGS.

\(fn TAGS &optional ALLP MSGP)" t nil)

(autoload 'bmkp-bmenu-unmark-bookmarks-tagged-some "bookmark+-bmu" "\
Unmark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
any tags at all.

With a prefix arg, unmark all that are *not* tagged with *all* TAGS.

\(fn TAGS &optional SOMENOTP MSGP)" t nil)

(autoload 'bmkp-bmenu-unmark-bookmarks-tagged-not-all "bookmark+-bmu" "\
Unmark all visible bookmarks that are *not* tagged with *all* TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
no tags at all.

With a prefix arg, unmark all that are tagged with *some* TAGS.

\(fn TAGS &optional SOMEP MSGP)" t nil)

(autoload 'bmkp-bmenu-copy-tags "bookmark+-bmu" "\
Copy tags from this bookmark, so you can paste them to another bookmark.

\(fn &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-paste-add-tags "bookmark+-bmu" "\
Add tags to this bookmark that were copied from another bookmark.

\(fn &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-paste-replace-tags "bookmark+-bmu" "\
Replace tags for this bookmark with those copied from another bookmark.

\(fn &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-paste-add-tags-to-marked "bookmark+-bmu" "\
Add tags that were copied from another bookmark to the marked bookmarks.

\(fn &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-paste-replace-tags-for-marked "bookmark+-bmu" "\
Replace tags for the marked bookmarks with tags copied previously.

\(fn &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-w32-open "bookmark+-bmu" "\
Use `w32-browser' to open this bookmark.

\(fn)" t nil)

(autoload 'bmkp-bmenu-w32-open-with-mouse "bookmark+-bmu" "\
Use `w32-browser' to open the bookmark clicked.

\(fn EVENT)" t nil)

(autoload 'bmkp-bmenu-w32-open-select "bookmark+-bmu" "\
Use `w32-browser' to open this bookmark and all marked bookmarks.

\(fn)" t nil)

(autoload 'bmkp-bmenu-mode-status-help "bookmark+-bmu" "\
`describe-mode' + current status of `*Bookmark List*' + face legend.

\(fn)" t nil)

(autoload 'bmkp-bmenu-define-jump-marked-command "bookmark+-bmu" "\
Define a command to jump to a bookmark that is one of those now marked.
The bookmarks marked now will be those that are completion candidates
for the command (but omitted bookmarks are excluded).
Save the command definition in `bmkp-bmenu-commands-file'.

\(fn)" t nil)

(autoload 'bmkp-bmenu-define-command "bookmark+-bmu" "\
Define a command to use the current sort order, filter, and omit list.
Prompt for the command name.  Save the command definition in
`bmkp-bmenu-commands-file'.

The current sort order, filter function, omit list, and title for
buffer `*Bookmark List*' are encapsulated as part of the command.
Use the command at any time to restore them.

\(fn)" t nil)

(autoload 'bmkp-bmenu-define-full-snapshot-command "bookmark+-bmu" "\
Define a command to restore the current bookmark-list state.
Prompt for the command name.  Save the command definition in
`bmkp-bmenu-commands-file'.

Be aware that the command definition can be quite large, since it
copies the current bookmark list and accessory lists (hidden
bookmarks, marked bookmarks, etc.).  For a lighter weight command, use
`bmkp-bmenu-define-full-snapshot-command' instead.  That records only
the omit list and the sort & filter information.

\(fn)" t nil)

(autoload 'bmkp-define-tags-sort-command "bookmark+-bmu" "\
Define a command to sort bookmarks in the bookmark list by tags.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.

The new command sorts first by the first tag in TAGS, then by the
second, and so on.

Besides sorting for these specific tags, any bookmark that has a tag
sorts before one that has no tags.  Otherwise, sorting is by bookmark
name, alphabetically.

The name of the new command is `bmkp-bmenu-sort-' followed by the
specified tags, in order, separated by hyphens (`-').  E.g., for TAGS
\(\"alpha\" \"beta\"), the name is `bmkp-bmenu-sort-alpha-beta'.

\(fn TAGS &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-edit-bookmark "bookmark+-bmu" "\
Edit the bookmark under the cursor: its name and file name.
With a prefix argument, edit the complete bookmark record (the
internal, Lisp form).

\(fn &optional INTERNALP)" t nil)

(autoload 'bmkp-bmenu-edit-tags "bookmark+-bmu" "\
Edit the tags of the bookmark under the cursor.
The edited value must be a list each of whose elements is either a
string or a cons whose key is a string.

\(fn)" t nil)

(autoload 'bmkp-bmenu-quit "bookmark+-bmu" "\
Quit the bookmark list (aka \"menu list\").
If `bmkp-bmenu-state-file' is non-nil, then save the state, to be
restored the next time the bookmark list is shown.  Otherwise, reset
the internal lists that record menu-list markings.

\(fn)" t nil)

(autoload 'bmkp-bmenu-change-sort-order-repeat "bookmark+-bmu" "\
Cycle to the next sort order.
With a prefix arg, reverse current sort order.
This is a repeatable version of `bmkp-bmenu-change-sort-order'.

\(fn ARG)" t nil)

(autoload 'bmkp-bmenu-change-sort-order "bookmark+-bmu" "\
Cycle to the next sort order.
With a prefix arg, reverse the current sort order.

\(fn &optional ARG)" t nil)

(autoload 'bmkp-reverse-sort-order "bookmark+-bmu" "\
Reverse the current bookmark sort order.
If you combine this with \\<bookmark-bmenu-mode-map>`\\[bmkp-reverse-multi-sort-order]', then see the doc for that command.

\(fn)" t nil)

(autoload 'bmkp-reverse-multi-sort-order "bookmark+-bmu" "\
Reverse the application of multi-sorting predicates.
These are the PRED predicates described for option
`bmkp-sort-comparer'.

This reverses the order in which the predicates are tried, and it
also complements the truth value returned by each predicate.

For example, if the list of multi-sorting predicates is (p1 p2 p3),
then the predicates are tried in the order: p3, p2, p1.  And if a
predicate returns true, `(t)', then the effect is as if it returned
false, `(nil)', and vice versa.

The use of multi-sorting predicates tends to group bookmarks, with the
first predicate corresponding to the first bookmark group etc.

The effect of \\<bookmark-bmenu-mode-map>`\\[bmkp-reverse-multi-sort-order]' is roughly as follows:

 - without also `\\[bmkp-reverse-sort-order]', it reverses the bookmark order in each group

 - combined with `\\[bmkp-reverse-sort-order]', it reverses the order of the bookmark
   groups, but not the bookmarks within a group

This is a rough description.  The actual behavior can be complex,
because of how each predicate is defined.  If this description helps
you, fine.  If not, just experiment and see what happens. ;-)

Remember that ordinary `\\[bmkp-reverse-sort-order]' reversal on its own is straightforward.
If you find `\\[bmkp-reverse-multi-sort-order]' confusing or not helpful, then do not use it.

\(fn)" t nil)

(autoload 'bmkp-bmenu-describe-this+move-down "bookmark+-bmu" "\
Describe bookmark of current line, then move down to the next bookmark.
With a prefix argument, show the internal definition of the bookmark.

\(fn &optional DEFN)" t nil)

(autoload 'bmkp-bmenu-describe-this+move-up "bookmark+-bmu" "\
Describe bookmark of current line, then move down to the next bookmark.
With a prefix argument, show the internal definition of the bookmark.

\(fn &optional DEFN)" t nil)

(autoload 'bmkp-bmenu-describe-this-bookmark "bookmark+-bmu" "\
Describe bookmark of current line.
With a prefix argument, show the internal definition of the bookmark.

\(fn &optional DEFN)" t nil)

(autoload 'bmkp-bmenu-describe-marked "bookmark+-bmu" "\
Describe the marked bookmarks.
With a prefix argument, show the internal definitions.

\(fn &optional DEFN)" t nil)

(autoload 'bmkp-bmenu-mouse-3-menu "bookmark+-bmu" "\
Pop-up menu on `mouse-3' for a bookmark listed in `*Bookmark List*'.

\(fn EVENT)" t nil)

;;;***

;;;### (autoloads (bmkp-previous-lighted-this-buffer-repeat bmkp-next-lighted-this-buffer-repeat
;;;;;;  bmkp-previous-lighted-this-buffer bmkp-next-lighted-this-buffer
;;;;;;  bmkp-cycle-lighted-this-buffer-other-window bmkp-cycle-lighted-this-buffer
;;;;;;  bmkp-light-non-autonamed-this-buffer bmkp-light-autonamed-this-buffer
;;;;;;  bmkp-light-bookmarks-in-region bmkp-light-this-buffer bmkp-light-navlist-bookmarks
;;;;;;  bmkp-light-bookmarks bmkp-light-bookmark-this-buffer bmkp-light-bookmark
;;;;;;  bmkp-set-lighting-for-this-buffer bmkp-set-lighting-for-buffer
;;;;;;  bmkp-set-lighting-for-bookmark bmkp-unlight-this-buffer bmkp-unlight-non-autonamed-this-buffer
;;;;;;  bmkp-unlight-autonamed-this-buffer bmkp-unlight-bookmarks
;;;;;;  bmkp-unlight-bookmark-this-buffer bmkp-unlight-bookmark-here
;;;;;;  bmkp-unlight-bookmark bmkp-lighted-jump-other-window bmkp-lighted-jump
;;;;;;  bmkp-bookmarks-lighted-at-point bmkp-bmenu-set-lighting-for-marked
;;;;;;  bmkp-bmenu-set-lighting bmkp-bmenu-unlight-marked bmkp-bmenu-unlight
;;;;;;  bmkp-bmenu-light-marked bmkp-bmenu-light bmkp-bmenu-show-only-lighted
;;;;;;  bmkp-light-threshold bmkp-light-style-non-autonamed bmkp-light-style-autonamed
;;;;;;  bmkp-light-priorities bmkp-auto-light-when-set bmkp-auto-light-when-jump
;;;;;;  bmkp-auto-light-relocate-when-jump-flag) "bookmark+-lit"
;;;;;;  "site-lisp/bookmark+/bookmark+-lit.el" (19862 26951))
;;; Generated autoloads from site-lisp/bookmark+/bookmark+-lit.el

(defvar bmkp-auto-light-relocate-when-jump-flag t "\
*Non-nil means highlight the relocated, instead of the recorded, position.
This has an effect only when the highlighting style for the bookmark
is `point'.")

(custom-autoload 'bmkp-auto-light-relocate-when-jump-flag "bookmark+-lit" t)

(defvar bmkp-auto-light-when-jump nil "\
*Which bookmarks to automatically highlight when jumped to.")

(custom-autoload 'bmkp-auto-light-when-jump "bookmark+-lit" t)

(defvar bmkp-auto-light-when-set nil "\
*Which bookmarks to automatically highlight when set.")

(custom-autoload 'bmkp-auto-light-when-set "bookmark+-lit" t)

(defvar bmkp-light-priorities '((bmkp-autonamed-overlays . 160) (bmkp-non-autonamed-overlays . 150)) "\
*Priorities of bookmark highlighting overlay types.
As an idea, `ediff' uses 100+, `isearch' uses 1001.")

(custom-autoload 'bmkp-light-priorities "bookmark+-lit" t)

(defvar bmkp-light-style-autonamed (if (not (fboundp 'fringe-columns)) 'line 'line+lfringe) "\
*Default highlight style for autonamed bookmarks.")

(custom-autoload 'bmkp-light-style-autonamed "bookmark+-lit" t)

(defvar bmkp-light-style-non-autonamed (if (not (fboundp 'fringe-columns)) 'line 'line+rfringe) "\
*Default highlight style for non-autonamed bookmarks.")

(custom-autoload 'bmkp-light-style-non-autonamed "bookmark+-lit" t)

(defvar bmkp-light-threshold 100000 "\
*Maximum number of bookmarks to highlight.")

(custom-autoload 'bmkp-light-threshold "bookmark+-lit" t)

(autoload 'bmkp-bmenu-show-only-lighted "bookmark+-lit" "\
Display a list of highlighted bookmarks (only).

\(fn)" t nil)

(autoload 'bmkp-bmenu-light "bookmark+-lit" "\
Highlight the location of this line's bookmark.

\(fn)" t nil)

(autoload 'bmkp-bmenu-light-marked "bookmark+-lit" "\
Highlight the marked bookmarks.

\(fn &optional PARG MSGP)" t nil)

(autoload 'bmkp-bmenu-unlight "bookmark+-lit" "\
Highlight the location of this line's bookmark.

\(fn)" t nil)

(autoload 'bmkp-bmenu-unlight-marked "bookmark+-lit" "\
Unhighlight the marked bookmarks.

\(fn &optional PARG MSGP)" t nil)

(autoload 'bmkp-bmenu-set-lighting "bookmark+-lit" "\
Set the `lighting' property for this line's bookmark.
You are prompted for the highlight style, face, and condition (when).

\(fn STYLE FACE WHEN &optional MSGP)" t nil)

(autoload 'bmkp-bmenu-set-lighting-for-marked "bookmark+-lit" "\
Set the `lighting' property for the marked bookmarks.
You are prompted for the highlight style, face, and condition (when).

\(fn STYLE FACE WHEN &optional MSGP)" t nil)

(autoload 'bmkp-bookmarks-lighted-at-point "bookmark+-lit" "\
Return a list of the bookmarks highlighted at point.
With no prefix arg, return the bookmark names.
With a prefix arg, return the full bookmark data.
Interactively, display the info.
Non-interactively, use the bookmarks at POSITION (default: point).

\(fn &optional POSITION FULLP MSGP)" t nil)

(autoload 'bmkp-lighted-jump "bookmark+-lit" "\
Jump to a highlighted bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-lighted-jump-other-window "bookmark+-lit" "\
Jump to a highlighted bookmark in another window.
See `bmkp-lighted-jump'.

\(fn BOOKMARK-NAME &optional USE-REGION-P)" t nil)

(autoload 'bmkp-unlight-bookmark "bookmark+-lit" "\
Unhighlight BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.

\(fn BOOKMARK &optional NOERRORP MSGP)" t nil)

(autoload 'bmkp-unlight-bookmark-here "bookmark+-lit" "\
Unhighlight a bookmark at point or the same line (in that order).

\(fn &optional NOERRORP MSGP)" t nil)

(autoload 'bmkp-unlight-bookmark-this-buffer "bookmark+-lit" "\
Unhighlight a BOOKMARK in this buffer.
BOOKMARK is a bookmark name or a bookmark record.
With a prefix arg, choose from all bookmarks, not just those in this
buffer.

\(fn BOOKMARK &optional NOERRORP MSGP)" t nil)

(autoload 'bmkp-unlight-bookmarks "bookmark+-lit" "\
Unhighlight bookmarks.
A prefix argument determines which bookmarks to unhighlight:
 none    - Current buffer, all bookmarks.
 >= 0    - Current buffer, autonamed bookmarks only.
 < 0     - Current buffer, non-autonamed bookmarks only.
 C-u     - All buffers (all bookmarks).

\(fn &optional OVERLAYS-SYMBOLS THIS-BUFFER-P MSGP)" t nil)

(autoload 'bmkp-unlight-autonamed-this-buffer "bookmark+-lit" "\
Unhighlight autonamed bookmarks.
No prefix arg: unhighlight them only in the current buffer.
Prefix arg, unhighlight them everywhere.

\(fn &optional EVERYWHEREP)" t nil)

(autoload 'bmkp-unlight-non-autonamed-this-buffer "bookmark+-lit" "\
Unhighlight non-autonamed bookmarks.
No prefix arg: unhighlight them only in the current buffer.
Prefix arg, unhighlight them everywhere.

\(fn &optional EVERYWHEREP)" t nil)

(autoload 'bmkp-unlight-this-buffer "bookmark+-lit" "\
Unhighlight all bookmarks in the current buffer.

\(fn)" t nil)

(autoload 'bmkp-set-lighting-for-bookmark "bookmark+-lit" "\
Set the `lighting' property for bookmark BOOKMARK-NAME.
You are prompted for the bookmark, highlight style, face, and condition.
With a prefix argument, do not highlight now.

Non-interactively:
STYLE, FACE, and WHEN are as for a bookmark's `lighting' property
 entries, or nil if no such entry.
Non-nil MSGP means display a highlighting progress message.
Non-nil LIGHT-NOW-P means apply the highlighting now.

\(fn BOOKMARK-NAME STYLE FACE WHEN &optional MSGP LIGHT-NOW-P)" t nil)

(autoload 'bmkp-set-lighting-for-buffer "bookmark+-lit" "\
Set the `lighting' property for each of the bookmarks for BUFFER.
You are prompted for the highlight style, face, and condition (when).
With a prefix argument, do not highlight now.

Non-interactively:
STYLE, FACE, and WHEN are as for a bookmark's `lighting' property
 entries, or nil if no such entry.
Non-nil MSGP means display a highlighting progress message.
Non-nil LIGHT-NOW-P means apply the highlighting now.

\(fn BUFFER STYLE FACE WHEN &optional MSGP LIGHT-NOW-P)" t nil)

(autoload 'bmkp-set-lighting-for-this-buffer "bookmark+-lit" "\
Set the `lighting' property for each of the bookmarks for this buffer.
You are prompted for the highlight style, face, and condition (when).
With a prefix argument, do not highlight now.

Non-interactively:
STYLE, FACE, and WHEN are as for a bookmark's `lighting' property
 entries, or nil if no such entry.
Non-nil MSGP means display a highlighting progress message.
Non-nil LIGHT-NOW-P means apply the highlighting now.

\(fn STYLE FACE WHEN &optional MSGP LIGHT-NOW-P)" t nil)

(autoload 'bmkp-light-bookmark "bookmark+-lit" "\
Highlight BOOKMARK.
With a prefix arg you are prompted for the style and/or face to use:
 Plain prefix arg (`C-u'): prompt for both style and face.
 Numeric non-negative arg: prompt for face.
 Numeric negative arg: prompt for style.

Non-interactively:
 BOOKMARK is a bookmark name or a bookmark record.
 STYLE and FACE override the defaults.
 POINT-P non-nil means highlight point rather than the recorded
  bookmark `position.

\(fn BOOKMARK &optional STYLE FACE MSGP POINTP)" t nil)

(autoload 'bmkp-light-bookmark-this-buffer "bookmark+-lit" "\
Highlight a BOOKMARK in the current buffer.
With a prefix arg you are prompted for the style and/or face to use:
 Plain prefix arg (`C-u'): prompt for both style and face.
 Numeric non-negative arg: prompt for face.
 Numeric negative arg: prompt for style.
See `bmkp-light-boookmark' for argument descriptions.

\(fn BOOKMARK &optional STYLE FACE MSGP)" t nil)

(autoload 'bmkp-light-bookmarks "bookmark+-lit" "\
Highlight bookmarks.
A prefix argument determines which bookmarks to highlight:
 none    - Current buffer, all bookmarks.
 = 0     - Current buffer, highlighted bookmarks only (rehighlight).
 > 0     - Current buffer, autonamed bookmarks only.
 < 0     - Current buffer, non-autonamed bookmarks only.
 C-u     - All buffers (all bookmarks) - after confirmation.
 C-u C-u - Navlist (all bookmarks).

Non-interactively, ALIST is the alist of bookmarks to highlight.

\(fn &optional ALIST OVERLAYS-SYMBOLS MSGP)" t nil)

(autoload 'bmkp-light-navlist-bookmarks "bookmark+-lit" "\
Highlight bookmarks in the navigation list.
No prefix arg:   all bookmarks.
Prefix arg >= 0: autonamed bookmarks only.
Prefix arg < 0:  non-autonamed bookmarks only.

\(fn &optional OVERLAYS-SYMBOLS MSGP)" t nil)

(autoload 'bmkp-light-this-buffer "bookmark+-lit" "\
Highlight bookmarks in the current buffer.
No prefix arg:   all bookmarks.
Prefix arg >= 0: autonamed bookmarks only.
Prefix arg < 0:  non-autonamed bookmarks only.

\(fn &optional OVERLAYS-SYMBOLS MSGP)" t nil)

(autoload 'bmkp-light-bookmarks-in-region "bookmark+-lit" "\
Highlight bookmarks in the region.
No prefix arg:   all bookmarks.
Prefix arg >= 0: autonamed bookmarks only.
Prefix arg < 0:  non-autonamed bookmarks only.

\(fn START END &optional OVERLAYS-SYMBOLS MSGP)" t nil)

(autoload 'bmkp-light-autonamed-this-buffer "bookmark+-lit" "\
Highlight all autonamed bookmarks.

\(fn &optional MSGP)" t nil)

(autoload 'bmkp-light-non-autonamed-this-buffer "bookmark+-lit" "\
Highlight all non-autonamed bookmarks.

\(fn &optional MSGP)" t nil)

(autoload 'bmkp-cycle-lighted-this-buffer "bookmark+-lit" "\
Cycle through highlighted bookmarks in this buffer by INCREMENT.
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value 

To change the sort order, you can filter the `*Bookmark List*' to show
only highlighted bookmarks for this buffer, sort the bookmarks there,
and use `\\[bmkp-choose-navlist-from-bookmark-list]', choosing `CURRENT *Bookmark List*' as the
navigation list.

Then you can cycle the bookmarks using `bookmark-cycle'
\(`\\[bmkp-next-bookmark-repeat]' etc.), instead of `bookmark-cycle-lighted-this-buffer'.

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist.

\(fn INCREMENT &optional OTHER-WINDOW STARTOVERP)" t nil)

(autoload 'bmkp-cycle-lighted-this-buffer-other-window "bookmark+-lit" "\
Same as `bmkp-cycle-lighted-this-buffer' but uses another window.

\(fn INCREMENT &optional STARTOVERP)" t nil)

(autoload 'bmkp-next-lighted-this-buffer "bookmark+-lit" "\
Jump to the Nth-next highlighted bookmark in the current buffer.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle-lighted-this-buffer'.

\(fn N &optional STARTOVERP)" t nil)

(autoload 'bmkp-previous-lighted-this-buffer "bookmark+-lit" "\
Jump to the Nth-previous highlighted bookmark in the current buffer.
See `bmkp-next-lighted-this-buffer'.

\(fn N &optional STARTOVERP)" t nil)

(autoload 'bmkp-next-lighted-this-buffer-repeat "bookmark+-lit" "\
Jump to the Nth next highlighted bookmark in the current buffer.
This is a repeatable version of `bmkp-next-bookmark-this-buffer'.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one (and no repeat).

\(fn ARG)" t nil)

(autoload 'bmkp-previous-lighted-this-buffer-repeat "bookmark+-lit" "\
Jump to the Nth previous highlighted bookmark in the current buffer.
See `bmkp-next-lighted-this-buffer-repeat'.

\(fn ARG)" t nil)

;;;***

;;;### (autoloads (bmkp-menu-bar-make-toggle bmkp-define-file-sort-predicate
;;;;;;  bmkp-define-sort-command bmkp-define-next+prev-cycle-commands
;;;;;;  bmkp-define-cycle-command) "bookmark+-mac" "site-lisp/bookmark+/bookmark+-mac.el"
;;;;;;  (19862 27002))
;;; Generated autoloads from site-lisp/bookmark+/bookmark+-mac.el

(autoload 'bmkp-define-cycle-command "bookmark+-mac" "\
Define a cycling command for bookmarks of type TYPE.
Non-nil OTHERP means define a command that cycles in another window.

\(fn TYPE &optional OTHERP)" nil (quote macro))

(autoload 'bmkp-define-next+prev-cycle-commands "bookmark+-mac" "\
Define `next' and `previous' commands for bookmarks of type TYPE.

\(fn TYPE)" nil (quote macro))

(autoload 'bmkp-define-sort-command "bookmark+-mac" "\
Define a command to sort bookmarks in the bookmark list by SORT-ORDER.
SORT-ORDER is a short string or symbol describing the sorting method.
Examples: \"by last access time\", \"by bookmark name\".

The new command is named by replacing any spaces in SORT-ORDER with
hyphens (`-') and then adding the prefix `bmkp-bmenu-sort-'.  Example:
`bmkp-bmenu-sort-by-bookmark-name', for SORT-ORDER `by bookmark name'.

COMPARER compares two bookmarks, returning non-nil if and only if the
first bookmark sorts before the second.  It must be acceptable as a
value of `bmkp-sort-comparer'.  That is, it is either nil, a
predicate, or a list ((PRED...) FINAL-PRED).  See the doc for
`bmkp-sort-comparer'.

DOC-STRING is the doc string of the new command.

\(fn SORT-ORDER COMPARER DOC-STRING)" nil (quote macro))

(autoload 'bmkp-define-file-sort-predicate "bookmark+-mac" "\
Define a predicate for sorting bookmarks by file attribute ATT-NB.
See function `file-attributes' for the meanings of the various file
attribute numbers.

String attribute values sort alphabetically; numerical values sort
numerically; nil sorts before t.

For ATT-NB 0 (file type), a file sorts before a symlink, which sorts
before a directory.

For ATT-NB 2 or 3 (uid, gid), a numerical value sorts before a string
value.

A bookmark that has file attributes sorts before a bookmark that does
not.  A file bookmark sorts before a non-file bookmark.  Only local
files are tested for attributes - remote-file bookmarks are treated
here like non-file bookmarks.

\(fn ATT-NB)" nil (quote macro))

(autoload 'bmkp-menu-bar-make-toggle "bookmark+-mac" "\
Return a valid `menu-bar-make-toggle' call in Emacs 20 or later.
NAME is the name of the toggle command to define.
VARIABLE is the variable to set.
DOC is the menu-item name.
MESSAGE is the toggle message, minus status.
HELP is `:help' string.
BODY is the function body to use.  If present, it is responsible for
setting the variable and displaying a status message (not MESSAGE).

\(fn NAME VARIABLE DOC MESSAGE HELP &rest BODY)" nil (quote macro))

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

;;;### (autoloads (cl-info) "cl-info" "cl-info.el" (20042 54464))
;;; Generated autoloads from cl-info.el

(autoload 'cl-info "cl-info" "\
Not documented

\(fn SYMBOL-NAME)" t nil)

;;;***

;;;### (autoloads (turn-on-cldoc-mode cldoc-mode cldoc-minor-mode-string
;;;;;;  cldoc-mode) "cldoc" "site-lisp/lisp/cldoc.el" (18429 49075))
;;; Generated autoloads from site-lisp/lisp/cldoc.el

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

;;;### (autoloads (col-highlight-flash col-highlight-set-interval
;;;;;;  col-highlight-toggle-when-idle column-highlight-mode col-highlight-period
;;;;;;  col-highlight-vline-face-flag column-highlight) "col-highlight"
;;;;;;  "site-lisp/drewadams/col-highlight.el" (19746 39549))
;;; Generated autoloads from site-lisp/drewadams/col-highlight.el

(let ((loads (get 'column-highlight 'custom-loads))) (if (member '"col-highlight" loads) nil (put 'column-highlight 'custom-loads (cons '"col-highlight" loads))))

(defvar col-highlight-vline-face-flag t "\
*Non-nil means `column-highlight-mode' uses `col-highlight-face'.
nil means that it uses `vline-face'.")

(custom-autoload 'col-highlight-vline-face-flag "col-highlight" t)

(defvar col-highlight-period 1 "\
*Number of seconds to highlight the current column.")

(custom-autoload 'col-highlight-period "col-highlight" t)

(defface col-highlight '((t (:background "SlateGray3"))) "\
*Face for current-column highlighting by `column-highlight-mode'.
Not used if `col-highlight-vline-face-flag' is nil." :group (quote column-highlight) :group (quote faces))

(defvar column-highlight-mode nil "\
Non-nil if Column-Highlight mode is enabled.
See the command `column-highlight-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `column-highlight-mode'.")

(custom-autoload 'column-highlight-mode "col-highlight" nil)

(autoload 'column-highlight-mode "col-highlight" "\
Toggle highlighting the current column.
With ARG, turn column highlighting on if and only if ARG is positive.

Column-Highlight mode uses the functions
`col-highlight-unhighlight' and `col-highlight-highlight'
on `pre-command-hook' and `post-command-hook'.

\(fn &optional ARG)" t nil)

(defalias 'toggle-highlight-column-when-idle 'col-highlight-toggle-when-idle)

(autoload 'col-highlight-toggle-when-idle "col-highlight" "\
Turn on or off highlighting the current column when Emacs is idle.
With prefix argument, turn on if ARG > 0; else turn off.

\(fn &optional ARG)" t nil)

(autoload 'col-highlight-set-interval "col-highlight" "\
Set wait until highlight current column when Emacs is idle.
Whenever Emacs is idle for this many seconds, the current column
will be highlighted in the face that is the value of variable
`col-highlight-face'.

To turn on or off automatically highlighting the current column
when Emacs is idle, use `\\[toggle-highlight-column-when-idle].

\(fn SECS)" t nil)

(defalias 'flash-column-highlight 'col-highlight-flash)

(autoload 'col-highlight-flash "col-highlight" "\
Highlight the current column for `col-highlight-period' seconds.
With a prefix argument, highlight for that many seconds.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (color-theme-initialize color-theme-submit color-theme-install
;;;;;;  color-theme-compare color-theme-make-snapshot color-theme-analyze-defun
;;;;;;  color-theme-print color-theme-install-at-point-for-current-frame
;;;;;;  color-theme-install-at-mouse color-theme-describe color-theme-select)
;;;;;;  "color-theme" "site-lisp/color-theme/color-theme.el" (17529
;;;;;;  41105))
;;; Generated autoloads from site-lisp/color-theme/color-theme.el

(autoload 'color-theme-select "color-theme" "\
Displays a special buffer for selecting and installing a color theme.
With optional prefix ARG, this buffer will include color theme libraries
as well.  A color theme library is in itself not complete, it must be
used as part of another color theme to be useful.  Thus, color theme
libraries are mainly useful for color theme authors.

\(fn &optional ARG)" t nil)

(autoload 'color-theme-describe "color-theme" "\
Describe color theme listed at point.
This shows the documentation of the value of text-property color-theme
at point.  The text-property color-theme should be a color theme
function.  See `color-themes'.

\(fn)" t nil)

(autoload 'color-theme-install-at-mouse "color-theme" "\
Install color theme clicked upon using the mouse.
First argument EVENT is used to set point.  Then
`color-theme-install-at-point' is called.

\(fn EVENT)" t nil)

(autoload 'color-theme-install-at-point-for-current-frame "color-theme" "\
Install color theme at point for current frame only.
Binds `color-theme-is-global' to nil and calls
`color-theme-install-at-point'.

\(fn)" t nil)

(autoload 'color-theme-print "color-theme" "\
Print the current color theme function.

You can contribute this function to <URL:news:gnu.emacs.sources> or
paste it into your .emacs file and call it.  That should recreate all
the settings necessary for your color theme.

Example:

    (require 'color-theme)
    (defun my-color-theme ()
      \"Color theme by Alex Schroeder, created 2000-05-17.\"
      (interactive)
      (color-theme-install
       '(...
	 ...
	 ...)))
    (my-color-theme)

If you want to use a specific color theme function, you can call the
color theme function in your .emacs directly.

Example:

    (require 'color-theme)
    (color-theme-gnome2)

\(fn &optional BUF)" t nil)

(autoload 'color-theme-analyze-defun "color-theme" "\
Once you have a color-theme printed, check for missing faces.
This is used by maintainers who receive a color-theme submission
and want to make sure it follows the guidelines by the color-theme
author.

\(fn)" t nil)

(autoload 'color-theme-make-snapshot "color-theme" "\
Return the definition of the current color-theme.
The function returned will recreate the color-theme in use at the moment.

\(fn)" nil nil)

(autoload 'color-theme-compare "color-theme" "\
Compare two color themes.
This will print the differences between installing THEME-A and
installing THEME-B.  Note that the order is important: If a face is
defined in THEME-A and not in THEME-B, then this will not show up as a
difference, because there is no reset before installing THEME-B.  If a
face is defined in THEME-B and not in THEME-A, then this will show up as
a difference.

\(fn THEME-A THEME-B)" t nil)

(autoload 'color-theme-install "color-theme" "\
Install a color theme defined by frame parameters, variables and faces.

The theme is installed for all present and future frames; any missing
faces are created.  See `color-theme-install-faces'.

THEME is a color theme definition.  See below for more information.

If you want to install a color theme from your .emacs, use the output
generated by `color-theme-print'.  This produces color theme function
which you can copy to your .emacs.

A color theme definition is a list:
\([FUNCTION] FRAME-PARAMETERS VARIABLE-SETTINGS FACE-DEFINITIONS)

FUNCTION is the color theme function which called `color-theme-install'.
This is no longer used.  There was a time when this package supported
automatic factoring of color themes.  This has been abandoned.

FRAME-PARAMETERS is an alist of frame parameters.  These are installed
with `color-theme-install-frame-params'.  These are installed last such
that any changes to the default face can be changed by the frame
parameters.

VARIABLE-DEFINITIONS is an alist of variable settings.  These are
installed with `color-theme-install-variables'.

FACE-DEFINITIONS is an alist of face definitions.  These are installed
with `color-theme-install-faces'.

If `color-theme-is-cumulative' is nil, a color theme will undo face and
frame-parameter settings of previous color themes.

\(fn THEME)" nil nil)

(autoload 'color-theme-submit "color-theme" "\
Submit your color-theme to the maintainer.

\(fn)" t nil)

(autoload 'color-theme-initialize "color-theme" "\
Initialize the color theme package by loading color-theme-libraries.

\(fn)" t nil)

;;;***

;;;### (autoloads nil "column-marker" "site-lisp/column-marker.el"
;;;;;;  (18429 49075))
;;; Generated autoloads from site-lisp/column-marker.el

(autoload 'column-marker-1 "column-marker" "\
Highlight a column." t)

;;;***

;;;### (autoloads (company-mode) "company" "site-lisp/company/company.el"
;;;;;;  (19333 2704))
;;; Generated autoloads from site-lisp/company/company.el

(autoload 'company-mode "company" "\
\"complete anything\"; in in-buffer completion framework.
Completion starts automatically, depending on the values
`company-idle-delay' and `company-minimum-prefix-length'.

Completion can be controlled with the commands:
`company-complete-common', `company-complete-selection', `company-complete',
`company-select-next', `company-select-previous'.  If these commands are
called before `company-idle-delay', completion will also start.

Completions can be searched with `company-search-candidates' or
`company-filter-candidates'.  These can be used while completion is
inactive, as well.

The completion data is retrieved using `company-backends' and displayed using
`company-frontends'.  If you want to start a specific back-end, call it
interactively or use `company-begin-backend'.

regular keymap (`company-mode-map'):

\\{company-mode-map}
keymap during active completions (`company-active-map'):

\\{company-active-map}

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (company-abbrev) "company-abbrev" "site-lisp/company/company-abbrev.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-abbrev.el

(autoload 'company-abbrev "company-abbrev" "\
A `company-mode' completion back-end for abbrev.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-css) "company-css" "site-lisp/company/company-css.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-css.el

(autoload 'company-css "company-css" "\
A `company-mode' completion back-end for `css-mode'.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-dabbrev) "company-dabbrev" "site-lisp/company/company-dabbrev.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-dabbrev.el

(autoload 'company-dabbrev "company-dabbrev" "\
A dabbrev-like `company-mode' completion back-end.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-dabbrev-code) "company-dabbrev-code" "site-lisp/company/company-dabbrev-code.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-dabbrev-code.el

(autoload 'company-dabbrev-code "company-dabbrev-code" "\
A dabbrev-like `company-mode' back-end for code.
The back-end looks for all symbols in the current buffer that aren't in
comments or strings.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-elisp) "company-elisp" "site-lisp/company/company-elisp.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-elisp.el

(autoload 'company-elisp "company-elisp" "\
A `company-mode' completion back-end for `emacs-lisp-mode'.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-etags) "company-etags" "site-lisp/company/company-etags.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-etags.el

(autoload 'company-etags "company-etags" "\
A `company-mode' completion back-end for etags.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-files) "company-files" "site-lisp/company/company-files.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-files.el

(autoload 'company-files "company-files" "\
a `company-mode' completion back-end existing file names.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-gtags) "company-gtags" "site-lisp/company/company-gtags.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-gtags.el

(autoload 'company-gtags "company-gtags" "\
A `company-mode' completion back-end for GNU Global.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-ispell) "company-ispell" "site-lisp/company/company-ispell.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-ispell.el

(autoload 'company-ispell "company-ispell" "\
A `company-mode' completion back-end using ispell.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-keywords) "company-keywords" "site-lisp/company/company-keywords.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-keywords.el

(autoload 'company-keywords "company-keywords" "\
A `company-mode' back-end for programming language keywords.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-nxml) "company-nxml" "site-lisp/company/company-nxml.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-nxml.el

(autoload 'company-nxml "company-nxml" "\
A `company-mode' completion back-end for `nxml-mode'.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-oddmuse) "company-oddmuse" "site-lisp/company/company-oddmuse.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-oddmuse.el

(autoload 'company-oddmuse "company-oddmuse" "\
A `company-mode' completion back-end for `oddmuse-mode'.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-pysmell) "company-pysmell" "site-lisp/company/company-pysmell.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-pysmell.el

(autoload 'company-pysmell "company-pysmell" "\
A `company-mode' completion back-end for pysmell.
This requires pysmell.el and pymacs.el.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-semantic) "company-semantic" "site-lisp/company/company-semantic.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-semantic.el

(autoload 'company-semantic "company-semantic" "\
A `company-mode' completion back-end using CEDET Semantic.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-tempo) "company-tempo" "site-lisp/company/company-tempo.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-tempo.el

(autoload 'company-tempo "company-tempo" "\
A `company-mode' completion back-end for tempo.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (company-xcode) "company-xcode" "site-lisp/company/company-xcode.el"
;;;;;;  (19332 59877))
;;; Generated autoloads from site-lisp/company/company-xcode.el

(autoload 'company-xcode "company-xcode" "\
A `company-mode' completion back-end for Xcode projects.

\(fn COMMAND &optional ARG &rest IGNORED)" t nil)

;;;***

;;;### (autoloads (compile-mode-summary) "compile+" "site-lisp/drewadams/compile+.el"
;;;;;;  (19802 51197))
;;; Generated autoloads from site-lisp/drewadams/compile+.el

(autoload 'compile-mode-summary "compile+" "\
Display brief help message for Compile Mode.

\(fn)" t nil)

;;;***

;;;### (autoloads (compilation-message-face) "compile-" "site-lisp/drewadams/compile-.el"
;;;;;;  (19814 57638))
;;; Generated autoloads from site-lisp/drewadams/compile-.el

(defvar compilation-message-face nil "\
*Face name to use for whole messages.
Faces `compilation-error-face', `compilation-warning-face',
`compilation-info-face', `compilation-line-face' and
`compilation-column-face' get prepended to this, when applicable.")

(custom-autoload 'compilation-message-face "compile-" t)

(defface compilation-mouseover '((t (:underline t))) "\
*Face used to highlight text the mouse is over." :group (quote compilation) :group (quote font-lock-highlighting-faces))

;;;***

;;;### (autoloads (context-mode) "context" "site-lisp/auctex/context.el"
;;;;;;  (19318 46167))
;;; Generated autoloads from site-lisp/auctex/context.el

(defalias 'ConTeXt-mode 'context-mode)

(autoload 'context-mode "context" "\
Major mode in AUCTeX for editing ConTeXt files.

Special commands:
\\{ConTeXt-mode-map}

Entering `context-mode' calls the value of `text-mode-hook',
then the value of `TeX-mode-hook', and then the value
of context-mode-hook.

\(fn)" t nil)

;;;***

;;;### (autoloads (context-en-mode) "context-en" "site-lisp/auctex/context-en.el"
;;;;;;  (18541 18440))
;;; Generated autoloads from site-lisp/auctex/context-en.el

(autoload 'context-en-mode "context-en" "\
Major mode for editing files for ConTeXt using its english interface.

Special commands:
\\{ConTeXt-mode-map}

Entering `context-mode' calls the value of `text-mode-hook',
then the value of TeX-mode-hook, and then the value
of context-mode-hook.

\(fn)" t nil)

;;;***

;;;### (autoloads (context-nl-mode) "context-nl" "site-lisp/auctex/context-nl.el"
;;;;;;  (18489 3127))
;;; Generated autoloads from site-lisp/auctex/context-nl.el

(autoload 'context-nl-mode "context-nl" "\
Major mode for editing files for ConTeXt using its dutch interface.

Special commands:
\\{ConTeXt-mode-map}

Entering `context-mode' calls the value of `text-mode-hook',
then the value of TeX-mode-hook, and then the value
of context-mode-hook.

\(fn)" t nil)

;;;***

;;;### (autoloads (crosshairs-unhighlight crosshairs-highlight crosshairs
;;;;;;  crosshairs-flash crosshairs-toggle-when-idle crosshairs-mode
;;;;;;  crosshairs-vline-same-face-flag crosshairs-overlay-priority
;;;;;;  crosshairs) "crosshairs" "site-lisp/drewadams/crosshairs.el"
;;;;;;  (19746 41427))
;;; Generated autoloads from site-lisp/drewadams/crosshairs.el

(let ((loads (get 'crosshairs 'custom-loads))) (if (member '"crosshairs" loads) nil (put 'crosshairs 'custom-loads (cons '"crosshairs" loads))))

(defvar crosshairs-overlay-priority nil "\
*Priority to use for overlay `global-hl-line-overlay'.")

(custom-autoload 'crosshairs-overlay-priority "crosshairs" t)

(defvar crosshairs-vline-same-face-flag t "\
*Non-nil means use face `hl-line' for column highlighting also.
nil means highlight the column according to the value of `vline-style'
and face `vline'.")

(custom-autoload 'crosshairs-vline-same-face-flag "crosshairs" t)

(defvar crosshairs-mode nil "\
Non-nil if Crosshairs mode is enabled.
See the command `crosshairs-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `crosshairs-mode'.")

(custom-autoload 'crosshairs-mode "crosshairs" nil)

(autoload 'crosshairs-mode "crosshairs" "\
Toggle highlighting the current line and column.
With ARG, turn highlighting on if and only if ARG is positive.

\(fn &optional ARG)" t nil)

(defalias 'toggle-crosshairs-when-idle 'crosshairs-toggle-when-idle)

(autoload 'crosshairs-toggle-when-idle "crosshairs" "\
Toggle highlighting the current line and column when Emacs is idle.
With prefix argument, turn on if ARG > 0; else turn off.
You can use commands `col-highlight-set-interval' and
`hl-line-when-idle-interval' to change the idle times.

\(fn &optional ARG)" t nil)

(defalias 'flash-crosshairs 'crosshairs-flash)

(autoload 'crosshairs-flash "crosshairs" "\
Highlight the current line and column temporarily.
Highlight the line for `hl-line-flash-show-period' and the column for
`column-show-period' seconds.  With prefix argument SECONDS, highlight
both for SECONDS seconds.

\(fn &optional SECONDS)" t nil)

(autoload 'crosshairs "crosshairs" "\
Highlight current position with crosshairs.
With no prefix arg, highlighting turns off at the next command.
With a prefix arg, highlighting stays on until you toggle it off using
`crosshairs-mode'.

\(fn &optional MODALP)" t nil)

(autoload 'crosshairs-highlight "crosshairs" "\
Echo current position and highlight it with crosshairs.
If optional arg MODE is `line-only', then highlight only the line.
If optional arg MODE is `col-only', then highlight only the column.
 Interactively:
  A non-negative prefix argument uses MODE `line-only'.
  A negative prefix argument uses MODE `col-only'.

Optional arg NOMSG non-nil means show no message.

If the current buffer is not the same as the value of `orig-buff',
then indicate the buffer, as well as the position.  Variable
`orig-buff' is not bound here; if you want to take advantage of this
feature in your code, then bind it.

Return current position as a marker.

\(fn &optional MODE NOMSG)" t nil)

(autoload 'crosshairs-unhighlight "crosshairs" "\
Turn off crosshairs highlighting of current position.
Optional arg nil means do nothing if this event is a frame switch.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (curchg-change-cursor-when-idle-interval curchg-toggle-cursor-type-when-idle
;;;;;;  curchg-set-cursor-type curchg-overwrite/read-only-cursor-type
;;;;;;  curchg-input-method-cursor-color curchg-idle-cursor-type
;;;;;;  curchg-default-cursor-type curchg-default-cursor-color curchg-change-cursor-on-overwrite/read-only-flag
;;;;;;  curchg-change-cursor-on-input-method-flag) "cursor-chg" "site-lisp/drewadams/cursor-chg.el"
;;;;;;  (19746 41610))
;;; Generated autoloads from site-lisp/drewadams/cursor-chg.el

(defvar curchg-change-cursor-on-input-method-flag t "\
*Non-nil means to use a different cursor when using an input method.")

(custom-autoload 'curchg-change-cursor-on-input-method-flag "cursor-chg" t)

(defvar curchg-change-cursor-on-overwrite/read-only-flag t "\
*Non-nil means use a different cursor for overwrite mode or read-only.")

(custom-autoload 'curchg-change-cursor-on-overwrite/read-only-flag "cursor-chg" t)

(defvar curchg-default-cursor-color (or (cdr (assq 'cursor-color default-frame-alist)) "Red") "\
*Default text cursor color for non-special frames.")

(custom-autoload 'curchg-default-cursor-color "cursor-chg" t)

(defvar curchg-default-cursor-type 'bar "\
*Default text cursor type.")

(custom-autoload 'curchg-default-cursor-type "cursor-chg" t)

(defvar curchg-idle-cursor-type 'box "\
*Text cursor type when Emacs is idle.")

(custom-autoload 'curchg-idle-cursor-type "cursor-chg" t)

(defvar curchg-input-method-cursor-color "Orange" "\
*Default cursor color if using an input method.
This has no effect if `curchg-change-cursor-on-input-method-flag' is nil.")

(custom-autoload 'curchg-input-method-cursor-color "cursor-chg" t)

(defvar curchg-overwrite/read-only-cursor-type 'box "\
*Default text cursor type for overwrite mode or read-only buffer.
This applies only to non-special frames.  This has no effect if
`curchg-change-cursor-on-overwrite/read-only-flag' is nil.")

(custom-autoload 'curchg-overwrite/read-only-cursor-type "cursor-chg" t)

(autoload 'curchg-set-cursor-type "cursor-chg" "\
Set the cursor type of the selected frame to CURSOR-TYPE.
When called interactively, prompt for the type to use.
To get the frame's current cursor type, use `frame-parameters'.

\(fn CURSOR-TYPE)" t nil)

(defalias 'toggle-cursor-type-when-idle 'curchg-toggle-cursor-type-when-idle)

(autoload 'curchg-toggle-cursor-type-when-idle "cursor-chg" "\
Turn on or off automatically changing cursor type when Emacs is idle.
When on, use `curchg-idle-cursor-type' whenever Emacs is idle.
With prefix argument, turn on if ARG > 0; else turn off.

\(fn &optional ARG)" t nil)

(autoload 'curchg-change-cursor-when-idle-interval "cursor-chg" "\
Set wait until automatically change cursor type when Emacs is idle.
Whenever Emacs is idle for this many seconds, the cursor type will
change to `curchg-idle-cursor-type'.

To turn on or off automatically changing the cursor type when idle,
use `\\[toggle-cursor-type-when-idle].

\(fn SECS)" t nil)

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

;;;### (autoloads (font-latex-setup) "font-latex" "site-lisp/auctex/font-latex.el"
;;;;;;  (19254 11585))
;;; Generated autoloads from site-lisp/auctex/font-latex.el

(autoload 'font-latex-setup "font-latex" "\
Setup this buffer for LaTeX font-lock.  Usually called from a hook.

\(fn)" nil nil)

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
;;;;;;  gist-region) "gist" "site-lisp/gist/gist.el" (20032 31679))
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

;;;### (autoloads (gnus-harvest-install gnus-harvest-find-address
;;;;;;  gnus-harvest-addresses) "gnus-harvest" "site-lisp/gnus-harvest/gnus-harvest.el"
;;;;;;  (20045 54265))
;;; Generated autoloads from site-lisp/gnus-harvest/gnus-harvest.el

(autoload 'gnus-harvest-addresses "gnus-harvest" "\
Harvest and remember the addresses in the current article buffer.

\(fn)" nil nil)

(autoload 'gnus-harvest-find-address "gnus-harvest" "\
Not documented

\(fn)" t nil)

(autoload 'gnus-harvest-install "gnus-harvest" "\
Not documented

\(fn &rest FEATURES)" nil nil)

;;;***

;;;### (autoloads (grepp-toggle-comments grepp-remove-comments grepp-choose-grep-buffer
;;;;;;  grepp-new-grep-buffer grep grepp-default-regexp-fn grepp-default-comment-line-regexp)
;;;;;;  "grep+" "site-lisp/drewadams/grep+.el" (19814 59175))
;;; Generated autoloads from site-lisp/drewadams/grep+.el

(defvar grepp-default-comment-line-regexp ":[0-9]+: *;" "\
*Default regexp for a comment line, for use in `grepp-remove-comments'.
The default value matches lines that begin with a Lisp comment.")

(custom-autoload 'grepp-default-comment-line-regexp "grep+" t)

(defvar grepp-default-regexp-fn (if (fboundp 'symbol-name-nearest-point) 'symbol-name-nearest-point 'word-at-point) "\
*Function of 0 args called to provide default search regexp to \\[grep].
Some reasonable choices: `word-nearest-point',
`symbol-name-nearest-point', `sexp-nearest-point'.

This is ignored if Transient Mark mode is on and the region is active
and non-empty.  In that case, the quoted (\") region text is used as
the default regexp.

If `grepp-default-regexp-fn' is nil and no prefix arg is given to
`grep', then no defaulting is done.

Otherwise, if the value is not a function, then function
`grepp-default-regexp-fn' does the defaulting.")

(custom-autoload 'grepp-default-regexp-fn "grep+" t)

(autoload 'grep "grep+" "\
Run `grep', with user-specified args, and collect output in a buffer.
COMMAND-ARGS are the user-specified arguments.
While `grep' runs asynchronously, you can use the
\\[next-error] command (M-x next-error), or \\<grep-mode-map>\\[compile-goto-error]
in the *grep* output buffer, to find the text that `grep' hits refer to.

This command uses a special history list for its COMMAND-ARGS, so you can
easily repeat a grep command.

The text (regexp) to find is defaulted as follows:

- If Transient Mark mode is on and the region is active and nonempty,
  then the double-quoted region text is used.  (If the region contains
  double-quotes (\"), then you will need to escape them by hand.)

- If option `grepp-default-regexp-fn' is a function, then it is called
  to return the default regexp.

- If `grepp-default-regexp-fn' is nil and no prefix arg is provided,
  then no default regexp is used.

If a prefix arg is provided, then the default text is substituted
into the last grep command in the grep command history (or into
`grep-command' if that history list is empty).  That is, the same
command options and files to search are used as the last time.

If specified, optional second arg HIGHLIGHT-REGEXP is the regexp to
temporarily highlight in visited source lines.

\(fn COMMAND-ARGS &optional HIGHLIGHT-REGEXP)" t nil)

(defalias 'new-grep-buffer 'grepp-new-grep-buffer)

(autoload 'grepp-new-grep-buffer "grep+" "\
Rename current grep buffer and switch to new buffer *grep*.
Current buffer must be a grep buffer.  It is renamed to *grep*<N>.

\(fn)" t nil)

(defalias 'choose-grep-buffer 'grepp-choose-grep-buffer)

(autoload 'grepp-choose-grep-buffer "grep+" "\
Switch to a grep buffer.

\(fn BUF)" t nil)

(defalias 'remove-grep-comments 'grepp-remove-comments)

(autoload 'grepp-remove-comments "grep+" "\
Remove lines that are completely commented out.
With a prefix argument, you are prompted for the regexp used to match
 commented lines.  The default value is 
 `grepp-default-comment-line-regexp'.
With no prefix argument, this default value is used as the regexp.

You can use command `grep-toggle-comments' to toggle automatic removal
of commented lines.

Note: This simply removes lines that begin with the regexp you
provide.  It does not, in general, remove multi-line comments.  Use it
to remove C++ comments that start with //, but not multi-line comments
between /* and */.

\(fn &optional READ-REGEXP-P)" t nil)

(defalias 'toggle-grep-comments 'grepp-toggle-comments)

(autoload 'grepp-toggle-comments "grep+" "\
Toggle removal of commented lines in grep output.

\(fn)" t nil)

;;;***

;;;### (autoloads (gtags-mode) "gtags" "site-lisp/gtags.el" (20032
;;;;;;  41059))
;;; Generated autoloads from site-lisp/gtags.el

(autoload 'gtags-mode "gtags" "\
Toggle Gtags mode, a minor mode for browsing source code using GLOBAL.

Specify the root directory of project.
	\\[gtags-visit-rootdir]
Input tag name and move to the definition.
	\\[gtags-find-tag]
Input tag name and move to the definition in other window.
        \\[gtags-find-tag-other-window]
Input tag name and move to the referenced point.
	\\[gtags-find-rtag]
Input symbol and move to the locations.
	\\[gtags-find-symbol]
Input pattern, search with grep(1) and move to the locations.
	\\[gtags-find-with-grep]
Input pattern, search with idutils(1) and move to the locations.
	\\[gtags-find-with-idutils]
Input pattern and move to the top of the file.
	\\[gtags-find-file]
Input pattern and show the list of definitions of the file.
	\\[gtags-parse-file]
Get the expression as a tagname around here and move there.
	\\[gtags-find-tag-from-here]
Display current screen on hypertext browser.
	\\[gtags-display-browser]
Get the expression as a tagname around here and move there.
	\\[gtags-find-tag-by-event]
Move to previous point on the stack.
	\\[gtags-pop-stack]

Key definitions:
\\{gtags-mode-map}
Turning on Gtags mode calls the value of the variable `gtags-mode-hook'
with no args, if that value is non-nil.

\(fn &optional FORCES)" t nil)

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

;;;### (autoloads (hide-region-unhide hide-region-hide) "hide-region"
;;;;;;  "site-lisp/hide-region.el" (20026 111))
;;; Generated autoloads from site-lisp/hide-region.el

(autoload 'hide-region-hide "hide-region" "\
Hides a region by making an invisible overlay over it and save the
overlay on the hide-region-overlays \"ring\"

\(fn)" t nil)

(autoload 'hide-region-unhide "hide-region" "\
Unhide a region at a time, starting with the last one hidden and
deleting the overlay from the hide-region-overlays \"ring\".

\(fn)" t nil)

;;;***

;;;### (autoloads (highlight-parentheses-mode) "highlight-parentheses"
;;;;;;  "site-lisp/highlight-parentheses.el" (18882 10149))
;;; Generated autoloads from site-lisp/highlight-parentheses.el

(autoload 'highlight-parentheses-mode "highlight-parentheses" "\
Minor mode to highlight the surrounding parentheses.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (hl-line-flash hl-line-when-idle-interval hl-line-toggle-when-idle
;;;;;;  hl-line-inhibit-highlighting-for-modes hl-line-flash-show-period)
;;;;;;  "hl-line+" "site-lisp/drewadams/hl-line+.el" (19814 59509))
;;; Generated autoloads from site-lisp/drewadams/hl-line+.el

(defface hl-line '((t (:background "SlateGray3"))) "\
*Face to use for `hl-line-face'." :group (quote hl-line))

(defvar hl-line-flash-show-period 1 "\
*Number of seconds for `hl-line-flash' to highlight the line.")

(custom-autoload 'hl-line-flash-show-period "hl-line+" t)

(defvar hl-line-inhibit-highlighting-for-modes nil "\
*Modes where highlighting is inhibited for `hl-line-highlight-now'.
A list of `major-mode' values (symbols).")

(custom-autoload 'hl-line-inhibit-highlighting-for-modes "hl-line+" t)

(defalias 'toggle-hl-line-when-idle 'hl-line-toggle-when-idle)

(autoload 'hl-line-toggle-when-idle "hl-line+" "\
Turn on or off using `global-hl-line-mode' when Emacs is idle.
When on, use `global-hl-line-mode' whenever Emacs is idle.
With prefix argument, turn on if ARG > 0; else turn off.

\(fn &optional ARG)" t nil)

(autoload 'hl-line-when-idle-interval "hl-line+" "\
Set wait until using `global-hl-line-mode' when Emacs is idle.
Whenever Emacs is idle for this many seconds, `global-hl-line-mode'
will be turned on.

To turn on or off using `global-hl-line-mode' when idle,
use `\\[toggle-hl-line-when-idle].

\(fn SECS)" t nil)

(defalias 'flash-line-highlight 'hl-line-flash)

(autoload 'hl-line-flash "hl-line+" "\
Highlight the current line for `hl-line-flash-show-period' seconds.
With a prefix argument, highlight for that many seconds.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (ido-completing-read ido-read-directory-name ido-read-file-name
;;;;;;  ido-read-buffer ido-dired ido-insert-file ido-write-file
;;;;;;  ido-find-file-other-frame ido-display-file ido-find-file-read-only-other-frame
;;;;;;  ido-find-file-read-only-other-window ido-find-file-read-only
;;;;;;  ido-find-alternate-file ido-find-file-other-window ido-find-file
;;;;;;  ido-find-file-in-dir ido-switch-buffer-other-frame ido-insert-buffer
;;;;;;  ido-kill-buffer ido-display-buffer ido-switch-buffer-other-window
;;;;;;  ido-switch-buffer ido-mode ido-mode) "ido" "ido.el" (20032
;;;;;;  25852))
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
Toggle ido mode on or off.
With ARG, turn ido-mode on if arg is positive, off otherwise.
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
PREDICATE and INHERIT-INPUT-METHOD is currently ignored; it is included
 to be compatible with `completing-read'.
If REQUIRE-MATCH is non-nil, the user is not allowed to exit unless
 the input is (or completes to) an element of CHOICES or is null.
 If the input is null, `ido-completing-read' returns DEF, or an empty
 string if DEF is nil, regardless of the value of REQUIRE-MATCH.
If INITIAL-INPUT is non-nil, insert it in the minibuffer initially,
 with point positioned at the end.
HIST, if non-nil, specifies a history list.
DEF, if non-nil, is the default value.

\(fn PROMPT CHOICES &optional _PREDICATE REQUIRE-MATCH INITIAL-INPUT HIST DEF _INHERIT-INPUT-METHOD)" nil nil)

;;;***

;;;### (autoloads (imenu-add-defs-to-menubar imenu-toggle-sort) "imenu+"
;;;;;;  "site-lisp/drewadams/imenu+.el" (19935 51692))
;;; Generated autoloads from site-lisp/drewadams/imenu+.el

(defalias 'toggle-imenu-sort 'imenu-toggle-sort)

(autoload 'imenu-toggle-sort "imenu+" "\
Toggle imenu between sorting menus and not.
Non-nil prefix FORCE-P => Sort iff FORCE-P >= 0.

\(fn FORCE-P)" t nil)

(autoload 'imenu-add-defs-to-menubar "imenu+" "\
Add \"Defs\" imenu entry to menu bar for current local keymap.
See `imenu' for more information.

\(fn)" t nil)

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

;;;### (autoloads (Info-merge-subnodes Info-goto-emacs-key-command-node
;;;;;;  Info-goto-emacs-command-node Info-subtree-separator Info-display-node-header-fn
;;;;;;  Info-fontify-reference-items-flag Info-fontify-single-quote-flag
;;;;;;  Info-fontify-quotations-flag Info-fit-frame-flag Info-Plus)
;;;;;;  "info+" "site-lisp/drewadams/info+.el" (19814 60231))
;;; Generated autoloads from site-lisp/drewadams/info+.el

(let ((loads (get 'Info-Plus 'custom-loads))) (if (member '"info+" loads) nil (put 'Info-Plus 'custom-loads (cons '"info+" loads))))

(defface info-file '((((background dark)) (:foreground "Yellow" :background "DimGray")) (t (:foreground "Blue" :background "LightGray"))) "\
*Face for file heading labels in `info'." :group (quote Info-Plus) :group (quote faces))

(defface info-menu '((((background dark)) (:foreground "Yellow")) (t (:foreground "Blue"))) "\
*Face used for menu items in `info'." :group (quote Info-Plus) :group (quote faces))

(defface info-quoted-name '((((background dark)) (:inherit font-lock-string-face :foreground "#6B6BFFFF2C2C")) (((background light)) (:inherit font-lock-string-face :foreground "DarkViolet")) (t (:foreground "yellow"))) "\
*Face for quoted names (`...') in `info'." :group (quote Info-Plus) :group (quote faces))

(defface info-string '((((background dark)) (:inherit font-lock-string-face :foreground "Orange")) (t (:inherit font-lock-string-face :foreground "red3"))) "\
*Face for strings (\"...\") in `info'." :group (quote Info-Plus) :group (quote faces))

(defface info-single-quote '((((background dark)) (:inherit font-lock-keyword-face :foreground "Green")) (t (:inherit font-lock-keyword-face :foreground "Magenta"))) "\
*Face for isolated single-quote marks (') in `info'." :group (quote Info-Plus) :group (quote faces))

(defface info-title-1 '((((type tty pc) (class color) (background dark)) :foreground "yellow" :weight bold) (((type tty pc) (class color) (background light)) :foreground "brown" :weight bold)) "\
*Face for info titles at level 1." :group (if (facep (quote info-title-1)) (quote info) (quote Info-Plus)))

(defface info-title-2 '((((type tty pc) (class color)) :foreground "lightblue" :weight bold)) "\
*Face for info titles at level 2." :group (if (facep (quote info-title-1)) (quote info) (quote Info-Plus)))

(defface info-title-3 '((((type tty pc) (class color)) :weight bold)) "\
*Face for info titles at level 3." :group (if (facep (quote info-title-1)) (quote info) (quote Info-Plus)))

(defface info-title-4 '((((type tty pc) (class color)) :weight bold)) "\
*Face for info titles at level 4." :group (if (facep (quote info-title-1)) (quote info) (quote Info-Plus)))

(defface info-function-ref-item '((((background dark)) (:foreground "#4D4DDDDDDDDD" :background "DimGray")) (t (:foreground "DarkBlue" :background "LightGray"))) "\
*Face used for \"Function:\" reference items in `info' manual." :group (quote Info-Plus) :group (quote faces))

(defface info-variable-ref-item '((((background dark)) (:foreground "Orange" :background "DimGray")) (t (:foreground "FireBrick" :background "LightGray"))) "\
*Face used for \"Variable:\" reference items in `info' manual." :group (quote Info-Plus) :group (quote faces))

(defface info-special-form-ref-item '((((background dark)) (:foreground "Yellow" :background "DimGray")) (t (:foreground "DarkMagenta" :background "LightGray"))) "\
*Face used for \"Special Form:\" reference items in `info' manual." :group (quote Info-Plus) :group (quote faces))

(defface info-command-ref-item '((((background dark)) (:foreground "#7474FFFF7474" :background "DimGray")) (t (:foreground "Blue" :background "LightGray"))) "\
*Face used for \"Command:\" reference items in `info' manual." :group (quote Info-Plus) :group (quote faces))

(defface info-user-option-ref-item '((((background dark)) (:foreground "Red" :background "DimGray")) (t (:foreground "Red" :background "LightGray"))) "\
*Face used for \"User Option:\" reference items in `info' manual." :group (quote Info-Plus) :group (quote faces))

(defface info-macro-ref-item '((((background dark)) (:foreground "Yellow" :background "DimGray")) (t (:foreground "DarkMagenta" :background "LightGray"))) "\
*Face used for \"Macro:\" reference items in `info' manual." :group (quote Info-Plus) :group (quote faces))

(defface info-syntax-class-item '((((background dark)) (:foreground "#FFFF9B9BFFFF" :background "DimGray")) (t (:foreground "DarkGreen" :background "LightGray"))) "\
*Face used for \"Syntax Class:\" reference items in `info' manual." :group (quote Info-Plus) :group (quote faces))

(defface info-reference-item '((((background dark)) (:background "DimGray")) (t (:background "LightGray"))) "\
*Face used for reference items in `info' manual." :group (quote Info-Plus) :group (quote faces))

(defvar Info-fit-frame-flag t "\
*Non-nil means call `fit-frame' on Info buffer.")

(custom-autoload 'Info-fit-frame-flag "info+" t)

(defvar Info-fontify-quotations-flag t "\
*Non-nil means `info' fontifies text between quotes.
This applies to double-quote strings (\"...\") and text between
single-quotes (`...').

Note: This fontification can never be 100% reliable.  It aims to be
useful in most Info texts, but it can occasionally result in
fontification that you might not expect.  This is not a bug; it is
part of the design to be able to appropriately fontify a great variety
of texts.  Set this flag to nil if you do not find this fontification
useful.")

(custom-autoload 'Info-fontify-quotations-flag "info+" t)

(defvar Info-fontify-single-quote-flag t "\
*Non-nil means `info' fontifies ' when not preceded by `....
A non-nil value has no effect unless `Info-fontify-quotations-flag' is
also non-nil.

Note: This fontification can never be 100% reliable.  It aims to be
useful in most Info texts, but it can occasionally result in
fontification that you might not expect.  This is not a bug; it is
part of the design to be able to appropriately fontify a great variety
of texts.  Set this flag to nil if you do not find this fontification
useful.")

(custom-autoload 'Info-fontify-single-quote-flag "info+" t)

(defvar Info-fontify-reference-items-flag t "\
*Non-nil means `info' fontifies reference items such as \"Function:\".")

(custom-autoload 'Info-fontify-reference-items-flag "info+" t)

(defvar Info-display-node-header-fn 'Info-display-node-default-header "\
*Function to insert header by `Info-merge-subnodes'.")

(custom-autoload 'Info-display-node-header-fn "info+" t)

(defvar Info-subtree-separator "\n* " "\
*A string used to separate Info node descriptions.
Inserted by `Info-merge-subnodes' just before each node title.
Setting this to a string that includes a form-feed (^L), such as
\"\\f\\n* \", will cause a page break before each node description.

Use command `set-variable' to set this, quoting any control characters
you want to include, such as form-feed (^L) and newline (^J), with ^Q.
For example, type `^Q^L^Q^J* ' to set this to \"\\f\\n* \".")

(custom-autoload 'Info-subtree-separator "info+" t)

(autoload 'Info-goto-emacs-command-node "info+" "\
Go to the Info node in the Emacs manual for command COMMAND.
The command is found by looking it up in Emacs manual's indexes,
or in another manual found via COMMAND's `info-file' property or
the variable `Info-file-list-for-emacs'.
COMMAND must be a symbol or string.

\(fn COMMAND)" t nil)

(autoload 'Info-goto-emacs-key-command-node "info+" "\
Go to the node in the Emacs manual describing command bound to KEY.
KEY is a string.

Interactively, if the binding is `execute-extended-command', then a
command is read.

The command is found by looking it up in Emacs manual's indexes,
or in another manual's index found via COMMAND's `info-file' property
or the variable `Info-file-list-for-emacs'.

If key's command cannot be found by looking in indexes, then
`Info-search' is used to search for the key sequence in the info text.

\(fn KEY)" t nil)

(autoload 'Info-merge-subnodes "info+" "\
Integrate current node with nodes referred to in its Menu.

Displays the current Info node, together with the nodes in its Menu.
Buffer `*Info: NODE*' is used for the display, where NODE is the name
of the current node.  The contents of this node's subnodes (the nodes
named in this node's Menu) are included in the buffer, following the
contents of the current node.

Optional arg RECURSIVE-DISPLAY-P (prefix arg if interactive) governs
the way menus of subnodes are treated:

  If nil, nothing additional happens.  Subnode menus are not explored.
  Only the current node and its immediate subnodes are documented, in
  the single display buffer `*Info: NODE*'.

  If non-nil, then the subnodes of a node are treated in the same way
  as the parent node, recursively: If any of them has, itself, a Menu,
  then that menu's subnodes are also explored, and so on.

    If RECURSIVE-DISPLAY-P is zero, then a single display buffer is
    used for all of the nodes explored.  Otherwise, a separate display
    buffer is used for each subnode that has a Menu (see next).

      Use this when you want a single, flat compilation of the current
      node and all of its subnodes.  It is less appropriate when the
      current node has several levels of subnodes: The flattened
      result can be difficult to read.

    If RECURSIVE-DISPLAY-P is positive, then the contents of each
    subnode are displayed twice: once in the parent node's display,
    and once in the subnode's own display.

      Use this when the current node has several levels of subnodes
      and you want each display buffer to be self-contained.

    If RECURSIVE-DISPLAY-P is negative, then there is no redundancy: A
    subnode's contents are only displayed in its parent's buffer.  The
    subnode's own display buffer only contains the contents of its own
    subnodes.

      Use this when the current node has several levels of subnodes
      and you want no redundancy between the display buffers.

The user option (variable) `Info-subtree-separator' is a string to be
inserted by `Info-merge-subnodes' just before the title of each
node (preceding its description).  By default it is \"\\n* \", producing
a node title resembling a menu item.  Setting this to \"\\f\\n* \" will
cause a page break before each node description.  For more on setting
this variable, type \\<Info-mode-map>`\\[describe-variable] Info-subtree-separator'.

------

Optional second arg RECURSIVE-CALL-P is only for internal use.  It is
used to indicate whether (non-nil) or not (nil) this is a recursive
\(i.e. not a top-level) call to `Info-merge-subnodes'.  Non-nil
means that this is a subnode, and that its contents should only be
included in the present display if RECURSIVE-DISPLAY-P is also
non-nil.  For proper operation when RECURSIVE-DISPLAY-P is zero, the
non-nil value of RECURSIVE-CALL-P should be the node name of the
top-level call to `Info-merge-subnodes'.

\(fn &optional RECURSIVE-DISPLAY-P RECURSIVE-CALL-P)" t nil)

;;;***

;;;### (autoloads (docTeX-mode TeX-latex-mode BibTeX-auto-store)
;;;;;;  "latex" "site-lisp/auctex/latex.el" (19180 28128))
;;; Generated autoloads from site-lisp/auctex/latex.el

(autoload 'BibTeX-auto-store "latex" "\
This function should be called from `bibtex-mode-hook'.
It will setup BibTeX to store keys in an auto file.

\(fn)" nil nil)

(add-to-list 'auto-mode-alist '("\\.drv\\'" . latex-mode))

(autoload 'TeX-latex-mode "latex" "\
Major mode in AUCTeX for editing LaTeX files.
See info under AUCTeX for full documentation.

Special commands:
\\{LaTeX-mode-map}

Entering LaTeX mode calls the value of `text-mode-hook',
then the value of `TeX-mode-hook', and then the value
of `LaTeX-mode-hook'.

\(fn)" t nil)

(add-to-list 'auto-mode-alist '("\\.dtx\\'" . doctex-mode))

(autoload 'docTeX-mode "latex" "\
Major mode in AUCTeX for editing .dtx files derived from `LaTeX-mode'.
Runs `LaTeX-mode', sets a few variables and
runs the hooks in `docTeX-mode-hook'.

\(fn)" t nil)

(defalias 'TeX-doctex-mode 'docTeX-mode)

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
;;;;;;  (20028 26506))
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

;;;### (autoloads (size-indication-mode modelinepos-column-limit)
;;;;;;  "modeline-posn" "site-lisp/modeline-posn.el" (19747 30566))
;;; Generated autoloads from site-lisp/modeline-posn.el

(defface modelinepos-column-warning '((t (:foreground "Red"))) "\
*Face used to highlight the modeline column number.
This is used when the current column number is greater than
`modelinepos-column-limit'." :group (quote Modeline) :group (quote Convenience) :group (quote Help) :group (quote faces))

(defvar modelinepos-column-limit 70 "\
Current column greater than this means highlight column in mode-line.")

(custom-autoload 'modelinepos-column-limit "modeline-posn" t)

(defvar size-indication-mode nil "\
Non-nil if Size-Indication mode is enabled.
See the command `size-indication-mode' for a description of this minor mode.")

(custom-autoload 'size-indication-mode "modeline-posn" nil)

(autoload 'size-indication-mode "modeline-posn" "\
Toggle Size Indication mode.
With arg, turn Size Indication mode on iff arg is positive.
When Size Indication mode is enabled, the buffer or region size
appears in the mode line.  If Transient Mark mode is enabled, the
region size is shown; otherwise, the size of the accessible part
of the buffer is shown.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (multi-prompt-key-value multi-prompt) "multi-prompt"
;;;;;;  "site-lisp/auctex/multi-prompt.el" (18915 28236))
;;; Generated autoloads from site-lisp/auctex/multi-prompt.el

(autoload 'multi-prompt "multi-prompt" "\
Completing prompt for a list of strings.  
The first argument SEPARATOR should be the string (of length 1) to
separate the elements in the list.  The second argument UNIQUE should
be non-nil, if each element must be unique.  The remaining elements
are the arguments to `completing-read'.  See that.

\(fn SEPARATOR UNIQUE PROMPT TABLE &optional MP-PREDICATE REQUIRE-MATCH INITIAL HISTORY)" nil nil)

(autoload 'multi-prompt-key-value "multi-prompt" "\
Read multiple strings, with completion and key=value support.
PROMPT is a string to prompt with, usually ending with a colon
and a space.  TABLE is an alist.  The car of each element should
be a string representing a key and the optional cdr should be a
list with strings to be used as values for the key.

See the documentation for `completing-read' for details on the
other arguments: PREDICATE, REQUIRE-MATCH, INITIAL-INPUT, HIST,
DEF, and INHERIT-INPUT-METHOD.

The return value is the string as entered in the minibuffer.

\(fn PROMPT TABLE &optional PREDICATE REQUIRE-MATCH INITIAL-INPUT HIST DEF INHERIT-INPUT-METHOD)" nil nil)

;;;***

;;;### (autoloads (nxhtml-byte-recompile-file nxhtml-byte-compile-file
;;;;;;  nxhtml-get-missing-files nxhtml-update-existing-files nxhtml-setup-download-all
;;;;;;  nxhtml-setup-auto-download nxhtml-setup-install) "nxhtml-web-vcs"
;;;;;;  "site-lisp/nxhtml/nxhtml-web-vcs.el" (19412 55566))
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
;;;;;;  (19379 9076))
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

;;;### (autoloads (refresh-pretty-control-l pp^L-^L-string Pretty-Control-L)
;;;;;;  "pp-c-l" "site-lisp/pp-c-l.el" (19747 36364))
;;; Generated autoloads from site-lisp/pp-c-l.el

(let ((loads (get 'Pretty-Control-L 'custom-loads))) (if (member '"pp-c-l" loads) nil (put 'Pretty-Control-L 'custom-loads (cons '"pp-c-l" loads))))

(defface pp^L-highlight (if (> emacs-major-version 21) '((((type x w32 mac graphic) (class color)) (:box (:line-width 3 :style pressed-button))) (t (:inverse-video t))) '((((type x w32 mac graphic) (class color)) (:foreground "Blue" :background "DarkSeaGreen1")) (t (:inverse-video t)))) "\
*Face used to highlight `pp^L-^L-vector'." :group (quote Pretty-Control-L) :group (quote faces))

(defvar pp^L-^L-string "          Section (Printable Page)          " "\
*Highlighted string displayed in place of each Control-l (^L) character.
If `pp^L-^L-string-function' is non-nil, then the string that function
returns is used instead of `pp^L-^L-string'.")

(custom-autoload 'pp^L-^L-string "pp-c-l" t)

(defalias 'pp^l 'pretty-control-l-mode)

(autoload 'refresh-pretty-control-l "pp-c-l" "\
Reinitialize `pretty-control-l-mode', if on, to update the display.

\(fn)" t nil)

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
;;;;;;  "site-lisp/python-mode/python-mode.el" (20026 23246))
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
;;;;;;  (20028 26506))
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

;;;### (autoloads (shell-toggle shell-toggle-cd) "sh-toggle" "sh-toggle.el"
;;;;;;  (20034 52464))
;;; Generated autoloads from sh-toggle.el

(autoload 'shell-toggle-cd "sh-toggle" "\
Calls `shell-toggle' with a prefix argument.
See the command `shell-toggle'

\(fn)" t nil)

(autoload 'shell-toggle "sh-toggle" "\
Toggles between the *shell* buffer and the current buffer.
With a prefix ARG also insert a \"cd DIR\" command into the shell,
where DIR is the directory of the current buffer.

Call twice in a row to get a full screen window for the *shell*
buffer.

When called in the *shell* buffer returns you to the buffer you were
editing before caling the first time.

Options: `shell-toggle-goto-eob'

\(fn MAKE-CD)" t nil)

;;;***

;;;### (autoloads (sr-dired sunrise-cd sunrise) "sunrise-commander"
;;;;;;  "site-lisp/sunrise-commander/sunrise-commander.el" (20024
;;;;;;  6655))
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

;;;### (autoloads (TeX-submit-bug-report ams-tex-mode TeX-auto-generate-global
;;;;;;  TeX-auto-generate TeX-plain-tex-mode TeX-tex-mode) "tex"
;;;;;;  "site-lisp/auctex/tex.el" (19327 63823))
;;; Generated autoloads from site-lisp/auctex/tex.el

(autoload 'TeX-tex-mode "tex" "\
Major mode in AUCTeX for editing TeX or LaTeX files.
Tries to guess whether this file is for plain TeX or LaTeX.

The algorithm is as follows:

   1) if the file is empty or `TeX-force-default-mode' is not set to nil,
      `TeX-default-mode' is chosen
   2) If \\documentstyle or \\begin{, \\section{, \\part{ or \\chapter{ is
      found, `latex-mode' is selected.
   3) Otherwise, use `plain-tex-mode'

\(fn)" t nil)

(autoload 'TeX-plain-tex-mode "tex" "\
Major mode in AUCTeX for editing plain TeX files.
See info under AUCTeX for documentation.

Special commands:
\\{plain-TeX-mode-map}

Entering `plain-tex-mode' calls the value of `text-mode-hook',
then the value of `TeX-mode-hook', and then the value
of plain-TeX-mode-hook.

\(fn)" t nil)

(autoload 'TeX-auto-generate "tex" "\
Generate style file for TEX and store it in AUTO.
If TEX is a directory, generate style files for all files in the directory.

\(fn TEX AUTO)" t nil)

(autoload 'TeX-auto-generate-global "tex" "\
Create global auto directory for global TeX macro definitions.

\(fn)" t nil)

(autoload 'ams-tex-mode "tex" "\
Major mode in AUCTeX for editing AmS-TeX files.
See info under AUCTeX for documentation.

Special commands:
\\{AmSTeX-mode-map}

Entering AmS-tex-mode calls the value of `text-mode-hook',
then the value of `TeX-mode-hook', and then the value
of `AmS-TeX-mode-hook'.

\(fn)" t nil)

(autoload 'TeX-submit-bug-report "tex" "\
Submit a bug report on AUCTeX via mail.

Don't hesitate to report any problems or inaccurate documentation.

If you don't have setup sending mail from (X)Emacs, please copy the
output buffer into your mail program, as it gives us important
information about your AUCTeX version and AUCTeX configuration.

\(fn)" t nil)

;;;***

;;;### (autoloads (LaTeX-install-toolbar TeX-install-toolbar) "tex-bar"
;;;;;;  "site-lisp/auctex/tex-bar.el" (18580 49499))
;;; Generated autoloads from site-lisp/auctex/tex-bar.el

(autoload 'TeX-install-toolbar "tex-bar" "\
Install toolbar buttons for TeX mode.

\(fn)" t nil)

(autoload 'LaTeX-install-toolbar "tex-bar" "\
Install toolbar buttons for LaTeX mode.

\(fn)" t nil)

;;;***

;;;### (autoloads nil "tex-fold" "site-lisp/auctex/tex-fold.el" (19227
;;;;;;  40177))
;;; Generated autoloads from site-lisp/auctex/tex-fold.el
 (autoload 'TeX-fold-mode "tex-fold" "Minor mode for hiding and revealing macros and environments." t)

(defalias 'tex-fold-mode 'TeX-fold-mode)

;;;***

;;;### (autoloads (tex-font-setup) "tex-font" "site-lisp/auctex/tex-font.el"
;;;;;;  (18341 54636))
;;; Generated autoloads from site-lisp/auctex/tex-font.el

(autoload 'tex-font-setup "tex-font" "\
Setup font lock support for TeX.

\(fn)" nil nil)

;;;***

;;;### (autoloads (TeX-texinfo-mode) "tex-info" "site-lisp/auctex/tex-info.el"
;;;;;;  (18903 48810))
;;; Generated autoloads from site-lisp/auctex/tex-info.el

(defalias 'Texinfo-mode 'texinfo-mode)

(autoload 'TeX-texinfo-mode "tex-info" "\
Major mode in AUCTeX for editing Texinfo files.

Special commands:
\\{Texinfo-mode-map}

Entering Texinfo mode calls the value of `text-mode-hook'  and then the
value of `Texinfo-mode-hook'.

\(fn)" t nil)

;;;***

;;;### (autoloads (japanese-latex-mode japanese-plain-tex-mode) "tex-jp"
;;;;;;  "site-lisp/auctex/tex-jp.el" (18768 5174))
;;; Generated autoloads from site-lisp/auctex/tex-jp.el

(autoload 'japanese-plain-tex-mode "tex-jp" "\
Major mode in AUCTeX for editing Japanese plain TeX files.
Set `japanese-TeX-mode' to t, and enter `TeX-plain-tex-mode'.

\(fn)" t nil)

(autoload 'japanese-latex-mode "tex-jp" "\
Major mode in AUCTeX for editing Japanese LaTeX files.
Set `japanese-TeX-mode' to t, and enter `TeX-latex-mode'.

\(fn)" t nil)

;;;***

;;;### (autoloads (texmathp-match-switch texmathp) "texmathp" "site-lisp/auctex/texmathp.el"
;;;;;;  (18489 3128))
;;; Generated autoloads from site-lisp/auctex/texmathp.el

(autoload 'texmathp "texmathp" "\
Determine if point is inside (La)TeX math mode.
Returns t or nil.  Additional info is placed into `texmathp-why'.
The functions assumes that you have (almost) syntactically correct (La)TeX in
the buffer.
See the variable `texmathp-tex-commands' about which commands are checked.

\(fn)" t nil)

(autoload 'texmathp-match-switch "texmathp" "\
Search backward for any of the math switches.
Limit searched to BOUND.

\(fn BOUND)" nil nil)

;;;***

;;;### (autoloads nil "toolbar-x" "site-lisp/auctex/toolbar-x.el"
;;;;;;  (18580 49487))
;;; Generated autoloads from site-lisp/auctex/toolbar-x.el
 (autoload 'toolbarx-install-toolbar "toolbar-x")

;;;***

;;;### (autoloads (vcard-parse-region vcard-parse-string vcard-pretty-print
;;;;;;  vcard-standard-filters vcard-pretty-print-function) "vcard"
;;;;;;  "site-lisp/vcard.el" (14683 33501))
;;; Generated autoloads from site-lisp/vcard.el

(defvar vcard-pretty-print-function 'vcard-format-sample-box "\
*Formatting function used by `vcard-pretty-print'.")

(custom-autoload 'vcard-pretty-print-function "vcard" t)

(defvar vcard-standard-filters '(vcard-filter-html vcard-filter-adr-newlines vcard-filter-tel-normalize vcard-filter-textprop-cr) "\
*Standard list of filters to apply to parsed vcard data.
These filters are applied sequentially to vcard attributes when
the function `vcard-standard-filter' is supplied as the second argument to
`vcard-parse'.")

(custom-autoload 'vcard-standard-filters "vcard" t)

(autoload 'vcard-pretty-print "vcard" "\
Format VCARD into a string suitable for display to user.
VCARD can be an unparsed string containing raw VCF vcard data
or a parsed vcard alist as returned by `vcard-parse-string'.

The result is a string with formatted vcard information suitable for
insertion into a mime presentation buffer.

The function specified by the variable `vcard-pretty-print-function'
actually performs the formatting.  That function will always receive a
parsed vcard alist.

\(fn VCARD)" nil nil)

(autoload 'vcard-parse-string "vcard" "\
Parse RAW vcard data as a string, and return an alist representing data.

If the optional function FILTER is specified, apply that filter to each
attribute.  If no filter is specified, `vcard-standard-filter' is used.

Filters should accept two arguments: the property list and the value list.
Modifying in place the property or value list will affect the resulting
attribute in the vcard alist.

Vcard data is normally in the form

    begin:                        vcard
    prop1a:                       value1a
    prop2a;prop2b;prop2c=param2c: value2a
    prop3a;prop3b:                value3a;value3b;value3c
    end:                          vcard

\(Whitespace around the `:' separating properties and values is optional.)
If supplied to this function an alist of the form

    (((\"prop1a\") \"value1a\")
     ((\"prop2a\" \"prop2b\" (\"prop2c\" . \"param2c\")) \"value2a\")
     ((\"prop3a\" \"prop3b\") \"value3a\" \"value3b\" \"value3c\"))

would be returned.

\(fn RAW &optional FILTER)" nil nil)

(autoload 'vcard-parse-region "vcard" "\
Parse the raw vcard data in region, and return an alist representing data.
This function is just like `vcard-parse-string' except that it operates on
a region of the current buffer rather than taking a string as an argument.

Note: this function modifies the buffer!

\(fn BEG END &optional FILTER)" nil nil)

;;;***

;;;### (autoloads (vline-global-mode vline-mode) "vline" "site-lisp/drewadams/vline.el"
;;;;;;  (19305 58831))
;;; Generated autoloads from site-lisp/drewadams/vline.el

(autoload 'vline-mode "vline" "\
Display vertical line mode.

\(fn &optional ARG)" t nil)

(defvar vline-global-mode nil "\
Non-nil if Vline-Global mode is enabled.
See the command `vline-global-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `vline-global-mode'.")

(custom-autoload 'vline-global-mode "vline" nil)

(autoload 'vline-global-mode "vline" "\
Toggle Vline mode in every possible buffer.
With prefix ARG, turn Vline-Global mode on if and only if
ARG is positive.
Vline mode is enabled in all buffers where
`(lambda nil (unless (minibufferp) (vline-mode 1)))' would do it.
See `vline-mode' for more information on Vline mode.

\(fn &optional ARG)" t nil)

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
;;;;;;  (19412 55566))
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

;;;### (autoloads (yas-template-install yas-template-insert) "yas-template"
;;;;;;  "site-lisp/el-staging/yas-template.el" (20048 33582))
;;; Generated autoloads from site-lisp/el-staging/yas-template.el

(autoload 'yas-template-insert "yas-template" "\
Not documented

\(fn &rest IGNORE)" nil nil)

(autoload 'yas-template-install "yas-template" "\
Not documented

\(fn)" nil nil)

;;;***

;;;### (autoloads (yas/minor-mode yas/snippet-dirs) "yasnippet" "site-lisp/yasnippet/yasnippet.el"
;;;;;;  (20048 30693))
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

;;;### (autoloads (color-theme-zenburn) "zenburn" "site-lisp/zenburn-el/zenburn.el"
;;;;;;  (20046 33348))
;;; Generated autoloads from site-lisp/zenburn-el/zenburn.el

(autoload 'color-theme-zenburn "zenburn" "\
Just some alien fruit salad to keep you in the zone.

\(fn)" t nil)

(defalias 'zenburn #'color-theme-zenburn)

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

;;;### (autoloads nil nil ("cus-dirs.el" "init.el" "org-devonthink.el"
;;;;;;  "site-lisp/all.el" "site-lisp/anything-complete.el" "site-lisp/anything-complete.el"
;;;;;;  "site-lisp/anything-gtags.el" "site-lisp/anything-gtags.el"
;;;;;;  "site-lisp/anything/anything-match-plugin.el" "site-lisp/anything/anything-startup.el"
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
;;;;;;  "site-lisp/ascii.el" "site-lisp/auctex/auctex.el" "site-lisp/auctex/auto-loads.el"
;;;;;;  "site-lisp/auctex/lpath.el" "site-lisp/auctex/tex-buf.el"
;;;;;;  "site-lisp/auctex/tex-fptex.el" "site-lisp/auctex/tex-mik.el"
;;;;;;  "site-lisp/auctex/tex-site.el" "site-lisp/auctex/tex-style.el"
;;;;;;  "site-lisp/auctex/tex-wizard.el" "site-lisp/bbdb/loadpath.el"
;;;;;;  "site-lisp/bookmark+/bookmark+-chg.el" "site-lisp/bookmark+/bookmark+-doc.el"
;;;;;;  "site-lisp/bookmark+/bookmark+-key.el" "site-lisp/breadcrumb.el"
;;;;;;  "site-lisp/breadcrumb.el" "site-lisp/browse-kill-ring+.el"
;;;;;;  "site-lisp/browse-kill-ring+.el" "site-lisp/browse-kill-ring.el"
;;;;;;  "site-lisp/chess/auto-autoloads.el" "site-lisp/chess/chess-ai.el"
;;;;;;  "site-lisp/chess/chess-algebraic.el" "site-lisp/chess/chess-announce.el"
;;;;;;  "site-lisp/chess/chess-auto.el" "site-lisp/chess/chess-autosave.el"
;;;;;;  "site-lisp/chess/chess-chat.el" "site-lisp/chess/chess-clock.el"
;;;;;;  "site-lisp/chess/chess-common.el" "site-lisp/chess/chess-crafty.el"
;;;;;;  "site-lisp/chess/chess-database.el" "site-lisp/chess/chess-display.el"
;;;;;;  "site-lisp/chess/chess-eco.el" "site-lisp/chess/chess-engine.el"
;;;;;;  "site-lisp/chess/chess-epd.el" "site-lisp/chess/chess-fen.el"
;;;;;;  "site-lisp/chess/chess-file.el" "site-lisp/chess/chess-game.el"
;;;;;;  "site-lisp/chess/chess-german.el" "site-lisp/chess/chess-gnuchess.el"
;;;;;;  "site-lisp/chess/chess-ics1.el" "site-lisp/chess/chess-images.el"
;;;;;;  "site-lisp/chess/chess-input.el" "site-lisp/chess/chess-irc.el"
;;;;;;  "site-lisp/chess/chess-kibitz.el" "site-lisp/chess/chess-log.el"
;;;;;;  "site-lisp/chess/chess-maint.el" "site-lisp/chess/chess-message.el"
;;;;;;  "site-lisp/chess/chess-module.el" "site-lisp/chess/chess-network.el"
;;;;;;  "site-lisp/chess/chess-none.el" "site-lisp/chess/chess-phalanx.el"
;;;;;;  "site-lisp/chess/chess-plain.el" "site-lisp/chess/chess-ply.el"
;;;;;;  "site-lisp/chess/chess-pos.el" "site-lisp/chess/chess-scid.el"
;;;;;;  "site-lisp/chess/chess-sjeng.el" "site-lisp/chess/chess-sound.el"
;;;;;;  "site-lisp/chess/chess-test.el" "site-lisp/chess/chess-transport.el"
;;;;;;  "site-lisp/chess/chess-ucb.el" "site-lisp/chess/chess-var.el"
;;;;;;  "site-lisp/color-theme/color-theme-autoloads.el" "site-lisp/column-marker.el"
;;;;;;  "site-lisp/company/company-clang.el" "site-lisp/company/company-eclim.el"
;;;;;;  "site-lisp/company/company-ropemacs.el" "site-lisp/company/company-template.el"
;;;;;;  "site-lisp/css-mode.el" "site-lisp/css-mode.el" "site-lisp/csv-mode.el"
;;;;;;  "site-lisp/csv-mode.el" "site-lisp/descbinds-anything.el"
;;;;;;  "site-lisp/descbinds-anything.el" "site-lisp/diff-mode-.el"
;;;;;;  "site-lisp/diff-mode-.el" "site-lisp/diminish.el" "site-lisp/double-insert.el"
;;;;;;  "site-lisp/double-insert.el" "site-lisp/dwamacs/dwamacs-install.el"
;;;;;;  "site-lisp/dwamacs/init.el" "site-lisp/edit-server.el" "site-lisp/edit-server.el"
;;;;;;  "site-lisp/ee/ee-autoloads.el" "site-lisp/emacs-w3m/mew-w3m.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-bug.el" "site-lisp/emacs-w3m/w3m-ccl.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-ems.el" "site-lisp/emacs-w3m/w3m-favicon.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-hist.el" "site-lisp/emacs-w3m/w3m-image.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-load.el" "site-lisp/emacs-w3m/w3m-mail.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-proc.el" "site-lisp/emacs-w3m/w3m-rss.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-tabmenu.el" "site-lisp/emacs-w3m/w3m-ucs.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-util.el" "site-lisp/emacs-w3m/w3m-xmas.el"
;;;;;;  "site-lisp/emacs-w3m/w3mhack.el" "site-lisp/escreen.el" "site-lisp/escreen.el"
;;;;;;  "site-lisp/eshell/auto-autoloads.el" "site-lisp/eshell/em-alias.el"
;;;;;;  "site-lisp/eshell/em-banner.el" "site-lisp/eshell/em-basic.el"
;;;;;;  "site-lisp/eshell/em-cmpl.el" "site-lisp/eshell/em-dirs.el"
;;;;;;  "site-lisp/eshell/em-glob.el" "site-lisp/eshell/em-hist.el"
;;;;;;  "site-lisp/eshell/em-ls.el" "site-lisp/eshell/em-pred.el"
;;;;;;  "site-lisp/eshell/em-prompt.el" "site-lisp/eshell/em-rebind.el"
;;;;;;  "site-lisp/eshell/em-script.el" "site-lisp/eshell/em-smart.el"
;;;;;;  "site-lisp/eshell/em-term.el" "site-lisp/eshell/em-unix.el"
;;;;;;  "site-lisp/eshell/em-xtra.el" "site-lisp/eshell/esh-arg.el"
;;;;;;  "site-lisp/eshell/esh-cmd.el" "site-lisp/eshell/esh-ext.el"
;;;;;;  "site-lisp/eshell/esh-groups.el" "site-lisp/eshell/esh-io.el"
;;;;;;  "site-lisp/eshell/esh-maint.el" "site-lisp/eshell/esh-module.el"
;;;;;;  "site-lisp/eshell/esh-opt.el" "site-lisp/eshell/esh-proc.el"
;;;;;;  "site-lisp/eshell/esh-toggle.el" "site-lisp/eshell/esh-util.el"
;;;;;;  "site-lisp/eshell/esh-var.el" "site-lisp/eshell/eshell-auto.el"
;;;;;;  "site-lisp/eval-expr.el" "site-lisp/fdb.el" "site-lisp/fdb.el"
;;;;;;  "site-lisp/find-library.el" "site-lisp/fit-frame.el" "site-lisp/fm.el"
;;;;;;  "site-lisp/fm.el" "site-lisp/gnuplot-gui.el" "site-lisp/gnuplot-gui.el"
;;;;;;  "site-lisp/gnuplot.el" "site-lisp/grep-ed.el" "site-lisp/grep-ed.el"
;;;;;;  "site-lisp/gtags.el" "site-lisp/haskell-mode/haskell-font-lock.el"
;;;;;;  "site-lisp/haskell-mode/haskell-ghci.el" "site-lisp/haskell-mode/haskell-hugs.el"
;;;;;;  "site-lisp/haskell-mode/haskell-simple-indent.el" "site-lisp/haskell-mode/haskell-site-file.el"
;;;;;;  "site-lisp/hide-region.el" "site-lisp/hide-search.el" "site-lisp/hide-search.el"
;;;;;;  "site-lisp/highlight-parentheses.el" "site-lisp/howm/action-lock.el"
;;;;;;  "site-lisp/howm/bcomp.el" "site-lisp/howm/cheat-font-lock.el"
;;;;;;  "site-lisp/howm/gfunc.el" "site-lisp/howm/honest-report.el"
;;;;;;  "site-lisp/howm/howm-backend.el" "site-lisp/howm/howm-cl.el"
;;;;;;  "site-lisp/howm/howm-common.el" "site-lisp/howm/howm-date.el"
;;;;;;  "site-lisp/howm/howm-lang-en.el" "site-lisp/howm/howm-lang-ja.el"
;;;;;;  "site-lisp/howm/howm-menu-en.el" "site-lisp/howm/howm-menu-ja.el"
;;;;;;  "site-lisp/howm/howm-menu.el" "site-lisp/howm/howm-misc.el"
;;;;;;  "site-lisp/howm/howm-mkmenu.el" "site-lisp/howm/howm-mode.el"
;;;;;;  "site-lisp/howm/howm-reminder.el" "site-lisp/howm/howm-vars.el"
;;;;;;  "site-lisp/howm/howm-version.el" "site-lisp/howm/howm-view.el"
;;;;;;  "site-lisp/howm/howm.el" "site-lisp/howm/illusion.el" "site-lisp/howm/riffle.el"
;;;;;;  "site-lisp/hs-lint.el" "site-lisp/hs-lint.el" "site-lisp/indirect.el"
;;;;;;  "site-lisp/indirect.el" "site-lisp/initsplit/initsplit-test.el"
;;;;;;  "site-lisp/initsplit/initsplit.el" "site-lisp/linum.el" "site-lisp/lisp/paredit.el"
;;;;;;  "site-lisp/lisp/parenface.el" "site-lisp/lisp/redshank.el"
;;;;;;  "site-lisp/magit/50magit.el" "site-lisp/magit/magit-bisect.el"
;;;;;;  "site-lisp/magit/magit-key-mode.el" "site-lisp/magit/magit-pkg.el"
;;;;;;  "site-lisp/magit/magit-stgit.el" "site-lisp/magit/magit-svn.el"
;;;;;;  "site-lisp/magit/magit-topgit.el" "site-lisp/markdown-mode.el"
;;;;;;  "site-lisp/message-x.el" "site-lisp/message-x.el" "site-lisp/modeline-posn.el"
;;;;;;  "site-lisp/mudel.el" "site-lisp/mudel.el" "site-lisp/nxhtml/autostart.el"
;;;;;;  "site-lisp/nxhtml/autostart22.el" "site-lisp/nxhtml/nxhtml-base.el"
;;;;;;  "site-lisp/nxhtml/nxhtml-loaddefs.el" "site-lisp/nxhtml/web-autoload.el"
;;;;;;  "site-lisp/per-window-point.el" "site-lisp/per-window-point.el"
;;;;;;  "site-lisp/po-mode.el" "site-lisp/po-mode.el" "site-lisp/pp-c-l.el"
;;;;;;  "site-lisp/psvn.el" "site-lisp/puppet-mode.el" "site-lisp/python-mode/highlight-indentation.el"
;;;;;;  "site-lisp/python-mode/pars-part-output.el" "site-lisp/python-mode/py-bug-numbered-tests.el"
;;;;;;  "site-lisp/python-mode/pycomplete.el" "site-lisp/python-mode/python-components-test.el"
;;;;;;  "site-lisp/python-mode/python-mode-test.el" "site-lisp/regex-tool/regex-tool.el"
;;;;;;  "site-lisp/repeat-insert.el" "site-lisp/repeat-insert.el"
;;;;;;  "site-lisp/settings.el" "site-lisp/settings.el" "site-lisp/slime/hyperspec.el"
;;;;;;  "site-lisp/slime/slime-autoloads.el" "site-lisp/slime/slime.el"
;;;;;;  "site-lisp/sunrise-commander/sunrise-x-buttons.el" "site-lisp/sunrise-commander/sunrise-x-checkpoints.el"
;;;;;;  "site-lisp/sunrise-commander/sunrise-x-loop.el" "site-lisp/sunrise-commander/sunrise-x-mirror.el"
;;;;;;  "site-lisp/sunrise-commander/sunrise-x-modeline.el" "site-lisp/sunrise-commander/sunrise-x-old-checkpoints.el"
;;;;;;  "site-lisp/sunrise-commander/sunrise-x-popviewer.el" "site-lisp/sunrise-commander/sunrise-x-tabs.el"
;;;;;;  "site-lisp/sunrise-commander/sunrise-x-tree.el" "site-lisp/sunrise-commander/sunrise-x-w32-addons.el"
;;;;;;  "site-lisp/vcard.el" "site-lisp/vkill.el" "site-lisp/vkill.el"
;;;;;;  "site-lisp/wcount.el" "site-lisp/wcount.el" "site-lisp/wgrep.el"
;;;;;;  "site-lisp/wgrep.el" "site-lisp/whole-line-or-region.el"
;;;;;;  "site-lisp/xml-rpc.el" "site-lisp/xml-rpc.el" "site-lisp/xray.el"
;;;;;;  "site-lisp/yasnippet/dropdown-list.el" "site-lisp/yasnippet/yasnippet-debug.el"
;;;;;;  "tds2texi.el") (20048 39098 865071))

;;;***

;;;### (autoloads (c-includes c-includes-current-file c-includes-add-binding)
;;;;;;  "c-includes" "c-includes.el" (20022 25706))
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
you to determine order of occurrence.

\(fn FILENAME &optional REGEXP)" t nil)

;;;***
