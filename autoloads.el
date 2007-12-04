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
