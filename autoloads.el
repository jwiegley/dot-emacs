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
Any changes made in that buffer will be propagated to this buffer.

\(fn REGEXP &optional NLINES)" t nil)

;;;***

;;;### (autoloads (ascii-off ascii-on ascii-display ascii-customize)
;;;;;;  "ascii" "site-lisp/ascii.el" (18084 9489))
;;; Generated autoloads from site-lisp/ascii.el

(autoload (quote ascii-customize) "ascii" "\
Customize ASCII options.

\(fn)" t nil)

(autoload (quote ascii-display) "ascii" "\
Toggle ASCII code display.

If ARG is null, toggle ASCII code display.
If ARG is a number and is greater than zero, turn on display; otherwise, turn
off display.
If ARG is anything else, turn on display.

\(fn &optional ARG)" t nil)

(autoload (quote ascii-on) "ascii" "\
Turn on ASCII code display.

\(fn)" t nil)

(autoload (quote ascii-off) "ascii" "\
Turn off ASCII code display.

\(fn)" t nil)

;;;***

;;;### (autoloads (browse-kill-ring browse-kill-ring-default-keybindings)
;;;;;;  "browse-kill-ring" "site-lisp/browse-kill-ring.el" (18084
;;;;;;  9490))
;;; Generated autoloads from site-lisp/browse-kill-ring.el

(autoload (quote browse-kill-ring-default-keybindings) "browse-kill-ring" "\
Set up M-y (`yank-pop') so that it can invoke `browse-kill-ring'.
Normally, if M-y was not preceeded by C-y, then it has no useful
behavior.  This function sets things up so that M-y will invoke
`browse-kill-ring'.

\(fn)" t nil)

(autoload (quote browse-kill-ring) "browse-kill-ring" "\
Display items in the `kill-ring' in another buffer.

\(fn)" t nil)

;;;***

;;;### (autoloads (check-mail) "check-mail" "check-mail.el" (18205
;;;;;;  36835))
;;; Generated autoloads from check-mail.el

(autoload (quote check-mail) "check-mail" "\
Check all of the boxes listed in `mail-boxes-to-check' for new mail.

\(fn)" t nil)

;;;***

;;;### (autoloads (chop-move-down chop-move-up) "chop" "site-lisp/chop.el"
;;;;;;  (18084 9489))
;;; Generated autoloads from site-lisp/chop.el

(autoload (quote chop-move-up) "chop" "\
Move by one 'chop' into the upper half of the remaining space.

\(fn)" t nil)

(autoload (quote chop-move-down) "chop" "\
Move by one 'chop' into the lower half of the remaining space.

\(fn)" t nil)

;;;***

;;;### (autoloads (circe) "circe" "site-lisp/circe/circe.el" (18101
;;;;;;  64394))
;;; Generated autoloads from site-lisp/circe/circe.el

(autoload (quote circe) "circe" "\
Connect to the IRC server HOST at SERVICE.
NETWORK is the shorthand used for indicating where we're connected
to. (defaults to HOST)
PASS is the password.
NICK is the nick name to use (defaults to `circe-default-nick')
USER is the user name to use (defaults to `circe-default-user')
REALNAME is the real name to use (defaults to `circe-default-realname')

\(fn HOST SERVICE &optional NETWORK PASS NICK USER REALNAME)" t nil)

;;;***

;;;### (autoloads (enable-circe-highlight-all-nicks) "circe-highlight-all-nicks"
;;;;;;  "site-lisp/circe/circe-highlight-all-nicks.el" (17197 53002))
;;; Generated autoloads from site-lisp/circe/circe-highlight-all-nicks.el

(autoload (quote enable-circe-highlight-all-nicks) "circe-highlight-all-nicks" "\
Enable the Highlight Nicks module for Circe.
This module highlights all occurances of nicks in the current
channel in messages of other people.

\(fn)" t nil)

;;;***

;;;### (autoloads (enable-circe-log) "circe-log" "site-lisp/circe/circe-log.el"
;;;;;;  (18080 62587))
;;; Generated autoloads from site-lisp/circe/circe-log.el

(autoload (quote enable-circe-log) "circe-log" "\
Enables automatic logging for all buffers matching
`circe-log-buffer-regexp' and not matching
`circe-log-exlude-buffer-regexp'.

\(fn)" t nil)

;;;***

;;;### (autoloads (cl-info) "cl-info" "cl-info.el" (18237 22608))
;;; Generated autoloads from cl-info.el

(autoload (quote cl-info) "cl-info" "\
Not documented

\(fn SYMBOL-NAME)" t nil)

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

(custom-autoload (quote cldoc-mode) "cldoc" t)

(defvar cldoc-minor-mode-string " Cldoc" "\
*String to display in mode line when Cldoc Mode is enabled.")

(custom-autoload (quote cldoc-minor-mode-string) "cldoc" t)

(cond ((fboundp (quote add-minor-mode)) (add-minor-mode (quote cldoc-mode) (quote cldoc-minor-mode-string))) ((assq (quote cldoc-mode) (default-value (quote minor-mode-alist)))) (t (setq-default minor-mode-alist (append (default-value (quote minor-mode-alist)) (quote ((cldoc-mode cldoc-minor-mode-string)))))))

(autoload (quote cldoc-mode) "cldoc" "\
*Enable or disable cldoc mode.
See documentation for the variable of the same name for more details.

If called interactively with no prefix argument, toggle current condition
of the mode.
If called with a positive or negative prefix argument, enable or disable
the mode, respectively.

\(fn &optional PREFIX)" t nil)

(autoload (quote turn-on-cldoc-mode) "cldoc" "\
Unequivocally turn on cldoc-mode (see variable documentation).

\(fn)" t nil)

;;;***

;;;### (autoloads nil "column-marker" "site-lisp/column-marker.el"
;;;;;;  (17638 24216))
;;; Generated autoloads from site-lisp/column-marker.el

(autoload (quote column-marker-1) "column-marker" "\
Highlight a column." t)

;;;***

;;;### (autoloads (darcsum-view darcsum-whatsnew) "darcsum" "darcsum.el"
;;;;;;  (18170 21799))
;;; Generated autoloads from darcsum.el

(autoload (quote darcsum-whatsnew) "darcsum" "\
Run `darcs whatsnew' in DIRECTORY, displaying the output in `darcsum-mode'.

When invoked interactively, prompt for the directory to display changes for.

\(fn DIRECTORY &optional LOOK-FOR-ADDS NO-DISPLAY SHOW-CONTEXT)" t nil)

(autoload (quote darcsum-view) "darcsum" "\
View the contents of the current buffer as a darcs changeset for DIRECTORY.
More precisely, searches forward from point for the next changeset-like region,
and attempts to parse that as a darcs patch.

When invoked interactively, prompts for a directory; by default, the current
working directory is assumed.

\(fn DIRECTORY)" t nil)

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
to TO-WHAT if it's > 1 char long & doesn't already begin with a space.

\(fn MODE &optional TO-WHAT)" t nil)

(autoload (quote diminish-undo) "diminish" "\
Restore mode-line display of diminished mode MODE to its minor-mode value.
Do nothing if the arg is a minor mode that hasn't been diminished.

Interactively, enter (with completion) the name of any diminished mode (a
mode that was formerly a minor mode on which you invoked M-x diminish).
To restore all diminished modes to minor status, answer `diminished-modes'.
The response to the prompt shouldn't be quoted.  However, in Lisp code,
the arg must be quoted as a symbol, as in (diminish-undo 'diminished-modes).

\(fn MODE)" t nil)

(autoload (quote diminished-modes) "diminish" "\
Echo all active diminished or minor modes as if they were minor.
The display goes in the echo area; if it's too long even for that,
you can see the whole thing in the *Messages* buffer.
This doesn't change the status of any modes; it just lets you see
what diminished modes would be on the mode-line if they were still minor.

\(fn)" t nil)

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
\".tar.Z\" or else this command will assume it's not a tar file.

\(fn PREFIX-ARG)" t nil)

(add-hook (quote dired-mode-hook) (function (lambda nil (define-key dired-mode-map "T" (quote dired-tar-pack-unpack)))))

;;;***

;;;### (autoloads (edit-variable) "edit-var" "site-lisp/edit-var.el"
;;;;;;  (18084 9491))
;;; Generated autoloads from site-lisp/edit-var.el

(autoload (quote edit-variable) "edit-var" "\
Edit the value of VARIABLE.

\(fn VARIABLE)" t nil)

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
List all keys matched with NAME from the public keyring.

\(fn &optional NAME)" t nil)

(autoload (quote epa-list-secret-keys) "epa" "\
List all keys matched with NAME from the private keyring.

\(fn &optional NAME)" t nil)

(autoload (quote epa-select-keys) "epa" "\
Display a user's keyring and ask him to select keys.
CONTEXT is an epg-context.
PROMPT is a string to prompt with.
NAMES is a list of strings to be matched with keys.  If it is nil, all
the keys are listed.
If SECRET is non-nil, list secret keys instead of public keys.

\(fn CONTEXT PROMPT &optional NAMES SECRET)" nil nil)

(autoload (quote epa-decrypt-file) "epa" "\
Decrypt FILE.

\(fn FILE)" t nil)

(autoload (quote epa-verify-file) "epa" "\
Verify FILE.

\(fn FILE)" t nil)

(autoload (quote epa-sign-file) "epa" "\
Sign FILE by SIGNERS keys selected.

\(fn FILE SIGNERS MODE)" t nil)

(autoload (quote epa-encrypt-file) "epa" "\
Encrypt FILE for RECIPIENTS.

\(fn FILE RECIPIENTS)" t nil)

(autoload (quote epa-decrypt-region) "epa" "\
Decrypt the current region between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload (quote epa-decrypt-armor-in-region) "epa" "\
Decrypt OpenPGP armors in the current region between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload (quote epa-verify-region) "epa" "\
Verify the current region between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload (quote epa-verify-cleartext-in-region) "epa" "\
Verify OpenPGP cleartext signed messages in the current region
between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload (quote epa-sign-region) "epa" "\
Sign the current region between START and END by SIGNERS keys selected.

Don't use this command in Lisp programs!

\(fn START END SIGNERS MODE)" t nil)

(autoload (quote epa-encrypt-region) "epa" "\
Encrypt the current region between START and END for RECIPIENTS.

Don't use this command in Lisp programs!

\(fn START END RECIPIENTS SIGN SIGNERS)" t nil)

(autoload (quote epa-delete-keys) "epa" "\
Delete selected KEYS.

Don't use this command in Lisp programs!

\(fn KEYS &optional ALLOW-SECRET)" t nil)

(autoload (quote epa-import-keys) "epa" "\
Import keys from FILE.

Don't use this command in Lisp programs!

\(fn FILE)" t nil)

(autoload (quote epa-import-keys-region) "epa" "\
Import keys from the region.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload (quote epa-import-armor-in-region) "epa" "\
Import keys in the OpenPGP armor format in the current region
between START and END.

Don't use this command in Lisp programs!

\(fn START END)" t nil)

(autoload (quote epa-export-keys) "epa" "\
Export selected KEYS to FILE.

Don't use this command in Lisp programs!

\(fn KEYS FILE)" t nil)

(autoload (quote epa-insert-keys) "epa" "\
Insert selected KEYS after the point.

Don't use this command in Lisp programs!

\(fn KEYS)" t nil)

(autoload (quote epa-sign-keys) "epa" "\
Sign selected KEYS.
If a prefix-arg is specified, the signature is marked as non exportable.

Don't use this command in Lisp programs!

\(fn KEYS &optional LOCAL)" t nil)

;;;***

;;;### (autoloads (epa-file-disable epa-file-enable) "epa-file" "site-lisp/epg/epa-file.el"
;;;;;;  (18076 8990))
;;; Generated autoloads from site-lisp/epg/epa-file.el

(put (quote epa-file-encrypt-to) (quote safe-local-variable) (lambda (val) (or (stringp val) (and (listp val) (catch (quote safe) (mapc (lambda (elt) (unless (stringp elt) (throw (quote safe) nil))) val) t)))))

(put (quote epa-file-encrypt-to) (quote permanent-local) t)

(autoload (quote epa-file-enable) "epa-file" "\
Not documented

\(fn)" t nil)

(autoload (quote epa-file-disable) "epa-file" "\
Not documented

\(fn)" t nil)

;;;***

;;;### (autoloads (epa-mail-import-keys epa-mail-encrypt epa-mail-sign
;;;;;;  epa-mail-verify epa-mail-decrypt) "epa-mail" "site-lisp/epg/epa-mail.el"
;;;;;;  (17903 32178))
;;; Generated autoloads from site-lisp/epg/epa-mail.el

(autoload (quote epa-mail-decrypt) "epa-mail" "\
Decrypt OpenPGP armors in the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn)" t nil)

(autoload (quote epa-mail-verify) "epa-mail" "\
Verify OpenPGP cleartext signed messages in the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn)" t nil)

(autoload (quote epa-mail-sign) "epa-mail" "\
Sign the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn START END SIGNERS MODE)" t nil)

(autoload (quote epa-mail-encrypt) "epa-mail" "\
Encrypt the current buffer.
The buffer is expected to contain a mail message.

Don't use this command in Lisp programs!

\(fn START END RECIPIENTS SIGN SIGNERS)" t nil)

(autoload (quote epa-mail-import-keys) "epa-mail" "\
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
;;;;;;  epg-cancel epg-list-keys) "epg" "site-lisp/epg/epg.el" (17968
;;;;;;  18206))
;;; Generated autoloads from site-lisp/epg/epg.el

(autoload (quote epg-list-keys) "epg" "\
Return a list of epg-key objects matched with NAME.
If MODE is nil or 'public, only public keyring should be searched.
If MODE is t or 'secret, only secret keyring should be searched. 
Otherwise, only public keyring should be searched and the key
signatures should be included.
NAME is either a string or a list of strings.

\(fn CONTEXT &optional NAME MODE)" nil nil)

(autoload (quote epg-cancel) "epg" "\
Not documented

\(fn CONTEXT)" nil nil)

(autoload (quote epg-start-decrypt) "epg" "\
Initiate a decrypt operation on CIPHER.
CIPHER must be a file data object.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-decrypt-file' or `epg-decrypt-string' instead.

\(fn CONTEXT CIPHER)" nil nil)

(autoload (quote epg-decrypt-file) "epg" "\
Decrypt a file CIPHER and store the result to a file PLAIN.
If PLAIN is nil, it returns the result as a string.

\(fn CONTEXT CIPHER PLAIN)" nil nil)

(autoload (quote epg-decrypt-string) "epg" "\
Decrypt a string CIPHER and return the plain text.

\(fn CONTEXT CIPHER)" nil nil)

(autoload (quote epg-start-verify) "epg" "\
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

(autoload (quote epg-verify-file) "epg" "\
Verify a file SIGNATURE.
SIGNED-TEXT and PLAIN are also a file if they are specified.

For a detached signature, both SIGNATURE and SIGNED-TEXT should be
string.  For a normal or a cleartext signature, SIGNED-TEXT should be
nil.  In the latter case, if PLAIN is specified, the plaintext is
stored into the file after successful verification.

\(fn CONTEXT SIGNATURE &optional SIGNED-TEXT PLAIN)" nil nil)

(autoload (quote epg-verify-string) "epg" "\
Verify a string SIGNATURE.
SIGNED-TEXT is a string if it is specified.

For a detached signature, both SIGNATURE and SIGNED-TEXT should be
string.  For a normal or a cleartext signature, SIGNED-TEXT should be
nil.  In the latter case, this function returns the plaintext after
successful verification.

\(fn CONTEXT SIGNATURE &optional SIGNED-TEXT)" nil nil)

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
`epg-sign-file' or `epg-sign-string' instead.

\(fn CONTEXT PLAIN &optional MODE)" nil nil)

(autoload (quote epg-sign-file) "epg" "\
Sign a file PLAIN and store the result to a file SIGNATURE.
If SIGNATURE is nil, it returns the result as a string.
If optional 3rd argument MODE is t or 'detached, it makes a detached signature.
If it is nil or 'normal, it makes a normal signature.
Otherwise, it makes a cleartext signature.

\(fn CONTEXT PLAIN SIGNATURE &optional MODE)" nil nil)

(autoload (quote epg-sign-string) "epg" "\
Sign a string PLAIN and return the output as string.
If optional 3rd argument MODE is t or 'detached, it makes a detached signature.
If it is nil or 'normal, it makes a normal signature.
Otherwise, it makes a cleartext signature.

\(fn CONTEXT PLAIN &optional MODE)" nil nil)

(autoload (quote epg-start-encrypt) "epg" "\
Initiate an encrypt operation on PLAIN.
PLAIN is a data object.
If RECIPIENTS is nil, it performs symmetric encryption.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-encrypt-file' or `epg-encrypt-string' instead.

\(fn CONTEXT PLAIN RECIPIENTS &optional SIGN ALWAYS-TRUST)" nil nil)

(autoload (quote epg-encrypt-file) "epg" "\
Encrypt a file PLAIN and store the result to a file CIPHER.
If CIPHER is nil, it returns the result as a string.
If RECIPIENTS is nil, it performs symmetric encryption.

\(fn CONTEXT PLAIN RECIPIENTS CIPHER &optional SIGN ALWAYS-TRUST)" nil nil)

(autoload (quote epg-encrypt-string) "epg" "\
Encrypt a string PLAIN.
If RECIPIENTS is nil, it performs symmetric encryption.

\(fn CONTEXT PLAIN RECIPIENTS &optional SIGN ALWAYS-TRUST)" nil nil)

(autoload (quote epg-start-export-keys) "epg" "\
Initiate an export keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-export-keys-to-file' or `epg-export-keys-to-string' instead.

\(fn CONTEXT KEYS)" nil nil)

(autoload (quote epg-export-keys-to-file) "epg" "\
Extract public KEYS.

\(fn CONTEXT KEYS FILE)" nil nil)

(autoload (quote epg-export-keys-to-string) "epg" "\
Extract public KEYS and return them as a string.

\(fn CONTEXT KEYS)" nil nil)

(autoload (quote epg-start-import-keys) "epg" "\
Initiate an import keys operation.
KEYS is a data object.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-import-keys-from-file' or `epg-import-keys-from-string' instead.

\(fn CONTEXT KEYS)" nil nil)

(autoload (quote epg-import-keys-from-file) "epg" "\
Add keys from a file KEYS.

\(fn CONTEXT KEYS)" nil nil)

(autoload (quote epg-import-keys-from-string) "epg" "\
Add keys from a string KEYS.

\(fn CONTEXT KEYS)" nil nil)

(autoload (quote epg-start-receive-keys) "epg" "\
Initiate a receive key operation.
KEY-ID-LIST is a list of key IDs.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-generate-key-from-file' or `epg-generate-key-from-string' instead.

\(fn CONTEXT KEY-ID-LIST)" nil nil)

(autoload (quote epg-receive-keys) "epg" "\
Add keys from server.
KEYS is a list of key IDs

\(fn CONTEXT KEYS)" nil nil)

(defalias (quote epg-import-keys-from-server) (quote epg-receive-keys))

(autoload (quote epg-start-delete-keys) "epg" "\
Initiate an delete keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-delete-keys' instead.

\(fn CONTEXT KEYS &optional ALLOW-SECRET)" nil nil)

(autoload (quote epg-delete-keys) "epg" "\
Delete KEYS from the key ring.

\(fn CONTEXT KEYS &optional ALLOW-SECRET)" nil nil)

(autoload (quote epg-start-sign-keys) "epg" "\
Initiate an sign keys operation.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-sign-keys' instead.

\(fn CONTEXT KEYS &optional LOCAL)" nil nil)

(autoload (quote epg-sign-keys) "epg" "\
Sign KEYS from the key ring.

\(fn CONTEXT KEYS &optional LOCAL)" nil nil)

(autoload (quote epg-start-generate-key) "epg" "\
Initiate a key generation.
PARAMETERS specifies parameters for the key.

If you use this function, you will need to wait for the completion of
`epg-gpg-program' by using `epg-wait-for-completion' and call
`epg-reset' to clear a temporaly output file.
If you are unsure, use synchronous version of this function
`epg-generate-key-from-file' or `epg-generate-key-from-string' instead.

\(fn CONTEXT PARAMETERS)" nil nil)

(autoload (quote epg-generate-key-from-file) "epg" "\
Generate a new key pair.
PARAMETERS is a file which tells how to create the key.

\(fn CONTEXT PARAMETERS)" nil nil)

(autoload (quote epg-generate-key-from-string) "epg" "\
Generate a new key pair.
PARAMETERS is a string which tells how to create the key.

\(fn CONTEXT PARAMETERS)" nil nil)

;;;***

;;;### (autoloads (epg-expand-group epg-check-configuration epg-configuration)
;;;;;;  "epg-config" "site-lisp/epg/epg-config.el" (17853 29144))
;;; Generated autoloads from site-lisp/epg/epg-config.el

(autoload (quote epg-configuration) "epg-config" "\
Return a list of internal configuration parameters of `epg-gpg-program'.

\(fn)" nil nil)

(autoload (quote epg-check-configuration) "epg-config" "\
Verify that a sufficient version of GnuPG is installed.

\(fn CONFIG &optional MINIMUM-VERSION)" nil nil)

(autoload (quote epg-expand-group) "epg-config" "\
Look at CONFIG and try to expand GROUP.

\(fn CONFIG GROUP)" nil nil)

;;;***

;;;### (autoloads (eshell-toggle eshell-toggle-cd) "esh-toggle" "esh-toggle.el"
;;;;;;  (15542 40456))
;;; Generated autoloads from esh-toggle.el

(autoload (quote eshell-toggle-cd) "esh-toggle" "\
Calls `eshell-toggle' with a prefix argument.
See the command `eshell-toggle'

\(fn)" t nil)

(autoload (quote eshell-toggle) "esh-toggle" "\
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
Replace standard eval-expression command with enhanced eval-expr.

\(fn)" t nil)

(autoload (quote eval-expr) "eval-expr" "\
Evaluate EXPRESSION and print value in minibuffer, temp, or current buffer.
A temp output buffer is used if there is more than one line in the
evaluated result.
If invoked with a prefix arg, or second lisp argument EE::INSERT-VALUE is
non-nil, then insert final value into the current buffer at point.

Value is also consed on to front of the variable `values'.

\(fn EE::EXPRESSION &optional EE::INSERT-VALUE)" t nil)

;;;***

;;;### (autoloads (find-and-load-library find-library) "find-library"
;;;;;;  "site-lisp/find-library.el" (18084 9489))
;;; Generated autoloads from site-lisp/find-library.el

(autoload (quote find-library) "find-library" "\
Find a library file with completion.

\(fn)" t nil)

(autoload (quote find-and-load-library) "find-library" "\
Find a library file with completion.

\(fn)" t nil)

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
is also deleted.

\(fn)" t nil)

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
\\{groovy-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads (enable-lui-irc-colors) "lui-irc-colors" "site-lisp/circe/lui-irc-colors.el"
;;;;;;  (18087 33243))
;;; Generated autoloads from site-lisp/circe/lui-irc-colors.el

(autoload (quote enable-lui-irc-colors) "lui-irc-colors" "\
Enable IRC color interpretation for Lui.

\(fn)" t nil)

;;;***

;;;### (autoloads (mime-w3m-preview-text/html) "mime-w3m" "site-lisp/emacs-w3m/mime-w3m.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/mime-w3m.el

(autoload (quote mime-w3m-preview-text/html) "mime-w3m" "\
Not documented

\(fn ENTITY SITUATION)" nil nil)

;;;***

;;;### (autoloads (nnml-generate-nov-databases) "nnml" "nnml.el"
;;;;;;  (18208 5033))
;;; Generated autoloads from nnml.el

(autoload (quote nnml-generate-nov-databases) "nnml" "\
Generate NOV databases in all nnml directories.

\(fn &optional SERVER)" t nil)

;;;***

;;;### (autoloads (nxml-glyph-display-string) "nxml-glyph" "site-lisp/nxml-mode/nxml-glyph.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/nxml-glyph.el

(autoload (quote nxml-glyph-display-string) "nxml-glyph" "\
Return a string that can display a glyph for Unicode code-point N.
FACE gives the face that will be used for displaying the string.
Return nil if the face cannot display a glyph for N.

\(fn N FACE)" nil nil)

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
\\[customize-group] nxml RET.

\(fn)" t nil)

;;;***

;;;### (autoloads (nxml-enable-unicode-char-name-sets) "nxml-uchnm"
;;;;;;  "site-lisp/nxml-mode/nxml-uchnm.el" (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/nxml-uchnm.el

(autoload (quote nxml-enable-unicode-char-name-sets) "nxml-uchnm" "\
Enable the use of Unicode standard names for characters.
The Unicode blocks for which names are enabled is controlled by
the variable `nxml-enabled-unicode-blocks'.

\(fn)" t nil)

;;;***

;;;### (autoloads (octet-mime-setup mime-view-octet mime-preview-octet
;;;;;;  octet-find-file octet-buffer) "octet" "site-lisp/emacs-w3m/octet.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/octet.el

(autoload (quote octet-buffer) "octet" "\
View octet-stream content according to `octet-type-filter-alist'.
Optional NAME is the filename.
If optional CONTENT-TYPE is specified, it is used for type guess.

\(fn &optional NAME CONTENT-TYPE)" t nil)

(autoload (quote octet-find-file) "octet" "\
Find FILE with octet-stream decoding.

\(fn FILE)" t nil)

(autoload (quote mime-preview-octet) "octet" "\
A method for mime-view to preview octet message.

\(fn ENTITY SITUATION)" nil nil)

(autoload (quote mime-view-octet) "octet" "\
A method for mime-view to display octet message.

\(fn ENTITY SITUATION)" nil nil)

(autoload (quote octet-mime-setup) "octet" "\
Octet setting for MIME module.

\(fn)" nil nil)

;;;***

;;;### (autoloads (pcomplete/scp pcomplete/ssh) "pcmpl-ssh" "site-lisp/pcmpl-ssh.el"
;;;;;;  (18261 64359))
;;; Generated autoloads from site-lisp/pcmpl-ssh.el

(autoload (quote pcomplete/ssh) "pcmpl-ssh" "\
Completion rules for the `ssh' command.

\(fn)" nil nil)

(autoload (quote pcomplete/scp) "pcmpl-ssh" "\
Completion rules for the `scp' command.

Includes files as well as host names followed by a colon.

\(fn)" nil nil)

;;;***

;;;### (autoloads (run-prolog mercury-mode prolog-mode) "prolog"
;;;;;;  "site-lisp/prolog.el" (18145 21220))
;;; Generated autoloads from site-lisp/prolog.el

(autoload (quote prolog-mode) "prolog" "\
Major mode for editing Prolog code.

Blank lines and `%%...' separate paragraphs.  `%'s starts a comment
line and comments can also be enclosed in /* ... */.

If an optional argument SYSTEM is non-nil, set up mode for the given system.

To find out what version of Prolog mode you are running, enter
`\\[prolog-mode-version]'.

Commands:
\\{prolog-mode-map}
Entry to this mode calls the value of `prolog-mode-hook'
if that value is non-nil.

\(fn &optional SYSTEM)" t nil)

(autoload (quote mercury-mode) "prolog" "\
Major mode for editing Mercury programs.
Actually this is just customized `prolog-mode'.

\(fn)" t nil)

(autoload (quote run-prolog) "prolog" "\
Run an inferior Prolog process, input and output via buffer *prolog*.
With prefix argument ARG, restart the Prolog process if running before.

\(fn ARG)" t nil)

;;;***

;;;### (autoloads (svn-status svn-checkout) "psvn" "site-lisp/psvn.el"
;;;;;;  (18206 14650))
;;; Generated autoloads from site-lisp/psvn.el

(autoload (quote svn-checkout) "psvn" "\
Run svn checkout REPOS-URL PATH.

\(fn REPOS-URL PATH)" t nil)
 (defalias 'svn-examine 'svn-status)

(autoload (quote svn-status) "psvn" "\
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

;;;### (autoloads (remember-destroy remember-buffer remember-clipboard
;;;;;;  remember-region remember-other-frame remember) "remember"
;;;;;;  "site-lisp/remember/remember.el" (18144 32674))
;;; Generated autoloads from site-lisp/remember/remember.el

(autoload (quote remember) "remember" "\
Remember an arbitrary piece of data.
With a prefix, uses the region as INITIAL.

\(fn &optional INITIAL)" t nil)

(autoload (quote remember-other-frame) "remember" "\
Not documented

\(fn &optional INITIAL)" t nil)

(autoload (quote remember-region) "remember" "\
Remember the data from BEG to END.
If called from within the remember buffer, BEG and END are ignored,
and the entire buffer will be remembered.

This function is meant to be called from the *Remember* buffer.
If you want to remember a region, supply a universal prefix to
`remember' instead. For example: C-u M-x remember.

\(fn &optional BEG END)" t nil)

(autoload (quote remember-clipboard) "remember" "\
Remember the contents of the current clipboard.
Most useful for remembering things from Netscape or other X Windows
application.

\(fn)" t nil)

(autoload (quote remember-buffer) "remember" "\
Remember the contents of the current buffer.

\(fn)" t nil)

(autoload (quote remember-destroy) "remember" "\
Destroy the current *Remember* buffer.

\(fn)" t nil)

;;;***

;;;### (autoloads (remember-bbdb-store-in-mailbox) "remember-bbdb"
;;;;;;  "site-lisp/remember/remember-bbdb.el" (18090 5625))
;;; Generated autoloads from site-lisp/remember/remember-bbdb.el

(autoload (quote remember-bbdb-store-in-mailbox) "remember-bbdb" "\
Store remember data as if it were incoming mail.
In which case `remember-mailbox' should be the name of the mailbox.
Each piece of psuedo-mail created will have an `X-Todo-Priority'
field, for the purpose of appropriate splitting.

\(fn)" nil nil)

;;;***

;;;### (autoloads (remember-location remember-url) "remember-bibl"
;;;;;;  "site-lisp/remember/remember-bibl.el" (18090 5625))
;;; Generated autoloads from site-lisp/remember/remember-bibl.el

(autoload (quote remember-url) "remember-bibl" "\
Remember a URL in `bibl-mode' that is being visited with w3.

\(fn)" t nil)

(autoload (quote remember-location) "remember-bibl" "\
Remember a bookmark location in `bibl-mode'.

\(fn)" t nil)

;;;***

;;;### (autoloads (remember-blosxom) "remember-blosxom" "site-lisp/remember/remember-blosxom.el"
;;;;;;  (18090 5625))
;;; Generated autoloads from site-lisp/remember/remember-blosxom.el

(autoload (quote remember-blosxom) "remember-blosxom" "\
Remember this text to a blosxom story.
This function can be added to `remember-handler-functions'.

\(fn)" nil nil)

;;;***

;;;### (autoloads (remember-emacs-wiki-journal-add-entry-maybe remember-emacs-wiki-journal-add-entry-auto
;;;;;;  remember-emacs-wiki-journal-add-entry) "remember-emacs-wiki-journal"
;;;;;;  "site-lisp/remember/remember-emacs-wiki-journal.el" (18090
;;;;;;  5625))
;;; Generated autoloads from site-lisp/remember/remember-emacs-wiki-journal.el

(autoload (quote remember-emacs-wiki-journal-add-entry) "remember-emacs-wiki-journal" "\
Prompt for category and heading and add entry.

\(fn)" nil nil)

(autoload (quote remember-emacs-wiki-journal-add-entry-auto) "remember-emacs-wiki-journal" "\
Add entry where the category is the first word and the heading the
rest of the words on the first line.

\(fn)" nil nil)

(autoload (quote remember-emacs-wiki-journal-add-entry-maybe) "remember-emacs-wiki-journal" "\
Like `remember-emacs-wiki-journal-add-entry-auto' but only adds
entry if the first line matches `emacs-wiki-journal-category-regexp'.

\(fn)" nil nil)

;;;***

;;;### (autoloads (rfcview-mode rfcview-customize) "rfcview" "site-lisp/rfcview.el"
;;;;;;  (18084 9490))
;;; Generated autoloads from site-lisp/rfcview.el

(autoload (quote rfcview-customize) "rfcview" "\
Not documented

\(fn)" t nil)

(autoload (quote rfcview-mode) "rfcview" "\
Major mode for viewing Internet RFCs.

http://www.neilvandyke.org/rfcview/

Key bindings:
\\{rfcview-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads (rng-c-load-schema) "rng-cmpct" "site-lisp/nxml-mode/rng-cmpct.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/rng-cmpct.el

(autoload (quote rng-c-load-schema) "rng-cmpct" "\
Load a schema in RELAX NG compact syntax from FILENAME.
Return a pattern.

\(fn FILENAME)" nil nil)

;;;***

;;;### (autoloads (rng-write-version rng-format-manual rng-byte-compile-load
;;;;;;  rng-update-autoloads) "rng-maint" "site-lisp/nxml-mode/rng-maint.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/rng-maint.el

(autoload (quote rng-update-autoloads) "rng-maint" "\
Update the autoloads in rng-auto.el.

\(fn)" t nil)

(autoload (quote rng-byte-compile-load) "rng-maint" "\
Byte-compile and load all of the RELAX NG library in an appropriate order.

\(fn)" t nil)

(autoload (quote rng-format-manual) "rng-maint" "\
Create manual.texi from manual.xml.

\(fn)" t nil)

(autoload (quote rng-write-version) "rng-maint" "\
Not documented

\(fn)" nil nil)

;;;***

;;;### (autoloads (rng-nxml-mode-init) "rng-nxml" "site-lisp/nxml-mode/rng-nxml.el"
;;;;;;  (18090 5620))
;;; Generated autoloads from site-lisp/nxml-mode/rng-nxml.el

(autoload (quote rng-nxml-mode-init) "rng-nxml" "\
Initialize `nxml-mode' to take advantage of `rng-validate-mode'.
This is typically called from `nxml-mode-hook'.
Validation will be enabled if `rng-nxml-auto-validate-flag' is non-nil.

\(fn)" t nil)

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
to use for finding the schema.

\(fn &optional ARG NO-CHANGE-SCHEMA)" t nil)

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
strings represent the same value, the returned objects must be equal.

\(fn NAME PARAMS)" nil nil)

;;;***

;;;### (autoloads (schedule-completion-time) "schedule" "schedule.el"
;;;;;;  (18205 36835))
;;; Generated autoloads from schedule.el

(autoload (quote schedule-completion-time) "schedule" "\
Advance THEN by COUNT seconds, skipping the weekends and holidays.
THEN must not already be in a holiday or non-worktime.  Make sure that
`schedule-align-now' is called at least once before this function ever
gets called.

\(fn THEN COUNT)" nil nil)

;;;***

;;;### (autoloads (session-initialize) "session" "site-lisp/session.el"
;;;;;;  (18084 9489))
;;; Generated autoloads from site-lisp/session.el

(autoload (quote session-initialize) "session" "\
Initialize package session and read previous session file.
Setup hooks and load `session-save-file', see `session-initialize'.  At
best, this function is called at the end of the Emacs startup, i.e., add
this function to `after-init-hook'.

\(fn &rest DUMMIES)" t nil)

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
variable.

\(fn INPUT-ARGS &optional BUFFER)" t nil)

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

(autoload (quote visit-url) "visit-url" "\
Not documented

\(fn &optional URL)" t nil)

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
POST-DATA and REFERER will be sent to the web server with a request.

\(fn URL &optional NO-DECODE NO-CACHE POST-DATA REFERER HANDLER)" nil nil)

(autoload (quote w3m-download) "w3m" "\
Not documented

\(fn URL &optional FILENAME NO-CACHE HANDLER)" t nil)

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

\[1] A note for the developers: ELEMENT is a history element which has
already been registered in the `w3m-history-flat' variable.  It is
corresponding to URL to be retrieved at this time, not for the url of
the current page.

\(fn URL &optional RELOAD CHARSET POST-DATA REFERER HANDLER ELEMENT)" t nil)

(autoload (quote w3m-goto-url-new-session) "w3m" "\
Visit World Wide Web pages in a new session.
If you invoke this command in the emacs-w3m buffer, the new session
will be created by copying the current session.  Otherwise, the new
session will start afresh.

\(fn URL &optional RELOAD CHARSET POST-DATA REFERER)" t nil)

(autoload (quote w3m-gohome) "w3m" "\
Go to the Home page.

\(fn)" t nil)

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
interactive command in the batch mode.

\(fn &optional URL NEW-SESSION INTERACTIVE-P)" t nil)

(autoload (quote w3m-browse-url) "w3m" "\
Ask emacs-w3m to browse URL.
NEW-SESSION specifies whether to create a new emacs-w3m session.  URL
defaults to the string looking like a url around the cursor position.
Pop to a window or a frame up according to `w3m-pop-up-windows' and
`w3m-pop-up-frames'.

\(fn URL &optional NEW-SESSION)" t nil)

(autoload (quote w3m-find-file) "w3m" "\
Function used to open FILE whose name is expressed in ordinary format.
The file name will be converted into the file: scheme.

\(fn FILE)" t nil)

(autoload (quote w3m-region) "w3m" "\
Render the region of the current buffer between START and END.
URL specifies the address where the contents come from.  It can be
omitted or nil when the address is not identified.  CHARSET is used
for decoding the contents.  If it is nil, this function attempts to
parse the meta tag to extract the charset.

\(fn START END &optional URL CHARSET)" t nil)

;;;***

;;;### (autoloads (w3m-antenna w3m-about-antenna) "w3m-antenna" "site-lisp/emacs-w3m/w3m-antenna.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-antenna.el

(autoload (quote w3m-about-antenna) "w3m-antenna" "\
Not documented

\(fn URL &optional NO-DECODE NO-CACHE POST-DATA REFERER HANDLER)" nil nil)

(autoload (quote w3m-antenna) "w3m-antenna" "\
Report changes of WEB sites, which is specified in `w3m-antenna-sites'.

\(fn &optional NO-CACHE)" t nil)

;;;***

;;;### (autoloads (w3m-about-bookmark w3m-bookmark-view w3m-bookmark-add-current-url-group
;;;;;;  w3m-bookmark-add-current-url w3m-bookmark-add-this-url) "w3m-bookmark"
;;;;;;  "site-lisp/emacs-w3m/w3m-bookmark.el" (18090 5606))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-bookmark.el

(autoload (quote w3m-bookmark-add-this-url) "w3m-bookmark" "\
Add link under cursor to bookmark.

\(fn)" t nil)

(autoload (quote w3m-bookmark-add-current-url) "w3m-bookmark" "\
Add link of current page to bookmark.
With prefix, ask new url to add instead of current page.

\(fn &optional ARG)" t nil)

(autoload (quote w3m-bookmark-add-current-url-group) "w3m-bookmark" "\
Add link of the group of current urls to the bookmark.

\(fn)" t nil)

(autoload (quote w3m-bookmark-view) "w3m-bookmark" "\
Not documented

\(fn &optional RELOAD)" t nil)

(autoload (quote w3m-about-bookmark) "w3m-bookmark" "\
Not documented

\(fn &rest ARGS)" nil nil)

;;;***

;;;### (autoloads (w3m-about-cookie w3m-cookie w3m-cookie-get w3m-cookie-set
;;;;;;  w3m-cookie-shutdown) "w3m-cookie" "site-lisp/emacs-w3m/w3m-cookie.el"
;;;;;;  (18090 5606))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-cookie.el

(autoload (quote w3m-cookie-shutdown) "w3m-cookie" "\
Save cookies.

\(fn)" t nil)

(autoload (quote w3m-cookie-set) "w3m-cookie" "\
Register cookies which correspond to URL.
BEG and END should be an HTTP response header region on current buffer.

\(fn URL BEG END)" nil nil)

(autoload (quote w3m-cookie-get) "w3m-cookie" "\
Get a cookie field string which corresponds to the URL.

\(fn URL)" nil nil)

(autoload (quote w3m-cookie) "w3m-cookie" "\
Display cookies and enable you to manage them.

\(fn &optional NO-CACHE)" t nil)

(autoload (quote w3m-about-cookie) "w3m-cookie" "\
Make the html contents to display and to enable you to manage cookies.

\(fn URL &optional NO-DECODE NO-CACHE POST-DATA &rest ARGS)" nil nil)

;;;***

;;;### (autoloads (w3m-dtree w3m-about-dtree) "w3m-dtree" "site-lisp/emacs-w3m/w3m-dtree.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-dtree.el

(autoload (quote w3m-about-dtree) "w3m-dtree" "\
Not documented

\(fn URL &optional NODECODE ALLFILES &rest ARGS)" nil nil)

(autoload (quote w3m-dtree) "w3m-dtree" "\
Display directory tree on local file system.
If called with 'prefix argument', display all directorys and files.

\(fn ALLFILES PATH)" t nil)

;;;***

;;;### (autoloads (w3m-filter) "w3m-filter" "site-lisp/emacs-w3m/w3m-filter.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-filter.el

(autoload (quote w3m-filter) "w3m-filter" "\
Apply filtering rule of URL against a content in this buffer.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (w3m-fontify-forms) "w3m-form" "site-lisp/emacs-w3m/w3m-form.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-form.el

(autoload (quote w3m-fontify-forms) "w3m-form" "\
Process half-dumped data and fontify forms in this buffer.

\(fn)" nil nil)

;;;***

;;;### (autoloads (w3m-link-numbering-mode) "w3m-lnum" "site-lisp/emacs-w3m/w3m-lnum.el"
;;;;;;  (18090 5606))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-lnum.el

(autoload (quote w3m-link-numbering-mode) "w3m-lnum" "\
Minor mode to enable operations using link numbers.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (w3m-namazu w3m-about-namazu) "w3m-namazu" "site-lisp/emacs-w3m/w3m-namazu.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-namazu.el

(autoload (quote w3m-about-namazu) "w3m-namazu" "\
Not documented

\(fn URL &optional NO-DECODE NO-CACHE &rest ARGS)" nil nil)

(autoload (quote w3m-namazu) "w3m-namazu" "\
Search indexed files with Namazu.

\(fn INDEX QUERY &optional RELOAD)" t nil)

;;;***

;;;### (autoloads (w3m-perldoc w3m-about-perldoc) "w3m-perldoc" "site-lisp/emacs-w3m/w3m-perldoc.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-perldoc.el

(autoload (quote w3m-about-perldoc) "w3m-perldoc" "\
Not documented

\(fn URL &optional NO-DECODE NO-CACHE &rest ARGS)" nil nil)

(autoload (quote w3m-perldoc) "w3m-perldoc" "\
View Perl documents.

\(fn DOCNAME)" t nil)

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
and deactivate the mark.

\(fn SEARCH-ENGINE QUERY)" t nil)

(autoload (quote w3m-search-uri-replace) "w3m-search" "\
Generate query string for ENGINE from URI matched by last search.

\(fn URI ENGINE)" nil nil)

;;;***

;;;### (autoloads (w3m-replace-symbol) "w3m-symbol" "site-lisp/emacs-w3m/w3m-symbol.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-symbol.el

(autoload (quote w3m-replace-symbol) "w3m-symbol" "\
Not documented

\(fn)" nil nil)

;;;***

;;;### (autoloads (w3m-about-weather w3m-weather) "w3m-weather" "site-lisp/emacs-w3m/w3m-weather.el"
;;;;;;  (18090 5605))
;;; Generated autoloads from site-lisp/emacs-w3m/w3m-weather.el

(autoload (quote w3m-weather) "w3m-weather" "\
Display weather report.

\(fn AREA)" t nil)

(autoload (quote w3m-about-weather) "w3m-weather" "\
Not documented

\(fn URL NO-DECODE NO-CACHE POST-DATA REFERER HANDLER)" nil nil)

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
If LIMIT is non-nil, then do not consider characters beyond LIMIT.

\(fn &optional LIMIT)" nil nil)

;;;***

;;;### (autoloads (xray-features xray-hooks xray-faces xray-screen
;;;;;;  xray-overlay xray-marker xray-frame xray-window xray-buffer
;;;;;;  xray-position xray-symbol xray-click/key xray-on-mode-line-click
;;;;;;  xray-on-click xray-customize) "xray" "site-lisp/xray.el"
;;;;;;  (18243 36009))
;;; Generated autoloads from site-lisp/xray.el

(autoload (quote xray-customize) "xray" "\
Customize xray group.

\(fn)" t nil)

(autoload (quote xray-on-click) "xray" "\
Give help on an object clicked with the mouse.

\(fn CLICK)" t nil)

(autoload (quote xray-on-mode-line-click) "xray" "\
Give help on the mode line.

\(fn CLICK)" t nil)

(autoload (quote xray-click/key) "xray" "\
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

(autoload (quote xray-symbol) "xray" "\
Display SYMBOL internal cells in a temporary buffer.

That is, displays the symbol name cell, the symbol function cell, the symbol
value cell and the symbol property list cell.  It's also displayed the key
bindings associated with symbol (if any), from which file it was loaded and
some apropos information.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-symbol' (non-nil)
or `xray-help-symbol' (nil).

See `xray-customize' for customization.

\(fn SYMBOL &optional BUFFER)" t nil)

(autoload (quote xray-position) "xray" "\
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

(autoload (quote xray-buffer) "xray" "\
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

(autoload (quote xray-window) "xray" "\
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

(autoload (quote xray-frame) "xray" "\
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

(autoload (quote xray-marker) "xray" "\
Display MARKER internal cells in a temporary buffer.

If MARKER is nil, it's used (mark t).

That is, displays the associated buffer, the position, the insertion type, the
mark, the beginning of region, the end of region, some variable related to
marker, hooks and the mark ring.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-marker'
\(non-nil) or `xray-help-marker' (nil).

See `xray-customize' for customization.

\(fn &optional MARKER)" t nil)

(autoload (quote xray-overlay) "xray" "\
Display OVERLAY internal cells in a temporary buffer.

If OVERLAY is nil, try to use the overlay on current buffer position (if any).

That is, displays the buffer associated, the start position, the end position,
the overlay list and the property list.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-overlay'
\(non-nil) or `xray-help-overlay' (nil).

See `xray-customize' for customization.

\(fn &optional OVERLAY)" t nil)

(autoload (quote xray-screen) "xray" "\
Display SCREEN capabilities in a temporary buffer.

If SCREEN is nil, use the first screen given by `x-display-list'.

That's, displays SCREEN capabilities, some variables and hooks related to
screen, and the display list.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-screen'
\(non-nil) or `xray-help-screen' (nil).

See `xray-customize' for customization.

\(fn &optional SCREEN)" t nil)

(autoload (quote xray-faces) "xray" "\
Display all defined faces.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-faces'
\(non-nil) or `xray-help-faces' (nil).

See `xray-customize' for customization.

\(fn)" t nil)

(autoload (quote xray-hooks) "xray" "\
Display all standard hooks and other defined hooks.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-hooks'
\(non-nil) or `xray-help-hooks' (nil).

See `xray-customize' for customization.

\(fn)" t nil)

(autoload (quote xray-features) "xray" "\
Display all features loaded.

It uses `xray-electric-p' to decide if it invokes `xray-ehelp-features'
\(non-nil) or `xray-help-features' (nil).

See `xray-customize' for customization.

\(fn)" t nil)

;;;***

;;;### (autoloads nil nil ("am-send.el" "cus-dirs.el" "flyspell-ext.el"
;;;;;;  "initsplit.el" "org-crypt.el" "org-devonthink.el" "org-message.el"
;;;;;;  "regex-tool.el" "site-lisp/anything.el" "site-lisp/anything.el"
;;;;;;  "site-lisp/circe/circe-auto.el" "site-lisp/circe/circe-chanop.el"
;;;;;;  "site-lisp/circe/circe-e21.el" "site-lisp/circe/circe-xemacs.el"
;;;;;;  "site-lisp/circe/incomplete.el" "site-lisp/circe/lcs.el"
;;;;;;  "site-lisp/circe/lui-format.el" "site-lisp/circe/lui-logging.el"
;;;;;;  "site-lisp/circe/lui-xemacs.el" "site-lisp/circe/lui.el"
;;;;;;  "site-lisp/circe/tracking.el" "site-lisp/crypt++.el" "site-lisp/crypt++.el"
;;;;;;  "site-lisp/csharp-mode.el" "site-lisp/csharp-mode.el" "site-lisp/css-mode.el"
;;;;;;  "site-lisp/css-mode.el" "site-lisp/csv.el" "site-lisp/csv.el"
;;;;;;  "site-lisp/dedicated.el" "site-lisp/dedicated.el" "site-lisp/dvc-snapshot/dvc-load-install.el"
;;;;;;  "site-lisp/dvc-snapshot/dvc-load.el" "site-lisp/edit-env.el"
;;;;;;  "site-lisp/edit-env.el" "site-lisp/emacs-w3m/mew-w3m.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-bitmap.el" "site-lisp/emacs-w3m/w3m-bug.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-ccl.el" "site-lisp/emacs-w3m/w3m-e19.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-e20.el" "site-lisp/emacs-w3m/w3m-e21.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-favicon.el" "site-lisp/emacs-w3m/w3m-fsf.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-hist.el" "site-lisp/emacs-w3m/w3m-image.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-load.el" "site-lisp/emacs-w3m/w3m-om.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-proc.el" "site-lisp/emacs-w3m/w3m-rss.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-tabmenu.el" "site-lisp/emacs-w3m/w3m-ucs.el"
;;;;;;  "site-lisp/emacs-w3m/w3m-util.el" "site-lisp/emacs-w3m/w3m-xmas.el"
;;;;;;  "site-lisp/emacs-w3m/w3mhack.el" "site-lisp/epg/epa-dired.el"
;;;;;;  "site-lisp/epg/epa-setup.el" "site-lisp/epg/epg-package-info.el"
;;;;;;  "site-lisp/fdb.el" "site-lisp/fdb.el" "site-lisp/fm.el" "site-lisp/fm.el"
;;;;;;  "site-lisp/hide-search.el" "site-lisp/hide-search.el" "site-lisp/include.el"
;;;;;;  "site-lisp/include.el" "site-lisp/indentx.el" "site-lisp/indentx.el"
;;;;;;  "site-lisp/indirect.el" "site-lisp/indirect.el" "site-lisp/ipython.el"
;;;;;;  "site-lisp/ipython.el" "site-lisp/lisppaste.el" "site-lisp/lisppaste.el"
;;;;;;  "site-lisp/marker-visit.el" "site-lisp/marker-visit.el" "site-lisp/mdfind.el"
;;;;;;  "site-lisp/mdfind.el" "site-lisp/message-x.el" "site-lisp/message-x.el"
;;;;;;  "site-lisp/mudel.el" "site-lisp/mudel.el" "site-lisp/multi-region.el"
;;;;;;  "site-lisp/multi-region.el" "site-lisp/narrow-stack.el" "site-lisp/narrow-stack.el"
;;;;;;  "site-lisp/nxml-mode/nxml-enc.el" "site-lisp/nxml-mode/nxml-maint.el"
;;;;;;  "site-lisp/nxml-mode/nxml-ns.el" "site-lisp/nxml-mode/nxml-outln.el"
;;;;;;  "site-lisp/nxml-mode/nxml-parse.el" "site-lisp/nxml-mode/nxml-rap.el"
;;;;;;  "site-lisp/nxml-mode/nxml-util.el" "site-lisp/nxml-mode/rng-auto.el"
;;;;;;  "site-lisp/nxml-mode/rng-dt.el" "site-lisp/nxml-mode/rng-loc.el"
;;;;;;  "site-lisp/nxml-mode/rng-match.el" "site-lisp/nxml-mode/rng-parse.el"
;;;;;;  "site-lisp/nxml-mode/rng-pttrn.el" "site-lisp/nxml-mode/rng-uri.el"
;;;;;;  "site-lisp/nxml-mode/rng-util.el" "site-lisp/nxml-mode/xsd-regexp.el"
;;;;;;  "site-lisp/org-log.el" "site-lisp/org-log.el" "site-lisp/pabbrev.el"
;;;;;;  "site-lisp/pabbrev.el" "site-lisp/paredit.el" "site-lisp/paredit.el"
;;;;;;  "site-lisp/redshank.el" "site-lisp/redshank.el" "site-lisp/remember/read-file-name.el"
;;;;;;  "site-lisp/remember/remember-autoloads.el" "site-lisp/remember/remember-diary.el"
;;;;;;  "site-lisp/remember/remember-experimental.el" "site-lisp/remember/remember-planner.el"
;;;;;;  "site-lisp/repeat-insert.el" "site-lisp/repeat-insert.el"
;;;;;;  "site-lisp/slime/hyperspec.el" "site-lisp/slime/slime-autoloads.el"
;;;;;;  "site-lisp/slime/slime.el" "site-lisp/snippet.el" "site-lisp/snippet.el"
;;;;;;  "site-lisp/sudo-save.el" "site-lisp/sudo-save.el" "site-lisp/trac-wiki.el"
;;;;;;  "site-lisp/trac-wiki.el" "site-lisp/vkill.el" "site-lisp/vkill.el"
;;;;;;  "site-lisp/wcount.el" "site-lisp/wcount.el" "site-lisp/xml-rpc.el"
;;;;;;  "site-lisp/xml-rpc.el") (18268 29976 185537))

;;;***

;;;### (autoloads (c-includes c-includes-current-file c-includes-add-binding)
;;;;;;  "c-includes" "c-includes.el" (14822 57866))
;;; Generated autoloads from c-includes.el

(autoload (quote c-includes-add-binding) "c-includes" "\
Set binding for C-c C-i in cc-mode.

\(fn)" nil nil)

(autoload (quote c-includes-current-file) "c-includes" "\
Find all of the header file included by the current file.

\(fn &optional REGEXP)" t nil)

(autoload (quote c-includes) "c-includes" "\
Find all of the header files included by FILENAME.
REGEXP, if non-nil, is a regular expression to search for within
FILENAME and the files that it includes.  The output will be
structured in the same order that the compiler will see it, enabling
you determine order of occurrence.

\(fn FILENAME &optional REGEXP)" t nil)

;;;***
