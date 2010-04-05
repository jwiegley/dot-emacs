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
;;;;;;  (18429 49075))
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

;;;### (autoloads (edit-variable) "edit-var" "site-lisp/edit-var.el"
;;;;;;  (18429 49075))
;;; Generated autoloads from site-lisp/edit-var.el

(autoload 'edit-variable "edit-var" "\
Edit the value of VARIABLE.

\(fn VARIABLE)" t nil)

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

;;;### (autoloads (eshell-toggle eshell-toggle-cd) "esh-toggle" "site-lisp/eshell/esh-toggle.el"
;;;;;;  (18807 50473))
;;; Generated autoloads from site-lisp/eshell/esh-toggle.el

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

;;;### (autoloads (gist-fetch gist-region-or-buffer-private gist-region-or-buffer
;;;;;;  gist-buffer-private gist-buffer gist-region-private gist-region)
;;;;;;  "gist" "site-lisp/gist/gist.el" (19082 3388))
;;; Generated autoloads from site-lisp/gist/gist.el

(autoload 'gist-region "gist" "\
Post the current region as a new paste at gist.github.com
Copies the URL into the kill ring.

With a prefix argument, makes a private paste.

\(fn BEGIN END &optional PRIVATE)" t nil)

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

(autoload 'gist-fetch "gist" "\
Fetches a Gist and inserts it into a new buffer
If the Gist already exists in a buffer, switches to it

\(fn ID)" t nil)

;;;***

;;;### (autoloads (groovy-mode) "groovy" "site-lisp/groovy.el" (18901
;;;;;;  31841))
;;; Generated autoloads from site-lisp/groovy.el

(autoload 'groovy-mode "groovy" "\
Major mode for editing Groovy source text.

Key bindings:

\\{groovy-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads (haskell-c-mode) "haskell-c" "site-lisp/haskell-mode/haskell-c.el"
;;;;;;  (19385 28295))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-c.el

(add-to-list 'auto-mode-alist '("\\.hsc\\'" . haskell-c-mode))

(autoload 'haskell-c-mode "haskell-c" "\
Major mode for Haskell FFI files.

\(fn)" t nil)

;;;***

;;;### (autoloads (haskell-cabal-mode) "haskell-cabal" "site-lisp/haskell-mode/haskell-cabal.el"
;;;;;;  (19385 28295))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-cabal.el

(add-to-list 'auto-mode-alist '("\\.cabal\\'" . haskell-cabal-mode))

(autoload 'haskell-cabal-mode "haskell-cabal" "\
Major mode for Cabal package description files.

\(fn)" t nil)

;;;***

;;;### (autoloads (haskell-decl-scan-mode) "haskell-decl-scan" "site-lisp/haskell-mode/haskell-decl-scan.el"
;;;;;;  (19385 28295))
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

\(fn &optional ARG)" nil nil)

;;;***

;;;### (autoloads (haskell-doc-show-type haskell-doc-mode) "haskell-doc"
;;;;;;  "site-lisp/haskell-mode/haskell-doc.el" (19385 28295))
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
;;;;;;  (19385 28295))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-indent.el

(autoload 'haskell-indent-mode "haskell-indent" "\
``intelligent'' Haskell indentation mode that deals with
the layout rule of Haskell.  \\[haskell-indent-cycle] starts the cycle
which proposes new possibilities as long as the TAB key is pressed.
Any other key or mouse click terminates the cycle and is interpreted
except for RET which merely exits the cycle.
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

Note: \\[indent-region] which applies \\[haskell-indent-cycle] for each line
of the region also works but it stops and asks for any line having more
than one possible indentation.
Use TAB to cycle until the right indentation is found and then RET to go the
next line to indent.

Invokes `haskell-indent-hook' if not nil.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (haskell-hoogle literate-haskell-mode haskell-mode)
;;;;;;  "haskell-mode" "site-lisp/haskell-mode/haskell-mode.el" (19385
;;;;;;  28295))
;;; Generated autoloads from site-lisp/haskell-mode/haskell-mode.el

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
(add-to-list 'auto-mode-alist '("\\.\\(?:[gh]s\\|hi\\)\\'" . haskell-mode))
(add-to-list 'auto-mode-alist '("\\.l[gh]s\\'" . literate-haskell-mode))
(add-hook 'haskell-mode-hook 'turn-on-haskell-doc-mode)
(add-hook 'haskell-mode-hook 'turn-on-haskell-indent)

(autoload 'haskell-hoogle "haskell-mode" "\
Do a Hoogle search for QUERY.

\(fn QUERY)" t nil)

;;;***

;;;### (autoloads (inferior-haskell-find-haddock inferior-haskell-find-definition
;;;;;;  inferior-haskell-info inferior-haskell-type inferior-haskell-load-file
;;;;;;  switch-to-haskell) "inf-haskell" "site-lisp/haskell-mode/inf-haskell.el"
;;;;;;  (19385 28295))
;;; Generated autoloads from site-lisp/haskell-mode/inf-haskell.el

(defalias 'run-haskell 'switch-to-haskell)

(autoload 'switch-to-haskell "inf-haskell" "\
Show the inferior-haskell buffer.  Start the process if needed.

\(fn &optional ARG)" t nil)

(autoload 'inferior-haskell-load-file "inf-haskell" "\
Pass the current buffer's file to the inferior haskell process.
If prefix arg \\[universal-argument] is given, just reload the previous file.

\(fn &optional RELOAD)" t nil)

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

;;;### (autoloads (magit-status) "magit" "site-lisp/magit/magit.el"
;;;;;;  (19384 63855))
;;; Generated autoloads from site-lisp/magit/magit.el

(autoload 'magit-status "magit" "\
Not documented

\(fn DIR)" t nil)

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

;;;### (autoloads (planner-calendar-show planner-calendar-goto planner-search-notes
;;;;;;  planner-search-notes-with-body planner-create-task-from-buffer
;;;;;;  planner-create-low-priority-task-from-buffer planner-create-medium-priority-task-from-buffer
;;;;;;  planner-create-high-priority-task-from-buffer planner-goto-next-daily-page
;;;;;;  planner-goto-previous-daily-page planner-goto-tomorrow planner-goto-yesterday
;;;;;;  planner-goto-most-recent planner-goto-today planner-show
;;;;;;  planner-goto-plan-page planner-goto plan planner-create-note
;;;;;;  planner-resolve-position-url planner-browse-position-url
;;;;;;  planner-annotation-from-file-with-position planner-annotation-as-kill
;;;;;;  planner-mode) "planner" "site-lisp/planner/planner.el" (18573
;;;;;;  9421))
;;; Generated autoloads from site-lisp/planner/planner.el

(autoload 'planner-mode "planner" "\
A personal information manager for Emacs.
\\{planner-mode-map}

\(fn)" t nil)

(autoload 'planner-annotation-as-kill "planner" "\
Copy the current annotation into the kill ring.
When called with a prefix argument, prompt for the link display name.

\(fn ARG)" t nil)

(autoload 'planner-annotation-from-file-with-position "planner" "\
Return the filename and cursor position of the current buffer.
If `planner-annotation-use-relative-file' is t or a function that
returns non-nil, a relative link is used instead. If
`planner-annotation-strip-directory' is non-nil, the directory is
stripped from the link description.

\(fn)" nil nil)

(autoload 'planner-browse-position-url "planner" "\
If this is a position URL, jump to it.

\(fn URL)" nil nil)

(autoload 'planner-resolve-position-url "planner" "\
Replace ID with the blog, web or e-mail address of the BBDB record.

\(fn ID)" nil nil)

(autoload 'planner-create-note "planner" "\
Create a note to be remembered in PAGE (today if PAGE is nil).
If `planner-reverse-chronological-notes' is non-nil, create the
note at the beginning of the notes section; otherwise, add it to
the end.  Position point after the anchor.

\(fn &optional PAGE)" t nil)

(autoload 'plan "planner" "\
Start your planning for the day, carrying unfinished tasks forward.

If FORCE-DAYS is a positive integer, search that many days in the past
for unfinished tasks.
If FORCE-DAYS is 0 or t, scan all days.
If FORCE-DAYS is nil, use the value of `planner-carry-tasks-forward'
instead, except t means scan only yesterday.

\(fn &optional FORCE-DAYS)" t nil)

(autoload 'planner-goto "planner" "\
Jump to the planning page for DATE.
If no page for DATE exists and JUST-SHOW is non-nil, don't create
a new page - simply return nil.

\(fn DATE &optional JUST-SHOW)" t nil)

(autoload 'planner-goto-plan-page "planner" "\
Opens PAGE in the the `planner-project' wiki.
Use `planner-goto' if you want fancy calendar completion.

\(fn PAGE)" t nil)

(autoload 'planner-show "planner" "\
Show the plan page for DATE in another window, but don't select it.
If no page for DATE exists, return nil.

\(fn DATE)" t nil)

(autoload 'planner-goto-today "planner" "\
Jump to the planning page for today.

\(fn)" t nil)

(autoload 'planner-goto-most-recent "planner" "\
Go to the most recent day with planning info.

\(fn)" t nil)

(autoload 'planner-goto-yesterday "planner" "\
Goto the planner page DAYS before the currently displayed date.
If DAYS is nil, goes to the day immediately before the currently
displayed date.  If the current buffer is not a daily planner
page, calculates date based on today.

\(fn &optional DAYS)" t nil)

(autoload 'planner-goto-tomorrow "planner" "\
Goto the planner page DAYS after the currently displayed date.
If DAYS is nil, goes to the day immediately after the currently
displayed date.  If the current buffer is not a daily planner
page, calculates date based on today.

\(fn &optional DAYS)" t nil)

(autoload 'planner-goto-previous-daily-page "planner" "\
Goto the last plan page before the current date.
The current date is taken from the day page in the current
buffer, or today if the current buffer is not a planner page.
Does not create pages if they do not yet exist.

\(fn)" t nil)

(autoload 'planner-goto-next-daily-page "planner" "\
Goto the first plan page after the current date.
The current date is taken from the day page in the current
buffer, or today if the current buffer is not a planner page.
Does not create pages if they do not yet exist.

\(fn)" t nil)

(autoload 'planner-create-high-priority-task-from-buffer "planner" "\
Create a high-priority task based on this buffer.
Do not use this in LISP programs. Instead, set the value of
`planner-default-task-priority' and call `planner-create-task' or
`planner-create-task-from-buffer'.

\(fn)" t nil)

(autoload 'planner-create-medium-priority-task-from-buffer "planner" "\
Create a high-priority task based on this buffer.
Do not use this in LISP programs. Instead, set the value of
`planner-default-task-priority' and call `planner-create-task' or
`planner-create-task-from-buffer'.

\(fn)" t nil)

(autoload 'planner-create-low-priority-task-from-buffer "planner" "\
Create a high-priority task based on this buffer.
Do not use this in LISP programs. Instead, set the value of
`planner-default-task-priority' and call `planner-create-task' or
`planner-create-task-from-buffer'.

\(fn)" t nil)

(autoload 'planner-create-task-from-buffer "planner" "\
Create a new task named TITLE on DATE based on the current buffer.
With a prefix, do not prompt for PLAN-PAGE. The task is
associated with PLAN-PAGE if non-nil. If STATUS is non-nil, use
that as the status for the task. Otherwise, use
`planner-default-task-status'. See `planner-create-task' for more
information.

\(fn TITLE DATE &optional PLAN-PAGE STATUS)" t nil)

(autoload 'planner-search-notes-with-body "planner" "\
Return a buffer with all the notes returned by the query for REGEXP.
If called with a prefix argument, prompt for LIMIT and search days on
or after LIMIT. Display the body of the notes as well.

\(fn REGEXP LIMIT)" t nil)

(autoload 'planner-search-notes "planner" "\
Return a buffer with all the notes returned by the query for REGEXP.
If called with a prefix argument, prompt for LIMIT and search days on
or after LIMIT. If INCLUDE-BODY is non-nil, return the body as well.

\(fn REGEXP LIMIT &optional INCLUDE-BODY)" t nil)

(autoload 'planner-calendar-goto "planner" "\
Goto the plan page corresponding to the calendar date.

\(fn)" t nil)

(autoload 'planner-calendar-show "planner" "\
Show the plan page for the calendar date under point in another window.

\(fn)" t nil)

;;;***

;;;### (autoloads (planner-accomplishments-show planner-accomplishments-update
;;;;;;  planner-accomplishments-insinuate) "planner-accomplishments"
;;;;;;  "site-lisp/planner/planner-accomplishments.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-accomplishments.el

(autoload 'planner-accomplishments-insinuate "planner-accomplishments" "\
Automatically call `planner-accomplishments-update'.

\(fn)" nil nil)

(autoload 'planner-accomplishments-update "planner-accomplishments" "\
Update `planner-accomplishments-section'.

\(fn)" t nil)

(autoload 'planner-accomplishments-show "planner-accomplishments" "\
Display a buffer with the current page's accomplishment report.

\(fn)" t nil)

;;;***

;;;### (autoloads (planner-appt-use-tasks-and-schedule planner-appt-use-schedule
;;;;;;  planner-appt-use-tasks planner-appt-insinuate planner-appt-insinuate-if-today
;;;;;;  planner-appt-update) "planner-appt" "site-lisp/planner/planner-appt.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-appt.el

(autoload 'planner-appt-update "planner-appt" "\
Update the appointments on the current page.

\(fn)" t nil)

(autoload 'planner-appt-insinuate-if-today "planner-appt" "\
Not documented

\(fn)" nil nil)

(autoload 'planner-appt-insinuate "planner-appt" "\
Insinuate appointment alerting into planner mode.
Appointment methods should be set up first using one of:
  `planner-appt-use-tasks'
  `planner-appt-use-schedule'
  `planner-appt-use-tasks-and-schedule'.

\(fn)" nil nil)

(autoload 'planner-appt-use-tasks "planner-appt" "\
Use tasks to derive appointment alerts.

\(fn)" nil nil)

(autoload 'planner-appt-use-schedule "planner-appt" "\
Use the schedule to derive appointment alerts.

\(fn)" nil nil)

(autoload 'planner-appt-use-tasks-and-schedule "planner-appt" "\
Use both tasks and the schedule to derive appointment alerts.

\(fn)" nil nil)

;;;***

;;;### (autoloads (planner-bbdb-resolve-url planner-bbdb-browse-url
;;;;;;  planner-bbdb-annotation-from-bbdb) "planner-bbdb" "site-lisp/planner/planner-bbdb.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-bbdb.el

(autoload 'planner-bbdb-annotation-from-bbdb "planner-bbdb" "\
If called from a bbdb buffer, return an annotation.
Suitable for use in `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-bbdb-browse-url "planner-bbdb" "\
If this is a BBDB URL, jump to it.

\(fn URL)" nil nil)

(autoload 'planner-bbdb-resolve-url "planner-bbdb" "\
Replace ID with the blog, web or e-mail address of the BBDB record.

\(fn ID)" nil nil)

;;;***

;;;### (autoloads (planner-bibtex-browse-url planner-bibtex-annotation-old
;;;;;;  planner-bibtex-annotation-new) "planner-bibtex" "site-lisp/planner/planner-bibtex.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-bibtex.el

(autoload 'planner-bibtex-annotation-new "planner-bibtex" "\
Return an annotation for the current bibtex entry.

\(fn)" nil nil)

(autoload 'planner-bibtex-annotation-old "planner-bibtex" "\
Return the filename on the current line in dired.

\(fn)" nil nil)

(autoload 'planner-bibtex-browse-url "planner-bibtex" "\
If this is a Bibtex URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-bookmark-browse-url planner-bookmark-annotation-from-bookmark)
;;;;;;  "planner-bookmark" "site-lisp/planner/planner-bookmark.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-bookmark.el

(autoload 'planner-bookmark-annotation-from-bookmark "planner-bookmark" "\
If called from a bookmark buffer, return an annotation.
Suitable for use in `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-bookmark-browse-url "planner-bookmark" "\
If this is a bookmark URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-cyclic-create-tasks-maybe) "planner-cyclic"
;;;;;;  "site-lisp/planner/planner-cyclic.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-cyclic.el

(autoload 'planner-cyclic-create-tasks-maybe "planner-cyclic" "\
Maybe create cyclic tasks.
This will only create tasks for future dates or today.

\(fn)" t nil)

;;;***

;;;### (autoloads (planner-deadline-remove planner-deadline-change
;;;;;;  planner-deadline-update) "planner-deadline" "site-lisp/planner/planner-deadline.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-deadline.el

(autoload 'planner-deadline-update "planner-deadline" "\
Replace the text for all tasks with deadlines.
By default, deadlines are of the form {{Deadline: yyyy.mm.dd}}.
See `planner-deadline-regexp' for details.

\(fn)" t nil)

(autoload 'planner-deadline-change "planner-deadline" "\
Change the deadline of current task to DATE.
If DATE is nil, prompt for it.

\(fn DATE)" t nil)

(defalias 'planner-deadline-add 'planner-deadline-change)

(autoload 'planner-deadline-remove "planner-deadline" "\
Remove the deadline of the current task.

\(fn)" t nil)

;;;***

;;;### (autoloads (planner-diary-add-entry planner-diary-insinuate
;;;;;;  planner-diary-show-day-plan-or-diary planner-diary-insert-all-diaries-maybe
;;;;;;  planner-diary-insert-all-diaries planner-diary-update-section)
;;;;;;  "planner-diary" "site-lisp/planner/planner-diary.el" (18573
;;;;;;  9421))
;;; Generated autoloads from site-lisp/planner/planner-diary.el

(autoload 'planner-diary-update-section "planner-diary" "\
Update FILE's existing section TITLE by replacing existing text with TEXT.
If optional arg FORCE is non-nil, update the section even if it doesn't exist,
i.e. insert TITLE followed by TEXT at the top of the buffer.

\(fn FILE TITLE TEXT &optional FORCE)" nil nil)

(autoload 'planner-diary-insert-all-diaries "planner-diary" "\
Update all diary sections in a day plan file.
If FORCE is non-nil, insert a diary section even if there is no section header.
Inserts only diaries if the corresponding `planner-diary-use-*' variable is t.

\(fn &optional FORCE)" t nil)

(autoload 'planner-diary-insert-all-diaries-maybe "planner-diary" "\
Update all diary sections in a day plan file.
If the current day is in the past and FORCE is nil, don't do anything.
If FORCE is non-nil, insert a diary section even if there is no section header.
Inserts only diaries if the corresponding `planner-diary-use-*' variable is t.

\(fn &optional FORCE)" t nil)

(autoload 'planner-diary-show-day-plan-or-diary "planner-diary" "\
Show the day plan or diary entries for the date under point in calendar.
Add this to `calendar-move-hook' if you want to use it.  In that case you
should also `remove-hook' `planner-calendar-show' from `calendar-move-hook'.

\(fn)" t nil)

(autoload 'planner-diary-insinuate "planner-diary" "\
Hook Diary into Planner.
Automatically insert and update a Diary section in day plan files.
This adds a new key binding to `planner-mode-map':
C-cC-e updates the diary sections.

\(fn)" nil nil)

(defalias 'planner-insinuate-diary 'planner-diary-insinuate)

(autoload 'planner-diary-add-entry "planner-diary" "\
Prompt for a diary entry to add to `diary-file' on DATE.
Uses `planner-annotation-functions' to make hyperlinks.
TIME and TEXT are used in the description.

\(fn DATE TIME TEXT)" t nil)

;;;***

;;;### (autoloads (planner-erc-browse-url planner-erc-annotation-from-erc)
;;;;;;  "planner-erc" "site-lisp/planner/planner-erc.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-erc.el

(autoload 'planner-erc-annotation-from-erc "planner-erc" "\
Return an annotation for the current line.
This function can be added to `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-erc-browse-url "planner-erc" "\
If this is an IRC URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-export-diary planner-export-diary-setup
;;;;;;  planner-export-diary-future) "planner-export-diary" "site-lisp/planner/planner-export-diary.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-export-diary.el

(autoload 'planner-export-diary-future "planner-export-diary" "\
Exports only `planner-export-number-of-days' days of entries.
This function can be put into your `after-save-hook'.

\(fn)" t nil)

(autoload 'planner-export-diary-setup "planner-export-diary" "\
Add `planner-export-diary-future' to `after-save-hook' in planner buffers.
You can add this function to `planner-mode-hook'.

\(fn)" nil nil)

(autoload 'planner-export-diary "planner-export-diary" "\
Exports all the schedules or the ones from FROM to TO (inclusive).

\(fn &optional FROM TO)" t nil)

;;;***

;;;### (autoloads (planner-gnats-browse-url planner-gnats-annotation-from-gnats)
;;;;;;  "planner-gnats" "site-lisp/planner/planner-gnats.el" (18573
;;;;;;  9421))
;;; Generated autoloads from site-lisp/planner/planner-gnats.el

(autoload 'planner-gnats-annotation-from-gnats "planner-gnats" "\
If called from gnats-edit or gnats-view buffer, return an annotation.
Suitable for use in `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-gnats-browse-url "planner-gnats" "\
If this is a Gnats URL, view the pr (view-pr).

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-gnus-browse-url planner-gnus-annotation
;;;;;;  planner-gnus-insinuate) "planner-gnus" "site-lisp/planner/planner-gnus.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-gnus.el

(autoload 'planner-gnus-insinuate "planner-gnus" "\
Hook Planner into Gnus.

Adds special planner keybindings to the variable
`gnus-summary-article-map'. From a summary or article buffer, you
can type C-c C-t to call planner-create-task-from-buffer.

\(fn)" nil nil)

(autoload 'planner-gnus-annotation "planner-gnus" "\
Return an annotation from a Gnus summary or message buffer.
Suitable for use in `planner-annotation-functions'. If you
include this, you can omit `planner-gnus-annotation-from-summary'
and `planner-gnus-annotation-from-message'.

\(fn)" nil nil)

(autoload 'planner-gnus-browse-url "planner-gnus" "\
If this is a Gnus URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-id-setup planner-id-update-tasks-maybe
;;;;;;  planner-id-markup planner-id-add-task-id-maybe planner-id-jump-to-linked-task
;;;;;;  planner-id-find-task) "planner-id" "site-lisp/planner/planner-id.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-id.el

(autoload 'planner-id-find-task "planner-id" "\
Find task described by TASK-INFO. If POINT is non-nil, start from there.
If task is found, move point to line beginning and return non-nil.
If task is not found, leave point at POINT or the start of the buffer
and return nil.

\(fn TASK-INFO &optional POINT)" nil nil)

(autoload 'planner-id-jump-to-linked-task "planner-id" "\
Display the linked task page.
If INFO is specified, follow that task instead.

\(fn &optional INFO)" t nil)

(autoload 'planner-id-add-task-id-maybe "planner-id" "\
Add task ID if `planner-id-add-task-id-flag' is non-nil.

\(fn)" nil nil)

(autoload 'planner-id-markup "planner-id" "\
Highlight IDs as unobtrusive, clickable text from BEG to END.
VERBOSE is ignored.

\(fn BEG END &optional VERBOSE)" nil nil)

(autoload 'planner-id-update-tasks-maybe "planner-id" "\
Update tasks depending on the value of `planner-id-update-automatically'.

\(fn)" nil nil)

(autoload 'planner-id-setup "planner-id" "\
Hook into `planner-mode'.

\(fn)" nil nil)

;;;***

;;;### (autoloads (planner-ledger-insert-maybe) "planner-ledger"
;;;;;;  "site-lisp/planner/planner-ledger.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-ledger.el

(autoload 'planner-ledger-insert-maybe "planner-ledger" "\
Maybe insert ledger sections into a Planner page.

\(fn)" t nil)

;;;***

;;;### (autoloads (planner-lisp-browse-url) "planner-lisp" "site-lisp/planner/planner-lisp.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-lisp.el

(autoload 'planner-lisp-browse-url "planner-lisp" "\
If this is a LISP URL, evaluate it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-log-edit-add-note) "planner-log-edit"
;;;;;;  "site-lisp/planner/planner-log-edit.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-log-edit.el

(autoload 'planner-log-edit-add-note "planner-log-edit" "\
Add a note describing the commit to the current planner page.

\(fn)" nil nil)

;;;***

;;;### (autoloads (planner-mhe-browse-url planner-mhe-annotation)
;;;;;;  "planner-mhe" "site-lisp/planner/planner-mhe.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-mhe.el

(autoload 'planner-mhe-annotation "planner-mhe" "\
If called from a MH-E folder or message buffer, return an annotation.
Suitable for use in `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-mhe-browse-url "planner-mhe" "\
If this is a MH-E URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-multi-remove-task-from-pool) "planner-multi"
;;;;;;  "site-lisp/planner/planner-multi.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-multi.el

(autoload 'planner-multi-remove-task-from-pool "planner-multi" "\
Remove completed tasks from `planner-multi-copy-tasks-to-page' if that still leaves them linked.

\(fn OLD-STATUS NEW-STATUS)" nil nil)

;;;***

;;;### (autoloads (planner-notes-index-years planner-notes-index-months
;;;;;;  planner-notes-index-weeks planner-notes-index-days planner-notes-index
;;;;;;  planner-notes-index-month-table-tag planner-notes-index-tag)
;;;;;;  "planner-notes-index" "site-lisp/planner/planner-notes-index.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-notes-index.el

(autoload 'planner-notes-index-tag "planner-notes-index" "\
Mark up planner-notes-index tags.

Tags can be of the form:

  <planner-notes-index page=\"2004.03.02\">
  <planner-notes-index from=\"2004.03.01\" to=\"2004.03.31\">
  <planner-notes-index limit=\"10\">

\(fn TAG-BEG TAG-END ATTRS)" nil nil)

(autoload 'planner-notes-index-month-table-tag "planner-notes-index" "\
Mark up a month note index.  Tag is from BEG to END.
ATTRS is a list of attributes. \"Month\" is a yyyy.mm
 string (default: current month). \"Limit\" is the maximum number
 of items per day (default: all).

Examples:
<planner-notes-index-month-table month=\"2004.02\">
<planner-notes-index-month-table month=\"2004.02\" limit=\"4\">

\(fn BEG END ATTRS)" nil nil)

(autoload 'planner-notes-index "planner-notes-index" "\
Display a clickable notes index.
If called from a Lisp program, display only dates between FROM
and TO. With a prefix arg LIMIT, display only that number of
entries.

\(fn &optional FROM TO LIMIT)" t nil)

(autoload 'planner-notes-index-days "planner-notes-index" "\
Display an index of notes posted over the past few DAYS.
The list ends with the day of the current buffer or `planner-today'.

\(fn DAYS)" t nil)

(autoload 'planner-notes-index-weeks "planner-notes-index" "\
Display an index of notes posted over the past few WEEKS.
The list ends with the week of the current buffer or `planner-today'.
Weeks start from Sunday.

\(fn WEEKS)" t nil)

(autoload 'planner-notes-index-months "planner-notes-index" "\
Display an index of notes posted over the past few MONTHS.
The list ends with the month of the current buffer or `planner-today'.

\(fn MONTHS)" t nil)

(autoload 'planner-notes-index-years "planner-notes-index" "\
Display an index of notes posted over the past few YEARS.
The current year is included.

\(fn YEARS)" t nil)

;;;***

;;;### (autoloads (planner-psvn-log-edit-add-note planner-psvn-browse-url
;;;;;;  planner-annotation-from-psvn) "planner-psvn" "site-lisp/planner/planner-psvn.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-psvn.el

(autoload 'planner-annotation-from-psvn "planner-psvn" "\
If called from a psvn  *svn-log-view* buffer, return an annotation.
Suitable for use in `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-psvn-browse-url "planner-psvn" "\
If this is a psvn url, handle it.

\(fn URL)" nil nil)

(autoload 'planner-psvn-log-edit-add-note "planner-psvn" "\
Add a note describing the commit via psvn to the current planner page.

\(fn)" nil nil)

;;;***

;;;### (autoloads (planner-rank-update-all planner-rank-update-current-task
;;;;;;  planner-rank-change planner-sort-tasks-by-urgency planner-sort-tasks-by-importance
;;;;;;  planner-sort-tasks-by-rank) "planner-rank" "site-lisp/planner/planner-rank.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-rank.el

(autoload 'planner-sort-tasks-by-rank "planner-rank" "\
Sort tasks by status (_PDXC), priority (ABC), and rank.
Suitable for `planner-sort-tasks-key-function'

\(fn)" nil nil)

(autoload 'planner-sort-tasks-by-importance "planner-rank" "\
Sort tasks by status (_PDXC), priority (ABC), and importance.
Suitable for `planner-sort-tasks-key-function'

\(fn)" nil nil)

(autoload 'planner-sort-tasks-by-urgency "planner-rank" "\
Sort tasks by status (_PDXC), priority (ABC), and urgency.
Suitable for `planner-sort-tasks-key-function'

\(fn)" nil nil)

(autoload 'planner-rank-change "planner-rank" "\
Change the IMPORTANCE and URGENCY of the current task.
If there's deadline available, calculate urgency instead of asking
the user.

\(fn &optional IMPORTANCE URGENCY)" t nil)

(autoload 'planner-rank-update-current-task "planner-rank" "\
Re-calculate rank for the current task.

\(fn)" t nil)

(autoload 'planner-rank-update-all "planner-rank" "\
Re-calculate rank for all tasks in the current page.

\(fn)" t nil)

;;;***

;;;### (autoloads (planner-rdf-publish-index planner-rdf-publish-file)
;;;;;;  "planner-rdf" "site-lisp/planner/planner-rdf.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-rdf.el

(autoload 'planner-rdf-publish-file "planner-rdf" "\
Publish the file in RDF format, if called by PlannerMode.
Designed to be called via `muse-after-publish-hook'.
Non-Planner files, matching `muse-image-regexp' will be treated
differently. Currently they are simply ignored.

\(fn FILE)" t nil)

(autoload 'planner-rdf-publish-index "planner-rdf" "\
Create an index for the .rdf files.
Will be called via `muse-after-publish-hook'.
Creates index.rdf, a rdf:bag, with all existing .rdf files as
items.

\(fn)" t nil)

;;;***

;;;### (autoloads (planner-registry-initialize) "planner-registry"
;;;;;;  "site-lisp/planner/planner-registry.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-registry.el

(autoload 'planner-registry-initialize "planner-registry" "\
Set `planner-registry-alist' from `planner-registry-file'.
If `planner-registry-file' doesn't exist, create it.
If FROM-SCRATCH is non-nil, make the registry from scratch.

\(fn &optional FROM-SCRATCH)" t nil)

;;;***

;;;### (autoloads (planner-report-generate) "planner-report" "site-lisp/planner/planner-report.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-report.el

(autoload 'planner-report-generate "planner-report" "\
Generate a status report spanning a period from BEGIN to END.
BEGIN and END are in the format YYYY.MM.DD.

\(fn BEGIN END)" t nil)

;;;***

;;;### (autoloads (planner-rmail-browse-url planner-rmail-annotation-from-mail)
;;;;;;  "planner-rmail" "site-lisp/planner/planner-rmail.el" (18573
;;;;;;  9421))
;;; Generated autoloads from site-lisp/planner/planner-rmail.el

(autoload 'planner-rmail-annotation-from-mail "planner-rmail" "\
Return an annotation for the current message.
This function can be added to `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-rmail-browse-url "planner-rmail" "\
If this is an RMAIL URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-rss-add-note) "planner-rss" "site-lisp/planner/planner-rss.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-rss.el

(autoload 'planner-rss-add-note "planner-rss" "\
Export the current note using `planner-rss-add-item'.
If FEED is non-nil, add the note to the specified feed only.
Call with the interactive prefix in order to be prompted for FEED.

\(fn &optional FEED)" t nil)

;;;***

;;;### (autoloads (planner-schedule-show-end-project) "planner-schedule"
;;;;;;  "site-lisp/planner/planner-schedule.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-schedule.el

(autoload 'planner-schedule-show-end-project "planner-schedule" "\
Display the estimated project completion time.

\(fn)" t nil)

;;;***

;;;### (autoloads (planner-tasks-overview-show-summary planner-tasks-overview-jump
;;;;;;  planner-tasks-overview-jump-other-window planner-tasks-overview)
;;;;;;  "planner-tasks-overview" "site-lisp/planner/planner-tasks-overview.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-tasks-overview.el

(autoload 'planner-tasks-overview "planner-tasks-overview" "\
Display a task overview from START to END.

\(fn START END)" t nil)

(autoload 'planner-tasks-overview-jump-other-window "planner-tasks-overview" "\
Display the task under point in a different window.

\(fn)" t nil)

(autoload 'planner-tasks-overview-jump "planner-tasks-overview" "\
Display the task under point.

\(fn &optional OTHER-WINDOW)" t nil)

(autoload 'planner-tasks-overview-show-summary "planner-tasks-overview" "\
Count unscheduled, scheduled, and completed tasks for FILE-LIST.
If called with an interactive prefix, prompt for the page(s) to
display. planner-multi is required for multiple pages.

\(fn &optional FILE-LIST)" t nil)

;;;***

;;;### (autoloads (planner-colors-timeclock-report-tag) "planner-timeclock"
;;;;;;  "site-lisp/planner/planner-timeclock.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-timeclock.el

(autoload 'planner-colors-timeclock-report-tag "planner-timeclock" "\
Replace the region BEG to END with a timeclock report, colorizing
the result.

\(fn BEG END)" nil nil)

;;;***

;;;### (autoloads (planner-timeclock-summary-show-2 planner-timeclock-summary-show-range-filter
;;;;;;  planner-timeclock-summary-show-filter planner-timeclock-summary-show
;;;;;;  planner-timeclock-summary-update planner-timeclock-summary-insinuate)
;;;;;;  "planner-timeclock-summary" "site-lisp/planner/planner-timeclock-summary.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-timeclock-summary.el

(autoload 'planner-timeclock-summary-insinuate "planner-timeclock-summary" "\
Automatically call `planner-timeclock-summary-update'.
This function is called when the day page is saved.

\(fn)" nil nil)

(autoload 'planner-timeclock-summary-update "planner-timeclock-summary" "\
Update `planner-timeclock-summary-section'. in the current day page.
The section is updated only if it exists.

\(fn)" t nil)

(autoload 'planner-timeclock-summary-show "planner-timeclock-summary" "\
Display a buffer with the timeclock summary for DATE.
Date is a string in the form YYYY.MM.DD.

\(fn &optional DATE)" t nil)

(autoload 'planner-timeclock-summary-show-filter "planner-timeclock-summary" "\
Show a timeclock report filtered by FILTER for DATE.

If FILTER is a regexp, only plan pages matching that regexp will
be included. If FILTER is a function, it will be called with the
current timeclock item, and the line considered if the function
returned non-nil.

If called interactively, prompt for FILTER (a regexp) and DATE.
DATE is a string in the form YYYY.MM.DD and can be nil.

\(fn FILTER DATE)" t nil)

(autoload 'planner-timeclock-summary-show-range-filter "planner-timeclock-summary" "\
Show a timeclock report filtered by FILTER for START-DATE to END-DATE.

If FILTER is a regexp, only plan pages matching that regexp will
be included. If FILTER is a function, it will be called with the
current timeclock item, and the line considered if the function
returned non-nil.

If called interactively, prompt for FILTER (a regexp), START-DATE and END-DATE.
Dates are strings in the form YYYY.MM.DD and can be nil.

\(fn FILTER START-DATE END-DATE)" t nil)

(autoload 'planner-timeclock-summary-show-2 "planner-timeclock-summary" "\
Display a buffer with the timeclock summary for DATE.

Date is a string in the form YYYY.MM.DD. It will be asked if not
given.

\(fn &optional DATE)" t nil)

;;;***

;;;### (autoloads (planner-timeclock-summary-proj-report planner-timeclock-summary-proj-current
;;;;;;  planner-timeclock-summary-proj-all) "planner-timeclock-summary-proj"
;;;;;;  "site-lisp/planner/planner-timeclock-summary-proj.el" (18573
;;;;;;  9421))
;;; Generated autoloads from site-lisp/planner/planner-timeclock-summary-proj.el

(autoload 'planner-timeclock-summary-proj-all "planner-timeclock-summary-proj" "\
Insert time report for all projects in the current buffer.

\(fn)" t nil)

(autoload 'planner-timeclock-summary-proj-current "planner-timeclock-summary-proj" "\
Insert time report for the current project in the current buffer.

\(fn)" t nil)

(autoload 'planner-timeclock-summary-proj-report "planner-timeclock-summary-proj" "\
Insert time report for PROJECT in the current buffer.

\(fn PROJECT)" t nil)

;;;***

;;;### (autoloads (planner-trunk-tasks) "planner-trunk" "site-lisp/planner/planner-trunk.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-trunk.el

(autoload 'planner-trunk-tasks "planner-trunk" "\
Trunk(group) tasks in the current page.
Please refer the docstring of `planner-trunk-rule-list' for how
it works. You may want to call this function before you sort tasks
and/or after you create new tasks. If a prefix is given or FORCE is not
nil, trunk completed tasks together with non-completed tasks not
matter what the `planner-trunk-rule-list' said.

\(fn &optional FORCE)" t nil)

;;;***

;;;### (autoloads (planner-unix-mail-browse-url planner-unix-mail-annotation-from-mail)
;;;;;;  "planner-unix-mail" "site-lisp/planner/planner-unix-mail.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-unix-mail.el

(autoload 'planner-unix-mail-annotation-from-mail "planner-unix-mail" "\
Return an annotation for the current message.
This function can be added to `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-unix-mail-browse-url "planner-unix-mail" "\
If this is an UNIX-MAIL URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-vm-browse-url planner-vm-annotation-from-mail)
;;;;;;  "planner-vm" "site-lisp/planner/planner-vm.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-vm.el

(autoload 'planner-vm-annotation-from-mail "planner-vm" "\
Return an annotation for the current message.
This function can be added to `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-vm-browse-url "planner-vm" "\
If this is an VM URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-w3m-annotation-from-w3m) "planner-w3m"
;;;;;;  "site-lisp/planner/planner-w3m.el" (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-w3m.el

(autoload 'planner-w3m-annotation-from-w3m "planner-w3m" "\
If called from a w3m page, return an annotation.
Suitable for use in `planner-annotation-functions'.

\(fn)" nil nil)

;;;***

;;;### (autoloads (planner-wl-browse-url planner-wl-annotation-from-wl
;;;;;;  planner-wl-insinuate) "planner-wl" "site-lisp/planner/planner-wl.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-wl.el

(autoload 'planner-wl-insinuate "planner-wl" "\
Hook Planner into Wanderlust.
Add special planner keybindings to`wl-summary-mode-map'.
From the Wanderlust Summary view, you can type C-c C-t to create a task.

\(fn)" nil nil)

(autoload 'planner-wl-annotation-from-wl "planner-wl" "\
If called from wl, return an annotation.
Suitable for use in `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-wl-browse-url "planner-wl" "\
If this is a Wanderlust URL, jump to it.

\(fn URL)" nil nil)

;;;***

;;;### (autoloads (planner-xtla-log-edit-add-note planner-xtla-browse-url
;;;;;;  planner-annotation-from-xtla) "planner-xtla" "site-lisp/planner/planner-xtla.el"
;;;;;;  (18573 9421))
;;; Generated autoloads from site-lisp/planner/planner-xtla.el

(autoload 'planner-annotation-from-xtla "planner-xtla" "\
If called from a xtla buffer, return an annotation.
Suitable for use in `planner-annotation-functions'.

\(fn)" nil nil)

(autoload 'planner-xtla-browse-url "planner-xtla" "\
If this is a xtla url, handle it.

\(fn URL)" nil nil)

(autoload 'planner-xtla-log-edit-add-note "planner-xtla" "\
Provide `planner-log-edit'-like functionality for xtla.
This function is automatically called by `tla-commit-hook'.
See also `planner-xtla-log-edit-notice-commit-function'.

\(fn)" t nil)

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

;;;### (autoloads (remember-diary-extract-entries remember-clipboard
;;;;;;  remember-other-frame remember) "remember" "site-lisp/remember/remember.el"
;;;;;;  (18454 52960))
;;; Generated autoloads from site-lisp/remember/remember.el

(autoload 'remember "remember" "\
Remember an arbitrary piece of data.
INITIAL is the text to initially place in the *Remember* buffer,
or nil to bring up a blank *Remember* buffer.

With a prefix or a visible region, use the region as INITIAL.

\(fn &optional INITIAL)" t nil)

(autoload 'remember-other-frame "remember" "\
Call `remember' in another frame.

\(fn &optional INITIAL)" t nil)

(autoload 'remember-clipboard "remember" "\
Remember the contents of the current clipboard.
Most useful for remembering things from Netscape or other X Windows
application.

\(fn)" t nil)

(autoload 'remember-diary-extract-entries "remember" "\
Extract diary entries from the region.

\(fn)" nil nil)

;;;***

;;;### (autoloads (remember-bbdb-store-in-mailbox) "remember-bbdb"
;;;;;;  "site-lisp/remember/remember-bbdb.el" (18454 52960))
;;; Generated autoloads from site-lisp/remember/remember-bbdb.el

(autoload 'remember-bbdb-store-in-mailbox "remember-bbdb" "\
Store remember data as if it were incoming mail.
In which case `remember-mailbox' should be the name of the mailbox.
Each piece of psuedo-mail created will have an `X-Todo-Priority'
field, for the purpose of appropriate splitting.

\(fn)" nil nil)

;;;***

;;;### (autoloads (remember-location remember-url) "remember-bibl"
;;;;;;  "site-lisp/remember/remember-bibl.el" (18454 52960))
;;; Generated autoloads from site-lisp/remember/remember-bibl.el

(autoload 'remember-url "remember-bibl" "\
Remember a URL in `bibl-mode' that is being visited with w3.

\(fn)" t nil)

(autoload 'remember-location "remember-bibl" "\
Remember a bookmark location in `bibl-mode'.

\(fn)" t nil)

;;;***

;;;### (autoloads (remember-blosxom) "remember-blosxom" "site-lisp/remember/remember-blosxom.el"
;;;;;;  (18454 52960))
;;; Generated autoloads from site-lisp/remember/remember-blosxom.el

(autoload 'remember-blosxom "remember-blosxom" "\
Remember this text to a blosxom story.
This function can be added to `remember-handler-functions'.

\(fn)" nil nil)

;;;***

;;;### (autoloads (remember-emacs-wiki-journal-add-entry-maybe remember-emacs-wiki-journal-add-entry-auto
;;;;;;  remember-emacs-wiki-journal-add-entry) "remember-emacs-wiki-journal"
;;;;;;  "site-lisp/remember/remember-emacs-wiki-journal.el" (18454
;;;;;;  52960))
;;; Generated autoloads from site-lisp/remember/remember-emacs-wiki-journal.el

(autoload 'remember-emacs-wiki-journal-add-entry "remember-emacs-wiki-journal" "\
Prompt for category and heading and add entry.

\(fn)" nil nil)

(autoload 'remember-emacs-wiki-journal-add-entry-auto "remember-emacs-wiki-journal" "\
Add entry where the category is the first word and the heading the
rest of the words on the first line.

\(fn)" nil nil)

(autoload 'remember-emacs-wiki-journal-add-entry-maybe "remember-emacs-wiki-journal" "\
Like `remember-emacs-wiki-journal-add-entry-auto' but only adds
entry if the first line matches `emacs-wiki-journal-category-regexp'.

\(fn)" nil nil)

;;;***

;;;### (autoloads (remember-planner-append) "remember-planner" "site-lisp/remember/remember-planner.el"
;;;;;;  (18454 52960))
;;; Generated autoloads from site-lisp/remember/remember-planner.el

(autoload 'remember-planner-append "remember-planner" "\
Remember this text to PAGE or today's page.
This function can be added to `remember-handler-functions'.

\(fn &optional PAGE)" nil nil)

;;;***

;;;### (autoloads (rfcview-mode rfcview-customize) "rfcview" "site-lisp/rfcview.el"
;;;;;;  (18429 49078))
;;; Generated autoloads from site-lisp/rfcview.el

(autoload 'rfcview-customize "rfcview" "\
Not documented

\(fn)" t nil)

(autoload 'rfcview-mode "rfcview" "\
Major mode for viewing Internet RFCs.

http://www.neilvandyke.org/rfcview/

Key bindings:
\\{rfcview-mode-map}

\(fn)" t nil)

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

;;;### (autoloads (visit-url) "visit-url" "visit-url.el" (18429 49044))
;;; Generated autoloads from visit-url.el

(autoload 'visit-url "visit-url" "\
Not documented

\(fn &optional URL)" t nil)

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

;;;### (autoloads nil nil ("cus-dirs.el" "flyspell-ext.el" "org-crypt.el"
;;;;;;  "org-devonthink.el" "org-ext.el" "site-lisp/all.el" "site-lisp/apel/apel-ver.el"
;;;;;;  "site-lisp/apel/atype.el" "site-lisp/apel/broken.el" "site-lisp/apel/calist.el"
;;;;;;  "site-lisp/apel/emu-mule.el" "site-lisp/apel/emu.el" "site-lisp/apel/file-detect.el"
;;;;;;  "site-lisp/apel/filename.el" "site-lisp/apel/install.el"
;;;;;;  "site-lisp/apel/inv-18.el" "site-lisp/apel/inv-19.el" "site-lisp/apel/inv-xemacs.el"
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
;;;;;;  "site-lisp/ascii.el" "site-lisp/bookmark+.el" "site-lisp/breadcrumb.el"
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
;;;;;;  "site-lisp/cldoc.el" "site-lisp/column-marker.el" "site-lisp/crypt++.el"
;;;;;;  "site-lisp/crypt++.el" "site-lisp/csharp-mode.el" "site-lisp/csharp-mode.el"
;;;;;;  "site-lisp/css-mode.el" "site-lisp/css-mode.el" "site-lisp/csv-mode.el"
;;;;;;  "site-lisp/csv-mode.el" "site-lisp/csv.el" "site-lisp/csv.el"
;;;;;;  "site-lisp/cycbuf.el" "site-lisp/cycbuf.el" "site-lisp/dedicated.el"
;;;;;;  "site-lisp/dedicated.el" "site-lisp/diminish.el" "site-lisp/dired-tar.el"
;;;;;;  "site-lisp/edit-env.el" "site-lisp/edit-env.el" "site-lisp/edit-var.el"
;;;;;;  "site-lisp/elscreen.el" "site-lisp/elscreen.el" "site-lisp/epg/epa-dired.el"
;;;;;;  "site-lisp/epg/epa-setup.el" "site-lisp/epg/pgg-epg.el" "site-lisp/eshell/auto-autoloads.el"
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
;;;;;;  "site-lisp/eshell/esh-proc.el" "site-lisp/eshell/esh-util.el"
;;;;;;  "site-lisp/eshell/esh-var.el" "site-lisp/eshell/eshell-auto.el"
;;;;;;  "site-lisp/eval-expr.el" "site-lisp/find-library.el" "site-lisp/fm.el"
;;;;;;  "site-lisp/fm.el" "site-lisp/groovy.el" "site-lisp/haskell-mode/haskell-font-lock.el"
;;;;;;  "site-lisp/haskell-mode/haskell-ghci.el" "site-lisp/haskell-mode/haskell-hugs.el"
;;;;;;  "site-lisp/haskell-mode/haskell-simple-indent.el" "site-lisp/haskell-mode/haskell-site-file.el"
;;;;;;  "site-lisp/hide-search.el" "site-lisp/hide-search.el" "site-lisp/hs-lint.el"
;;;;;;  "site-lisp/hs-lint.el" "site-lisp/idomenu.el" "site-lisp/idomenu.el"
;;;;;;  "site-lisp/indirect.el" "site-lisp/indirect.el" "site-lisp/js2.el"
;;;;;;  "site-lisp/js2.el" "site-lisp/magit/50magit.el" "site-lisp/magit/magit-pkg.el"
;;;;;;  "site-lisp/mdfind.el" "site-lisp/mdfind.el" "site-lisp/mudel.el"
;;;;;;  "site-lisp/mudel.el" "site-lisp/nxhtml/autostart.el" "site-lisp/nxhtml/autostart22.el"
;;;;;;  "site-lisp/nxhtml/nxhtml-base.el" "site-lisp/nxhtml/nxhtml-loaddefs.el"
;;;;;;  "site-lisp/nxhtml/web-autoload.el" "site-lisp/paredit.el"
;;;;;;  "site-lisp/paredit.el" "site-lisp/parenface.el" "site-lisp/parenface.el"
;;;;;;  "site-lisp/planner/planner-authz.el" "site-lisp/planner/planner-calendar.el"
;;;;;;  "site-lisp/planner/planner-experimental.el" "site-lisp/planner/planner-ical.el"
;;;;;;  "site-lisp/planner/planner-publish.el" "site-lisp/planner/planner-zoom.el"
;;;;;;  "site-lisp/po-mode.el" "site-lisp/po-mode.el" "site-lisp/puppet-mode.el"
;;;;;;  "site-lisp/radio.el" "site-lisp/radio.el" "site-lisp/redshank.el"
;;;;;;  "site-lisp/redshank.el" "site-lisp/regex-tool/regex-tool.el"
;;;;;;  "site-lisp/remember/read-file-name.el" "site-lisp/remember/remember-experimental.el"
;;;;;;  "site-lisp/repeat-insert.el" "site-lisp/repeat-insert.el"
;;;;;;  "site-lisp/rfcview.el" "site-lisp/ruby-mode/inf-ruby.el"
;;;;;;  "site-lisp/ruby-mode/rdoc-mode.el" "site-lisp/ruby-mode/ruby-electric.el"
;;;;;;  "site-lisp/ruby-mode/ruby-style.el" "site-lisp/session.el"
;;;;;;  "site-lisp/slime/hyperspec.el" "site-lisp/slime/slime-autoloads.el"
;;;;;;  "site-lisp/slime/slime.el" "site-lisp/smex.el" "site-lisp/sudo-save.el"
;;;;;;  "site-lisp/sudo-save.el" "site-lisp/sunrise-commander.el"
;;;;;;  "site-lisp/sunrise-commander.el" "site-lisp/vkill.el" "site-lisp/vkill.el"
;;;;;;  "site-lisp/wcount.el" "site-lisp/wcount.el" "site-lisp/xml-rpc.el"
;;;;;;  "site-lisp/xml-rpc.el" "site-lisp/xray.el") (19385 30558
;;;;;;  623250))

;;;***

;;;### (autoloads (ido-completing-read ido-read-directory-name ido-read-file-name
;;;;;;  ido-read-buffer ido-dired ido-insert-file ido-write-file
;;;;;;  ido-find-file-other-frame ido-display-file ido-find-file-read-only-other-frame
;;;;;;  ido-find-file-read-only-other-window ido-find-file-read-only
;;;;;;  ido-find-alternate-file ido-find-file-other-window ido-find-file
;;;;;;  ido-find-file-in-dir ido-switch-buffer-other-frame ido-insert-buffer
;;;;;;  ido-kill-buffer ido-display-buffer ido-switch-buffer-other-window
;;;;;;  ido-switch-buffer ido-mode ido-mode) "ido" "ido.el" (19385
;;;;;;  26890))
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
