;;; DO NOT MODIFY THIS FILE
(if (featurep 'proof-autoloads) (error "Already loaded"))

(provide 'proof-autoloads)


;;;### (autoloads (bufhist-exit bufhist-init) "bufhist" "../lib/bufhist.el"
;;;;;;  (18316 54227))
;;; Generated autoloads from ../lib/bufhist.el

(autoload (quote bufhist-init) "bufhist" "\
Initialise a ring history for the current buffer.
The history will be read-only unless READWRITE is non-nil.
For read-only histories, edits to the buffer switch to the latest version.
The size defaults to `bufhist-ring-size'.

\(fn &optional READWRITE RINGSIZE)" t nil)

(autoload (quote bufhist-exit) "bufhist" "\
Stop keeping ring history for current buffer.

\(fn)" t nil)

(autoload (quote bufhist-mode) "bufhist" "\
Minor mode retaining an in-memory history of the buffer contents.")

;;;***

;;;### (autoloads (holes-mode) "holes" "../lib/holes.el" (18316 54227))
;;; Generated autoloads from ../lib/holes.el

(autoload (quote holes-mode) "holes" "\
If ARG is nil, then toggle holes mode on/off.
If arg is positive, then turn holes mode on.  If arg is negative, then
turn it off.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (maths-menu-mode) "maths-menu" "../lib/maths-menu.el"
;;;;;;  (18271 52110))
;;; Generated autoloads from ../lib/maths-menu.el

(autoload (quote maths-menu-mode) "maths-menu" "\
Install a menu for entering mathematical characters.
Uses window system menus only when they can display multilingual text.
Otherwise the menu-bar item activates the text-mode menu system.
This mode is only useful with a font which can display the maths repertoire.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (proof-associated-windows proof-associated-buffers)
;;;;;;  "pg-assoc" "pg-assoc.el" (18319 24214))
;;; Generated autoloads from pg-assoc.el

(autoload (quote proof-associated-buffers) "pg-assoc" "\
Return a list of the associated buffers.  
Some may be dead/nil.

\(fn)" nil nil)

(autoload (quote proof-associated-windows) "pg-assoc" "\
Return a list of the associated buffers windows.  
Dead or nil buffers are not represented in the list.

\(fn)" nil nil)

;;;***

;;;### (autoloads (proof-goals-config-done) "pg-goals" "pg-goals.el"
;;;;;;  (18318 19099))
;;; Generated autoloads from pg-goals.el

(autoload (quote proof-goals-config-done) "pg-goals" "\
Initialise the goals buffer after the child has been configured.

\(fn)" nil nil)

;;;***

;;;### (autoloads (pg-pgip-askprefs pg-pgip-maybe-askpgip pg-pgip-process-packet)
;;;;;;  "pg-pgip" "pg-pgip.el" (18319 24214))
;;; Generated autoloads from pg-pgip.el

(autoload (quote pg-pgip-process-packet) "pg-pgip" "\
Process the command packet PGIP, which is parsed XML according to pg-xml-parse-*.
The list PGIPS may contain one or more PGIP packets, whose contents are processed.

\(fn PGIPS)" nil nil)

(autoload (quote pg-pgip-maybe-askpgip) "pg-pgip" "\
Send an <askpgip> message to the prover if PGIP is supported.

\(fn)" nil nil)

(autoload (quote pg-pgip-askprefs) "pg-pgip" "\
Send an <askprefs> message to the prover.

\(fn)" nil nil)

;;;***

;;;### (autoloads (pg-response-has-error-location proof-next-error
;;;;;;  pg-response-display-with-face pg-response-maybe-erase proof-response-config-done
;;;;;;  proof-response-mode) "pg-response" "pg-response.el" (18319
;;;;;;  24214))
;;; Generated autoloads from pg-response.el

(autoload (quote proof-response-mode) "pg-response" "\
Responses from Proof Assistant

\(fn)" t nil)

(autoload (quote proof-response-config-done) "pg-response" "\
Complete initialisation of a response-mode derived buffer.

\(fn)" nil nil)

(autoload (quote pg-response-maybe-erase) "pg-response" "\
Erase the response buffer according to pg-response-erase-flag.
ERASE-NEXT-TIME is the new value for the flag.
If CLEAN-WINDOWS is set, use proof-clean-buffer to do the erasing.
If FORCE, override pg-response-erase-flag.

If the user option proof-tidy-response is nil, then
the buffer is only cleared when FORCE is set.

No effect if there is no response buffer currently.
Returns non-nil if response buffer was cleared.

\(fn &optional ERASE-NEXT-TIME CLEAN-WINDOWS FORCE)" nil nil)

(autoload (quote pg-response-display-with-face) "pg-response" "\
Display STR with FACE in response buffer.

\(fn STR &optional FACE)" nil nil)

(autoload (quote proof-next-error) "pg-response" "\
Jump to location of next error reported in the response buffer.

A prefix arg specifies how many error messages to move;
negative means move back to previous error messages.

Optional argument ARGP means reparse the error message buffer
and start at the first error.

\(fn &optional ARGP)" t nil)

(autoload (quote pg-response-has-error-location) "pg-response" "\
Return non-nil if the response buffer has an error location.
See `pg-next-error-regexp'.

\(fn)" nil nil)

;;;***

;;;### (autoloads (pg-defthymode) "pg-thymodes" "pg-thymodes.el"
;;;;;;  (18316 54225))
;;; Generated autoloads from pg-thymodes.el

(autoload (quote pg-defthymode) "pg-thymodes" "\
Define a Proof General mode for theory files.
Mode name is SYM-mode, named NAMED.  BODY is the body of a setq and
can define a number of variables for the mode, viz:

  SYM-<font-lock-keywords>      (value for font-lock-keywords)
  SYM-<syntax-table-entries>	(list of pairs: used for modify-syntax-entry calls)
  SYM-<menu>			(menu for the mode, arg of easy-menu-define)
  SYM-<parent-mode>		(defaults to fundamental-mode)
  SYM-<filename-regexp>	        (regexp matching filenames for auto-mode-alist)

All of these settings are optional.

\(fn SYM NAME &rest BODY)" nil (quote macro))

;;;***

;;;### (autoloads (pg-clear-input-ring pg-remove-from-input-history
;;;;;;  pg-add-to-input-history pg-next-matching-input-from-input
;;;;;;  pg-previous-matching-input-from-input proof-imenu-enable
;;;;;;  pg-hint pg-next-error-hint pg-processing-complete-hint pg-jump-to-end-hint
;;;;;;  pg-response-buffers-hint pg-slow-fontify-tracing-hint proof-electric-term-incomment-fn
;;;;;;  proof-electric-terminator-enable proof-define-assistant-command-witharg
;;;;;;  proof-define-assistant-command proof-interrupt-process) "pg-user"
;;;;;;  "pg-user.el" (18319 24214))
;;; Generated autoloads from pg-user.el

(autoload (quote proof-interrupt-process) "pg-user" "\
Interrupt the proof assistant.  Warning! This may confuse Proof General.
This sends an interrupt signal to the proof assistant, if Proof General
thinks it is busy.

This command is risky because when an interrupt is trapped in the
proof assistant, we don't know whether the last command succeeded or
not.  The assumption is that it didn't, which should be true most of
the time, and all of the time if the proof assistant has a careful
handling of interrupt signals.

\(fn)" t nil)

(autoload (quote proof-define-assistant-command) "pg-user" "\
Define FN (docstring DOC) to send BODY to prover, based on CMDVAR.
BODY defaults to CMDVAR, a variable.

\(fn FN DOC CMDVAR &optional BODY)" nil (quote macro))

(autoload (quote proof-define-assistant-command-witharg) "pg-user" "\
Define command FN to prompt for string CMDVAR to proof assistant.
CMDVAR is a variable holding a function or string.  Automatically has history.

\(fn FN DOC CMDVAR PROMPT &rest BODY)" nil (quote macro))

(autoload (quote proof-electric-terminator-enable) "pg-user" "\
Make sure the modeline is updated to display new value for electric terminator.

\(fn)" nil nil)

(autoload (quote proof-electric-term-incomment-fn) "pg-user" "\
Used as argument to proof-assert-until-point.

\(fn)" nil nil)

(autoload (quote pg-slow-fontify-tracing-hint) "pg-user" "\
Not documented

\(fn)" nil nil)

(autoload (quote pg-response-buffers-hint) "pg-user" "\
Not documented

\(fn &optional NEXTBUF)" nil nil)

(autoload (quote pg-jump-to-end-hint) "pg-user" "\
Not documented

\(fn)" nil nil)

(autoload (quote pg-processing-complete-hint) "pg-user" "\
Display hint for showing end of locked region or processing complete.

\(fn)" nil nil)

(autoload (quote pg-next-error-hint) "pg-user" "\
Display hint for locating error.

\(fn)" nil nil)

(autoload (quote pg-hint) "pg-user" "\
Display a hint HINTMSG in the minibuffer, if `pg-show-hints' is non-nil.
The function `substitute-command-keys' is called on the argument.

\(fn HINTMSG)" nil nil)

(autoload (quote proof-imenu-enable) "pg-user" "\
Add or remove index menu.

\(fn)" nil nil)

(autoload (quote pg-previous-matching-input-from-input) "pg-user" "\
Search backwards through input history for match for current input.
\(Previous history elements are earlier commands.)
With prefix argument N, search for Nth previous match.
If N is negative, search forwards for the -Nth following match.

\(fn N)" t nil)

(autoload (quote pg-next-matching-input-from-input) "pg-user" "\
Search forwards through input history for match for current input.
\(Following history elements are more recent commands.)
With prefix argument N, search for Nth following match.
If N is negative, search backwards for the -Nth previous match.

\(fn N)" t nil)

(autoload (quote pg-add-to-input-history) "pg-user" "\
Maybe add CMD to the input history.
CMD is only added to the input history if it is not a duplicate
of the last item added.

\(fn CMD)" nil nil)

(autoload (quote pg-remove-from-input-history) "pg-user" "\
Maybe remove CMD from the end of the input history.
This is called when the command is undone.  It's only 
removed if it matches the last item in the ring.

\(fn CMD)" nil nil)

(autoload (quote pg-clear-input-ring) "pg-user" "\
Not documented

\(fn)" nil nil)

;;;***

;;;### (autoloads (pg-xml-parse-string) "pg-xml" "pg-xml.el" (18319
;;;;;;  24214))
;;; Generated autoloads from pg-xml.el

(autoload (quote pg-xml-parse-string) "pg-xml" "\
Parse string in ARG, same as pg-xml-parse-buffer.

\(fn ARG)" nil nil)

;;;***

;;;### (autoloads (proof-dependency-in-span-context-menu proof-depends-process-dependencies)
;;;;;;  "proof-depends" "proof-depends.el" (18319 24214))
;;; Generated autoloads from proof-depends.el

(autoload (quote proof-depends-process-dependencies) "proof-depends" "\
Process dependencies reported by prover, for NAME in span GSPAN.
Called from `proof-done-advancing' when a save is processed and
`proof-last-theorem-dependencies' is set.

\(fn NAME GSPAN)" nil nil)

(autoload (quote proof-dependency-in-span-context-menu) "proof-depends" "\
Make a portion of a context-sensitive menu showing proof dependencies.

\(fn SPAN)" nil nil)

;;;***

;;;### (autoloads (proof-easy-config) "proof-easy-config" "proof-easy-config.el"
;;;;;;  (18319 24214))
;;; Generated autoloads from proof-easy-config.el

(autoload (quote proof-easy-config) "proof-easy-config" "\
Configure Proof General for proof-assistant using BODY as a setq body.
The symbol SYM and string name NAME must match those given in
the `proof-assistant-table', which see.

\(fn SYM NAME &rest BODY)" nil (quote macro))

;;;***

;;;### (autoloads (proof-indent-line) "proof-indent" "proof-indent.el"
;;;;;;  (18329 64338))
;;; Generated autoloads from proof-indent.el

(autoload (quote proof-indent-line) "proof-indent" "\
Indent current line of proof script, if indentation enabled.

\(fn)" t nil)

;;;***

;;;### (autoloads (proof-maths-menu-enable proof-maths-menu-support-available)
;;;;;;  "proof-maths-menu" "proof-maths-menu.el" (18319 24214))
;;; Generated autoloads from proof-maths-menu.el

(autoload (quote proof-maths-menu-support-available) "proof-maths-menu" "\
A test to see whether maths-menu support is available.

\(fn)" nil nil)

(autoload (quote proof-maths-menu-enable) "proof-maths-menu" "\
Turn on or off maths-menu mode in Proof General script buffer.
This invokes `maths-menu-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have maths menu mode turn itself on automatically 
in future if we have just activated it for this buffer.

\(fn)" t nil)

;;;***

;;;### (autoloads (defpacustom proof-defpacustom-fn proof-aux-menu
;;;;;;  proof-menu-define-specific proof-menu-define-main proof-menu-define-keys)
;;;;;;  "proof-menu" "proof-menu.el" (18329 64338))
;;; Generated autoloads from proof-menu.el

(autoload (quote proof-menu-define-keys) "proof-menu" "\
Not documented

\(fn MAP)" nil nil)

(autoload (quote proof-menu-define-main) "proof-menu" "\
Not documented

\(fn)" nil nil)

(autoload (quote proof-menu-define-specific) "proof-menu" "\
Not documented

\(fn)" nil nil)

(autoload (quote proof-aux-menu) "proof-menu" "\
Construct and return PG auxiliary menu used in non-scripting buffers.

\(fn)" nil nil)

(autoload (quote proof-defpacustom-fn) "proof-menu" "\
As for macro `defpacustom' but evaluating arguments.

\(fn NAME VAL ARGS)" nil nil)

(autoload (quote defpacustom) "proof-menu" "\
Define a setting NAME for the current proof assitant, default VAL.
NAME can correspond to some internal setting, flag, etc, for the
proof assistant, in which case a :setting and :type value should be provided.
The :type of NAME should be one of 'integer, 'boolean, 'string.
The customization variable is automatically in group `proof-assistant-setting'.
The function `proof-assistant-format' is used to format VAL.
If NAME corresponds instead to a PG internal setting, then a form :eval to
evaluate can be provided instead.

\(fn NAME VAL &rest ARGS)" nil (quote macro))

;;;***

;;;### (autoloads (proof-mmm-enable proof-mmm-support-available)
;;;;;;  "proof-mmm" "proof-mmm.el" (18319 24214))
;;; Generated autoloads from proof-mmm.el

(autoload (quote proof-mmm-support-available) "proof-mmm" "\
A test to see whether mmm support is available.

\(fn)" nil nil)

(autoload (quote proof-mmm-enable) "proof-mmm" "\
Turn on or off MMM mode in Proof General script buffer.
This invokes `mmm-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have MMM mode turn itself on automatically 
in future if we have just activated it for this buffer.

\(fn)" t nil)

;;;***

;;;### (autoloads (proof-config-done proof-mode proof-insert-pbp-command
;;;;;;  pg-set-span-helphighlights proof-locked-region-empty-p proof-locked-region-full-p
;;;;;;  proof-locked-end proof-unprocessed-begin) "proof-script"
;;;;;;  "proof-script.el" (18329 64338))
;;; Generated autoloads from proof-script.el

(autoload (quote proof-unprocessed-begin) "proof-script" "\
Return end of locked region in current buffer or (point-min) otherwise.
The position is actually one beyond the last locked character.

\(fn)" nil nil)

(autoload (quote proof-locked-end) "proof-script" "\
Return end of the locked region of the current buffer.
Only call this from a scripting buffer.

\(fn)" nil nil)

(autoload (quote proof-locked-region-full-p) "proof-script" "\
Non-nil if the locked region covers all the buffer's non-whitespace.
Works on any buffer.

\(fn)" nil nil)

(autoload (quote proof-locked-region-empty-p) "proof-script" "\
Non-nil if the locked region is empty.  Works on any buffer.

\(fn)" nil nil)

(autoload (quote pg-set-span-helphighlights) "proof-script" "\
Set the help echo message, default highlight, and keymap for SPAN.

\(fn SPAN &optional NOHIGHLIGHT)" nil nil)

(autoload (quote proof-insert-pbp-command) "proof-script" "\
Insert CMD into the proof queue.

\(fn CMD)" nil nil)

(autoload (quote proof-mode) "proof-script" "\
Proof General major mode class for proof scripts.
\\{proof-mode-map}

\(fn)" t nil)

(autoload (quote proof-config-done) "proof-script" "\
Finish setup of Proof General scripting mode.
Call this function in the derived mode for the proof assistant to
finish setup which depends on specific proof assistant configuration.

\(fn)" nil nil)

;;;***

;;;### (autoloads (proof-shell-config-done proof-shell-mode proof-shell-invisible-command-invisible-result
;;;;;;  proof-shell-invisible-cmd-get-result proof-shell-invisible-command
;;;;;;  proof-shell-wait proof-extend-queue proof-start-queue proof-shell-insert
;;;;;;  proof-shell-available-p proof-shell-live-buffer proof-shell-ready-prover)
;;;;;;  "proof-shell" "proof-shell.el" (18319 24214))
;;; Generated autoloads from proof-shell.el

(autoload (quote proof-shell-ready-prover) "proof-shell" "\
Make sure the proof assistant is ready for a command.
If QUEUEMODE is set, succeed if the proof shell is busy but
has mode QUEUEMODE, which is a symbol or list of symbols.
Otherwise, if the shell is busy, give an error.
No change to current buffer or point.

\(fn &optional QUEUEMODE)" nil nil)

(autoload (quote proof-shell-live-buffer) "proof-shell" "\
Return buffer of active proof assistant, or nil if none running.

\(fn)" nil nil)

(autoload (quote proof-shell-available-p) "proof-shell" "\
Returns non-nil if there is a proof shell active and available.
No error messages.  Useful as menu or toolbar enabler.

\(fn)" nil nil)

(autoload (quote proof-shell-insert) "proof-shell" "\
Insert STRING at the end of the proof shell, call `comint-send-input'.

First call `proof-shell-insert-hook'.  The argument ACTION may be
examined by the hook to determine how to process the STRING variable.

Then strip STRING of carriage returns before inserting it and updating
`proof-marker' to point to the end of the newly inserted text.

Do not use this function directly, or output will be lost.  It is only
used in `proof-append-alist' when we start processing a queue, and in
`proof-shell-exec-loop', to process the next item.

\(fn STRING ACTION)" nil nil)

(autoload (quote proof-start-queue) "proof-shell" "\
Begin processing a queue of commands in ALIST.
If START is non-nil, START and END are buffer positions in the
active scripting buffer for the queue region.

This function calls `proof-append-alist'.

\(fn START END ALIST)" nil nil)

(autoload (quote proof-extend-queue) "proof-shell" "\
Extend the current queue with commands in ALIST, queue end END.
To make sense, the commands should correspond to processing actions
for processing a region from (buffer-queue-or-locked-end) to END.
The queue mode is set to 'advancing

\(fn END ALIST)" nil nil)

(autoload (quote proof-shell-wait) "proof-shell" "\
Busy wait for `proof-shell-busy' to become nil.
Needed between sequences of commands to maintain synchronization,
because Proof General does not allow for the action list to be extended
in some cases.   May be called by `proof-shell-invisible-command'.

\(fn)" nil nil)

(autoload (quote proof-shell-invisible-command) "proof-shell" "\
Send CMD to the proof process.
The CMD is `invisible' in the sense that it is not recorded in buffer.
CMD may be a string or a string-yielding expression.

Automatically add proof-terminal-char if necessary, examining
proof-shell-no-auto-terminate-commands.

By default, let the command be processed asynchronously.
But if optional WAIT command is non-nil, wait for processing to finish
before and after sending the command.

In case CMD is (or yields) nil, do nothing.

\(fn CMD &optional WAIT)" nil nil)

(autoload (quote proof-shell-invisible-cmd-get-result) "proof-shell" "\
Execute CMD and return result as a string.
This expects CMD to print something to the response buffer.
The output in the response buffer is disabled, and the result
\(contents of `proof-shell-last-output') is returned as a 
string instead.  

Errors are not supressed and will result in a display as 
usual, unless NOERROR is non-nil.

\(fn CMD &optional NOERROR)" nil nil)

(autoload (quote proof-shell-invisible-command-invisible-result) "proof-shell" "\
Execute CMD, wait for but do not display result.

\(fn CMD &optional NOERROR)" nil nil)

(autoload (quote proof-shell-mode) "proof-shell" "\
Proof General shell mode class for proof assistant processes

\(fn)" t nil)

(autoload (quote proof-shell-config-done) "proof-shell" "\
Initialise the specific prover after the child has been configured.
Every derived shell mode should call this function at the end of
processing.

\(fn)" nil nil)

;;;***

;;;### (autoloads (proof-splash-message proof-splash-display-screen)
;;;;;;  "proof-splash" "proof-splash.el" (18319 24214))
;;; Generated autoloads from proof-splash.el

(autoload (quote proof-splash-display-screen) "proof-splash" "\
Save window config and display Proof General splash screen.
If TIMEOUT is non-nil, time out outside this function, definitely
by end of configuring proof mode.
Otherwise, timeout inside this function after 10 seconds or so.

\(fn &optional TIMEOUT)" t nil)

(autoload (quote proof-splash-message) "proof-splash" "\
Make sure the user gets welcomed one way or another.

\(fn)" t nil)

;;;***

;;;### (autoloads (proof-splice-separator proof-format) "proof-syntax"
;;;;;;  "proof-syntax.el" (18319 24214))
;;; Generated autoloads from proof-syntax.el

(autoload (quote proof-format) "proof-syntax" "\
Format a string by matching regexps in ALIST against STRING.
ALIST contains (REGEXP . REPLACEMENT) pairs where REPLACEMENT
may be a string or sexp evaluated to get a string.

\(fn ALIST STRING)" nil nil)

(autoload (quote proof-splice-separator) "proof-syntax" "\
Splice SEP into list of STRINGS.

\(fn SEP STRINGS)" nil nil)

;;;***

;;;### (autoloads (proof-toolbar-scripting-menu proof-toolbar-setup)
;;;;;;  "proof-toolbar" "proof-toolbar.el" (18319 24214))
;;; Generated autoloads from proof-toolbar.el

(autoload (quote proof-toolbar-setup) "proof-toolbar" "\
Initialize Proof General toolbar and enable it for current buffer.
If `proof-toolbar-enable' is nil, change the current buffer toolbar
to the default toolbar.

\(fn)" t nil)
 (autoload 'proof-toolbar-toggle "proof-toolbar")

(autoload (quote proof-toolbar-scripting-menu) "proof-toolbar" "\
Menu made from the Proof General toolbar commands.

\(fn)" nil nil)

;;;***

;;;### (autoloads (proof-unicode-tokens-enable proof-unicode-tokens-support-available)
;;;;;;  "proof-unicode-tokens" "proof-unicode-tokens.el" (18329 59881))
;;; Generated autoloads from proof-unicode-tokens.el

(autoload (quote proof-unicode-tokens-support-available) "proof-unicode-tokens" "\
A test to see whether unicode tokens support is available.

\(fn)" nil nil)

(autoload (quote proof-unicode-tokens-enable) "proof-unicode-tokens" "\
Turn on or off Unicode tokens mode in Proof General script buffer.
This invokes `maths-menu-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have maths menu mode turn itself on automatically 
in future if we have just activated it for this buffer.

\(fn)" t nil)

;;;***

;;;### (autoloads (proof-x-symbol-config-output-buffer proof-x-symbol-shell-config
;;;;;;  proof-x-symbol-decode-region proof-x-symbol-enable proof-x-symbol-support-maybe-available)
;;;;;;  "proof-x-symbol" "proof-x-symbol.el" (18319 24214))
;;; Generated autoloads from proof-x-symbol.el

(autoload (quote proof-x-symbol-support-maybe-available) "proof-x-symbol" "\
A test to see whether x-symbol support may be available.

\(fn)" nil nil)

(autoload (quote proof-x-symbol-enable) "proof-x-symbol" "\
Turn on or off X-Symbol in current Proof General script buffer.
This invokes `x-symbol-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have X-Symbol mode turn itself on automatically 
in future if we have just activated it for this buffer.

\(fn)" nil nil)

(autoload (quote proof-x-symbol-decode-region) "proof-x-symbol" "\
Not documented

\(fn START END)" nil nil)

(autoload (quote proof-x-symbol-shell-config) "proof-x-symbol" "\
Configure the proof shell for x-symbol, if proof-x-symbol-support<>nil.
Assumes that the current buffer is the proof shell buffer.

\(fn)" nil nil)

(autoload (quote proof-x-symbol-config-output-buffer) "proof-x-symbol" "\
Configure the current output buffer (goals/response/trace) for X-Symbol.

\(fn)" nil nil)

;;;***

;;;### (autoloads nil nil ("../lib/holes-load.el" "../lib/local-vars-list.el"
;;;;;;  "../lib/pg-dev.el" "../lib/proof-compat.el" "../lib/span-extent.el"
;;;;;;  "../lib/span-overlay.el" "../lib/span.el" "../lib/unicode-chars.el"
;;;;;;  "../lib/xml-fixed.el" "pg-autotest.el" "pg-custom.el" "pg-metadata.el"
;;;;;;  "pg-pbrpm.el" "pg-pgip-old.el" "pg-vars.el" "pg-xhtml.el"
;;;;;;  "proof-config.el" "proof-site.el" "proof-utils.el" "proof.el")
;;;;;;  (18329 64408 502433))

;;;***

;;;### (autoloads (texi-docstring-magic) "texi-docstring-magic" "../lib/texi-docstring-magic.el"
;;;;;;  (18318 19099))
;;; Generated autoloads from ../lib/texi-docstring-magic.el

(autoload (quote texi-docstring-magic) "texi-docstring-magic" "\
Update all texi docstring magic annotations in buffer.
With prefix arg, no errors on unknown symbols.  (This results in
@def .. @end being deleted if not known).

\(fn &optional NOERROR)" t nil)

;;;***
