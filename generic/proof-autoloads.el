;;; DO NOT MODIFY THIS FILE
(if (featurep 'proof-autoloads) (error "Already loaded"))

(provide 'proof-autoloads)


;;;### (autoloads nil "bufhist" "../lib/bufhist.el" (17799 61158))
;;; Generated autoloads from ../lib/bufhist.el

(autoload (quote bufhist-mode) "bufhist" "\
Minor mode retaining an in-memory history of the buffer contents.")

;;;***

;;;### (autoloads (holes-mode) "holes" "../lib/holes.el" (17641 26026))
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

;;;### (autoloads (pg-pgip-askprefs pg-pgip-maybe-askpgip pg-pgip-process-packet)
;;;;;;  "pg-pgip" "pg-pgip.el" (18269 10080))
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

;;;### (autoloads (pg-response-has-error-location proof-next-error)
;;;;;;  "pg-response" "pg-response.el" (18269 10080))
;;; Generated autoloads from pg-response.el

(autoload (quote proof-next-error) "pg-response" "\
Jump to location of next error reported in the response buffer.

A prefix arg specifies how many error messages to move;
negative means move back to previous error messages.
Just C-u as a prefix means reparse the error message buffer
and start at the first error.

\(fn &optional ARGP)" t nil)

(autoload (quote pg-response-has-error-location) "pg-response" "\
Return non-nil if the response buffer has an error location.
See `pg-next-error-regexp'.

\(fn)" nil nil)

;;;***

;;;### (autoloads (pg-defthymode) "pg-thymodes" "pg-thymodes.el"
;;;;;;  (16513 49231))
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

;;;### (autoloads (proof-define-assistant-command-witharg proof-define-assistant-command)
;;;;;;  "pg-user" "pg-user.el" (18271 11570))
;;; Generated autoloads from pg-user.el

(autoload (quote proof-define-assistant-command) "pg-user" "\
Define command FN to send string BODY to proof assistant, based on CMDVAR.
BODY defaults to CMDVAR, a variable.

\(fn FN DOC CMDVAR &optional BODY)" nil (quote macro))

(autoload (quote proof-define-assistant-command-witharg) "pg-user" "\
Define command FN to prompt for string CMDVAR to proof assistant.
CMDVAR is a variable holding a function or string.  Automatically has history.

\(fn FN DOC CMDVAR PROMPT &rest BODY)" nil (quote macro))

;;;***

;;;### (autoloads (pg-xml-parse-string) "pg-xml" "pg-xml.el" (18268
;;;;;;  11587))
;;; Generated autoloads from pg-xml.el

(autoload (quote pg-xml-parse-string) "pg-xml" "\
Parse string in ARG, same as pg-xml-parse-buffer.

\(fn ARG)" nil nil)

;;;***

;;;### (autoloads (proof-dependency-in-span-context-menu proof-depends-process-dependencies)
;;;;;;  "proof-depends" "proof-depends.el" (16513 49231))
;;; Generated autoloads from proof-depends.el

(autoload (quote proof-depends-process-dependencies) "proof-depends" "\
Process dependencies reported by prover, for NAME in span GSPAN.
Called from `proof-done-advancing' when a save is processed and
proof-last-theorem-dependencies is set.

\(fn NAME GSPAN)" nil nil)

(autoload (quote proof-dependency-in-span-context-menu) "proof-depends" "\
Make a portion of a context-sensitive menu showing proof dependencies.

\(fn SPAN)" nil nil)

;;;***

;;;### (autoloads (proof-easy-config) "proof-easy-config" "proof-easy-config.el"
;;;;;;  (16513 49231))
;;; Generated autoloads from proof-easy-config.el

(autoload (quote proof-easy-config) "proof-easy-config" "\
Configure Proof General for proof-assistant using BODY as a setq body.
The symbol SYM and string name NAME must match those given in
the `proof-assistant-table', which see.

\(fn SYM NAME &rest BODY)" nil (quote macro))

;;;***

;;;### (autoloads (proof-indent-line) "proof-indent" "proof-indent.el"
;;;;;;  (17893 29685))
;;; Generated autoloads from proof-indent.el

(autoload (quote proof-indent-line) "proof-indent" "\
Indent current line of proof script, if indentation enabled.

\(fn)" t nil)

;;;***

;;;### (autoloads (proof-maths-menu-enable proof-maths-menu-support-available)
;;;;;;  "proof-maths-menu" "proof-maths-menu.el" (18271 52951))
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

;;;### (autoloads (defpacustom proof-defpacustom-fn proof-definvisible
;;;;;;  proof-defshortcut proof-menu-define-specific proof-menu-define-main
;;;;;;  proof-menu-define-keys) "proof-menu" "proof-menu.el" (18271
;;;;;;  52994))
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

(autoload (quote proof-defshortcut) "proof-menu" "\
Define shortcut function FN to insert STRING, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is inserted using `proof-insert', which see.
KEY is added onto proof-assistant map.

\(fn FN STRING &optional KEY)" nil (quote macro))

(autoload (quote proof-definvisible) "proof-menu" "\
Define function FN to send STRING to proof assistant, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is sent using proof-shell-invisible-command, which see.
STRING may be a string or a function which returns a string.
KEY is added onto proof-assistant map.

\(fn FN STRING &optional KEY)" nil (quote macro))

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
;;;;;;  "proof-mmm" "proof-mmm.el" (18268 11505))
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

;;;### (autoloads (proof-shell-invisible-command proof-shell-wait
;;;;;;  proof-extend-queue proof-start-queue proof-shell-available-p
;;;;;;  proof-shell-live-buffer proof-shell-ready-prover) "proof-shell"
;;;;;;  "proof-shell.el" (18120 5775))
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

;;;***

;;;### (autoloads (proof-splash-message proof-splash-display-screen)
;;;;;;  "proof-splash" "proof-splash.el" (18271 10299))
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

;;;### (autoloads (proof-format) "proof-syntax" "proof-syntax.el"
;;;;;;  (17987 35833))
;;; Generated autoloads from proof-syntax.el

(autoload (quote proof-format) "proof-syntax" "\
Format a string by matching regexps in ALIST against STRING.
ALIST contains (REGEXP . REPLACEMENT) pairs where REPLACEMENT
may be a string or sexp evaluated to get a string.

\(fn ALIST STRING)" nil nil)

;;;***

;;;### (autoloads (proof-toolbar-setup) "proof-toolbar" "proof-toolbar.el"
;;;;;;  (18271 10299))
;;; Generated autoloads from proof-toolbar.el

(autoload (quote proof-toolbar-setup) "proof-toolbar" "\
Initialize Proof General toolbar and enable it for current buffer.
If `proof-toolbar-enable' is nil, change the current buffer toolbar
to the default toolbar.

\(fn)" t nil)

;;;***

;;;### (autoloads (proof-x-symbol-config-output-buffer proof-x-symbol-shell-config
;;;;;;  proof-x-symbol-enable proof-x-symbol-support-maybe-available)
;;;;;;  "proof-x-symbol" "proof-x-symbol.el" (18269 9038))
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

(defalias (quote proof-x-symbol-decode-region) (quote x-symbol-decode-region))

(autoload (quote proof-x-symbol-shell-config) "proof-x-symbol" "\
Configure the proof shell for x-symbol, if proof-x-symbol-support<>nil.
Assumes that the current buffer is the proof shell buffer.

\(fn)" nil nil)

(autoload (quote proof-x-symbol-config-output-buffer) "proof-x-symbol" "\
Configure the current output buffer (goals/response/trace) for X-Symbol.

\(fn)" nil nil)

;;;***

;;;### (autoloads (texi-docstring-magic) "texi-docstring-magic" "../lib/texi-docstring-magic.el"
;;;;;;  (18269 10371))
;;; Generated autoloads from ../lib/texi-docstring-magic.el

(autoload (quote texi-docstring-magic) "texi-docstring-magic" "\
Update all texi docstring magic annotations in buffer.
With prefix arg, no errors on unknown symbols.  (This results in
@def .. @end being deleted if not known).

\(fn &optional NOERROR)" t nil)

;;;***

;;;### (autoloads nil nil ("../lib/holes-load.el" "../lib/local-vars-list.el"
;;;;;;  "../lib/proof-compat.el" "../lib/span-extent.el" "../lib/span-overlay.el"
;;;;;;  "../lib/span.el" "../lib/unichars.el" "../lib/xml-fixed.el"
;;;;;;  "../lib/xmlunicode.el" "pg-assoc.el" "pg-autotest.el" "pg-festival.el"
;;;;;;  "pg-goals.el" "pg-metadata.el" "pg-pbrpm.el" "pg-pgip-old.el"
;;;;;;  "pg-xhtml.el" "proof-config.el" "proof-script.el" "proof-site.el"
;;;;;;  "proof-system.el" "proof-utils.el" "proof.el") (18271 52998
;;;;;;  138163))

;;;***

;;;### (autoloads nil "_pkg" "_pkg.el" (16513 49231))
;;; Generated autoloads from _pkg.el

(package-provide (quote ProofGeneral) :version "3.3pre010320" :type (quote regular))

;;;***
