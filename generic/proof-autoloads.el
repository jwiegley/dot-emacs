;;; DO NOT MODIFY THIS FILE
(if (featurep 'proof-autoloads) (error "Already loaded"))

(provide 'proof-autoloads)

;;;### (autoloads nil "_pkg" "generic/_pkg.el")

(package-provide 'ProofGeneral :version "3.3pre010320" :type 'regular)

;;;***

;;;### (autoloads (pg-pgip-askprefs pg-pgip-maybe-askpgip pg-pgip-process-packet) "pg-pgip" "generic/pg-pgip.el")

(autoload 'pg-pgip-process-packet "pg-pgip" "\
Process the command packet PGIP, which is parsed XML according to pg-xml-parse-*.
The list PGIPS may contain one or more PGIP packets, whose contents are processed." nil nil)

(autoload 'pg-pgip-maybe-askpgip "pg-pgip" "\
Send an <askpgip> message to the prover if PGIP is supported." nil nil)

(autoload 'pg-pgip-askprefs "pg-pgip" "\
Send an <askprefs> message to the prover." nil nil)

;;;***

;;;### (autoloads (pg-response-has-error-location proof-next-error) "pg-response" "generic/pg-response.el")

(autoload 'proof-next-error "pg-response" "\
Jump to location of next error reported in the response buffer.

A prefix arg specifies how many error messages to move;
negative means move back to previous error messages.
Just C-u as a prefix means reparse the error message buffer
and start at the first error." t nil)

(autoload 'pg-response-has-error-location "pg-response" "\
Return non-nil if the response buffer has an error location.
See `pg-next-error-regexp'." nil nil)

;;;***

;;;### (autoloads (pg-defthymode) "pg-thymodes" "generic/pg-thymodes.el")

(autoload 'pg-defthymode "pg-thymodes" "\
Define a Proof General mode for theory files.
Mode name is SYM-mode, named NAMED.  BODY is the body of a setq and
can define a number of variables for the mode, viz:

  SYM-<font-lock-keywords>      (value for font-lock-keywords)
  SYM-<syntax-table-entries>	(list of pairs: used for modify-syntax-entry calls)
  SYM-<menu>			(menu for the mode, arg of easy-menu-define)
  SYM-<parent-mode>		(defaults to fundamental-mode)
  SYM-<filename-regexp>	        (regexp matching filenames for auto-mode-alist)

All of these settings are optional." nil 'macro)

;;;***

;;;### (autoloads (proof-define-assistant-command-witharg proof-define-assistant-command) "pg-user" "generic/pg-user.el")

(autoload 'proof-define-assistant-command "pg-user" "\
Define command FN to send string BODY to proof assistant, based on CMDVAR.
BODY defaults to CMDVAR, a variable." nil 'macro)

(autoload 'proof-define-assistant-command-witharg "pg-user" "\
Define command FN to prompt for string CMDVAR to proof assistant.
CMDVAR is a variable holding a function or string.  Automatically has history." nil 'macro)

;;;***

;;;### (autoloads (pg-xml-parse-string) "pg-xml" "generic/pg-xml.el")

(autoload 'pg-xml-parse-string "pg-xml" "\
Parse string in ARG, same as pg-xml-parse-buffer." nil nil)

;;;***

;;;### (autoloads (proof-dependency-in-span-context-menu proof-depends-process-dependencies) "proof-depends" "generic/proof-depends.el")

(autoload 'proof-depends-process-dependencies "proof-depends" "\
Process dependencies reported by prover, for NAME in span GSPAN.
Called from `proof-done-advancing' when a save is processed and
proof-last-theorem-dependencies is set." nil nil)

(autoload 'proof-dependency-in-span-context-menu "proof-depends" "\
Make a portion of a context-sensitive menu showing proof dependencies." nil nil)

;;;***

;;;### (autoloads (proof-easy-config) "proof-easy-config" "generic/proof-easy-config.el")

(autoload 'proof-easy-config "proof-easy-config" "\
Configure Proof General for proof-assistant using BODY as a setq body." nil 'macro)

;;;***

;;;### (autoloads (proof-indent-line) "proof-indent" "generic/proof-indent.el")

(autoload 'proof-indent-line "proof-indent" "\
Indent current line of proof script, if indentation enabled." t nil)

;;;***

;;;### (autoloads (defpacustom proof-defpacustom-fn proof-definvisible proof-defshortcut proof-menu-define-specific proof-menu-define-main proof-menu-define-keys) "proof-menu" "generic/proof-menu.el")

(autoload 'proof-menu-define-keys "proof-menu" nil nil nil)

(autoload 'proof-menu-define-main "proof-menu" nil nil nil)

(autoload 'proof-menu-define-specific "proof-menu" nil nil nil)

(autoload 'proof-defshortcut "proof-menu" "\
Define shortcut function FN to insert STRING, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is inserted using `proof-insert', which see.
KEY is added onto proof-assistant map." nil 'macro)

(autoload 'proof-definvisible "proof-menu" "\
Define function FN to send STRING to proof assistant, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is sent using proof-shell-invisible-command, which see.
STRING may be a string or a function which returns a string.
KEY is added onto proof-assistant map." nil 'macro)

(autoload 'proof-defpacustom-fn "proof-menu" "\
As for macro `defpacustom' but evaluating arguments." nil nil)

(autoload 'defpacustom "proof-menu" "\
Define a setting NAME for the current proof assitant, default VAL.
NAME can correspond to some internal setting, flag, etc, for the
proof assistant, in which case a :setting and :type value should be provided.
The :type of NAME should be one of 'integer, 'boolean, 'string.
The customization variable is automatically in group `proof-assistant-setting'.
The function `proof-assistant-format' is used to format VAL.
If NAME corresponds instead to a PG internal setting, then a form :eval to
evaluate can be provided instead." nil 'macro)

;;;***

;;;### (autoloads (proof-mmm-enable proof-mmm-support-available) "proof-mmm" "generic/proof-mmm.el")

(autoload 'proof-mmm-support-available "proof-mmm" "\
A test to see whether mmm support is available." nil nil)

(autoload 'proof-mmm-enable "proof-mmm" "\
Turn on or off MMM mode in Proof General script buffers.
This invokes `mmm-mode' to toggle the setting for the current
buffer, and then sets PG's option for the setting accordingly." nil nil)

;;;***

;;;### (autoloads nil "proof-script" "generic/proof-script.el")

;;;***

;;;### (autoloads (proof-shell-invisible-command proof-shell-wait proof-extend-queue proof-start-queue proof-shell-available-p proof-shell-live-buffer proof-shell-ready-prover) "proof-shell" "generic/proof-shell.el")

(autoload 'proof-shell-ready-prover "proof-shell" "\
Make sure the proof assistant is ready for a command.
If QUEUEMODE is set, succeed if the proof shell is busy but
has mode QUEUEMODE, which is a symbol or list of symbols.
Otherwise, if the shell is busy, give an error.
No change to current buffer or point." nil nil)

(autoload 'proof-shell-live-buffer "proof-shell" "\
Return buffer of active proof assistant, or nil if none running." nil nil)

(autoload 'proof-shell-available-p "proof-shell" "\
Returns non-nil if there is a proof shell active and available.
No error messages.  Useful as menu or toolbar enabler." nil nil)

(autoload 'proof-start-queue "proof-shell" "\
Begin processing a queue of commands in ALIST.
If START is non-nil, START and END are buffer positions in the
active scripting buffer for the queue region.

This function calls `proof-append-alist'." nil nil)

(autoload 'proof-extend-queue "proof-shell" "\
Extend the current queue with commands in ALIST, queue end END.
To make sense, the commands should correspond to processing actions
for processing a region from (buffer-queue-or-locked-end) to END.
The queue mode is set to 'advancing" nil nil)

(autoload 'proof-shell-wait "proof-shell" "\
Busy wait for `proof-shell-busy' to become nil.
Needed between sequences of commands to maintain synchronization,
because Proof General does not allow for the action list to be extended
in some cases.   May be called by `proof-shell-invisible-command'." nil nil)

(autoload 'proof-shell-invisible-command "proof-shell" "\
Send CMD to the proof process.
The CMD is `invisible' in the sense that it is not recorded in buffer.
CMD may be a string or a string-yielding expression.

Automatically add proof-terminal-char if necessary, examining
proof-shell-no-auto-terminate-commands.

By default, let the command be processed asynchronously.
But if optional WAIT command is non-nil, wait for processing to finish
before and after sending the command.

In case CMD is (or yields) nil, do nothing." nil nil)

;;;***

;;;### (autoloads (proof-splash-message proof-splash-display-screen) "proof-splash" "generic/proof-splash.el")

(autoload 'proof-splash-display-screen "proof-splash" "\
Save window config and display Proof General splash screen.
If TIMEOUT is non-nil, time out outside this function, definitely
by end of configuring proof mode.
Otherwise, timeout inside this function after 10 seconds or so." t nil)

(autoload 'proof-splash-message "proof-splash" "\
Make sure the user gets welcomed one way or another." t nil)

;;;***

;;;### (autoloads (proof-format) "proof-syntax" "generic/proof-syntax.el")

(autoload 'proof-format "proof-syntax" "\
Format a string by matching regexps in ALIST against STRING.
ALIST contains (REGEXP . REPLACEMENT) pairs where REPLACEMENT
may be a string or sexp evaluated to get a string." nil nil)

;;;***

;;;### (autoloads (proof-toolbar-setup) "proof-toolbar" "generic/proof-toolbar.el")

(autoload 'proof-toolbar-setup "proof-toolbar" "\
Initialize Proof General toolbar and enable it for current buffer.
If `proof-toolbar-enable' is nil, change the current buffer toolbar
to the default toolbar." t nil)

;;;***

;;;### (autoloads (proof-x-symbol-config-output-buffer proof-x-symbol-shell-config proof-x-symbol-enable proof-x-symbol-support-maybe-available) "proof-x-symbol" "generic/proof-x-symbol.el")

(autoload 'proof-x-symbol-support-maybe-available "proof-x-symbol" "\
A test to see whether x-symbol support may be available." nil nil)

(autoload 'proof-x-symbol-enable "proof-x-symbol" "\
Turn on or off X-Symbol in current Proof General script buffer.
This invokes `x-symbol-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have X-Symbol mode turn itself on automatically 
in future if we have just activated it for this buffer." nil nil)

(defalias 'proof-x-symbol-decode-region 'x-symbol-decode-region)

(autoload 'proof-x-symbol-shell-config "proof-x-symbol" "\
Configure the proof shell for x-symbol, if proof-x-symbol-support<>nil.
Assumes that the current buffer is the proof shell buffer." nil nil)

(autoload 'proof-x-symbol-config-output-buffer "proof-x-symbol" "\
Configure the current output buffer (goals/response/trace) for X-Symbol." nil nil)

;;;***

;;;### (autoloads (bufhist-checkpoint) "bufhist" "lib/bufhist.el")

(autoload 'bufhist-checkpoint "bufhist" "\
Add the current buffer contents to the ring history." t nil)

(autoload 'bufhist-mode "bufhist" "\
Minor mode retaining an in-memory history of the buffer contents.")

;;;***

;;;### (autoloads nil "bufregring" "lib/bufregring.el")

(autoload 'bufhist-mode "bufhist" "\
Minor mode retaining an in-memory history of the buffer contents.")

;;;***

;;;### (autoloads nil "bufregs" "lib/bufregs.el")

(autoload 'bufregs-mode "bufregs" "\
Minor mode retaining an in-memory history of the buffer contents.")

;;;***

;;;### (autoloads (holes-mode) "holes" "lib/holes.el")

(autoload 'holes-mode "holes" "\
If ARG is nil, then toggle holes mode on/off.
If arg is positive, then turn holes mode on.  If arg is negative, then
turn it off." t nil)

;;;***

;;;### (autoloads (texi-docstring-magic) "texi-docstring-magic" "lib/texi-docstring-magic.el")

(autoload 'texi-docstring-magic "texi-docstring-magic" "\
Update all texi docstring magic annotations in buffer.
With prefix arg, no errors on unknown symbols.  (This results in
@def .. @end being deleted if not known)." t nil)

;;;***

