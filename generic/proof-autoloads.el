;;; DO NOT MODIFY THIS FILE
(if (featurep 'proof-autoloads) (error "Already loaded"))

;;;### (autoloads (proof-easy-config) "proof-easy-config" "generic/proof-easy-config.el")

(autoload 'proof-easy-config "proof-easy-config" "\
Configure Proof General for proof-assistant using BODY as a setq body." nil 'macro)

;;;***

;;;### (autoloads (proof-indent-line) "proof-indent" "generic/proof-indent.el")

(autoload 'proof-indent-line "proof-indent" "\
Indent current line of proof script" t nil)

;;;***

;;;### (autoloads (proof-deftoggle proof-menu-define-specific proof-menu-define-main proof-menu-define-keys) "proof-menu" "generic/proof-menu.el")

(autoload 'proof-menu-define-keys "proof-menu" nil nil nil)

(autoload 'proof-menu-define-main "proof-menu" nil nil nil)

(autoload 'proof-menu-define-specific "proof-menu" nil nil nil)

(autoload 'proof-deftoggle "proof-menu" "\
Define a function VAR-toggle for toggling a boolean customize setting VAR.
The toggle function uses customize-set-variable to change the variable." nil 'macro)

;;;***

;;;### (autoloads nil "proof-script" "generic/proof-script.el")

;;;***

;;;### (autoloads (proof-shell-invisible-command proof-shell-wait proof-extend-queue proof-start-queue proof-shell-available-p proof-shell-live-buffer proof-shell-ready-prover) "proof-shell" "generic/proof-shell.el")

(autoload 'proof-shell-ready-prover "proof-shell" "\
Make sure the proof assistant is ready for a command.
If QUEUEMODE is set, succeed if the proof shell is busy but
has mode QUEUEMODE.
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
Busy wait for proof-shell-busy to become nil, or for TIMEOUT seconds.
Needed between sequences of commands to maintain synchronization,
because Proof General does not allow for the action list to be extended
in some cases.   May be called by proof-shell-invisible-command." nil nil)

(autoload 'proof-shell-invisible-command "proof-shell" "\
Send CMD to the proof process.  Add terminal string if necessary.
By default, let the command be processed asynchronously.
But if optional WAIT command is non-nil, wait for processing to finish
before and after sending the command.
If WAIT is an integer, wait for that many seconds afterwards." nil nil)

;;;***

;;;### (autoloads (proof-splash-display-screen) "proof-splash" "generic/proof-splash.el")

(autoload 'proof-splash-display-screen "proof-splash" "\
Save window config and display Proof General splash screen." nil nil)

;;;***

;;;### (autoloads (proof-toolbar-setup) "proof-toolbar" "generic/proof-toolbar.el")

(autoload 'proof-toolbar-setup "proof-toolbar" "\
Initialize Proof General toolbar and enable it for the current buffer.
If proof-mode-use-toolbar is nil, change the current buffer toolbar
to the default toolbar." t nil)

;;;***

;;;### (autoloads (proof-x-symbol-configure proof-x-symbol-mode proof-x-symbol-decode-region proof-x-symbol-enable) "proof-x-symbol" "generic/proof-x-symbol.el")

(autoload 'proof-x-symbol-enable "proof-x-symbol" "\
Turn on or off support for x-symbol, initializing if necessary.
Calls proof-x-symbol-toggle-clean-buffers afterwards." nil nil)

(autoload 'proof-x-symbol-decode-region "proof-x-symbol" "\
Call (x-symbol-decode-region A Z), if x-symbol support is enabled.
This converts tokens in the region into X-Symbol characters." nil nil)

(autoload 'proof-x-symbol-mode "proof-x-symbol" "\
Turn on/off x-symbol mode in current buffer, from proof-x-symbol-enable.
The X-Symbol minor mode is only useful in buffers where symbol input
takes place (it isn't used for output-only buffers)." t nil)

(autoload 'proof-x-symbol-configure "proof-x-symbol" "\
Configure the current buffer (goals or response) for X-Symbol." nil nil)

;;;***

;;;### (autoloads (texi-docstring-magic) "texi-docstring-magic" "generic/texi-docstring-magic.el")

(autoload 'texi-docstring-magic "texi-docstring-magic" "\
Update all texi docstring magic annotations in buffer." t nil)

;;;***

(provide 'proof-autoloads)
