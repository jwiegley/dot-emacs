;; proof-config.el  Proof General configuration for proof assistant
;;
;; Copyright (C) 1998-2002 LFCS Edinburgh. 
;; Author:      David Aspinall <da@dcs.ed.ac.uk> and others
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; This file declares all user options and prover-specific
;; configuration variables for Proof General.  The variables
;; are used variously by the proof script mode and the 
;; proof shell mode, menus, and toolbar.
;; 
;; To customize Proof General for a new proof assistant, you
;; should read this file carefully! 
;;
;;  1. User options 
;;      1b.  Faces
;;
;;     CONFIGURATION VARIABLES
;;  2. Major modes
;;  3. Menus, user-level commands, toolbar
;;  4. Script mode configuration 
;;  5. Shell mode configuration
;;     5a. commands
;;     5b. regexps
;;     5c. hooks and others
;;  6. Goals buffer configuration
;;  [ 7. Splash screen settings  -- moved to proof-splash.el now ]
;;  8. X-Symbol support
;;  9. Prover specific settings
;; 10. Global constants 
;;
;; The user options don't need to be set on a per-prover basis,
;; and the global constants probably should not be touched.
;; The remaining variables in sections 2-9 should be set for
;; each proof assistant.  You don't need to set every variable
;; for basic functionality; consult the manual for details of
;; which ones are important.
;;
;; Customization groups and structure (sections in brackets)
;;
;;  proof-general	      : Overall group
;;    proof-user-options      : User options for Proof General    (1)
;;    <ProverName>            : User options for proof assistant (9)
;;    <ProverName->-internals : Internal settings for proof assistant (9)
;;
;;  proof-general-internals  :  Internal settings of Proof General 
;;    prover-config	     :  Configuration for proof assistant (2,3)
;;      proof-script	     :     settings for proof script mode (4)
;;      proof-shell	     :     settings for proof shell mode (5)
;;      proof-goals	     :     settings for goals buffer (6)
;;      proof-x-symbol	     :     settings for X-Symbol (8)
;;    <Prover name>-config   :  Specific internal settings for a prover
;;
;; ==================================================
;;
;; Developers notes:
;;   i. When adding a new configuration variable, please
;;       (a) put it in the right customize group, and
;;       (b) add a magical comment in NewDoc.texi to document it!
;;  ii. Presently the customize library seems a bit picky over the
;;    	:type property and some correct but complex types don't work 
;;	properly.
;;    	If the type is ill-formed, editing the whole group will be broken.
;;    	Check after updates, by killing all customize buffers and
;;    	invoking customize-group
;;
;; ==================================================

(require 'proof-utils)			;; Macros used below


;;
;; 1. User options for proof mode
;;
;; The following variables are user options for Proof General.
;; They appear in the 'proof' customize group and should
;; *not* normally be touched by prover specific code.
;;

(defgroup proof-user-options nil
  "User options for Proof General."
  :group 'proof-general
  :prefix "proof-")

(defcustom proof-electric-terminator-enable nil 
  "*If non-nil, use electric terminator mode.
If electric terminator mode is enabled, pressing a terminator will 
automatically issue `proof-assert-next-command' for convenience,
to send the command straight to the proof process.  If the command
you want to send already has a terminator character, you don't
need to delete the terminator character first.  Just press the
terminator somewhere nearby.  Electric!"
  :type 'boolean
  :set 'proof-set-value
  :group 'proof-user-options)

(defcustom proof-toolbar-enable t
  "*If non-nil, display Proof General toolbar for script buffers.
NB: the toolbar is only available with XEmacs and GNU Emacs>=21."
  :type 'boolean
  :set 'proof-set-value
  :group 'proof-user-options)

(defpgcustom x-symbol-enable nil
  "*Whether to use x-symbol in Proof General for this assistant.
If you activate this variable, whether or not you really get x-symbol
support depends on whether your proof assistant supports it and
whether X-Symbol is installed in your Emacs."
  :type 'boolean
  :set 'proof-set-value
  :group 'proof-user-options)

(defcustom proof-output-fontify-enable t
  "*Whether to fontify output from the proof assistant.
If non-nil, output from the proof assistant will be highlighted
in the goals and response buffers.
(This is providing font-lock-keywords have been set for the 
buffer modes)."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-trace-output-fontify-enable t ;; testing
  ;; (not (and proof-running-on-XEmacs (>= emacs-major-version 21))) production
  "*Whether to fontify output from the proof assistant during tracing.
If non-nil and proof-output-fontify-enable is also non-nil, 
output from the proof assistant will be highlighted in the trace buffer.
This is not recommended in XEmacs 21, since the font-lock parser 
is easily overloaded by large tracing output."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-strict-state-preserving t
  "*Whether Proof General is strict about the state preserving test.
Proof General lets the user send arbitrary commands to the proof
engine with `proof-minibuffer-cmd'.  To attempt to preserve
synchronization, there may be a test `proof-state-preserving-p'
configured which prevents the user issuing certain commands
directly (instead, they may only be entered as part of the script).

Clever or arrogant users may want to avoid this test, which is
done if this `proof-strict-state-preserving' is turned off (nil)."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-strict-read-only 
  ;; For GNU Emacs, strict read only is buggy when used in
  ;; conjunction with font-lock.
  ;; The second conjunctive ensures that the expression is either
  ;; `nil' or `strict' (and not 15!!).  
  (and proof-running-on-XEmacs 'strict)
  "*Whether Proof General is strict about the read-only region in buffers.
If non-nil, an error is given when an attempt is made to edit the
read-only region.  If nil, Proof General is more relaxed (but may give
you a reprimand!).

If you change proof-strict-read-only during a session, you must 
use the \"Restart\" button (or M-x proof-shell-restart) before
you can see the effect in buffers.

The default value for proof-strict-read-only depends on which
version of Emacs you are using.  In GNU Emacs, strict read only is buggy
when it used in conjunction with font-lock, so it is disabled by default."
  :type 'boolean
  :group 'proof-user-options)


(defcustom proof-three-window-mode nil
  "*Whether response and goals buffers have dedicated windows.
If non-nil, Emacs windows displaying messages from the prover will not
be switchable to display other windows.

This option can help manage your display.

Setting this option triggers a three-buffer mode of interaction where
the goals buffer and response buffer are both displayed, rather than
the two-buffer mode where they are switched between.  It also prevents
Emacs automatically resizing windows between proof steps.  

If you use several frames (the same Emacs in several windows on the
screen), you can force a frame to stick to showing the goals or
response buffer.

For single frame use this option may be inconvenient for
experienced Emacs users."  
  ;; Did say: 
  ;; Moreover, this option may cause problems with multi-frame 
  ;; use because of a bug.  
  ;; but I can't find it as of 3.0pre201099.  
  :type 'boolean 
  :group 'proof-user-options)

(defcustom proof-multiple-frames-enable nil
  "*Whether response and goals buffers have separate frames.
If non-nil, Emacs will make separate frames (screen windows) for
the goals and response buffers, by altering the Emacs variable
`special-display-regexps'."  
  :type 'boolean 
  :set 'proof-set-value
  :group 'proof-user-options)

(defcustom proof-delete-empty-windows 
  nil
  "*If non-nil, automatically remove windows when they are cleaned.
For example, at the end of a proof the goals buffer window will
be cleared; if this flag is set it will automatically be removed.
If you want to fix the sizes of your windows you may want to set this
variable to 'nil' to avoid windows being deleted automatically.
If you use multiple frames, only the windows in the currently
selected frame will be automatically deleted."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-toolbar-use-button-enablers 
  (not
   (or 
    ;; Disabled by default for win32 and solaris
    proof-running-on-win32
    (and (boundp 'system-configuration)
	 (string-match "sun-solaris" system-configuration))))
  "*If non-nil, toolbars buttons may be enabled/disabled automatically.
Toolbar buttons can be automatically enabled/disabled according to
the context.  Set this variable to nil if you don't like this feature
or if you find it unreliable.

Notes: 
* Toolbar enablers are only available with XEmacs 21 and later.
* With this variable nil, buttons do nothing when they would
otherwise be disabled.
* If you change this variable it will only be noticed when you 
next start Proof General.
* The default value for XEmacs built for solaris is nil, because
of unreliabilities with enablers there."
  :type 'boolean
  :group 'proof-user-options)

; (defcustom proof-auto-retract 
;   nil
;   "*If non-nil, retract automatically when locked region is edited.
; With this option active, the locked region will automatically be
; unlocked when the user attempts to edit it.   To make use of this
; option, proof-strict-read-only should be turned off.

; Note: this feature has not been implemented yet, it is only an idea."
;   :type 'boolean
;   :group 'proof-user-options)

(defcustom proof-query-file-save-when-activating-scripting 
  t
"*If non-nil, query user to save files when activating scripting.

Often, activating scripting or executing the first scripting command
of a proof script will cause the proof assistant to load some files
needed by the current proof script.  If this option is non-nil, the
user will be prompted to save some unsaved buffers in case any of 
them corresponds to a file which may be loaded by the proof assistant.

You can turn this option off if the save queries are annoying, but
be warned that with some proof assistants this may risk processing 
files which are out of date with respect to the loaded buffers!"
  :type 'boolean
  :group 'proof-user-options)

(defpgcustom script-indent t
  "*If non-nil, enable indentation code for proof scripts."
  :type 'boolean 
  :group 'proof-user-options)

;; FIXME: implement it!  Use in indentation code.
(defcustom proof-one-command-per-line 
  nil
  "*If non-nil, format for newlines after each proof command in a script.
This option is not fully-functional at the moment."
  :type 'boolean
  :group 'proof-user-options)


(defcustom proof-prog-name-ask 
  nil
  "*If non-nil, query user which program to run for the inferior process."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-prog-name-guess 
  nil
  "*If non-nil, use `proof-guess-command-line' to guess proof-prog-name.
This option is compatible with proof-prog-name-ask.
No effect if proof-guess-command-line is nil."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-tidy-response
  t
  "*Non-nil indicates that the response buffer should be cleared often.
The response buffer can be set either to accumulate output, or to
clear frequently.  

With this variable non-nil, the response buffer is kept tidy by
clearing it often, typically between successive commands (just like the
goals buffer).  

Otherwise the response buffer will accumulate output from the prover."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-show-debug-messages nil
  "*Whether to display debugging messages in the response buffer.
If non-nil, debugging messages are displayed in the response giving
information about what Proof General is doing.
To avoid erasing the messages shortly after they're printed, 
you should set `proof-tidy-response' to nil."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-experimental-features 
  ;; Turn on experimental features for pre-releases.
  (if (string-match "pre" proof-general-version) t)
  "*Whether to enable certain features regarded as experimental.
Proof General includes a few features designated as \"experimental\".
Enabling these will usually have no detrimental effects on using PG,
but the features themselves may be buggy.

We encourage users to set this flag and test the features, but being
aware that the features may be buggy (problem reports and 
suggestions for improvements are welcomed)."
  :type 'boolean
  :group 'proof-user-options)

;;; NON BOOLEAN OPTIONS 

(defcustom proof-follow-mode 'locked
  "*Choice of how point moves with script processing commands.
One of the symbols: 'locked, 'follow, 'ignore.

If 'locked, point sticks to the end of the locked region.
If 'follow, point moves just when needed to display the locked region end.
If 'ignore, point is never moved after movement commands or on errors.

If you choose 'ignore, you can find the end of the locked using
`M-x proof-goto-end-of-locked'."
  :type '(choice
	  (const :tag "Follow locked region" locked)
	  (const :tag "Keep locked region displayed" follow)
	  (const :tag "Never move" ignore))
  :group 'proof-user-options)

(defcustom proof-auto-action-when-deactivating-scripting nil
  "*If 'retract or 'process, do that when deactivating scripting.

With this option set to 'retract or 'process, when scripting 
is turned off in a partly processed buffer, the buffer will be 
retracted or processed automatically.

With this option unset (nil), the user is questioned instead.

Proof General insists that only one script buffer can be partly
processed: all others have to be completely processed or completely
unprocessed.  This is to make sure that handling of multiple files
makes sense within the proof assistant.

NB: A buffer is completely processed when all non-whitespace is
locked (coloured blue); a buffer is completely unprocessed when there
is no locked region."
  :type '(choice
	  (const :tag "No automatic action; query user" nil)
	  (const :tag "Automatically retract" retract)
	  (const :tag "Automatically process" process))
  :group 'proof-user-options)

(defcustom proof-script-command-separator " "
  "*String separating commands in proof scripts.
For example, if a proof assistant prefers one command per line, then 
this string should be set to a newline.  Otherwise it should be
set to a space."
  :type 'string
  :group 'proof-user-options)

(defcustom proof-rsh-command ""
  "*Shell command prefix to run a command on a remote host.  
For example,

   ssh bigjobs

Would cause Proof General to issue the command `ssh bigjobs isabelle'
to start Isabelle remotely on our large compute server called `bigjobs'.

The protocol used should be configured so that no user interaction
(passwords, or whatever) is required to get going."
  :type 'string
  :group 'proof-user-options)

(defcustom proof-disappearing-proofs nil
  "*Non-nil causes Proof General to hide proofs as they are completed."
  :type 'boolean
  :group 'proof-user-options)





;;
;; 1b. Faces.
;;
;; We ought to test that these work sensibly:
;;   a) with default colours
;;   b) with -rv
;;   c) on console 
;;   d) on win32
;;   e) all above with GNU Emacs and XEmacs.
;; But it's difficult to keep track of all that!  
;; Please report any bad/failing colour 
;; combinations to proofgen@dcs.ed.ac.uk
;;
;; Some of these faces aren't used by default in Proof General,
;; but you can use them in font lock patterns for specific
;; script languages.
;;

(defgroup proof-faces nil
  "Faces used by Proof General."
  :group 'proof-general
  :prefix "proof-")
  
(defmacro proof-face-specs (bl bd ow)
  "Return a spec for `defface' with BL for light bg, BD for dark, OW o/w."
  `(append
    (apply 'append
     (mapcar 
     (lambda (ty) (list
		     (list (list (list 'type ty) '(class color)
			   (list 'background 'light))
			   (quote ,bl))
		     (list (list (list 'type ty) '(class color)
				 (list 'background 'dark))
			   (quote ,bd))))
     '(x mswindows gtk)))
    (list (list t (quote ,ow)))))

(defface proof-queue-face 
  (proof-face-specs 
   (:background "darksalmon") ;; was "mistyrose"
   (:background "mediumvioletred")
   (:foreground "white" :background "black"))
  "*Face for commands in proof script waiting to be processed."
  :group 'proof-faces)

(defface proof-locked-face
  (proof-face-specs
   (:background "lightsteelblue") ;; was "lavender", later "lightcyan".
   (:background "navy")
   (:underline t))
  "*Face for locked region of proof script (processed commands)."
  :group 'proof-faces)

(defface proof-declaration-name-face
  (proof-face-specs
   (:foreground "chocolate" :bold t)
   (:foreground "orange" :bold t)
   (:italic t :bold t))
  "*Face for declaration names in proof scripts.
Exactly what uses this face depends on the proof assistant."
  :group 'proof-faces)

;; FIXME da: are these defconsts still needed now we use defface?
;; Answer: yes, for GNU Emacs they are.

(defconst proof-declaration-name-face 'proof-declaration-name-face
  "Expression that evaluates to a face.
Required so that 'proof-declaration-name-face is a proper facename in
both XEmacs 20.4 and Emacs 20.2's version of font-lock.")

(defface proof-tacticals-name-face
  (proof-face-specs
   (:foreground "MediumOrchid3")
   (:foreground "orchid")
   (bold t))
  "*Face for names of tacticals in proof scripts.
Exactly what uses this face depends on the proof assistant."
  :group 'proof-faces)

(defconst proof-tacticals-name-face 'proof-tacticals-name-face
  "Expression that evaluates to a face.
Required so that 'proof-tacticals-name-face is a proper facename in
both XEmacs 20.4 and Emacs 20.3's version of font-lock.")

(defface proof-tactics-name-face
  '((t				
     (bold t)))
  "*Face for names of tactics in proof scripts.
By default, they are printed with default face but the user
may want to color them differently."
  :group 'proof-faces)

(defconst proof-tactics-name-face 'proof-tactics-name-face
  "Expression that evaluates to a face.
Required so that 'proof-tactics-name-face is a proper facename in
both XEmacs 20.4 and Emacs 20.3's version of font-lock.")

(defface proof-error-face 
  (proof-face-specs
   (:background "salmon1" :bold t)
   (:background "brown" :bold t)
   (:bold t))
  "*Face for error messages from proof assistant."
  :group 'proof-faces)

(defface proof-warning-face
  (proof-face-specs
   (:background "lemon chiffon")
   (:background "orange2")
   (:italic t))
  "*Face for warning messages.
Warning messages can come from proof assistant or from Proof General itself."
  :group 'proof-faces)

(defface proof-eager-annotation-face
  (proof-face-specs
   (:background "palegoldenrod")
   (:background "darkgoldenrod")
   (:italic t))
  "*Face for important messages from proof assistant."
  :group 'proof-faces)

(defface proof-debug-message-face
  (proof-face-specs
   (:foreground "Gray65")
   (:background "Gray30")
   (:italic t))
  "*Face for debugging messages from Proof General."
  :group 'proof-faces)

(defface proof-boring-face
  (proof-face-specs
   (:foreground "Gray65")
   (:background "Gray30")
   (:italic t))
  "*Face for boring text in proof assistant output."
  :group 'proof-faces)

(defface proof-mouse-highlight-face
  (proof-face-specs
   (:background "paleturquoise")
   (:background "steelblue")
   (:italic t))
  "*General mouse highlighting face."
  :group 'proof-faces)

(defface proof-highlight-dependent-face
  (proof-face-specs
   (:background "orange")
   (:background "darkorange")
   (:italic t))
  "*Face for showing (backwards) dependent parts."
  :group 'proof-faces)
  
(defface proof-highlight-dependency-face
  (proof-face-specs
   (:background "khaki")
   (:background "peru")
   (:italic t))
  "*Face for showing (forwards) dependencies."
  :group 'proof-faces)





;;
;; START OF CONFIGURATION VARIABLES
;;
;; Prelude
;;

(defgroup prover-config nil
  "Configuration of Proof General for the prover in use."
  :group 'proof-general-internals
  :prefix "proof-")

;; The variables in the "prover-config" (NB: not "proof config"!!)
;; customize group are those which are intended to be set by the
;; prover specific elisp, i.e. constants set on a per-prover basis.

;; Putting these in a customize group is useful for documenting
;; this type of variable, and for developing a new instantiation
;; of Proof General.
;; But it is *not* useful for final user-level customization!
;; The reason is that saving these customizations across a session is
;; not liable to work, because the prover specific elisp usually
;; overrides with a series of setq's in <assistant>-mode-config type
;; functions.  This is why prover-config appears under the
;; proof-general-internal group.








;;
;; 2. Major modes used by Proof General.
;;
;; The first three settings are used when starting a shell,
;; so the must be set before a shell is started, so we
;; know what modes are needed for each of the buffers.
;; Hence the use of pre-shell-start-hook.

(defcustom proof-mode-for-shell 'proof-shell-mode
  "Mode for proof shell buffers.
Usually customised for specific prover.
Suggestion: this can be set a function called by `proof-pre-shell-start-hook'."
  :type 'function
  :group 'prover-config)

(defcustom proof-mode-for-response 'proof-response-mode
  "Mode for proof response buffer (and trace buffer, if used).
Usually customised for specific prover.
Suggestion: this can be set a function called by `proof-pre-shell-start-hook'."
  :type 'function
  :group 'prover-config)

(defcustom proof-mode-for-goals 'proof-goals-mode
  "Mode for proof state display buffers.
Usually customised for specific prover.
Suggestion: this can be set a function called by `proof-pre-shell-start-hook'."
  :type 'function
  :group 'prover-config)

(defcustom proof-mode-for-script 'proof-mode
  "Mode for proof script buffers.
This is used by Proof General to find out which buffers 
contain proof scripts.
The regular name for this is <PA>-mode.  If you use any of the
convenience macros Proof General provides for defining commands
etc, then you should stick to this name.
Suggestion: this can be set in the script mode configuration."
  :type 'function
  :group 'prover-config)

(defcustom proof-guess-command-line nil
  "Function to guess command line for proof assistant, given a filename.
The function could take a filename as argument, run `make -n' to see
how to compile the file non-interactively, then translate the result 
into an interactive invocation of the proof assistant with the same 
command line options.  For an example, see coq/coq.el."
  :type 'function
  :group 'prover-config)



;;
;; 3. Configuration for menus, user-level commands, toolbar, etc.
;;

(defcustom proof-assistant-home-page ""
  "Web address for information on proof assistant.
Used for Proof General's help menu."
  :type 'string
  :group 'prover-config)

(defcustom proof-context-command nil
  "Command to display the context in proof assistant."
  :type 'string
  :group 'prover-config)

(defcustom proof-info-command nil
  "Command to ask for help or information in the proof assistant.
String or fn.  If a string, the command to use. 
If a function, it should return the command string to insert."
  :type '(choice string function)
  :group 'prover-config)

(defcustom proof-showproof-command nil
  "Command to display proof state in proof assistant."
  :type 'string
  :group 'prover-config)

(defcustom proof-goal-command nil
  "Command to set a goal in the proof assistant.  String or fn.
If a string, the format character `%s' will be replaced by the
goal string. 
If a function, it should return the command string to insert."
  :type '(choice string function)
  :group 'prover-config)

(defcustom proof-save-command nil
  "Command to save a proved theorem in the proof assistant.  String or fn.
If a string, the format character `%s' will be replaced by the
theorem name. 
If a function, it should return the command string to insert."
  :type '(choice string function)
  :group 'prover-config)

(defcustom proof-find-theorems-command nil
  "Command to search for a theorem containing a given term. String or fn.
If a string, the format character `%s' will be replaced by the term.
If a function, it should return the command string to insert."
  :type '(choice string function)
  :group 'prover-config)

(defconst proof-toolbar-entries-default
  `((state	"Display Proof State" "Display the current proof state" t 
		proof-showproof-command)
    (context	"Display Context" "Display the current context" t 
		proof-context-command)
    (goal	"Start a New Proof"   "Start a new proof" t
		proof-goal-command)
    (retract	"Retract Buffer"      "Retract (undo) whole buffer" t)
    (undo	"Undo Step"           "Undo the previous proof command" t)
    (delete	"Delete Step"         nil t)
    (next	"Next Step"           "Process the next proof command" t)
    (use	"Use Buffer"  	      "Process whole buffer" t)
    (goto	"Goto Point"	      "Process or undo to the cursor position" t)
    (restart	"Restart Scripting"   "Restart scripting (clear all locked regions)" t)
    (qed	"Finish Proof"        "Close/save proved theorem" t
		proof-save-command)
    (lockedend  "Locked End"	      nil t)
    (find	"Find Theorems"	      "Find theorems" t
		proof-find-theorems-command)
    (command    "Issue Command"	      "Issue a non-scripting command" t)
    (interrupt  "Interrupt Prover"    "Interrupt the proof assistant (warning: may break synchronization)" t)
    (show       "Show Proofs"         nil t)
    (hide       "Hide Proofs"	      nil t)
    (info	nil		      "Show online proof assistant information" t
		proof-info-command)
    (help	nil		      "Proof General manual" t))
"Example value for proof-toolbar-entries.  Also used to define scripting menu.
This gives a bare toolbar that works for any prover, providing the
appropriate configuration variables are set.
To add/remove prover specific buttons, adjust the `<PA>-toolbar-entries' 
variable, and follow the pattern in `proof-toolbar.el' for 
defining functions, images.")

(defpgcustom toolbar-entries proof-toolbar-entries-default
  "List of entries for Proof General toolbar and Scripting menu.
Format of each entry is (TOKEN MENUNAME TOOLTIP DYNAMIC-ENABLER-P ENABLE).

For each TOKEN, we expect an icon with base filename TOKEN,
a function proof-toolbar-<TOKEN>, and (optionally) a dynamic enabler 
proof-toolbar-<TOKEN>-enable-p.

If ENABLEP is absent, item is enabled; if ENABLEP is present, item
is only added to menubar and toolbar if ENABLEP is non-null.

If MENUNAME is nil, item will not appear on the scripting menu.

If TOOLTIP is nil, item will not appear on the toolbar.

The default value is `proof-toolbar-entries-default' which contains
the standard Proof General buttons.")

(defcustom proof-assistant-true-value "true"
  "String for true values in proof assistant, used for setting flags.
Default is the string \"true\"."
  :type 'string
  :group 'prover-config)

(defcustom proof-assistant-false-value "false"
  "String for false values in proof assistant, used for setting flags.
Default is the string \"false\"."
  :type 'string
  :group 'prover-config)

(defcustom proof-assistant-format-int-fn 'int-to-string
  "Function for converting integer values to ints in proof assistant.
Used for configuring settings in proof assistant.
Default is `int-to-string'."
  :type 'function
  :group 'prover-config)

(defcustom proof-assistant-format-string-fn  (lambda (value) value)
  "Function for converting string values to strings in proof assistant.
Used for configuring settings in proof assistant.
Default is the identity function."
  :type 'string
  :group 'prover-config)

(defcustom proof-assistant-setting-format nil
  "Function for formatting setting strings for proof assistant.
Setting strings are calculated by replacing a format character
%b, %i, or %s in the :setting string in for each variable defined with
`defpacustom', using the current value of that variable.  This
function  is applied as a final step to do any extra markup, or
conversion, etc.  (No changes are done if nil)."
  :type '(choice string nil)
  :group 'prover-config)



;;
;; 4. Configuration for proof script mode
;;

;;
;; The following variables should be set before proof-config-done
;; is called.  These configure the mode for the script buffer,
;; including highlighting, etc.
;;

(defgroup proof-script nil
  "Proof General configuration of scripting buffer mode."
  :group 'prover-config
  :prefix "proof-")

(defcustom proof-terminal-char nil
  "Character which terminates every command sent to proof assistant.  nil if none.

To configure command recognition properly, you must set at least one
of these: `proof-script-sexp-commands', `proof-script-command-end-regexp', 
`proof-script-command-start-regexp', `proof-terminal-char',
or `proof-script-parse-function'."
  :type 'character
  :group 'prover-config)

(defcustom proof-script-sexp-commands nil
  "Non-nil if proof script has a LISP-like syntax, and commands are top-level sexps.
You should set this variable in script mode configuration.

To configure command recognition properly, you must set at least one
of these: `proof-script-sexp-commands', `proof-script-command-end-regexp', 
`proof-script-command-start-regexp', `proof-terminal-char',
or `proof-script-parse-function'."
  :type 'boolean
  :group 'prover-config)

(defcustom proof-script-command-end-regexp nil
  "Regular expression which matches end of commands in proof script.
You should set this variable in script mode configuration.

To configure command recognition properly, you must set at least one
of these: `proof-script-sexp-commands', `proof-script-command-end-regexp', 
`proof-script-command-start-regexp', `proof-terminal-char',
or `proof-script-parse-function'."
  :type 'string
  :group 'prover-config)

(defcustom proof-script-command-start-regexp nil
  "Regular expression which matches start of commands in proof script.
You should set this variable in script mode configuration.

To configure command recognition properly, you must set at least one
of these: `proof-script-sexp-commands', `proof-script-command-end-regexp', 
`proof-script-command-start-regexp', `proof-terminal-char',
or `proof-script-parse-function'."
  :type 'string
  :group 'prover-config)

(defcustom proof-script-use-old-parser t ;; nil ;;experiment and let folk complain 
  "Whether to use the old parsing mechanism.
This is a stop-gap option in Proof General 3.4 added for
proof assistants which still depend on peculiarities of the old
parsing functions. (Specific example: Isar relies on certain
text being sent to prover which according to syntax configuration
are comments; new parser does not send these currently.)"
  :type 'boolean
  :group 'prover-config)

(defcustom proof-script-integral-proofs nil
  "Whether the complete text after a goal confines the actual proof.

In structured proof languages like Isabelle/Isar a theorem is
established by a goal statement (with full information about the
result, including name and statement), followed by a self-contained
piece of text for the proof.  The latter should be treated as an
integral entity for purposes of hiding proof bodies etc.

This variable is better set to nil for tactical provers (like Coq)
where important information about the result is spread over the
initial ``goal'' and the final ``save'' command."
  :type 'boolean
  :group 'prover-config)

;; Unadvertised customization variable
(defvar proof-script-fly-past-comments t
  "*If non-nil, fly past comments when scripting, coalescing them into single spans.")



(defcustom proof-script-parse-function nil
  "A function which parses a portion of the proof script.
It is called with the proof script as the current buffer, and
point the position where the parse should begin.  It should
move point to the exact end of the next \"segment\", and return 
a symbol indicating what has been parsed:

  'comment	for a comment 
  'cmd		for a proof script command
  nil		if there is no complete next segment in the buffer

If this is left unset, it will be configured automatically to
a generic function according to which of `proof-terminal-char' 
and its friends are set."
  :type 'string
  :group 'prover-config)


(defcustom proof-script-comment-start ""
  "String which starts a comment in the proof assistant command language.
The script buffer's comment-start is set to this string plus a space.
Moreover, comments are usually ignored during script management, and not
sent to the proof process.

You should set this variable for reliable working of Proof General,
as well as `proof-script-comment-end'."
  :type 'string
  :group 'proof-script)

(defcustom proof-script-comment-start-regexp nil
  "Regexp which matches a comment start in the proof command language.

The default value for this is set as (regexp-quote proof-script-comment-start)
but you can set this variable to something else more precise if necessary."
  :type 'string
  :group 'proof-script)

(defcustom proof-script-comment-end "\n"
  "String which ends a comment in the proof assistant command language.
The script buffer's comment-end is set to a space plus this string.
See also `proof-script-comment-start'.

You should set this variable for reliable working of Proof General,"
  :type 'string
  :group 'proof-script)

(defcustom proof-script-comment-end-regexp nil
  "Regexp which matches a comment end in the proof command language.

The default value for this is set as (regexp-quote proof-script-comment-end)
but you can set this variable to something else more precise if necessary."
  :type 'string
  :group 'proof-script)

(defcustom pg-insert-output-as-comment-fn nil
  "Function to insert last output as a comment.  Passed output as arg.
If left as nil, the default behaviour is to insert and call `comment-region'."
  :type '(choice function nil)
  :group 'proof-script)

(defcustom proof-string-start-regexp "\""
  "Matches the start of a quoted string in the proof assistant command language."
  :type 'string
  :group 'proof-script)

(defcustom proof-string-end-regexp "\""
  "Matches the end of a quoted string in the proof assistant command language."
  :type 'string
  :group 'proof-script)

(defcustom proof-case-fold-search nil
  "Value for case-fold-search when recognizing portions of proof scripts.
Also used for completion, via `proof-script-complete'.
The default value is `nil'.  If your prover has a case *insensitive*
input syntax, proof-case-fold-search should be set to `t' instead.  
NB: This setting is not used for matching output from the prover."  
  :type 'boolean :group
  'proof-script)

(defcustom proof-save-command-regexp nil 
  "Matches a save command."
  :type 'regexp
  :group 'proof-script)

(defcustom proof-save-with-hole-regexp nil 
  "Regexp which matches a command to save a named theorem.
The name of the theorem is build from the variable
proof-save-with-hole-result using the same convention as 
query-replace-regexp. 
Used for setting names of goal..save and proof regions and for 
default function-menu configuration in proof-script-find-next-entity.

It's safe to leave this setting as nil."
  :type 'regexp
  :group 'proof-script)

(defcustom proof-save-with-hole-result 2 
  "String or Int: how to build the theorem name after matching
with proof-save-with-hole-regexp. If it is an int N use match-string 
to recover the value of the Nth parenthesis matched. If it is a string
use replace-match. It the later case, proof-save-with-hole-regexp should
match the entire command"

  :type '(choice string int)
  :group 'proof-script)

;; FIXME: unify uses so that proof-anchor-regexp works sensibly
(defcustom proof-goal-command-regexp nil
  "Matches a goal command in the proof script.   
This is used (1) to make the default value for `proof-goal-command-p',
used as an important part of script management to find the start
of an atomic undo block, and (2) to construct the default 
for `proof-script-next-entity-regexps' used for function menus."
  :type 'regexp
  :group 'proof-script)

(defcustom proof-goal-with-hole-regexp nil 
  "Regexp which matches a command used to issue and name a goal.
The name of the theorem is build from the variable
proof-goal-with-hole-result using the same convention as 
query-replace-regexp. 
Used for setting names of goal..save regions and for default
function-menu configuration in proof-script-find-next-entity.

It's safe to leave this setting as nil."
  :type 'regexp
  :group 'proof-script)

(defcustom proof-goal-with-hole-result 2
  "String or Int: how to build the theorem name after matching
with proof-goal-with-hole-regexp. If it is an int N use match-string 
to recover the value of the Nth parenthesis matched. If it is a string
use replace-match. It the later case, proof-goal-with-hole-regexp should
match the entire command"

  :type '(choice string int)
  :group 'proof-script)

(defcustom proof-non-undoables-regexp nil
  "Regular expression matching commands which are *not* undoable.
These are commands which should not appear in proof scripts,
for example, undo commands themselves (if the proof assistant
cannot \"redo\" an \"undo\").
Used in default functions `proof-generic-state-preserving-p' 
and `proof-generic-count-undos'.  If you don't use those,
may be left as nil."
  :type '(choice nil regexp)
  :group 'proof-script)

(defcustom proof-nested-undo-regexp nil
  "Regexp for commands that must be counted in nested goal-save regions.

Used for provers which allow nested atomic goal-saves, but with some
nested history that must be undone specially.

At the moment, the behaviour is that a goal-save span has a 'nestedundos
property which is set to the number of commands within it which match
this regexp.  The idea is that the prover-specific code can create a
customized undo command to retract the goal-save region, based on the
'nestedundos setting.  Coq uses this to forget declarations, since
declarations in Coq reside in a separate context with its own (flat)
history."
  :type '(choice nil regexp)
  :group 'proof-script)

(defcustom proof-ignore-for-undo-count nil
  "Matcher for script commands to be ignored in undo count.
May be left as nil, in which case it will be set to
`proof-non-undoables-regexp'.
Used in default function `proof-generic-count-undos'."
  :type '(choice nil regexp function)
  :group 'proof-script)

(defcustom proof-script-next-entity-regexps nil
  "Regular expressions to help find definitions and proofs in a script.
This is the list of the form

   (ANYENTITY-REGEXP
    DISCRIMINATOR-REGEXP  ... DISCRIMINATOR-REGEXP)

The idea is that ANYENTITY-REGEXP matches any named entity in the
proof script, on a line where the name appears.  This is assumed to be
the start or the end of the entity.  The discriminators then test
which kind of entity has been found, to get its name.  A
DISCRIMINATOR-REGEXP has one of the forms

  (REGEXP MATCHNOS)
  (REGEXP MATCHNOS 'backward BACKREGEXP)
  (REGEXP MATCHNOS 'forward FORWARDREGEXP)

If REGEXP matches the string captured by ANYENTITY-REGEXP, then
MATCHNOS are the match numbers for the substrings which name the entity
(these may be either a single number or a list of numbers).

If 'backward BACKREGEXP is present, then the start of the entity
is found by searching backwards for BACKREGEXP.

Conversely, if 'forward FORWARDREGEXP is found, then the end of
the entity is found by searching forwards for FORWARDREGEXP.

Otherwise, the start and end of the entity will be the region matched
by ANYENTITY-REGEXP.

This mechanism allows fairly complex parsing of the buffer, in
particular, it allows for goal..save regions which are named
only at the end.  However, it does not parse strings,
comments, or parentheses.

This variable may not need to be set: a default value which should
work for goal..saves is calculated from proof-goal-with-hole-regexp,
proof-goal-command-regexp, and proof-save-with-hole-regexp."
  :type 'sexp
    ;; Bit tricky.
    ;; (list (regexp :tag "Any entity matcher")
    ;;    (:inline t repeat (choice regexp (const 'backward) etc
  :group 'proof-script)

(defcustom proof-script-find-next-entity-fn
  'proof-script-find-next-entity
  "Name of function to find next interesting entity in a script buffer.
This is used to configure func-menu.  The default value is
proof-script-find-next-entity, which searches for the next entity
based on fume-function-name-regexp which by default is set from
proof-script-next-entity-regexps.  

The function should move point forward in a buffer, and return a cons
cell of the name and the beginning of the entity's region.

Note that proof-script-next-entity-regexps is set to a default value
from proof-goal-with-hole-regexp and proof-save-with-hole-regexp in
the function proof-config-done, so you may not need to worry about any
of this.  See whether function menu does something sensible by
default."
  :type 'function
  :group 'proof-script)

;; FIXME da: This next one is horrible.  We clearly would rather
;; have just proof-goal-command regexp instead.  This was born to solve
;; problem that Coq can have goals which look like definitions, etc.
;; Perhaps we can generalise the matching to understand function
;; values as well as regexps. 
;; FIXME: could just as easily give default value of 
;; proof-std-goal-command-p here, why not?
(defcustom proof-goal-command-p 'proof-generic-goal-command-p
  "A function to test: is this really a goal command?

This is added as a more refined addition to proof-goal-command-regexp,
to solve the problem that Coq and some other provers can have goals which 
look like definitions, etc.  (In the future we may generalize 
proof-goal-command-regexp instead)."
  :type 'function
  :group 'proof-script)

;; FIXME mmw: increasing the horror even more ...
;; FIXME da: why do you need the span below?   I would like to replace
;;  this mess by single config variables which are allowed to be
;;  regexps or functions, handled in proof-string-match.
;; FIXME mmw: the span is required to scan backwards through the text,
;;  determining the depth of proof nesting.
;; FIXME da: yuck!  What I'd really like to replace the mess with is
;;  feedback from the proof assistant, saying "that was a save", etc.
;; FIXME mmw: all we need is some tracking of the 'depth' of commands;
;;  Why not let PG track this as in spans, changing the value based
;;  on some regexps for 'open' / 'close' commands? This would basically
;;  move the code of isar-global-save-command-p to proof-done-advancing.
;; FIXME da: sounds like a good idea, then that would give us a proper 
;;  handling of nested proofs?
;;
(defcustom proof-really-save-command-p (lambda (span cmd) t)
  "Is this really a save command?

This is a more refined addition to proof-save-command-regexp.
It should be a function taking a span and command as argument,
and can be used to track nested proofs.  (See what is done in
isar/ for example). In the future, this setting should be
removed when the generic core is extended to handle nested
proofs smoothly."
  :type 'function
  :group 'proof-script)

(defcustom proof-completed-proof-behaviour nil
  "Indicates how Proof General treats commands beyond the end of a proof.
Normally goal...save regions are \"closed\", i.e. made atomic for undo.
But once a proof has been completed, there may be a delay before 
the \"save\" command appears --- or it may not appear at all.  Unless
nested proofs are supported, this can spoil the undo-behaviour in
script management since once a new goal arrives the old undo history
may be lost in the prover.  So we allow Proof General to close 
off the goal..[save] region in more flexible ways.  
The possibilities are:

        nil  -  nothing special; close only when a save arrives
  'closeany  -  close as soon as the next command arrives, save or not
 'closegoal  -  close when the next \"goal\" command arrives
    'extend  -  keep extending the closed region until a save or goal.

If your proof assistant allows nested goals, it will be wrong to close
off the portion of proof so far, so this variable should be set to nil."
  :type '(choice
	  (const :tag "Close on save only" nil)
	  (const :tag "Close next command" closeany)
	  (const :tag "Close next goal" closegoal)
	  (const :tag "Extend" ignore))
  :group 'proof-script)

(defcustom proof-count-undos-fn 'proof-generic-count-undos
  "Function to calculate a command to issue undos to reach a target span.
The function takes a span as an argument, and should return a string
which is the command to undo to the target span.  The target is
guaranteed to be within the current (open) proof.
This is an important function for script management.
The default setting `proof-generic-count-undos' is based on the
settings `proof-non-undoables-regexp' and
`proof-non-undoables-regexp'."
  :type 'function
  :group 'proof-script)

; Not yet implemented.
;
;(defcustom proof-atomic-sequence-lists nil
;  "list of instructions for setting up atomic sequences of commands (ACS).

;Each instruction is
;a list of the form `(END START &optional FORGET-COMMAND)'. END is a
;regular expression to recognise the last command in an ACS. START
;is a function. Its input is the last command of an ACS. Its output
;is a regular exression to recognise the first command of the ACS.
;It is evaluated once and the output is successively matched agains
;previously processed commands until a match occurs (or the
;beginning of the current buffer is reached). The region determined
;by (START,END) is locked as an ACS. Optionally, the ACS is
;annotated with the actual command to retract the ACS. This is
;computed by applying FORGET-COMMAND to the first and last command
;of the ACS."
;  ;; FIXME customize broken on choices with function in them?
;  ;;:type '(repeat (cons regexp function (choice (const nil) function)))
;  :type '(repeat (cons regexp function function))
;  :group 'proof-shell)


(defconst proof-no-command "COMMENT"
  "String used as a nullary action (send no command to the proof assistant).
Only relevant for proof-find-and-forget-fn.
(NB: this is a CONSTANT, don't change it).")

(defcustom proof-find-and-forget-fn 'proof-generic-find-and-forget
  "Function that returns a command to forget back to before its argument span.
This setting is used to for retraction (undoing) in proof scripts.

It should undo the effect of all settings between its target span
up to (proof-locked-end).  This may involve forgetting a number
of definitions, declarations, or whatever.

The special string proof-no-command means there is nothing to do.

This is an important function for script management.
Study one of the existing instantiations for examples of how to write it,
or leave it set to the default function `proof-generic-find-and-forget'
(which see)."
  :type 'function
  :group 'proof-script)

(defcustom proof-forget-id-command nil
  "Command to forget back to a given named span.
A string; `%s' will be replaced by the name of the span.

This is only used in the implementation of `proof-generic-find-and-forget',
you only need to set if you use that function (by not customizing
`proof-find-and-forget-fn'."
  :type 'string
  :group 'proof-script)

(defcustom pg-topterm-goalhyp-fn nil
  "Function which returns cons cell if point is at a goal/hypothesis.
This is used to parse the proofstate output to mark it up for
proof-by-pointing.  It should return a cons or nil.  First element of
the cons is a symbol, 'goal' or 'hyp'.  The second element is a
string: the goal or hypothesis itself.

If you leave this variable unset, no proof-by-pointing markup
will be attempted."
  :type '(choice function nil)
  :group 'proof-script)

(defcustom proof-kill-goal-command ""
  "Command to kill the currently open goal.

If this is set to nil, PG will expect proof-find-and-forget-fn
to do all the work of retracting to an arbitrary point in a file.
Otherwise, the generic split-phase mechanism will be used:

  1. If inside an unclosed proof, use proof-count-undos.
  2. If retracting to before an unclosed proof, use 
     proof-kill-goal-command, followed by proof-find-and-forget-fn
     if necessary."
  :type 'string
  :group 'proof-script)

(defcustom proof-undo-n-times-cmd nil
  "Command to undo n steps of the currently open goal.
String or function.
If this is set to a string, `%s' will be replaced by the number of
undo steps to issue. 
If this is set to a function, it should return the appropriate
command when called with an integer (the number of undo steps).

This setting is used for the default `proof-generic-count-undos'.
If you set `proof-count-undos-fn' to some other function, there is no
need to set this variable."
  :type '(or string function)
  :group 'proof-script)

(defcustom proof-nested-goals-history-p nil
  "Whether the prover supports recovery of history for nested proofs.
If it does (non-nil), Proof General will retain history inside 
nested proofs.
If it does not, Proof General will amalgamate nested proofs into single
steps within the outer proof."
  :type 'boolean
  :group 'proof-script)

(defcustom proof-state-preserving-p 'proof-generic-state-preserving-p
  "A predicate, non-nil if its argument (a command) preserves the proof state.
This is a safety-test used by proof-minibuffer-cmd to filter out scripting
commands which should be entered directly into the script itself.

The default setting for this function, `proof-generic-state-preserving-p'
tests by negating the match on `proof-non-undoables-regexp'."
  :type 'function
  :group 'proof-script)

(defcustom proof-activate-scripting-hook nil
  "Hook run when a buffer is switched into scripting mode.
The current buffer will be the newly active scripting buffer.

This hook may be useful for synchronizing with the proof
assistant, for example, to switch to a new theory
(in case that isn't already done by commands in the proof
script).

When functions in this hook are called, the variable
`activated-interactively' will be non-nil if 
proof-activate-scripting was called interactively
(rather than as a side-effect of some other action).
If a hook function sends commands to the proof process,
it should wait for them to complete (so the queue is cleared
for scripting commands), unless activated-interactively is set."
  :type '(repeat function)
  :group 'proof-script)

;;
;; Proof script indentation
;;

(defcustom proof-indent 2
  "Amount of proof script indentation."
  :type 'number
  :group 'proof-script)

(defcustom proof-indent-hang nil
  "Enable 'hanging' indentation for proof script."
  :type 'boolean
  :group 'proof-script)

(defcustom proof-indent-enclose-offset 1
  "Extra offset for enclosing indentation syntax elements."
  :type 'number
  :group 'proof-script)

(defcustom proof-indent-open-offset 1
  "Extra offset for opening indentation syntax elements."
  :type 'number
  :group 'proof-script)

(defcustom proof-indent-close-offset 1
  "Extra offset for closing indentation syntax elements."
  :type 'number
  :group 'proof-script)

(defcustom proof-indent-any-regexp "\\s(\\|\\s)"
  "Regexp for *any* syntax element guiding proof script indentation."
  :type 'string
  :group 'proof-script)

(defcustom proof-indent-inner-regexp nil
  "Regexp for text within syntax elements of proof script indentation."
  :type 'string
  :group 'proof-script)

(defcustom proof-indent-enclose-regexp nil
  "Regexp for enclosing syntax elements of proof script indentation."
  :type 'string
  :group 'proof-script)

(defcustom proof-indent-open-regexp "\\s("
  "Regexp for opening syntax elements of proof script indentation."
  :type 'string
  :group 'proof-script)

(defcustom proof-indent-close-regexp "\\s)"
  "Regexp for closing syntax elements of proof script indentation."
  :type 'string
  :group 'proof-script)


(defcustom proof-font-lock-zap-commas nil
  "If non-nil, enable a font-lock hack which unfontifies commas.
If you fontify variables inside lists like [a,b,c] by matching
on the brackets `[' and `]', you may take objection to the commas 
being coloured as well.  In that case, enable this hack which
will magically restore the commas to the default font for you.

The hack is rather painful and forces immediate fontification of
files on loading (no lazy, caching locking).  It is unreliable
under GNU Emacs, to boot.

LEGO and Coq enable it by tradition."
  :type 'boolean
  :group 'proof-script)

(defcustom proof-script-font-lock-keywords nil
  "Value of font-lock-keywords used to fontify proof scripts.
This is currently used only by proof-easy-config mechanism,
to set font-lock-keywords before calling proof-config-done.
See also proof-{shell,resp,goals}-font-lock-keywords."
  :type 'sexp
  :group 'proof-script)





;;
;;  5. Configuration for proof shell	                            
;;
;; The variables in this section concern the proof shell mode.
;; The first group of variables are hooks invoked at various points.
;; The second group of variables are concerned with matching the output
;; from the proof assistant.
;;
;; Variables here are put into the customize group 'proof-shell'.
;;
;; These should be set in the shell mode configuration, again,
;; before proof-shell-config-done is called.
;;

(defgroup proof-shell nil
  "Settings for output from the proof assistant in the proof shell."
  :group 'prover-config
  :prefix "proof-shell-")


;; 
;; 5a. commands
;;

(defcustom proof-prog-name nil
  "System command to run the proof assistant in the proof shell.
Suggestion: this can be set in proof-pre-shell-start-hook from
a variable which is in the proof assistant's customization
group.  This allows different proof assistants to coexist
(albeit in separate Emacs sessions)."
  :type 'string
  :group 'proof-shell)

(defcustom proof-shell-auto-terminate-commands t
  "Non-nil if Proof General should try to add terminator to every command.
If non-nil, whenever a command is sent to the prover using
`proof-shell-invisible-command', Proof General will check to see if it
ends with proof-terminal-char, and add it if not.
If proof-terminal-char is nil, this has no effect."
  :type 'boolean
  :group 'proof-shell)

(defcustom proof-shell-pre-sync-init-cmd nil
   "The command for configuring the proof process to gain synchronization.
This command is sent before Proof General's synchronization
mechanism is engaged, to allow customization inside the process
to help gain syncrhonization (e.g. engaging special markup).

It is better to configure the proof assistant for this purpose
via command line options if possible, in which case this variable 
does not need to be set.

See also `proof-shell-init-cmd'."
   :type '(choice string (const nil))
   :group 'proof-shell)

(defcustom proof-shell-init-cmd nil
   "The command for initially configuring the proof process.
This command is sent to the process as soon as synchronization is gained
(when an annotated prompt is first recognized).  It can be used to configure 
the proof assistant in some way, or print a welcome message
(since output before the first prompt is discarded).

See also `proof-shell-pre-sync-init-cmd'."
   :type '(choice string (const nil))
   :group 'proof-shell)

(defcustom proof-shell-restart-cmd ""
   "A command for re-initialising the proof process."
   :type '(choice string (const nil))
   :group 'proof-shell)

(defcustom proof-shell-quit-cmd nil
  "A command to quit the proof process.  If nil, send EOF instead."
   :type '(choice string (const nil))
   :group 'proof-shell)

(defcustom proof-shell-quit-timeout 4
  ;; FIXME could add option to quiz user before rude kill.
  "The number of seconds to wait after sending proof-shell-quit-cmd.
After this timeout, the proof shell will be killed off more rudely.
If your proof assistant takes a long time to clean up (for
example writing persistent databases out or the like), you may
need to bump up this value."
   :type '(choice string (const nil))
   :group 'proof-shell)

(defcustom proof-shell-cd-cmd nil
  "Command to the proof assistant to change the working directory.
The format character `%s' is replaced with the directory, and
the escape sequences in `proof-shell-filename-escapes' are 
applied to the filename.

This setting is used to define the function proof-cd which 
changes to the value of (default-directory) for script buffers.
For files, the value of (default-directory) is simply the
directory the file resides in.

NB: By default, proof-cd is called from proof-activate-scripting-hook,
so that the prover switches to the directory of a proof
script every time scripting begins."
  :type 'string
  :group 'proof-shell)

(defcustom proof-shell-start-silent-cmd nil
  "Command to turn prover goals output off when sending many script commands.
If non-nil, Proof General will automatically issue this command
to help speed up processing of long proof scripts.  
See also proof-shell-stop-silent-cmd.
NB: terminator not added to command."
  :type '(choice string (const nil))
  :group 'proof-shell)

(defcustom proof-shell-stop-silent-cmd nil
  "Command to turn prover output on.  
If non-nil, Proof General will automatically issue this command
to help speed up processing of long proof scripts.  
See also proof-shell-start-silent-cmd.
NB: Terminator not added to command."
  :type '(choice string (const nil))
  :group 'proof-shell)

(defcustom proof-shell-silent-threshold 2
  "Number of waiting commands in the proof queue needed to trigger silent mode.
Default is 2, but you can raise this in case switching silent mode
on or off is particularly expensive (or make it ridiculously large
to disable silent mode altogether)."
  :type 'integer
  :group 'proof-shell)

(defcustom  proof-shell-inform-file-processed-cmd nil
 "Command to the proof assistant to tell it that a file has been processed.
The format character `%s' is replaced by a complete filename for a
script file which has been fully processed interactively with
Proof General.  See `proof-format-filename' for other possibilities
to process the filename.

This setting used to interface with the proof assistant's internal
management of multiple files, so the proof assistant is kept aware of
which files have been processed.  Specifically, when scripting
is deactivated in a completed buffer, it is added to Proof General's
list of processed files, and the prover is told about it by
issuing this command.

If this is set to nil, no command is issued.

See also: proof-shell-inform-file-retracted-cmd, 
proof-shell-process-file, proof-shell-compute-new-files-list."
 :type '(choice string (const nil))
 :group 'proof-shell)

(defcustom  proof-shell-inform-file-retracted-cmd nil
 "Command to the proof assistant to tell it that a file has been retracted.
The format character `%s' is replaced by a complete filename for a
script file which Proof General wants the prover to consider as not
completely processed.  See `proof-format-filename' for other
possibilities to process the filename.

This is used to interface with the proof assistant's internal
management of multiple files, so the proof assistant is kept aware of
which files have been processed.  Specifically, when scripting
is activated, the file is removed from Proof General's list of 
processed files, and the prover is told about it by issuing this 
command.  The action may cause the prover in turn to suggest to 
Proof General that files depending on this one are
also unlocked.

If this is set to nil, no command is issued.

See also: proof-shell-inform-file-processed-cmd, 
proof-shell-process-file, proof-shell-compute-new-files-list."
 :type '(choice string (const nil))
 :group 'proof-shell)

(defcustom proof-auto-multiple-files nil
  "Whether to use automatic multiple file management.
If non-nil, Proof General will automatically retract a script file
whenever another one is retracted which it depends on.  It assumes
a simple linear dependency between files in the order which
they were processed.

If your proof assistant has no management of file dependencies, or one
which depends on a simple linear context, you may be able to use this
setting to good effect.  If the proof assistant has more complex
file dependencies then you should configure it to communicate with
Proof General about the dependencies rather than using this setting."
  :type 'boolean
  :group 'proof-shell)

;; (defcustom  proof-shell-adjust-line-width-cmd nil






;;
;; 5b. Regexp variables for matching output from proof process.
;;

(defcustom proof-shell-prompt-pattern nil 
   "Proof shell's value for comint-prompt-pattern, which see.
This pattern is just for interaction in comint (shell buffer).
You don't really need to set it."
   :type 'regexp
   :group 'proof-shell)

;; FIXME da: replace this with wakeup-regexp or prompt-regexp?
;; May not need next variable.
(defcustom proof-shell-wakeup-char nil
  "A special character which terminates an annotated prompt.
Set to nil if proof assistant does not support annotated prompts."
  :type '(choice character (const nil))
  :group 'proof-shell)

(defcustom proof-shell-annotated-prompt-regexp nil
  "Regexp matching a (possibly annotated) prompt pattern.

THIS IS THE MOST IMPORTANT SETTING TO CONFIGURE!!   

Output is grabbed between pairs of lines matching this regexp,
and the appearance of this regexp is used by Proof General to
recognize when the prover has finished processing a command.

To help speed up matching you may be able to annotate the 
proof assistant prompt with a special character not appearing 
in ordinary output.  The special character should appear in 
this regexp, and should be the value of proof-shell-wakeup-char."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-abort-goal-regexp nil
  "Regexp matching output from an aborted proof."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-error-regexp nil
  "Regexp matching an error report from the proof assistant.

We assume that an error message corresponds to a failure in the last
proof command executed.  So don't match mere warning messages with
this regexp.  Moreover, an error message should not be matched as an
eager annotation (see proof-shell-eager-annotation-start) otherwise it
will be lost.

Error messages are considered to begin from proof-shell-error-regexp
and continue until the next prompt.  The variable
`proof-shell-truncate-before-error' controls whether text before the
error message is displayed.

The engine matches interrupts before errors, see proof-shell-interrupt-regexp.

It is safe to leave this variable unset (as nil)."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-truncate-before-error t
  "Non-nil means truncate output that appears before error messages.
If nil, the whole output that the prover generated before the last
error message will be shown.

NB: the default setting for this is `t' to be compatible with
behaviour in Proof General before version 3.4.  The more obvious
setting for new instances is probably `nil'.

Interrupt messages are treated in the same way.
See `proof-shell-error-regexp' and `proof-shell-interrupt-regexp'."
  :type 'boolean
  :group 'proof-shell)

(defcustom proof-shell-next-error-regexp nil
  "Regular expression which matches an error message, perhaps with line/column.
Used by `proof-next-error' to jump to line numbers causing 
errors during some batch processing of the proof assistant.
(During \"manual\" script processing, script usually automatically
jumps to the end of the locked region)

Match number 2 should be the line number, if present.
Match number 3 should be the column number, if present.

The filename may be matched by `proof-shell-next-error-filename-regexp',
which is assumed to precede proof-shell-next-error-regexp."
  :type 'string
  :group 'proof-shell)

(defcustom proof-shell-next-error-filename-regexp nil
  "Used to locate a filename that an error message refers to.
Used by `proof-next-error' to jump to locations causing 
errors during some batch processing of the proof assistant.
(During \"manual\" script processing, the script usually automatically
jumps to the end of the locked region).

Match number 2 should be the file name, if present.

Errors must first be matched by `proof-shell-next-error-regexp'
(whether they contain a line number or not).  The response buffer
is then searched *backwards* for a regexp matching this variable,
`proof-shell-next-error-filename-regexp'.  (So if the
filename appears after the line number, make the first regexp
match the whole line).  Finally 
`proof-shell-next-error-extract-filename'
may be used to extract the filename from 
This regexp should be set to match messages also matched by
`proof-shell-error-message-line-number-regexp'.  
Match number 1 should be the filename."
  :type 'string
  :group 'proof-shell)

;; FIXME: generalize this to string-or-function scheme
(defcustom proof-shell-next-error-extract-filename nil
  "A string used to extract filename from error message.  %s replaced.
NB: this is only used if the match itself does not already correspond
to a filename."
  :type 'string
  :group 'proof-shell)

(defcustom proof-shell-interrupt-regexp nil
  "Regexp matching output indicating the assistant was interrupted.
We assume that an interrupt message corresponds to a failure in the last
proof command executed.  So don't match mere warning messages with
this regexp.  Moreover, an interrupt message should not be matched as an
eager annotation (see proof-shell-eager-annotation-start) otherwise it
will be lost.

The engine matches interrupts before errors, see proof-shell-error-regexp.

It is safe to leave this variable unset (as nil)."
  :type '(choice nil regexp)
  :group 'proof-shell) 

(defcustom proof-shell-proof-completed-regexp nil
  "Regexp matching output indicating a finished proof.

When output which matches this regexp is seen, we clear the goals
buffer in case this is not also marked up as a `goals' type of
message.

We also enable the QED function (save a proof) and we may automatically
close off the proof region if another goal appears before a save
command, depending on whether the prover supports nested proofs or not."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-clear-response-regexp nil
  "Regexp matching output telling Proof General to clear the response buffer.
This feature is useful to give the prover more control over what output
is shown to the user.  Set to nil to disable."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-clear-goals-regexp nil
  "Regexp matching output telling Proof General to clear the goals buffer.
This feature is useful to give the prover more control over what output
is shown to the user.  Set to nil to disable."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-start-goals-regexp nil
  "Regexp matching the start of the proof state output.
This is an important setting.  Output between `proof-shell-start-goals-regexp'
and `proof-shell-end-goals-regexp' will be pasted into the goals buffer
and possibly analysed further for proof-by-pointing markup."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-end-goals-regexp nil
  "Regexp matching the end of the proof state output, or nil.
If nil, just use the rest of the output following proof-shell-start-goals-regexp."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-eager-annotation-start nil
  "Eager annotation field start.  A regular expression or nil.
An eager annotation indicates to Proof General that some following output
should be displayed (or processed) immediately and not accumulated for 
parsing later. 

It is nice to recognize (starts of) warnings or file-reading messages
with this regexp.  You must also recognize any special messages
from the prover to PG with this regexp (e.g. `proof-shell-clear-goals-regexp', 
`proof-shell-retract-files-regexp', etc.)

See also `proof-shell-eager-annotation-start-length',
`proof-shell-eager-annotation-end'.

Set to nil to disable this feature."
  :type '(choice regexp (const :tag "Disabled" nil))
  :group 'proof-shell)

(defcustom proof-shell-eager-annotation-start-length 10
  "Maximum length of an eager annotation start. 
Must be set to the maximum length of the text that may match
`proof-shell-eager-annotation-start' (at least 1).
If this value is too low, eager annotations may be lost!

This value is used internally by Proof General to optimize the process
filter to avoid unnecessary searching."
  :type 'integer
  :group 'proof-shell)

(defcustom proof-shell-eager-annotation-end "\n"
  "Eager annotation field end.  A regular expression or nil.
An eager annotation indicates to Emacs that some following output
should be displayed or processed immediately.

See also `proof-shell-eager-annotation-start'.

It is nice to recognize (ends of) warnings or file-reading messages
with this regexp.  You must also recognize (ends of) any special messages
from the prover to PG with this regexp (e.g. `proof-shell-clear-goals-regexp', 
`proof-shell-retract-files-regexp', etc.)

The default value is \"\\n\" to match up to the end of the line."
  :type '(choice regexp (const :tag "Unset" nil))
  :group 'proof-shell)

(defcustom proof-shell-assumption-regexp nil
  "A regular expression matching the name of assumptions.

At the moment, this setting is not used in the generic Proof General.

In the future it will be used for a generic implementation for `pg-topterm-goalhyp-fn',
used to help parse the goals buffer to annotate it for proof by pointing."
  :type '(choice regexp (const :tag "Unset" nil))
  :group 'proof-shell)

(defcustom proof-shell-process-file nil
  "A pair (REGEXP . FUNCTION) to match a processed file name.

If REGEXP matches output, then the function FUNCTION is invoked on the
output string chunk. It must return the name of a script file (with
complete path) that the system has successfully processed. In
practice, FUNCTION is likely to inspect the match data.  If it returns
the empty string, the file name of the scripting buffer is used
instead.  If it returns nil, no action is taken.

Care has to be taken in case the prover only reports on compiled
versions of files it is processing. In this case, FUNCTION needs to
reconstruct the corresponding script file name. The new (true) file
name is added to the front of `proof-included-files-list'."
  :type '(choice (cons regexp function) (const nil))
  :group 'proof-shell)


;; FIXME da: why not amalgamate the next two into a single
;;	     variable as above?  Maybe because removing one
;;	     

(defcustom proof-shell-retract-files-regexp nil
  "Matches a message that the prover has retracted a file.

At this stage, Proof General's view of the processed files is out of
date and needs to be updated with the help of the function
`proof-shell-compute-new-files-list'."
  :type '(choice regexp (const nil))
  :group 'proof-shell)

(defcustom proof-shell-compute-new-files-list nil
  "Function to update `proof-included-files list'.

It needs to return an up to date list of all processed files. Its
output is stored in `proof-included-files-list'. Its input is the
string of which `proof-shell-retract-files-regexp' matched a
substring. In practice, this function is likely to inspect the
previous (global) variable `proof-included-files-list' and the match
data triggered by `proof-shell-retract-files-regexp'."
  :type '(choice function (const nil))
  :group 'proof-shell)

(defcustom pg-use-specials-for-fontify nil
  "Flag indicating whether to strip annotations from output or not.
\"annotations\" are special characters with the top bit set.
If annotations are left in, they are made invisible and can be used
to do syntax highlighting with font-lock."
  :type 'boolean
  :group 'proof-shell)

(defcustom proof-shell-set-elisp-variable-regexp nil
  "Regexp matching output telling Proof General to set some variable.
This allows the proof assistant to configure Proof General directly
and dynamically.  

If the regexp matches output from the proof assistant, there should be
two match strings: (match-string 1) should be the name of the elisp
variable to be set, and (match-string 2) should be the value of the
variable (which will be evaluated as a lisp expression).

A good markup for the second string is to delimit with #'s, since
these are not valid syntax for elisp evaluation.

Elisp errors will be trapped when evaluating; set 
proof-show-debug-messages to be informed when this happens.

Example uses are to adjust PG's internal copies of proof assistant's
settings, or to make automatic dynamic syntax adjustments in Emacs to
match changes in theory, etc.  

If you pick a dummy variable name (e.g. `proof-dummy-setting') you
can just evaluation arbitrary elisp expressions for their side
effects, to adjust menu entries, or even launch auxiliary programs.
But use with care -- there is no protection against catastrophic elisp!

This setting could also be used to move some configuration settings
from PG to the prover, but this is not really supported (most settings
must be made before this mechanism will work).  In future, the PG
standard protocol, PGIP, will use this mechanism for making all
settings."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-match-pgip-cmd nil
  "Regexp used to match PGIP command from proof assistant.
The matching string will be parsed as XML and then processed by 
`pg-pgip-process-cmd'."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-theorem-dependency-list-regexp nil
  "Regexp matching output telling Proof General what the dependencies are.  
This is so that the dependent theorems can be highlighted somehow.  
Set to nil to disable.
This is an experimental feature, currently work-in-progress."
  :type '(choice nil regexp)
  :group 'proof-shell)

(defcustom proof-shell-show-dependency-cmd nil
  "Command sent to the prover to display a dependency.
This is typically a command used to print a theorem, constant, or whatever.
A string with %s replaced by the dependency name."
  :type 'string
  :group 'proof-shell)

(defcustom proof-shell-trace-output-regexp nil
  "Regexp matching tracing output which should be displayed in trace buffer.
Each line which matches this regexp but would otherwise be treated
as an ordinary response, is sent to the trace buffer instead of the
response buffer.   

This is intended for unusual debugging output from 
the prover, rather than ordinary output from final proofs.  

Set to nil to disable.

Suggestion: this can be set a function called by `proof-pre-shell-start-hook'."
  :type '(choice nil regexp)
  :group 'proof-shell)


;;
;; 5c. hooks and other miscellaneous customizations
;;

(defcustom proof-shell-filename-escapes nil
  "A list of escapes that are applied to %s for filenames.
A list of cons cells, car of which is string to be replaced
by the cdr.
For example, when directories are sent to Isabelle, HOL, and Coq,
they appear inside ML strings and the backslash character and
quote characters must be escaped.  The setting
  '((\"\\\\\\\\\" . \"\\\\\\\\\")
    (\"\\\"\" . \"\\\\\\\"\"))
achieves this.   This does not apply to LEGO, which does not
need backslash escapes and does not allow filenames with
quote characters.

This setting is used inside the function `proof-format-filename'."
  :type '(list (cons string string))
  :group 'proof-shell)

(defcustom proof-shell-process-connection-type 
  ;; Use ptys unless it seems like we're on Solaris.  Only have
  ;; a good chance to guess if shell-command-to-string and uname
  ;; available.
  (if (and
       (not (fboundp 'win32-long-file-name))
       (fboundp 'shell-command-to-string))
      (not (string-match "[sS]un" (shell-command-to-string "uname")))
    t)
  "The value of process-connection-type for the proof shell.
Set non-nil for ptys, nil for pipes.
The default (and preferred) option is to use pty communication.
However there is a long-standing backslash/long line problem with
Solaris which gives a mess of ^G characters when some input is sent
which has a \ in the 256th position.   
So we select pipes by default if it seems like we're on Solaris.
We do not force pipes everywhere because this risks loss of data."
  :type 'boolean
  :group 'proof-shell)

(defcustom proof-shell-strip-crs-from-input t
  "If non-nil, replace carriage returns in every input with spaces.
This is enabled by default: it is appropriate for some systems
because several CR's can result in several prompts, which may mess
up the display (or even worse, the synchronization)."
  :type 'boolean
  :group 'proof-shell)
  
(defcustom proof-shell-strip-crs-from-output (eq system-type 'cygwin32)
  ;; Cygwin32 probs with Isabelle noted by Norbert Voelker
  "If non-nil, remove carriage returns (^M) at the end of lines from output.
This is enabled for cygwin32 systems by default.  You should turn it off
if you don't need it (slight speed penalty)."
  :type 'boolean
  :group 'proof-shell)

(defcustom proof-shell-insert-hook nil 
  "Hooks run by proof-shell-insert before inserting a command.
Can be used to configure the proof assistant to the interface in
various ways -- for example, to observe or alter the commands sent to
the prover, or to sneak in extra commands to configure the prover.

This hook is called inside a save-excursion with the proof-shell-buffer 
current, just before inserting and sending the text in the 
variable `string'.  The hook can massage `string' or insert additional 
text directly into the proof-shell-buffer.  
Before sending `string', it will be stripped of carriage returns.

Additionally, the hook can examine the variable `action'.  It will be
a symbol, set to the callback command which is executed in the proof
shell filter once `string' has been processed.  The `action' variable
suggests what class of command is about to be inserted:
  
 'proof-done-invisible	     A non-scripting command
 'proof-done-advancing	     A \"forward\" scripting command
 'proof-done-retracting	     A \"backward\" scripting command

Caveats: You should be very careful about setting this hook.  Proof
General relies on a careful synchronization with the process between
inputs and outputs.  It expects to see a prompt for each input it
sends from the queue.  If you add extra input here and it causes more
prompts than expected, things will break!  Extending the variable
`string' may be safer than inserting text directly, since it is
stripped of carriage returns before being sent.

Example uses:
LEGO uses this hook for setting the pretty printer width if
the window width has changed;
Plastic uses it to remove literate-style markup from `string'. 
The x-symbol support uses this hook to convert special characters
into tokens for the proof assistant."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-pre-shell-start-hook nil
  "Hooks run before proof shell is started.
Suggestion: set this to a function which configures just these proof
shell variables: 

   proof-prog-name
   proof-mode-for-shell
   proof-mode-for-response
   proof-mode-for-goals
   proof-shell-trace-output-regexp

This is the bare minimum needed to get a shell buffer and
its friends configured in the function proof-shell-start."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-shell-handle-delayed-output-hook
  '(proof-pbp-focus-on-first-goal)
  "Hooks run after new output has been displayed in goals or response buffer."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-shell-handle-error-or-interrupt-hook
  '(proof-goto-end-of-locked-if-pos-not-visible-in-window)
  "Run after an error or interrupt has been reported in the response buffer.
Hook functions may inspect `proof-shell-error-or-interrupt-seen' to 
determine whether the cause was an error or interrupt."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-shell-pre-interrupt-hook
  nil
  "Run immediately after `comint-interrupt-subjob' is called.
This hook is added to allow customization for Poly/ML and other
systems where the system queries the user before returning to
the top level.  For Poly/ML it can be used to send the string \"f\",
for example."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-shell-process-output-system-specific nil
  "Set this variable to handle system specific output.
Errors, start of proofs, abortions of proofs and completions of
proofs are recognised in the function `proof-shell-process-output'.
All other output from the proof engine is simply reported to the
user in the RESPONSE buffer.

To catch further special cases, set this variable to a pair of
functions '(condf . actf). Both are given (cmd string) as arguments.
`cmd' is a string containing the currently processed command.
`string' is the response from the proof system. To change the
behaviour of `proof-shell-process-output', (condf cmd string) must
return a non-nil value. Then (actf cmd string) is invoked. 

See the documentation of `proof-shell-process-output' for the required
output format."  
  :type '(repeat function) 
  :group 'proof-shell)

(defcustom proof-state-change-hook nil
  "This hook is called when state change may have occurred. 
Specifically, this hook is called after a region has been asserted or
retracted, or after a command has been sent to the prover with
proof-shell-invisible-command.

This hook is used within Proof General to refresh the toolbar."

  :type '(repeat function) 
  :group 'proof-shell)

(defcustom proof-shell-font-lock-keywords nil
  "Value of font-lock-keywords used to fontify the proof shell.
This is currently used only by proof-easy-config mechanism, to set
`font-lock-keywords' before calling `proof-config-done'.
See also proof-{script,resp,goals}-font-lock-keywords."
  :type 'sexp
  :group 'proof-shell)



;;
;; 6. Goals buffer
;;

(defgroup proof-goals nil
  "Settings for configuring the goals buffer."
  :group 'prover-config
  :prefix "pg-goals-")

(defcustom pg-subterm-first-special-char nil
  "First special character.
Codes above this character can have special meaning to Proof General,
and are stripped from the prover's output strings.
Leave unset if no special characters are being used."
  :type '(choice character (const nil))
  :group 'proof-goals)

(defcustom pg-subterm-anns-use-stack nil
  "Choice of syntax tree encoding for terms.

If nil, prover is expected to make no optimisations.
If non-nil, the pretty printer of the prover only reports local changes. 
For LEGO 1.3.1 use `nil', for Coq 6.2, use `t'."
  :type 'boolean
  :group 'proof-goals)

(defcustom pg-goals-change-goal nil
  "Command to change to the goal `%s'"
  :type 'string
  :group 'proof-goals)

(defcustom pbp-goal-command nil
  "Command sent when `pg-goals-button-action' is requested on a goal."
  :type '(choice nil string)
  :group 'proof-goals)

(defcustom pbp-hyp-command nil
  "Command sent when `pg-goals-button-action' is requested on an assumption."
  :type '(choice nil string)
  :group 'proof-goals)

(defcustom pg-subterm-help-cmd nil
  "Command to display mouse help about a subterm.
This command is sent to the proof assistant, replacing %s by the
subterm that the mouse is over."
  :type '(choice nil string)
  :group 'proof-goals)

(defcustom pg-goals-error-regexp nil
  "Regexp indicating that the proof process has identified an error."
  :type '(choice nil regexp)
  :group 'proof-goals)

(defcustom proof-shell-result-start nil
  "Regexp matching start of an output from the prover after pbp commands.
In particular, after a `pbp-goal-command' or a `pbp-hyp-command'."
  :type '(choice nil regexp)
  :group 'proof-goals)

(defcustom proof-shell-result-end ""
  "Regexp matching end of output from the prover after pbp commands.
In particular, after a `pbp-goal-command' or a `pbp-hyp-command'."
  :type 'regexp
  :group 'proof-goals)

(defcustom pg-subterm-start-char nil
  "Opening special character for subterm markup.
Subsequent special characters with values *below* 
pg-subterm-first-special-char are assumed to be subterm position 
indicators.  Annotations should be finished with pg-subterm-sep-char; 
the end of the concrete syntax is indicated by pg-subterm-end-char.

If `pg-subterm-start-char' is nil, subterm markup is disabled.

See doc of `pg-goals-analyse-structure' for more details of
subterm and proof-by-pointing markup mechanisms.."
  :type '(choice character (const nil))
  :group 'proof-goals)

(defcustom pg-subterm-sep-char nil
  "Finishing special for a subterm markup.
See doc of `pg-subterm-start-char'."
  :type '(choice character (const nil))
  :group 'proof-goals)

(defcustom pg-subterm-end-char nil
  "Closing special character for subterm markup.
See `pg-subterm-start-char'."
  :type 'character
  :group 'proof-goals)

(defcustom pg-topterm-char nil
  "Annotation character that indicates the beginning of a \"top\" element.
A \"top\" element may be a sub-goal to be proved or a named hypothesis,
for example.  It is currently assumed (following LEGO/Coq conventions)
to span a whole line.

The function `pg-topterm-goalhyp-fn' examines text following this
special character, to determine what kind of top element it is.

This setting is also used to see if proof-by-pointing features
are configured.  If it is unset, some of the code 
for parsing the prover output is disabled."
  :type 'character
  :group 'proof-goals)



(defcustom proof-goals-font-lock-keywords nil
  "Value of font-lock-keywords used to fontify the goals output.
NB: the goals output is not kept in font-lock-mode because the
fontification may rely on annotations which are erased before
displaying.  This means internal functions of PG must be used
to display to the goals buffer to ensure fontification is done!
This is currently used only by proof-easy-config mechanism,
to set font-lock-keywords before calling proof-config-done.
See also proof-{script,shell,resp}-font-lock-keywords."
  :type 'sexp
  :group 'proof-goals)

;; FIXME: perhaps we need new customize group here, "goals" is
;; not quite right for response buffer!
(defcustom proof-resp-font-lock-keywords nil
  "Value of font-lock-keywords used to fontify the response output.
NB: the goals output is not kept in font-lock-mode because the
fontification may rely on annotations which are erased before
displaying.  This means internal functions of PG must be used
to display to the goals buffer to ensure fontification is done!
This is currently used only by proof-easy-config mechanism,
to set font-lock-keywords before calling proof-config-done.
See also proof-{script,shell,resp}-font-lock-keywords."
  :type 'sexp
  :group 'proof-goals)

(defcustom pg-before-fontify-output-hook nil
  "This hook is called before fontifying a region in an output buffer.
A function on this hook can alter the region of the buffer within
the current restriction, and must return the final value of (point-max).
[This hook is presently only used by phox-sym-lock]."
  :type '(repeat function)
  :group 'proof-goals)

(defcustom pg-after-fontify-output-hook nil
  "This hook is called before fonfitying a region in an output buffer.
[This hook is presently only used by Isabelle]."
  :type '(repeat function)
  :group 'proof-goals)



;;
;; 8. X-Symbol configuration
;;

(defgroup proof-x-symbol nil
  "Configuration of X-Symbol for Proof General."
  :group 'prover-config
  :prefix "proof-xsym-")

(defcustom proof-xsym-extra-modes nil
  "List of additional mode names to use X-Symbol with Proof General tokens.
These modes will have X-Symbol enabled for the proof assistant token language,
in addition to the four modes for Proof General (script, shell, response, pbp).

Set this variable if you want additional modes to also display 
tokens (for example, editing documentation or source code files)."
  :type '(repeat symbol)
  :group 'proof-x-symbol)

;; FIXME: should perhaps be one of these per prover
;; FIXME: actually this setting doesn't seem to be needed:
;; instead X-Symbol uses x-symbol-<lang>-font-lock-keywords.
(defcustom proof-xsym-font-lock-keywords nil
  "Font lock keywords to use for the proof assistants X-Symbol token language.
This should be set to the additional font-lock-keywords used for the
proof assistant when X-Symbol is enabled.  (For example, additional
keywords used for bold or superscript text: see isa/x-symbol-isabelle.el)"
  :type 'sexp
  :group 'proof-x-symbol)

(defcustom proof-xsym-activate-command nil
  "Command to activate token input/output for X-Symbol.
If non-nil, this command is sent to the proof assistant when 
X-Symbol support is activated."
  :type 'string
  :group 'proof-x-symbol)

(defcustom proof-xsym-deactivate-command nil
  "Command to deactivate token input/output for X-Symbol.
If non-nil, this command is sent to the proof assistant when 
X-Symbol support is deactivated."
  :type 'string
  :group 'proof-x-symbol)

(defpgcustom x-symbol-language proof-assistant-symbol
  "Setting for x-symbol-language for the current proof assistant.
It defaults to proof-assistant-symbol, which makes X Symbol
look for files named x-symbol-<PA>.el.")




;;
;; 9. Prover specific settings 
;;
;; The settings defined here automatically use the current proof
;; assistant symbol as a prefix, i.e.  isa-favourites, coq-favourites,
;; or whatever will be defined on evaluation.

(defpgcustom favourites nil
  "*Favourite commands for this proof assistant.
A list of lists of the form (COMMAND INSCRIPT MENUNAME KEY), 
arguments for `proof-add-favourite', which see.")

(defpgcustom menu-entries nil
  "Extra entries for proof assistant specific menu. 
A list of menu items [NAME CALLBACK ENABLER ...].  See the documentation
of `easy-menu-define' for more details."
  :type 'sexp
  :group 'prover-config)

(defpgcustom help-menu-entries nil
  "Extra entries for help submenu for proof assistant specific help menu.
A list of menu items [NAME CALLBACK ENABLER ...].  See the documentation
of `easy-menu-define' for more details."
  :type 'sexp
  :group 'prover-config)

(defpgcustom keymap (make-keymap (concat proof-assistant " keymap"))
  "Proof assistant specific keymap, used under prefix C-c a."
  :type 'sexp
  :group 'prover-config)

(defpgcustom completion-table nil
  "List of identifiers to use for completion for this proof assistant.
Completion is activated with \\[complete].

If this table is empty or needs adjusting, please make changes using
`customize-variable' and send suggestions to support@@proofgeneral.org"
  :type '(list string)
  :group 'prover-config)

;; FIXME: not used yet.
(defpgcustom tags-program nil
  "Program to run to generate TAGS table for proof assistant."
  :type 'file
  :group 'prover-config)

		     



;;
;; 10. Global constants

(defcustom proof-general-name "Proof-General"
  "Proof General name used internally and in menu titles."
  :type 'string
  :group 'proof-general-internals)

(defcustom proof-general-home-page
  "http://www.proofgeneral.org"
  "*Web address for Proof General"
  :type 'string
  :group 'proof-general-internals)

(defcustom proof-unnamed-theorem-name
  "Unnamed_thm"
  "A name for theorems which are unnamed.  Used internally by Proof General."
  :type 'string
  :group 'proof-general-internals)

;; FIXME: da: could we put these into another keymap shared across the
;; various PG modes?
(defcustom proof-universal-keys
  (cons
   (if proof-running-on-XEmacs 
       '([(control c) \`] . proof-next-error)
     '("`" . proof-next-error))
   '(([(control c) (control c)] . proof-interrupt-process)
     ([(control c) (control v)] . proof-minibuffer-cmd)))
"List of key-bindings made for the script, goals and response buffer. 
Elements of the list are tuples `(k . f)' 
where `k' is a key-binding (vector) and `f' the designated function."
  :type 'sexp
  :group 'proof-general-internals)






;; End of proof-config.el
(provide 'proof-config)
