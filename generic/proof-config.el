;; proof-config.el  Proof General configuration for proof assistant
;;
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
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
;;  2. Major modes
;;  3. Menus, user-level commands.
;;  4. Script mode configuration 
;;  5. Shell mode configuration
;;     5a. commands
;;     5b. regexps
;;     5c. hooks
;;  6. Global constants 
;;
;; The user options don't need to be set on a per-prover basis,
;; and the global constants probably should not be touched.
;; The remaining variables in sections 2-5 must be set for
;; each proof assistant.
;;



;;
;; 1. User options for proof mode
;;
;; The following variables are user options for Proof General.
;; They appear in the 'proof' customize group and should
;; *not* normally be touched by prover specific code.
;;

(defcustom proof-prog-name-ask-p nil
  "*If non-nil, query user which program to run for the inferior process."
  :type 'boolean
  :group 'proof-general)

(defcustom proof-one-command-per-line nil
  "*If non-nil, format for newlines after each proof command in a script."
  :type 'boolean
  :group 'proof-general)

(and (featurep 'toolbar)
(defcustom proof-toolbar-wanted t
  "*Whether to use toolbar in proof mode."
  :type 'boolean
  :group 'proof-general))

(defcustom proof-toolbar-follow-mode 'follow
  "*Choice of how point moves with toolbar commands.
One of the symbols: locked, follow, ignore.
If locked, point sticks to the end of the locked region with toolbar commands.
If follow, point moves just when needed to display the locked region end.
If ignore, point is never moved after toolbar movement commands."
  :type '(choice
	  (const :tag "Follow locked region" locked)
	  (const :tag "Keep locked region displayed" follow)
	  (const :tag "Never move" ignore))
  :group 'proof-general)


;;
;; Faces.
;; We ought to test that these work sensibly:
;;   a) with default colours
;;   b) with -rv
;;   c) on console 
;;   d) on win32
;;   e) all above with FSF Emacs and XEmacs.
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
  :group 'proof
  :prefix "proof-")
  

(defface proof-queue-face
  '((((type x) (class color) (background light))
     (:background "mistyrose"))
    (((type x) (class color) (background dark))
     (:background "mediumvioletred"))
    (t				
     (:foreground "white" :background "black")))
  "*Face for commands in proof script waiting to be processed."
  :group 'proof-faces)

(defface proof-locked-face
  '((((type x) (class color) (background light))   
     (:background "lavender"))
    (((type x) (class color) (background dark))   
     (:background "navy"))
    (t				
     (:underline t)))
  "*Face for locked region of proof script (processed commands)."
  :group 'proof-faces)

(defface proof-declaration-name-face
  '((((type x) (class color) (background light))   
     (:foreground "chocolate" 
      :bold t))
    (((type x) (class color) (background dark))   
     (:foreground "orange"
      :bold t))
    (t				
     (:italic t :bold t)))
  "*Face for declaration names in proof scripts."
  :group 'proof-faces)

(defface proof-tacticals-name-face
  '((((type x) (class color) (background light))   
     (:foreground "MediumOrchid3"))
    (((type x) (class color) (background dark))   
     (:foreground "orchid"))
    (t				
     (bold t)))
  "*Face for names of tacticals in proof scripts."
  :group 'proof-faces)

(defface proof-error-face 
  '((((type x) (class color) (background light))   
     (:background "salmon1"  
      :bold t))
    (((type x) (class color) (background dark))   
     (:background "brown" 
      :bold t))
    (t				
     (:bold t)))
  "*Face for error messages from proof assistant."
  :group 'proof-faces)

(defface proof-warning-face
  '((((type x) (class color) (background light))   
     (:background "lemon chiffon"))
    (((type x) (class color) (background dark))   
     (:background "orange2"))
    (t				
     (:italic t)))
  "*Face for warning messages.
Could come either from proof assistant or Proof General itself."
  :group 'proof-faces)

(defface proof-eager-annotation-face
  '((((type x) (class color) (background light))   
     (:background "lightgoldenrod"))
    (((type x) (class color) (background dark))   
     (:background "darkgoldenrod"))
    (t				
     (:italic t)))
  "*Face for messages from proof assistant."
  :group 'proof-faces)





;;
;; CONFIGURATION VARIABLES
;;
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

(defcustom proof-assistant ""
  "Name of the proof assistant Proof General is using.
This is set automatically by the mode stub defined in proof-site,
from the name given in proof-assistant-table."
  :type 'string
  :group 'prover-config)




;;
;; 2. The major modes used by Proof General.
;;

;; FIXME: these symbols could be set automatically to standard values,
;; i.e. <assistant>-mode, <assistant>-shell-mode, <assistant>-pbp-mode.
;; FIXME: mode-for-script is unused at the moment, added just for
;; uniformity.  The other two are used when a shell buffer is started.

(defcustom proof-mode-for-shell nil
  "Mode for proof shell buffers.
Suggestion: this can be set in proof-pre-shell-start-hook."
  :type 'symbol
  :group 'prover-config)

(defcustom proof-mode-for-pbp nil
  "Mode for proof state display buffers.
Suggestion: this can be set in proof-pre-shell-start-hook."
  :type 'symbol
  :group 'prover-config)

(defcustom proof-mode-for-script nil
  "Mode for proof script buffers.
This is used by Proof General to find out which buffers 
contain proof scripts.
Suggestion: this can be set in the script mode configuration."
  :type 'symbol
  :group 'prover-config)




;;
;; 3. Configuration for menus, user-level commands, etc.
;;

(defcustom proof-asssistant-home-page ""
  "Web address for information on proof assistant"
  :type 'string
  :group 'prover-config)

(defcustom proof-ctxt-string ""
  "*Command to display the context in proof assistant."
  :type 'string
  :group 'prover-config)

(defcustom proof-help-string ""
  "*Command to ask for help in proof assistant."
  :type 'string
  :group 'prover-config)

(defcustom proof-prf-string ""
  "Command to display proof state in proof assistant."
  :type 'string
  :group 'prover-config)

(defcustom proof-goal-command nil
  "Command to set a goal in the proof assistant.  String or fn.
If a string, the format character %s will be replaced by the
goal string. If a function, should return a command string to
insert when called interactively."
  :type '(choice string function)
  :group 'prover-config)

(defcustom proof-save-command nil
  "Command to save a proved theorem in the proof assistant.  String or fn.
If a string, the format character %s will be replaced by the
theorem name. If a function, should return a command string to
insert when called interactively."
  :type '(choice string function)
  :group 'prover-config)


;; FIXME: allow this to be set in the mode fn instead.
(defcustom proof-tags-support t
  "If non-nil, include tags functions in menus.
This variable should be set before requiring proof.el"
  :type 'boolean
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
  "Character which terminates a proof command in a script buffer."
  :type 'character
  :group 'proof-script)

(defcustom proof-comment-start ""
  "String which starts a comment in the proof assistant command language.
The script buffer's comment-start is set to this string plus a space."
  :type 'string
  :group 'proof-script)

(defcustom proof-comment-end ""
  "String which starts a comment in the proof assistant command language.
The script buffer's comment-end is set to this string plus a space."
  :type 'string
  :group 'proof-script)

(defcustom proof-save-command-regexp nil 
  "Matches a save command"
  :type 'regexp
  :group 'prover-config)

(defcustom proof-save-with-hole-regexp nil 
  "Matches a named save command"
  :type 'regexp
  :group 'proof-script)

(defcustom proof-goal-with-hole-regexp nil 
  "Matches a saved goal command"
  :type 'regexp
  :group 'proof-script)

(defcustom proof-goal-command-p nil 
  "Is this a goal"
  :type 'function
  :group 'proof-script)

(defcustom proof-lift-global nil
  "This function lifts local lemmas from inside goals out to top level.
This function takes the local goalsave span as an argument. Set this
to `nil' of the proof assistant does not support nested goals."
  :type '(choice nil function)
  :group 'proof-script)

(defcustom proof-count-undos-fn nil 
  "Compute number of undos in a target segment"
  :type 'function
  :group 'proof-script)

(defcustom proof-atomic-sequence-lists nil
  "list of instructions for setting up atomic sequences of commands (ACS).

Each instruction is
a list of the form `(END START &optional FORGET-COMMAND)'. END is a
regular expression to recognise the last command in an ACS. START
is a function. Its input is the last command of an ACS. Its output
is a regular exression to recognise the first command of the ACS.
It is evaluated once and the output is successively matched agains
previously processed commands until a match occurs (or the
beginning of the current buffer is reached). The region determined
by (START,END) is locked as an ACS. Optionally, the ACS is
annotated with the actual command to retract the ACS. This is
computed by applying FORGET-COMMAND to the first and last command
of the ACS."
  :type '(repeat (cons regexp function (choice (const nil) function)))
  :group 'proof-shell)


(defconst proof-no-command "COMMENT"
  "String used as a nullary action (send no command to the proof assistant).
Only relevant for proof-find-and-forget-fn.")

(defcustom proof-find-and-forget-fn nil
  "Function returning a command string to forget back to before its argument span.
The special string proof-no-command means there is nothing to do."
  :type 'function
  :group 'proof-script)

(defcustom proof-goal-hyp-fn nil
  "Function which returns cons cell if point is at a goal/hypothesis.
First element of cell is a symbol, 'goal' or 'hyp'.  The second
element is a string: the goal or hypothesis itself.  This is used
when parsing the proofstate output"
  :type 'function
  :group 'proof-script)

(defcustom proof-kill-goal-command ""
  "Command to kill a goal."
  :type 'string
  :group 'proof-script)

(defcustom proof-global-p nil
  "Whether a command is a global declaration.  Predicate on strings or nil.
This is used to handle nested goals allowed by some provers."
  :type 'function
  :group 'proof-script)

(defcustom proof-state-preserving-p nil
  "A predicate, non-nil if its argument preserves the proof state."
  :type 'function
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
  "System command to run program name in proof shell.
Suggestion: this can be set in proof-pre-shell-start-hook from
a variable which is in the proof assistant's customization
group.  This allows different proof assistants to coexist
(albeit in separate Emacs sessions)."
  :type 'string
  :group 'proof-shell)

(defcustom proof-shell-init-cmd ""
   "The command for initially configuring the proof process."
   :type '(choice string (const nil))
   :group 'proof-shell)

(defcustom proof-shell-cd nil
  "Command to the proof assistant to change the working directory."
  :type 'string
  :group 'proof-shell)


;;
;; 5b. Regexp variables for matching output from proof process.
;;

(defcustom proof-shell-prompt-pattern nil 
   "Proof shell's value for comint-prompt-pattern, which see."
   :type 'regexp
   :group 'proof-shell)

;; FIXME da: replace this with wakeup-regexp or prompt-regexp?
;; May not need next variable.
(defcustom proof-shell-wakeup-char nil
  "A special character which terminates an annotated prompt.
Set to nil if proof assistant does not support annotated prompts."
  :type '(choice character (const nil))
  :group 'proof-shell)

(defcustom proof-shell-annotated-prompt-regexp ""
  "Regexp matching a (possibly annotated) prompt pattern.
Output is grabbed between pairs of lines matching this regexp.
To help matching you may be able to annotate the proof assistant
prompt with a special character not appearing in ordinary output.
The special character should appear in this regexp, should
be the value of proof-shell-wakeup-char."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-abort-goal-regexp nil
  "Regexp matching output from an aborted proof."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-error-regexp nil
  "Regexp matching an error report from the proof assistant.
We assume that an error message corresponds to a failure
in the last proof command executed.  (So don't match
mere warning messages with this regexp)."
  :type 'regexp
  :group 'proof-shell) 

(defcustom proof-shell-interrupt-regexp nil
  "Regexp matching output indicating the assistant was interrupted."
  :type 'regexp
  :group 'proof-shell) 

(defcustom proof-shell-proof-completed-regexp nil
  "Regexp matching output indicating a finished proof."
  :type 'regexp
  :group 'proof-shell)

(defcustom pbp-goal-command nil
  "Command informing the prover that `pbp-button-action' has been
  requested on a goal."
  :type 'regexp
  :group 'proof-shell)

(defcustom pbp-hyp-command nil
  "Command informing the prover that `pbp-button-action' has been
  requested on an assumption."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-result-start ""
  "Regexp matching start of an output from the prover after pbp commands.
In particular, after a `pbp-goal-command' or a `pbp-hyp-command'."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-result-end ""
  "Regexp matching end of output from the prover after pbp commands.
In particular, after a `pbp-goal-command' or a `pbp-hyp-command'."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-start-goals-regexp ""
  "Regexp matching the start of the proof state output."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-end-goals-regexp ""
  "Regexp matching the end of the proof state output."
  :type 'regexp
  :group 'proof-shell)

(defcustom pbp-error-regexp nil
  "Regexp indicating that the proof process has identified an error."
  :type 'regexp
  :group 'proof-shell)

(defcustom proof-shell-eager-annotation-start nil
  "Eager annotation field start.  A regular expression or nil.
An eager annotation indicates to Emacs that some following output
should be displayed immediately and not accumulated for parsing.
Set to nil to disable this feature.

The default value is \"\n\" to match up to the end of the line."
  :type '(choice regexp nil)
  :group 'proof-shell)

(defcustom proof-shell-eager-annotation-end "\n"
  "Eager annotation field end.  A regular expression or nil.
An eager annotation indicates to Emacs that some following output
should be displayed immediately and not accumulated for parsing.
The default value is \"\n\" to match up to the end of the line."
  :type '(choice regexp nil)
  :group 'proof-shell)

(defcustom proof-shell-assumption-regexp nil
  "A regular expression matching the name of assumptions."
  :type '(choice regexp nil)
  :group 'proof-shell)



;;
;; 5c. hooks 
;;

(defcustom proof-shell-insert-hook nil 
  "Hooks run by proof-shell-insert before inserting a command.
Can be used to configure the proof assistant to the interface in
various ways (for example, setting the line width of output).
Any text inserted by these hooks will be sent to the proof process
before every command issued by Proof General."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-pre-shell-start-hook nil
  "Hooks run before proof shell is started.
Usually this is set to a function which configures the proof shell
variables."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-shell-handle-delayed-output-hook
  '(proof-pbp-focus-on-first-goal)
  "Hooks run after new output has been displayed in the RESPONSE buffer."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-shell-handle-error-hook
  '(proof-goto-end-of-locked-if-pos-not-visible-in-window)
  "Hooks run after an error has been reported in the RESPONSE buffer."
  :type '(repeat function)
  :group 'proof-shell)

(defcustom proof-shell-process-file nil
  "A tuple of the form (regexp . function) to match a processed file name.

If REGEXP matches output, then the function FUNCTION is invoked on the
output string chunk. It must return a script file name (with complete
path) the system is currently processing. In practice, FUNCTION is
likely to inspect the match data.  If it returns the empty string,
the file name of the scripting buffer is used instead.  If it
returns nil, no action is taken.

Care has to be taken in case the prover only reports on compiled
versions of files it is processing. In this case, FUNCTION needs to
reconstruct the corresponding script file name. The new (true) file
name is added to the front of `proof-included-files-list'."
  :type '(choice (cons regexp function) (const nil))
  :group 'proof-shell)

(defcustom proof-shell-retract-files-regexp nil
  "A REGEXP to match that the prover has retracted across file boundaries.

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





;;
;; 6. Global constants
;; 
(defcustom proof-mode-name "Proof-General"
  "Root name for proof script mode.  
Used internally and in menu titles."
  :type 'string
  :group 'proof-general-internals)

(defcustom proof-proof-general-home-page
  "http://www.dcs.ed.ac.uk/home/proofgen"
  "*Web address for Proof General"
  :type 'string
  :group 'proof-general-internals)

;; FIXME: da: could we put these into another keymap already?
;; FIXME: da: it's offensive to experienced users to rebind global stuff
;;        like meta-tab, this should be removed.
(defcustom proof-universal-keys
  (append
   '(([(control c) (control c)] . proof-interrupt-process)
    ([(control c) (control v)] . proof-execute-minibuffer-cmd))
   (if proof-tags-support
       '(([(meta tab)]	       . tag-complete-symbol))
     nil))
"List of keybindings which for the script and response buffer. 
Elements of the list are tuples (k . f) 
where `k' is a keybinding (vector) and `f' the designated function."
  :type 'sexp
  :group 'proof-general-internals)



;;; 
;;; FIXME: unsorted below here
;;;

(defcustom pbp-change-goal nil
  "Command to change to the goal %s"
  :type 'string
  :group 'prover-config)

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
return a non-nil value. Then (actf cmd string) is invoked. See the
documentation of `proof-shell-process-output' for the required
output format."
  :type '(cons (function function))
  :group 'proof-shell)

(defcustom proof-activate-scripting-hook nil
  "Hook run when a buffer is switched into scripting mode.
The current buffer will be the newly active scripting buffer.

This hook may be useful for synchronizing with the proof
assistant, for example, to switch to a new theory."
  :type '(repeat function)
  :group 'proof-script)




;;
;; Proof script indentation
;;

;; FIXME: document this junk
(defcustom proof-stack-to-indent nil
  "Prover-specific code for indentation."
  :type 'sexp
  :group 'proof-script)

(defcustom proof-parse-indent nil
  "Proof-assistant specific function for parsing characters for
  indentation which is invoked in `proof-parse-to-point.'. Must be a
  function taking two arguments, a character (the current character)
  and a stack reflecting indentation, and must return a stack. The
  stack is a list of the form (c . p) where `c' is a character
  representing the type of indentation and `p' records the column for
  indentation. The generic `proof-parse-to-point.' function supports
  parentheses and commands. It represents these with the characters
  `?\(', `?\[' and `proof-terminal-char'. "
  :type 'sexp
  :group 'proof-script)


;;
;; More shell junk to sort out [maybe for pbp]
;;

(defvar proof-shell-first-special-char nil "where the specials start")
(defvar proof-shell-goal-char nil "goal mark")
(defvar proof-shell-start-char nil "annotation start")
(defvar proof-shell-end-char nil "annotation end")
(defvar proof-shell-field-char nil "annotated field end")


;; FIXME da: where is this variable used?  
;;	      dropped in favour of goal-char?
;; Answer: this is used in *specific* modes, see e.g.
;; lego-goal-hyp.  This stuff needs making more generic.

(defvar proof-shell-goal-regexp nil
  "A regular expression matching the identifier of a goal.
Used by proof mode to parse proofstate output, and also
to set outline heading regexp.")

(defvar proof-shell-noise-regexp nil
  "Unwanted information output from the proof process within
  `proof-start-goals-regexp' and `proof-end-goals-regexp'.")

(defvar proof-analyse-using-stack nil
  "Are annotations sent by proof assistant local or global")


;; End of proof-config.el
(provide 'proof-config)
