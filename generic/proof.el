;; proof.el  Major mode for proof assistants
;;
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; Thanks to Rod Burstall, Martin Hofmann,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens
;;   for helpful comments and code.
;;
;; $Id$
;;
;; PENDING:
;;
;; da: I propose splitting this file as follows:
;;
;;  proof.el         Controls loading.  Requires proof-script, proof-shell.
;;		     Retains misc utils, user options, splash screen.
;;  proof-script.el  Script management mode.
;;  proof-shell.el   Proof shell mode.
;;
;; The shell mode and script mode are already fairly independent in
;; this file.
;;

(require 'proof-site)

;;
;; Here is the first configuration variable, proof-assistant.
;; Others follow below, along with notes about the prover-config
;; customization group.
;;
(defgroup prover-config nil
  "Configuration of Proof General for the prover in use."
  :group 'proof-internal)

(defcustom proof-assistant ""
  "Name of the proof assistant Proof General is using.
This is set automatically by the mode stub defined in proof-site,
from the name given in proof-internal-assistant-table."
  :type 'string
  :group 'proof-config)


;;;
;;; Splash screen (XEmacs specific for now)
;;;
(if (string-match "XEmacs" emacs-version)
(progn     
(require 'annotations)
(defconst proof-welcome "*Proof General Welcome*"
  "Name of the Proof General splash buffer.")

(defconst proof-display-splash-image
  ;; Use jpeg if we can, otherwise assume gif will work.
  (if (featurep 'jpeg)
      (cons 'jpeg
	    (concat proof-internal-images-directory 
		    "ProofGeneral.jpg"))
  (cons 'gif
	(concat proof-internal-images-directory 
		(concat "ProofGeneral"
			(or (and
			     (fboundp 'device-pixel-depth)
			     (> (device-pixel-depth) 8)
			     ".gif")
			    ;; Low colour gif for poor displays
			    ".8bit.gif")))))
  "Format and File name of Proof General Image.")

(defcustom proof-display-splash 
  (valid-instantiator-p
   (vector (car proof-display-splash-image)
		 :file (cdr proof-display-splash-image)) 'image)
  "*Display splash screen when Proof General is loaded."
  :type 'boolean
  :group 'proof)

(defcustom proof-internal-display-splash-time 4
  "Minimum number of seconds to display splash screen for.
If the machine gets to the end of proof-mode faster than this,
we wait for the remaining time.  Must be a value less than 40."
  :type 'integer
  :group 'proof-internal)

;; We take some care to preserve the users window configuration
;; underneath the splash screen.  This is just to be polite.
(defun proof-remove-splash-screen (conf)
  "Make function to remove splash screen and restore window config to conf."
  `(lambda ()
     (and ;; If splash buffer is still alive 
      (get-buffer proof-welcome)
      (if (get-buffer-window (get-buffer proof-welcome))
	  ;; Restore the window config if splash is being displayed
	  (set-window-configuration ,conf)
	t)
      ;; And destroy splash buffer.
      (kill-buffer proof-welcome))))

(defun proof-display-splash-screen ()
  "Save window config and display Proof General splash screen.
No effect if proof-display-splash-time is zero."
  (interactive)
  (if proof-display-splash
      (let*
	  ((splashbuf   (get-buffer-create proof-welcome))
	   (imglyph	(make-glyph
			 (list (vector (car proof-display-splash-image) ':file
				       (cdr proof-display-splash-image)))))
	   ;; Keep win config explicitly instead of pushing/popping because
	   ;; if the user switches windows by hand in some way, we want
	   ;; to ignore the saved value.  Unfortunately there seems to
	   ;; be no way currently to remove the top item of the stack.
	   (removefn    (proof-remove-splash-screen
			 (current-window-configuration))))
	(save-excursion
	  (set-buffer splashbuf)
	  (erase-buffer)
	  ;; FIXME: centre display better.  support FSFmacs.
	  (insert "\n\n\n\t\t")
	  (insert-char ?\  (/ (length proof-assistant) 2))
	  (insert "    Welcome to\n\t\t  "
		  proof-assistant " Proof General!\n\n\n\t\t ")
	  (let ((ann (make-annotation imglyph))) ; reveal-annotation doesn't
	    (reveal-annotation ann))	;      autoload, so use let form.  
	  (insert "\n\n")
	  (delete-other-windows (display-buffer splashbuf)))
	;; Start the timer with a dummy value of 40 secs, to time the
	;; loading of the rest of the mode.  This is a kludge to make
	;; sure that the splash screen appears at least throughout the
	;; load (which shouldn't last 40 secs!).  But if the load is
	;; triggered by something other than a call to proof-mode,
	;; the splash screen *will* appear for 40 secs (unless the
	;; user kills it or switches buffer).
	(redisplay-frame nil t)
	(start-itimer proof-welcome removefn 40))))

;; PROBLEM: when to call proof-display-splash-screen?  Effect we'd
;; like is to call it during loading/initialising.  It's hard to make
;; the screen persist after loading because of the action of
;; display-buffer acting after the mode function during find-file.
;; To approximate the best behaviour, we assume that this file is
;; loaded by a call to proof-mode.  We display the screen now and add
;; a wait procedure temporarily to proof-mode-hook which prevents
;; redisplay until at least proof-internal-display-splash-time
;; has elapsed. 

;; Display the screen ASAP...
(proof-display-splash-screen)

(defun proof-wait-for-splash-proof-mode-hook-fn ()
  "Wait for a while displaying splash screen, then remove self from hook." 
  (if proof-display-splash
       (let ((timer (get-itimer proof-welcome)))
	 (if timer
	     (if (< (- 40 proof-internal-display-splash-time)
		    (itimer-value timer))
		 ;; Splash has still not been seen for all of
		 ;; internal-display-splash-time, set the timer
		 ;; for the remaining time...
		 (progn
		   (set-itimer-value timer
		    (- proof-internal-display-splash-time
		       (- 40 (itimer-value timer))))
		   ;; and wait until it finishes or user-input
		   (while (and (get-itimer proof-welcome)
			       (sit-for 1 t)))
		   ;; If timer still running, run function
		   ;; and delete timer.
		   (if (itimer-live-p timer)
		       (progn
			 (funcall (itimer-function timer))
			 (delete-itimer timer))))))))
  (remove-hook 'proof-mode-hook 'proof-wait-for-splash-hook))

(add-hook 'proof-mode-hook 'proof-wait-for-splash-proof-mode-hook-fn)

))
;;; End splash screen code


;;;
;;; Requires for included modules.
;;;

;; FIXME da: I think some of these should be autoloaded (etags,...)
(require 'cl)
(require 'compile)
(require 'comint)
(require 'etags)			
(cond ((fboundp 'make-extent) (require 'span-extent))
      ((fboundp 'make-overlay) (require 'span-overlay))
      (t nil))
(require 'easymenu)			; present in XEmacs 20.4 by default.

(require 'proof-syntax)
(require 'proof-indent)

(autoload 'w3-fetch "w3" nil t)		; FIXME: shouldn't we use browse-url?

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 (list 'progn
   (list 'defvar var 'nil docstring)
   (list 'make-variable-buffer-local (list 'quote var))
   (list 'setq-default var value)))

;; Load toolbar code if toolbars available.
(if (featurep 'toolbar)
    (require 'proof-toolbar))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; User options                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; The following variables are user options for Proof General.
;; They appear in the 'proof' customize group and should
;; not normally be touched by prover specific code.
;;
;;
(defcustom proof-prog-name-ask-p nil
  "*If non-nil, query user which program to run for the inferior process."
  :type 'boolean
  :group 'proof)

(defcustom proof-one-command-per-line nil
  "*If non-nil, format for newlines after each proof command in a script."
  :type 'boolean
  :group 'proof)
 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuration for proof assistant				    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; The variables in the "prover-config" customize group are those
;; which are intended to be set by the prover specific elisp,
;; i.e. constants set on a per-prover basis.
;;
;; Putting these in a customize group is useful for documenting
;; this type of variable, and for developing a new instantiation
;; of Proof General.
;; But it is *not* useful for final user-level customization!
;; The reason is that saving these customizations across a session is
;; not liable to work, because the prover specific elisp usually
;; overrides with a series of setq's in <assistant>-mode-config type
;; functions.  This is why prover-config appears under the
;; proof-internal group.
;;
;;

;; The Customization menus would be nicer if the variables in
;; prover-config group were uniformly renamed prover-config-*
;; (and similarly for other variables/groups).  But it's
;; somewhat of a horror in the code?

(defcustom proof-www-home-page ""
  "Web address for information on proof assistant"
  :type 'string
  :group 'prover-config)

(defcustom proof-shell-cd nil
  "Command to the inferior process to change the directory."
  :type 'string
  :group 'prover-config)

(defcustom proof-tags-support t
  "If non-nil, include tags functions in menus.
This variable should be set before requiring proof.el"
  :type 'boolean
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
  :group 'prover-config)

(defcustom proof-activate-scripting-hook nil
  "Hook run when a buffer is switched into scripting mode.
The current buffer will be the newly active scripting buffer.

This hook may be useful for synchronizing with the proof
assistant, for example, to switch to a new theory.")

;;
;; The following variables should be set before proof-config-done
;; is called.  These configure the mode for the script buffer,
;; including highlighting, etc.
;;

(defgroup proof-script nil
  "Proof General configuration of scripting buffer mode."
  :group 'prover-config)


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

(defconst proof-no-command "COMMENT"
  "String used as a nullary action (send no command to the proof assistant).
Only relevant for proof-find-and-forget-fn.")

(defcustom proof-find-and-forget-fn nil
  "Function returning a command string to forget back to before its argument span.
The special string proof-no-command means there is nothing to do."
  :type 'function
  :group 'proof-script)

(defcustom proof-goal-hyp-fn nil
  "A function which returns cons cell if point is at a goal/hypothesis.
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

(defcustom pbp-change-goal nil
  "Command to change to the goal %s"
  :type 'string
  :group 'prover-config)

;;
;; The following variables should be set in
;; proof-pre-shell-start-hook.
;;

;; FIXME da: these could be put in another customize group? 

(defcustom proof-prog-name nil
  "Command to run program name in proof shell"
  :type 'string
  :group 'prover-config)

(defcustom proof-mode-for-shell nil
  "Mode for proof shell"
  :type 'function
  :group 'prover-config)

(defcustom proof-mode-for-pbp nil
  "Mode for Proof-by-Pointing."
  :type 'function
  :group 'prover-config)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Generic config for proof shell	                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
  :group 'prover-config)

;;
;; Hooks for the proof shell
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

(defcustom proof-shell-init-cmd ""
   "The command for initially configuring the proof process."
   :type '(choice string (const nil))
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

;;
;; Regexp variables for matching output from proof process.
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

(defcustom proof-shell-process-file nil
  "A tuple of the form (regexp . function) to match a processed file name.

If REGEXP matches output, then the function FUNCTION is invoked on the
output string chunk. It must return a script file name (with complete
path) the system is currently processing. In practice, FUNCTION is
likely to inspect the match data.

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Internal variables used by scripting and pbp                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst proof-mode-name "Proof-General")

;; FIXME da: remove proof-terminal-string.  At the moment some
;; commands need to have the terminal string, some don't.
;; We should assume commands are terminated properly at the
;; specific level.
(defvar proof-terminal-string nil 
  "End-of-line string for proof process.")

(defvar proof-re-end-of-cmd nil 
  "Regexp matching end of command.  Based on proof-terminal-string.
Set in proof-config-done.")

(defvar proof-re-term-or-comment nil 
  "Regexp matching terminator, comment start, or comment end.
Set in proof-config-done.")

(defvar proof-marker nil 
  "Marker in proof shell buffer pointing to previous command input.")

(defvar proof-shell-buffer nil
  "Process buffer where the proof assistant is run.")

(defvar proof-script-buffer-list nil
  "Scripting buffers with locked regions.
The first element is current and in scripting minor mode.
The list of corresponding file names is a subset of
`proof-included-files-list'.")

(defvar proof-pbp-buffer nil
  "The goals buffer (also known as the pbp buffer).")

(defvar proof-response-buffer nil
  "The response buffer.")

(defvar proof-shell-busy nil 
  "A lock indicating that the proof shell is processing.
When this is non-nil, proof-check-process-available will give
an error.")

(deflocal proof-buffer-type nil 
  "Symbol indicating the type of this buffer: 'script, 'shell, or 'pbp.")

(defvar proof-action-list nil "action list")

(defvar proof-included-files-list nil 
  "List of files currently included in proof process.
Whenever a new file is being processed, it gets added to the front of
the list. When the prover retracts across file boundaries, this list
is resynchronised. It contains files in canonical truename format")

(deflocal proof-active-buffer-fake-minor-mode nil
  "An indication in the modeline that this is the *active* script buffer")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A few small utilities					    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-message (str)
  "Output STR in minibuffer."
  (message (concat "[" proof-assistant "] " str)))

;; append-element in tl-list
(defun proof-append-element (ls elt)
  "Append ELT to last of LS if ELT is not nil. [proof.el]
This function coincides with `append-element' in the package
[tl-list.el.]"
  (if elt
      (append ls (list elt))
    ls))

(defun proof-define-keys (map kbl)
  "Adds keybindings KBL in MAP.
The argument KBL is a list of tuples (k . f) where `k' is a keybinding
(vector) and `f' the designated function."
  (mapcar
   (lambda (kbl)
     (let ((k (car kbl)) (f (cdr kbl)))
         (define-key map k f)))
   kbl))

(defun proof-string-to-list (s separator) 
  "Return the list of words in S separated by SEPARATOR."
  (let ((end-of-word-occurence (string-match (concat separator "+") s)))
    (if (not end-of-word-occurence)
        (if (string= s "") 
            nil
          (list s))
      (cons (substring s 0 end-of-word-occurence) 
            (proof-string-to-list 
             (substring s
                        (string-match (concat "[^" separator "]")
                                      s end-of-word-occurence)) separator)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic code for the locked region and the queue region            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME: da: doc below needs fixing.
(defvar proof-locked-hwm nil
  "Upper limit of the locked region")

(defvar proof-queue-loose-end nil
  "Limit of the queue region that is not equal to proof-locked-hwm.")

(defvar proof-locked-span nil
  "Upper limit of the locked region")

(defvar proof-queue-span nil
  "Upper limit of the locked region")

(make-variable-buffer-local 'proof-locked-span)
(make-variable-buffer-local 'proof-queue-span)

(defface proof-queue-face
  '((((type x) (class color) (background light))
     (:background "mistyrose"))
    (((type x) (class color) (background dark))
     (:background "mediumvioletred"))
    (t				
     (:foreground "white" :background "black")))
  "Face for commands in proof script waiting to be processed."
  :group 'proof)

(defface proof-locked-face
  '((((type x) (class color) (background light))   
     (:background "lavender"))
    (((type x) (class color) (background dark))   
     (:background "navy"))
    (t				
     (:underline t)))
  "Face for locked region of proof script (processed commands)."
  :group 'proof)

(defun proof-init-segmentation ()
  (setq proof-queue-loose-end nil)
  (if (not proof-queue-span)
      (setq proof-queue-span (make-span 1 1)))
  (set-span-property proof-queue-span 'start-closed t)
  (set-span-property proof-queue-span 'end-open t)
  (span-read-only proof-queue-span)

  (set-span-property proof-queue-span 'face 'proof-queue-face)

  (detach-span proof-queue-span)
  
  (setq proof-locked-hwm nil)
  (if (not proof-locked-span)
      (setq proof-locked-span (make-span 1 1)))
  (set-span-property proof-locked-span 'start-closed t)
  (set-span-property proof-locked-span 'end-open t)
  (span-read-only proof-locked-span)

  (set-span-property proof-locked-span 'face 'proof-locked-face)

  (detach-span proof-locked-span))

(defsubst proof-lock-unlocked ()
  "Make the locked region read only."
  (span-read-only proof-locked-span))

(defsubst proof-unlock-locked ()
  "Make the locked region read-write."
  (span-read-write proof-locked-span))

(defsubst proof-set-queue-endpoints (start end)
  "Set the queue span to be START, END."
  (set-span-endpoints proof-queue-span start end))

(defsubst proof-set-locked-endpoints (start end)
  "Set the locked span to be START, END."
  (set-span-endpoints proof-locked-span start end))

(defsubst proof-detach-queue ()
  "Remove the span for the queue region."
  (and proof-queue-span (detach-span proof-queue-span)))

(defsubst proof-detach-locked ()
  "Remove the span for the locked region."
  (and proof-locked-span (detach-span proof-locked-span)))

(defsubst proof-set-queue-start (start)
  "Set the queue span to begin at START."
  (set-span-start proof-queue-span start))

(defsubst proof-set-queue-end (end)
  "Set the queue span to end at END."
  (set-span-end proof-queue-span end))

(defun proof-detach-segments (&optional buffer)
  "Remove locked and queue region from BUFFER.
Defaults to current buffer when BUFFER is nil."
  (let ((buffer (or buffer (current-buffer))))
    (save-excursion
      (proof-detach-queue)
      (proof-detach-locked))))

(defsubst proof-set-locked-end (end)
  "Set the end of the locked region to be END, sort of? FIXME.
If END is past the end of the buffer, remove the locked region.
Otherwise set the locked region to be from the start of the
buffer to END."
  (if (>= (point-min) end)
      (proof-detach-locked)
    (set-span-endpoints proof-locked-span (point-min) end)))

(defun proof-unprocessed-begin ()
  "Return end of locked region in current buffer or (point-min) otherwise."
  (or 
   (and (member (current-buffer) proof-script-buffer-list)
	proof-locked-span (span-end proof-locked-span))
   (point-min)))

(defun proof-locked-end ()
  "Return end of the locked region of the current buffer.
Only call this from a scripting buffer."
  (if (member (current-buffer) proof-script-buffer-list)
      (proof-unprocessed-begin)
    (error "bug: proof-locked-end called from wrong buffer")))

(defsubst proof-end-of-queue ()
  "Return the end of the queue region, or nil if none."
  (and proof-queue-span (span-end proof-queue-span)))

(defun proof-dont-show-annotations ()
  "Set display values of annotations (characters 128-255) to be invisible."
  (let ((disp (make-display-table))
	(i 128))
	(while (< i 256)
	  (aset disp i [])
	  (incf i))
	(cond ((fboundp 'add-spec-to-specifier)
	       (add-spec-to-specifier current-display-table disp
				      (current-buffer)))
	      ((boundp 'buffer-display-table)
	       (setq buffer-display-table disp)))))

(defun proof-mark-buffer-atomic (buffer)
  "Mark BUFFER as having processed in a single step.

If buffer already contains a locked region, only the remainder of the
buffer is closed off atomically." 
  (save-excursion
    (set-buffer buffer)
    (let ((span (make-span (proof-unprocessed-begin) (point-max)))
	  cmd)
      ;; compute first command of buffer
      (goto-char (point-min))
      (proof-find-next-terminator)
      (let ((cmd-list (member-if
		       (lambda (entry) (equal (car entry) 'cmd))
		       (proof-segment-up-to (point)))))
	(proof-init-segmentation)
	(if cmd-list 
	    (progn
	      (setq cmd (second (car cmd-list)))
	      (set-span-property span 'type 'vanilla)
	      (set-span-property span 'cmd cmd))
	  ;; If there was no command in the buffer, atomic
	  ;; span becomes a comment.
	  (set-span-property span 'type 'comment)))
      (proof-set-locked-end (point-max))
      (or (member buffer proof-script-buffer-list)
	  (setq proof-script-buffer-list
		(append proof-script-buffer-list (list buffer)))))))

(defun proof-file-truename (filename)
  "Returns the true name of the file FILENAME or nil."
  (and filename (file-exists-p filename) (file-truename filename)))

(defun proof-register-new-processed-file (file)
  "Register a new FILE as having been processed by the prover."
  (let* ((cfile (file-truename file))
	 (buffer (proof-file-to-buffer cfile)))
    (assert (not (member cfile proof-included-files-list))
	    'showargs "proof-register-new-processed-file")
    (setq proof-included-files-list
	  (cons cfile proof-included-files-list))
    (or (equal cfile
	       (file-truename (buffer-file-name
			       (car proof-script-buffer-list))))
	(not buffer)
	(proof-mark-buffer-atomic buffer))))


;;; begin messy COMPATIBILITY HACKING for FSFmacs.
;;; 
;;; In case Emacs is not aware of the function read-shell-command,
;;; and read-shell-command-map, we duplicate some code adjusted from
;;; minibuf.el distributed with XEmacs 20.4.
;;;
;;; This code is still required as of FSF Emacs 20.2.
;;;
;;; I think bothering with this just to give completion for
;;; when proof-prog-name-ask-p=t is a big overkill!   - da.
;;;	
(defvar read-shell-command-map
  (let ((map (make-sparse-keymap 'read-shell-command-map)))
    (if (not (fboundp 'set-keymap-parents))
        (if (fboundp 'set-keymap-parent)
	    ;; FSF Emacs 20.2
	    (set-keymap-parent map minibuffer-local-map)
	  ;; Earlier FSF Emacs
	  (setq map (append minibuffer-local-map map))
	  ;; XEmacs versions?
	  (set-keymap-parents map minibuffer-local-map)))
    (define-key map "\t" 'comint-dynamic-complete)
    (define-key map "\M-\t" 'comint-dynamic-complete)
    (define-key map "\M-?" 'comint-dynamic-list-completions)
    map)
  "Minibuffer keymap used by shell-command and related commands.")

(or (fboundp 'read-shell-command)
    (defun read-shell-command (prompt &optional initial-input history)
      "Just like read-string, but uses read-shell-command-map:
\\{read-shell-command-map}"
      (let ((minibuffer-completion-table nil))
        (read-from-minibuffer prompt initial-input read-shell-command-map
                              nil (or history
                              'shell-command-history)))))

;; The package fume-func provides a function with the same name and
;; specification. However, fume-func's version is incorrect.
;; da: make this hack more prominent so someone remembers to remove it
;; later on.
(and (fboundp 'fume-match-find-next-function-name)
(defun fume-match-find-next-function-name (buffer)
  "General next function name in BUFFER finder using match.
  The regexp is assumed to be a two item list the car of which is the regexp
  to use, and the cdr of which is the match position of the function name"
  (save-excursion
    (set-buffer buffer)
    (let ((r (car fume-function-name-regexp))
	  (p (cdr fume-function-name-regexp)))
      (and (re-search-forward r nil t)
	   (cons (buffer-substring (setq p (match-beginning p)) (point)) p))))))


;;; end messy COMPATIBILITY HACKING


;;
;; Misc movement functions
;;

;; FIXME da: these next two functions slightly different, why?
;; (unprocessed-begin vs proof-locked-end)
(defun proof-goto-end-of-locked-interactive ()
  "Jump to the end of the locked region."
  (interactive)
  (switch-to-buffer (car proof-script-buffer-list))
  (goto-char (proof-locked-end)))

(defun proof-goto-end-of-locked ()
  "Jump to the end of the locked region."
  (goto-char (proof-unprocessed-begin)))

(defun proof-in-locked-region-p ()
  "Non-nil if point is in locked region.  Assumes proof script buffer current."
  (< (point) (proof-locked-end)))

(defun proof-goto-end-of-locked-if-pos-not-visible-in-window ()
  "If the end of the locked region is not visible, jump to the end of it."
  (interactive)
  (let* ((proof-script-buffer (car proof-script-buffer-list))
	 (pos (save-excursion
	       (set-buffer proof-script-buffer)
	       (proof-locked-end))))
    (or (pos-visible-in-window-p pos (get-buffer-window
				      proof-script-buffer t))
        (proof-goto-end-of-locked-interactive))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Starting and stopping the proof-system shell                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-shell-live-buffer ()
  "Return buffer of active proof assistant, or nil if none running."
  (and proof-shell-buffer
       (comint-check-proc proof-shell-buffer)
       proof-shell-buffer))

(defun proof-start-shell ()
  "Initialise a shell-like buffer for a proof assistant.

Also generates goal and response buffers.
Initialises current buffer for scripting.
Does nothing if proof assistant is already running."
  (if (proof-shell-live-buffer)
      ()
    (run-hooks 'proof-pre-shell-start-hook)
    (setq proof-included-files-list nil)
    (if proof-prog-name-ask-p
	(save-excursion
	  (setq proof-prog-name (read-shell-command "Run process: "
						    proof-prog-name))))
    (let ((proc
	   (concat "Inferior "
		   (substring proof-prog-name
			      (string-match "[^/]*$" proof-prog-name)))))
      (while (get-buffer (concat "*" proc "*"))
	(if (string= (substring proc -1) ">")
	    (aset proc (- (length proc) 2) 
		  (+ 1 (aref proc (- (length proc) 2))))
	  (setq proc (concat proc "<2>"))))

      (message (format "Starting %s process..." proc))

      ;; Starting the inferior process (asynchronous)
      (let ((prog-name-list (proof-string-to-list proof-prog-name " ")))
	(apply 'make-comint  (append (list proc (car prog-name-list) nil)
				     (cdr prog-name-list))))
      ;; To send any initialisation commands to the inferior process,
      ;; consult proof-shell-config-done...

      (setq proof-shell-buffer (get-buffer (concat "*" proc "*"))
	    proof-pbp-buffer (get-buffer-create (concat "*" proc "-goals*"))
	    proof-response-buffer (get-buffer-create (concat "*" proc
	    "-response*")))

      (save-excursion
	(set-buffer proof-shell-buffer)
	(funcall proof-mode-for-shell)
	(set-buffer proof-pbp-buffer)
	(funcall proof-mode-for-pbp))

      (setq proof-script-buffer-list (list (current-buffer)))
      (proof-init-segmentation)
      (setq proof-active-buffer-fake-minor-mode t)
      (run-hooks 'proof-activate-scripting-hook)

      (if (fboundp 'redraw-modeline)
	  (redraw-modeline)
	(force-mode-line-update))

      (or (assq 'proof-active-buffer-fake-minor-mode minor-mode-alist)
	  (setq minor-mode-alist
		(append minor-mode-alist
			(list '(proof-active-buffer-fake-minor-mode 
				" Scripting")))))

      (message 
       (format "Starting %s process... done." proc)))))
  

;; Should this be the same as proof-restart-script?
;; Perhaps this is redundant.
(defun proof-stop-shell ()
  "Exit the proof process.  Runs proof-shell-exit-hook if non-nil"
  (interactive)
  (save-excursion
    (let ((buffer (proof-shell-live-buffer)) 
	  proc)
      (if buffer
	  (progn
	    (save-excursion
	      (set-buffer buffer)
	      (setq proc (process-name (get-buffer-process)))
	      (comint-send-eof)
		(mapcar 'proof-detach-segments proof-script-buffer-list)
	      (kill-buffer))
	    (run-hooks 'proof-shell-exit-hook)

             ;;it is important that the hooks are
	     ;;run after the buffer has been killed. In the reverse
	     ;;order e.g., intall-shell-fonts causes problems and it
	     ;;is impossible to restart the PROOF shell

	    (message (format "%s process terminated." proc)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Proof by pointing                                       ;;
;;          All very lego-specific at present                       ;;
;;          To make sense of this code, you should read the         ;;
;;          relevant LFCS tech report by tms, yb, and djs           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defvar pbp-goal-command nil
  "Command informing the prover that `pbp-button-action' has been
  requested on a goal.")

(defvar pbp-hyp-command nil
  "Command informing the prover that `pbp-button-action' has been
  requested on an assumption.")

(defun pbp-button-action (event)
   (interactive "e")
   (mouse-set-point event)
   (pbp-construct-command))

; Using the spans in a mouse behavior is quite simple: from the
; mouse position, find the relevant span, then get its annotation
; and produce a piece of text that will be inserted in the right
; buffer.  

(defun proof-expand-path (string)
  (let ((a 0) (l (length string)) ls)
    (while (< a l) 
      (setq ls (cons (int-to-string (aref string a)) 
		     (cons " " ls)))
      (incf a))
    (apply 'concat (nreverse ls))))

(defun proof-send-span (event)
  (interactive "e")
  (let* ((span (span-at (mouse-set-point event) 'type))
	 (str (span-property span 'cmd)))
    (cond ((and (member (current-buffer) proof-script-buffer-list) (not (null span)))
	   (proof-goto-end-of-locked)
	   (cond ((eq (span-property span 'type) 'vanilla)
		  (insert str)))))))

(defun pbp-construct-command ()
  (let* ((span (span-at (point) 'proof))
	 (top-span (span-at (point) 'proof-top-element))
	 top-info)
    (if (null top-span) ()
      (setq top-info (span-property top-span 'proof-top-element))
      (pop-to-buffer (car proof-script-buffer-list))
      (cond
       (span
	(proof-invisible-command 
	 (format (if (eq 'hyp (car top-info)) pbp-hyp-command 
		                              pbp-goal-command)
		 (concat (cdr top-info) (proof-expand-path 
					 (span-property span 'proof))))))
       ((eq (car top-info) 'hyp)
	(proof-invisible-command (format pbp-hyp-command (cdr top-info))))
       (t
	 (proof-insert-pbp-command (format pbp-change-goal (cdr top-info))))))
    ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Turning annotated output into pbp goal set              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-shell-first-special-char nil "where the specials start")
(defvar proof-shell-goal-char nil "goal mark")
(defvar proof-shell-start-char nil "annotation start")
(defvar proof-shell-end-char nil "annotation end")
(defvar proof-shell-field-char nil "annotated field end")

(defvar proof-shell-eager-annotation-start nil
  "Eager annotation field start.  A regular expression or nil.
An eager annotation indicates to Emacs that some following output
should be displayed immediately and not accumulated for parsing.
Set to nil if the proof to disable this feature.")

(defvar proof-shell-eager-annotation-end "$"
  "Eager annotation field end.  A regular expression or nil.
An eager annotation indicates to Emacs that some following output
should be displayed immediately and not accumulated for parsing.
Set to nil if the proof to disable this feature.

The default value is \"$\" to match up to the end of the line.")

(defvar proof-shell-assumption-regexp nil
  "A regular expression matching the name of assumptions.")

;; FIXME da: where is this variable used?  
;;	      dropped in favour of goal-char?
;; Answer: this is used in *specific* modes, see e.g.
;; lego-goal-hyp.  This stuff needs making more generic.
(defvar proof-shell-goal-regexp nil
  "A regular expression matching the identifier of a goal.")

(defvar proof-shell-noise-regexp nil
  "Unwanted information output from the proof process within
  `proof-start-goals-regexp' and `proof-end-goals-regexp'.")

(defun pbp-make-top-span (start end)
  (let (span name)
    (goto-char start)
    ;; FIXME da: why name?  This is a character function
    (setq name (funcall proof-goal-hyp-fn))
    (beginning-of-line)
    (setq start (point))
    (goto-char end)
    (beginning-of-line)
    (backward-char)
    (setq span (make-span start (point)))
    (set-span-property span 'mouse-face 'highlight)
    (set-span-property span 'proof-top-element name)))

;; Need this for processing error strings and so forth


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   The filter. First some functions that handle those few         ;;
;;   occasions when the glorious illusion that is script-management ;;
;;   is temporarily suspended                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;   Output from the proof process is handled lazily, so that only  
;;   the output from the last of multiple commands is actually      
;;   processed (assuming they're all successful)

(defvar proof-shell-delayed-output nil
  "The last interesting output the proof process output, and what to do
   with it.")

(defvar proof-shell-proof-completed nil
  "Flag indicating that a completed proof has just been observed.")

(defvar proof-analyse-using-stack nil
  "Are annotations sent by proof assistant local or global")

(defun proof-shell-analyse-structure (string)
  (save-excursion
    (let* ((ip 0) (op 0) ap (l (length string)) 
	   (ann (make-string (length string) ?x))
           (stack ()) (topl ()) 
	   (out (make-string l ?x)) c span)
      (while (< ip l)	
	(if (< (setq c (aref string ip)) 128)
	    (progn (aset out op c)
		   (incf op)))
	(incf ip))
      (display-buffer (set-buffer proof-pbp-buffer))
      (erase-buffer)
      (insert (substring out 0 op))

      (setq ip 0
	    op 1)
      (while (< ip l)
	(setq c (aref string ip))
	(cond
	 ((= c proof-shell-goal-char)
	  (setq topl (cons op topl))
	  (setq ap 0))
	 ((= c proof-shell-start-char)
	  (if proof-analyse-using-stack
	      (setq ap (- ap (- (aref string (incf ip)) 128)))
	    (setq ap (- (aref string (incf ip)) 128)))
	  (incf ip)
	  (while (not (= (setq c (aref string ip)) proof-shell-end-char))
	    (aset ann ap (- c 128))
	    (incf ap)
	    (incf ip))
	  (setq stack (cons op (cons (substring ann 0 ap) stack))))
	 ((= c proof-shell-field-char)
	  (setq span (make-span (car stack) op))
	  (set-span-property span 'mouse-face 'highlight)
	  (set-span-property span 'proof (car (cdr stack)))
	  ;; Pop annotation off stack
	  (and proof-analyse-using-stack
	       (progn
		 (setq ap 0)
		 (while (< ap (length (cadr stack)))
		   (aset ann ap (aref (cadr stack) ap))
		   (incf ap))))
	  ;; Finish popping annotations
	  (setq stack (cdr (cdr stack))))
	 (t (incf op)))
	(incf ip))
      (setq topl (reverse (cons (point-max) topl)))
      ;; If we want Coq pbp: (setq coq-current-goal 1)
      (while (setq ip (car topl) 
		   topl (cdr topl))
	(pbp-make-top-span ip (car topl))))))

(defun proof-shell-strip-annotations (string)
  (let* ((ip 0) (op 0) (l (length string)) (out (make-string l ?x )))
    (while (< ip l)
      (if (>= (aref string ip) proof-shell-first-special-char)
	  (if (char-equal (aref string ip) proof-shell-start-char)
	      (progn (incf ip)
		     (while (< (aref string ip) proof-shell-first-special-char)
		       (incf ip))))
	(aset out op (aref string ip))
	(incf op))
      (incf ip))
    (substring out 0 op)))

(defun proof-shell-handle-output (start-regexp end-regexp append-face)
  "Pretty print output in process buffer in specified region.
The region begins with the match for START-REGEXP and is delimited by
END-REGEXP. The match for END-REGEXP is not part of the specified region.
Removes any annotations in the region.
Fontifies the region.
Appends APPEND-FACE to the text property of the region .
Returns the string (with faces) in the specified region."
  (let (start end string)
    (save-excursion
      (set-buffer proof-shell-buffer)
      (goto-char (point-max))
      (setq start (search-backward-regexp start-regexp))
      (save-excursion (setq end (- (search-forward-regexp end-regexp)
				   (length (match-string 0)))))
      (setq string
	    (proof-shell-strip-annotations (buffer-substring start end)))
      (delete-region start end)
      (insert string)
      (setq end (+ start (length string)))
      ;; This doesn't work with FSF Emacs 20.2's version of Font-lock
      ;; because there are no known keywords in the process buffer
      ;; Never mind. In a forthcoming version, the process buffer will
      ;; not be tempered with. Fontification will take place in a
      ;; separate response buffer.
      ;; (font-lock-fontify-region start end)
      (font-lock-append-text-property start end 'face append-face)
      (buffer-substring start end))))

(defun proof-shell-handle-delayed-output ()
  (let ((ins (car proof-shell-delayed-output))
	(str (cdr proof-shell-delayed-output)))
    (display-buffer proof-pbp-buffer)
    (save-excursion
      (cond 
       ((eq ins 'insert)
	(setq str (proof-shell-strip-annotations str))
	(set-buffer proof-pbp-buffer)
	(erase-buffer)
	(insert str))
       ((eq ins 'analyse)
	(proof-shell-analyse-structure str))
       (t (set-buffer proof-pbp-buffer)
	  (insert "\n\nbug???")))))
  (run-hooks 'proof-shell-handle-delayed-output-hook)
  (setq proof-shell-delayed-output (cons 'insert "done")))


;; Notes on markup in the scripting buffer. (da)
;;
;; The locked region is covered by a collection of non-overlaping
;; spans (our abstraction of extents/overlays).
;;
;; For an unfinished proof, there is one extent for each command 
;; or comment outside a command.   For a finished proof, there
;; is one extent for the whole proof.
;;
;; Each command span has a 'type property, one of:
;;
;;     'vanilla      Initialised in proof-semis-to-vanillas, for
;;     'goalsave 
;;     'comment      A comment outside a command.
;;
;;  All spans except those of type 'comment have a 'cmd property,
;;  which is set to a string of its command.  This is the
;;  text in the buffer stripped of leading whitespace and any comments.
;;
;; 

(defun proof-shell-handle-error (cmd string)
  "React on an error message triggered by the prover.
We display the process buffer, scroll to the end, beep and fontify the
error message. At the end it calls `proof-shell-handle-error-hook'. "
    ;; We extract all text between text matching
    ;; `proof-shell-error-regexp' and the following prompt.
    ;; Alternatively one could higlight all output between the
    ;; previous and the current prompt.
    ;; +/- of our approach
    ;; + Previous not so relevent output is not highlighted
    ;; - Proof systems have to conform to error messages whose start  can be
    ;;   detected by a regular expression.
  (proof-shell-handle-output
   proof-shell-error-regexp proof-shell-annotated-prompt-regexp
   'font-lock-error-face)
  (save-excursion (display-buffer proof-shell-buffer)
		  (beep)

		  ;; unwind script buffer
		  (set-buffer (car proof-script-buffer-list))
		  (proof-detach-queue)
		  (delete-spans (proof-locked-end) (point-max) 'type)
		  (proof-release-lock)
		  (run-hooks 'proof-shell-handle-error-hook)))

(defun proof-shell-handle-interrupt ()
  (save-excursion 
    (display-buffer (set-buffer proof-pbp-buffer))
    (goto-char (point-max))
    (newline 2)
    (insert-string 
     "Interrupt: Script Management may be in an inconsistent state\n")
    (beep)
  (set-buffer (car proof-script-buffer-list)))
  (if proof-shell-busy
      (progn (proof-detach-queue)
	     (delete-spans (proof-locked-end) (point-max) 'type)
	     (proof-release-lock))))


(defun proof-goals-pos (span maparg)
  "Given a span, this function returns the start of it if corresponds
  to a goal and nil otherwise."
 (and (eq 'goal (car (span-property span 'proof-top-element)))
		(span-start span)))

(defun proof-pbp-focus-on-first-goal ()
  "If the `proof-pbp-buffer' contains goals, the first one is brought
  into view."
  (and (fboundp 'map-extents)
       (let
	   ((pos (map-extents 'proof-goals-pos proof-pbp-buffer
			      nil nil nil nil 'proof-top-element)))
	 (and pos (set-window-point
		   (get-buffer-window proof-pbp-buffer t) pos)))))

           

(defun proof-shell-process-output (cmd string)
  "Process shell output by matching on STRING.
This function deals with errors, start of proofs, abortions of
proofs and completions of proofs. All other output from the proof
engine is simply reported to the user in the response buffer.
To extend this function, set
`proof-shell-process-output-system-specific'.

This function - it can return one of 4 things: 'error, 'interrupt,
'loopback, or nil. 'loopback means this was output from pbp, and
should be inserted into the script buffer and sent back to the proof
assistant."
  (cond
   ((string-match proof-shell-error-regexp string)
    (cons 'error (proof-shell-strip-annotations
		  (substring string
			     (match-beginning 0)))))

   ((string-match proof-shell-interrupt-regexp string)
    'interrupt)

   ((and proof-shell-abort-goal-regexp
	 (string-match proof-shell-abort-goal-regexp string))
    (setq proof-shell-delayed-output (cons 'insert "\n\nAborted"))
    ())
	 
   ((string-match proof-shell-proof-completed-regexp string)
    (setq proof-shell-proof-completed t)
    (setq proof-shell-delayed-output
	  (cons 'insert (concat "\n" (match-string 0 string)))))

   ((string-match proof-shell-start-goals-regexp string)
    (setq proof-shell-proof-completed nil)
    (let (start end)
      (while (progn (setq start (match-end 0))
		    (string-match proof-shell-start-goals-regexp 
				  string start)))
      (setq end (string-match proof-shell-end-goals-regexp string start))
      (setq proof-shell-delayed-output 
	    (cons 'analyse (substring string start end)))))
       
   ((string-match proof-shell-result-start string)
    (setq proof-shell-proof-completed nil)
    (let (start end)
      (setq start (+ 1 (match-end 0)))
      (string-match proof-shell-result-end string)
      (setq end (- (match-beginning 0) 1))
      (cons 'loopback (substring string start end))))
   
   ;; hook to tailor proof-shell-process-output to a specific proof
   ;; system  
   ((and proof-shell-process-output-system-specific
	 (funcall (car proof-shell-process-output-system-specific)
		  cmd string))
    (funcall (cdr proof-shell-process-output-system-specific)
	     cmd string))

   (t (setq proof-shell-delayed-output (cons 'insert string)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Low-level commands for shell communication                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME da: Should this kind of ordinary input go onto the queue of
;; things to do?  Then errors during processing would prevent it being
;; sent.  Also the proof shell lock would be set automatically, which
;; might be nice?
(defun proof-shell-insert (string)
  (save-excursion
    (set-buffer proof-shell-buffer)
    (goto-char (point-max))

    (run-hooks 'proof-shell-insert-hook)
    (insert string)

    ;; xemacs and emacs19 have different semantics for what happens when
    ;; shell input is sent next to a marker
    ;; the following code accommodates both definitions
    (if (marker-position proof-marker)
	(let ((inserted (point)))
	  (comint-send-input)
	  (set-marker proof-marker inserted))
      (comint-send-input))))

;; da: This function strips carriage returns from string, then
;; sends it.  (Why strip CRs?)
(defun proof-send (string)
  (let ((l (length string)) (i 0))
    (while (< i l)
      (if (= (aref string i) ?\n) (aset string i ?\ ))
      (incf i)))
  (save-excursion (proof-shell-insert string)))

(defun proof-check-process-available (&optional relaxed)
  "Adjust internal variables for scripting of current buffer.

Signals an error if current buffer is not a proof script or if the
proof process is not idle. If RELAXED is set, nothing more is done. No
changes are necessary if the current buffer is already in Scripting
minor mode. Otherwise, the current buffer will become the current
scripting buffer provided the current scripting buffer has either no
locked region or everything in it has been processed."
  (proof-start-shell)
  (cond
   ((not (or relaxed (eq proof-buffer-type 'script)))
    (error "Must be running in a script buffer"))
   (proof-shell-busy (error "Proof Process Busy!"))
   (relaxed ())			;exit cond

   ;; No buffer is in Scripting minor mode.
   ;; We assume the setup is done somewhere else
   ((null proof-script-buffer-list) (assert nil))

   ;; The current buffer is in Scripting minor mode
   ((equal (current-buffer) (car proof-script-buffer-list)))

   (t
    (let ((script-buffer (car proof-script-buffer-list))
	  (current-buffer (current-buffer)))
      (save-excursion
	(set-buffer script-buffer)
	;; We only allow switching of the Scripting buffer if the
	;; locked region is either empty or full for all buffers.
	(if (or 
	     (eq (proof-unprocessed-begin) (point-min))
	     (progn
	       ;; Skip empty space at end of buffer
	       (goto-char (point-max))
	       (skip-chars-backward " \t\n")
	       (>= (proof-unprocessed-begin) (point))))

	    ;; we are changing the scripting buffer
	   (progn
	     (setq proof-active-buffer-fake-minor-mode nil)
	     (set-buffer current-buffer)

	     ;; does the current buffer contain locked regions already?
	     (if (member current-buffer proof-script-buffer-list)
		 (setq proof-script-buffer-list
		       (remove current-buffer proof-script-buffer-list))
	       (proof-init-segmentation))
	     (setq proof-script-buffer-list
		   (cons current-buffer proof-script-buffer-list))
	     (setq proof-active-buffer-fake-minor-mode t)
	     (run-hooks 'proof-activate-scripting-hook))
	  (error "Cannot deal with two unfinished script buffers!")
	))))))


(defun proof-grab-lock (&optional relaxed)
  (proof-start-shell)
  (proof-check-process-available relaxed)
  (setq proof-shell-busy t))

(defun proof-release-lock ()
  (if (proof-shell-live-buffer)
      (progn
	(if (not proof-shell-busy)
	    ; (error "Bug in proof-release-lock: Proof process not busy")
	    (message "Nag, nag, nag: proof-release-lock: Proof process not busy"))
	(if (not (member (current-buffer) proof-script-buffer-list))
	    (error "Bug in proof-release-lock: Don't own process"))
	(setq proof-shell-busy nil))))

; Pass start and end as nil if the cmd isn't in the buffer.

(defun proof-start-queue (start end alist &optional relaxed)
  (if start
      (proof-set-queue-endpoints start end))
  (let (item)
    (while (and alist (string= 
		       (nth 1 (setq item (car alist))) 
		       proof-no-command))
    (funcall (nth 2 item) (car item))
    (setq alist (cdr alist)))
  (if alist
      (progn
	(proof-grab-lock relaxed) 
	(setq proof-shell-delayed-output (cons 'insert "Done."))
	(setq proof-action-list alist)
	(proof-send (nth 1 item))))))

; returns t if it's run out of input


;; 
;; The loop looks like: Execute the
; command, and if it's successful, do action on span.  If the
; command's not successful, we bounce the rest of the queue and do
; some error processing.

(defun proof-shell-exec-loop () 
"Process the proof-action-list.
proof-action-list contains a list of (span,command,action) triples.
This function is called with a non-empty proof-action-list, where the
head of the list is the previously executed command which succeeded.
We execute (action span) on the first item, then (action span) on
following items which have proof-no-command as their cmd components.
Return non-nil if the action list becomes empty; unlock the process
and removes the queue region.  Otherwise send the next command to the
proof process."
  (save-excursion
    (set-buffer (car proof-script-buffer-list))
    ;; (if (null proof-action-list) 
    ;;	(error "proof-shell-exec-loop: called with empty proof-action-list."))
    ;; Be more relaxed about calls with empty action list
    (if proof-action-list
	(let ((item (car proof-action-list)))
	  ;; Do (action span) on first item in list
	  (funcall (nth 2 item) (car item))
	  (setq proof-action-list (cdr proof-action-list))
	  ;; Process following items in list with the form
	  ;; ("COMMENT" cmd) by calling (cmd "COMMENT")
	  (while (and proof-action-list
		      (string= 
		       (nth 1 (setq item (car proof-action-list))) 
		       proof-no-command))
	    ;; Do (action span) on comments
	    (funcall (nth 2 item) (car item))
	    (setq proof-action-list (cdr proof-action-list)))
	  ;; If action list is empty now, release the process lock
	  (if (null proof-action-list)
	      (progn (proof-release-lock)
		     (proof-detach-queue)
		     ;; indicate finished
		     t)
	    ;; Send the next command to the process
	    (proof-send (nth 1 item))
	    ;; indicate not finished
	    nil))
      ;; Just indicate finished if called with empty proof-action-list.
      t)))

(defun proof-shell-insert-loopback-cmd  (cmd)
  "Insert command sequence triggered by the proof process
at the end of locked region (after inserting a newline and indenting)."
  (save-excursion
    (set-buffer (car proof-script-buffer-list))
    (let (span)
      (proof-goto-end-of-locked)
      (newline-and-indent)
      (insert cmd)
      (setq span (make-span (proof-locked-end) (point)))
      (set-span-property span 'type 'pbp)
      (set-span-property span 'cmd cmd)
      (proof-set-queue-endpoints (proof-locked-end) (point))
      (setq proof-action-list 
	    (cons (car proof-action-list) 
		  (cons (list span cmd 'proof-done-advancing)
			(cdr proof-action-list)))))))

;; ******** NB **********
;;  While we're using pty communication, this code is OK, since all
;; eager annotations are one line long, and we get input a line at a
;; time. If we go over to piped communication, it will break.

;; FIXME: highlight eager annotation-end : fix proof-shell-handle-output
;; to highlight whole string.
(defun proof-shell-popup-eager-annotation ()
  "Process urgent messages.
Eager annotations are annotations which the proof system produces
while it's doing something (e.g. loading libraries) to say how much
progress it's made. Obviously we need to display these as soon as they
arrive."
  (let ((str (proof-shell-handle-output
	      proof-shell-eager-annotation-start
	      proof-shell-eager-annotation-end
	      'font-lock-eager-annotation-face))
	file module)
    (proof-message str)))

(defun proof-response-buffer-display (str face)
  "Display STR with FACE in response buffer."
  (let ((start))
    (save-excursion
      (set-buffer proof-response-buffer)
      (setq start (goto-char (point-max)))
      (insert str)
      (font-lock-fontify-region start (point-max))
      (font-lock-append-text-property start (point-max) 'face face)
      (insert "\n"))))

(defun proof-file-to-buffer (filename)
  "Converts a FILENAME  into a buffer name"
  (let* ((buffers (buffer-list))
	 (pos
	  (position (file-truename filename)
		    (mapcar 'proof-file-truename
			    (mapcar 'buffer-file-name
				    buffers))
		    :test 'equal)))
    (and pos (nth pos buffers))))

(defun proof-files-to-buffers (filenames)
  "Converts a list of FILENAMES into a list of BUFFERS."
  (if (null filenames) nil
    (let* ((buffer (proof-file-to-buffer (car filenames)))
	  (rest (proof-files-to-buffers (cdr filenames))))
      (if buffer (cons buffer rest) rest))))
	  
		  
(defun proof-shell-process-urgent-message (message)
  "Display and analyse urgent MESSAGE for asserting or retracting files."
  (proof-message message)
  (proof-response-buffer-display message 'font-lock-eager-annotation-face)

  ;; Is the prover processing a file?
  (cond ((and proof-shell-process-file 
	      (string-match (car proof-shell-process-file) message))
	 (progn
	   (setq file (funcall (cdr proof-shell-process-file) message))
	   (if (string= file "") 
	       (setq file (buffer-file-name (car proof-script-buffer-list))))
	   (proof-register-new-processed-file file)))

  ;; Is the prover retracting across files?
	((and proof-shell-retract-files-regexp
	      (string-match proof-shell-retract-files-regexp message))
	 (let ((current-included proof-included-files-list))
	   (setq proof-included-files-list
		 (funcall proof-shell-compute-new-files-list message))
	   (proof-restart-buffers
	    (remove (car proof-script-buffer-list)
		    (proof-files-to-buffers
		     (set-difference current-included
				     proof-included-files-list))))))))

(defun proof-shell-process-urgent-messages (str)
  "Scan the process output for urgent messages.
Display them immediately in the Response buffer.
Keep `proof-included-files-list' up to date.
The input STR is the most recent chunk of output sent to the process
filter. We assume that urgent messages are fully contained in STR."
  (let ((start (string-match proof-shell-eager-annotation-start str))
	end)
    (and start
	 (setq end
	       (string-match proof-shell-eager-annotation-end str
	       start))
	 (progn
	   (proof-shell-process-urgent-message
	    (proof-shell-strip-annotations (substring str start end)))
	   (proof-shell-process-urgent-messages (substring str end))))))

(defun proof-shell-filter (str) 
  "Filter for the proof assistant shell-process.
We sleep until we get a wakeup-char in the input, then run
proof-shell-process-output, and set proof-marker to keep track of
how far we've got."
  (and proof-shell-eager-annotation-start
       (proof-shell-process-urgent-messages str)) 
       
  (if (or
       ;; Some proof systems can be hacked to have annotated prompts;
       ;; for these we set proof-shell-wakeup-char to the annotation special.  
       (and proof-shell-wakeup-char
	   (string-match (char-to-string proof-shell-wakeup-char) str))
       ;; Others rely on a standard top-level (e.g. SML) whose prompt can't
       ;; be hacked.  For those we use the annotated prompt regexp.
       (string-match proof-shell-annotated-prompt-regexp str))
      (if (null (marker-position proof-marker))
	  ;; Set marker to first prompt in output buffer, and sleep again.
	  (progn
	    (goto-char (point-min))
	    (re-search-forward proof-shell-annotated-prompt-regexp)
	    (set-marker proof-marker (point)))
	;; We've matched against a second prompt in str now.  Search
	;; the output buffer for the second prompt after the one previously
	;; marked.
	(let (string res cmd)	
	  (goto-char (marker-position proof-marker))
	  (re-search-forward proof-shell-annotated-prompt-regexp nil t)
	  (backward-char (- (match-end 0) (match-beginning 0)))
	  (setq string (buffer-substring (marker-position proof-marker)
					 (point)))
	  (goto-char (point-max))	; da: assumed to be after a prompt?
	  (setq cmd (nth 1 (car proof-action-list)))
	  (save-excursion
	    ;; 
	    (setq res (proof-shell-process-output cmd string))
	    ;; da: Added this next line to redisplay, for proof-toolbar
	    ;; FIXME: should do this for all frames displaying the script
	    ;; buffer!
	    ;; ODDITY: has strange effect on highlighting, leave it.
	    ;; (redisplay-frame (window-buffer  t)
	    (cond
	     ((eq (car-safe res) 'error)
	      (proof-shell-handle-error cmd (cdr res)))
	     ((eq res 'interrupt)
	      (proof-shell-handle-interrupt))
	     ((eq (car-safe res) 'loopback)
	      (proof-shell-insert-loopback-cmd (cdr res))
	      (proof-shell-exec-loop))
	     (t (if (proof-shell-exec-loop)
		    (proof-shell-handle-delayed-output)))))))))

(defun proof-last-goal-or-goalsave ()
  (save-excursion
    (let ((span (span-at-before (proof-locked-end) 'type)))
    (while (and span 
		(not (eq (span-property span 'type) 'goalsave))
		(or (eq (span-property span 'type) 'comment)
		    (not (funcall proof-goal-command-p
				       (span-property span 'cmd)))))
      (setq span (prev-span span 'type)))
    span)))
    
(defun proof-done-invisible (span) ())

(defun proof-invisible-command (cmd &optional relaxed)
  "Send cmd to the proof process without responding to the user."
  (proof-check-process-available relaxed)
  (if (not (string-match proof-re-end-of-cmd cmd))
      (setq cmd (concat cmd proof-terminal-string)))
  (proof-start-queue nil nil (list (list nil cmd
  'proof-done-invisible)) relaxed))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          User Commands                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
; Script management uses two major segments: Locked, which marks text
; which has been sent to the proof assistant and cannot be altered
; without being retracted, and Queue, which contains stuff being
; queued for processing.  proof-action-list contains a list of
; (span,command,action) triples. The loop looks like: Execute the
; command, and if it's successful, do action on span.  If the
; command's not successful, we bounce the rest of the queue and do
; some error processing.
;
; when a span has been processed, we classify it as follows:
; 'goalsave - denoting a 'goalsave pair in the locked region
;    a 'goalsave region has a 'name property which is the name of the goal
; 'comment - denoting a comment
; 'pbp - denoting a span created by pbp
; 'vanilla - denoting any other span.
;   'pbp & 'vanilla spans have a property 'cmd, which says what
;   command they contain. 

; We don't allow commands while the queue has anything in it.  So we
; do configuration by concatenating the config command on the front in
; proof-send

;;         proof-assert-until-point, and various gunk for its       ;;
;;         setup and callback                                       ;;


(defun proof-done-advancing (span)
  "The callback function for assert-until-point."
  (let ((end (span-end span)) nam gspan next cmd)
    (proof-set-locked-end end)
    (proof-set-queue-start end)
    (setq cmd (span-property span 'cmd))
    (cond
     ((eq (span-property span 'type) 'comment)
      (set-span-property span 'mouse-face 'highlight))
     ((string-match proof-save-command-regexp cmd)
      ;; In coq, we have the invariant that if we've done a save and
      ;; there's a top-level declaration then it must be the
      ;; associated goal.  (Notice that because it's a callback it
      ;; must have been approved by the theorem prover.)
      (if (string-match proof-save-with-hole-regexp cmd)
	  (setq nam (match-string 2 cmd)))
      (setq gspan span)
      (while (or (eq (span-property gspan 'type) 'comment)
		 (not (funcall proof-goal-command-p 
				    (setq cmd (span-property gspan 'cmd)))))
	(setq next (prev-span gspan 'type))
	(delete-span gspan)
	(setq gspan next))

      (if (null nam)
	  (if (string-match proof-goal-with-hole-regexp
			    (span-property gspan 'cmd))
	      (setq nam (match-string 2 (span-property gspan 'cmd)))
	    ;; This only works for Coq, but LEGO raises an error if
	    ;; there's no name.
	    ;; FIXME: a nonsense for Isabelle.
	    (setq nam "Unnamed_thm")))

      (set-span-end gspan end)
      (set-span-property gspan 'mouse-face 'highlight)
      (set-span-property gspan 'type 'goalsave)
      (set-span-property gspan 'name nam)

      (and proof-lift-global
	   (funcall proof-lift-global gspan)))
     (t
      (set-span-property span 'mouse-face 'highlight)
      (and proof-global-p 
	   (funcall proof-global-p cmd)
	   proof-lift-global
	   (funcall proof-lift-global span))))))



;; FIXME da: Below it would probably be faster to use the primitive
;; skip-chars-forward rather than scanning character-by-character 
;; with a lisp loop over the whole region. Also I'm not convinced that
;; Emacs should be better at skipping whitespace and comments than the
;; proof process itself!

(defun proof-segment-up-to (pos &optional next-command-end)
  "Create a list of (type,int,string) tuples from end of locked region to POS.
Each tuple denotes the command and the position of its terminator,
type is one of 'comment, or 'cmd. 'unclosed-comment may be consed onto
the start if the segment finishes with an unclosed comment.
If optional NEXT-COMMAND-END is non-nil, we contine past POS until
the next command end."
  (save-excursion
      ;; depth marks number of nested comments.
      ;; quote-parity is false if we're inside ""'s.
      ;; Only one of (depth > 0) and (not quote-parity)
      ;; should be true at once. -- hhg
    (let ((str (make-string (- (buffer-size)
			       (proof-unprocessed-begin) -10) ?x))
	  (i 0) (depth 0) (quote-parity t) done alist c)
     (proof-goto-end-of-locked)
     (while (not done)
       (cond
	;; Case 1. We've reached POS, not allowed to go past it,
	;; and are inside a comment
	((and (not next-command-end) (= (point) pos) (> depth 0))
	 (setq done t alist (cons 'unclosed-comment alist)))
	;; Case 2. We've reached the end of the buffer while
	;; scanning inside a comment or string
	((= (point) (point-max))
	 (cond
	  ((not quote-parity)
	   (message "Warning: unclosed quote"))
	  ((> depth 0)
	   (setq done t alist (cons 'unclosed-comment alist))))
	 (setq done t))
	;; Case 3. Found a comment end, not inside a string
	((and (looking-at (regexp-quote proof-comment-end)) quote-parity)
	 (if (= depth 0) 
	     (progn
	       (message "Warning: extraneous comment end")
	       (setq done t))
	   (setq depth (- depth 1))
	   (forward-char (length proof-comment-end))
	   (if (eq i 0) 
	       (setq alist (cons (list 'comment "" (point)) alist))
	     (aset str i ?\ )
	     (incf i))))
	;; Case 4. Found a comment start, not inside a string
	((and (looking-at (regexp-quote proof-comment-start)) quote-parity)
	 (setq depth (+ depth 1))
	 (forward-char (length proof-comment-start)))
	;; Case 5. Inside a comment. 
	((> depth 0)
	 (forward-char))
	;; Case 6. Anything else
	(t
	 ;; Skip whitespace before the start of a command, otherwise
	 ;; other characters in the accumulator string str
	 (setq c (char-after (point)))
	 (if (or (> i 0) (not (= (char-syntax c) ?\ )))
	     (progn
	       (aset str i c)
	       (incf i)))
	 
	 (if (looking-at "\"")	; FIXME da: should this be more generic?
	     (setq quote-parity (not quote-parity)))
	 
	 (forward-char)

	 ;; Found the end of a command
	 (if (and (= c proof-terminal-char) quote-parity)
	     (progn 
	       (setq alist 
		     (cons (list 'cmd (substring str 0 i) (point)) alist))
	       (if (>= (point) pos)
		   (setq done t)
		 (setq i 0)))))))
     alist)))

(defun proof-semis-to-vanillas (semis &optional callback-fn)
  "Convert a sequence of semicolon positions (returned by the above
function) to a set of vanilla extents."
  (let ((ct (proof-unprocessed-begin)) span alist semi)
    (while (not (null semis))
      (setq semi (car semis)
            span (make-span ct (nth 2 semi))
	    ct (nth 2 semi))
      (if (eq (car (car semis)) 'cmd)
	  (progn
	    (set-span-property span 'type 'vanilla)
	    (set-span-property span 'cmd (nth 1 semi))
	    (setq alist (cons (list span (nth 1 semi) 
				    (or callback-fn 'proof-done-advancing))
			      alist)))
	(set-span-property span 'type 'comment)
	(setq alist (cons (list span proof-no-command 'proof-done-advancing) alist)))
	(setq semis (cdr semis)))
    (nreverse alist)))

;;
;; Two commands for moving forwards in proof scripts.
;; Moving forward for a "new" command may insert spaces
;; or new lines.  Moving forward for the "next" command
;; does not.
;;

(defun proof-script-new-command-advance ()
  "Move point to a nice position for a new command.
Assumes that point is at the end of a command."
  (interactive)
  (if proof-one-command-per-line
      ;; One command per line: move to next new line,
      ;; creating one if at end of buffer or at the
      ;; start of a blank line.  (This has the pleasing
      ;; effect that blank regions of the buffer are
      ;; automatically extended when inserting new commands).
      (cond
       ((eq (forward-line) 1)
	(newline))
       ((eolp)
        (newline)
	(forward-line -1)))
    ;; Multiple commands per line: skip spaces at point,
    ;; and insert the same number of spaces that were
    ;; skipped in front of point (at least one).
    ;; This has the pleasing effect that the spacing
    ;; policy of the current line is copied: e.g.
    ;;   <command>;  <command>;
    ;; Tab columns don't work properly, however.
    ;; Instead of proof-one-command-per-line we could
    ;; introduce a "proof-command-separator" to improve
    ;; this.
    (let ((newspace (max (skip-chars-forward " \t") 1))
	  (p (point)))
	(insert-char ?\ newspace)
	(goto-char p))))

(defun proof-script-next-command-advance ()
  "Move point to the beginning of the next command if it's nearby.
Assumes that point is at the end of a command."
  (interactive)
  ;; skip whitespace on this line
  (skip-chars-forward " \t")		
  (if (and proof-one-command-per-line (eolp))
      ;; go to the next line if we have one command per line
      (forward-line)))



; Assert until point - We actually use this to implement the 
; assert-until-point, active terminator keypress, and find-next-terminator. 
; In different cases we want different things, but usually the information
; (i.e. are we inside a comment) isn't available until we've actually run
; proof-segment-up-to (point), hence all the different options when we've
; done so.

;; FIXME da: this command doesn't behave as the doc string says when
;; inside comments.  Also is unhelpful at the start of commands, and
;; in the locked region.  I prefer the new version below.

(defun proof-assert-until-point
  (&optional unclosed-comment-fun ignore-proof-process-p)
  "Process the region from the end of the locked-region until point.
   Default action if inside a comment is just to go until the start of
   the comment. If you want something different, put it inside
   unclosed-comment-fun. If ignore-proof-process-p is set, no commands
   will be added to the queue."
  (interactive)
  (let ((pt (point))
	(crowbar (or ignore-proof-process-p (proof-check-process-available)))
	semis)
    (save-excursion
      (if (not (re-search-backward "\\S-" (proof-unprocessed-begin) t))
	  (progn (goto-char pt)
		 (error "Nothing to do!")))
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (not crowbar) (null semis))
	  (error "Nothing to do!"))
      (goto-char (nth 2 (car semis)))
      (and (not ignore-proof-process-p)
	   (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
;	     (if crowbar (setq vanillas (cons crowbar vanillas)))
	     (proof-start-queue (proof-unprocessed-begin) (point) vanillas))))))


;; da: This is my alternative version of the above.
;; It works from the locked region too.
;; I find it more convenient to assert up to the current command (command
;; point is inside), and move to the next command.
;; This means proofs can be easily replayed with point at the start
;; of lines.  Above function gives stupid "nothing to do error." when
;; point is on the start of line or in the locked region.

;; FIXME: behaviour inside comments may be odd at the moment.  (it
;; doesn't behave as docstring suggests, same prob as
;; proof-assert-until-point)
;; FIXME: polish the undo behaviour and quit behaviour of this
;; command (should inhibit quit somewhere or other).

(defun proof-assert-next-command
  (&optional unclosed-comment-fun ignore-proof-process-p
	     dont-move-forward for-new-command)
  "Process until the end of the next unprocessed command after point.
If inside a comment, just to go the start of
the comment.  If you want something different, put it inside
UNCLOSED-COMMENT-FUN. If IGNORE-PROOF-PROCESS-P is set, no commands
will be added to the queue.
Afterwards, move forward to near the next command afterwards, unless
DONT-MOVE-FORWARD is non-nil.  If FOR-NEW-COMMAND is non-nil,
a space or newline will be inserted automatically."
  (interactive)
  (let ((pt (point))
	(crowbar (or ignore-proof-process-p (proof-check-process-available)))
	semis)
    (save-excursion
      ;; CHANGE from old proof-assert-until-point: don't bother check
      ;; for non-whitespace between locked region and point.
      ;; CHANGE: ask proof-segment-up-to to scan until command end
      ;; (which it used to do anyway, except in the case of a comment)
      (setq semis (proof-segment-up-to (point) t)))
    ;; old code:
    ;;(if (not (re-search-backward "\\S-" (proof-unprocessed-begin) t))
    ;;	  (progn (goto-char pt)
    ;;       (error "Nothing to do!")))
    ;; (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis))
	  ;; CHANGE: if inside a comment, do as the documentation
	  ;; suggests.
	  (setq semis nil))
      (if (and (not ignore-proof-process-p) (not crowbar) (null semis))
	  (error "Nothing to do!"))
      (goto-char (nth 2 (car semis)))
      (if (not ignore-proof-process-p)
	   (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
;	     (if crowbar (setq vanillas (cons crowbar vanillas)))
	     (proof-start-queue (proof-unprocessed-begin) (point) vanillas)))
      ;; This is done after the queuing to be polite: it means the
      ;; spacing policy enforced here is not put into the locked
      ;; region so the user can re-edit.
      (if (not dont-move-forward)
	   (if for-new-command
	       (proof-script-new-command-advance)
	     (proof-script-next-command-advance))))))

;;         insert-pbp-command - an advancing command, for use when  ;;
;;         PbpHyp or Pbp has executed in LEGO, and returned a       ;;
;;         command for us to run                                    ;;

(defun proof-insert-pbp-command (cmd)
  (proof-check-process-available)
  (let (span)
    (proof-goto-end-of-locked)
    (insert cmd)
    (setq span (make-span (proof-locked-end) (point)))
    (set-span-property span 'type 'pbp)
    (set-span-property span 'cmd cmd)
    (proof-start-queue (proof-unprocessed-begin) (point) 
		       (list (list span cmd 'proof-done-advancing)))))


;;         proof-retract-until-point and associated gunk            ;;
;;         most of the hard work (i.e computing the commands to do  ;;
;;         the retraction) is implemented in the customisation      ;;
;;         module (lego.el or coq.el) which is why this looks so    ;;
;;         straightforward                                          ;;


(defun proof-done-retracting (span)
  "Updates display after proof process has reset its state. See also
the documentation for `proof-retract-until-point'. It optionally
deletes the region corresponding to the proof sequence."
  (let ((start (span-start span))
        (end (span-end span))
	(kill (span-property span 'delete-me)))
    (proof-set-locked-end start)
    (proof-set-queue-end start)
    (delete-spans start end 'type)
    (delete-span span)
    (if kill (delete-region start end))))

(defun proof-setup-retract-action (start end proof-command delete-region)
  (let ((span (make-span start end)))
    (set-span-property span 'delete-me delete-region)
    (list (list span proof-command 'proof-done-retracting))))

(defun proof-retract-target (target delete-region)
  (let ((end (proof-locked-end))
	(start (span-start target))
	(span (proof-last-goal-or-goalsave))
	actions)
    
    (if (and span (not (eq (span-property span 'type) 'goalsave)))
	(if (< (span-end span) (span-end target))
	    (progn
	      (setq span target)
	      (while (and span (eq (span-property span 'type) 'comment))
		(setq span (next-span span 'type)))
	      (setq actions (proof-setup-retract-action
			     start end 
			     (if (null span) proof-no-command
			       (funcall proof-count-undos-fn span))
			     delete-region)
		    end start))
	  
	  (setq actions (proof-setup-retract-action (span-start span) end
						    proof-kill-goal-command
						    delete-region)
		end (span-start span))))
    
    (if (> end start) 
	(setq actions
	      (nconc actions (proof-setup-retract-action 
			      start end
			      (funcall proof-find-and-forget-fn target)
			      delete-region))))
      
    (proof-start-queue (min start end) (proof-locked-end) actions)))

;; FIXME da:  I would rather that this function moved point to
;; the start of the region retracted?

(defun proof-retract-until-point (&optional delete-region)
  "Sets up the proof process for retracting until point. In
   particular, it sets a flag for the filter process to call
   `proof-done-retracting' after the proof process has actually
   successfully reset its state. It optionally deletes the region in
   the proof script corresponding to the proof command sequence. If
   this function is invoked outside a locked region, the last
   successfully processed command is undone."
  (interactive)
  (proof-check-process-available)
  (let ((span (span-at (point) 'type)))
    (if (null (proof-locked-end)) (error "No locked region"))
    (and (null span)
	 (progn (proof-goto-end-of-locked) (backward-char)
		(setq span (span-at (point) 'type))))
    (proof-retract-target span delete-region)))

;;         proof-try-command                                        ;;
;;         this isn't really in the spirit of script management,    ;;
;;         but sometimes the user wants to just try an expression   ;;
;;         without having to undo it in order to try something      ;;
;;         different. Of course you can easily lose sync by doing   ;;
;;         something here which changes the proof state             ;;

(defun proof-done-trying (span)
  (delete-span span)
  (proof-detach-queue))
			
(defun proof-try-command
  (&optional unclosed-comment-fun) 

  "Process the command at point,
   but don't add it to the locked region. This will only happen if
   the command satisfies proof-state-preserving-p.

   Default action if inside a comment is just to go until the start of
   the comment. If you want something different, put it inside
   unclosed-comment-fun."
  (interactive)
  (let ((pt (point)) semis crowbar test)
    (setq crowbar (proof-check-process-available))
    (save-excursion
      (if (not (re-search-backward "\\S-" (proof-locked-end) t))
	  (progn (goto-char pt)
		 (error "Nothing to do!")))
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not crowbar) (null semis)) (error "Nothing to do!"))
      (setq test (car semis))
      (if (not (funcall proof-state-preserving-p (nth 1 test)))
	  (error "Command is not state preserving"))
      (goto-char (nth 2 test))
      (let ((vanillas (proof-semis-to-vanillas (list test)
					       'proof-done-trying)))
;	(if crowbar (setq vanillas (cons crowbar vanillas)))
	(proof-start-queue (proof-unprocessed-begin) (point) vanillas)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;         misc other user functions                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun proof-undo-last-successful-command (&optional no-delete)
  "Undo last successful command at end of locked region.
Unless optional NO-DELETE is set, the text is also deleted from
the proof script."
  (interactive "p")
  (let ((lastspan (span-at-before (proof-locked-end) 'type)))
    (if lastspan
	(progn
	  (goto-char (span-start lastspan))
	  (proof-retract-until-point (not no-delete)))
      (error "Nothing to undo!"))))

(defun proof-interrupt-process ()
  (interactive)
  (if (not (proof-shell-live-buffer))
      (error "Proof Process Not Started!"))
  (if (not (member (current-buffer) proof-script-buffer-list))
      (error "Don't own process!"))
  (if (not proof-shell-busy)
      (error "Proof Process Not Active!"))
  (save-excursion
    (set-buffer proof-shell-buffer)
    (comint-interrupt-subjob)))
  
    
(defun proof-find-next-terminator ()
  "Set point after next `proof-terminal-char'."
  (interactive)
  (let ((cmd (span-at (point) 'type)))
    (if cmd (goto-char (span-end cmd))
      (and (re-search-forward "\\S-" nil t)
	   (proof-assert-until-point nil 'ignore-proof-process)))))

(defun proof-goto-command-start ()
  "Move point to start of current command."
  (interactive)
  (let ((cmd (span-at (point) 'type)))
    (if cmd (goto-char (span-start cmd)) ; BUG: only works for unclosed proofs.
      (let ((semis (proof-segment-up-to (point) t)))
	(if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
	(if (and semis (car semis) (car (car semis)))
	    (progn
	      (goto-char (nth 2 (car (car semis))))
	      (skip-chars-forward " \t\n")))))))

(defun proof-process-buffer ()
  "Process the current buffer and set point at the end of the buffer."
  (interactive)
  (goto-char (point-max))
  (proof-assert-until-point))

(defun proof-restart-buffer (buffer)
  "Remove all extents in BUFFER and update `proof-script-buffer-list'."
  (save-excursion
    (if (buffer-live-p buffer)
	(progn
	  (set-buffer buffer)
	  (setq proof-active-buffer-fake-minor-mode nil)
	  (delete-spans (point-min) (point-max) 'type)
	  (proof-detach-segments)))
    (setq proof-script-buffer-list
	  (remove buffer proof-script-buffer-list))))

(defun proof-restart-buffers (bufferlist)
  "Remove all extents in BUFFERLIST and update `proof-script-buffer-list'."
  (mapcar 'proof-restart-buffer bufferlist))
  
;; For when things go horribly wrong
;; FIXME: this needs to politely stop the process by sending
;; an EOF or customizable command.  (maybe timeout waiting for
;; it to die before killing the buffer)
;; maybe better:
;;  Put a funciton to remove all extents in buffers into
;; the kill-buffer-hook for the proof shell.  Then this
;; function just stops the shell nicely (see proof-stop-shell).
(defun proof-restart-script ()
  "Restart Proof General.
Kill off the proof assistant process and remove all markings in the
script buffers."
  (interactive)
  (proof-restart-buffers proof-script-buffer-list)
  ;; { (equal proof-script-buffer-list nil) }
   (setq proof-shell-busy nil
	 proof-included-files-list nil
	 proof-shell-proof-completed nil)
   (if (buffer-live-p proof-shell-buffer) 
       (kill-buffer proof-shell-buffer))
   (if (buffer-live-p proof-pbp-buffer)
       (kill-buffer proof-pbp-buffer))
   (and (buffer-live-p proof-response-buffer)
	(kill-buffer proof-response-buffer)))

;; For when things go not-quite-so-horribly wrong
;; FIXME: this may need work, and maybe isn't needed at
;; all (proof-retract-file when it appears may be enough).
(defun proof-restart-script-same-process ()
  (interactive)
  (save-excursion
    (if (buffer-live-p proof-script-buffer)
	(progn
	  (set-buffer proof-script-buffer)
	  (setq proof-active-buffer-fake-minor-mode nil)
	  (delete-spans (point-min) (point-max) 'type)
	  (proof-detach-segments)))))

;; A command for making things go horribly wrong - it moves the
;; end-of-locked-region marker backwards, so user had better move it
;; correctly to sync with the proof state, or things will go all
;; pear-shaped.

(defun proof-frob-locked-end ()
  (interactive)
  "Move the end of the locked region backwards. 
Only for use by consenting adults."
  (cond
   ((not (member (current-buffer) proof-script-buffer-list))
    (error "Not in proof buffer"))
   ((> (point) (proof-locked-end))
    (error "Can only move backwards"))
   (t (proof-set-locked-end (point))
      (delete-spans (proof-locked-end) (point-max) 'type))))

(defvar proof-minibuffer-history nil
  "History of proof commands read from the minibuffer")

(defun proof-execute-minibuffer-cmd ()
  (interactive)
  (let (cmd)
    (proof-check-process-available 'relaxed)
    (setq cmd (read-string "Command: " nil 'proof-minibuffer-history))
    (proof-invisible-command cmd 'relaxed)))

;; da: below functions for input history simulation are quick hacks.
;; Could certainly be made more efficient.

(defvar proof-command-history nil
  "History used by proof-previous-matching-command and friends.")

(defun proof-build-command-history ()
  "Construct proof-command-history from script buffer.
Based on position of point."
  ;; let
  )

(defun proof-previous-matching-command (arg)
  "Search through previous commands for new command matching current input."
  (interactive))
  ;;(if (not (memq last-command '(proof-previous-matching-command
  ;; proof-next-matching-command)))
      ;; Start a new search
      
  

(defun proof-next-matching-command (arg)
  "Search through following commands for new command matching current input."
  (interactive "p")
  (proof-previous-matching-command (- arg)))
	  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Popup and Pulldown Menu ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Menu commands for the underlying proof assistant

;;; These are defcustom'd so that users may re-configure
;;; the system to their liking.
(defcustom proof-ctxt-string ""
  "*Command to display the context in proof assistant."
  :type 'string
  :group 'proof)

(defcustom proof-help-string ""
  "*Command to ask for help in proof assistant."
  :type 'string
  :group 'proof)

(defcustom proof-prf-string ""
  "Command to display proof state in proof assistant."
  :type 'string
  :group 'proof)

(defvar proof-goal-command nil
  "Command to set a goal in the proof assistant.  String or fn.
If a string, the format character %s will be replaced by the
goal string. If a function, should return a command string to
insert when called interactively.")

(defvar proof-save-command nil
  "Command to save a proved theorem in the proof assistant.  String or fn.
If a string, the format character %s will be replaced by the
theorem name. If a function, should return a command string to
insert when called interactively.")

;;; Functions using the above 

(defun proof-ctxt ()
  "List context."
  (interactive) 
  (proof-invisible-command (concat proof-ctxt-string proof-terminal-string)))

(defun proof-help ()
  "Print help message giving syntax."
  (interactive)
  (proof-invisible-command (concat proof-help-string proof-terminal-string)))

(defun proof-prf ()
  "List proof state."
  (interactive)
  (proof-invisible-command (concat proof-prf-string proof-terminal-string)))



;; FIXME: da: add more general function for inserting into the
;; script buffer and the proof process together, and using
;; a choice of minibuffer prompting (hated by power users, perfect
;; for novices).
;; Add named goals.
;; TODO:
;;   Add named goals.
;;   Coherent policy for movement here and elsewhere based on
;;    proof-one-command-per-line user option.
;;   Coherent policy for sending to process after writing into
;;    script buffer.  Could have one without the other.
;;    For example, may be more easy to edit complex goal string
;;    first in the script buffer.  Ditto for tactics, etc.

(defvar proof-issue-goal-history nil
  "History of goals for proof-issue-goal.")

(defun proof-issue-goal (goal-cmd)
  "Insert a goal command into the script buffer, issue it to prover."
  (interactive
   (if proof-goal-command 
       (if (stringp proof-goal-command)
	   (list (format proof-goal-command
			 (read-string "Goal: " ""
				      proof-issue-goal-history)))
	 (proof-goal-command))
     (error
      "Proof General not configured for goals: set proof-goal-command.")))
  (let ((proof-one-command-per-line t))   ; Goals always start at a new line
    (proof-issue-new-command goal-cmd)))

(defvar proof-issue-save-history nil
  "History of theorem names for proof-issue-save.")

(defun proof-issue-save (thmsave-cmd)
  "Insert a save theorem command into the script buffer, issue it."
  (interactive
   (if proof-save-command
       (if (stringp proof-save-command)
	   (list (format proof-save-command
			 (read-string "Save as: " ""
				      proof-issue-save-history)))
	 (proof-save-command))
     (error
      "Proof General not configured for save theorem: set proof-save-command.")))
  (let ((proof-one-command-per-line t))   ; Goals always start at a new line
    (proof-issue-new-command thmsave-cmd)))

(defun proof-issue-new-command (cmd)
  "Insert CMD into the script buffer and issue it to the proof assistant.
If point is in the locked region, move to the end of it first.
Start up the proof assistant if necessary."
  ;; FIXME: da: I think we need a (proof-script-switch-to-buffer)
  ;; function (so there is some control over display).
  ;; (switch-to-buffer proof-script-buffer)
  (if (proof-shell-live-buffer)
      (if (proof-in-locked-region-p)
	  (proof-goto-end-of-locked-interactive)))
  (proof-script-new-command-advance)
  ;; FIXME: fixup behaviour of undo here.  Really want
  ;; to temporarily disable undo for insertion.
  ;; (buffer-disable-undo) this trashes whole undo list!
  (insert cmd)
  ;; FIXME: could do proof-indent-line here, but let's
  ;; wait until indentation is fixed.
  (proof-assert-until-point))




;;; To be called from menu
(defun proof-info-mode ()
  "Call info on Proof General."
  (interactive)
  (info "ProofGeneral"))

(defun proof-exit ()
  "Exit Proof-assistant."
  (interactive)
  (proof-restart-script))

(defvar proof-help-menu
  '("Help"
	     ["Proof assistant web page"
	      (w3-fetch proof-www-home-page) t]
	     ["Help on Emacs proof-mode" proof-info-mode t]
	     )
  "The Help Menu in Script Management.")

(defvar proof-shared-menu
  (proof-append-element
   (append
    (list
     ["Display context" proof-ctxt
      :active (proof-shell-live-buffer)]
     ["Display proof state" proof-prf
      :active (proof-shell-live-buffer)]
     ["Exit proof assistant" proof-exit
      :active (proof-shell-live-buffer)])
    (if proof-tags-support
	(list
	 "----"
	 ["Find definition/declaration" find-tag-other-window t])
      nil))
    proof-help-menu))

(defvar proof-menu  
  (append '("Commands"
            ["Toggle active terminator" proof-active-terminator-minor-mode
	     :active t
	     :style toggle
             :selected proof-active-terminator-minor-mode]
            "----")
          (list (if (string-match "XEmacs 19.1[2-9]" emacs-version)
		    "--:doubleLine" "----"))
          proof-shared-menu
          )
  "*The menu for the proof assistant.")

(defvar proof-shell-menu proof-shared-menu
  "The menu for the Proof-assistant shell")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Active terminator minor mode                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflocal proof-active-terminator-minor-mode nil 
  "Active terminator minor mode flag")

(defun proof-active-terminator-minor-mode (&optional arg)
  "Toggle PROOF's Active Terminator minor mode.
With arg, turn on the Active Terminator minor mode if and only if arg
is positive.

If Active terminator mode is enabled, a terminator will process the
current command."

 (interactive "P")
 
;; has this minor mode been registered as such?
  (or (assq 'proof-active-terminator-minor-mode minor-mode-alist)
      (setq minor-mode-alist
            (append minor-mode-alist
                    (list '(proof-active-terminator-minor-mode
			    (concat " " proof-terminal-string))))))

  (setq proof-active-terminator-minor-mode
        (if (null arg) (not proof-active-terminator-minor-mode)
          (> (prefix-numeric-value arg) 0)))
  (if (fboundp 'redraw-modeline)
      (redraw-modeline)
    (force-mode-line-update)))

(defun proof-process-active-terminator ()
  "Insert the proof command terminator, and assert up to it.
Fire up proof process if necessary."
  (let ((mrk (point)) ins incomment)
    (if (looking-at "\\s-\\|\\'\\|\\w") 
	(if (not (re-search-backward "\\S-" (proof-unprocessed-begin) t))
	    (error "Nothing to do!")))
    (if (not (= (char-after (point)) proof-terminal-char))
	(progn (forward-char) (insert proof-terminal-string) (setq ins t)))
    (proof-assert-until-point
     (function (lambda ()
		 (setq incomment t)
		 (if ins (backward-delete-char 1))
		 (goto-char mrk)
		 (insert proof-terminal-string))))
    (or incomment
	(proof-script-next-command-advance))))

(defun proof-active-terminator ()
  "Insert the terminator, perhaps sending the command to the assistant.
If proof-active-terminator-minor-mode is non-nil, the command will be
sent to the assistant."
  (interactive)
  (if proof-active-terminator-minor-mode 
      (proof-process-active-terminator)
    (self-insert-command 1)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof General scripting mode configuration			    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; da: this isn't so nice if a scripting buffer should inherit
;; from another mode: e.g. for Isabelle, we would like to use
;; sml-mode.
;; FIXME: add more doc to the mode below, to give hints on
;; configuring for new assistants.
(define-derived-mode proof-mode fundamental-mode 
  proof-mode-name
  "Proof General major mode for proof scripts.
\\{proof-mode-map}
"
  (setq proof-buffer-type 'script)

  ;; Has buffer already been processed?
  (and (member buffer-file-truename proof-included-files-list)
       (proof-mark-buffer-atomic (current-buffer)))

  (make-local-variable 'kill-buffer-hook)
  (add-hook 'kill-buffer-hook
	    (lambda ()
	      (setq proof-script-buffer-list
		    (remove (current-buffer) proof-script-buffer-list)))))

;; FIXME: da: could we put these into another keymap already?
;; FIXME: da: it's offensive to experience users to rebind global stuff
;;        like meta-tab, this should be removed.
(defconst proof-universal-keys
  (append
   '(([(control c) (control c)] . proof-interrupt-process)
    ([(control c) (control v)] . proof-execute-minibuffer-cmd))
   (if proof-tags-support
       '(([(meta tab)]	       . tag-complete-symbol))
     nil))
"List of keybindings which for the script and response buffer. 
Elements of the list are tuples (k . f) 
where `k' is a keybinding (vector) and `f' the designated function.")

;; Fixed definitions in proof-mode-map, which don't depend on
;; prover configuration.
;;; INDENT HACK: font-lock only recognizes define-key at start of line
(let ((map proof-mode-map))
(define-key map [(control c) (control e)] 'proof-find-next-terminator)
(define-key map [(control c) (control a)] 'proof-goto-command-start)
(define-key map [(control c) (control n)] 'proof-assert-next-command)
(define-key map [(control c) (return)]	  'proof-assert-next-command)
(define-key map [(control c) (control t)] 'proof-try-command)
(define-key map [(control c) ?u]	  'proof-retract-until-point)
(define-key map [(control c) (control u)] 'proof-undo-last-successful-command)
(define-key map [(control c) ?\']	  'proof-goto-end-of-locked-interactive)
(define-key map [(control button1)]	  'proof-send-span)
(define-key map [(control c) (control b)] 'proof-process-buffer)
(define-key map [(control c) (control z)] 'proof-frob-locked-end)
(define-key map [(control c) (control p)] 'proof-prf)
(define-key map [(control c) ?c]	  'proof-ctxt)
(define-key map [(control c) ?h]	  'proof-help)
(define-key map [(meta p)]		  'proof-previous-matching-command)
(define-key map [(meta n)]		  'proof-next-matching-command)
;; FIXME da: this shouldn't need setting, because it works
;; via indent-line-function which is set below.  Check this.
(define-key map [tab] 'proof-indent-line)
(proof-define-keys map proof-universal-keys))



;; the following callback is an irritating hack - there should be some
;; elegant mechanism for computing constants after the child has
;; configured.

(defun proof-config-done () 
  "Finish setup of Proof General scripting mode.
Call this function in the derived mode for the proof assistant to
finish setup which depends on specific proof assistant configuration."
  ;; calculate some strings and regexps for searching
  (setq proof-terminal-string (char-to-string proof-terminal-char))

  ;; FIXME: these are LEGO specific!
  (setq pbp-goal-command (concat "Pbp %s" proof-terminal-string))
  (setq pbp-hyp-command (concat "PbpHyp %s" proof-terminal-string))

  ;; FIXME da: I'm not sure we ought to add spaces here, but if
  ;; we don't, there would be trouble overloading these settings
  ;; to also use as regexps for finding comments.
  ;; 
  (make-local-variable 'comment-start)
  (setq comment-start (concat proof-comment-start " "))
  (make-local-variable 'comment-end)
  (setq comment-end (concat " " proof-comment-end))
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip 
    (concat (regexp-quote proof-comment-start) "+\\s_?"))

  (setq proof-re-end-of-cmd (concat "\\s_*" proof-terminal-string "\\s_*\\\'"))
  (setq proof-re-term-or-comment 
	(concat proof-terminal-string "\\|" (regexp-quote proof-comment-start)
		"\\|" (regexp-quote proof-comment-end)))

  ;; func-menu --- Jump to a goal within a buffer
  (and (boundp 'fume-function-name-regexp-alist)
       (defvar fume-function-name-regexp-proof
	 (cons proof-goal-with-hole-regexp 2))
       (push (cons major-mode 'fume-function-name-regexp-proof)
	     fume-function-name-regexp-alist))
  (and (boundp 'fume-find-function-name-method-alist)
       (push (cons major-mode 'fume-match-find-next-function-name)
	     fume-find-function-name-method-alist))

  ;; Additional key definitions which depend on configuration for
  ;; specific proof assistant.
  (define-key proof-mode-map
    (vconcat [(control c)] (vector proof-terminal-char))
    'proof-active-terminator-minor-mode)

  (define-key proof-mode-map (vector proof-terminal-char)
    'proof-active-terminator)

  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'proof-indent-line)

  ;; Toolbar
  (if (featurep 'proof-toolbar)
      (proof-toolbar-setup))

  ;; Menu
  (easy-menu-define proof-mode-menu  
		    proof-mode-map
		    "Menu used in Proof General scripting mode."
		    (cons proof-mode-name
			  (append
			   (cdr proof-menu)
			   ;; begin UGLY COMPATIBILTY HACK
			   ;; older/non-existent customize doesn't have 
			   ;; this function.  
			   (if (fboundp 'customize-menu-create)
			       (list (customize-menu-create 'proof)
				     (customize-menu-create 'proof-internal
							    "Internals"))
			     nil)
			   ;; end UGLY COMPATIBILTY HACK
			   )))
  (easy-menu-add proof-mode-menu proof-mode-map)

  ;; For fontlock

  ;; setting font-lock-defaults explicitly is required by FSF Emacs
  ;; 20.2's version of font-lock
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(font-lock-keywords))

  ;; FIXME (da): zap commas support is too specific, should be enabled
  ;; by each proof assistant as it likes.
  (remove-hook 'font-lock-after-fontify-buffer-hook 'proof-zap-commas-buffer t)
  (add-hook 'font-lock-after-fontify-buffer-hook 
	    'proof-zap-commas-buffer nil t)
  (remove-hook 'font-lock-mode-hook 'proof-unfontify-separator t)
  (add-hook 'font-lock-mode-hook 'proof-unfontify-separator nil t)

  ;; if we don't have the following, zap-commas fails to work.
  ;; FIXME (da): setting this to t everywhere is too brutal.  Should
  ;; probably make it local.
  (and (boundp 'font-lock-always-fontify-immediately)
       (setq font-lock-always-fontify-immediately t))

  (run-hooks 'proof-mode-hook))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof General shell mode configuration			    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This has to come after proof-mode is defined
(define-derived-mode proof-shell-mode comint-mode 
  "proof-shell" "Proof shell mode - not standalone"
  (setq proof-buffer-type 'shell)
  (setq proof-shell-busy nil)
  (setq proof-shell-delayed-output (cons 'insert "done"))
  (setq proof-shell-proof-completed nil)
  (make-local-variable 'proof-shell-insert-hook)

  ;; comint customisation. comint-prompt-regexp is used by
  ;; comint-get-old-input, comint-skip-prompt, comint-bol, backward
  ;; matching input, etc.  
  (setq comint-prompt-regexp proof-shell-prompt-pattern)

  ;; An article by Helen Lowe in UITP'96 suggests that the user should
  ;; not see all output produced by the proof process. 
  (remove-hook 'comint-output-filter-functions
	       'comint-postoutput-scroll-to-bottom 'local)

  (add-hook 'comint-output-filter-functions 'proof-shell-filter nil 'local)
  (setq comint-get-old-input (function (lambda () "")))
  (proof-dont-show-annotations)
  (setq proof-marker (make-marker)))

(easy-menu-define proof-shell-menu
		  proof-shell-mode-map
		  "Menu used in Proof General shell mode."
		  (cons proof-mode-name (cdr proof-shell-menu)))

(defun proof-shell-config-done ()
  (accept-process-output (get-buffer-process (current-buffer)))

  ;; If the proof process in invoked on a different machine e.g.,
  ;; for proof-prog-name="rsh fastmachine proofprocess", one needs
  ;; to adjust the directory:
  (and proof-shell-cd
       (proof-shell-insert (format proof-shell-cd
       ;; under Emacs 19.34 default-directory contains "~" which causes
       ;; problems with LEGO's internal Cd command
				   (expand-file-name default-directory))))

  (if proof-shell-init-cmd
       (proof-shell-insert proof-shell-init-cmd))

  ;; Note that proof-marker actually gets set in proof-shell-filter.
  ;; This is manifestly a hack, but finding somewhere more convenient
  ;; to do the setup is tricky.

  (while (null (marker-position proof-marker))
    (if (accept-process-output (get-buffer-process (current-buffer)) 15)
	()
      (error "Failed to initialise proof process"))))

(define-derived-mode pbp-mode fundamental-mode 
  proof-mode-name "Proof by Pointing"
  ;; defined-derived-mode pbp-mode initialises pbp-mode-map
  (setq proof-buffer-type 'pbp)
  (suppress-keymap pbp-mode-map 'all)
;  (define-key pbp-mode-map [(button2)] 'pbp-button-action)
  (proof-define-keys pbp-mode-map proof-universal-keys)
  (erase-buffer))


(provide 'proof)
;; proof.el ends here
