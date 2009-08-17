;;; proof-shell.el --- Proof General shell mode.
;;
;; Copyright (C) 1994-2008 LFCS Edinburgh. 
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

(eval-when-compile
  (require 'cl)
  (require 'span)
  (require 'comint)
  (require 'font-lock)
  (require 'proof-utils))

(require 'proof-autoloads)
(require 'pg-response)
(require 'pg-goals)
(require 'proof-script)

;; ============================================================
;;
;; Internal variables used by proof shell
;;

(defvar proof-marker nil 
  "Marker in proof shell buffer pointing to previous command input.")

(defvar proof-action-list nil
  "A list of lists of the form

  (SPAN COMMAND ACTION [FLAGS])

which is a queue of things to do.  Flags are set for non-standard
commands (out of script).  They may include

  'no-response-display   do not display messages in *response* buffer
  'no-error-display      do not display errors/take error action
  'no-goals-display      do not goals in *goals* buffer

If flags are non-empty, other interactive cues will be surpressed.
\(E.g., printing help messages).

See the functions `proof-start-queue' and `proof-exec-loop'.")

(defvar proof-shell-silent nil
  "A flag, non-nil if PG thinks the prover is silent.")

;; We record the last output from the prover and a flag indicating its
;; type, as well as a previous ("delayed") version to for when the end
;; of the queue is reached or an error or interrupt occurs.

(defvar proof-shell-last-prompt nil
  "A raw record of the last prompt seen from the proof system.
This is the string matched by `proof-shell-annotated-prompt-regexp'.")

(defvar proof-shell-last-output-kind nil
  "A symbol denoting the type of the last output string from the proof system.
Specifically:

 'interrupt   	 An interrupt message
 'error	      	 An error message
 'abort	      	 A proof abort message
 'loopback    	 A command sent from the PA to be inserted into the script
 'response    	 A response message
 'goals	      	 A goals (proof state) display
 'systemspecific Something specific to a particular system,
		  -- see `proof-shell-classify-output-system-specific'

The output corresponding to this will be in proof-shell-last-output.

See also `proof-shell-proof-completed' for further information about
the proof process output, when ends of proofs are spotted.

This variable can be used for instance specific functions which want
to examine proof-shell-last-output.")

(defvar proof-shell-delayed-output ""
  "A copy of `proof-shell-last-output' held back for processing at end of queue.")

(defvar proof-shell-delayed-output-kind nil
  "A copy of `proof-shell-last-output-kind' held back for processing at end of queue.")

(defvar proof-shell-delayed-output-flags nil
  "A copy of the `proof-action-list' flags for `proof-shell-delayed-output'.")



;;
;; Indicator and fake minor mode for active scripting buffer
;; 

(defcustom proof-shell-active-scripting-indicator
  " Scripting"
  "Modeline indicator for active scripting buffer.
If first component is extent it will automatically follow the colour
of the queue region."
  :type 'sexp
  :group 'proof-general-internals)

(unless
    (assq 'proof-active-buffer-fake-minor-mode minor-mode-alist)
  (setq minor-mode-alist
	(append minor-mode-alist
		(list 
		 (list
		  'proof-active-buffer-fake-minor-mode
		  proof-shell-active-scripting-indicator)))))




;;
;; Implementing the process lock
;;
;; da: In fact, there is little need for a lock.  Since Emacs Lisp
;; code is single-threaded, a loop parsing process output cannot get
;; pre-empted by the user trying to send more input to the process,
;; or by the process filter trying to deal with more output.
;; (Moreover, we can tell when the process is busy because the 
;; queue is non-empty).
;;

;;
;; We have two functions:
;;
;;  proof-shell-ready-prover   
;;    starts proof shell, gives error if it's busy.
;;
;;  proof-activate-scripting  (in proof-script.el)
;;    calls proof-shell-ready-prover, and turns on scripting minor
;;    mode for current (scripting) buffer.
;;
;; Also, a new enabler predicate:
;;  
;;  proof-shell-available
;;    returns non-nil if a proof shell is active and not locked.
;;
;; Maybe proof-shell-ready-prover doesn't need to start the shell?
;;

;;;###autoload
(defun proof-shell-ready-prover (&optional queuemode)
  "Make sure the proof assistant is ready for a command.
If QUEUEMODE is set, succeed if the proof shell is busy but
has mode QUEUEMODE, which is a symbol or list of symbols.
Otherwise, if the shell is busy, give an error.
No change to current buffer or point."
  (proof-shell-start)
  (unless (or (not proof-shell-busy)
	      (eq queuemode proof-shell-busy)
	      (and (listp queuemode) 
		   (member proof-shell-busy queuemode)))
    (error "Proof Process Busy!")))

;;;###autoload
(defun proof-shell-live-buffer ()
  "Return buffer of active proof assistant, or nil if none running."
  (and proof-shell-buffer
       (buffer-live-p proof-shell-buffer)
       (comint-check-proc proof-shell-buffer)))

;;;###autoload
(defun proof-shell-available-p ()
  "Returns non-nil if there is a proof shell active and available.
No error messages.  Useful as menu or toolbar enabler."
  (and (proof-shell-live-buffer)
       (not proof-shell-busy)))

(defun proof-grab-lock (&optional queuemode)
  "Grab the proof shell lock, starting the proof assistant if need be.
Runs `proof-state-change-hook' to notify state change.
Clears the `proof-shell-error-or-interrupt-seen' flag.
If QUEUEMODE is supplied, set the lock to that value."
  (proof-shell-ready-prover queuemode)
  (setq proof-shell-error-or-interrupt-seen nil)
  (setq proof-shell-interrupt-pending nil)
  (setq proof-shell-busy (or queuemode t))
  ;; Make modeline indicator follow state (on XEmacs at least)
  ;; PG4.0: TODO: alter modeline indicator
  (run-hooks 'proof-state-change-hook))

(defun proof-release-lock (&optional err-or-int)
  "Release the proof shell lock, with error or interrupt flag ERR-OR-INT.
Clear `proof-shell-busy', and set `proof-shell-error-or-interrupt-seen'
to err-or-int."
  (setq proof-shell-error-or-interrupt-seen err-or-int)
  (setq proof-shell-busy nil)
  ;; PG4.0: TODO: alter modeline indicator
  )



;;
;;  Starting and stopping the proof shell  
;;

(defcustom proof-shell-fiddle-frames t 
  "Non-nil if proof-shell functions should fire-up/delete frames.
NB: this is a temporary config variable, it will be removed at some point!"
  :type 'boolean
  :group 'proof-shell)

(defun proof-shell-set-text-representation ()
  "Adjust representation for the current buffer to match `proof-shell-unicode'."
  (if proof-shell-unicode
      nil ;; leave at default for now; new Emacsen OK
    (and 
     ;; On GNU Emacs, prevent interpretation of multi-byte characters.
     ;; If not done, chars 128-255 get remapped higher, breaking regexps
     (fboundp 'toggle-enable-multibyte-characters)
     (toggle-enable-multibyte-characters -1))))


(defun proof-shell-start ()
  "Initialise a shell-like buffer for a proof assistant.

Also generates goal and response buffers.
Does nothing if proof assistant is already running."
  (interactive)
  (unless (proof-shell-live-buffer)

    (setq proof-included-files-list nil) ; clear some state

    (let ((name (buffer-file-name (current-buffer))))
      (if (and name proof-prog-name-guess proof-guess-command-line)
	  (setq proof-prog-name
		(apply proof-guess-command-line (list name)))))
    
    (if proof-prog-name-ask
	(save-excursion
	  (setq proof-prog-name (read-shell-command "Run process: "
						    proof-prog-name))))
    (let
	((proc (downcase proof-assistant)))

      ;; Starting the inferior process (asynchronous)
      (let* ((prog-name-list1
	      (if (proof-ass prog-args)
		 ;; If argument list supplied in <PA>-prog-args, use that.
		  (cons proof-prog-name (proof-ass prog-args))
		;; Otherwise, cut prog name on spaces
		(split-string proof-prog-name)))
	     (prog-name-list
	      ;; Splice in proof-rsh-command if it's non-nil 
	      (if (and proof-rsh-command
		       (> (length proof-rsh-command) 0))
		  (append (split-string proof-rsh-command)
			  prog-name-list1)
		prog-name-list1))
	     (prog-command-line 
	      (proof-splice-separator " " prog-name-list))

	     (process-connection-type
	      proof-shell-process-connection-type)

	     ;; Adjust the LANG variable to remove UTF-8 encoding 
	     ;; if not wanted; it conflicts with using chars 128-255 for markup
	     ;; and results in blocking in C libraries.
	    (process-environment
	     (append (proof-ass prog-env)	       ;; custom environment
		     (if proof-shell-unicode           ;; if specials not used,
			 process-environment	       ;; leave it alone
		       (cons
			(if (getenv "LANG")            
			    (format "LANG=%s"
				    (replace-in-string (getenv "LANG")
						       "\\.UTF-8" ""))
			  "LANG=C")
			(delete
			 (concat "LANG=" (getenv "LANG"))
			 process-environment)))))

	    ;; If we use troublesome codes between 128 and 255, we want to
	    ;; treat the output of the process as binary, except for
	    ;; end-of-line conversion (hence `raw-text').
	    ;; It is also the only sensible choice since we make the buffer
	    ;; unibyte below.
	    ;;
	    ;; Update: there are problems here with systems where
	    ;;  i) coding-system-for-read/write is not available 
	    ;;  (e.g. MacOS XEmacs non-mule)
	    ;; ii) 'rawtext can give wrong behaviour anyway 
	    ;;     (e.g. Mac OS GNU Emacs, maybe Windows)
	    ;;     probably because of line-feed conversion.
	    ;;
	    ;; Update: much more info now in Elisp manual and recommendations
	    ;; for sub processes.

	    (normal-coding-system-for-read (and (boundp 'coding-system-for-read)
						coding-system-for-read))
	    (coding-system-for-read
	     (if proof-shell-unicode 
		 (or (condition-case nil
			 (check-coding-system 'utf-8)
		       (error nil))
		     normal-coding-system-for-read)

	       (if (string-match "Linux" 
				 (shell-command-to-string "uname"))
		   'raw-text
		 normal-coding-system-for-read)))

	    (coding-system-for-write coding-system-for-read))

	;; PG 3.7: there is now yet another way to influence this:
	;; (unless 
	;;    (assoc (concat proof-prog-name " .*") process-coding-system-alist)
	;;  (setq process-coding-system-alist
	;;	(cons (cons (concat proof-prog-name " .*")
	;;		    (if proof-shell-unicode 'utf-8 'raw-text))
	;;	      process-coding-system-alist)))

	(message "Starting process: %s" prog-command-line)

	(apply 'make-comint  (append (list proc (car prog-name-list) nil)
				     (cdr prog-name-list)))
	
	(setq proof-shell-buffer (get-buffer (concat "*" proc "*")))

	(unless (proof-shell-live-buffer)
	  ;; Give error now if shell buffer isn't live
	  ;; Solves problem of make-comint succeeding but process
	  ;; exiting immediately.  Sentinels may still trigger.
	  (setq proof-shell-buffer nil)
	  (error "Starting process: %s..failed" prog-command-line))
	)

      ;; Create the associated buffers and set buffer variables

      (let ((goals	"*goals*")
	    (resp	"*response*")
	    (trace	"*trace*")
	    (thms	"*thms*"))
	(setq proof-goals-buffer    (get-buffer-create goals))
	(setq proof-response-buffer (get-buffer-create resp))
	(if proof-shell-trace-output-regexp
	    (setq proof-trace-buffer (get-buffer-create trace)))
	(if proof-shell-thms-output-regexp
	    (setq proof-thms-buffer (get-buffer-create thms)))
	;; Set the special-display-regexps now we have the buffer names
	(setq pg-response-special-display-regexp
	      (proof-regexp-alt goals resp trace thms)))

      (with-current-buffer proof-shell-buffer
	
	(erase-buffer)

	;; Set text representation (see CVS history for comments)
	(proof-shell-set-text-representation)

	;; Initialise shell mode (does process initialisation)
	(funcall proof-mode-for-shell)

	;; Check to see that the process is still going.  If not,
	;; switch buffer to display the error messages to the user.
	(unless (proof-shell-live-buffer)
	  (switch-to-buffer proof-shell-buffer)
	  (error "%s process exited!" proc))

	;; Initialise associated buffers

	(set-buffer proof-response-buffer)
	(proof-shell-set-text-representation)
	(funcall proof-mode-for-response)
	
	(proof-with-current-buffer-if-exists proof-trace-buffer
	  (proof-shell-set-text-representation)
	  (funcall proof-mode-for-response)
	  (setq pg-response-eagerly-raise nil))

	(set-buffer proof-goals-buffer)
	(proof-shell-set-text-representation)
	(funcall proof-mode-for-goals)

	;; Setting modes initialises local variables which
	;; may affect frame/buffer appearance: so we fire up frames
	;; once this has been done.
	(if proof-shell-fiddle-frames
	    ;; Call multiple-frames-enable in case we need to fire up
	    ;; new frames (NB: sets specifiers to remove modeline)
	    (save-selected-window
	      (save-selected-frame
	       (proof-multiple-frames-enable)))))

      (message "Starting %s process... done." proc))))


;;
;;  Shutting down proof shell and associated buffers
;;

;; Hooks here are handy for liaising with prover config stuff.

(defvar proof-shell-kill-function-hooks nil
  "Functions run from proof-shell-kill-function.")
  
(defun proof-shell-kill-function ()
  "Function run when a proof-shell buffer is killed.
Try to shut down the proof process nicely and clear locked
regions and state variables.  Value for `kill-buffer-hook' in
shell buffer, alled by `proof-shell-bail-out' if process exits."
  (let* ((alive    (comint-check-proc (current-buffer)))
	 (proc     (get-buffer-process (current-buffer)))
	 (bufname  (buffer-name)))
    (message "%s, cleaning up and exiting..." bufname)

    (let (;;(inhibit-quit t)		; disable C-g for now
	  timeout-id)			; [NO: don't do that]
      (sit-for 0)			; redisplay [does it work?]
      (if alive				; process still there
	  (progn
	    (catch 'exited
	      (set-process-sentinel proc
				    (lambda (p m) (throw 'exited t)))
	      ;; First, turn off scripting in any active scripting
	      ;; buffer.  (This helps support persistent sessions with
	      ;; Isabelle, for example, by making sure that no file is
	      ;; partly processed when exiting, and registering completed
	      ;; files).
	      (proof-deactivate-scripting-auto)
	      ;; FIXME: if the shell is busy now, we should wait
	      ;; for a while (in case deactivate causes processing)
	      ;; and then send an interrupt.

	      ;; Second, we try to shut down the proof process
	      ;; politely.  Do this before deleting other buffers,
	      ;; etc, so that any closing down processing works okay.
	      (if proof-shell-quit-cmd
		  (comint-send-string proc
				      (concat proof-shell-quit-cmd "\n"))
		(comint-send-eof))
	      ;; Wait a while for it to die before killing
	      ;; it off more rudely.  In XEmacs, accept-process-output
	      ;; or sit-for will run process sentinels if a process
	      ;; changes state.
	      ;; In Emacs I've no idea how to get the process sentinel
	      ;; to run outside the top-level loop.
	      ;; So put an ugly timeout and busy wait here instead
	      ;; of simply (accept-process-output nil 10).
	      (setq timeout-id
		    (add-timeout
		     proof-shell-quit-timeout
		     (lambda (&rest args)
		       (if (comint-check-proc (current-buffer))
			   (kill-process (get-buffer-process
					  (current-buffer))))
		       (throw 'exited t)) nil))
	      (while (comint-check-proc (current-buffer))
		;; Perhaps XEmacs hangs too, lets try both wait forms.
		(accept-process-output nil 1)
		(sit-for 1)))
	    ;; Disable timeout and sentinel in case one or
	    ;; other hasn't signalled yet, but we're here anyway.
	    (disable-timeout timeout-id)
	    ;; FIXME: this was added to fix 'No catch for exited tag'
	    ;; problem, but it's done later below anyway?
	    (set-process-sentinel proc nil)))
      (if (comint-check-proc (current-buffer))
	  (proof-debug
	   "Error in proof-shell-kill-function: process still lives!"))
      ;; For GNU Emacs, proc may be nil if killed already.
      (if proc (set-process-sentinel proc nil))
      ;; Restart all scripting buffers
      (proof-script-remove-all-spans-and-deactivate)
      ;; Clear state
      (proof-shell-clear-state)
      ;; Run hooks
      (run-hooks 'proof-shell-kill-function-hooks)
      ;; Remove auxiliary windows if they were being used, to
      ;; try to stop proliferation of frames (NB: this loses
      ;; currently, in case user has switched buffer in one of the
      ;; specially made frames)
      (if (and proof-multiple-frames-enable
	       proof-shell-fiddle-frames)
	  (proof-delete-other-frames))
      ;; Kill buffers associated with shell buffer
      (let ((proof-shell-buffer nil)) ;; fool kill buffer hooks
 	(dolist (buf '(proof-goals-buffer proof-response-buffer
					  proof-trace-buffer))
 	  (if (buffer-live-p (symbol-value buf))
 	      (progn
 		(kill-buffer (symbol-value buf))
 		(set buf nil)))))
      (message "%s exited." bufname))))

(defun proof-shell-clear-state ()
  "Clear internal state of proof shell."
  (setq proof-action-list nil
	proof-included-files-list nil
	proof-shell-busy nil
	proof-shell-proof-completed nil
	proof-nesting-depth 0
	proof-shell-error-or-interrupt-seen nil
	proof-shell-silent nil
	proof-shell-last-output nil
	proof-shell-last-output-kind nil
	proof-shell-last-prompt nil
	proof-shell-delayed-output nil
	proof-shell-delayed-output-kind nil))

(defun proof-shell-exit ()
  "Query the user and exit the proof process.

This simply kills the `proof-shell-buffer' relying on the hook function
`proof-shell-kill-function' to do the hard work."
  (interactive)
  (if (buffer-live-p proof-shell-buffer)
      (if (yes-or-no-p (format "Exit %s process? " proof-assistant))
	  (progn (kill-buffer proof-shell-buffer)
		 (setq proof-shell-buffer nil))
	(error "No proof shell buffer to kill!"))))

(defun proof-shell-bail-out (process event)
  "Value for the process sentinel for the proof assistant process.
If the proof assistant dies, run proof-shell-kill-function to
cleanup and remove the associated buffers.  The shell buffer is
left around so the user may discover what killed the process."
  (message "Process %s %s, shutting down scripting..." process event)
  (proof-shell-kill-function)
  (message "Process %s %s, shutting down scripting...done." process event))

(defun proof-shell-restart ()
  "Clear script buffers and send `proof-shell-restart-cmd'.
All locked regions are cleared and the active scripting buffer
deactivated.  

If the proof shell is busy, an interrupt is sent with
`proof-interrupt-process' and we wait until the process is ready.

The restart command should re-synchronize Proof General with the proof
assistant, without actually exiting and restarting the proof assistant
process.

It is up to the proof assistant how much context is cleared: for
example, theories already loaded may be \"cached\" in some way,
so that loading them the next time round only performs a re-linking
operation, not full re-processing.  (One way of caching is via
object files, used by Lego and Coq)."
  (interactive)
  (if proof-shell-busy
      (progn
	(proof-interrupt-process)
	(proof-shell-wait)))
  (if (not (proof-shell-live-buffer))
      (proof-shell-start) ;; start if not running
    ;; otherwise clear context
    (proof-script-remove-all-spans-and-deactivate)
    (proof-shell-clear-state)
    (if (and (buffer-live-p proof-shell-buffer)
	     proof-shell-restart-cmd)
	(proof-shell-invisible-command
	 proof-shell-restart-cmd))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Response buffer processing
;;

(defvar proof-shell-urgent-message-marker nil
  "Marker in proof shell buffer pointing to end of last urgent message.")

(defvar proof-shell-urgent-message-scanner nil
  "Marker in proof shell buffer pointing to scan start for urgent messages.")


(defun proof-shell-handle-output (start-regexp append-face)
  "Displays output from process in `proof-response-buffer'.
The output is taken from `proof-shell-last-output' and begins
the first match for START-REGEXP.

If START-REGEXP is nil or no match can be found (which can happen
if output has been garbled somehow), begin from the start of
the output for this command.

This is a subroutine of `proof-shell-handle-error'."
  (let (start end string)
    (with-current-buffer proof-shell-buffer
      
      ;; NB: it's tempting to use proof-shell-last-output here which
      ;; already contains the text (change suggested by Stefan
      ;; Monnier), but characters have been stripped from that text
      ;; that may be needed in our start-regexp parameter (e.g. Isabelle).

      (goto-char (point-max))
      (setq end (re-search-backward 
		 proof-shell-annotated-prompt-regexp))
      (goto-char (marker-position proof-marker))
      (setq start (point))

      (if (and start-regexp
	       (re-search-forward start-regexp nil t))
	  (setq start (- (point) (length (match-string 0)))))

      (setq string (buffer-substring-no-properties start end))

      ;; Erase if need be, and erase next time round too.
      (pg-response-maybe-erase t nil)
      (pg-response-display-with-face string append-face))))




(defsubst proof-shell-strip-output-markup (string &optional push)
  "Strip output markup from STRING.
Convenience function to call ` proof-shell-strip-output-markup'."
  (funcall proof-shell-strip-output-markup string))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; Processing error output
;;

(defvar proof-shell-no-error-display nil
  "If non-nil, do not display errors from the prover. 
An internal setting used in `proof-shell-invisible-cmd-get-result'.")

;; TODO: combine next two functions

(defun proof-shell-handle-error (cmd flags)
  "React on an error message triggered by the prover.
We first flush unprocessed goals to the goals buffer.
The error message is displayed in the response buffer.
Then we call `proof-shell-error-or-interrupt-action', which see."
  ;; [FIXME: Why not flush goals also for interrupts?]
  ;; Flush goals or response buffer (from some last successful proof step)
  (unless (memq 'no-error-display flags)
    (save-excursion
      (proof-shell-handle-delayed-output))
    (proof-shell-handle-output
     (if proof-shell-truncate-before-error proof-shell-error-regexp)
     'proof-error-face)
    (proof-display-and-keep-buffer proof-response-buffer)
    ;; NB: change here: we only call error action if flags allow
    (proof-shell-error-or-interrupt-action 'error)))

(defun proof-shell-handle-interrupt (flags)
   "React on an interrupt message from the prover.
Runs `proof-shell-error-or-interrupt-action'."
   (unless (memq 'no-error-display flags)
     (pg-response-maybe-erase t t t) ; force cleaned now & next
     (proof-shell-handle-output
      (if proof-shell-truncate-before-error proof-shell-interrupt-regexp)
      'proof-error-face)
     ;;  (proof-display-and-keep-buffer proof-response-buffer)
     (proof-warning 
      "Interrupt: script management may be in an inconsistent state
           (but it's probably okay)")
     (setq proof-shell-interrupt-pending nil)
     (proof-shell-error-or-interrupt-action 'interrupt)))

(defun proof-shell-error-or-interrupt-action (&optional err-or-int)
  "General action when an error or interrupt message appears from prover.

A subroutine for `proof-shell-handle-interrupt' and `proof-shell-handle-error'.

We sound a beep, clear queue spans and `proof-action-list', and set the flag
`proof-shell-error-or-interrupt-seen' to the ERR-OR-INT argument.
Then we call `proof-shell-handle-error-or-interrupt-hook'.

Commands which are not part of regular script management (with non-empty
flags) will not invoke this action."
  (save-excursion			;; for safety.
    (unless proof-shell-quiet-errors
      (beep))
    (proof-script-clear-queue-spans)

    ;; TODO: add temporary span for error message
    (setq proof-action-list nil)
    (proof-release-lock err-or-int)

    ;; Give a hint about C-c C-`.  NB: this is rather approximate,
    ;; we ought to check whether there is an error location in the
    ;; latest message, not just somewhere in the response buffer.
    (if (pg-response-has-error-location) 
	(pg-next-error-hint)))

    ;; Make sure that prover is outputting data now.
    ;; FIXME: put something here!
    (run-hooks 'proof-shell-handle-error-or-interrupt-hook))

(defun proof-goals-pos (span maparg)
  "Given a span, return the start of it if corresponds to a goal, nil otherwise."
  (and (eq 'goal (car (span-property span 'proof-top-element)))
       (span-start span)))

(defun proof-pbp-focus-on-first-goal ()
  "If the `proof-goals-buffer' contains goals, bring the first one into view.
This is a hook function for proof-shell-handle-delayed-output-hook."
  )
;; PG 4.0 FIXME
;       (let
;	   ((pos (map-extents 'proof-goals-pos proof-goals-buffer
;			      nil nil nil nil 'proof-top-element)))
;	 (and pos (set-window-point
;		   (get-buffer-window proof-goals-buffer t) pos)))))

           
(defsubst proof-shell-string-match-safe (regexp string)
  "Like string-match except returns nil if REGEXP is nil."
  (and regexp (string-match regexp string)))

      
(defun proof-shell-classify-output (cmd string)
  "Process shell output (resulting from CMD) by matching on STRING.
CMD is the first part of the `proof-action-list' that lead to this
output.  The result of this function is a pair (SYMBOL NEWSTRING).

Here is where we classify interrupts, abortions of proofs, errors,
completions of proofs, and proof step hints (proof by pointing results).
They are checked for in this order, using
 
  `proof-shell-interrupt-regexp'
  `proof-shell-error-regexp'
  `proof-shell-abort-goal-regexp'
  `proof-shell-proof-completed-regexp'
  `proof-shell-result-start'

All other output from the proof engine will be reported to the user in
the response buffer by setting `proof-shell-delayed-output' to a cons
cell of ('insert . TEXT) where TEXT is the text string to be inserted.

Order of testing is: interrupt, abort, error, completion.

To extend this function, set `proof-shell-classify-output-system-specific'.

The \"aborted\" case is intended for killing off an open proof during
retraction.  Typically it matches the message caused by a
`proof-kill-goal-command'.  It simply inserts the word \"Aborted\" into
the response buffer.  So it is expected to be the result of a 
retraction, rather than the indication that one should be made.

This function sets variables: `proof-shell-last-output', 
`proof-shell-last-output-kind', `proof-shell-proof-completed'."
  ;; Keep a record of the last message from the prover
  (setq proof-shell-last-output string)
  (or
   ;; First check for error, interrupt, abort, proof completed
   (cond
    ((proof-shell-string-match-safe proof-shell-interrupt-regexp string)
     (setq proof-shell-last-output-kind 'interrupt))
    
    ((proof-shell-string-match-safe proof-shell-error-regexp string)
     (setq proof-shell-last-output-kind 'error))
    
    ((proof-shell-string-match-safe proof-shell-abort-goal-regexp string)
     (proof-clean-buffer proof-goals-buffer)
     (setq proof-shell-last-output-kind 'abort))
    
    ((proof-shell-string-match-safe proof-shell-proof-completed-regexp string)
     ;; FIXME PG 4.0: want to remove side effects here
     ;;  In case no goals display
     ;;     (proof-clean-buffer proof-goals-buffer) 
     (setq proof-shell-last-output-kind 'goals) ;; PG 4.0: test
     ;; counter of commands since proof complete.
     (setq proof-shell-proof-completed 0)
     ;; But!  We carry on matching below for goals output, so that
     ;; provers may include proof completed message as part of 
     ;; goals message (Isabelle, HOL) or not (LEGO, Coq).
     nil))

   ;; Check for remaining things
   (cond
    ((proof-shell-string-match-safe proof-shell-start-goals-regexp string)
     (let ((start (match-end 0))
	   end)
       ;; Find the last goal string in the output
       (while (string-match proof-shell-start-goals-regexp string start)
	 (setq start (match-end 0)))
       ;; Convention: provers with special characters appearing in
       ;; proof-start-goals-regexp don't include the match in their 
       ;; goals output.  Others do.
       ;; (Improvement to examine proof-start-goals-regexp suggested
       ;;  for Coq by Robert Schneck because Coq has specials but
       ;;  doesn't markup goals output specially).
;; FIXME: try to remove this for PG 4.0
;;        (unless (and 
;; 		pg-subterm-first-special-char
;; 		(not (string-equal 
;; 		      proof-shell-start-goals-regexp
;; 		      (pg-assoc-strip-subterm-markup 
;; 		       proof-shell-start-goals-regexp))))
       (setq start (match-beginning 0))
       (setq end (if proof-shell-end-goals-regexp
		     (string-match proof-shell-end-goals-regexp string start)
		   (length string)))
       (setq proof-shell-last-output (substring string start end))
       (setq proof-shell-last-output-kind 'goals)))
    
    ;; Test for a proof by pointing command hint
    ((proof-shell-string-match-safe proof-shell-result-start string)
     (let (start end)
       (setq start (+ 1 (match-end 0)))
       (string-match proof-shell-result-end string)
       (setq end (- (match-beginning 0) 1))
       ;; Only record the loopback command in the last output message
       (setq proof-shell-last-output (substring string start end)))
     (setq proof-shell-last-output-kind 'loopback))
    
    ;; Hook to tailor proof-shell-classify-output to a specific proof
    ;; system, in the case that all the above matches fail.
    ((and proof-shell-classify-output-system-specific
	  (funcall (car proof-shell-classify-output-system-specific)
		   cmd string))
     (setq proof-shell-last-output-kind 'systemspecific)
     (funcall (cdr proof-shell-classify-output-system-specific)
	      cmd string))

    ;; Finally, any other output will appear as a response.
    (t 
     (setq proof-shell-last-output-kind 'response)))))


;;
;;   Low-level commands for shell communication
;;



;;;###autoload
(defun proof-shell-insert (string action)
  "Insert STRING at the end of the proof shell, call `comint-send-input'.

First call `proof-shell-insert-hook'.  The argument ACTION may be
examined by the hook to determine how to process the STRING variable.
NB: the hook is not called for the empty (null) string.

Then strip STRING of carriage returns before inserting it and updating
`proof-marker' to point to the end of the newly inserted text.

Do not use this function directly, or output will be lost.  It is only
used in `proof-append-alist' when we start processing a queue, and in
`proof-shell-exec-loop', to process the next item."
  (with-current-buffer proof-shell-buffer
    (goto-char (point-max))
    
    ;; Hook for munging `string' and other hacks.  
    (unless (null string)
      (run-hooks 'proof-shell-insert-hook))

    ;; Replace CRs from string with spaces to avoid spurious prompts.
    (if proof-shell-strip-crs-from-input
	(setq string (subst-char-in-string ?\n ?\  string)))
    
    (insert (or string ""))  ;; robust against call with nil

    ;; Advance the proof-marker, if synchronization has been gained.
    ;; Null marker => no yet synced; output is ignored.
    (unless (null (marker-position proof-marker))
      (set-marker proof-marker (point)))

    ;; FIXME da: this space fudge is actually a visible hack:
    ;; the response string begins with a space and a newline.
    ;; It was needed to work around differences in Emacs versions.
    ;; PG 4.0: consider alternative of maintaining marker at 
    ;; position -1
    (insert " ")

    ;; Note: comint-send-input perversely calls the output filter
    ;; functions on the input, sigh.  This can mess up PGIP processing
    ;; since we try to re-interpret an XML message which has been
    ;; string-escaped, etc, etc.  We prevent this by disabling the
    ;; output filter functions when calling the input function.
    (let ((comint-output-filter-functions nil))
      (comint-send-input))

    (setq proof-shell-expecting-output t)))


;; ============================================================
;;
;; Code for manipulating proof queue
;;


(defun proof-shell-action-list-item (cmd callback &optional flags)
  "Return action list entry run CMD with callback CALLBACK and FLAGS.
The queue entry does not refer to a span in the script buffer."
  (append (list nil cmd callback) flags))


(defun proof-shell-set-silent (span)
  "Callback for `proof-shell-start-silent'.
Very simple function but it's important to give it a name to help
track what happens in the proof queue."
  (setq proof-shell-silent t))

(defun proof-shell-start-silent-item ()
  "Return proof queue entry for starting silent mode."
  (proof-shell-action-list-item
   proof-shell-start-silent-cmd
   'proof-shell-set-silent))

(defun proof-shell-clear-silent (span)
  "Callback for `proof-shell-stop-silent'.
Very simple function but it's important to give it a name to help
track what happens in the proof queue."
  (setq proof-shell-silent nil))

(defun proof-shell-stop-silent-item ()
  "Return proof queue entry for stopping silent mode."
  (proof-shell-action-list-item
   proof-shell-stop-silent-cmd
   'proof-shell-clear-silent))

;; FIXME: could be macro for efficiency improvement in avoiding calculating num
(defun proof-shell-should-be-silent (num)
  "Return non-nil if we must switch to silent mode, adding NUM entries to queue."
  (if (and (not proof-full-annotation)
	   proof-shell-start-silent-cmd)
      (or proof-shell-silent	; already
	  ;; NB: there is some question here over counting the
	  ;; proof-action-list, since it could itself contain
	  ;; silent-on/off commands which should be ignored for
	  ;; counting, really... also makes cutting lists for advanced
	  ;; queue processing more tricky.
	  (>= (+ num (length proof-action-list))
	     proof-shell-silent-threshold))))
	      

(defsubst proof-shell-invoke-callback (listitem)
  "From a `proof-action-list' entry, invoke the callback on the span."
  (funcall (nth 2 listitem) (car listitem)))

(defun proof-append-alist (alist &optional queuemode)
  "Chop off the vacuous prefix of the command queue ALIST and queue it.
For each `proof-no-command' item at the head of the list, invoke its 
callback and remove it from the list.

Append the result onto `proof-action-list', and if the proof 
shell isn't already busy, grab the lock with QUEUEMODE and
start processing the queue.

If the proof shell is busy when this function is called,
then QUEUEMODE must match the mode of the queue currently
being processed."
  (let (item)
    ;; NB: wrong time for callbacks for no-op commands, if queue non-empty.
    (while (and alist (string= 
		       (nth 1 (setq item (car alist))) 
		       proof-no-command))
      (proof-shell-invoke-callback item)
      (setq alist (cdr alist)))
    (if (and (null alist) (null proof-action-list))
	;; remove the queue (otherwise done in proof-shell-exec-loop)
	(proof-detach-queue))
	
    (if alist
	(if proof-action-list
	    (progn
	      ;; internal check: correct queuemode in force if busy
	      ;; (should have proof-action-list<>nil -> busy)
	      (and proof-shell-busy queuemode
		   (unless (eq proof-shell-busy queuemode)
		     (proof-debug "proof-append-alist: wrong queuemode detected for busy shell")
		     (assert (eq proof-shell-busy queuemode))))
	      ;; See if we should make prover quieten down
	      (if (proof-shell-should-be-silent (length alist))
		;; Make it ASAP, which is just after the current
		;; command (head of queue).
		  (setq proof-action-list
			(cons (car proof-action-list)
			      (cons (proof-shell-start-silent-item)
				     (cdr proof-action-list)))))
	      ;; append to the current queue
	      (setq proof-action-list
		    (nconc proof-action-list alist)))
	  ;; start processing a new queue
	  (progn
	    (proof-grab-lock queuemode)
	    (setq proof-shell-last-output-kind nil)
	    (if (proof-shell-should-be-silent (length alist))
		;; 
		(progn
		  (setq proof-action-list 
			(list (proof-shell-start-silent-item)))
		  (setq item (car proof-action-list))))
	    (setq proof-action-list
		  (nconc proof-action-list alist))
	    ;; Really start things going here
	    (proof-shell-insert (nth 1 item) (nth 2 item)))))))

;;;###autoload    
(defun proof-start-queue (start end alist)
  "Begin processing a queue of commands in ALIST.
If START is non-nil, START and END are buffer positions in the
active scripting buffer for the queue region.

This function calls `proof-append-alist'."
  (if start
      (proof-set-queue-endpoints start end))
  (proof-append-alist alist))

;;;###autoload
(defun proof-extend-queue (end alist)
  "Extend the current queue with commands in ALIST, queue end END.
To make sense, the commands should correspond to processing actions
for processing a region from (buffer-queue-or-locked-end) to END.
The queue mode is set to 'advancing"
  (proof-set-queue-endpoints (proof-unprocessed-begin) end)
  (proof-append-alist alist 'advancing))


(defun proof-shell-exec-loop () 
  "Process the `proof-action-list'.

`proof-action-list' contains a list of (SPAN COMMAND ACTION [FLAGS]) lists.

If this function is called with a non-empty proof-action-list, the
head of the list is the previously executed command which succeeded.
We execute (ACTION SPAN) on the first item, then (ACTION SPAN) on any
following items which have `proof-no-command' as their cmd components.

If a there is a next command after that, send it to the process.  

If the action list becomes empty, unlock the process and remove
the queue region.

The return value is non-nil if the action list is now empty."

  (or 
   (null proof-action-list)
   (save-excursion
     (if proof-script-buffer		      ; switch to active script
	 (set-buffer proof-script-buffer)) 
     
     (let ((item  (car proof-action-list))
	   (flags (nthcdr 3 (car proof-action-list))))
       
       ;; invoke callback on just processed command
       (proof-shell-invoke-callback item)
       (setq proof-action-list (cdr proof-action-list))

       ;; slurp comments without sending to prover
       (while (and proof-action-list
		   (string= 
		    (nth 1 (setq item (car proof-action-list))) 
		    proof-no-command))
	 (proo-shell-invoke-callback item)
	 (setq proof-action-list (cdr proof-action-list)))

       ;; if action list is (nearly) empty, ensure prover is noisy.
       ;; FIXME: chance to loose output if we processed a bunch of o/p 
       ;; ending with a series of comments!
       (if (and proof-shell-silent
		(or (null proof-action-list)
		    (null (cdr proof-action-list))))
	   (progn
	     ;; Insert the quieten command on head of queue
	     (setq proof-action-list
		   (cons (proof-shell-stop-silent-item)
			 proof-action-list))
	     (setq item (car proof-action-list))))
       
       ;; deal with pending interrupts (which were sent but caused no prover error)
       (if proof-shell-interrupt-pending
	   (progn
	     (proof-debug "Processed pending interrupt")
	     (proof-shell-handle-interrupt flags)))

       (if proof-action-list
	   ;; send the next command to the process.
	   (proof-shell-insert (nth 1 item) (nth 2 item))
	 
	 ;; action list is empty, release lock and cleanup
	 (proof-release-lock)
	 (proof-detach-queue)
	 (unless flags ; hint after a batch of scripting
	   (pg-processing-complete-hint))
	 (pg-finish-tracing-display))
       
       (null proof-action-list)))))


(defun proof-shell-insert-loopback-cmd  (cmd)
  "Insert command sequence sent from prover into script buffer.
String is inserted at the end of locked region, after a newline 
and indentation.  Assumes proof-script-buffer is active."
  (unless (string-match "^\\s-*$" cmd)	; FIXME: assumes cmd is single line
    (with-current-buffer proof-script-buffer
      (let (span)
	(proof-goto-end-of-locked)
	(let ((proof-one-command-per-line t)) ; because pbp several commands
	  (proof-script-new-command-advance))
	(insert cmd)
	;; Fix 16.11.99.  Comment in todo suggested old code below
	;; assumed the pbp command would succeed, but it seems fine?
	;; But this action belongs in the proof script code.
	;; NB: difference between ordinary commands and pbp is that
	;; pbp can return *several* commands, that are treated as 
	;; a unit, i.e. sent to the proof assistant together.
	;; FIXME da: this seems very similar to proof-insert-pbp-command
	;; in proof-script.el.  Should be unified, I suspect.
	(setq span (span-make (proof-locked-end) (point)))
	(span-set-property span 'type 'pbp)
	(span-set-property span 'cmd cmd)
	(proof-set-queue-endpoints (proof-locked-end) (point))
	(setq proof-action-list 
	      (cons (car proof-action-list) 
		    (cons (list span cmd 'proof-done-advancing)
			  (cdr proof-action-list))))))))

(defun proof-shell-message (str)
  "Output STR in minibuffer."
  (message "%s" ;; to escape format characters
	   (concat "[" proof-assistant "] " 
		   ;; TODO: rather than stripping, could try fontifying
		   (proof-shell-strip-output-markup str))))

(defun proof-shell-process-urgent-message (message)
  "Analyse urgent MESSAGE for various cases.
Cases are: included file, retracted file, cleared response buffer, 
variable setting or dependency list. 
If none of these apply, display MESSAGE.

MESSAGE should be a string annotated with 
`proof-shell-eager-annotation-start', `proof-shell-eager-annotation-end'."
    (cond
     ;; CASE tracing output: use tracing buffer
     ((and proof-shell-trace-output-regexp
	   (string-match proof-shell-trace-output-regexp message))
      (proof-trace-buffer-display 
;; FIXME: remove for PG 4.0
;;       (if (or pg-use-specials-for-fontify
;;	       proof-shell-unicode)
	   message
;;	 (pg-assoc-strip-subterm-markup message))
	   )
      (unless (and proof-trace-output-slow-catchup
		   (pg-tracing-tight-loop))
	(proof-display-and-keep-buffer proof-trace-buffer))
      ;; If user quits during tracing output, send an interrupt
      ;; to the prover.  Helps when Emacs is "choking".
      (if (and quit-flag proof-action-list)
	  (proof-interrupt-process)))

       
     ;; CASE processing file: update known files list
     ((and proof-shell-process-file 
	   (string-match (car proof-shell-process-file) message))
      (let
	  ((file (funcall (cdr proof-shell-process-file) message)))
	(if (and file (not (string= file "")))
	    (proof-register-possibly-new-processed-file file))))

     ;; CASE retract: the prover is retracting across files
     ((and proof-shell-retract-files-regexp
	   (string-match proof-shell-retract-files-regexp message))
      (let ((current-included proof-included-files-list))
	(setq proof-included-files-list
	      (funcall proof-shell-compute-new-files-list message))
	(let
	    ;; Previously active scripting buffer
	    ((scrbuf proof-script-buffer))
	  ;; NB: we assume that no new buffers are *added* by
	  ;; the proof-shell-compute-new-files-list 
	  (proof-restart-buffers
	   (proof-files-to-buffers
	  (set-difference current-included
			  proof-included-files-list)))
	  (cond
	   ;; Do nothing if there was no active scripting buffer
	   ((not scrbuf))
	   ;; Do nothing if active buffer hasn't changed (may be nuked)
	   ((eq scrbuf proof-script-buffer))
	   ;; Otherwise, active scripting buffer has been retracted.
	   (t
	    (setq proof-script-buffer nil))))))
     
     ;; CASE clear response: prover asks PG to clear response buffer
     ((and proof-shell-clear-response-regexp
	   (string-match proof-shell-clear-response-regexp message))
      (pg-response-maybe-erase nil t t))
     
     ;; CASE clear goals: prover asks PG to clear goals buffer
     ((and proof-shell-clear-goals-regexp
	   (string-match proof-shell-clear-goals-regexp message))
      (proof-clean-buffer proof-goals-buffer))
   
     ;; CASE variable setting: prover asks PG to set some variable 
     ((and proof-shell-set-elisp-variable-regexp
	   (string-match proof-shell-set-elisp-variable-regexp message))
      (let 
	  ((variable   (match-string 1 message))
	   (expr       (match-string 2 message)))
	(condition-case nil
	    (with-temp-buffer
	      (insert expr) ; massive risk from malicious provers!!
	      (set (intern variable) (eval-last-sexp t)))
	  (t (proof-debug 
	      (concat
	       "lisp error when obeying proof-shell-set-elisp-variable: \n"
	       "setting `" variable "'\n to: \n"
	       expr "\n"))))))
     
     ;; CASE PGIP message from proof assistant.
     ((and proof-shell-match-pgip-cmd
	   (string-match proof-shell-match-pgip-cmd message))
      (require 'pg-xml)
      (require 'pg-pgip)
      (unless (string-match (match-string 0 message)
			    proof-shell-eager-annotation-start)
	;; Assume that eager annotation regexps are _not_ part of PGIP
	(setq message (proof-shell-strip-eager-annotations message)))
      (let
	  ((parsed-pgip  (pg-xml-parse-string message)))
	(pg-pgip-process-packet parsed-pgip)))
     
     ;; CASE theorem dependency: prover lists thms used in last proof
     ((and proof-shell-theorem-dependency-list-regexp 
	   (string-match proof-shell-theorem-dependency-list-regexp message))
      (let ((names   (match-string 1 message))
	    (deps    (match-string 2 message)))
	(setq proof-last-theorem-dependencies 
	      (cons 
	       (split-string names 
			     proof-shell-theorem-dependency-list-split)
	       (split-string deps  
			     proof-shell-theorem-dependency-list-split)))))

	   
     (t
      ;; CASE everything else.  We're about to display a message.  
      ;; Clear the response buffer this time, but not next, leave window.
      (pg-response-maybe-erase nil nil)
;; FIXME: remove for PG 4.0
;;      (let ((stripped (if proof-shell-unicode 
;;			  (proof-shell-strip-eager-annotations message)
;;			(pg-remove-specials-in-string
;;			 (pg-assoc-strip-subterm-markup message)))))
	;; Display first chunk of output in minibuffer.
	;; Maybe this should be configurable, it can get noisy.
	(proof-shell-message 
	 (substring message 0 (or (string-match "\n" message)
				   (min (length message) 75))))
	(pg-response-display-with-face 
	 (proof-shell-strip-eager-annotations message)
	 'proof-eager-annotation-face))))

(defun proof-shell-strip-eager-annotations (string)
  "Strip `proof-shell-eager-annotation-{start,end}' from STRING."
  (save-match-data
   (substring 
    string
    (if (string-match proof-shell-eager-annotation-start string)
	(match-end 0) 0)
    (if (string-match proof-shell-eager-annotation-end string)
	(match-beginning 0)))))


(defvar proof-shell-minibuffer-urgent-interactive-input-history nil)

(defun proof-shell-minibuffer-urgent-interactive-input (msg)
  "Issue MSG as a prompt and receive user input."
  (let ((input
	 (ignore-errors
	   (read-string msg nil 
	    'proof-shell-minibuffer-urgent-interactive-input-history))))
    ;; Always send something, even if read-input was errorful
    (proof-shell-insert (or input "") 'interactive-input)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; The proof shell process filter
;;


;; NOTE da: proof-shell-filter does *not* update the proof-marker,
;; that's done in proof-shell-insert.  Previous docstring below was
;; wrong.  The one case where this function updates proof-marker is
;; the first time through the loop to synchronize.
(defun proof-shell-filter (str)
  "Filter for the proof assistant shell-process.
A function for `comint-output-filter-functions'.

Deal with output and issue new input from the queue.

Handle urgent messages first.  As many as possible are processed,
using the function `proof-shell-process-urgent-messages'.

Otherwise wait until an annotated prompt appears in the input.  
If `proof-shell-wakeup-char' is set, wait until we see that in the
output chunk STR.  This optimizes the filter a little bit.

If a prompt is seen, run `proof-shell-classify-output' on the output
between the new prompt and the last input (position of `proof-marker')
or the last urgent message (position of
`proof-shell-urgent-message-marker'), whichever is later.
For example, in this case:

 PROMPT> INPUT
 OUTPUT-1
 URGENT-MESSAGE
 OUTPUT-2
 PROMPT>

`proof-marker' is set after INPUT by `proof-shell-insert' and
`proof-shell-urgent-message-marker' is set after URGENT-MESSAGE.
Only OUTPUT-2 will be processed.  For this reason, error
messages and interrupt messages should *not* be considered
urgent messages.

Output is processed using the function
`proof-shell-filter-manage-output'.

The first time that a prompt is seen, `proof-marker' is
initialised to the end of the prompt.  This should
correspond with initializing the process.  The 
ordinary output before the first prompt is ignored (urgent messages, 
however, are always processed; hence their name)."

  (save-excursion
    ;; Strip CRs.
    (if proof-shell-strip-crs-from-output
	(progn
	  (setq str (replace-regexp-in-string "\r+$" "" str))
	  ;; Do the same thing in the buffer via comint's function
	  ;; (sometimes put on comint-output-filter-functions too).
	  (comint-strip-ctrl-m)))

    ;; Process urgent messages.
    (and proof-shell-eager-annotation-start
	 (proof-shell-process-urgent-messages))

    ;; FIXME da: some optimization possible here by customizing filter
    ;; according to whether proof-shell-wakeup-char, etc, are non-nil.
    ;; Could make proof-shell-filter into a macro to do this.
    ;; On the other hand: it's not clear that wakeup-char is really
    ;; needed, as matching the prompt may be efficient enough anyway.

    (if ;; Some proof systems can be hacked to have annotated prompts;
	;; for these we set proof-shell-wakeup-char to the annotation 
	;; special, and look for it in the output before doing anything.
	(if proof-shell-wakeup-char
	    ;; NB: this match doesn't work in emacs-mule, darn.
	    ;; (string-match (char-to-string proof-shell-wakeup-char) str))
	    ;; NB: this match doesn't work in GNU Emacs 20.5, darn.
	    ;; (find proof-shell-wakeup-char str)
	    ;; So let's use both tests!
	    (or
	     (string-match (char-to-string proof-shell-wakeup-char) str)
	     (find proof-shell-wakeup-char str))
	  ;; Others systems rely on a standard top-level (e.g. SML) whose
	  ;; prompts may be difficult or impossible to hack.
	  ;; For those we must search in the buffer for the prompt.
	  t)
	(if (null (marker-position proof-marker))
	    ;; Initialisation of proof-marker:
	    ;; Set marker to after the first prompt in the
	    ;; output buffer if one can be found now.
	    ;; NB: ideally, we'd rather do this initialization outside
	    ;; of the filter function for slightly better efficiency.  
	    ;; Could be achieved by switching between filter functions.
	    (progn
	      (goto-char (point-min))
	      (if (re-search-forward proof-shell-annotated-prompt-regexp nil t)
		  (progn
		    (set-marker proof-marker (point))
		    ;; The first time a prompt is seen we ignore any 
		    ;; output that occured before it, assuming that
		    ;; corresponds to uninteresting startup messages. 
		    ;; We process the
		    ;; action list to remove the first item if need
		    ;; be (proof-shell-init-cmd sent if 
		    ;; proof-shell-config-done).
		    (if proof-action-list
			(proof-shell-filter-manage-output "")))))
	  ;; Now we're looking for the end of the piece of output
	  ;; which will be processed.  
	  
	  ;; Note that the way this filter works, only one piece of
	  ;; output can be dealt with at a time so we loose sync if
	  ;; there's more than one bit there.
	  
	  (if proof-action-list
	      ;; We were expecting some output, examine it.
	      (let ((urgnt    (marker-position 
			       proof-shell-urgent-message-marker))
		    string startpos prev-prompt)

		;; Ignore any urgent messages that have already been
		;; dealt with.  This loses in the case mentioned
		;; above.  A more general way of doing this would be
		;; to filter out or delete the urgent messages which
		;; have been processed already.
		(setq prev-prompt (goto-char (marker-position proof-marker)))
		(setq startpos prev-prompt) 
		(if (and urgnt
			 (< startpos urgnt))
		    (setq startpos (goto-char urgnt))
		  ;; Otherwise, skip possibly a (fudge) space and new line
		  (if (eq (char-after startpos) ?\ )
		      (setq startpos (goto-char (+ 2 startpos)))
		    (setq startpos (goto-char (1+ startpos)))))
		;; Find next prompt.  
		(if (re-search-forward 
		     proof-shell-annotated-prompt-regexp nil t)
		    (progn
		      (setq proof-shell-last-prompt
			    (buffer-substring-no-properties
			     (match-beginning 0) (match-end 0)))
		      (backward-char (- (match-end 0) (match-beginning 0)))
		      (setq string (buffer-substring-no-properties
				    startpos (point)))
		      (goto-char (point-max))
		      (setq proof-shell-expecting-output nil)
		      ;; Process output string.
		      (proof-shell-filter-manage-output string)
		      ;; Cleanup shell buffer 
		      (unless proof-general-debug
			(pg-remove-specials prev-prompt (point-max)))
		      )))
	    (if proof-shell-busy
		;; internal error recovery:
		(progn
		  (proof-debug 
		   "proof-shell-filter found empty action list yet proof shell busy.")
		  (proof-release-lock))))))))

(defun proof-shell-process-urgent-messages ()
  "Scan the shell buffer for urgent messages.
Scanning starts from `proof-shell-urgent-message-scanner' or 
`comint-last-input-end', which ever is later.  We deal with strings
between regexps eager-annotation-start and eager-annotation-end.

Note that we must search the buffer rather than the chunk of output
being filtered process because we have no guarantees about where
chunks are broken: it may be in the middle of an annotation.

This is a subroutine of `proof-shell-filter'."
  (let ((pt (point)) (end t) lastend 
	(start (max (marker-position proof-shell-urgent-message-scanner)
		    (marker-position comint-last-input-end))))
    (goto-char start)
    (while (and end
		(re-search-forward proof-shell-eager-annotation-start 
				   nil 'end))
      (setq start (match-beginning 0))
      (if (setq end
		(re-search-forward proof-shell-eager-annotation-end nil t))

	  ;; Process the text including annotations (stripped if specials)
	  (save-excursion
	    (setq lastend end)
	    (proof-shell-process-urgent-message
	     (buffer-substring start end)))))

    ;; Set the marker to the (character after) the end of the last
    ;; message found, if any.  Must take care to keep the marker
    ;; behind the process marker otherwise no output is seen!
    ;; (insert-before-markers in comint)
    (if lastend
	(set-marker
	 proof-shell-urgent-message-marker
	 (min lastend
	      (1- (process-mark (get-buffer-process (current-buffer)))))))
    ;; Now an optimization to avoid searching the same bit of text
    ;; over and over.  But it requires that we know the maximum
    ;; possible length of an annotation to avoid missing them.
    (if end
	;; If the search for the starting annotation was unsuccessful,
	;; set the scanner marker to the limit of the last search for
	;; the starting annotation, less the maximal length of the
	;; annotation.  
	(set-marker
	 proof-shell-urgent-message-scanner
	 (min
	  ;; NB: possible fix here not included: a test to be sure we
	  ;; don't go back before the start of the command!  This
	  ;; fixes a minor problem which is possible duplication
	  ;; of urgent messages which are less than
	  ;; proof-shell-eager-annotation-start-length characters.
	  ;; But if proof-general is configured properly, there
	  ;; should never be any such messages!
	  ;; (max
	  ;;  (marker-position proof-marker)
	      (- (point) (1+ proof-shell-eager-annotation-start-length))
	  (1- (process-mark (get-buffer-process (current-buffer))))))
      ;; Otherwise, the search for the ending annotation was
      ;; unsuccessful, so we set the scanner marker to the start of
      ;; the annotation found.
      (set-marker
       proof-shell-urgent-message-scanner
       (min
	start
	(1- (process-mark (get-buffer-process (current-buffer)))))))
    (goto-char pt)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Despatching output
;;


(defun proof-shell-filter-manage-output (string)
  "Subroutine of `proof-shell-filter' to process output STRING.

Appropriate action is taken depending on what
`proof-shell-classify-output' returns: maybe handle an interrupt, an
error, or deal with ordinary output which is a candidate for the goal
or response buffer.  

Ordinary output is only displayed when the proof action list
becomes empty, to avoid a confusing rapidly changing output.

After processing the current output, the last step undertaken
by the filter is to send the next command from the queue."
  (let ((cmd   (nth 1 (car proof-action-list)))
	(flags (nthcdr 3 (car proof-action-list))))

    (proof-shell-classify-output cmd string)

    (cond
     ((eq proof-shell-last-output-kind 'error)
      (proof-shell-handle-error cmd flags))
     ((eq proof-shell-last-output-kind 'interrupt)
      (proof-shell-handle-interrupt flags))
     ((eq proof-shell-last-output-kind 'loopback)
      (proof-shell-insert-loopback-cmd proof-shell-last-output)
      (proof-shell-exec-loop))

     ;; Otherwise, delay handling ordinary script functions: don't act
     ;; unless all the commands the queue region have been processed.
     (t 
      (setq proof-shell-delayed-output-kind proof-shell-last-output-kind)
      (setq proof-shell-delayed-output proof-shell-last-output)
      (setq proof-shell-delayed-flags flags)
      (if (proof-shell-exec-loop)
	  (proof-shell-handle-delayed-output))))))


(defun proof-shell-handle-delayed-output ()
  "Display delayed output.
This function handles the cases of `proof-shell-delayed-output-kind' which
are not dealt with eagerly during script processing, namely
'abort, 'response, 'goals outputs.
This is useful even with empty delayed output, since it clears buffers."
  (cond
   ;; Response buffer output
   ((eq proof-shell-delayed-output-kind 'abort)
    (unless (memq 'no-error-display proof-shell-delayed-flags)
      (pg-response-display proof-shell-delayed-output)))
   ((eq proof-shell-delayed-output-kind 'response)
    (unless (memq 'no-response-display proof-shell-delayed-flags))
      (pg-response-display proof-shell-delayed-output))
   ;; Goals buffer output
   ((eq proof-shell-delayed-output-kind 'goals)
    (unless (memq 'no-goals-display proof-shell-delayed-flags)
      (pg-goals-display proof-shell-delayed-output)))
   ;; Ignore other cases
   )
  (run-hooks 'proof-shell-handle-delayed-output-hook))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Interrupt
;;

(defvar proof-shell-expecting-output nil
  "A flag indicating some input has been sent and we're expecting output.
This is used when processing interrupts.")

(defvar proof-shell-interrupt-pending nil
  "A flag indicating an interrupt is pending.
This ensures that the proof queue will be interrupted even if no
interrupt message is printed from the prover after the last output.")


(defun proof-interrupt-process ()
  "Interrupt the proof assistant.  Warning! This may confuse Proof General.

This sends an interrupt signal to the proof assistant, if Proof General
thinks it is busy.  

This command is risky because we don't know whether the last command 
succeeded or not.  The assumption is that it didn't, which should be true 
most of the time, and all of the time if the proof assistant has a careful
handling of interrupt signals.

Some provers may ignore (and lose) interrupt signals, or fail to indicate
that they have been acted upon but get stop in the middle of output.  
In the first case, PG will terminate the queue of commands at the first 
available point.  In the second case, you may need to press enter inside
the prover command buffer (e.g., with Isabelle2009 press RET inside *isabelle*)."
  (interactive)
  (unless (proof-shell-live-buffer)
      (error "Proof Process Not Started!"))
  (unless proof-shell-busy
    (error "Proof Process Not Active!"))
  (with-current-buffer proof-shell-buffer
    (if proof-shell-expecting-output
	(progn 
	  (setq proof-shell-interrupt-pending t) ; interrupt even if no interrupt message
	  (interrupt-process nil comint-ptyp))
      ;; otherwise, interrupt the queue right here
      (proof-shell-error-or-interrupt-action 'interrupt))))
      



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tracing catch-up: prevent Emacs-consumes-all-CPU-fontifying phenomenon
;;

;; FIXME: not quite finished:
;; -- need some way of coming out of tracing slow mode in case
;;   tracing output has ended
;; -- need to fontify remaining portion of buffer in case
;;   tracing output has ended when in slow mode (and refresh
;;   final display)  
;; -- shouldn't be trigger for only a small amount of output 
;;   (e.g. output from blast).  Or a count of number of succesive
;;   bursts?

(defvar pg-last-tracing-output-time nil
  "Time of last tracing output, as recorded by (current-time).")

(defconst pg-slow-mode-duration 2
  "Maximum duration of slow mode in seconds.")

(defconst pg-fast-tracing-mode-threshold 50000
  "Minimum microsecond delay between tracing outputs that triggers slow mode.")

(defvar pg-tracing-cleanup-timer nil)

(defun pg-tracing-tight-loop ()
  "Return non-nil in case it seems like prover is dumping a lot of output.
This is a performance hack to avoid Emacs consuming CPU when prover is output
tracing information.
Only works when system timer has microsecond count available."
  (let ((tm (current-time)))
    (if pg-tracing-slow-mode
	(if (eq (nth 0 pg-last-tracing-output-time) (nth 0 tm))
	    ;; see if seconds has changed by at least pg-slow-mode-duration
	    (if (> (- (nth 1 tm) (nth 1 pg-last-tracing-output-time)) 
		   pg-slow-mode-duration)
		;; go out of slow mode
		(progn 
		  (setq pg-tracing-slow-mode nil)
		  (setq pg-last-tracing-output-time tm)
		  (cancel-timer pg-tracing-cleanup-timer))
	      ;; otherwise: stay in slow mode
	      t)
	  ;; different seconds-major count: go out of slow mode
	  (progn 
	    (setq pg-last-tracing-output-time tm)
	    (setq pg-tracing-slow-mode nil)))
      ;; ordinary mode: examine difference since last output
      (if
	  (and pg-last-tracing-output-time 
	       (eq (nth 0 tm) (nth 0 pg-last-tracing-output-time))
	       (eq (nth 1 tm) (nth 1 pg-last-tracing-output-time))
	       ;; Same second: examine microsecond
	       (> (nth 2 tm) 0) ;; some systems always have zero count
	       ;; 
	       (< (- (nth 2 tm) (nth 2 pg-last-tracing-output-time)) 
		  pg-fast-tracing-mode-threshold))
	  ;; quickly consecutive and large tracing outputs: go into slow mode
	  (progn
	    (setq pg-tracing-slow-mode t)
	    (pg-slow-fontify-tracing-hint)
	    (setq pg-tracing-cleanup-timer
		  (run-with-idle-timer 2 nil 'pg-finish-tracing-display))
	    t)
	;; not quick enough to trigger slow mode: allow screen update
	(setq pg-last-tracing-output-time tm)
	nil))))

(defun pg-finish-tracing-display ()
  "Cancel tracing slow mode and ensure tracing buffer is fontified."
  (if pg-tracing-slow-mode
      (progn
	(setq pg-tracing-slow-mode nil)
	(proof-trace-buffer-finish))))







  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; proof-shell-invisible-command: for user-level commands.
;;

;;;###autoload
(defun proof-shell-wait ()
  "Busy wait for `proof-shell-busy' to become nil.
Needed between sequences of commands to maintain synchronization,
because Proof General does not allow for the action list to be extended
in some cases.   May be called by `proof-shell-invisible-command'."
  (let ((proverproc (get-buffer-process proof-shell-buffer)))
    (if proverproc ;; in case no prover process, just return (shouldn't happen)
	(progn
	  (sit-for 0) ;; ensure display up-to-date
	  (while (and proof-shell-busy (not quit-flag))
	    ;; We call both sit-for and accept-process-output, since
	    ;; they have different behaviours in GNU Emacs/XEmacs.
	    (accept-process-output proverproc 1)
	    (sit-for 1))
	  (if quit-flag
	      ;; This *shouldn't* really happen, but lockups in this 
	      ;; function have been seen in some odd scenarios.
	      (error "Proof General: Quit in proof-shell-wait"))))))

(defun proof-done-invisible (span)
  "Callback for proof-shell-invisible-command.  
Calls proof-state-change-hook."
  (run-hooks 'proof-state-change-hook))

;;;###autoload
(defun proof-shell-invisible-command (cmd &optional wait invisiblecallback 
					  &rest flags)
  "Send CMD to the proof process.
The CMD is `invisible' in the sense that it is not recorded in buffer.
CMD may be a string or a string-yielding expression.

Automatically add proof-terminal-char if necessary, examining
`proof-shell-no-auto-terminate-commands'.

By default, let the command be processed asynchronously.
But if optional WAIT command is non-nil, wait for processing to finish
before and after sending the command.

In case CMD is (or yields) nil, do nothing.

INVISIBLECALLBACK will be invoked after the command has finished,
if it is set.  It should probably run the hook variables 
`proof-state-change-hook'.

If NOERROR is set, surpress usual error action."
  (unless (stringp cmd)
    (setq cmd (eval cmd)))
  (if cmd
      (progn
	(unless (or (null proof-terminal-char)
		    (not proof-shell-auto-terminate-commands)
		    (string-match (concat
				   (regexp-quote
				    (char-to-string proof-terminal-char))
				   "[ \t]*$") cmd))
	  (setq cmd (concat cmd (char-to-string proof-terminal-char))))
	(if wait (proof-shell-wait))
	(proof-shell-ready-prover)  ; start proof assistant; set vars.
	(let* ((callback
		(if invisiblecallback 
		    (lexical-let ((icb invisiblecallback))
		      (lambda (span)
			(funcall icb span)))
		  'proof-done-invisible)))
	  (proof-start-queue nil nil
			     (list (proof-shell-action-list-item 
				    cmd 
				    callback
				    flags))))
	(if wait (proof-shell-wait)))))

;;;###autoload
(defun proof-shell-invisible-cmd-get-result (cmd)
  "Execute CMD and return result as a string.
This expects CMD to result in some theorem prover output.
Ordinary output (and error handling) is disabled, and the result
\(contents of `proof-shell-last-output') is returned as a string."
  (proof-shell-invisible-command cmd 'waitforit
				 nil
				 'no-response-display
				 'no-error-display)
  proof-shell-last-output)

;;;###autoload
(defun proof-shell-invisible-command-invisible-result (cmd)
  "Execute CMD for side effect in the theorem prover, waiting before and after.
Error messages are displayed as usual."
  (proof-shell-invisible-command cmd 'waitforit
				 nil
				 'no-response-display))
  





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Proof General shell mode definition
;;

;(eval-and-compile			; to define vars
;;;###autoload
(define-derived-mode proof-shell-mode comint-mode 
  "proof-shell" "Proof General shell mode class for proof assistant processes"

  (setq proof-buffer-type 'shell)
  
  ;; Clear state
  (proof-shell-clear-state)

  ;; Efficiency: don't keep undo history
  (buffer-disable-undo)

  ;; comint customisation. comint-prompt-regexp is used by
  ;; comint-get-old-input, comint-skip-prompt, comint-bol, backward
  ;; matching input, etc.  
  (if proof-shell-prompt-pattern
      (setq comint-prompt-regexp proof-shell-prompt-pattern))

  ;; An article by Helen Lowe in UITP'96 suggests that the user should
  ;; not see all output produced by the proof process. 
  (remove-hook 'comint-output-filter-functions
	       'comint-postoutput-scroll-to-bottom 'local)

  (add-hook 'comint-output-filter-functions 'proof-shell-filter nil 'local)
  (setq comint-get-old-input (function (lambda () "")))

  ;; For a bit of memory saving in case of large inputs, don't keep history ring
  (setq comint-input-ring-size 1)
  (setq comint-input-ring (make-ring comint-input-ring-size))

  ;; Proof marker is initialised in filter to first prompt found
  (setq proof-marker (make-marker))
  ;; Urgent message marker records end position of last urgent
  ;; message seen.
  (setq proof-shell-urgent-message-marker (make-marker))
  ;; Urgent message scan marker records starting position to 
  ;; scan for urgent messages from
  (setq proof-shell-urgent-message-scanner (make-marker))
  (set-marker proof-shell-urgent-message-scanner (point-min))

  ;; Make cut functions work with proof shell output 
  (add-hook 'buffer-substring-filters 'proof-shell-strip-output-markup)

  ;; FIXME da: before entering proof assistant specific code,
  ;; we'd do well to check that process is actually up and
  ;; running now.  If not, call the process sentinel function
  ;; to display the buffer, and give an error.
  ;; (Problem to fix is that process can die before sentinel is set:
  ;;  it ought to be set just here, perhaps: but setting hook here
  ;;  had no effect for some odd reason).
  ;; What actually happens: an obscure infinite loop somewhere
  ;; that can lead to "lisp nesting exceeded" somewhere, when
  ;; shell startup fails.  Ugly, but low priority to fix.
  );)

;;
;; Sanity checks on important settings
;;

(defconst proof-shell-important-settings
  '(proof-shell-annotated-prompt-regexp ; crucial
    ))


;;;###autoload
(defun proof-shell-config-done ()
  "Initialise the specific prover after the child has been configured.
Every derived shell mode should call this function at the end of
processing."
  (with-current-buffer proof-shell-buffer

    ;; Give warnings if some crucial settings haven't been made
    (dolist (sym proof-shell-important-settings)
      (proof-warn-if-unset "proof-shell-config-done" sym))

    ;; We do not use font-lock here, it's a waste of cycles.
    (font-lock-mode 0)

    (let ((proc (get-buffer-process proof-shell-buffer)))
      ;; Add the kill buffer function and process sentinel
      (add-hook 'kill-buffer-hook 'proof-shell-kill-function t t)
      (set-process-sentinel proc 'proof-shell-bail-out)

      ;; Pre-sync initialization command.  This is necessary
      ;; for proof assistants which change their output modes
      ;; only after some initializations.
      (if proof-shell-pre-sync-init-cmd
	  (proof-shell-insert proof-shell-pre-sync-init-cmd 'init-cmd))

      ;; Flush pending output from startup (it gets hidden from the user)
      ;; while waiting for the prompt to appear
      (while (and (memq (process-status proc) '(open run))
		  (null (marker-position proof-marker)))
	(accept-process-output proc 1))

      (if (memq (process-status proc) '(open run))
	  (progn
	    ;; Also ensure that proof-action-list is initialised. 
	    (setq proof-action-list nil)
	    ;; Send main intitialization command and wait for it to be
	    ;; processed.   
	    
	    ;; First, if the prover supports PGIP and preferences are
	    ;; not configured, we may configure them.  (NB: this
	    ;; assumes that PGIP provers are ready-to-go, without
	    ;; needing init-cmd before PGIP processing).  We do this
	    ;; so that user preferences may be then set sensibly in
	    ;; the next step.
	    (proof-maybe-askprefs)
	    
	    ;; Now send the initialisation commands.
	    (unwind-protect
		(progn
		  (run-hooks 'proof-shell-init-hook)
		  (if proof-shell-init-cmd
		      (proof-shell-invisible-command proof-shell-init-cmd t))
		  (if proof-assistant-settings
		      (proof-shell-invisible-command 
		       (proof-assistant-settings-cmd) t)))

	      ;; Configure for unicode input
	      ;(proof-unicode-tokens-shell-config)
	      ))))))


(provide 'proof-shell)
;; proof-shell.el ends here
