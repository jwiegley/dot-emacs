;; proof-shell.el  Proof General shell mode.
;;
;; Copyright (C) 1994-2000 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

(require 'proof-menu)

;; Nuke some byte compiler warnings.

(eval-when-compile
  (require 'comint)
  (require 'font-lock))

;; Spans are our abstraction of extents/overlays.
(eval-and-compile
  (cond ((fboundp 'make-extent) (require 'span-extent))
	((fboundp 'make-overlay) (require 'span-overlay))))

;; FIXME:
;; Autoloads for proof-script (added to nuke warnings,
;; maybe should be 'official' exported functions in proof.el)
;; This helps see interface between proof-script / proof-shell.
;; FIXME 2: We can probably assume that proof-script is always
;; loaded before proof-shell, so just put a require on 
;; proof-script here.
(eval-and-compile
  (mapcar (lambda (f) 
	    (autoload f "proof-script"))
	  '(proof-goto-end-of-locked
	    proof-insert-pbp-command
	    proof-detach-queue 
	    proof-locked-end 
	    proof-set-queue-endpoints
	    proof-script-clear-queue-spans
	    proof-file-to-buffer 
	    proof-register-possibly-new-processed-file
	    proof-restart-buffers)))

;; FIXME:
;; Some variables from proof-shell are also used, in particular,
;; the menus.  These should probably be moved out to proof-menu.

;; ============================================================
;;
;; Internal variables used by proof shell
;;

(defvar proof-marker nil 
  "Marker in proof shell buffer pointing to previous command input.")

(defvar proof-action-list nil
  "A list of

  (SPAN COMMAND ACTION)

triples, which is a queue of things to do.
See the functions `proof-start-queue' and `proof-exec-loop'.")

(defvar proof-shell-silent nil
  "A flag, non-nil if PG thinks the prover is silent.")


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
has mode QUEUEMODE.
Otherwise, if the shell is busy, give an error.
No change to current buffer or point."
  (proof-shell-start)
  (unless (or (not proof-shell-busy) (eq queuemode proof-shell-busy))
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
Runs proof-state-change-hook to notify state change.
Clears the proof-shell-error-or-interrupt-seen flag.
If QUEUEMODE is supplied, set the lock to that value."
  (proof-shell-ready-prover queuemode)
  (setq proof-shell-error-or-interrupt-seen nil)
  (setq proof-shell-busy (or queuemode t))
  (run-hooks 'proof-state-change-hook))

(defun proof-release-lock (&optional err-or-int)
  "Release the proof shell lock, with error or interrupt flag ERR-OR-INT.
Clear proof-shell-busy, and set proof-shell-error-or-interrupt-seen
to err-or-int."
  (setq proof-shell-error-or-interrupt-seen err-or-int)
  (setq proof-shell-busy nil))



;;
;;  Starting and stopping the proof shell  
;;

(defun proof-shell-start ()
  "Initialise a shell-like buffer for a proof assistant.

Also generates goal and response buffers.
Does nothing if proof assistant is already running."
  (interactive)
  (unless (proof-shell-live-buffer)

    ;; This should configure the mode-setting variables
    ;; proof-mode-for-<blah> so we can set the modes below. 
    ;; <blah>=shell,goals,response.  We also need to set
    ;; proof-prog-name to start the program!
    (run-hooks 'proof-pre-shell-start-hook)

    ;; Clear some state
    (setq proof-included-files-list nil)

    ;; Added 05/99 by Patrick L.
    (let ((name (buffer-file-name (current-buffer))))
      ;; FIXME : we check that the buffer corresponds to a file,
      ;; but we do not check that it is in coq- or isa-mode
      (if (and name proof-prog-name-guess proof-guess-command-line)
	  (setq proof-prog-name 
		(apply proof-guess-command-line (list name)))))
    
    (if proof-prog-name-ask
	(save-excursion
	  (setq proof-prog-name (read-shell-command "Run process: "
						    proof-prog-name))))
    (let 
	;; PG 3.1: Buffer names are now based simply on proof assistant
	;; name, not process name which was a bit lowlevel and sometimes
	;; ugly (coqtop, hol.unquote).
	((proc (downcase proof-assistant)))

      (message (format "Starting process: %s" proof-prog-name))

      ;; Starting the inferior process (asynchronous)
      (let ((prog-name-list 
	     (proof-string-to-list 
	      ;; Cut in proof-rsh-command if it's non-nil and
	      ;; non whitespace.  FIXME: whitespace at start
	      ;; of this string is nasty.
	      (if (and proof-rsh-command
		       (not (string-match "^[ \t]*$" proof-rsh-command)))
		  (concat proof-rsh-command " " proof-prog-name)
		proof-prog-name)
	      ;; Split on spaces: FIXME: maybe should be whitespace.
	      " "))

	    (process-connection-type 
	     proof-shell-process-connection-type))

	;; An improvement here might be to catch failure of
	;; make-comint and then kill off the buffer.  Then we 
	;; could add back code above for multiple shells <2> <3>, etc.
	;; Seems hardly worth it.
	(apply 'make-comint  (append (list proc (car prog-name-list) nil)
				     (cdr prog-name-list))))

      (setq proof-shell-buffer (get-buffer (concat "*" proc "*")))

      (unless (proof-shell-live-buffer)
	;; Give error now if shell buffer isn't live
	;; Solves problem of make-comint succeeding but process
	;; exiting immediately.
	;; Might still be problems here if sentinels are set.
	(setq proof-shell-buffer nil)
	(error (format "Starting process: %s..failed" proof-prog-name)))

      ;; Create the associated buffers and set buffer variables
      (let ((goals	(concat "*" proc "-goals*"))
	    (resp	(concat "*" proc "-response*")))
	(setq proof-goals-buffer (get-buffer-create goals))
	(setq proof-response-buffer (get-buffer-create resp))
	;; Set the special-display-regexps now we have the buffer names
	(setq proof-shell-special-display-regexp 
	      (proof-regexp-alt goals resp))
	(proof-multiple-frames-enable))

      (save-excursion
	(set-buffer proof-shell-buffer)
	
	;; FIXME: Disable 16 Bit
	;; We noticed that for LEGO, it otherwise converts annotations
	;; to characters with (non-ASCII) code around 3000 which screws
	;; up our conventions that annotations lie between 128 and
	;; 256. We only observed the problem with FSF GNU Emacs 20.3 at
	;; present.
	(and (fboundp 'toggle-enable-multibyte-characters)
	     (toggle-enable-multibyte-characters -1))
	
	;; Initialise shell mode 
	;; Q: should this be done every time the process is started?
	;; A: yes, it does the process initialization, which is a bit
	;; odd (would expect it to be done here, maybe).


	(funcall proof-mode-for-shell)
	;; Check to see that the process is still going.
	;; Otherwise the sentinel will have killed off the
	;; other buffers and there's no point initialising
	;; them.
	(if (proof-shell-live-buffer)
	    (progn
	      (set-buffer proof-response-buffer)
	      (funcall proof-mode-for-response)
	      (set-buffer proof-goals-buffer)
	      (and (fboundp 'toggle-enable-multibyte-characters)
		   (toggle-enable-multibyte-characters -1))
	      (funcall proof-mode-for-goals))
	  (switch-to-buffer proof-shell-buffer)
	  (error "%s process exited!" proc)))
      (message 
       (format "Starting %s process... done." proc)))))


;;
;; Indicator and fake minor mode for active scripting buffer
;; 

(defcustom proof-shell-active-scripting-indicator
  (if proof-running-on-XEmacs
      (cons (make-extent nil nil) " Scripting ")
    " Scripting")
  "Modeline indicator for active scripting buffer.
If first component is extent it will automatically follow the colour
of the queue region."
  :type 'sexp
  :group 'proof-general-internals)

(cond
 (proof-running-on-XEmacs
  (if (extentp (car proof-shell-active-scripting-indicator))
      (set-extent-properties
       (car proof-shell-active-scripting-indicator)
       '(face proof-locked-face)))))

(unless
    (assq 'proof-active-buffer-fake-minor-mode minor-mode-alist)
  (setq minor-mode-alist
	(append minor-mode-alist
		(list 
		 (list
		  'proof-active-buffer-fake-minor-mode
		  proof-shell-active-scripting-indicator)))))


;;
;;  Shutting down proof shell and associated buffers
;;

(defun proof-shell-kill-function ()
  "Function run when a proof-shell buffer is killed.
Attempt to shut down the proof process nicely and
clear up all the locked regions and state variables.
Value for kill-buffer-hook in shell buffer.
Also called by proof-shell-bail-out if the process is
exited by hand (or exits by itself)."
  (let* ((alive    (comint-check-proc (current-buffer)))
	 (proc     (get-buffer-process (current-buffer)))
	 (bufname  (buffer-name)))
    (message "%s, cleaning up and exiting..." bufname)
    (let ((inhibit-quit t)		; disable C-g for now
	  timeout-id)
      (sit-for 0)			; redisplay
      (if alive				; process still there
	  (progn
	    (catch 'exited
	      (set-process-sentinel proc
				    (lambda (p m) (throw 'exited t)))
	      ;; Try to shut it down politely
	      ;; Do this before deleting other buffers, etc, so that
	      ;; any closing down processing works okay.
	      (if proof-shell-quit-cmd
		  (comint-send-string proc
				      (concat proof-shell-quit-cmd "\n"))
		(comint-send-eof))
	      ;; Wait a while for it to die before killing
	      ;; it off more rudely.  In XEmacs, accept-process-output
	      ;; or sit-for will run process sentinels if a process
	      ;; changes state.
	      ;; In FSF I've no idea how to get the process sentinel
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
      ;; For FSF Emacs, proc may be nil if killed already.
      (if proc (set-process-sentinel proc nil))
      ;; Restart all scripting buffers
      (proof-script-remove-all-spans-and-deactivate)
      ;; Clear state 
      (proof-shell-clear-state)
      ;; Kill buffers associated with shell buffer
      (if (buffer-live-p proof-goals-buffer)
	  (progn 
	    (kill-buffer proof-goals-buffer)
	    (setq proof-goals-buffer nil)))
      (if (buffer-live-p proof-response-buffer)
	  (progn 
	    (kill-buffer proof-response-buffer)
	    (setq proof-response-buffer nil)))
      (message "%s exited." bufname))))

(defun proof-shell-clear-state ()
  "Clear internal state of proof shell."
  (setq proof-action-list nil
	proof-included-files-list nil
	proof-shell-busy nil
	proof-shell-proof-completed nil
	proof-shell-error-or-interrupt-seen nil
	proof-shell-silent nil))

(defun proof-shell-exit ()
  "Query the user and exit the proof process.

This simply kills the proof-shell-buffer relying on the hook function
proof-shell-kill-function to do the hard work."
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
  "Clear script buffers and send proof-shell-restart-cmd.
All locked regions are cleared and the active scripting buffer
deactivated.  

If the proof shell is busy, an interrupt is sent with
proof-interrupt-process and we wait until the process is ready.

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
  ;; Now clear all context
  (proof-script-remove-all-spans-and-deactivate)
  (proof-shell-clear-state)
  (if (and (buffer-live-p proof-shell-buffer)
	   proof-shell-restart-cmd)
	   (proof-shell-invisible-command
	    proof-shell-restart-cmd)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Proof by pointing                                       ;;
;;          All very lego-specific at present                       ;;
;;          To make sense of this code, you should read the         ;;
;;          relevant LFCS tech report by tms, yb, and djs           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; New function added for 3.0 -da
(defun pbp-yank-subterm (event)
  "Copy the subterm indicated by the mouse-click EVENT.
This function should be bound to a mouse button in the Proof General
goals buffer.

The EVENT is used to find the smallest subterm around a point.  The
subterm is copied to the kill-ring, and immediately yanked (copied)
into the current buffer at the current cursor position.

In case the current buffer is the goals buffer itself, the yank
is not performed.  Then the subterm can be retrieved later by an
explicit yank."
  (interactive "e")
  (let (span)
    (save-window-excursion
      (save-excursion
	(mouse-set-point event)
	(setq span (span-at (point) 'proof))
	(if span (copy-region-as-kill
		  (span-start span) 
		  (span-end span)))))
    (if (and span (not (eq proof-buffer-type 'pbp)))
	(yank))))

(defun pbp-button-action (event)
  "Construct a proof-by-pointing command based on the mouse-click EVENT.
This function should be bound to a mouse button in the Proof General
goals buffer.

The EVENT is used to find the smallest subterm around a point.  A
position code for the subterm is sent to the proof assistant, to ask
it to construct an appropriate proof command.  The command which is
constructed will be inserted at the end of the locked region in the
proof script buffer, and immediately sent back to the proof assistant.
If it succeeds, the locked region will be extended to cover the
proof-by-pointing command, just as for any proof command the 
user types by hand."
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
      (setq ls (cons (int-to-string 
		      ;; FIXME: FSF doesn't have char-to-int.
		      (char-to-int (aref string a)))
		     (cons " " ls)))
      (incf a))
    (apply 'concat (nreverse ls))))

(defun pbp-construct-command ()
  (let* ((span (span-at (point) 'proof))
	 (top-span (span-at (point) 'proof-top-element))
	 top-info)
    (if (null top-span) ()
      (setq top-info (span-property top-span 'proof-top-element))
      (pop-to-buffer proof-script-buffer)
      (cond
       (span
	(proof-shell-invisible-command 
	 (format (if (eq 'hyp (car top-info)) pbp-hyp-command 
		                              pbp-goal-command)
		 (concat (cdr top-info) (proof-expand-path 
					 (span-property span 'proof))))))
       ((eq (car top-info) 'hyp)
	(proof-shell-invisible-command
	 (format pbp-hyp-command (cdr top-info))))
       (t
	 (proof-insert-pbp-command
	  (format pbp-change-goal (cdr top-info))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Turning annotated output into pbp goal set              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pbp-make-top-span (start end)
  (let (span name)
    (goto-char start)
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
  "Last interesting output from proof process output and what to do with it.

This is a list of tuples of the form (TYPE . STRING). type is either
'analyse or 'insert. 

'analyse denotes that string's term structure  ought to be analysed
         and displayed in the `proof-goals-buffer'

'insert  denotes that string ought to be displayed in the
         `proof-response-buffer' ")

(defun proof-shell-analyse-structure (string)
  "Analyse the term structure of STRING and display it in proof-goals-buffer.
This function converts proof-by-pointing markup into mouse-highlighted
extents."
  (save-excursion
    (let* ((ip 0) (op 0) ap (l (length string)) 
	   (ann (make-string (length string) ?x))
           (stack ()) (topl ()) 
	   (out (make-string l ?x)) 
	   c span)

      ;; Form output string by removing characters 128 or greater,
      ;; (ALL annotations), unless proof-shell-leave-annotations-in-output 
      ;; is set.  

      ;; FIXME da: this can be removed now that we strip annotations
      ;; immediately after fontification in proof-fontify-region.  We
      ;; may no longer need the setting
      ;; proof-shell-leave-annotations-in-ouput, unless it breaks LEGO
      ;; font lock patterns for example.

      (unless proof-shell-leave-annotations-in-output
	(while (< ip l)	
	  (if (< (setq c (aref string ip)) 128)
	      (progn (aset out op c)
		     (incf op)))
	  (incf ip)))

      ;; Response buffer may be out of date. It may contain (error)
      ;; messages relating to earlier proof states
      
      ;; FIXME da: this isn't always the case.  In Isabelle
      ;; we get <WARNING MESSAGE> <CURRENT GOALS> output,
      ;; or <WARNING MESSAGE> <ORDINARY MESSAGE>.  Both times
      ;; <WARNING MESSAGE> would be relevant.
      ;; We should only clear the output that was displayed from
      ;; the *previous* prompt.

      ;; FIXME da: I get a lot of empty response buffers displayed
      ;; which might be nicer removed. Temporary test for this
      ;; clean-buffer to see if it behaves well.

      ;; Erase the response buffer if need be, maybe also removing the
      ;; window.  Indicate that it should be erased before the next
      ;; output.
      (proof-shell-maybe-erase-response t t)

      (set-buffer proof-goals-buffer)

      (erase-buffer)

      ;; Insert the (possibly cleaned up) string.
      (if proof-shell-leave-annotations-in-output
	  (insert string)
	(insert (substring out 0 op)))
      
      ;; Get fonts and characters right
      (proof-fontify-region (point-min) (point-max))

      (set-buffer-modified-p nil)	; nicety

      ;; Keep point at the start of the buffer.  Might be nicer to
      ;; keep point at "current" subgoal a la Isamode, but never mind
      ;; just now.
      (proof-display-and-keep-buffer proof-goals-buffer (point-min))

      ;; FIXME: This code is broken for Emacs 20.3 (mule?) which has
      ;; 16 bit character codes.  (Despite earlier attempts to make
      ;; character codes in this buffer 8 bit) 
      ;; But this is a more serious future problem in Proof General
      ;; which requires re-engineering all this 128 mess.
      ;; FIXME Mk II: This is also going to be broken for X-Symbol
      ;; interaction, when tokens (several chars long) are replaced by
      ;; single characters.
      (unless
	  (or
	   ;; No point if we haven't set the pbp char vars
	   (not proof-shell-goal-char)
	   ;; Don't do it for Emacs 20.3 or any version which
	   ;; has this suspicious function.
	   (fboundp 'toggle-enable-multibyte-characters))
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
	   ((and (consp stack) (= c proof-shell-field-char))
	    ;; (consp stack) has been added to make the code more robust.
	    ;; In fact, this condition is violated when using
	    ;; lego/example.l and FSF GNU Emacs 20.3
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
	(if proof-goal-hyp-fn
	    (while (setq ip (car topl) 
			 topl (cdr topl))
	      (pbp-make-top-span ip (car topl))))))))

(defun proof-shell-strip-special-annotations (string)
  "Strip special annotations from a string, returning cleaned up string.
*Special* annotations are characters with codes higher than
'proof-shell-first-special-char'.
If proof-shell-first-special-char is unset, return STRING unchanged."
  (if proof-shell-first-special-char
      (let* ((ip 0) (op 0) (l (length string)) (out (make-string l ?x )))
	(while (< ip l)
	  (if (>= (aref string ip) proof-shell-first-special-char)
	      (if (char-equal (aref string ip) proof-shell-start-char)
		  (progn (incf ip)
			 (while 
			     (< (aref string ip) 
				proof-shell-first-special-char)
			   (incf ip))))
	    (aset out op (aref string ip))
	    (incf op))
	  (incf ip))
	(substring out 0 op))
    string))

(defun proof-shell-handle-output (start-regexp end-regexp append-face)
  "Displays output from `proof-shell-buffer' in `proof-response-buffer'.
The region in `proof-shell-buffer begins with the first match 
beyond the prompt for START-REGEXP and is delimited by the
last match in the buffer for END-REGEXP.  The match for END-REGEXP 
is not part of the specified region.  This mechanism means if there
are multiple matches for START-REGEXP and END-REGEXP, we match the
largest region containing them all.
This is a subroutine of proof-shell-handle-error.
Returns the string (with faces) in the specified region."
  (let (start end string)
    (save-excursion
      (set-buffer proof-shell-buffer)
      (goto-char (point-max))
      (setq end (search-backward-regexp end-regexp))
      (goto-char (marker-position proof-marker))
      (setq start (- (search-forward-regexp start-regexp)
		     (length (match-string 0))))
      ;; FIXME: if the shell buffer is x-symbol minor mode,
      ;; this string can contain X-Symbol characters, which
      ;; is not suitable for processing with proof-fontify-region.
      (setq string
	    (if proof-shell-leave-annotations-in-output
		(buffer-substring start end)
	      (proof-shell-strip-special-annotations
	       (buffer-substring start end)))))
    ;; Erase if need be, and erase next time round too.
    (proof-shell-maybe-erase-response t nil)
    (proof-response-buffer-display string append-face)))

(defun proof-shell-handle-delayed-output ()
  "Display delayed output.
This function expects 'proof-shell-delayed-output' to be a cons cell
of the form ('insert . TXT) or ('analyse . TXT).
See the documentation for `proof-shell-delayed-output' for further details."
  (let ((ins (car proof-shell-delayed-output))
	(str (cdr proof-shell-delayed-output)))
    (cond 
     ;; 
     ;; 1. Text to be inserted in response buffer.
     ;;
     ((eq ins 'insert)
      ;; FIXME da: this next line is nasty, it breaks something?
      ;;   (unless (string-equal str "done")  
      ;; Think this was meant as a get out clause from somewhere.
      ;; Maybe if the output string from the prover is empty?
      ;; Anyway, we leave it alone now, maybe to see some spurious 
      ;; "done" displays 

      ;; FIXME: this can be done away with, probably.
      (unless proof-shell-leave-annotations-in-output
	(setq str (proof-shell-strip-special-annotations str)))

      (proof-shell-maybe-erase-response t nil)
      (proof-response-buffer-display str)
      (proof-display-and-keep-buffer proof-response-buffer))
     ;;
     ;; 2. Text to be inserted in goals buffer
     ((eq ins 'analyse)
      (proof-shell-analyse-structure str))
     ;;
     ;; 3. Nothing else should happen
     (t (assert nil "proof-shell-handle-delayed-output: wrong type!"))))
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



;; FIXME da: the magical use of "Done." and "done" as values in
;; proof-shell-handled-delayed-output is horrendous.  Should
;; be changed to something more understandable!!

(defun proof-shell-handle-error (cmd string)
  "React on an error message triggered by the prover.
We first flush unprocessed goals to the goals buffer.
The error message is displayed in the responsebuffer.
Then we call `proof-shell-error-or-interrupt-action', which see."
  ;; Why not flush goals also for interrupts?
  (unless
      (or
       ;; da: a first safety check 
       (not (eq (car proof-shell-delayed-output) 'insert))
       (equal (cdr proof-shell-delayed-output) "Done.")
       ;; da: added this, seems little point in printing "done" either?
       (equal (cdr proof-shell-delayed-output) "done"))
    ;; Flush goals (from some last successful proof step) to goals
    ;; buffer
    (save-excursion
      (proof-shell-analyse-structure 
       (cdr proof-shell-delayed-output))))
  ;; Perhaps we should erase the proof-response-buffer?
  (proof-shell-handle-output
   proof-shell-error-regexp proof-shell-annotated-prompt-regexp
   'proof-error-face)
  (proof-display-and-keep-buffer proof-response-buffer)
  (proof-shell-error-or-interrupt-action 'error))

(defun proof-shell-handle-interrupt ()
   "React on an interrupt message from the prover.
 Runs proof-shell-error-or-interrupt-action."
  (proof-shell-maybe-erase-response t t t) ; force cleaned now & next
  (proof-shell-handle-output
   proof-shell-interrupt-regexp proof-shell-annotated-prompt-regexp
   'proof-error-face)
;  (proof-display-and-keep-buffer proof-response-buffer)
  (proof-warning 
   "Interrupt: script management may be in an inconsistent state")
  (proof-shell-error-or-interrupt-action 'interrupt))

(defun proof-shell-error-or-interrupt-action (&optional err-or-int)
  "General action when an error or interrupt message appears from prover.
A subroutine for proof-shell-handle-interrupt and proof-shell-handle-error.

We sound a beep, clear queue spans and proof-action-list, and set the flag 
proof-shell-error-or-interrupt-seen to the ERR-OR-INT argument.
Then we call `proof-shell-handle-error-or-interrupt-hook'."
  (save-excursion			;; for safety.
    (beep)
    ;; NB: previously for interrupt, clear-queue-spans 
    ;; was only called if shell busy.  Any harm calling it always?
    (proof-script-clear-queue-spans) 
    (setq proof-action-list nil)
    (proof-release-lock err-or-int)
    ;; Make sure that prover is outputting data now.
    ;; FIXME: put something here!
    ;; New: this is called for interrupts too.
    (run-hooks 'proof-shell-handle-error-or-interrupt-hook)))

(defun proof-goals-pos (span maparg)
  "Given a span, return the start of it if corresponds to a goal, nil otherwise."
 (and (eq 'goal (car (span-property span 'proof-top-element)))
		(span-start span)))

(defun proof-pbp-focus-on-first-goal ()
  "If the `proof-goals-buffer' contains goals, bring the first one into view.
This is a hook function for proof-shell-handle-delayed-output-hook."
  ;; FIXME: does nothing in FSF
  (and (fboundp 'map-extents)
       (let
	   ((pos (map-extents 'proof-goals-pos proof-goals-buffer
			      nil nil nil nil 'proof-top-element)))
	 (and pos (set-window-point
		   (get-buffer-window proof-goals-buffer t) pos)))))

           
(defsubst proof-shell-string-match-safe (regexp string)
  "Like string-match except returns nil if REGEXP is nil."
  (and regexp (string-match regexp string)))

      
(defun proof-shell-process-output (cmd string)
  "Process shell output (resulting from CMD) by matching on STRING.
CMD is the first part of the proof-action-list that lead to this
output.  The result of this function is a pair (SYMBOL NEWSTRING).

Here is where we recognizes interrupts, abortions of proofs, errors,
completions of proofs, and proof step hints (proof by pointing results).
They are checked for in this order, using
 
  proof-shell-interrupt-regexp
  proof-shell-error-regexp
  proof-shell-abort-goal-regexp
  proof-shell-proof-completed-regexp
  proof-shell-result-start

All other output from the proof engine will be reported to the user in
the response buffer by setting proof-shell-delayed-output to a cons
cell of ('insert . TEXT) where TEXT is the text string to be inserted.

Order of testing is: interrupt, abort, error, completion.

To extend this function, set proof-shell-process-output-system-specific.

The \"aborted\" case is intended for killing off an open proof during
retraction.  Typically it the error message caused by a
proof-kill-goal-command.  It simply inserts the word \"Aborted\" into
the response buffer.  So it is expected to be the result of a 
retraction, rather than the indication that one should be made.

This function can return one of 4 things as the symbol: 'error,
'interrupt, 'loopback, or nil. 'loopback means this was output from
pbp, and should be inserted into the script buffer and sent back to
the proof assistant."
  (or
   ;; First check for error, interrupt, abort, proof completed
   (cond
    ((proof-shell-string-match-safe proof-shell-interrupt-regexp string)
     'interrupt)
    
    ((proof-shell-string-match-safe proof-shell-error-regexp string)
     (cons 'error (proof-shell-strip-special-annotations
		   (substring string
			      (match-beginning 0)))))
    
    ((proof-shell-string-match-safe proof-shell-abort-goal-regexp string)
     (proof-clean-buffer proof-goals-buffer)
     (setq proof-shell-delayed-output (cons 'insert "\nAborted\n"))
     ())
    
    ((proof-shell-string-match-safe proof-shell-proof-completed-regexp string)
     ;; In case no goals display
     (proof-clean-buffer proof-goals-buffer)
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
       ;; Ugly hack: provers with special characters don't include
       ;; the match in their goals output.  Others do.
       (unless proof-shell-first-special-char
	 (setq start (match-beginning 0)))
       (setq end (if proof-shell-end-goals-regexp
		     (string-match proof-shell-end-goals-regexp string start)
		   (length string)))
       (setq proof-shell-delayed-output 
	     (cons 'analyse (substring string start end)))))
    
    ;; Test for a proof by pointing command hint
    ((proof-shell-string-match-safe proof-shell-result-start string)
     (let (start end)
       (setq start (+ 1 (match-end 0)))
       (string-match proof-shell-result-end string)
       (setq end (- (match-beginning 0) 1))
       (cons 'loopback (substring string start end))))
    
    ;; Hook to tailor proof-shell-process-output to a specific proof
    ;; system, in the case that all the above matches fail.
    ((and proof-shell-process-output-system-specific
	  (funcall (car proof-shell-process-output-system-specific)
		   cmd string))
     (funcall (cdr proof-shell-process-output-system-specific)
	      cmd string))

    ;; Finally, any other output will appear as a response.
    (t (setq proof-shell-delayed-output (cons 'insert string))))))


;;
;;   Low-level commands for shell communication
;;

(defvar proof-shell-insert-space-fudge 
  (cond
   ((string-match "21.*XEmacs" emacs-version) " ")
   (proof-running-on-XEmacs "")
   (t " "))
  "String to insert after setting proof marker to prevent it moving.
Allows for a difference between different versions of comint across
different Emacs versions.")

(defun proof-shell-insert (string action)
  "Insert STRING at the end of the proof shell, call comint-send-input.

First call proof-shell-insert-hook.  The argument ACTION may be
examined by the hook to determine how to process the STRING variable.

Then strip STRING of carriage returns before inserting it and updating
proof-marker to point to the end of the newly inserted text.

Do not use this function directly, or output will be lost.  It is only
used in proof-append-alist when we start processing a queue, and in
proof-shell-exec-loop, to process the next item."
  (save-excursion
    (set-buffer proof-shell-buffer)
    (goto-char (point-max))
    
    ;; See docstring for this hook
    (run-hooks 'proof-shell-insert-hook)

    ;; Now we replace CRs from string with spaces. This was done in
    ;; "proof-send" previously and this function 
    ;; allowed for input with CRs to be sent.  But it was never
    ;; used.  The only place this was called instead of proof-send
    ;; was for proof-shell-init-cmd, but now that is sent via 
    ;; proof-shell-invisible-command instead.

    ;; HYPOTHESIS da: I don't know why proof-send strips CRs, no 
    ;; hints were given in the original code. I assume it is needed 
    ;; because several CR's can result in several prompts, and 
    ;; we want to stick to the one prompt per output chunk scenario. 
    ;; (However stripping carriage returns might just be
    ;; plain WRONG for some theorem prover's syntax, possibly)

    (let ((l (length string)) (i 0))
      (while (< i l)
	(if (= (aref string i) ?\n) (aset string i ?\ ))
	(incf i)))

    (insert string)

    ;; Advance the proof-marker, if synchronization has been gained.
    ;; A null marker position indicates that synchronization is not
    ;; yet gained.  (NB: Any output received before syncrhonization is
    ;; gained is ignored!)
    (unless (null (marker-position proof-marker))
      (set-marker proof-marker (point)))

    ;; FIXME: possible improvement.  Make for post 3.0 releases
    ;; in case of problems.
    ;; (set-marker proof-shell-urgent-message-marker (point))
    ;; (set-marker proof-shell-urgent-message-scanner (point))

    ;; FIXME da: this space fudge is actually a visible hack:
    ;; the response string begins with a space and a newline.
    (insert proof-shell-insert-space-fudge)
    (comint-send-input)))

;; OLD BUGGY CODE here 
;; Left in as a warning of a race condition.  
;; It seems that comint-send-input can lead to the 
;; output filter running before it returns, so that
;; the set-marker call below is executed too late.
;; The result is that the filter deals with
;; the previous portion of output instead of the 
;; most recent one!
;;
;; xemacs and FSF emacs have different semantics for what happens when
;; shell input is sent next to a marker
;; the following code accommodates both definitions
;    (let ((inserted (point)))
;      (comint-send-input)
;      (set-marker proof-marker inserted))))


;; ============================================================
;;
;; Code for manipulating proof queue
;;


(defun proof-shell-command-queue-item (cmd callback)
  "Return the proof queue entry needed to run CMD with callback CALLBACK."
  (list nil cmd callback))


(defun proof-shell-set-silent (span)
  "Callback for `proof-shell-start-silent'.
Very simple function but it's important to give it a name to help
track what happens in the proof queue."
  (setq proof-shell-silent t))

(defun proof-shell-start-silent-item ()
  "Return proof queue entry for starting silent mode."
  (proof-shell-command-queue-item 
   proof-shell-start-silent-cmd
   'proof-shell-set-silent))

(defun proof-shell-clear-silent (span)
  "Callback for `proof-shell-stop-silent'.
Very simple function but it's important to give it a name to help
track what happens in the proof queue."
  (setq proof-shell-silent nil))

(defun proof-shell-stop-silent-item ()
  "Return proof queue entry for stopping silent mode."
  (proof-shell-command-queue-item 
   proof-shell-stop-silent-cmd
   'proof-shell-clear-silent))

;; FIXME: could be macro for efficiency improvement in avoiding calculating num
(defun proof-shell-should-be-silent (num)
  "Return non-nil if we must switch to silent mode, adding NUM entries to queue."
  (if proof-shell-start-silent-cmd
      (or proof-shell-silent	; already
	  ;; NB: there is some question here over counting the
	  ;; proof-action-list, since it could itself contain
	  ;; silent-on/off commands which should be ignored for
	  ;; counting, really... also makes cutting lists for advanced
	  ;; queue processing more tricky.
	  (>= (+ num (length proof-action-list))
	     proof-shell-silent-threshold))))
	      

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
    ;; FIXME: may be wrong time to invoke callbacks for no-op commands,
    ;; if the queue is not empty.
    (while (and alist (string= 
		       (nth 1 (setq item (car alist))) 
		       proof-no-command))
      (funcall (nth 2 item) (car item))
      (setq alist (cdr alist)))
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
	    (setq proof-shell-delayed-output (cons 'insert "Done."))
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
  "Process the proof-action-list.

`proof-action-list' contains a list of (SPAN COMMAND ACTION) triples.

If this function is called with a non-empty proof-action-list, the
head of the list is the previously executed command which succeeded.
We execute (ACTION SPAN) on the first item, then (ACTION SPAN) on any
following items which have proof-no-command as their cmd components.
If a there is a next command after that, send it to the process.  If
the action list becomes empty, unlock the process and remove the queue
region.

The return value is non-nil if the action list is now empty."
  ;; The loop looks like: Execute the
  ;; command, and if it's successful, do action on span.  If the
  ;; command's not successful, we bounce the rest of the queue and do
  ;; some error processing.

  (unless (not proof-action-list)		; exit immediately if finished.
      (save-excursion
	;; Switch to active scripting buffer if there is one.
	(if proof-script-buffer
	    (set-buffer proof-script-buffer))
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
	  ;; If action list is empty or has a single element,
	  ;; we want to make sure prover is being noisy.
	  (if (and proof-shell-silent
		   (or (null proof-action-list)	; possible?
		       (null (cdr proof-action-list))))
	      (progn
		;; Stick the quieten command onto the queue
		(setq proof-action-list
		      (cons (proof-shell-stop-silent-item)
			    proof-action-list))
		(setq item (car proof-action-list))))
	  ;; If action list is empty now, release the process lock
	  (if (null proof-action-list)
	      (progn (proof-release-lock)
		     (proof-detach-queue)
		     ;; indicate finished
		     t)
	    ;; Otherwise, send the next command to the process.
	    (proof-shell-insert (nth 1 item) (nth 2 item))
	    ;; indicate not finished
	    nil)))))

;; FIXME da: some places in the code need to be made robust in
;; case of buffer kills, etc, before callbacks.  Is this function
;; one?
(defun proof-shell-insert-loopback-cmd  (cmd)
  "Insert command sequence triggered by the proof process
at the end of locked region (after inserting a newline and indenting).
Assume proof-script-buffer is active."
  (unless (string-match "^\\s-*$" cmd)	; FIXME: assumes cmd is single line
    (save-excursion
      (set-buffer proof-script-buffer) 
      (let (span)
	(proof-goto-end-of-locked)
	;; Fix 16.11.99.  This attempts to indent current line which can
	;; be read-only.  
      ;; (newline-and-indent)
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
	(setq span (make-span (proof-locked-end) (point)))
	(set-span-property span 'type 'pbp)
	(set-span-property span 'cmd cmd)
	(proof-set-queue-endpoints (proof-locked-end) (point))
	(setq proof-action-list 
	      (cons (car proof-action-list) 
		    (cons (list span cmd 'proof-done-advancing)
			  (cdr proof-action-list))))))))

;; da: first note of this sentence is false!
;; ******** NB **********
;;  While we're using pty communication, this code is OK, since all
;; eager annotations are one line long, and we get input a line at a
;; time. If we go over to piped communication, it will break.

(defun proof-shell-message (str)
  "Output STR in minibuffer."
  ;; %s is used below to escape characters special to 
  ;; 'format' which could appear in STR.
  (message "%s" (concat "[" proof-assistant "] " str)))

(defun proof-shell-process-urgent-message (message)
  "Analyse urgent MESSAGE for various cases.
Cases are: included file, retracted file, cleared response buffer, 
variable setting or dependency list. 
If none of these apply, display MESSAGE.

MESSAGE should be a string annotated with 
proof-shell-eager-annotation-start, proof-shell-eager-annotation-end."
    (cond
   ;; Is the prover processing a file?
   ;; FIXME da: this interface is quite restrictive: might be
   ;; useful for one message to name several files, or include
   ;; an instruction to purge the included files list, rather
   ;; than erasing everything and re-adding it.
   ;; Contrast retraction interface: there we compute whole
   ;; new list.
   ;; (Come to think of it, maybe we could unify the two
   ;; cases: automatically find removed files and added files
   ;; between two versions of proof-included-files-list)
   ((and proof-shell-process-file 
	 (string-match (car proof-shell-process-file) message))
    (let
	((file (funcall (cdr proof-shell-process-file) message)))
      ;; Special hack: empty string indicates current scripting buffer
      ;; (not used anywhere presently?)
      ;; (if (and proof-script-buffer (string= file ""))
      ;;  (setq file (buffer-file-name proof-script-buffer)))
      ;; YES!  It *was* used by LEGO.
      ;; Now we avoid this in favour of altering the processed
      ;; files list when the current scripting buffer changes,
      ;; inside Proof General.  Attempt to harmonize behaviour
      ;; with Isabelle.  Seems wrong to add "example.l" to
      ;; list of processed files if it's only partly processed?
      ;; (On the other hand, for lego, it may have declared a 
      ;;  module heading, which is probably Lego's standard
      ;;  for what a processed file actually is).
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
	 ;; Do nothing if active scripting buffer hasn't changed
	 ;; (NB: it might have been nuked)
	 ((eq scrbuf proof-script-buffer))
	 ;; FIXME da: I've forgotten the next condition was needed?
	 ;; 
	 ;; In fact, it breaks the case that the current scripting
	 ;; buffer should be deactivated if the prover retracts it.
	 ;; When scripting begins again in the buffer, other
	 ;; files may have to be re-read which may not happen unless
	 ;; scripting is properly de-activated.
	 ;;
	 ;; Otherwise, active scripting buffer has been retracted.
	 ;; Add it back!!  Why? Presumably because code likes to
	 ;; have an active scripting buffer??
	 (t
	  ;; FIXME da: want to test disabling currently active scripting
	  ;; buffer.  Unfortunately this doesn't work with current
	  ;; use of proof-script-buffer-list: always have to have
	  ;; *some* scripting buffer active.  ARGHH!
	  ;; FIXME da: test not having this add-back.  Then
	  ;; scripting buffer may change wrongly and randomly
	  ;; to some other buffer, without running change functions.
	  ;;
	  ;; FIXME da: test setting this to nil, scary!
	  (setq proof-script-buffer nil)
	  ;;(setq proof-script-buffer-list 
	  ;;	(cons scrbuf proof-script-buffer-list))
	  ;; (save-excursion
	  ;;  (set-buffer scrbuf)
	  ;;  (proof-init-segmentation)))))
	  )))
      ))

   ;; CASE clear response: prover asks PG to clear response buffer
   ((and proof-shell-clear-response-regexp
	 (string-match proof-shell-clear-response-regexp message)
	 proof-response-buffer)
    ;; Erase response buffer and possibly its windows.
    (proof-shell-maybe-erase-response nil t t))

   ;; CASE clear goals: prover asks PG to clear goals buffer
   ((and proof-shell-clear-goals-regexp
	 (string-match proof-shell-clear-goals-regexp message)
	 proof-goals-buffer)
    ;; Erase goals buffer but and possibly its windows
    (proof-clean-buffer proof-goals-buffer))
   
   ;; CASE variable setting: prover asks PG to set some variable 
   ;; NB: no safety protection whatsoever here, we use blind faith
   ;; that the prover will not send malicious elisp!!
   ((and proof-shell-set-elisp-variable-regexp
	 (string-match proof-shell-set-elisp-variable-regexp message))
    (let 
	((variable   (match-string 1 message))
	 (expr	     (match-string 2 message)))
      (condition-case err
	  ;; Easiest way to do this seems to be to dump the lisp
	  ;; string into another buffer -- no direct way to eval
	  ;; from a string?
	(with-temp-buffer
	  (insert expr)
	  (set (intern variable) (eval-last-sexp t)))
	(t (proof-debug 
	    (concat
	     "lisp error when obeying proof-shell-set-elisp-variable: \n"
	     "setting `" variable "'\n to: \n"
	     expr "\n"))))))

   ;; CASE theorem dependency: prover lists thms used in last proof
   ((and proof-shell-theorem-dependency-list-regexp 
	 (string-match proof-shell-theorem-dependency-list-regexp message))
      (setq proof-last-theorem-dependencies 
	    (split-string (match-string 1 message))))
   
   (t
    ;; We're about to display a message.  Clear the response buffer
    ;; if necessary, but don't clear it the next time.
    ;; Don't bother remove the window for the response buffer
    ;; because we're about to put a message in it.
    (proof-shell-maybe-erase-response nil nil)
    (let ((stripped	(proof-shell-strip-special-annotations message))
	  firstline)
      ;; Display first chunk of output in minibuffer.
      ;; Maybe this should be configurable, it can get noisy.
      (proof-shell-message 
       (substring stripped 0 (or (string-match "\n" stripped)
				 (min (length stripped) 75))))
      (proof-response-buffer-display 
       (if proof-shell-leave-annotations-in-output
	   message
	 stripped)
       'proof-eager-annotation-face)))))

(defvar proof-shell-urgent-message-marker nil
  "Marker in proof shell buffer pointing to end of last urgent message.")

(defvar proof-shell-urgent-message-scanner nil
  "Marker in proof shell buffer pointing to scan start for urgent messages.")

(defun proof-shell-process-urgent-messages ()
  "Scan the shell buffer for urgent messages.
Scanning starts from proof-shell-urgent-message-scanner and handles
strings between regexps eager-annotation-start and eager-annotation-end.

Note that we must search the buffer rather than the chunk of output
being filtered process because we have no guarantees about where
chunks are broken: it may be in the middle of an annotation.

This is a subroutine of proof-shell-filter."
  (let ((pt (point)) (end t) lastend start)
    (goto-char (marker-position proof-shell-urgent-message-scanner))
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
    ;; FIXME: maybe we don't need to be as careful as these three checks?
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
	      (- (point) proof-shell-eager-annotation-start-length)
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

	    
;; NOTE da: proof-shell-filter does *not* update the proof-marker,
;; that's done in proof-shell-insert.  Previous docstring below was
;; wrong.  The one case where this function updates proof-marker is
;; the first time through the loop to synchronize.
(defun proof-shell-filter (str)
  "Filter for the proof assistant shell-process.
A function for comint-output-filter-functions.

Deal with output and issue new input from the queue.

Handle urgent messages first.  As many as possible are processed,
using the function `proof-shell-process-urgent-messages'.

Otherwise wait until an annotated prompt appears in the input.  
If proof-shell-wakeup-char is set, wait until we see that in the
output chunk STR.  This optimizes the filter a little bit.

If a prompt is seen, run proof-shell-process-output on the output
between the new prompt and the last input (position of proof-marker)
or the last urgent message (position of
proof-shell-urgent-message-marker), whichever is later.  
For example, in this case:

 PROMPT> INPUT
 OUTPUT-1
 URGENT-MESSAGE
 OUTPUT-2
 PROMPT>

proof-marker is set after INPUT by proof-shell-insert and
proof-shell-urgent-message-marker is set after URGENT-MESSAGE.
Only OUTPUT-2 will be processed.  For this reason, error
messages and interrupt messages should *not* be considered
urgent messages.

Output is processed using proof-shell-filter-process-output.

The first time that a prompt is seen, proof-marker is 
initialised to the end of the prompt.  This should
correspond with initializing the process.  The 
ordinary output before the first prompt is ignored (urgent messages, 
however, are always processed; hence their name)."
  (save-excursion
    (and proof-shell-eager-annotation-start
	 (proof-shell-process-urgent-messages))

    ;; FIXME da: some optimization possible here by customizing
    ;; filter according to whether proof-shell-wakeup-char, etc,
    ;; are non-nil.  Make proof-shell-filter into a macro to do
    ;; this.

    (if ;; Some proof systems can be hacked to have annotated prompts;
	;; for these we set proof-shell-wakeup-char to the annotation 
	;; special, and look for it in the output before doing anything.
	(if proof-shell-wakeup-char
	    ;; FIXME: this match doesn't work in emacs-mule, darn.
	    ;; (string-match (char-to-string proof-shell-wakeup-char) str))
	    ;; FIXME: this match doesn't work in FSF emacs 20.5, darn.
	    ;; (find proof-shell-wakeup-char str)
	    ;; FIXME: 3.1pre: temporarily, use both tests!
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
	    ;; FIXME da: we'd rather do this initialization outside
	    ;; of the filter function for better efficiency!
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
			(proof-shell-filter-process-output "")))))
	  ;; Now we're looking for the end of the piece of output
	  ;; which will be processed.  
	  
	  ;; Note that the way this filter works, only one piece of
	  ;; output can be dealt with at a time so we loose sync if
	  ;; there's more than one bit there.
	  
	  ;; The blasphemous situation that the proof-action-list
	  ;; is empty is now quietly ignored so that users can
	  ;; type in the shell buffer without being screamed at.
	  ;; Also allows the process to output something for
	  ;; some other reason (perhaps it's just being chatty),
	  ;; although that could break the synchronization.
	  ;; Note that any "unexpected" output like this gets
	  ;; ignored.
	  (if proof-action-list
	      (let ((urgnt    (marker-position 
			       proof-shell-urgent-message-marker))
		    string startpos)
		;; Ignore any urgent messages that have already been 
		;; dealt with.  This loses in the case mentioned above.
		;; A more general way of doing this would be
		;; to filter out or delete the urgent messages which 
		;; have been processed already.  
		(setq startpos (goto-char (marker-position proof-marker)))
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
		      (backward-char (- (match-end 0) (match-beginning 0)))
		      ;; NB: decoding x-symbols here is perhaps a bit 
		      ;;  expensive; moreover it leads to problems 
		      ;;  processing special characters as annotations
		      ;;  later on.  So no fontify or decode.
		      ;;   (proof-fontify-region startpos (point))
		      (setq string (buffer-substring startpos (point)))
		      (goto-char (point-max))	
		      (proof-shell-filter-process-output string))))
	    ;; If proof-action-list is empty, make sure the process lock
	    ;; is not held!  This should solve continual "proof shell busy"
	    ;; error messages which sometimes occur during development,
	    ;; at least.
	    (if proof-shell-busy
		(progn
		  (proof-debug 
		   "proof-shell-filter found empty action list yet proof shell busy.")
		  (proof-release-lock))))))))


(defun proof-shell-filter-process-output (string)
  "Subroutine of proof-shell-filter to process output STRING.

Appropriate action is taken depending on the what
proof-shell-process-output returns: maybe handle an interrupt, an
error, or deal with ordinary output which is a candidate for the goal
or response buffer.  Ordinary output is only displayed when the proof
action list becomes empty, to avoid a confusing rapidly changing
output.

After processing the current output, the last step undertaken
by the filter is to send the next command from the queue."
  (let (cmd res)
    (setq cmd (nth 1 (car proof-action-list)))
    (save-excursion		;current-buffer
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
       ;; Otherwise, it's an 'insert or 'analyse indicator,
       ;; but we don't act on it unless all the commands
       ;; in the queue region have been processed.
       (t (if (proof-shell-exec-loop)
	      (proof-shell-handle-delayed-output)))))))


(defun proof-shell-dont-show-annotations (&optional buffer)
  "Set display values of annotations in BUFFER to be invisible.

Annotations are characters 128-255."
  (interactive)
  (with-current-buffer (or buffer (current-buffer))
    (let ((disp (make-display-table))
	  (i 128))
      (while (< i 256)
	(aset disp i [])
	(incf i))
      (cond ((fboundp 'add-spec-to-specifier)
	     (add-spec-to-specifier current-display-table disp (current-buffer)))
	    ((boundp 'buffer-display-table)
	     (setq buffer-display-table disp))))))

(defun proof-shell-show-annotations ()
  "Remove display table specifier from current buffer.
This function is for testing purposes only, to reveal 8-bit characters
in the shell buffer.  Use proof-shell-dont-show-annotations to turn
them off again.
XEmacs only."
  (interactive)
  (remove-specifier current-display-table (current-buffer)))

  


;;
;; proof-shell-invisible-command: used to implement user-level commands.
;;

;;;###autoload
(defun proof-shell-wait (&optional timeout)
  "Busy wait for proof-shell-busy to become nil, or for TIMEOUT seconds.
Needed between sequences of commands to maintain synchronization,
because Proof General does not allow for the action list to be extended
in some cases.   May be called by proof-shell-invisible-command."
  (while proof-shell-busy
    (accept-process-output nil timeout)
    (sit-for 0)))


(defun proof-done-invisible (span)
  "Callback for proof-shell-invisible-command.  
Calls proof-state-change-hook."
  (run-hooks 'proof-state-change-hook))

; new code to go in after 3.0
;(defun proof-done-invisible (&optional span)
;  "Callback for proof-shell-invisible-command.  
;Calls proof-state-change-hook."
;  (run-hooks 'proof-state-change-hook)
;  (remove-hook 'proof-shell-handle-error-or-interrupt-hook
;	       'proof-shell-invisible-hook-fn))
;; Seems to be hard to write this stuff without a temporary variable
;; (or higher-order functions, sob).
;(defun proof-shell-invisible-hook-fn ()
;  "Temporary function holding hook for proof-shell-invisible-command.")

;(defmacro proof-shell-invisible-failure-msg (errormsg)
;  "Construct a value for `proof-shell-handle-error-or-interrupt-hook'.
;Give error message ERRORMSG, then remove self from queue."
;  `(lambda ()
;     (proof-done-invisible)
;     (error ,(eval errormsg))))

;(defmacro proof-shell-invisible-failure-fn (fn)
;  "Construct a value for `proof-shell-handle-error-or-interrupt-hook'.
;Call function fn, then remove self from queue."
;  `(lambda ()
;     (proof-done-invisible)
;     (,(eval fn))))
;
; extra arg ERRORMSGFN to proof-shell-invisible-command:
;
;If ERRORMSGFN is non-nil, if the command leads to an error or interrupt
;in the proof assistant, we will give an error.  If ERRORMSGFN
;is a string, (error ERRORMSGFN) is called; if ERRORMSGFN is a function, 
;it is called directly.  If ERRORMSGFN is not a string or function,
;we will give standard error messages for interrupts and errors."
;
; Other (sensible) possibility is to call
; proof-shell-handle-error-or-interrupt-hook with span as argument.

;;;###autoload
(defun proof-shell-invisible-command (cmd &optional wait)
  "Send CMD to the proof process.  
Automatically add proof-terminal-char if necessary, examining
proof-shell-no-auto-terminate-commands.
By default, let the command be processed asynchronously.
But if optional WAIT command is non-nil, wait for processing to finish
before and after sending the command.
If WAIT is an integer, wait for that many seconds afterwards."
  (unless (or (null proof-terminal-char)
	      (not proof-shell-auto-terminate-commands)
	      (string-match (concat
			     (regexp-quote
			      (char-to-string proof-terminal-char))
			     "[ \t]*$") cmd))
    (setq cmd (concat cmd (char-to-string proof-terminal-char))))
  (if wait (proof-shell-wait))
  (proof-shell-ready-prover)		; start proof assistant; set vars.
  (proof-start-queue nil nil
		     (list (proof-shell-command-queue-item 
			    cmd 'proof-done-invisible)))
  (if wait (proof-shell-wait (if (numberp wait) wait))))







;;
;; Proof General shell mode definition
;;


(eval-and-compile			; to define vars
;;; NB: autoload tag below doesn't work for d-d-m, autoload is in proof.el
;;;###autoload
(define-derived-mode proof-shell-mode comint-mode 
  "proof-shell" "Proof General shell mode class for proof assistant processes"
  (setq proof-buffer-type 'shell)
  
  ;; Clear state
  (setq proof-shell-busy nil
	proof-shell-delayed-output (cons 'insert "done")
	proof-shell-proof-completed nil
	;; FIXME: these next two probably not necessary
	proof-shell-error-or-interrupt-seen nil
	proof-action-list nil)

  (make-local-variable 'proof-shell-insert-hook)

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
  (proof-shell-dont-show-annotations)

  ;; Proof marker is initialised in filter to first prompt found
  (setq proof-marker (make-marker))
  ;; Urgent message marker records end position of last urgent
  ;; message seen.
  (setq proof-shell-urgent-message-marker (make-marker))
  ;; Urgent message scan marker records starting position to 
  ;; scan for urgent messages from
  (setq proof-shell-urgent-message-scanner (make-marker))
  (set-marker proof-shell-urgent-message-scanner (point-min))

  ;; easy-menu-add must be in the mode function for XEmacs.
  (easy-menu-add proof-shell-mode-menu proof-shell-mode-map)

  ;; [ Should already be in proof-goals-buffer, really.]

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
  ))

;; watch difference with proof-shell-menu, proof-shell-mode-menu.
(defvar proof-shell-menu proof-shared-menu
  "The menu for the Proof-assistant shell.")

(easy-menu-define proof-shell-mode-menu
		  proof-shell-mode-map
		  "Menu used in Proof General shell mode."
		  (cons proof-general-name proof-shell-menu))


;;
;; Sanity checks on important settings
;;

(defconst proof-shell-important-settings
  '(proof-shell-annotated-prompt-regexp ; crucial
    ))


(defun proof-shell-config-done ()
  "Initialise the specific prover after the child has been configured.
Every derived shell mode should call this function at the end of
processing."
  (save-excursion			
    (set-buffer proof-shell-buffer)

    ;; Give warnings if some crucial settings haven't been made
    (dolist (sym proof-shell-important-settings)
      (proof-warn-if-unset "proof-shell-config-done" sym))

    ;; We do not enable font-lock here, it's a waste of cycles.
    ;; (proof-font-lock-configure-defaults)

    (let ((proc (get-buffer-process proof-shell-buffer)))
      ;; Add the kill buffer function and process sentinel
      (make-local-hook 'kill-buffer-hook)
      (add-hook 'kill-buffer-hook 'proof-shell-kill-function t t)
      (set-process-sentinel proc 'proof-shell-bail-out)

      ;; Pre-sync initialization command.  This is necessary
      ;; for proof assistants which change their output modes
      ;; only after some initializations.
      (if proof-shell-pre-sync-init-cmd
	  (proof-shell-insert proof-shell-pre-sync-init-cmd 'init-cmd))

      ;; Flush pending output from startup (it gets hidden from the user)
      ;; while waiting for the prompt to appear
      (while (and (process-live-p proc)
		  (null (marker-position proof-marker)))
	(accept-process-output proc 1))

      (if (process-live-p proc)
	  (progn
	    ;; Send main intitialization command and wait for it to be
	    ;; processed.   Also ensure that proof-action-list is initialised. 
	    (setq proof-action-list nil)
	    (if proof-shell-init-cmd
		(proof-shell-invisible-command proof-shell-init-cmd t))
      
	    ;; Configure for x-symbol
	    (proof-x-symbol-shell-config))))))


;;
;; Response buffer mode
;; 

(eval-and-compile
(define-derived-mode proof-universal-keys-only-mode fundamental-mode
    proof-general-name "Universal keymaps only"
    ;; Doesn't seem to supress TAB, RET
    (suppress-keymap proof-universal-keys-only-mode-map 'all)
    (proof-define-keys proof-universal-keys-only-mode-map 
		       proof-universal-keys)))

(eval-and-compile
(define-derived-mode proof-response-mode proof-universal-keys-only-mode
  "PGResp" "Responses from Proof Assistant"
  (setq proof-buffer-type 'response)
  (define-key proof-response-mode-map [q] 'bury-buffer)
  (easy-menu-add proof-response-mode-menu proof-response-mode-map)
  (setq proof-shell-next-error nil)	; all error msgs lost!
  (erase-buffer)))

(easy-menu-define proof-response-mode-menu
		  proof-response-mode-map
		  "Menu for Proof General response buffer."
		  (cons proof-general-name proof-shared-menu))

(defun proof-response-config-done ()
  "Initialise the response buffer after the child has been configured."
  (save-excursion
    (set-buffer proof-response-buffer)
    (proof-font-lock-configure-defaults)
    (proof-x-symbol-configure)))


;;
;; Goals buffer mode
;;


(eval-and-compile			; to define proof-goals-mode-map
(define-derived-mode proof-goals-mode proof-universal-keys-only-mode
  proof-general-name 
  "Mode for goals display.  
May enable proof-by-pointing or similar features.
\\{proof-goals-mode-map}"
  ;; defined-derived-mode proof-goals-mode initialises proof-goals-mode-map
  (setq proof-buffer-type 'goals)
  (cond 
   (proof-running-on-XEmacs
    (define-key proof-goals-mode-map [(button2)] 'pbp-button-action)
    (define-key proof-goals-mode-map [(control button2)] 'proof-undo-and-delete-last-successful-command)
    ;; button 2 is a nuisance on 2 button mice, so we'll do 1 as well.
    ;; Actually we better hadn't, people like to use it for cut and paste.
    ;; (define-key proof-goals-mode-map [(button1)] 'pbp-button-action)
    ;; (define-key proof-goals-mode-map [(control button1)] 'proof-undo-and-delete-last-successful-command)
    (define-key proof-goals-mode-map [(button3)] 'pbp-yank-subterm))
   (t
    (define-key proof-goals-mode-map [mouse-2] 'pbp-button-action)
    (define-key proof-goals-mode-map [C-mouse-2] 'proof-undo-and-delete-last-successful-command)
    ;; (define-key proof-goals-mode-map [mouse-1] 'pbp-button-action)
    ;; (define-key proof-goals-mode-map [C-mouse-1] 'proof-undo-and-delete-last-successful-command)
   (define-key proof-goals-mode-map [mouse-3] 'pbp-yank-subterm)))
  (define-key proof-goals-mode-map [q] 'bury-buffer)
  (easy-menu-add proof-goals-mode-menu proof-goals-mode-map)
  (erase-buffer)))

(easy-menu-define proof-goals-mode-menu
		  proof-goals-mode-map
		  "Menu for Proof General goals buffer."
		  (cons proof-general-name proof-shared-menu))

(defun proof-goals-config-done ()
  "Initialise the goals buffer after the child has been configured."
  (save-excursion
    (set-buffer proof-goals-buffer)
    (proof-font-lock-configure-defaults)
    (proof-x-symbol-configure)))


;; 
;; Multiple frames for goals and response buffers
;;
;;  -- because who's going to bother do this by hand?
;;

(defvar proof-shell-special-display-regexp nil
  "Regexp for special-display-regexps for multiple frame use.
Internal variable, setting this will have no effect!")

(defun proof-multiple-frames-enable ()
  (cond
   (proof-multiple-frames-enable
    (setq special-display-regexps
	  (union special-display-regexps 
		 (list proof-shell-special-display-regexp)))
    ;; If we're on XEmacs with toolbar, turn off toolbar and
    ;; menubar for the small frames to save space.
    ;; FIXME: this could be implemented more smoothly
    ;; with property lists, and specifiers should perhaps be set
    ;; for the frame rather than the buffer.  Then could disable
    ;; minibuffer, too.
    (if (featurep 'toolbar) 
	(progn
	  (proof-with-current-buffer-if-exists 
	   proof-response-buffer
	   (set-specifier default-toolbar-visible-p nil (current-buffer))
	   ;; (set-specifier minibuffer (minibuffer-window) (current-buffer))
	   (set-specifier has-modeline-p nil (current-buffer))
	   (set-specifier menubar-visible-p nil (current-buffer)))
	  (proof-with-current-buffer-if-exists 
	   proof-goals-buffer
	   (set-specifier default-toolbar-visible-p nil (current-buffer))
	   ;; (set-specifier minibuffer (minibuffer-window))
	   (set-specifier has-modeline-p nil (current-buffer))
	   (set-specifier menubar-visible-p nil (current-buffer)))))
    ;; Try to trigger re-display of goals/response buffers,
    ;; on next interaction.  
    ;; FIXME: would be nice to do the re-display here, rather
    ;; than waiting for next re-display
    (delete-other-windows 
     (if proof-script-buffer
	 (get-buffer-window proof-script-buffer t))))
   (t
    ;; FIXME: would be nice to kill off frames automatically,
    ;; but let's leave it to the user for now.
    (setq special-display-regexps
	  (delete proof-shell-special-display-regexp 
		  special-display-regexps)))))


;;
;; Next error function.
;; Added in 3.2
;;

(defvar proof-shell-next-error nil
  "Error counter in response buffer to count for next error message.")

;;;###autoload
(defun proof-next-error (&optional argp)
  "Jump to location of next error reported in the response buffer.

A prefix arg specifies how many error messages to move;
negative means move back to previous error messages.
Just C-u as a prefix means reparse the error message buffer
and start at the first error."
  (interactive "P")
  (if (and ;; At least one setting must be configured
       proof-shell-next-error-regexp
       ;; Response buffer must be live
       (or
	(buffer-live-p proof-response-buffer)
	(error "proof-next-error: no response buffer to parse!")))
      (let ((wanted-error    (or (and (not (consp argp))
				      (+ (prefix-numeric-value argp)
					 (or proof-shell-next-error 0)))
				 (and (consp arg) 1)
				 (or proof-shell-next-error 1)))
	    line column file errpos)
	(set-buffer proof-response-buffer)
	(goto-char (point-min))
	(if (re-search-forward proof-shell-next-error-regexp 
			       nil t wanted-error)
	    (progn
	      (setq errpos (save-excursion
			     (goto-char (match-beginning 0))
			     (beginning-of-line)
			     (point)))
	      (setq line (match-string 2)) ; may be unset
	      (if line (setq line (string-to-int line)))
	      (setq column (match-string 3)) ; may be unset
	      (if column (setq column (string-to-int column)))
	      (setq proof-shell-next-error wanted-error)
	      (if (and
		   proof-shell-next-error-filename-regexp
		     ;; Look for the most recently mentioned filename
		     (re-search-backward
		      proof-shell-next-error-filename-regexp nil t))
		    (setq file 
			  (if (file-exists-p (match-string 2))
			      (match-string 2)
			    ;; May need post-processing to extract filename
			    (if proof-shell-next-error-extract-filename
				(format 
				 proof-shell-next-error-extract-filename 
				 (match-string 2))))))
		;; Now find the other buffer we need to display
		(let*
		    ((errbuf	
		      (if file
			  (find-file-noselect file)
			(or proof-script-buffer 
			    ;; We could make more guesses here,
			    ;; e.g. last script buffer active 
			    ;; (keep a record of it?)
			    (error 
			     "proof-next-error: can't guess file for error message"))))
		     (pop-up-windows t)
		     (rebufwindow
		      (or (get-buffer-window proof-response-buffer 'visible)
			  ;; Pop up a window.
			  (display-buffer proof-response-buffer))))
		  ;; Make sure the response buffer stays where it is,
		  ;; and make sure source buffer is visible
		  (select-window rebufwindow)
		  (pop-to-buffer errbuf)
		  ;; Display the error message in the response buffer
		  (set-window-point rebufwindow errpos)
		  (set-window-start rebufwindow errpos)
		  ;; Find the error location in the error buffer
		  (set-buffer errbuf)
		  ;; FIXME: no handling of selective display here
		  (goto-line line)
		  (if (and column (> column 1))
		      (move-to-column (1- column)))))
	    (setq proof-shell-next-error nil)
	    (error "proof-next-error: couldn't find next error.")))))

   


(provide 'proof-shell)
;; proof-shell.el ends here.
