;; proof-shell.el  Major mode for proof assistant script files.
;;
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

;; FIXME: needed because of menu definitions, which should
;; be factored out into proof-menus.  Then require here is
;; just on proof-shell.
(require 'proof-script)			

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
(eval-when-compile
  (mapcar (lambda (f) 
	    (autoload f "proof-script"))
	  '(proof-goto-end-of-locked
	    proof-insert-pbp-command
	    proof-detach-queue 
	    proof-locked-end 
	    proof-set-queue-endpoints
	    proof-file-to-buffer 
	    proof-register-possibly-new-processed-file
	    proof-restart-buffers)))

;; FIXME:
;; Some variables from proof-shell are also used, in particular,
;; the menus.  These should probably be moved out to proof-menu.

;;
;; Internal variables used by shell mode
;;

(defvar proof-re-end-of-cmd nil 
  "Regexp matching end of command.  Based on proof-terminal-string.
Set in proof-shell-mode.")

(defvar proof-re-term-or-comment nil 
  "Regexp matching terminator, comment start, or comment end.
Set in proof-shell-mode.")

(defvar proof-marker nil 
  "Marker in proof shell buffer pointing to previous command input.")

(defvar proof-action-list nil
  "A list of

  (SPAN,COMMAND,ACTION)

triples, which is a queue of things to do.
See the functions proof-start-queue and proof-exec-loop.")




;;
;; Implementing the process lock
;;
;; da: In fact, there is little need for a lock.  Since Emacs Lisp
;; code is single-threaded, a loop parsing process output cannot get
;; pre-empted by the user trying to send more input to the process,
;; or by the process filter trying to deal with more output.
;;
;;

;;
;; History of these horrible functions.
;;
;;  proof-check-process-available
;;    Checks whether the proof process is available.
;; Specifically:
;;     (1) Is a proof process running?
;;     (2) Is the proof process idle?
;;     (3) Does the current buffer own the proof process?
;;     (4) Is the current buffer a proof script?
;; It signals an error if at least one of the conditions is not
;; fulfilled. If optional arg RELAXED is set, only (1) and (2) are 
;; tested.
;;
;; Later, proof-check-process-available was altered to also
;; start a proof shell if necessary, although this is also
;; done (later?) in proof-grab-lock.  It was also altered to
;; perform configuration for switching scripting buffers.
;;
;; Now, we have two functions again:
;;
;;  proof-shell-ready-prover   
;;    starts proof shell, gives error if it's busy.
;;
;;  proof-activate-scripting  (in proof-script.el)
;;    turns on scripting minor mode for current (scripting) buffer.
;;
;; Also, a new enabler predicate:
;;  
;;  proof-shell-available
;;    returns non-nil if a proof shell is active and not locked.
;;
;; Maybe proof-shell-ready-prover doesn't need to start the shell,
;; we can find that out later.
;;
;; Chasing down 'relaxed' flags:
;;
;;   was passed into proof-grab by proof-start-queue
;;    only call to proof-start-queue with this arg is in
;;    proof-shell-invisible-command.
;;   only call of proof-shell-invisible-command with relaxed arg
;;   is in proof-execute-minibuffer-cmd.
;;  --- presumably so that command could be executed from any
;;  buffer, not just a scripting one?
;;
;;  I think it's wrong for proof-shell-invisible-command to enforce
;;  scripting buffer!
;; 
;;  This is reflected now by just calling (proof-shell-ready-prover)
;;  in proof-shell-invisible-command, not proof-check-process-available.
;;
;; Hopefully we can get rid of these messy 'relaxed' flags now.
;;
;;  -da.

(defun proof-shell-ready-prover ()
  "Make sure the proof assistant is ready for a command"
  (proof-shell-start)
  (if proof-shell-busy (error "Proof Process Busy!")))

(defun proof-shell-live-buffer ()
  "Return buffer of active proof assistant, or nil if none running."
  (and proof-shell-buffer
       (comint-check-proc proof-shell-buffer)
       (buffer-live-p proof-shell-buffer)))

(defun proof-shell-available-p ()
  "Returns non-nil if there is a proof shell active and available.
No error messages.  Useful as menu or toolbar enabler."
  (and (proof-shell-live-buffer)
       (not proof-shell-busy)))

;; FIXME: note: removed optional 'relaxed' arg
(defun proof-grab-lock ()
  "Grab the proof shell lock."
  (proof-shell-ready-prover)
  (setq proof-shell-busy t))

(defun proof-release-lock ()
  "Release the proof shell lock."
  ; da: this test seems somewhat worthless
  ; (if (proof-shell-live-buffer)
  ; (progn
	; da: Removed this so that persistent users are allowed to
	; type in the process buffer without being hassled.
	;(if (not proof-shell-busy)
	;    (error "Bug in proof-release-lock: Proof process not busy"))
	; da: Removed this now since some commands run from other
	; buffers may claim process lock.
	; (if (not (eq (current-buffer) proof-script-buffer))
	; (error "Bug in proof-release-lock: Don't own process"))
  (setq proof-shell-busy nil))



;;
;;  Starting and stopping the proof shell  
;;

(defun proof-shell-start ()
  "Initialise a shell-like buffer for a proof assistant.

Also generates goal and response buffers.
Does nothing if proof assistant is already running."
  (interactive)
  (if (proof-shell-live-buffer)
      ()
    (run-hooks 'proof-pre-shell-start-hook)
    (setq proof-included-files-list nil)
    (if proof-prog-name-ask
	(save-excursion
	  (setq proof-prog-name (read-shell-command "Run process: "
						    proof-prog-name))))
    ;; FIXME da: why do we need this?  We never have more than
    ;; one proof shell running at a time.  We might as well
    ;; kill off the old buffer anyway.
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
	      " ")))
	(apply 'make-comint  (append (list proc (car prog-name-list) nil)
				     (cdr prog-name-list))))
      
      ;; Create the associated buffers and set buffer variables
      (setq proof-shell-buffer (get-buffer (concat "*" proc "*"))
	    proof-goals-buffer (get-buffer-create (concat "*" proc "-goals*"))
	    proof-response-buffer (get-buffer-create (concat "*" proc
	    "-response*")))
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
	      (funcall proof-mode-for-pbp))
	  (switch-to-buffer proof-shell-buffer)
	  (error "%s process exited!" proc)))
      (message 
       (format "Starting %s process... done." proc)))))


;;
;; Indicator and fake minor mode for active scripting buffer
;; 

(defcustom proof-shell-active-scripting-indicator
  (if (string-match "XEmacs" emacs-version)
      (cons (make-extent nil nil) " Scripting ")
    " Scripting")
  "Modeline indicator for active scripting buffer.
If first component is extent it will automatically follow the colour
of the queue region."
  :type 'sexp
  :group 'proof-general-internals)

(cond
 ((string-match "XEmacs" emacs-version)
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
Value for kill-buffer-hook in shell buffer.
Attempt to shut down the proof process nicely and
clears up all the locked regions and state variables."
  (let* ((alive    (comint-check-proc (current-buffer)))
	 (proc      (get-buffer-process (current-buffer)))
	 (bufname   (buffer-name)))
    (message "%s, cleaning up and exiting..." bufname)
    (sit-for 0)				; redisplay
    (if alive				; process still there
	(progn
	  ;; Try to shut it down politely
	  ;; Do this before deleting other buffers, etc, so that
	  ;; any closing down processing works okay.
	  (if proof-shell-quit-cmd
	      (comint-send-string proc
				  (concat proof-shell-quit-cmd "\n"))
	    (comint-send-eof))
	  ;; Wait a while for it to die before killing
	  ;; it off more rudely.
	  (set-process-sentinel proc
				(lambda (p m) (throw 'exited t)))
	  (catch 'exited
	    (accept-process-output nil 10)
	    (kill-process proc)
	    ;; another chance to catch
	    (accept-process-output))))
    ;; Restart all scripting buffers
    (proof-script-remove-all-spans-and-deactivate)
    ;; Clear state
    (setq proof-included-files-list nil
	  proof-shell-busy nil
	  proof-shell-proof-completed nil)
    ;; Kill buffers associated with shell buffer
    (if (buffer-live-p proof-goals-buffer)
	(kill-buffer proof-goals-buffer))
    (if (buffer-live-p proof-response-buffer)
	(kill-buffer proof-response-buffer))
    (message "%s exited." bufname)))


(defun proof-shell-exit ()
  "Query the user and exit the proof process.

This simply kills the proof-shell-buffer relying on the hook function
proof-shell-kill-function to do the hard work."
  (interactive)
  (if (buffer-live-p proof-shell-buffer)
      (if (yes-or-no-p (format "Exit %s process? " proof-assistant))
	  (kill-buffer proof-shell-buffer)
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
deactivated.  The restart command should re-synchronize
Proof General with the proof assitant."
  (interactive)
  (proof-script-remove-all-spans-and-deactivate)
  (setq proof-included-files-list nil
	proof-shell-busy nil
	proof-shell-proof-completed nil)
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

;; FIXME da: this is an oddity.  Was bound by default to
;; control - button1, I've turned it off.
(defun proof-send-span (event)
  (interactive "e")
  (let* ((span (span-at (mouse-set-point event) 'type))
	 (str  (if span (span-property span 'cmd))))
    (cond ((and (eq (current-buffer) proof-script-buffer)
		(not (null span)))
	   (proof-goto-end-of-locked)
	   (cond ((eq (span-property span 'type) 'vanilla)
		  (insert str)))))))

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




;;
;; Flag and function to keep response buffer tidy.
;;
(defvar proof-shell-erase-response-flag nil
  "Indicates that the response buffer should be cleared before next message.")

(defun proof-shell-maybe-erase-response
  (&optional erase-next-time clean-windows force)
  "Erase the response buffer according to proof-shell-erase-response-flag.
ERASE-NEXT-TIME is the new value for the flag.
If CLEAN-WINDOWS is set, use proof-clear-buffer to do the erasing.
If FORCE, override proof-shell-erase-response-flag."
  (if (or proof-shell-erase-response-flag force)
      (if clean-windows
	  (proof-clean-buffer proof-response-buffer)
	;; NB: useful optional arg to erase buffer is XEmacs specific, 8-(.
	;; (erase-buffer proof-response-buffer)
	(with-current-buffer proof-response-buffer
	  (erase-buffer))))
  (setq proof-shell-erase-response-flag erase-next-time))
		  


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

This is a list of tuples of the form (type . string). type is either
'analyse or 'insert. 

'analyse denotes that string's term structure  ought to be analysed
         and displayed in the `proof-goals-buffer'
'insert  denotes that string ought to be displayed in the
         `proof-response-buffer' ")

(defun proof-shell-analyse-structure (string)
  "Analyse the term structure of STRING and display it in proof-goals-buffer."
  (save-excursion
    (let* ((ip 0) (op 0) ap (l (length string)) 
	   (ann (make-string (length string) ?x))
           (stack ()) (topl ()) 
	   (out (make-string l ?x)) c span)

      ;; Form output string by removing characters 
      ;; 128 or greater.
      (while (< ip l)	
	(if (< (setq c (aref string ip)) 128)
	    (progn (aset out op c)
		   (incf op)))
	(incf ip))

      ;; Response buffer may be out of date. It may contain (error)
      ;; messages relating to earlier proof states
      
      ;; FIXME da: this isn't always the case.  In Isabelle
      ;; we get <WARNING MESSAGE> <CURRENT GOALS> output,
      ;; or <WARNING MESSAGE> <ORDINARY MESSAGE>.  Both times
      ;; <WARNING MESSAGE> would be relevant.
      ;; We should only clear the output that was displayed from
      ;; the *previous* prompt.

      ;; da: I get a lot of empty response buffers displayed
      ;; which might be nicer removed. Temporary test for
      ;; this clean-buffer to see if it behaves well.

      ;; NEW!!
      ;; Erase the response buffer if need be, maybe also removing the
      ;; window.  Indicate that it should be erased before the next output.
      (proof-shell-maybe-erase-response t t)

      (set-buffer proof-goals-buffer)
      ;; NEW!!  10.12.98 Keep point at beginning of buffer instead
      ;; of end.  Might be nicer to keep it at "current" subgoal
      ;; a la Isamode, but never mind.
      (erase-buffer)
      (insert (substring out 0 op))
      (proof-display-and-keep-buffer proof-goals-buffer (point-min))

      ;; FIXME: 
      ;; This code is broken for Emacs 20.3 which has 16 bit
      ;; character codes.  (Despite earlier attempts to make
      ;; character codes in this buffer 8 bit)
      ;; But this is a more general problem in Proof General
      ;; which requires re-engineering all this 128 mess.
      (unless
	  ;; Don't do it for Emacs 20.3 or any version which
	  ;; has this suspicious function.
	  (fboundp 'toggle-enable-multibyte-characters)
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
	(while (setq ip (car topl) 
		     topl (cdr topl))
	  (pbp-make-top-span ip (car topl)))))))

(defun proof-shell-strip-annotations (string)
  "Strip special annotations from a string, returning cleaned up string.
Special annotations are characters with codes higher than
'proof-shell-first-special-char'."
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
  "Displays output from `proof-shell-buffer' in `proof-response-buffer'.
The region in `proof-shell-buffer begins with the match for START-REGEXP
and is delimited by END-REGEXP. The match for END-REGEXP is not
part of the specified region.
Returns the string (with faces) in the specified region."
  (let (start end string)
    (save-excursion
      (set-buffer proof-shell-buffer)
      (goto-char (point-max))
      (setq start (search-backward-regexp start-regexp))
      (setq end (- (search-forward-regexp end-regexp)
				   (length (match-string 0))))
      (setq string
	    (proof-shell-strip-annotations (buffer-substring start end))))
    ;; Erase if need be, and erase next time round too.
    (proof-shell-maybe-erase-response t nil)
    (proof-response-buffer-display string append-face)))

(defun proof-shell-handle-delayed-output ()
  "Display delayed output.
This function expects 'proof-shell-delayed-output' to be a cons cell
of the form '(insert . txt) or '(analyse . txt).
See the documentation for `proof-shell-delayed-output' for further details."
  (let ((ins (car proof-shell-delayed-output))
	(str (cdr proof-shell-delayed-output)))
    (cond 
     ((eq ins 'insert)
       ; (unless (string-equal str "done") ;; FIXME da: nasty, breaks something?
	(setq str (proof-shell-strip-annotations str))
	(with-current-buffer proof-response-buffer
	  ;; FIXME da: have removed this, possibly it junks 
	  ;; relevant messages.  Instead set a flag to indicate
	  ;; that response buffer should be cleared before the
	  ;; next command.
	  ;; (erase-buffer)

	  ;; NEW!
	  ;; Erase the response buffer if need be, and indicate that
	  ;; it is to be erased again before the next message.
	  (proof-shell-maybe-erase-response t nil)
	  (insert str)
	  (proof-display-and-keep-buffer proof-response-buffer)))
     ((eq ins 'analyse)
      (proof-shell-analyse-structure str))
     (t (assert nil))))
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
Called with shell buffer current.
We first flush unprocessed goals to the goals buffer.
The error message is displayed in the `proof-response-buffer'.
Then we call `proof-shell-handle-error-hook'. "

  ;; flush goals
  (or (equal proof-shell-delayed-output (cons 'insert "Done."))
      (save-excursion ;current-buffer
	(set-buffer proof-goals-buffer)
	(erase-buffer)
	(insert (proof-shell-strip-annotations 
		   (cdr proof-shell-delayed-output)))
	(proof-display-and-keep-buffer proof-goals-buffer)))

  ;; This prevents problems if the user types in the
  ;; shell buffer: without it the same error is seen by
  ;; the proof-shell filter over and over.
  (setq proof-action-list nil)

  ;; Perhaps we should erase the buffer in proof-response-buffer, too?

    ;; We extract all text between text matching
    ;; `proof-shell-error-regexp' and the following prompt.
    ;; Alternatively one could higlight all output between the
    ;; previous and the current prompt.
    ;; +/- of our approach
    ;; + Previous not so relevent output is not highlighted
    ;; - Proof systems have to conform to error messages whose start can be
    ;;   detected by a regular expression.
  (proof-shell-handle-output
   proof-shell-error-regexp proof-shell-annotated-prompt-regexp
   'proof-error-face)

  
  (save-excursion ;current-buffer
    (proof-display-and-keep-buffer proof-response-buffer)
		  (beep)

		  ;; unwind script buffer
		  (if proof-script-buffer
		      (with-current-buffer proof-script-buffer
			(proof-detach-queue)
			(delete-spans (proof-locked-end) (point-max) 'type)))
		  (proof-release-lock)
		  (run-hooks 'proof-shell-handle-error-hook)))

;; FIXME da: this function is a mess.
(defun proof-shell-handle-interrupt ()
  (save-excursion 
    (set-buffer proof-goals-buffer)
    (display-buffer proof-goals-buffer)
    (goto-char (point-max))
    (newline 2)
    (insert-string 
     "Interrupt: Script Management may be in an inconsistent state\n")
    (beep)
    (if proof-script-buffer
	(set-buffer proof-script-buffer)))
  (if proof-shell-busy
      (progn (proof-detach-queue)
	     (setq proof-action-list nil)
	     (delete-spans (proof-locked-end) (point-max) 'type)
	     (proof-release-lock))))

(defun proof-goals-pos (span maparg)
  "Given a span, this function returns the start of it if corresponds
  to a goal and nil otherwise."
 (and (eq 'goal (car (span-property span 'proof-top-element)))
		(span-start span)))

(defun proof-pbp-focus-on-first-goal ()
  "If the `proof-goals-buffer' contains goals, the first one is brought
  into view."
  (and (fboundp 'map-extents)
       (let
	   ((pos (map-extents 'proof-goals-pos proof-goals-buffer
			      nil nil nil nil 'proof-top-element)))
	 (and pos (set-window-point
		   (get-buffer-window proof-goals-buffer t) pos)))))

           

(defun proof-shell-process-output (cmd string)
  "Process shell output (resulting from CMD) by matching on STRING.
CMD is the first part of the proof-action-list that lead to this
output.
This function deals with errors, start of proofs, abortions of
proofs and completions of proofs. All other output from the proof
engine is simply reported to the user in the response buffer
by setting proof-shell-delayed-output to a cons 
cell of (INSERT . TEXT) where TEXT is the text to be inserted.

To extend this function, set
proof-shell-process-output-system-specific.

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
    (proof-clean-buffer proof-goals-buffer)
   (setq proof-shell-delayed-output (cons 'insert "\nAborted\n"))
    ())
	 
   ((string-match proof-shell-proof-completed-regexp string)
    (proof-clean-buffer proof-goals-buffer)
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

(defvar proof-shell-insert-space-fudge 
  (if (string-match "XEmacs" emacs-version) "" " ")
  "String to insert after setting proof marker to prevent it moving.
Fixes a bug/problem with FSF Emacs.")

(defun proof-shell-insert (string)
  "Insert STRING at the end of the proof shell, call comint-send-input.
First call proof-shell-insert-hook. Then strip STRING of carriage
returns before inserting it and updating proof-marker to point to 
the end of the newly inserted text.
NB: This means that any output received up til now but not 
processed by the proof-shell-filter will be lost!   We must be
careful to synchronize with the process.  This function is used 
particularly in proof-start-queue and proof-shell-exec-loop."
  (save-excursion
    (set-buffer proof-shell-buffer)
    (goto-char (point-max))

    ;; Lego uses this hook for setting the pretty printer
    ;; width, Coq uses it for sending an initialization string
    ;; (although it could presumably use proof-shell-init-cmd?).
    ;; Paul Callaghan wants to use this hook to massage STRING
    ;; to remove literate-style markup from input. 
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
    (set-marker proof-marker (point))
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



; Pass start and end as nil if the cmd isn't in the buffer.

;; FIXME: note: removed optional 'relaxed' arg
(defun proof-start-queue (start end alist)
  "Begin processing a queue of commands in ALIST.
If START is non-nil, START and END are buffer positions in the
active scripting buffer for the queue region."
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
	  (proof-grab-lock) 
	  (setq proof-shell-delayed-output (cons 'insert "Done."))
	  (setq proof-action-list alist)
	  (proof-shell-insert (nth 1 item))))))

; returns t if it's run out of input


;; 
;; The loop looks like: Execute the
; command, and if it's successful, do action on span.  If the
; command's not successful, we bounce the rest of the queue and do
; some error processing.

(defun proof-shell-exec-loop () 
  "Process the proof-action-list.

`proof-action-list' contains a list of (SPAN COMMAND ACTION) triples.

If this function is called with a non-empty proof-action-list, the
head of the list is the previously executed command which succeeded.
We execute (ACTION SPAN) on the first item, then (ACTION SPAN) on
any following items which have proof-no-command as their cmd
components.  If a there is a next command, send it to the process.
If the action list becomes empty, unlock the process and remove the
queue region. 

The return value is non-nil if the action list is now empty."
  (or (not proof-action-list)		; exit immediately if finished.
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
	  ;; If action list is empty now, release the process lock
	  (if (null proof-action-list)
	      (progn (proof-release-lock)
		     (proof-detach-queue)
		     ;; indicate finished
		     t)
	    ;; Send the next command to the process
	    (proof-shell-insert (nth 1 item))
	    ;; indicate not finished
	    nil)))))

;; FIXME da: some places in the code need to be made robust in
;; case of buffer kills, etc, before callbacks.  Is this function
;; one?
(defun proof-shell-insert-loopback-cmd  (cmd)
  "Insert command sequence triggered by the proof process
at the end of locked region (after inserting a newline and indenting).
Assume proof-script-buffer is active."
  (save-excursion
    (set-buffer proof-script-buffer) 
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

;; FIXME: highlight eager annotation-end : fix proof-shell-handle-output
;; to highlight whole string.
;; FIXME da: this function seems to be dead
(defun proof-shell-popup-eager-annotation ()
  "Process urgent messages.
Eager annotations are annotations which the proof system produces
while it's doing something (e.g. loading libraries) to say how much
progress it's made. Obviously we need to display these as soon as they
arrive."
  (let ((str (proof-shell-handle-output
	      proof-shell-eager-annotation-start
	      proof-shell-eager-annotation-end
	      'proof-eager-annotation-face))
    (proof-shell-message str))))

(defun proof-files-to-buffers (filenames)
  "Converts a list of FILENAMES into a list of BUFFERS."
  (if (null filenames) nil
    (let* ((buffer (proof-file-to-buffer (car filenames)))
	  (rest (proof-files-to-buffers (cdr filenames))))
      (if buffer (cons buffer rest) rest))))

(defun proof-shell-process-urgent-message (message)
  "Analyse urgent MESSAGE for various cases.
Included file, retracted file, cleared response buffer, or
if none of these apply, display."

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
      ;;  module heading).
      (if (and file (not (string= file "")))
	  (proof-register-possibly-new-processed-file file))))

   ;; Is the prover retracting across files?
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

   ;; Is the prover asking Proof General to clear the response buffer?
   ((and proof-shell-clear-response-regexp
	 (string-match proof-shell-clear-response-regexp message)
	 proof-response-buffer)
    ;; Erase response buffer and possibly its windows.
    (proof-shell-maybe-erase-response nil t t))

   ;; Is the prover asking Proof General to clear the goals buffer?
   ((and proof-shell-clear-goals-regexp
	 (string-match proof-shell-clear-goals-regexp message)
	 proof-goals-buffer)
    ;; Erase goals buffer but and possibly its windows
    (proof-clean-buffer proof-goals-buffer))

   (t
    ;; We're about to display a message.  Clear the response buffer
    ;; if necessary, but don't clear it the next time.
    ;; Don't bother remove the window for the response buffer
    ;; because we're about to put a message in it.
    (proof-shell-maybe-erase-response nil nil)
    (proof-shell-message message)
    (proof-response-buffer-display message
				   'proof-eager-annotation-face))))

(defvar proof-shell-urgent-message-marker nil
  "Marker in proof shell buffer pointing to end of last urgent message.")

(defun proof-shell-process-urgent-messages ()
  "Scan the shell buffer for urgent messages.
Scanning starts from proof-shell-urgent-message-marker and processes
strings between eager-annotation-start and eager-annotation-end."
  (let ((pt (point)))
    (goto-char
     (or (marker-position proof-shell-urgent-message-marker) (point-min)))
    (let (end start)
      (while (re-search-forward proof-shell-eager-annotation-start nil t)
	(setq start (match-beginning 0))
	(if (setq end
		  (re-search-forward proof-shell-eager-annotation-end nil t))
	    (proof-shell-process-urgent-message
	     (proof-shell-strip-annotations (buffer-substring start end))))
	;; Set the marker to the end of the last message found, if any.
	;; Must take care to keep the marger behind the process marker
	;; otherwise no output is seen!  (insert-before-markers in comint)
	(if end
	    (set-marker
	     proof-shell-urgent-message-marker
	     (min end
		  (1- (process-mark (get-buffer-process (current-buffer)))))))
	))
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

 PROMPT INPUT
 OUTPUT-1
 URGENT-MESSAGE
 OUTPUT-2
 PROMPT

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
however, are always processed)."
  (save-excursion
    (and proof-shell-eager-annotation-start
	 (proof-shell-process-urgent-messages))
       
    (if (or
	 ;; Some proof systems can be hacked to have annotated prompts;
	 ;; for these we set proof-shell-wakeup-char to the annotation 
	 ;; special.  
	 (and proof-shell-wakeup-char
	      (string-match (char-to-string proof-shell-wakeup-char) str))
	 ;; Others may rely on a standard top-level (e.g. SML) whose
	 ;; prompt are difficult or impossible to hack.
	 ;; For those we must search in the buffer for the prompt.
	 t)
	(if (null (marker-position proof-marker))
	    ;; Initialisation of proof-marker:
	    ;; Set marker to after the first prompt in the
	    ;; output buffer if one can be found now.
	    (progn
	      (goto-char (point-min))
	      (if (re-search-forward proof-shell-annotated-prompt-regexp nil t)
		  (progn
		    (set-marker proof-marker (point))
		    ;; The first time a prompt is seen we ignore any 
		    ;; output that occured before it.  Process the
		    ;; action list to remove the first item if need
		    ;; be (proof-shell-init-cmd sent if 
		    ;; proof-shell-config-done).
		    (if proof-action-list
			(proof-shell-filter-process-output "")))))
	  ;; Now we're looking for the end of the piece of output
	  ;; which will be processed.  

          ;; Note that the way this filter works,
          ;; only one piece of output can be dealt with at a time
          ;; so we loose sync if there's more than one bit there.

	  ;; The blasphemous situation that the proof-action-list
	  ;; is empty is now quietly ignored so that users can
	  ;; type in the shell buffer without being screamed at.
	  ;; Also allows the process to output something for
	  ;; some other reason (perhaps it's just being chatty),
	  ;; although that could break the synchronization.
	  ;; Note that any "unexpected" output like this gets
	  ;; ignored.
	  (if proof-action-list
	      (let ((startpos (goto-char (marker-position proof-marker)))
		    (urgnt    (marker-position
			       proof-shell-urgent-message-marker))
		    string)
		;; Ignore any urgent messages that have already been 
		;; dealt with.  This loses in the case mentioned above.
		;; A more general way of doing this would be
		;; to filter out or delete the urgent messages which 
		;; have been processed already.  
		(if (and urgnt
			 (< (point) urgnt))
		    (setq startpos (goto-char urgnt)))
		;; Find next prompt.  
		(if (re-search-forward 
		     proof-shell-annotated-prompt-regexp nil t)
		    (progn
		      (backward-char (- (match-end 0) (match-beginning 0)))
		      (setq string (buffer-substring startpos (point)))
		      (goto-char (point-max))	; da: why?
		      (proof-shell-filter-process-output string)))))))))



(defun proof-shell-filter-process-output (string)
  "Subroutine of proof-shell-filter to process output STRING.

Appropriate action is taken depending on the what
proof-shell-process-output returns: maybe handle an interrupt, an
error, or deal with ordinary output which is a candidate for the goal
or response buffer.  Ordinary output is only displayed when the proof
action list becomes empty, to avoid a confusing rapidly changing
output."
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


(defun proof-shell-dont-show-annotations ()
  "Set display values of annotations in process buffer to be invisible.

Annotations are characters 128-255."
  (save-excursion
    (set-buffer proof-shell-buffer)
    (let ((disp (make-display-table))
	  (i 128))
      (while (< i 256)
	(aset disp i [])
	(incf i))
      (cond ((fboundp 'add-spec-to-specifier)
	     (add-spec-to-specifier current-display-table disp
				    proof-shell-buffer))
	    ((boundp 'buffer-display-table)
	     (setq buffer-display-table disp))))))


;;
;; proof-shell-invisible-command: used to implement user-level commands.
;;

(defun proof-shell-wait ()
  "Busy wait for proof-shell-busy to become nil.
Needed between sequences of commands to maintain synchronization,
because Proof General does not allow for the action list to be extended.
May be called by proof-shell-invisible-command."
  (while proof-shell-busy
    (accept-process-output)
    (sit-for 0)))


(defun proof-shell-done-invisible (span)
  "Callback for proof-shell-invisible-command.  Do nothing."
  ())

;; FIXME da: I find the name of this command misleading.
;; Nothing much is invisible really.  Old docstring was
;; also misleading.

(defun proof-shell-invisible-command (cmd &optional wait)
  "Send CMD to the proof process.
If optional WAIT command is non-nil, wait for processing to finish
before and after sending the command."
  (if wait (proof-shell-wait))
  (proof-shell-ready-prover)
  (if (not (string-match proof-re-end-of-cmd cmd))
      (setq cmd (concat cmd proof-terminal-string)))
  (proof-start-queue nil nil
		     (list (list nil cmd 'proof-shell-done-invisible)))
  (if wait (proof-shell-wait)))


  
  







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof General shell mode definition				    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OLD COMMENT: "This has to come after proof-mode is defined"

;;###autoload
(eval-and-compile			; to define vars
(define-derived-mode proof-shell-mode comint-mode 
  "proof-shell" "Proof General shell mode class for proof assistant processes"
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
  (proof-shell-dont-show-annotations)

  ;; Proof marker is initialised in filter to first prompt found
  (setq proof-marker (make-marker))
  ;; Urgent message marker defaults to (point-min) if unset.
  (setq proof-shell-urgent-message-marker (make-marker))

  (setq proof-re-end-of-cmd (concat "\\s_*" proof-terminal-string "\\s_*\\\'"))
  (setq proof-re-term-or-comment 
	(concat proof-terminal-string "\\|" (regexp-quote proof-comment-start)
		"\\|" (regexp-quote proof-comment-end)))
  
  ;; easy-menu-add must be in the mode function for XEmacs.
  (easy-menu-add proof-shell-mode-menu proof-shell-mode-map)

  ;; FIXME da: before entering proof assistant specific code,
  ;; we'd do well to check that process is actually up and
  ;; running now.  If not, call the process sentinel function
  ;; to display the buffer, and give an error.
  ;; (Problem to fix is that process can die before sentinel is set:
  ;;  it ought to be set just here, perhaps: but setting hook here
  ;;  had no effect for some odd reason).
  ))

;; watch difference with proof-shell-menu, proof-shell-mode-menu.
(defvar proof-shell-menu proof-shared-menu
  "The menu for the Proof-assistant shell")

(easy-menu-define proof-shell-mode-menu
		  proof-shell-mode-map
		  "Menu used in Proof General shell mode."
		  (cons proof-general-name (cdr proof-shell-menu)))



(defun proof-font-lock-minor-mode ()
  "Start font-lock as a minor mode in the current buffer."

  ;; setting font-lock-defaults explicitly is required by FSF Emacs
  ;; 20.2's version of font-lock
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(font-lock-keywords))
  (font-lock-set-defaults))

(defun proof-goals-config-done ()
  "Initialise the goals buffer after the child has been configured."
  (save-excursion
    (set-buffer proof-goals-buffer)
    (proof-font-lock-minor-mode)))


(defun proof-response-config-done ()
  "Initialise the response buffer after the child has been configured."
  (save-excursion
    (set-buffer proof-response-buffer)
    (proof-font-lock-minor-mode)))

(defun proof-shell-config-done ()
  "Initialise the specific prover after the child has been configured."
  (save-excursion
    (set-buffer proof-shell-buffer)
    (let ((proc (get-buffer-process proof-shell-buffer)))
      ;; Add the kill buffer function and process sentinel
      (make-local-hook 'kill-buffer-hook)
      (add-hook 'kill-buffer-hook 'proof-shell-kill-function t t)
      (set-process-sentinel proc 'proof-shell-bail-out)

      ;; Flush pending output from startup
      (accept-process-output proc 1)

      ;; If the proof process in invoked on a different machine e.g.,
      ;; for proof-prog-name="ssh fastmachine proofprocess", one needs
      ;; to adjust the directory. Perhaps one might even want to issue
      ;; this command whenever a new scripting buffer is active?

      ;; This is the last unsynchronized input to the process.
      ;; It would be better to synchronize it but then we lose
      ;; any startup messages from proof-shell-init-cmd.

      (if (and proof-shell-cd t) ;  proof-rsh-command)
 	  (proof-shell-insert
	   (format proof-shell-cd
		   ;; under Emacs 19.34 default-directory contains "~"
		   ;; which causes problems with LEGO's internal Cd
		   ;; command
		   (expand-file-name default-directory))))

      ;; Try to flush the output from the cd command.
      (accept-process-output proc 1)

      ;; Send intitialization command and wait for it to be
      ;; processed.   This also ensures proof-action-list is
      ;; initialised. 
      (if proof-shell-init-cmd
	  (proof-shell-invisible-command proof-shell-init-cmd t)))))

      ;; Set proof marker to current end of buffer
      ;; (temp hack for old code)
      ;;(set-marker proof-marker (point-max))))))

(eval-and-compile
(define-derived-mode proof-universal-keys-only-mode fundamental-mode
    proof-general-name "Universal keymaps only"
    (suppress-keymap proof-universal-keys-only-mode-map 'all)
    (proof-define-keys proof-universal-keys-only-mode-map proof-universal-keys)))

(eval-and-compile			; to define vars
(define-derived-mode pbp-mode proof-universal-keys-only-mode
  proof-general-name "Proof by Pointing"
  ;; defined-derived-mode pbp-mode initialises pbp-mode-map
  (setq proof-buffer-type 'pbp)
  ;; (define-key pbp-mode-map [(button2)] 'pbp-button-action)
  (erase-buffer)))

(eval-and-compile
(define-derived-mode proof-response-mode proof-universal-keys-only-mode
  "PGResp" "Responses from Proof Assistant"
  (setq proof-buffer-type 'response)
  (easy-menu-add proof-response-mode-menu proof-response-mode-map)))


(easy-menu-define proof-response-mode-menu
		  proof-response-mode-map
		  "Menu for Proof General response buffer."
		  (cons proof-general-name
			(cdr proof-shared-menu)))


(provide 'proof-shell)
;; proof-shell.el ends here.