;; pg-user.el   User level commands for Proof General
;;
;; Copyright (C) 2000-2002 LFCS Edinburgh. 
;; Author:     David Aspinall and others
;; License:    GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;

(require 'proof-config)			; for proof-follow-mode

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; first a couple of helper functions 
;;

(defmacro proof-maybe-save-point (&rest body)
  "Save point according to proof-follow-mode, execute BODY."
  `(if (eq proof-follow-mode 'locked)
       (progn
	 ,@body)
     (save-excursion
	,@body)))

(defun proof-maybe-follow-locked-end ()
  "Maybe point to the make sure the locked region is displayed."
  (if (eq proof-follow-mode 'follow)
    (proof-goto-end-of-queue-or-locked-if-not-visible)))


;;
;; Doing commands
;;

(defun proof-assert-next-command-interactive ()
  "Process until the end of the next unprocessed command after point.
If inside a comment, just process until the start of the comment."
  (interactive)
  (proof-with-script-buffer
   (proof-maybe-save-point
    (goto-char (proof-queue-or-locked-end))
    (proof-assert-next-command))
   (proof-maybe-follow-locked-end)))

(defun proof-process-buffer ()
  "Process the current (or script) buffer, and maybe move point to the end."
  (interactive)
  (proof-with-script-buffer
   (proof-maybe-save-point
    (goto-char (point-max))
    (proof-assert-until-point-interactive))
   (proof-maybe-follow-locked-end)))


;;
;; Undoing commands
;;

(defun proof-undo-last-successful-command ()
  "Undo last successful command at end of locked region."
  (interactive)
  (proof-undo-last-successful-command-1))

(defun proof-undo-and-delete-last-successful-command ()
  "Undo and delete last successful command at end of locked region.
Useful if you typed completely the wrong command.
Also handy for proof by pointing, in case the last proof-by-pointing
command took the proof in a direction you don't like.

Notice that the deleted command is put into the Emacs kill ring, so
you can use the usual `yank' and similar commands to retrieve the
deleted text."
  (interactive)
  (proof-undo-last-successful-command-1 'delete)
  ;; FIXME want to do this here for 3.3, for nicer behaviour
  ;; when deleting.
  ;; Unfortunately nasty problem with read only flag when
  ;; inserting at (proof-locked-end) sometimes behaves as if
  ;; point is inside locked region  (prob because span is 
  ;;  [ ) and not [ ] -- why??).
  ;; (proof-script-new-command-advance)
  )

;; No direct key-binding for this one: C-c C-u was too dangerous,
;; when used quickly it's too easy to accidently delete!
(defun proof-undo-last-successful-command-1 (&optional delete)
  "Undo last successful command at end of locked region.
If optional DELETE is non-nil, the text is also deleted from
the proof script."
  (interactive "P")
  (proof-with-script-buffer
   (proof-maybe-save-point
    (unless (proof-locked-region-empty-p)
      (let ((lastspan (span-at-before (proof-locked-end) 'type)))
	(if lastspan
	    (progn
	      (goto-char (span-start lastspan))
	      (proof-retract-until-point delete))
	  (error "Nothing to undo!")))))
   (proof-maybe-follow-locked-end)))

(defun proof-retract-buffer ()
  "Retract the current buffer, and maybe move point to the start."
  (interactive)
  (proof-with-script-buffer
   (proof-maybe-save-point
    (goto-char (point-min))
    (proof-retract-until-point-interactive))
   (proof-maybe-follow-locked-end)))

(defun proof-retract-current-goal ()
  "Retract the current proof, and move point to its start."
  (interactive)
  (proof-maybe-save-point
   (let
      ((span (proof-last-goal-or-goalsave)))
     (if (and span (not (eq (span-property span 'type) 'goalsave))
	      (< (span-end span) (proof-unprocessed-begin)))
	 (progn
	   (goto-char (span-start span))
	   (proof-retract-until-point-interactive)
	   (proof-maybe-follow-locked-end))
       (error "Not proving")))))

;;
;; Interrupt
;;

(defun proof-interrupt-process ()
  "Interrupt the proof assistant.  Warning! This may confuse Proof General.
This sends an interrupt signal to the proof assistant, if Proof General
thinks it is busy.  

This command is risky because when an interrupt is trapped in the
proof assistant, we don't know whether the last command succeeded or
not.  The assumption is that it didn't, which should be true most of
the time, and all of the time if the proof assistant has a careful
handling of interrupt signals."
  (interactive)
  (unless (proof-shell-live-buffer)
      (error "Proof Process Not Started!"))
  (unless proof-shell-busy
    (error "Proof Process Not Active!"))
  (with-current-buffer proof-shell-buffer
    ;; Just send an interrrupt.  
    ;; Action on receiving one is triggered in proof-shell
    (comint-interrupt-subjob)
    (run-hooks 'proof-shell-pre-interrupt-hook)))
  

;;
;; Movement commands
;;

;; FIXME da: the next function is messy.  Also see notes in 'todo'
(defun proof-goto-command-start ()
  "Move point to start of current (or final) command of the script."
  (interactive)
  (let* ((cmd (span-at (point) 'type))
	 (start (if cmd (span-start cmd))))
    (if start 
	(progn
	  ;; BUG: only works for unclosed proofs.
	  (goto-char start))
      (let ((semis (nth 1 (proof-segment-up-to (point) t))))
	(if (eq 'unclosed-comment (car-safe semis)) 
	    (setq semis (cdr-safe semis)))
	(if (nth 2 semis) ; fetch end point of previous command
	      (goto-char (nth 2 semis))
	  ;; no previous command: just next to end of locked
	  (goto-char (proof-locked-end)))))
    ;; Oddities of this function: if we're beyond the last proof
    ;; command, it jumps back to the last command.  Could alter this
    ;; by spotting that command end of last of semis is before
    ;; point.  Also, behaviour with comments is different depending
    ;; on whether locked or not.
    (skip-chars-forward " \t\n")))

(defun proof-goto-command-end ()
  "Set point to end of command at point."
  (interactive)
  (let ((cmd (span-at (point) 'type)))
    (if cmd (goto-char (span-end cmd))
;      (and (re-search-forward "\\S-" nil t)
;	   (proof-assert-until-point nil 'ignore-proof-process)) 
      (proof-assert-next-command nil 
				 'ignore-proof-process
				 'dontmoveforward))
    (skip-chars-backward " \t\n")
    (unless (eq (point) (point-min))
      ;; should land on terminal char
      (backward-char))))



;;
;; Mouse functions
;;

;; FIXME oddity here: with proof-follow-mode='locked, when retracting,
;; point stays where clicked.  When advancing, it moves.  Might
;; be nicer behaviour than actually moving point into locked region
;; which is only useful for cut and paste, really.
(defun proof-mouse-goto-point (event)
  "Call proof-goto-point on the click position."
  (interactive "e")
  (proof-maybe-save-point
   (mouse-set-point event)
   (proof-goto-point)))
  

;; FIXME da: this is an oddity.  It copies the span, but does not
;; send it, contrary to it's old name ("proof-send-span").   
;; Now made more general to behave like mouse-track-insert
;; when not over a span.
;; FIXME da: improvement would be to allow selection of part
;; of command by dragging, as in ordinary mouse-track-insert.
;; Maybe by setting some of the mouse track hooks.
(defun proof-mouse-track-insert (event)
  "Copy highlighted command under the mouse to point.  Ignore comments.
If there is no command under the mouse, behaves like mouse-track-insert."
  (interactive "e")
  (let ((str
	 (save-window-excursion
	   (save-excursion
	     (let* ((span (span-at (mouse-set-point event) 'type)))
	       (and
		span
		;; Next test might be omitted to allow for non-script
		;; buffer copying (e.g. from spans in the goals buffer)
		(eq (current-buffer) proof-script-buffer)
		;; Test for type=vanilla means that closed goal-save regions
		;; are not copied.
		;; PG 3.3: remove this test, why not copy full proofs?
		;; (wanted to remove tests for 'vanilla)
		;; (eq (span-property span 'type) 'vanilla)
		;; Finally, extracting the 'cmd part prevents copying
		;; comments, and supresses leading spaces, at least.
		;; Odd.
		(span-property span 'cmd)))))))
    ;; Insert copied command in original window, 
    ;; buffer, point position.
    (if str 
	(insert str proof-script-command-separator)
      (mouse-track-insert event))))




;;
;; Minibuffer non-scripting command
;;

(defvar proof-minibuffer-history nil
  "History of proof commands read from the minibuffer")

(defun proof-minibuffer-cmd (cmd)
  "Prompt for a command in the minibuffer and send it to proof assistant.
The command isn't added to the locked region.

If a prefix arg is given and there is a selected region, that is
pasted into the command.  This is handy for copying terms, etc from
the script.

If `proof-strict-state-preserving' is set, and `proof-state-preserving-p' 
is configured, then the latter is used as a check that the command
will be safe to execute, in other words, that it won't ruin
synchronization.  If when applied to the command it returns false,
then an error message is given.

WARNING: this command risks spoiling synchronization if the test
`proof-state-preserving-p' is not configured, if it is
only an approximate test, or if `proof-strict-state-preserving'
is off (nil)."
  (interactive
   (list (read-string "Command: " 
		      (if (and current-prefix-arg (region-exists-p))
			  (replace-in-string 
			   (buffer-substring (region-beginning) (region-end))
			   "[ \t\n]+" " "))
		      'proof-minibuffer-history)))
  (if (and proof-strict-state-preserving
	   proof-state-preserving-p
	   (not (funcall proof-state-preserving-p cmd)))
      (error "Command is not state preserving, I won't execute it!"))
  (proof-shell-invisible-command cmd))


;;
;; Frobbing locked end
;;

;; A command for making things go horribly wrong - it moves the
;; end-of-locked-region marker backwards, so user had better move it
;; correctly to sync with the proof state, or things will go all
;; pear-shaped.

;; In fact, it's so risky, we'll disable it by default
(if (if proof-running-on-XEmacs
	(get 'proof-frob-locked-end 'disabled t)
      ;; FSF code more approximate
      (not (member 'disabled (symbol-plist 'proof-frob-locked-end))))
    (put 'proof-frob-locked-end 'disabled t))

(defun proof-frob-locked-end ()
  "Move the end of the locked region backwards to regain synchronization.
Only for use by consenting adults.

This command can be used to repair synchronization in case something
goes wrong and you want to tell Proof General that the proof assistant
has processed less of your script than Proof General thinks.

You should only use it to move the locked region to the end of
a proof command."
  (interactive)
  (cond
   (proof-shell-busy
    (error "You can't use this command while %s is busy!" proof-assistant))
   ((not (eq (current-buffer) proof-script-buffer))
    (error "Must be in the active scripting buffer."))
   ;; Sometimes may need to move point forwards, when locked region
   ;; is editable.
   ;; ((> (point) (proof-locked-end))
   ;; (error "You can only move point backwards."))
   ;; FIXME da: should move to a command boundary, really!
   (t (proof-set-locked-end (point))	
      (delete-spans (proof-locked-end) (point-max) 'type))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; command history  (unfinished)
;;
;; da: below functions for input history simulation are quick hacks.
;; Could certainly be made more efficient.

;(defvar proof-command-history nil
;  "History used by proof-previous-matching-command and friends.")

;(defun proof-build-command-history ()
;  "Construct proof-command-history from script buffer.
;Based on position of point."
;  ;; let
;  )

;(defun proof-previous-matching-command (arg)
;  "Search through previous commands for new command matching current input."
;  (interactive))
;  ;;(if (not (memq last-command '(proof-previous-matching-command
;  ;; proof-next-matching-command)))
;      ;; Start a new search
      
;(defun proof-next-matching-command (arg)
;  "Search through following commands for new command matching current input."
;  (interactive "p")
;  (proof-previous-matching-command (- arg)))

;;
;; end command history stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	  



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; Non-scripting proof assistant commands.
;;;

;;; These are based on defcustom'd settings so that users may 
;;; re-configure the system to their liking.


;; FIXME: da: add more general function for inserting into the
;; script buffer and the proof process together, and using
;; a choice of minibuffer prompting (hated by power users, perfect
;; for novices).
;; TODO:
;;   Add named goals.
;;   Coherent policy for movement here and elsewhere based on
;;    proof-one-command-per-line user option.
;;   Coherent policy for sending to process after writing into
;;    script buffer.  Could have one without the other.
;;    For example, may be more easy to edit complex goal string
;;    first in the script buffer.  Ditto for tactics, etc.



;;
;; Helper macros and functions
;;

;; See put expression at end to give this indentation like while form
(defmacro proof-if-setting-configured (var &rest body)
  "Give error if a configuration setting VAR is unset, otherwise eval BODY."
  `(if ,var
       (progn ,@body)
     (error "Proof General not configured for this: set %s" 
	    ,(symbol-name var))))

(defmacro proof-define-assistant-command (fn doc cmdvar &optional body)
  "Define command FN to send string BODY to proof assistant, based on CMDVAR.
BODY defaults to CMDVAR, a variable."
  `(defun ,fn ()
     ,(concat doc 
	      (concat "\nIssues a command to the assistant based on " 
		      (symbol-name cmdvar) ".") 
		"")
     (interactive)
     (proof-if-setting-configured ,cmdvar
       (proof-shell-invisible-command ,(or body cmdvar)))))

(defmacro proof-define-assistant-command-witharg (fn doc cmdvar prompt &rest body)
  "Define command FN to prompt for string CMDVAR to proof assistant.
CMDVAR is a function or string.  Automatically has history."
  `(progn
     (defvar ,(intern (concat (symbol-name fn) "-history")) nil
       ,(concat "History of arguments for " (symbol-name fn) "."))
     (defun ,fn (arg)
     ,(concat doc "\nIssues a command based on ARG to the assistant, using " 
	      (symbol-name cmdvar) ".\n"
	      "The user is prompted for an argument.")
      (interactive
       (proof-if-setting-configured ,cmdvar
	   (if (stringp ,cmdvar)
	       (list (format ,cmdvar
		 	 (read-string 
			   ,(concat prompt ": ") ""
			   ,(intern (concat (symbol-name fn) "-history")))))
	     (funcall ,cmdvar))))
       ,@body)))

(defun proof-issue-new-command (cmd)
  "Insert CMD into the script buffer and issue it to the proof assistant.
If point is in the locked region, move to the end of it first.
Start up the proof assistant if necessary."
  (proof-with-script-buffer
   (if (proof-shell-live-buffer)
       (if (proof-in-locked-region-p)
	   (proof-goto-end-of-locked t)))
   (proof-script-new-command-advance)
   ;; FIXME: fixup behaviour of undo here.  Really want to temporarily
   ;; disable undo for insertion.  but (buffer-disable-undo) trashes
   ;; whole undo list!
   (insert cmd)
   ;; FIXME: could do proof-indent-line here, but let's wait until
   ;; indentation is fixed.
   (proof-assert-until-point-interactive)))

;;
;; Commands which do not require a prompt and send an invisible
;; command.
;;

(proof-define-assistant-command proof-prf  
  "Show the current proof state."
  proof-showproof-command)
(proof-define-assistant-command proof-ctxt 
  "Show the current context."
  proof-context-command)
(proof-define-assistant-command proof-help 
  "Show a help or information message from the proof assistant.
Typically, a list of syntax of commands available."
  proof-info-command)
(proof-define-assistant-command proof-cd
  "Change directory to the default directory for the current buffer."
  proof-shell-cd-cmd
  (proof-format-filename proof-shell-cd-cmd 
	  ;; FSF fix: use default-directory rather than fn
	  default-directory))

(defun proof-cd-sync ()
  "If proof-shell-cd-cmd is set, do proof-cd and wait for prover ready.
This is intended as a value for proof-activate-scripting-hook"
  ;; The hook is set in proof-mode before proof-shell-cd-cmd may be set,
  ;; so we explicitly test it here.  
  (if proof-shell-cd-cmd 
      (progn
	(proof-cd)
	(proof-shell-wait))))

;;
;; Commands which require an argument, and maybe affect the script.
;;

;; FIXME: maybe move these to proof-menu

(proof-define-assistant-command-witharg proof-find-theorems
 "Search for items containing given constants."
 proof-find-theorems-command
 "Find theorems containing"
 (proof-shell-invisible-command arg))

(proof-define-assistant-command-witharg proof-issue-goal
 "Write a goal command in the script, prompting for the goal."
 proof-goal-command
 "Goal"
 (let ((proof-one-command-per-line t))   ; Goals always start at a new line
   (proof-issue-new-command arg)))

(proof-define-assistant-command-witharg proof-issue-save 
 "Write a save/qed command in the script, prompting for the theorem name."
 proof-save-command
 "Save as"
 (let ((proof-one-command-per-line t))   ; Saves always start at a new line
   (proof-issue-new-command arg)))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Electric terminator mode
;;
;; NB: only relevant for provers with a "terminal char" which
;; terminates commands in proof scripts.

;; Register proof-electric-terminator as a minor mode.

(deflocal proof-electric-terminator nil
  "Fake minor mode for electric terminator.")

(or (assq 'proof-electric-terminator minor-mode-alist)
    (setq minor-mode-alist
	  (append minor-mode-alist
		  (list '(proof-electric-terminator
			  (concat " " proof-terminal-string))))))

;; This is a value used by custom-set property = proof-set-value.
(defun proof-electric-terminator-enable ()
  "Copy proof-electric-terminator-enable to all script mode copies of it.
Make sure the modeline is updated to display new value for electric terminator."
  (if proof-mode-for-script
      (proof-map-buffers (proof-buffers-in-mode proof-mode-for-script)
			 (setq proof-electric-terminator 
			       proof-electric-terminator-enable)))
  (redraw-modeline))

(proof-deftoggle proof-electric-terminator-enable proof-electric-terminator-toggle)

(defun proof-electric-term-incomment-fn ()
  "Used as argument to proof-assert-until-point."
  ;; CAREFUL: (1) dynamic scoping here 
  ;;          (2) needs this name to be recognized in 
  ;;		  proof-assert-until-point
  (setq incomment t)
  (if ins (backward-delete-char 1))
  (goto-char mrk)
  (insert proof-terminal-string))

;; FIXME da: this function is a mess and needs rewriting.  
;;  (proof-assert-until-point process needs cleaning up)
;;
;; What it should do: 
;;   * parse FIRST.  If we're inside a comment or string,
;;     then insert the terminator where we are.  Otherwise
;;     can skip backwards and insert the terminator at the
;;     command end (perhaps optionally), and look for 
;;     existing terminator.

(defun proof-process-electric-terminator ()
  "Insert the proof command terminator, and assert up to it.
This is a little bit clever with placement of semicolons, and will
try to avoid duplicating them in the buffer.
When used in the locked region (and so with strict read only off), it
always defaults to inserting a semi (nicer might be to parse for a
comment, and insert or skip to the next semi)."
  (let ((mrk (point)) ins incomment)
    (if (< mrk (proof-locked-end))
	;; In locked region, just insert terminator without further ado
	(insert proof-terminal-char)
      ;; Otherwise, do other thing.
      ;; Old idea: only shift terminator wildly if we're looking at
      ;; whitespace.  Why?
      ;; (if (looking-at "\\s-\\|\\'\\|\\w") 
      (if (proof-only-whitespace-to-locked-region-p)
	  (error "There's nothing to do!"))

      (if (not (= (char-after (point)) proof-terminal-char))
	  (progn 
	    (forward-char) ;; immediately after command end.
	    (insert proof-terminal-string) 
	    (setq ins t)))
      (proof-assert-until-point 'proof-electric-term-incomment-fn)
      (or incomment
	  (proof-script-next-command-advance)))))

(defun proof-electric-terminator ()
  "Insert the terminator, perhaps sending the command to the assistant.
If proof-electric-terminator-enable is non-nil, the command will be
sent to the assistant."
  (interactive)
  (if proof-electric-terminator-enable 
      (proof-process-electric-terminator)
    (self-insert-command 1)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Completion based on <PA>-completion-table
;;
;; Requires completion.el package.   Completion is usually
;; a hand-wavy thing, so we don't make any attempt to maintain
;; a precise completion table or anything.
;;
;; New in 3.2.  
;;
(defun proof-add-completions ()
  "Add completions from <PA>-completion-table to completion database.
Uses `add-completion' with a negative number of uses and ancient
last use time, to discourage saving these into the users database."
  (interactive)
  (require 'completion)
  (mapcar (lambda (cmpl) 
	    ;; completion gives error in this case; trapping
	    ;; the error here is tricky in FSF Emacs so duplicate
	    ;; the test.
	    (if (>= (length cmpl) completion-min-length)
		(add-completion cmpl -1000 0)))
	  (proof-ass completion-table)))

;; NB: completion table is expected to be set when proof-script 
;; is loaded!  Can call proof-script-add-completions if the table
;; is updated.
(eval-after-load "completion" 
  '(proof-add-completions))

(defun proof-script-complete (&optional arg)
  "Like `complete' but case-fold-search set to proof-case-fold-search."
  (interactive "*p")
  (let ((case-fold-search proof-case-fold-search))
    (complete arg)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tags table building
;;
;; New in 3.3... or perhaps later!
;;
;; FIXME: incomplete.  Add function to build tags table from
;; 






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Function to insert last prover output in comment.
;; Requested/suggested by Christophe Raffalli
;;

(defun pg-insert-last-output-as-comment ()
  "Insert the last output from the proof system as a comment in the proof script."
  (interactive)
  (if proof-shell-last-output
      ;; There may be a system specific function to insert the comment
      (if pg-insert-output-as-comment-fn
	  (pg-insert-output-as-comment-fn proof-shell-last-output)
	;; Otherwise the default behaviour is to use comment-region
	(let  ((beg (point)) end)
	  ;; pg-assoc-strip-subterm-markup: should be done
	  ;; for us in proof-fontify-region
	  (insert proof-shell-last-output)
	  ;; 3.4: add fontification. Questionable since comments will
	  ;; probably be re-highlighted, so colouration, especially
	  ;; based on removed specials, will be lost.  
	  ;; X-Symbol conversion is useful, but a surprising nuisance
	  ;; to achieve, mainly because x-symbol doesn't give us back
	  ;; a useful pointer to end of region after converting, and
	  ;; character positions change.
	  ;; (FIXME: contact x-sym author about this).
	  ;; proof-fontify-region does this for us, now
	  (setq end (proof-fontify-region beg (point)))
	  (comment-region beg end)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Span manipulation
;;

(defun pg-copy-span-contents (span)
  "Copy contents of SPAN to kill ring, sans surrounding whitespace."
  (copy-region-as-kill 
   (save-excursion 
     (goto-char (span-start span))
     (skip-chars-forward " \t\n")
     (point))
   (save-excursion
     (goto-char (span-end span))
     (skip-chars-backward " \t\n")
     (point)))
  (own-clipboard (car kill-ring)))

;; 3.3: these functions are experimental, in that they haven't
;; been rigorously tested.  They don't work well in FSF Emacs.

(defun pg-numth-span-higher-or-lower (span num &optional noerr)
  "Find NUM'th span after/before SPAN.  NUM is positive for after."
  (unless (and span (<= (span-end span) (proof-unprocessed-begin)))
    (if noerr 
	nil
      (error "No processed region under point")))
  (let ((downflag (> num 0))
	(num      (abs num))
	nextspan)
    (while (and (> num 0)
		(setq nextspan (if downflag
				   (next-span span 'type)
				 (prev-span span 'type)))
		(if downflag
		    ;; If moving down, check we don't go beyond
		    ;; end of processed region
		    (<= (span-end span) (proof-unprocessed-begin))
		  t))
      (setq num (1- num))
      (setq span nextspan))
    (if (= num 0)
	span
      (if noerr
	  nil
	(error "No region to move past" num)))))

(defun pg-control-span-of (span)
  "Return the controlling span of SPAN, or SPAN itself."
  (or (span-property span 'controlspan)
      span))

(defun pg-move-span-contents (span num)
  "Move SPAN up/downwards in the buffer, past NUM spans.
If NUM is negative, move upwards.  Return new span."
  ;; FIXME: maybe num arg is overkill, should only have 1?
  (save-excursion
    (let  ((downflag (> num 0)) nextspan)
      ;; Always move a control span instead; it contains
      ;; children span which move together with it.
      (setq span (pg-control-span-of span))
      (setq nextspan (pg-numth-span-higher-or-lower span num))
      ;; We're going to move the span to before/after nextspan.
      ;; First make sure inserting there doesn't extend the span.
      (if downflag
	  (set-span-property nextspan 'end-open t)
	(set-span-property nextspan 'start-open t))
      ;; When we delete the span, we want to duplicate it
      ;; to recreate in the new position.
      (set-span-property span 'duplicable 't)
      ;; FIXME: this is faulty: moving span up gives children
      ;; list with single nil element.  Hence liveness test
      (mapcar (lambda (s) (if (span-live-p s)
			      (set-span-property s 'duplicable 't)))
	      (span-property span 'children))
      (let* ((start     (span-start span))
	     (end       (span-end span))
	     (contents  (buffer-substring start end))
	     ;; Locked end may move up when we delete
	     ;; region: we'll make sure to reset it
	     ;; again later, it shouldn't change.  
	     ;; NB: (rely on singlethreadedness here, so
	     ;; lockedend doesn't move while in this code).
	     (lockedend (span-end proof-locked-span)))
	(let ((inhibit-read-only t))
	  ;; FIXME: undo behaviour isn't quite right yet.
	  (undo-boundary)
	  (delete-region start end)
	  (let ((insertpos (if downflag
			       (span-end nextspan)
			     (span-start nextspan))))
	    (goto-char insertpos)
	    ;; Let XEmacs duplicate extents as needed, then repair
	    ;; their associations
	    (insert contents)
	    (let ((new-span 
		   (span-at insertpos 'type)));should be one we deleted.
	      (set-span-property 
	       new-span 'children
	       (append 
		(mapcar-spans 'pg-fixup-children-span 
			      insertpos (point) 'type)))
	      (set-span-end proof-locked-span lockedend)
	      (undo-boundary)
	      new-span)))))))

(defun pg-fixup-children-span (span)
  (if (span-property span 'controlspan)
      ;; WARNING: dynamic binding
      (progn
	(set-span-property span 'controlspan new-span)
	(list span))))
      
(defun pg-move-region-down (&optional num)
  "Move the region under point downwards in the buffer, past NUM spans."
  (interactive "p")
  (let ((span  (span-at (point) 'type)))
    (and span 
	 (goto-char (span-start
		     (pg-move-span-contents span num)))
	 (skip-chars-forward " \t\n"))))

(defun pg-move-region-up (&optional num)
  "Move the region under point upwards in the buffer, past NUM spans."
  (interactive "p")
  (pg-move-region-down (- num)))

;; FIXME: not working right yet, sigh...
(defun proof-forward-command (&optional num)
  "Move forward to the start of the next proof region."
  (interactive "p")
  (skip-chars-forward " \t\n")
  (let* ((span  (or (span-at (point) 'type)
		    (and (skip-chars-backward " \t\n")
			 (> (point) (point-min))
			 (span-at (1- (point)) 'type))))
	 (nextspan (and span (pg-numth-span-higher-or-lower 
			      (pg-control-span-of span) num 'noerr))))
    (cond
     ((and nextspan (> num 0))
      (goto-char (span-start nextspan))
      (skip-chars-forward " \t\n"))
     ((and nextspan (< num 0))
      (goto-char (span-end nextspan)))
     ((and span (> num 0))
      (goto-char (span-end span)))
     ((and span (< num 0))
      (goto-char (span-start span))))))

(defun proof-backward-command (&optional num)
  (interactive "p")
  (proof-forward-command (- num)))
  

   



  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Span menus and keymaps  (maybe belongs in pg-menu)
;;

(defvar pg-span-context-menu-keymap
    (let ((map (make-sparse-keymap
		"Keymap for context-sensitive menus on spans")))
      (cond
       (proof-running-on-XEmacs
	(define-key map [button3] 'pg-span-context-menu))
       (proof-running-on-Emacs21
	(define-key map [down-mouse-3] 'pg-span-context-menu)))
      map))

;; FIXME: TODO here:
;;
;; Check for a 'type which is one of the elements we know about
;; (pgidioms).
;;

(defun pg-span-for-event (event)
  "Return span corresponding to position of a mouse click EVENT."
  (cond
   (proof-running-on-XEmacs
    (select-window (event-window event))
    (span-at (event-point event) 'type))
   (proof-running-on-Emacs21
    (with-current-buffer 
	(window-buffer (posn-window (event-start event)))
      (span-at  (posn-point (event-start event)) 'type)))))

(defun pg-span-context-menu (event)
  (interactive "e")
  (let ((span (pg-span-for-event event))
	cspan)
    ;; Find controlling span 
    (while (setq cspan (span-property span 'controlspan))
      (setq span cspan))
    (let*  
	((idiom (and span (span-property span 'idiom)))
	 (id    (and span (span-property span 'id))))
      (popup-menu (pg-create-in-span-context-menu 
		   span 
		   (if idiom (symbol-name idiom))
		   (if id (symbol-name id)))))))

(defun pg-toggle-visibility ()
  "Toggle visibility of region under point."
  (interactive)
  (let* ((span (span-at (point) 'type))
	 (idiom (and span (span-property span 'idiom)))
	 (id    (and span (span-property span 'id))))
    (and  idiom id
	 (pg-toggle-element-visibility (symbol-name idiom) (symbol-name id)))))


(defun pg-create-in-span-context-menu (span idiom name)
  "Create the dynamic context-sensitive menu for a span."
  ;; FIXME: performance here, consider caching in the span itself?
  ;; (or maybe larger menu spans which are associated with a menu).
  ;; FIXME: treat proof and non-proof regions alike, could add
  ;; visibility controls for non-proof regions also, redesigning
  ;; idiom notion.
  (append
   (list (pg-span-name span))
   (list (vector
	  "Show/hide"   
	  (if idiom (list `pg-toggle-element-visibility idiom name) 
	    idiom)
	  (not (not idiom))))
   (list (vector
	  "Copy"	(list 'pg-copy-span-contents span) t))
   (if proof-experimental-features
       (list (vector
	      "Move up"     (list 'pg-move-span-contents span -1)
	      (pg-numth-span-higher-or-lower (pg-control-span-of span) -1 'noerr))))
   (if proof-experimental-features
       (list (vector
	      "Move down"   (list 'pg-move-span-contents span 1)
	      (pg-numth-span-higher-or-lower (pg-control-span-of span) 1 'noerr))))
   (if (and proof-experimental-features 
	    proof-shell-theorem-dependency-list-regexp)
       (proof-dependency-in-span-context-menu span))
   (if proof-script-span-context-menu-extensions
       (funcall proof-script-span-context-menu-extensions span idiom name))))


  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic adjustmenth of prover's pretty-printing width
;; (adapted from Lego's mode, was also used in Isar and Plastic)
;; 
;; FIXME: complete this.

;(defvar pg-prover-current-line-width nil
;  "Cache value for pg-adjust-line-width to avoid repeatedly changing width.")

;(defun pg-adjust-line-width (buffer)
;  "Adjust the prover's line width to match that of BUFFER."
;  (proof-if-setting-configured proof-shell-adjust-line-width-cmd)
;  proof-shell-(let* ((win    (get-buffer-window buffer))
;	 (curwid (if win (window-width win))))
;    (if (and curwid
;	     (not (equal curwid pg-prover-current-line-width)))
;	(progn
;	  ;; Update the prover's output width
;	  (proof-shell-invisible-command
	   
	
;with-current-buffer buffer
;    (let ((current-width
;	   (window-width (get-buffer-window proof-goals-buffer)))
;      (if (equal current-width lego-shell-current-line-width) ()
;	     ; else
;	     (setq lego-shell-current-line-width current-width)
;	     (set-buffer proof-shell-buffer)
;	     (insert (format lego-pretty-set-width (- current-width 1)))
;	     )))))




(provide 'pg-user)
;; pg-user.el ends here.
