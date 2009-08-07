;;; pg-user.el --- User level commands for Proof General
;;
;; Copyright (C) 2000-2008 LFCS Edinburgh.
;; Author:     David Aspinall and others
;; License:    GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;
;;; Commentary:
;; 
;; This file defines some user-level commands.  Most of them
;; are script-based operations.  Exported user-level commands
;; are defined here as autoloads to avoid circular requires.

;;; Code:

(require 'span)
(require 'proof)			; loader
(require 'proof-script)			; we build on proof-script
(require 'comint)			; comint-interrupt-subjob/comint-ptyp

(eval-when-compile
  (require 'completion))		; loaded dynamically at runtime

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; first a couple of helper functions
;;

(defmacro proof-maybe-save-point (&rest body)
  "Save point according to `proof-follow-mode', execute BODY."
  ;; FIXME: This duplicates the code of the body, which isn't wrong but
  ;; is undesirable.
  `(if (eq proof-follow-mode 'locked)
       (progn
	 ,@body)
     (save-excursion
	,@body)))

(defun proof-maybe-follow-locked-end ()
  "Maybe move point to make sure the locked region is displayed."
  (cond
   ((eq proof-follow-mode 'follow)
    (proof-goto-end-of-queue-or-locked-if-not-visible))
   ((eq proof-follow-mode 'followdown)
    (if (> (proof-queue-or-locked-end) (point))
	(goto-char (proof-queue-or-locked-end))))))
	

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
  ;; FIXME (proof-script-new-command-advance)
  )

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

;;;###autoload
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
    ;; Send send an interrrupt, without comint-skip-input effect.
    ;; Interrupt is processed inside proof-shell.
    (interrupt-process nil comint-ptyp)
    (run-hooks 'proof-shell-pre-interrupt-hook)))
  

;;
;; Movement commands
;;

;; TODO da: the next function is messy.
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
      (proof-assert-next-command nil
				 'ignore-proof-process
				 'dontmoveforward))
    (skip-chars-backward " \t\n")
    (unless (eq (point) (point-min))
      (backward-char))))


;;
;; Mouse functions
;;

;; FIXME oddity here: with proof-follow-mode='locked, when retracting,
;; point stays where clicked.  When advancing, it moves.  Might
;; be nicer behaviour than actually moving point into locked region
;; which is only useful for cut and paste, really.
(defun proof-mouse-goto-point (event)
  "Call `proof-goto-point' on the click position EVENT."
  (interactive "e")
  (proof-maybe-save-point
   (mouse-set-point event)
   (proof-goto-point)))
  





;;
;; Minibuffer non-scripting command
;;

(defvar proof-minibuffer-history nil
  "History of proof commands read from the minibuffer.")

(defun proof-minibuffer-cmd (cmd)
  "Send CMD to proof assistant.  Interactively, read from minibuffer.
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
		      (if (and current-prefix-arg (region-active-p))
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
(put 'proof-frob-locked-end 'disabled t)

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
    (error "Must be in the active scripting buffer"))
   ;; Sometimes may need to move point forwards, when locked region
   ;; is editable.
   ;; ((> (point) (proof-locked-end))
   ;; (error "You can only move point backwards"))
   ;; FIXME da: should move to a command boundary, really!
   (t (proof-set-locked-end (point))
      (span-delete-spans (proof-locked-end) (point-max) 'type))))





	  



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; Non-scripting proof assistant commands.
;;;

;; These are based on defcustom'd settings so that users may
;; re-configure the system to their liking.


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

;;;###autoload
(defmacro proof-define-assistant-command (fn doc cmdvar &optional body)
  "Define FN (docstring DOC) to send BODY to prover, based on CMDVAR.
BODY defaults to CMDVAR, a variable."
  `(defun ,fn ()
     ,(concat doc
	      (concat "\nIssues a command to the assistant based on "
		      (symbol-name cmdvar) ".")
		"")
     (interactive)
     (proof-if-setting-configured ,cmdvar
       (proof-shell-invisible-command ,(or body cmdvar)))))

;;;###autoload
(defmacro proof-define-assistant-command-witharg (fn doc cmdvar prompt &rest body)
  "Define command FN to prompt for string CMDVAR to proof assistant.
CMDVAR is a variable holding a function or string.  Automatically has history."
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
  proof-showproof-command
  (progn
    (pg-goals-buffers-hint)
    proof-showproof-command))

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
	  default-directory))

(defun proof-cd-sync ()
  "If `proof-shell-cd-cmd' is set, do `proof-cd' and wait for prover ready.
This is intended as a value for `proof-activate-scripting-hook'"
  ;; The hook is set in proof-mode before proof-shell-cd-cmd may be set,
  ;; so we explicitly test it here.
  (if proof-shell-cd-cmd
      (progn
	(proof-cd)
	(proof-shell-wait))))

;;
;; Commands which require an argument, and maybe affect the script.
;;

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

(or (assq 'proof-electric-terminator-enable minor-mode-alist)
    (setq minor-mode-alist
	  (append minor-mode-alist
		  (list '(proof-electric-terminator-enable
			  (concat " " proof-terminal-string))))))

;; This is a function called by custom-set property = proof-set-value.
;;;###autoload
(defun proof-electric-terminator-enable ()
  "Make sure the modeline is updated to display new value for electric terminator."
  ;; TODO: probably even this isn't necessary
  (force-mode-line-update))

(proof-deftoggle proof-electric-terminator-enable proof-electric-terminator-toggle)

;;;###autoload
(defun proof-electric-term-incomment-fn ()
  "Used as argument to `proof-assert-until-point'."
  ;; CAREFUL: (1) dynamic scoping here  (incomment, ins, mrk)
  ;;          (2) needs this name to be recognized in
  ;;		  proof-assert-until-point
  (setq incomment t)
  (if ins (backward-delete-char 1)) ; delete spurious char in comment
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
      (if (proof-only-whitespace-to-locked-region-p)
	  (error "There's nothing to do!"))

      (if (not (= (char-after (point)) proof-terminal-char))
	  (progn
	    (forward-char) ;; immediately after command end.
	    (unless proof-electric-terminator-noterminator
	      (insert proof-terminal-string)
	      (setq ins t))))
      (proof-assert-until-point 'proof-electric-term-incomment-fn)
      (or incomment
	  (proof-script-next-command-advance)))))

(defun proof-electric-terminator ()
  "Insert the terminator, perhaps sending the command to the assistant.
If variable `proof-electric-terminator-enable' is non-nil, the command will be
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

;; completion not autoloaded in GNU Emacs
(or (fboundp 'complete)
    (autoload 'complete "completion"))

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
;; Function to insert last prover output in comment.
;; Requested/suggested by Christophe Raffalli
;;

(defun pg-insert-last-output-as-comment ()
  "Insert the last output from the proof system as a comment in the proof script."
  (interactive)
  (if proof-shell-last-output
      (let  ((beg (point)))
	(insert (proof-shell-strip-output-markup proof-shell-last-output))
	(comment-region beg (point)))))


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
  (if (fboundp 'own-clipboard)		;; XEmacs function
      (own-clipboard (car kill-ring))))

;; 3.3: these functions are experimental, in that they haven't
;; been rigorously tested.  FIXME: they don't work well in GNU Emacs.

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
	(error "No region to move past")))))

(defun pg-control-span-of (span)
  "Return the controlling span of SPAN, or SPAN itself."
  (or (span-property span 'controlspan)
      span))

;; Really a drag-and-drop interface for this would be nice.
(defun pg-move-span-contents (span num)
  "Move SPAN up/downwards in the buffer, past NUM spans.
If NUM is negative, move upwards.  Return new span."
  ;; TODO: maybe num arg is overkill, should only have 1?
  (save-excursion
    (let  ((downflag (> num 0)) nextspan)
      ;; Always move a control span instead; it contains
      ;; children span which move together with it.
      (setq span (pg-control-span-of span))
      (setq nextspan (pg-numth-span-higher-or-lower span num))
      ;; We're going to move the span to before/after nextspan.
      ;; First make sure inserting there doesn't extend the span.
      (if downflag
	  (span-set-property nextspan 'end-open t)
	(span-set-property nextspan 'start-open t))
      ;; When we delete the span, we want to duplicate it
      ;; to recreate in the new position.
      (span-set-property span 'duplicable 't)
      ;; TODO: this is faulty: moving span up gives children
      ;; list with single nil element.  Hence liveness test
      (mapcar (lambda (s) (if (span-live-p s)
			      (span-set-property s 'duplicable 't)))
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
	  ;; TODO: undo behaviour isn't quite right yet.
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
	      (span-set-property new-span 'children
				 (pg-fixup-children-spans
				  new-span insertpos (point)))
	      (span-set-end proof-locked-span lockedend)
	      (undo-boundary)
	      new-span)))))))

(defun pg-fixup-children-spans (new-parent start end)
  (append
   (span-mapcar-spans
    (lambda (span)
      (if (span-property span 'controlspan)
	  (progn
	    (span-set-property span 'controlspan new-parent)
	    (list span))))
    start end 'type)))
      
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Dragging regions around
;;
;; FIXME: unfinished

;(defvar pg-drag-region-point nil
;  "Temporary store of point being dragged.")

;(defun pg-mouse-drag-move-region-function (event click-count dragp)
;  (save-excursion
;    (let* ((span (span-at (mouse-set-point event) 'type)))
;      (if span
;	  (if pg-drag-region-point
;	      ;; Move the region at point to region here.
	      

	  
;(defun pg-mouse-drag-up-move-region-function (event click-count)
;  (setq pg-drag-region-point nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;; FIXME: TODO here:
;;
;; Check for a 'type which is one of the elements we know about
;; (pgidioms).
;;

(defun pg-pos-for-event (event)
  "Return position corresponding to position of a mouse click EVENT."
  (with-current-buffer
      (window-buffer (posn-window (event-start event)))
    (posn-point (event-start event))))

(defun pg-span-for-event (event)
  "Return span corresponding to position of a mouse click EVENT."
  (span-at (pg-pos-for-event event) 'type))

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
   (list (vector
	  "Undo"
	  (list 'pg-span-undo span) t))
   (if proof-experimental-features
       (list (vector
	      "Move up"     (list 'pg-move-span-contents span -1)
	      (pg-numth-span-higher-or-lower (pg-control-span-of span) -1 'noerr))))
   (if proof-experimental-features
       (list (vector
	      "Move down"   (list 'pg-move-span-contents span 1)
	      (pg-numth-span-higher-or-lower (pg-control-span-of span) 1 'noerr))))
   (if proof-script-span-context-menu-extensions
       (funcall proof-script-span-context-menu-extensions span idiom name))
   (if (and proof-experimental-features
	    proof-shell-theorem-dependency-list-regexp)
       (proof-dependency-in-span-context-menu span))))

(defun pg-span-undo (span)
  "Undo to the start of the given SPAN."
  (interactive)
  (goto-char (span-start span))
  (proof-retract-until-point))

  

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Message buffer hints  (added in PG 3.5)
;;

(defun pg-goals-buffers-hint ()
  (pg-hint "Use \\[proof-display-some-buffers] to rotate output buffers; \\[pg-response-clear-displays] to clear response & trace."))

;;;###autoload
(defun pg-slow-fontify-tracing-hint ()
  (pg-hint "Large tracing output; decorating intermittently.  Use \\[pg-response-clear-displays] to clear trace."))

;;;###autoload
(defun pg-response-buffers-hint (&optional nextbuf)
  (pg-hint
   (format
    "\\[proof-prf] for goals;%s \\[proof-layout-windows] refreshes"
    (if (not proof-multiple-frames-enable) ;; and not proof-three-window-enable
	(format " \\[proof-display-some-buffers] rotates output%s;"
		(if nextbuf (concat " (next:" nextbuf ")") ""))
      ""))))

;;;###autoload
(defun pg-jump-to-end-hint ()
  (pg-hint "Use \\[proof-goto-end-of-locked] to jump to end of processed region"))
  
;;;###autoload
(defun pg-processing-complete-hint ()
  "Display hint for showing end of locked region or processing complete."
  (if (buffer-live-p proof-script-buffer)
      (let ((win (get-buffer-window proof-script-buffer)))
	(unless ;; end of locked already displayed
	    (and win (pos-visible-in-window-p (proof-unprocessed-begin)))
	  (save-excursion
	    (set-buffer proof-script-buffer)
	    (cond
	     ((proof-locked-region-empty-p)) ;; nothing if empty
	     ((proof-locked-region-full-p)
	      (pg-hint
	       (concat "Processing complete in " (buffer-name proof-script-buffer))))
	     (t ;; partly complete: hint about displaying the locked end
	      (pg-jump-to-end-hint))))))))

;;;###autoload
(defun pg-next-error-hint ()
  "Display hint for locating error."
  (pg-hint "Use \\[proof-next-error] to go to next error location."))

;;;###autoload
(defun pg-hint (hintmsg)
  "Display a hint HINTMSG in the minibuffer, if `pg-show-hints' is non-nil.
The function `substitute-command-keys' is called on the argument."
  (if pg-show-hints (message (substitute-command-keys hintmsg))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Symbol near point/identifier under mouse query
;;

;; Note: making these bindings globally is perhaps a bit obnoxious, but
;; this modifier combination is currently unused.
(global-set-key [C-M-mouse-1] 'pg-identifier-under-mouse-query)
(global-set-key [f5] 'pg-identifier-near-point-query)

(defun pg-identifier-under-mouse-query (event)
  (interactive "e")
  (if proof-query-identifier-command
      (save-selected-window
	(save-selected-frame
	 (save-excursion
	   (mouse-set-point event)
	   (pg-identifier-near-point-query))))))

(defun pg-identifier-near-point-query ()
  (interactive)
  (let ((identifier 
	 ;; If there's an active region in this buffer, use that
	 ;; instead of the identifier under point.  Since
	 ;; region-end moves immediately to new point with
	 ;; zmacs-regions we use oldend instead of current.
	 (if (region-active-p)
	     (buffer-substring (region-beginning)
			       (or oldend (region-end)))
	   (current-word)))
	(ctxt (proof-buffer-syntactic-context)))
    (pg-identifier-query identifier ctxt)))

(defun proof-query-identifier (string)
  (interactive "sQuery identifier: ")
  (pg-identifier-query string))

(defun pg-identifier-query (identifier &optional ctxt)
  "Query the proof assisstant about the given identifier (or string).
This uses `proof-query-identifier-command'."
  (unless (or (null identifier)
	      (string-equal identifier "")) ;; or whitespace?
    (proof-shell-invisible-command
     (cond
      ((stringp proof-query-identifier-command)
       ;; simple customization
       (format proof-query-identifier-command identifier))
      (t
       ;; buffer-syntactic context dependent, as an alist
       ;; (handy for Isabelle: not a true replacement for parsing)
       (format (nth 1 (assq ctxt proof-query-identifier-command))
	       identifier))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Imenu and Speedbar (added in PG 3.5)
;;

(eval-after-load "speedbar"
  '(and proof-assistant-symbol ;; *should* be set by now
	(speedbar-add-supported-extension
	 (nth 2 (assoc proof-assistant-symbol proof-assistant-table)))))

;;;###autoload
(defun proof-imenu-enable ()
  "Add or remove index menu."
  (if proof-imenu-enable
      (imenu-add-to-menubar "Index")
    (progn
      (let ((oldkeymap (keymap-parent (current-local-map))))
	(if ;; sanity checks in case someone else set local keymap
	    (and oldkeymap
		 (lookup-key (current-local-map) [menu-bar index])
		 (not
		  (lookup-key oldkeymap [menu-bar index])))
	    (use-local-map oldkeymap)))
      (remove-hook 'menu-bar-update-hook 'imenu-update-menubar))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Command history  (added in PG 3.7)
;;
;; This implements a history ring for commands in the locked region.
;; Inspired by (and code heavily copied from) comint in XEmacs.
;;
;; The current behaviour is not ideal: we only extend the input ring as
;; we process (so history does not browse pink text while the
;; prover is busy).  Moreover, instead of using a history, we might
;; simply parse commands backwards (or forwards) in the buffer.
;; (i.e, more like the copying behaviour implemented in Bibtex mode).
;;

(defvar pg-input-ring nil
  "Ring of previous inputs.")

(defvar pg-input-ring-index nil
  "Position of last matched command.")

(defvar pg-stored-incomplete-input nil
  "Stored incomplete input: string between point and locked.")

(defun pg-previous-input (arg)
  "Cycle backwards through input history, saving input."
  (interactive "*p")
  (if (and pg-input-ring-index
	   (or		       ;; leaving the "end" of the ring
	    (and (< arg 0)		; going down
		 (eq pg-input-ring-index 0))
	    (and (> arg 0)		; going up
		 (eq pg-input-ring-index
		     (1- (ring-length pg-input-ring)))))
	   pg-stored-incomplete-input)
      (pg-restore-input)
    (pg-previous-matching-input "." arg)))

(defun pg-next-input (arg)
  "Cycle forwards through input history."
  (interactive "*p")
  (pg-previous-input (- arg)))

(defun pg-delete-input ()
  (let* ((unproc (proof-unprocessed-begin))
	 (start  (save-excursion
		   (goto-char unproc)
		   (skip-chars-forward " \t\n")
		   (point)))
	 (end    (point-at-eol)))
    (cond
     ((< start end)
      (delete-region start end))
     ((< start (point-at-eol))
      (delete-region start (point-at-eol))))))

(defun pg-get-old-input ()
  "Return text between end of locked region and point, up to EOL.
If there is no text, return the empty string."
  (let* ((unproc (proof-unprocessed-begin))
	 (start  (save-excursion
		   (goto-char unproc)
		   (skip-chars-forward " \t\n")
		   (point)))
	 (end    (point-at-eol)))
    (if (< start end)
	(buffer-substring-no-properties start end)
      nil)))


(defun pg-restore-input ()
  "Restore unfinished input."
  (interactive)
  (when pg-input-ring-index
    (pg-delete-input)
    (when (> (length pg-stored-incomplete-input) 0)
      (insert pg-stored-incomplete-input)
      (message "Input restored"))
    (setq pg-input-ring-index nil)))


(defun pg-search-start (arg)
  "Index to start a directional search, starting at `pg-input-ring-index'."
  (if pg-input-ring-index
      ;; If a search is running, offset by 1 in direction of arg
      (mod (+ pg-input-ring-index (if (> arg 0) 1 -1))
	   (ring-length pg-input-ring))
    ;; For a new search, start from beginning or end, as appropriate
    (if (>= arg 0)
	0				       ; First elt for forward search
      (1- (ring-length pg-input-ring)))))  ; Last elt for backward search


(defun pg-regexp-arg (prompt)
  "Return list of regexp and prefix arg using PROMPT."
  (let* (;; Don't clobber this.
	 (last-command last-command)
	 (regexp (read-from-minibuffer prompt nil nil nil
				       'minibuffer-history-search-history)))
    (list (if (string-equal regexp "")
	      (setcar minibuffer-history-search-history
		      (nth 1 minibuffer-history-search-history))
	    regexp)
	  (prefix-numeric-value current-prefix-arg))))

(defun pg-search-arg (arg)
  ;; First make sure there is a ring and that we are after the process mark
  (cond ((not (>= (point) (proof-unprocessed-begin)))
	 (error "Not in unlocked region"))
	((or (null pg-input-ring)
	     (ring-empty-p pg-input-ring))
	 (error "Empty input ring"))
	((zerop arg)
	 ;; arg of zero resets search from beginning, and uses arg of 1
	 (setq pg-input-ring-index nil)
	 1)
	(t
	 arg)))

(defun pg-previous-matching-input-string-position (regexp arg &optional start)
  "Return the index matching REGEXP ARG places along the input ring.
Moves relative to START, or `pg-input-ring-index'."
  (if (or (not (ring-p pg-input-ring))
	  (ring-empty-p pg-input-ring))
      (error "No history"))
  (let* ((len (ring-length pg-input-ring))
	 (motion (if (> arg 0) 1 -1))
	 (n (mod (- (or start (pg-search-start arg)) motion) len))
	 (tried-each-ring-item nil)
	 (prev nil))
    ;; Do the whole search as many times as the argument says.
    (while (and (/= arg 0) (not tried-each-ring-item))
      ;; Step once.
      (setq prev n
	    n (mod (+ n motion) len))
      ;; If we haven't reached a match, step some more.
      (while (and (< n len) (not tried-each-ring-item)
		  (not (string-match regexp (ring-ref pg-input-ring n))))
	(setq n (mod (+ n motion) len)
	      ;; If we have gone all the way around in this search.
	      tried-each-ring-item (= n prev)))
      (setq arg (if (> arg 0) (1- arg) (1+ arg))))
    ;; Now that we know which ring element to use, if we found it, return that.
    (if (string-match regexp (ring-ref pg-input-ring n))
	n)))

(defun pg-previous-matching-input (regexp n)
  "Search backwards through input history for match for REGEXP.
\(Previous history elements are earlier commands.)
With prefix argument N, search for Nth previous match.
If N is negative, find the next or Nth next match."
  (interactive (pg-regexp-arg "Previous input matching (regexp): "))
  (setq n (pg-search-arg n))
  (let ((pos (pg-previous-matching-input-string-position regexp n)))
    ;; Has a match been found?
    (if (null pos)
	(error "Match not found for regexp %s" regexp)
      ;; If leaving the edit line, save partial input
      (if (null pg-input-ring-index)	;not yet on ring
	  (setq pg-stored-incomplete-input (pg-get-old-input)))
      (setq pg-input-ring-index pos)
      (message "History item: %d" (1+ pos))
      (pg-delete-input)
      (insert (ring-ref pg-input-ring pos)))))

(defun pg-next-matching-input (regexp n)
  "Search forwards through input history for match for REGEXP.
\(Later history elements are more recent commands.)
With prefix argument N, search for Nth following match.
If N is negative, find the previous or Nth previous match."
  (interactive (pg-regexp-arg "Next input matching (regexp): "))
  (pg-previous-matching-input regexp (- n)))

(defvar pg-matching-input-from-input-string ""
  "Input previously used to match input history.")

;;;###autoload
(defun pg-previous-matching-input-from-input (n)
  "Search backwards through input history for match for current input.
\(Previous history elements are earlier commands.)
With prefix argument N, search for Nth previous match.
If N is negative, search forwards for the -Nth following match."
  (interactive "p")
  (if (not (memq last-command '(pg-previous-matching-input-from-input
				pg-next-matching-input-from-input)))
      ;; Starting a new search
      (setq pg-matching-input-from-input-string (pg-get-old-input)
	    pg-input-ring-index nil))
  (if pg-matching-input-from-input-string
      (pg-previous-matching-input
       (concat "^" (regexp-quote pg-matching-input-from-input-string))
       n)
    (pg-previous-matching-input "." n)))

;;;###autoload
(defun pg-next-matching-input-from-input (n)
  "Search forwards through input history for match for current input.
\(Following history elements are more recent commands.)
With prefix argument N, search for Nth following match.
If N is negative, search backwards for the -Nth previous match."
  (interactive "p")
  (pg-previous-matching-input-from-input (- n)))



;;;###autoload
(defun pg-add-to-input-history (cmd)
   "Maybe add CMD to the input history.
CMD is only added to the input history if it is not a duplicate
of the last item added."
   (when (or (not (ring-p pg-input-ring))
	     (ring-empty-p pg-input-ring)
	     (not (string-equal (ring-ref pg-input-ring 0) cmd)))
     (unless (ring-p pg-input-ring)
       (setq pg-input-ring (make-ring pg-input-ring-size)))
     (ring-insert pg-input-ring cmd)))

;;;###autoload
(defun pg-remove-from-input-history (cmd)
  "Maybe remove CMD from the end of the input history.
This is called when the command is undone.  It's only
removed if it matches the last item in the ring."
  (if (and (ring-p pg-input-ring)
	   (not (ring-empty-p pg-input-ring))
	   (string-equal (ring-ref pg-input-ring 0) cmd))
      (ring-remove pg-input-ring 0)))
  

;;;###autoload
(defun  pg-clear-input-ring ()
  (setq pg-input-ring nil))


(provide 'pg-user)

;;; pg-user.el ends here
