;; proof-script.el  Major mode for proof assistant script files.
;;
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

(require 'proof)
(require 'proof-syntax)

;; If it's disabled by proof-script-indent, it won't need to be
;; loaded.
(autoload 'proof-indent-line "proof-indent" 
	   "Indent current line of proof script")


;; Spans are our abstraction of extents/overlays.
(eval-and-compile
  (cond ((fboundp 'make-extent) (require 'span-extent))
	((fboundp 'make-overlay) (require 'span-overlay))))

;; Nuke some byte-compiler warnings
(eval-when-compile
  (if (locate-library "func-menu") (require 'func-menu))
  (require 'comint))

;; FIXME:
;; More autoloads for proof-shell (added to nuke warnings,
;; maybe some should be 'official' exported functions in proof.el)
;; This helps see interface between proof-script / proof-shell.
(eval-when-compile
  (mapcar (lambda (f) 
	    (autoload f "proof-shell"))
	  '(proof-shell-ready-prover
	    proof-start-queue
	    proof-shell-live-buffer
	    proof-shell-invisible-command)))
;; proof-response-buffer-display now in proof.el, removed from above.

;; FIXME: *variable* proof-shell-proof-completed is declared in proof-shell
;; and used here.  Should be moved to proof.el or removed from here.

;;
;;  Internal variables used by script mode
;;

(deflocal proof-active-buffer-fake-minor-mode nil
  "An indication in the modeline that this is the *active* script buffer")



;;
;; Configuration of func-menu ("fume")	
;;
;; This code is only enabled if the user loads func-menu into Emacs.
;;

(eval-after-load "func-menu"	'(progn	; BEGIN if func-menu
;; BEGIN OLD
;; FIXME da: wasn't this supposed to return a cons of a string
;; and a buffer position?
;(defun proof-match-find-next-function-name (buffer)
;  "General next function name in BUFFER finder using match.
;The regexp is assumed to be a two item list the car of which is the regexp
;to use, and the cdr of which is the match position of the function
;name. Moves point after the match.

;The package fume-func provides the function
;`fume-match-find-next-function-name' with the same specification.
;However, fume-func's version is incorrect"
;  ;; DO NOT USE save-excursion; we need to move point!
;  ;; save-excursion is called at a higher level in the func-menu
;  ;; package 
;    (set-buffer buffer)
;    (let ((r (car fume-function-name-regexp))
;	  (p (cdr fume-function-name-regexp)))
;      (and (re-search-forward r nil t)
;	   (cons (buffer-substring (setq p (match-beginning p)) (point)) p))))
;; END OLD.

;; This is actually a fairly general function.

(deflocal proof-script-last-entity nil
  "Record of last entity found.   A hack for entities that are named
in two places, so that find-next-entity doesn't return the same values
twice.")

(defun proof-script-find-next-entity (buffer)
  "Find the next entity for function menu in a proof script.
A value for fume-find-function-name-method-alist for proof scripts.
Uses fume-function-name-regexp, which is intialised from 
proof-script-next-entity-regexps, which see."
  ;; Hopefully this function is fast enough.
  (set-buffer buffer)
  ;;  could as well use next-entity-regexps directly since this is
  ;;  not really meant to be used as a general function. 
  (let ((anyentity	(car fume-function-name-regexp)))
    (if (re-search-forward anyentity nil t)
	;; We've found some interesting entity, but have to find out
	;; which one, and where it begins.  
	(let ((entity (buffer-substring (match-beginning 0) (match-end 0)))
	      (start (match-beginning 0))
	      (discriminators (cdr fume-function-name-regexp))
	      (p (point))
	      disc res)
	  (while (and (not res) (setq disc (car-safe discriminators)))
	    (if (proof-string-match (car disc) entity)
		(let ((name (substring
			     entity
			     (match-beginning (nth 1 disc))
			     (match-end (nth 1 disc)))))
		  (cond
		   ((eq (nth 2 disc) 'backward)
		    (setq start
			  (or (re-search-backward (nth 3 disc) nil t)
			      start))
		    (goto-char p))
		   ((eq (nth 2 disc) 'forward)
		    (re-search-forward (nth 3 disc))))
		  (setq res (cons name start)))
	      (setq discriminators (cdr discriminators))))
	  res))))

))					; END if func-menu




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic code for the locked region and the queue region            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflocal proof-locked-span nil
  "The locked span of the buffer.
Each script buffer has its own locked span, which may be detached
from the buffer.
Proof General allows buffers in other modes also to be locked;
these also have a non-nil value for this variable.")

;; FIXME da: really we only need one queue span rather than one per
;; buffer, but I've made it local because the initialisation occurs in
;; proof-init-segmentation, which can happen when a file is visited.
;; So nasty things might happen if a locked file is visited whilst
;; another buffer has a non-empty queue region being processed.

(deflocal proof-queue-span nil
  "The queue span of the buffer.  May be detached if inactive or empty.")

;; FIXME da: really the queue region should always be locked strictly.

(defun proof-span-read-only (span)
  "Make span be read-only, if proof-strict-read-only is non-nil.
Otherwise make span give a warning message on edits."
  (if proof-strict-read-only
      (span-read-only span)
    (span-write-warning span)))

;; not implemented yet
;; (defun proof-toggle-strict-read-only ()
;;  "Toggle proof-strict-read-only, changing current spans."
;;  (interactive)
;;   map-spans blah
;;  )

(defun proof-init-segmentation ()
  "Initialise the queue and locked spans in a proof script buffer.
Allocate spans if need be.  The spans are detached from the
buffer, so the locked region is made empty by this function."
  ;; Initialise queue span, remove it from buffer.
  (if (not proof-queue-span)
      (setq proof-queue-span (make-span 1 1)))
  (set-span-property proof-queue-span 'start-closed t)
  (set-span-property proof-queue-span 'end-open t)
  (proof-span-read-only proof-queue-span)
  (set-span-property proof-queue-span 'face 'proof-queue-face)
  (detach-span proof-queue-span)
  ;;
  ;; FIXME da: remove this dead code
  ;; (setq proof-locked-hwm nil)
  ;;
  ;; Initialised locked span, remove it from buffer
  (if (not proof-locked-span)
      (setq proof-locked-span (make-span 1 1)))
  (set-span-property proof-locked-span 'start-closed t)
  (set-span-property proof-locked-span 'end-open t)
  (proof-span-read-only proof-locked-span)
  (set-span-property proof-locked-span 'face 'proof-locked-face)
  (detach-span proof-locked-span))

;; These two functions are used in coq.el to edit the locked region
;; (by lifting local (nested) lemmas out of a proof, to make them global).   
(defsubst proof-unlock-locked ()
  "Make the locked region writable.  
Used in lisp programs for temporary editing of the locked region.
See proof-lock-unlocked for the reverse operation."
  (span-read-write proof-locked-span))

(defsubst proof-lock-unlocked ()
  "Make the locked region read only (according to proof-strict-read-only).
Used in lisp programs for temporary editing of the locked region.
See proof-unlock-locked for the reverse operation."
  (proof-span-read-only proof-locked-span))

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

;; FIXME da: optional arg here was ignored, have fixed.
;; Do we really need it though?
(defun proof-detach-segments (&optional buffer)
  "Remove locked and queue region from BUFFER.
Defaults to current buffer when BUFFER is nil."
  (let ((buffer (or buffer (current-buffer))))
    (with-current-buffer buffer
      (proof-detach-queue)
      (proof-detach-locked))))

(defsubst proof-set-locked-end (end)
  "Set the end of the locked region to be END, sort of? FIXME.
If END is past the end of the buffer, remove the locked region.
Otherwise set the locked region to be from the start of the
buffer to END."
  (if (>= (point-min) end)
      (proof-detach-locked)
    (set-span-endpoints proof-locked-span (point-min) end)
    ;; FIXME: this doesn't fix the disappearing regions
    ;; span property is lost in latest FSF Emacs, maybe
    ;; (set-span-property proof-locked-span 'face 'proof-locked-face)
    ))

(defun proof-unprocessed-begin ()
  "Return end of locked region in current buffer or (point-min) otherwise."
  (or 
   (and proof-locked-span 
	(span-end proof-locked-span))
   (point-min)))

;; da: NEW function added 28.10.98.  This seems more
;; appropriate point to move point to (or make sure is displayed)
;; when a queue of commands is being processed.  The locked
;; end may be further away.
(defun proof-queue-or-locked-end ()
  "Return the end of the queue region, or locked region, or (point-min).
This position should be the first writable position in the buffer."
  (cond (proof-queue-span
	 (span-end proof-queue-span))
	(proof-locked-span
	 (span-end proof-locked-span))
	(t
	 (point-min))))

;; FIXME: get rid of this function.  Some places expect this
;; to return nil if locked region is empty.	
(defun proof-locked-end ()
  "Return end of the locked region of the current buffer.
Only call this from a scripting buffer."
  (proof-unprocessed-begin))

(defsubst proof-end-of-queue ()
  "Return the end of the queue region, or nil if none."
  (and proof-queue-span (span-end proof-queue-span)))

(defun proof-mark-buffer-atomic (buffer)
  "Mark BUFFER as having been processed in a single step.

If buffer already contains a locked region, only the remainder of the
buffer is closed off atomically.

This works for buffers which are not in proof scripting mode too,
to allow other files loaded by proof assistants to be marked read-only." 
  (save-excursion
    (set-buffer buffer)
    (let ((span (make-span (proof-unprocessed-begin) (point-max)))
	  cmd)
      (if (eq proof-buffer-type 'script) 
	  ;; For a script buffer
	  (progn
	    (goto-char (point-min))
	    (proof-find-next-terminator)
	    (let ((cmd-list (member-if
			     (lambda (entry) (equal (car entry) 'cmd))
			     (proof-segment-up-to (point)))))
	      ;; Reset queue and locked regions.
	      (proof-init-segmentation)
	      (if cmd-list 
		  (progn
		    (setq cmd (second (car cmd-list)))
		    (set-span-property span 'type 'vanilla)
		    (set-span-property span 'cmd cmd))
		;; If there was no command in the buffer, atomic span
		;; becomes a comment. This isn't quite right because
		;; the first ACS in a buffer could also be a goal-save
		;; span. We don't worry about this in the current
		;; implementation. This case should not happen in a
		;; LEGO module (because we assume that the first
		;; command is a module declaration). It should have no
		;; impact in Isabelle either (because there is no real
		;; retraction).
		(set-span-property span 'type 'comment))))
	;; For a non-script buffer
	(proof-init-segmentation)
	(set-span-property span 'type 'comment))
      ;; End of locked region is always end of buffer
      (proof-set-locked-end (point-max)))))

(defun proof-file-truename (filename)
  "Returns the true name of the file FILENAME or nil."
  (and filename (file-exists-p filename) (file-truename filename)))

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

(defun proof-warning (str)
  "Issue the warning STR."
    (proof-response-buffer-display str 'proof-warning-face)
    (proof-display-and-keep-buffer proof-response-buffer))

(defun proof-register-possibly-new-processed-file (file)
  "Register a possibly new FILE as having been processed by the prover."
  (let* ((cfile (file-truename file))
	 (buffer (proof-file-to-buffer cfile)))
    (if (not (member cfile proof-included-files-list))
	(progn
	  (and buffer
	       (buffer-modified-p buffer)
	       (proof-warning (concat "Changes to "
				      (buffer-name buffer)
				      " have not been saved!")))
	  (setq proof-included-files-list
		(cons cfile proof-included-files-list))
	  ;; If the file is loaded into a buffer, put an
	  ;; atomic locked region in it.
	  (if buffer
	      (proof-mark-buffer-atomic buffer))))))

(defun proof-unregister-buffer-file-name ()
  "Remove current buffer's filename from the list of included files.
No effect if the current buffer has no file name."
  (if buffer-file-name
      (let ((cfile (file-truename buffer-file-name)))
	(setq proof-included-files-list
	      (delete cfile proof-included-files-list)))))

;; three NEW predicates, let's use them!

(defun proof-locked-region-full-p ()
  "Non-nil if the locked region covers all the buffer's non-whitespace.
Should be called from a proof script buffer."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n")
    (>= (proof-unprocessed-begin) (point))))

;; FIXME: doesn't need to be called from proof script buffer now
;; proof-unprocessed-begin is generalised.
(defun proof-locked-region-empty-p ()
  "Non-nil if the locked region is empty."
  (eq (proof-unprocessed-begin) (point-min)))

(defun proof-only-whitespace-to-locked-region-p ()
  "Non-nil if only whitespace separates point from end of locked region.
Point should be after the locked region.
NB: If nil, point is left at first non-whitespace character found.
If non-nil, point is left where it was."
  (not (re-search-backward "\\S-" (proof-unprocessed-begin) t)))


(defun proof-activate-scripting ()
  "Activate scripting for the current script buffer.

The current buffer is prepared for scripting.  No changes are
necessary if it is already in Scripting minor mode. Otherwise, it
will become the current scripting buffer provided the current
scripting buffer has either no locked region or everything in it has
been processed.

If we're changing scripting buffer and the old one is associated with
a file, add it to proof-included-files-list.

When a new script buffer has scripting minor mode turned on,
the hooks `proof-activate-scripting-hook' are run.  This can
be a useful place to configure the proof assistant for
scripting in a particular file, for example, loading the
correct theory, or whatever.

Finally, this may be a good time to ask if the user wants to save some
buffers."
  (cond 
   ((not (eq proof-buffer-type 'script)) 
    (error "Must be running in a script buffer"))

   ;; If the current buffer is the active one there's nothing to do.
   ((equal (current-buffer) proof-script-buffer))

   ;; Otherwise we need to activate a new Scripting buffer.
   (t
    (if proof-script-buffer
	(save-excursion
	  ;; We're switching from another scripting buffer
	  ;; to a new one.  Examine the old buffer.
	  (set-buffer proof-script-buffer)
	    
	  ;; We only allow switching of the Scripting buffer if the
	  ;; locked region is either empty or full for all buffers.
	  ;; Give the user the chance to retract previous buffer here.
	  ;; FIXME: ponder alternative of trying to complete rest
	  ;; of current scripting buffer?  Allowing to switch when
	  ;; a goal has been completed?
	  (or (proof-locked-region-empty-p) 
	      (proof-locked-region-full-p)
	      (if (or
		   ;; User option to always force retaction
		   proof-auto-retract-other-buffers
		   (yes-or-no-p 
		    (format
		     "Scripting already active in buffer: %s, retract there? "
		     proof-script-buffer)))
		  (progn
		    ;; FIXME: Maybe want unwind protect here
		    (proof-retract-buffer)
		    ;; Test again to see if retracting happened/was successful
		    (or (proof-locked-region-empty-p)
			(proof-locked-region-full-p))))
	      (error "You cannot have more than one active scripting buffer!"))

	    
	  ;; Mess around a little bit with the included files
	  ;; list to make sure it behaves as we expect
	  ;; with respect to the active scripting buffer.
	  ;; This is and attempt to harmonize mixed scripting/file
	  ;; reading in the prover.

	  (if (proof-locked-region-full-p)
	      ;; We're switching from a buffer which has been
	      ;; completely processed.  Make sure that it's
	      ;; registered on the included files list.
	      (if buffer-file-name
		  (proof-register-possibly-new-processed-file 
		   buffer-file-name)))

	  ;; 11.12.98 Added this.
	  (if (proof-locked-region-empty-p)
	      ;; We switching from a buffer which is empty.
	      ;; Make sure that it's *off* the included files
	      ;; list now.  
	      (proof-unregister-buffer-file-name))

	  ;; Turn off Scripting in the old buffer.
	  (setq proof-active-buffer-fake-minor-mode nil)))

    ;; Set the active scripting buffer, and initialise the 
    ;; queue and locked regions if necessary.
    (setq proof-script-buffer (current-buffer))
    (if (proof-locked-region-empty-p)
	;; This removes any locked region that was there, but
	;; sometimes we switch on scripting in "full" buffers,
	;; so mustn't do this.
	(proof-init-segmentation))

    ;; Turn on the minor mode, run hooks.
    (setq proof-active-buffer-fake-minor-mode t)
    (run-hooks 'proof-activate-scripting-hook)

    ;; Make status of active scripting buffer show up
    (if (fboundp 'redraw-modeline)
	(redraw-modeline)
      (force-mode-line-update))

    ;; This may be a good time to ask if the user wants to save some
    ;; buffers.  On the other hand, it's jolly annoying to be
    ;; queried on the active scripting buffer if we've started
    ;; writing in it.  So pretend that one is unmodified.
    (let ((modified (buffer-modified-p)))
      (set-buffer-modified-p nil)
      (unwind-protect
	  (save-some-buffers)
	(set-buffer-modified-p modified))))))

;; This could be a subroutine to the above for a more sophisticated
;; behaviour upon switching.
(defun proof-deactivate-scripting ()
  "Deactivate scripting, if the current script buffer is active.
Set proof-script-buffer to nil and turn off the modeline indicator.
If the locked region doesn't cover the entire file, retract it."
  (interactive)
  (if (eq (current-buffer) proof-script-buffer)
      (let ((bname  (buffer-name proof-script-buffer)))
	(message "Turning off scripting in %s..." bname)
	(if (proof-locked-region-full-p)
	;; If the buffer *was* fully processed, 
	;; lets add it into the list of processed files.  
	    (if buffer-file-name
		(proof-register-possibly-new-processed-file 
		 buffer-file-name))
	  ;; If the buffer is not fully processed, 
	  ;; ensure it's removed from the list of included files
	  ;; and retract it if the locked region is non-empty.  
	  (goto-char (point-min))
	  (proof-unregister-buffer-file-name)
	  (unless (proof-locked-region-empty-p)
	    (condition-case nil
		;; If retraction fails (e.g. proof proc busy), 
		;; never mind.
		(proof-retract-until-point)
	      (error nil))))
	;; In any case, turn off the fake minor mode
	(setq proof-active-buffer-fake-minor-mode nil)
	;; Make status of active scripting buffer show up
	;; FIXME da:
	;; not really necessary when called by kill buffer, at least.
	(if (fboundp 'redraw-modeline)
	    (redraw-modeline)
	  (force-mode-line-update))
	;; And now there is no active scripting buffer
	(setq proof-script-buffer nil)
	(message "Turning off scripting in %s... done." bname))))





;;; begin messy COMPATIBILITY HACKING for FSFmacs.
;;; 
;;; In case Emacs is not aware of the function read-shell-command,
;;; and read-shell-command-map, we duplicate some code adjusted from
;;; minibuf.el distributed with XEmacs 20.4.
;;;
;;; This code is still required as of FSF Emacs 20.2.
;;;
;;; I think bothering with this just to give completion for
;;; when proof-prog-name-ask=t is a big overkill!   - da.
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


;;; end messy COMPATIBILITY HACKING


;;
;; Misc movement functions
;;

;; FIXME da: these next two functions slightly different, why?
;; (unprocessed-begin vs proof-locked-end)
(defun proof-goto-end-of-locked-interactive ()
  "Switch to proof-script-buffer and jump to the end of the locked region.
Must be an active scripting buffer."
  (interactive)
  (switch-to-buffer proof-script-buffer)
  (goto-char (proof-locked-end)))

(defun proof-goto-end-of-locked ()
  "Jump to the end of the locked region."
  (goto-char (proof-unprocessed-begin)))

(defun proof-in-locked-region-p ()
  "Non-nil if point is in locked region.  Assumes proof script buffer current."
  (< (point) (proof-locked-end)))

(defun proof-goto-end-of-locked-if-pos-not-visible-in-window ()
  "If the end of the locked region is not visible, jump to the end of it.
A possible hook function for proof-shell-handle-error-hook.
Does nothing if there is no active scripting buffer."
  (interactive)
  (if proof-script-buffer
      (let* ((pos (save-excursion
		    (set-buffer proof-script-buffer)
		    (proof-locked-end))))
	(or (pos-visible-in-window-p pos (get-buffer-window
					  proof-script-buffer t))
	    (proof-goto-end-of-locked-interactive)))))

;; da: NEW function added 28.10.98.
;; This is used by toolbar follow mode (which used to use the function
;; above).  [But wouldn't work for proof-shell-handle-error-hook?].

(defun proof-goto-end-of-queue-or-locked-if-not-visible ()
  "Jump to the end of the queue region or locked region if it isn't visible.
Assumes script buffer is current"
  (unless (pos-visible-in-window-p
	   (proof-queue-or-locked-end)
	   (get-buffer-window (current-buffer) t))
    (goto-char (proof-queue-or-locked-end))))



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
; proof-shell-insert

;;         proof-assert-until-point, and various gunk for its       ;;
;;         setup and callback                                       ;;


(defun proof-check-atomic-sequents-lists (span cmd end)
  "Check if CMD is the final command in an ACS.

If CMD is matched by the end regexp in `proof-atomic-sequents-list',
the ACS is marked in the current buffer. If CMD does not match any,
`nil' is returned, otherwise non-nil."
  ;;FIXME tms: needs implementation
  nil)

(defun proof-done-advancing (span)
  "The callback function for assert-until-point."
  ;; FIXME da: if the buffer dies, this function breaks.
  ;; Needs robustifying.
  (let ((end (span-end span)) nam gspan next cmd)
    (proof-set-locked-end end)
    (proof-set-queue-start end)
    (setq cmd (span-property span 'cmd))
    (cond
     ((eq (span-property span 'type) 'comment)
      (set-span-property span 'mouse-face 'highlight))
     ((proof-check-atomic-sequents-lists span cmd end))
     ((and (proof-string-match proof-save-command-regexp cmd)
	   (funcall proof-really-save-command-p span cmd))
      ;; First, clear the proof completed flag
      (setq proof-shell-proof-completed nil)
      ;; In coq, we have the invariant that if we've done a save and
      ;; there's a top-level declaration then it must be the
      ;; associated goal.  (Notice that because it's a callback it
      ;; must have been approved by the theorem prover.)
      (if (proof-string-match proof-save-with-hole-regexp cmd)
	  (setq nam (match-string 2 cmd)))
      (setq gspan span)
      (while (or (eq (span-property gspan 'type) 'comment)
		 (not (funcall proof-goal-command-p 
				    (setq cmd (span-property gspan 'cmd)))))
	(setq next (prev-span gspan 'type))
	(delete-span gspan)
	(setq gspan next))

      (if (null nam)
	  (if (proof-string-match proof-goal-with-hole-regexp
			    (span-property gspan 'cmd))
	      (setq nam (match-string 2 (span-property gspan 'cmd)))
	    ;; This only works for Coq, but LEGO raises an error if
	    ;; there's no name.
	    ;; FIXME da: maybe this should be prover specific: is
	    ;; "Unnamed_thm" actually a Coq identifier?
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
	   (funcall proof-lift-global span)))))

  ;; State of scripting may have changed now
  (run-hooks 'proof-state-change-hook))



;; FIXME da: Below it would probably be faster to use the primitive
;; skip-chars-forward rather than scanning character-by-character 
;; with a lisp loop over the whole region. Also I'm not convinced that
;; Emacs should be better at skipping whitespace and comments than the
;; proof process itself!

;; FIXME da: this annoyingly slow even in a buffer only several
;; hundred lines long, even when compiled.

(defun proof-segment-up-to (pos &optional next-command-end)
  "Create a list of (type,int,string) tuples from end of locked region to POS.
Each tuple denotes the command and the position of its terminator,
type is one of 'comment, or 'cmd. 'unclosed-comment may be consed onto
the start if the segment finishes with an unclosed comment.
If optional NEXT-COMMAND-END is non-nil, we contine past POS until
the next command end."
  (save-excursion
      ;; depth marks number of nested comments.
      ;; quote-parity is false if we're inside quotes.
      ;; Only one of (depth > 0) and (not quote-parity)
      ;; should be true at once. -- hhg
    (let ((str (make-string (- (buffer-size)
			       (proof-unprocessed-begin) -10) ?x))
	  (i 0) (depth 0) (quote-parity t) done alist c
	  (comment-end-regexp (regexp-quote proof-comment-end))
	  (comment-start-regexp (regexp-quote proof-comment-start)))
	  ;; For forthcoming improvements: skip over boring
	  ;; characters, calculate strings with buffer-substring
	  ;; rather than character at a time.
	  ; (interesting-chars
	  ; (concat (substring proof-comment-start 1 1)
	  ;	   (substring proof-comment-end 1 1)
	  ;	   (char-to-string proof-terminal-char)
	  ;	   "\"")))
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
	((and (looking-at comment-end-regexp) quote-parity)
	 (if (= depth 0) 
	     (progn
	       (message "Warning: extraneous comment end")
	       (setq done t))
	   (setq depth (- depth 1))
	   (forward-char (length (match-string 0)))
	   (if (eq i 0) 
	       (setq alist (cons (list 'comment "" (point)) alist))
	     (aset str i ?\ )
	     (incf i))))
	;; Case 4. Found a comment start, not inside a string
	((and (looking-at comment-start-regexp) quote-parity)
	 (setq depth (+ depth 1))
	 (forward-char (length (match-string 0))))
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

	 ;; Maintain quote-parity
	 (cond
	  ((and quote-parity (looking-at proof-string-start-regexp))
	   (setq quote-parity nil))
	  ((and (not quote-parity) (looking-at proof-string-end-regexp))
	   (setq quote-parity t)))

	 (forward-char)

	 ;; Found the end of a command
	 (if (and (= c proof-terminal-char) quote-parity)
	     (progn 
	       (setq alist 
		     (cons (list 'cmd (substring str 0 i) (point)) alist))
	       (cond
		((> (point) pos)
		 (setq done t))
		;; FIXME da: This case preserves the old behaviour, but I
		;; think it's wrong: should just have > case above.
		((and (not next-command-end) (= (point) pos))
		 (setq done t))
		(t
		 (setq i 0))))))))
     alist)))

(defun proof-semis-to-vanillas (semis &optional callback-fn)
  "Convert a sequence of terminator positions to a set of vanilla extents.
Proof terminator positions SEMIS has the form returned by
the function proof-segment-up-to."
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
	(setq alist (cons (list span proof-no-command 'proof-done-advancing) 
			  alist)))
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


(defun proof-assert-until-point-interactive ()
  "Process the region from the end of the locked-region until point.
Default action if inside a comment is just process as far as the start of
the comment."
  (interactive)
  (proof-assert-until-point))


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
Default action if inside a comment is just process as far as the start of
the comment. 

If you want something different, put it inside
UNCLOSED-COMMENT-FUN. If IGNORE-PROOF-PROCESS-P is set, no commands
will be added to the queue and the buffer will not be activated for
scripting."
  (unless ignore-proof-process-p 
    (proof-shell-ready-prover)
    (proof-activate-scripting))
  (let ((semis))
    (save-excursion
      ;; Give error if no non-whitespace between point and end of locked region.
      ;; FIXME da: a nasty mess
      (if (proof-only-whitespace-to-locked-region-p)
	  (error "There's nothing to do in this buffer!"))
      ;; NB: (point) has now been moved backwards to first non-whitespace char.
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (null semis))
	  (error "There's nothing to do in this buffer!"))
      (goto-char (nth 2 (car semis)))
      (and (not ignore-proof-process-p)
	   (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
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

(defun proof-assert-next-command-interactive ()
  "Process until the end of the next unprocessed command after point.
If inside a comment, just process until the start of the comment."
  (interactive)
  (proof-assert-next-command))
  
(defun proof-assert-next-command
  (&optional unclosed-comment-fun ignore-proof-process-p
	     dont-move-forward for-new-command)
  "Process until the end of the next unprocessed command after point.
If inside a comment, just process until the start of the comment.  

If you want something different, put it inside UNCLOSED-COMMENT-FUN. 
If IGNORE-PROOF-PROCESS-P is set, no commands will be added to the queue.
Afterwards, move forward to near the next command afterwards, unless
DONT-MOVE-FORWARD is non-nil.  If FOR-NEW-COMMAND is non-nil,
a space or newline will be inserted automatically."
  (unless ignore-proof-process-p
    (proof-shell-ready-prover)
    ;; FIXME: check this
    (proof-activate-scripting))
  (or ignore-proof-process-p
      (if (proof-locked-region-full-p)
	  (error "Locked region is full, no more commands to do!")))
  (let ((semis))
    (save-excursion
      ;; CHANGE from old proof-assert-until-point: don't bother check
      ;; for non-whitespace between locked region and point.
      ;; CHANGE: ask proof-segment-up-to to scan until command end
      ;; (which it used to do anyway, except in the case of a comment)
      (setq semis (proof-segment-up-to (point) t)))
    ;; old code:
    ;;(if (not (re-search-backward "\\S-" (proof-unprocessed-begin) t))
    ;;	  (progn (goto-char pt)
    ;;       (error "I don't know what I should be doing in this buffer!")))
    ;; (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car-safe semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car-safe semis))
	  (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (null semis))
	  (error "I don't know what I should be doing in this buffer!"))
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
  (proof-shell-ready-prover)			; FIXME
  (proof-activate-scripting)
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
  "Update display after proof process has reset its state.
See also the documentation for `proof-retract-until-point'.
Optionally delete the region corresponding to the proof sequence."
  ;; 10.9.99: da: added this line so that undo always clears the
  ;; proof completed flag.  Maybe this belongs elsewhere.
  (setq proof-shell-proof-completed nil)
  (if (span-live-p span)
      (let ((start (span-start span))
	    (end (span-end span))
	    (kill (span-property span 'delete-me)))
	(unless (proof-locked-region-empty-p)
	  (proof-set-locked-end start)
	  (proof-set-queue-end start))
	(delete-spans start end 'type)
	(delete-span span)
	(if kill (kill-region start end))))
  ;; State of scripting may have changed now
  (run-hooks 'proof-state-change-hook))

(defun proof-setup-retract-action (start end proof-command delete-region)
  (let ((span (make-span start end)))
    (set-span-property span 'delete-me delete-region)
    (list (list span proof-command 'proof-done-retracting))))


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

(defun proof-retract-target (target delete-region)
  "Retract the span TARGET and delete it if DELETE-REGION is non-nil.
Notice that this necessitates retracting any spans following TARGET,
up to the end of the locked region."
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
	  
	  (setq actions 
		(proof-setup-retract-action (span-start span) end
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

;; FIXME da: Maybe retraction to the start of
;; a file should remove it from the list of included files?
(defun proof-retract-until-point-interactive (&optional delete-region)
  "Tell the proof process to retract until point.
If invoked outside a locked region, undo the last successfully processed
command.  If called with a prefix argument (DELETE-REGION non-nil), also
delete the retracted region from the proof-script."
  (interactive "P")
  (proof-retract-until-point delete-region))

(defun proof-retract-until-point (&optional delete-region)
  "Set up the proof process for retracting until point.
In particular, set a flag for the filter process to call 
`proof-done-retracting' after the proof process has successfully 
reset its state.
If DELETE-REGION is non-nil, delete the region in the proof script
corresponding to the proof command sequence.
If invoked outside a locked region, undo the last successfully processed
command."
  (proof-shell-ready-prover)
  (proof-activate-scripting)
  (let ((span (span-at (point) 'type)))
    ;; FIXME da: shouldn't this test be earlier??
    (if (proof-locked-region-empty-p)
	(error "No locked region"))
    ;; FIXME da: rationalize this: it retracts the last span
    ;; in the buffer if there was no span at point, right?
    ;; why?
    (and (null span)
	 (progn 
	   (proof-goto-end-of-locked) 
	   (backward-char)
	   (setq span (span-at (point) 'type))))
    (proof-retract-target span delete-region)))

;;         proof-try-command                                        ;;
;;         this isn't really in the spirit of script management,    ;;
;;         but sometimes the user wants to just try an expression   ;;
;;         without having to undo it in order to try something      ;;
;;         different. Of course you can easily lose sync by doing   ;;
;;         something here which changes the proof state             ;;

(defun proof-done-trying (span)
  "Callback for proof-try-command."
  (delete-span span)
  (proof-detach-queue))
			
(defun proof-try-command (&optional unclosed-comment-fun) 
  "Process the command at point, but don't add it to the locked region. 

Supplied to let the user to test the types and values of
expressions. Checks via the function proof-state-preserving-p that the
command won't change the proof state, but this isn't guaranteed to be
foolproof and may cause Proof General to lose sync with the prover.

Default action if inside a comment is just to go until the start of
the comment. If you want something different, put it inside
UNCLOSED-COMMENT-FUN."
  (interactive)
  (proof-shell-ready-prover)
  (proof-activate-scripting)
  (let ((pt (point)) semis test)
    (save-excursion
      (if (proof-only-whitespace-to-locked-region-p)
	  (progn (goto-char pt)
		 (error "I don't know what I should be doing in this buffer!")))
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (null semis) 
	  (error "I don't know what I should be doing in this buffer!"))
      (setq test (car semis))
      (if (not (funcall proof-state-preserving-p (nth 1 test)))
	  (error "Command is not state preserving, I won't try it."))
      (goto-char (nth 2 test))
      (let ((vanillas (proof-semis-to-vanillas (list test)
					       'proof-done-trying)))
	(proof-start-queue (proof-unprocessed-begin) (point) vanillas)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;         misc other user functions                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME: it turns out that this function is identical to the one below.
(defun proof-undo-last-successful-command-interactive (delete)
  "Undo last successful command at end of locked region.
If DELETE argument is set (called with a prefix argument), 
the text is also deleted from the proof script."
  (interactive "P")
  (proof-undo-last-successful-command (not delete)))

(defun proof-undo-last-successful-command (&optional no-delete)
  "Undo last successful command at end of locked region.
Unless optional NO-DELETE is set, the text is also deleted from
the proof script."
  (unless (proof-locked-region-empty-p)
    (let ((lastspan (span-at-before (proof-locked-end) 'type)))
      (if lastspan
	  (progn
	    (goto-char (span-start lastspan))
	    (proof-retract-until-point (not no-delete)))
	(error "Nothing to undo!")))))


;; FIXME da: need to add some way of recovery here.  Perhaps
;; query process as to its state as well.  Also unwind protects
;; here.

;; FIXME da: this probably belongs in proof-shell, as do
;; some of the following functions.

(defun proof-interrupt-process ()
  "Interrupt the proof assistant.  Warning! This may confuse Proof General."
  (interactive)
  (if (not (proof-shell-live-buffer))
      (error "Proof Process Not Started!"))
  ; 1.10.99 da: removed this test, it seems silly.
  ; (if (not (eq (current-buffer) proof-script-buffer))
  ;    (error "Don't own process!"))
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
;      (and (re-search-forward "\\S-" nil t)
;	   (proof-assert-until-point nil 'ignore-proof-process)))))
      (proof-assert-next-command nil 'ignore-proof-process))))

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
  (proof-assert-until-point-interactive))

(defun proof-retract-buffer ()
  "Retract the current buffer and set point at the start of the buffer."
  (interactive)
  (goto-char (point-min))
  (proof-retract-until-point-interactive))

;; FIXME da: this could do with some tweaking.  Be careful to
;; avoid memory leaks.  If a buffer is killed and it's local
;; variables are, then so should all the spans which were allocated
;; for that buffer.  Is this what happens?  By garbage collection?
;; Otherwise we should perhaps *delete* spans corresponding to 
;; the locked and queue regions as well as the others.
(defun proof-restart-buffers (buffers)
  "Remove all extents in BUFFERS and maybe reset `proof-script-buffer'.
No effect on a buffer which is nil or killed.  If one of the buffers
is the current scripting buffer, then proof-script-buffer 
will deactivated."
  (mapcar
   (lambda (buffer)
     (save-excursion
       (if (buffer-live-p buffer)
	   (with-current-buffer buffer
	     (if proof-active-buffer-fake-minor-mode
		 (setq proof-active-buffer-fake-minor-mode nil))
	     (delete-spans (point-min) (point-max) 'type)
	     (proof-detach-segments buffer)
	     ;; 29.9.99. Added next line to allow useful toggling
	     ;; of strict-read-only during a session.
	     (proof-init-segmentation)))
       (if (eq buffer proof-script-buffer)
	   (setq proof-script-buffer nil))))
   buffers))

(defun proof-script-buffers-with-spans ()
  "Return a list of all buffers with spans.
This is calculated by finding all the buffers with a non-nil
value of proof-locked span."
  (let ((bufs-left (buffer-list)) 
	bufs-got)
    (dolist (buf bufs-left bufs-got)
      (if (with-current-buffer buf proof-locked-span)
	  (setq bufs-got (cons buf bufs-got))))))

(defun proof-script-remove-all-spans-and-deactivate ()
  "Remove all spans from scripting buffers via proof-restart-buffers."
  (proof-restart-buffers (proof-script-buffers-with-spans)))

;; THIS HAS BEEN REPLACED WITH proof-shell-exit, proof-shell-restart.

;(defun proof-restart-script ()
;  "Restart Proof General.
;Re-initialise the proof assistant by sending the restart command,
;and clear all locked regions."
;  (interactive)
;  (proof-script-remove-all-spans-and-deactivate)
;  (setq proof-included-files nil
;	proof-shell-busy nil
;	proof-shell-proof-completed nil)
;  (if (buffer-live-p proof-shell-buffer) 
;      (kill-buffer proof-shell-buffer))
;  (if (buffer-live-p proof-goals-buffer)
;      (kill-buffer proof-goals-buffer))
;  (and (buffer-live-p proof-response-buffer)
;       (kill-buffer proof-response-buffer)))



;; A command for making things go horribly wrong - it moves the
;; end-of-locked-region marker backwards, so user had better move it
;; correctly to sync with the proof state, or things will go all
;; pear-shaped.

(defun proof-frob-locked-end ()
  (interactive)
  "Move the end of the locked region backwards. 
Only for use by consenting adults."
  (cond
   ((not (eq (current-buffer) proof-script-buffer))
    (error "Not in active scripting buffer"))
   ((> (point) (proof-locked-end))
    (error "Can only move backwards"))
   (t (proof-set-locked-end (point))
      (delete-spans (proof-locked-end) (point-max) 'type))))

(defvar proof-minibuffer-history nil
  "History of proof commands read from the minibuffer")

(defun proof-execute-minibuffer-cmd ()
  "Prompt for a command in the minibuffer and send it to proof assistant.
The command isn't added to the locked region.

Warning! No checking whatsoever is done on the command, so this is
even more dangerous than proof-try-command."
  (interactive)
  (let (cmd)
    ;; FIXME note: removed ready-prover call since it's done by
    ;; proof-shell-invisible-command anyway.
    ;; (proof-shell-ready-prover)
    ;; was (proof-check-process-available 'relaxed) 
    (setq cmd (read-string "Command: " nil 'proof-minibuffer-history))
    (proof-shell-invisible-command 
     (if proof-terminal-string
	 (concat cmd proof-terminal-string)
       cmd))))




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
	  



;;; 
;;; User-level commands invoking common commands for
;;; the underlying proof assistant.
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



;;; FIXME: should move these to a new file, not really scripting
;;; related.

;;; FIXME: rationalize use of terminator string (i.e. remove
;;; it below, add it to each instance for consistency).


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

(defmacro proof-define-assistant-command (fn doc cmdvar)
  "Define command FN to send string CMDVAR to proof assistant."
  `(defun ,fn ()
     ,(concat doc "\nIssues a command to the assistant from " 
	      (symbol-name cmdvar) ".")
     (interactive)
     (proof-if-setting-configured ,cmdvar
       (proof-shell-invisible-command
	(concat ,cmdvar proof-terminal-string)))))

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
  (proof-assert-until-point-interactive))

;;
;; Commands which do not require a prompt and send an invisible command.
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

;;
;; Commands which require an argument, and maybe affect the script.
;;

(proof-define-assistant-command-witharg proof-find-theorems
 "Search for items containing a given constant."					
 proof-find-theorems-command
 "Find theorems containing the constant"
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



;;;
;;; Definition of Menus
;;;

;;; A handy utility function used in buffer menu.
(defun proof-switch-to-buffer (buf &optional noselect)
  "Switch to or display buffer BUF in other window unless already displayed.
If optional arg NOSELECT is true, don't switch, only display it.
No action if BUF is nil."
  ;; Maybe this needs to be more sophisticated, using 
  ;; proof-display-and-keep-buffer ?
  (and buf
       (unless (eq buf (window-buffer (selected-window)))
	 (if noselect
	     (display-buffer buf t)
	   (switch-to-buffer-other-window buf)))))

(defvar proof-help-menu
  `("Help"
    [,(concat proof-assistant " web page")
     (browse-url proof-assistant-home-page) t]
    ["Proof General home page"
     (browse-url proof-proof-general-home-page) t]
    ["Proof General Info"
     (info "ProofGeneral") t]
    )
  "Proof General help menu.")

(defvar proof-buffer-menu
  '("Buffers"
    ["Active scripting"
     (proof-switch-to-buffer proof-script-buffer)
     :active (buffer-live-p proof-script-buffer)]
    ["Goals"
     (proof-switch-to-buffer proof-goals-buffer t)
     :active (buffer-live-p proof-goals-buffer)]
    ["Response"
     (proof-switch-to-buffer proof-response-buffer t)
     :active (buffer-live-p proof-response-buffer)]
    ["Shell"
     (proof-switch-to-buffer proof-shell-buffer)
     :active (buffer-live-p proof-shell-buffer)])
  "Proof General buffer menu.")

;; FIXME da: could move this elsewhere.  
;; FIXME da: rationalize toolbar menu items with this menu, i.e.
;; remove common stuff.
(defvar proof-shared-menu
  (append
    (list
;     ["Display proof state"
;      proof-prf
;      :active (proof-shell-live-buffer)]
;     ["Display context"
;      proof-ctxt
;      :active (proof-shell-live-buffer)]
;     ["Find theorems"
;      proof-find-theorems
;      :active (proof-shell-live-buffer)]
     ["Start proof assistant"
      proof-shell-start
      :active (not (proof-shell-live-buffer))]
;     ["Restart scripting"
;      proof-shell-restart
;      :active (proof-shell-live-buffer)]
     ["Exit proof assistant"
      proof-shell-exit
      :active (proof-shell-live-buffer)])
    (list proof-help-menu)
    (list proof-buffer-menu)
    ;; Would be nicer to put this at the bottom, but it's
    ;; a bit tricky then to get it in all menus.
    ;; UGLY COMPATIBILITY  FIXME: remove this soon
    (list (if (string-match "XEmacs 19.1[2-9]" emacs-version)
	      "--:doubleLine" "----"))
    )
  "Proof General menu for various modes.")

(defvar proof-bug-report-menu
  (append
   ;; UGLY COMPATIBILITY  FIXME: remove this soon
   (list (if (string-match "XEmacs 19.1[2-9]" emacs-version)
	     "--:doubleLine" "----"))
   (list
    ["Submit bug report"
     proof-submit-bug-report
     :active t]))
  "Proof General menu for submitting bug report (one item plus separator).")


(defvar proof-menu  
  (append '(["Active terminator" proof-active-terminator-minor-mode
	     :active t
	     :style toggle
             :selected proof-active-terminator-minor-mode]
	    ["Toolbar" proof-toolbar-toggle
	       :active (featurep 'toolbar)
	       :style toggle
	       :selected (not proof-toolbar-inhibit)]
	    "----")
	  ;; UGLY COMPATIBILITY  FIXME: remove this soon
          (list (if (string-match "XEmacs 19.1[2-9]" emacs-version)
		    "--:doubleLine" "----"))
          proof-shared-menu
          )
  "The menu for the proof assistant.")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Active terminator minor mode                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME: Paul Callaghan wants to make the default for this be
;; 't'.  Perhaps we need a user option which configures the default.
;; Moreover, this minor mode is only relevant to scripting
;; buffers, so a buffer-local setting may be inappropriate.
(deflocal proof-active-terminator-minor-mode nil 
  "Active terminator minor mode flag")

;; Make sure proof-active-terminator-minor-mode is registered
(or (assq 'proof-active-terminator-minor-mode minor-mode-alist)
    (setq minor-mode-alist
	  (append minor-mode-alist
		  (list '(proof-active-terminator-minor-mode
			  (concat " " proof-terminal-string))))))

(defun proof-active-terminator-minor-mode (&optional arg)
  "Toggle Proof General's active terminator minor mode.
With ARG, turn on the Active Terminator minor mode if and only if ARG
is positive.

If active terminator mode is enabled, pressing a terminator will 
automatically activate `proof-assert-next-command' for convenience."
 (interactive "P")
 (setq proof-active-terminator-minor-mode
       (if (null arg) (not proof-active-terminator-minor-mode)
	 (> (prefix-numeric-value arg) 0)))
 (if (fboundp 'redraw-modeline)
     (redraw-modeline)
   (force-mode-line-update)))

(defun proof-process-active-terminator ()
  "Insert the proof command terminator, and assert up to it."
  (let ((mrk (point)) ins incomment)
    (if (looking-at "\\s-\\|\\'\\|\\w") 
	(if (proof-only-whitespace-to-locked-region-p)
	    (error "I don't know what I should be doing in this buffer!")))
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
;; Proof General scripting mode definition			    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; da: this isn't so nice if a scripting buffer should inherit
;; from another mode: e.g. for Isabelle, we would like to use
;; sml-mode.
;; FIXME: add more doc to the mode below, to give hints on
;; configuring for new assistants.

;;;###autoload
(eval-and-compile			; to define vars
(define-derived-mode proof-mode fundamental-mode 
  proof-general-name
  "Proof General major mode class for proof scripts.
\\{proof-mode-map}"
  (setq proof-buffer-type 'script)

  (make-local-hook 'kill-buffer-hook)
  (add-hook 'kill-buffer-hook 'proof-script-kill-buffer-fn t t)))

(defun proof-script-kill-buffer-fn ()
  "Value of kill-buffer-hook for proof script buffers.
Clean up before a script buffer is killed.
If killing the active scripting buffer, run proof-deactivate-scripting.
Otherwise just do proof-restart-buffers to delete some spans from memory."
  ;; Deactivate scripting in the current buffer if need be.
  (if (eq (current-buffer) proof-script-buffer)
      (proof-deactivate-scripting))
  (proof-restart-buffers (list (current-buffer)))
  ;; Hide away goals and response: this is a hack because otherwise
  ;; we can lead the user to frustration with the dedicated windows
  ;; nonsense.
  (if proof-goals-buffer (bury-buffer proof-goals-buffer))
  (if proof-response-buffer (bury-buffer proof-response-buffer)))
  

;; Fixed definitions in proof-mode-map, which don't depend on
;; prover configuration.
;;; INDENT HACK: font-lock only recognizes define-key at start of line
(let ((map proof-mode-map))
(define-key map [(control c) (control e)] 'proof-find-next-terminator)
(define-key map [(control c) (control a)] 'proof-goto-command-start)

;; Sep'99. FIXME: key maps need reorganizing, so do the assert-until style
;; functions.   I've re-bound C-c C-n and C-c C-u to the toolbar functions
;; to make the behaviour the same.  People find the "enhanced" behaviour
;; of the other functions confusing.  Moreover the optional argument
;; to delete is a bad thing for C-c C-u, since repeating it fast will 
;; tend to delete!
(define-key map [(control c) (control n)] 'proof-toolbar-next)
(define-key map [(control c) (control u)] 'proof-toolbar-undo)
(define-key map [(control c) (control b)] 'proof-toolbar-use)
(define-key map [(control c) (control r)] 'proof-toolbar-retract) ;; new binding

;;;; (define-key map [(control c) (control n)] 'proof-assert-next-command-interactive)
;; FIXME : This ought to be set to 'proof-assert-until point
(define-key map [(control c) (return)]	  'proof-assert-next-command-interactive)
(define-key map [(control c) (control t)] 'proof-try-command)
;; FIXME: The following two functions should be unified.
(define-key map [(control c) ?u]	  'proof-retract-until-point-interactive)
;;;; (define-key map [(control c) (control u)] 'proof-undo-last-successful-command-interactive)
(define-key map [(control c) ?\']	  'proof-goto-end-of-locked-interactive)
;; FIXME da: this command copies a proof command from within the locked region
;; to the end of it at the moment (contrary to the old name "send", nothing to
;; do with shell).  Perhaps we could define a
;; collection of useful copying functions which do this kind of thing.
(define-key map [(control button1)]	  'proof-mouse-track-insert)
;;; (define-key map [(control c) (control b)] 'proof-process-buffer)

(define-key map [(control c) (control z)] 'proof-frob-locked-end)
(define-key map [(control c) (control p)] 'proof-prf)
(define-key map [(control c) ?c]	  'proof-ctxt)
;; NB: next binding overwrites comint-find-source-code.  Anyone miss it?
(define-key map [(control c) (control f)] 'proof-find-theorems)
(define-key map [(control c) ?f]	  'proof-help)
;; FIXME: not implemented yet 
;; (define-key map [(meta p)]		  'proof-previous-matching-command)
;; (define-key map [(meta n)]		  'proof-next-matching-command)
(proof-define-keys map proof-universal-keys))



;; the following callback is an irritating hack - there should be some
;; elegant mechanism for computing constants after the child has
;; configured.

(defun proof-config-done () 
  "Finish setup of Proof General scripting mode.
Call this function in the derived mode for the proof assistant to
finish setup which depends on specific proof assistant configuration."
  ;; Has buffer already been processed?
  ;; NB: call to file-truename is needed for FSF Emacs which
  ;; chooses to make buffer-file-truename abbreviate-file-name
  ;; form of file-truename.
  (and buffer-file-truename
       (member (file-truename buffer-file-truename)
	       proof-included-files-list)
       (proof-mark-buffer-atomic (current-buffer)))

  ;; calculate some strings and regexps for searching
  (setq proof-terminal-string (char-to-string proof-terminal-char))

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

  ;; Additional key definitions which depend on configuration for
  ;; specific proof assistant.
  (define-key proof-mode-map
    (vconcat [(control c)] (vector proof-terminal-char))
    'proof-active-terminator-minor-mode)

  (define-key proof-mode-map (vector proof-terminal-char)
    'proof-active-terminator)

  (make-local-variable 'indent-line-function)
  (if proof-script-indent
      (setq indent-line-function 'proof-indent-line))

  ;; Toolbar and scripting menu
  ;; NB: autloads proof-toolbar, which defines proof-toolbar-scripting-menu.
  (proof-toolbar-setup)

  ;; Menu
  (easy-menu-define proof-mode-menu  
		    proof-mode-map
		    "Proof General menu"
		    (cons proof-general-name
			  (append
			   proof-toolbar-scripting-menu
			   proof-menu
			   ;; begin UGLY COMPATIBILTY HACK
			   ;; older/non-existent customize doesn't have 
			   ;; this function.  
			   (if (fboundp 'customize-menu-create)
			       (list (customize-menu-create 'proof-general)
				     (customize-menu-create
				      'proof-general-internals
				      "Internals"))
			     nil)
			   ;; end UGLY COMPATIBILTY HACK
			   proof-bug-report-menu
			   )))

  ;; Put the ProofGeneral menu on the menubar
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

  ;; Assume font-lock case folding follows proof-case-fold-search
  (setq font-lock-keywords-case-fold-search proof-case-fold-search)

  ;; Make sure func menu is configured.  (NB: Ideal place for this and
  ;; similar stuff would be in something evaluated at top level after
  ;; defining the derived mode: normally we wouldn't repeat this
  ;; each time the mode function is run, so we wouldn't need "pushnew").

  (cond ((featurep 'func-menu)
	 (unless proof-script-next-entity-regexps ; unless already set
	   ;; Try to calculate a useful default value.
	   ;; FIXME: this is rather complicated!  The use of the regexp
	   ;; variables needs sorting out. 
	     (customize-set-variable
	      'proof-script-next-entity-regexps
	      (let ((goal-discrim
		     ;; Goal discriminator searches forward for matching
		     ;; save if the regexp is set.
		     (if proof-goal-with-hole-regexp
			 (if proof-save-command-regexp
			     (list
			      proof-goal-with-hole-regexp 2
			      'forward proof-save-command-regexp)
			   (list proof-goal-with-hole-regexp 2))))
		    ;; Save discriminator searches backward for matching
		    ;; goal if the regexp is set.
		    (save-discrim
		     (if proof-save-with-hole-regexp
			 (if proof-goal-command-regexp
			     (list
			      proof-save-with-hole-regexp 2
			      'backward proof-goal-command-regexp)
			   (list proof-save-with-hole-regexp 2)))))
		(cond
		 ((and proof-goal-with-hole-regexp proof-save-with-hole-regexp)
		  (list
		   (proof-regexp-alt
		    proof-goal-with-hole-regexp
		    proof-save-with-hole-regexp) goal-discrim save-discrim))
		  
		 (proof-goal-with-hole-regexp
		  (list proof-goal-with-hole-regexp goal-discrim))
		 
		 (proof-save-with-hole-regexp
		  (list proof-save-with-hole-regexp save-discrim))))))

	   (if proof-script-next-entity-regexps
	       ;; Enable func-menu for this mode if regexps set
	       (progn
		 (pushnew
		  (cons major-mode 'proof-script-next-entity-regexps)
		  fume-function-name-regexp-alist)
		 (pushnew
		  (cons major-mode proof-script-find-next-entity-fn)
		  fume-find-function-name-method-alist)))))

  ;; Offer to save script mode buffers which have no files,
  ;; in case Emacs is exited accidently.
  (or (buffer-file-name)
      (setq buffer-offer-save t)))


(provide 'proof-script)
;; proof-script.el ends here.

;; 
;;; Lo%al Va%iables:
;;; eval: (put 'proof-if-setting-configured 'lisp-indent-function 1)
;;; eval: (put 'proof-define-assistant-command 'lisp-indent-function 'defun)
;;; eval: (put 'proof-define-assistant-command-wtharg 'lisp-indent-function 'defun)
;;; End:

