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
(require 'proof-indent)

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
	    proof-shell-invisible-command
	    proof-response-buffer-display)))

;;
;;  Internal variables used by script mode
;;

(deflocal proof-active-buffer-fake-minor-mode nil
  "An indication in the modeline that this is the *active* script buffer")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A few small utilities					    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-match-find-next-function-name (buffer)
  "General next function name in BUFFER finder using match.
The regexp is assumed to be a two item list the car of which is the regexp
to use, and the cdr of which is the match position of the function
name. Moves point after the match.

The package fume-func provides the function
`fume-match-find-next-function-name' with the same specification.
However, fume-func's version is incorrect"
  ;; DO NOT USE save-excursion; we need to move point!
  ;; save-excursion is called at a higher level in the func-menu
  ;; package 
    (set-buffer buffer)
    (let ((r (car fume-function-name-regexp))
	  (p (cdr fume-function-name-regexp)))
      (and (re-search-forward r nil t)
	   (cons (buffer-substring (setq p (match-beginning p)) (point)) p))))

;; append-element in tl-list
(defun proof-append-element (ls elt)
  "Append ELT to last of LS if ELT is not nil. [proof.el]
This function coincides with `append-element' in the package
[tl-list.el.]"
  (if elt
      (append ls (list elt))
    ls))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic code for the locked region and the queue region            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME da: remove this dead code 
;; (defvar proof-locked-hwm nil
;;  "Upper limit of the locked region")
;; (defvar proof-queue-loose-end nil
;;  "Limit of the queue region that is not equal to proof-locked-hwm.")

(deflocal proof-locked-span nil
  "The locked span of the buffer.")

;; FIXME da: really we only need one queue span rather than one per
;; buffer, but I've made it local because the initialisation occurs in
;; proof-init-segmentation, which can happen when a file is visited.
;; So nasty things might happen if a locked file is visited whilst
;; another buffer has a non-empty queue region being processed.
(deflocal proof-queue-span nil
  "The queue span of the buffer.")

(defun proof-init-segmentation ()
  "Initialise the spans in a proof script buffer."
  ;; Initialise queue span, remove it from buffer.
  (if (not proof-queue-span)
      (setq proof-queue-span (make-span 1 1)))
  (set-span-property proof-queue-span 'start-closed t)
  (set-span-property proof-queue-span 'end-open t)
  (span-read-only proof-queue-span)
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
    (set-span-endpoints proof-locked-span (point-min) end)))

(defun proof-unprocessed-begin ()
  "Return end of locked region in current buffer or (point-min) otherwise."
  (or 
   (and (member (current-buffer) proof-script-buffer-list)
	proof-locked-span 
	(span-end proof-locked-span))
   (point-min)))

;; da: NEW function added 28.10.98.  This seems more
;; appropriate point to move point to (or make sure is displayed)
;; when a queue of commands is being processed.  The locked
;; end may be further away.
(defun proof-queue-or-locked-end ()
  "Return the end of the queue region, or locked region, or (point-min).
This position should be the first writable position in the buffer."
  (if (member (current-buffer) proof-script-buffer-list)
      (cond (proof-queue-span
	     (span-end proof-queue-span))
	    (proof-locked-span
	     (span-end proof-locked-span))
	    (t
	     (point-min)))))
	
(defun proof-locked-end ()
  "Return end of the locked region of the current buffer.
Only call this from a scripting buffer."
  (if (member (current-buffer) proof-script-buffer-list)
      (proof-unprocessed-begin)
    (error "bug: proof-locked-end called from wrong buffer")))

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
    (let ((instrumented (member buffer proof-script-buffer-list))
	  (span (make-span (proof-unprocessed-begin) (point-max)))
	  cmd)
      (if (eq proof-buffer-type 'script) 
	  ;; For a script buffer
	  (progn
	    (goto-char (point-min))
	    (proof-find-next-terminator)
	    (let ((cmd-list (member-if
			     (lambda (entry) (equal (car entry) 'cmd))
			     (proof-segment-up-to (point)))))
	      (or instrumented (proof-init-segmentation))
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
		(set-span-property span 'type 'comment)))
	    ;; Make sure a new proof script buffer enters the list
	    ;; of script buffers.
	    (or instrumented
		(setq proof-script-buffer-list
		      (append proof-script-buffer-list (list buffer)))))
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
	  ;; If the file is loaded into a buffer, which isn't
	  ;; the current scripting buffer, then put an
	  ;; atomic locked region in it.
	  (if (and buffer
		   proof-script-buffer-list
		   (not (equal cfile
			       (file-truename 
				(buffer-file-name
				 (car proof-script-buffer-list))))))
	      (proof-mark-buffer-atomic buffer))))))

;; three NEW predicates, let's use them!

(defun proof-locked-region-full-p ()
  "Non-nil if the locked region covers all the buffer's non-whitespace.
Should be called from a proof script buffer."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n")
    (>= (proof-unprocessed-begin) (point))))

(defun proof-locked-region-empty-p ()
  "Non-nil if the locked region is empty.
Should be called from a proof script buffer."
  (eq (proof-unprocessed-begin) (point-min)))

(defun proof-only-whitespace-to-locked-region-p ()
  "Non-nil if only whitespace separates point from end of locked region.
NB: If nil, point is left at first non-whitespace character found.
If non-nil, point is left where it was."
  (not (re-search-backward "\\S-" (proof-unprocessed-begin) t)))

(defun proof-activate-scripting ()
  "Activate scripting minor mode for current scripting buffer. 

The current buffer is prepared for scripting.  No changes are
necessary if it is already in Scripting minor mode. Otherwise, it
will become the current scripting buffer provided the current
scripting buffer has either no locked region or everything in it has
been processed.

When a new script buffer has scripting minor mode turned on,
the hooks `proof-activate-scripting-hook' are run."
  (cond 
   ((not (eq proof-buffer-type 'script)) 
    (error "Must be running in a script buffer"))

   ;; If the current buffer is the active one there's nothing to do.
   ((equal (current-buffer) (car-safe proof-script-buffer-list)))

   ;; Otherwise we need to activate a new Scripting buffer.
   (t
    (if proof-script-buffer-list
	(save-excursion
	  ;; We're switching from another scripting buffer
	  ;; to a new one.  Examine the old buffer.
	  (set-buffer (car proof-script-buffer-list))
	    
	  ;; We only allow switching of the Scripting buffer if the
	  ;; locked region is either empty or full for all buffers.
	  ;; FIXME: ponder alternative of trying to complete rest
	  ;; of current scripting buffer?
	  ;; FIXME: this test isn't necessary if the current
	  ;; buffer was already in proof-script-buffer-list.
	  (or (proof-locked-region-empty-p)
	      (proof-locked-region-full-p) ;; should be always t
	      (error 
	       "Cannot deal with two unfinished script buffers!"))
	    
	  (if (proof-locked-region-full-p)
	      ;; We're switching from a buffer which has been
	      ;; completely processed.  Make sure that it's
	      ;; registered on the included files list. 
	      (if buffer-file-name
		  (proof-register-possibly-new-processed-file 
		   buffer-file-name)))

	  ;; Turn off Scripting in the old buffer.
	  (setq proof-active-buffer-fake-minor-mode nil)))

    ;; does the new scripting buffer already have a locked region?
    (if (member (current-buffer) proof-script-buffer-list)
	;; If so, it must be moved to the head of the list
	(setq proof-script-buffer-list
	      (remove (current-buffer) proof-script-buffer-list))
      ;; If not, initialise the spans.
      (proof-init-segmentation))

    (setq proof-script-buffer-list
	  (cons (current-buffer) proof-script-buffer-list))

    ;; Turn on the minor mode, run hooks.
    (setq proof-active-buffer-fake-minor-mode t)
    (run-hooks 'proof-activate-scripting-hook)

    ;; Make status of active scripting buffer show up
    (if (fboundp 'redraw-modeline)
	(redraw-modeline)
      (force-mode-line-update))

    ;; This may be a good time to ask if the user wants to save some
    ;; buffers
    (save-some-buffers))))







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
  "If the end of the locked region is not visible, jump to the end of it.
A possible hook function for proof-shell-handle-error-hook."
  (interactive)
  (let* ((proof-script-buffer (car proof-script-buffer-list))
	 (pos (save-excursion
	       (set-buffer proof-script-buffer)
	       (proof-locked-end))))
    (or (pos-visible-in-window-p pos (get-buffer-window
				      proof-script-buffer t))
        (proof-goto-end-of-locked-interactive))))

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
; proof-send

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
  (let ((end (span-end span)) nam gspan next cmd)
    (proof-set-locked-end end)
    (proof-set-queue-start end)
    (setq cmd (span-property span 'cmd))
    (cond
     ((eq (span-property span 'type) 'comment)
      (set-span-property span 'mouse-face 'highlight))
     ((proof-check-atomic-sequents-lists span cmd end))
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
Default action if inside a comment is just process as far as the start of
the comment. If you want something different, put it inside
unclosed-comment-fun. If ignore-proof-process-p is set, no commands
will be added to the queue and the buffer will not be activated for
scripting."
  (interactive)
  (or ignore-proof-process-p 
      (progn
	(proof-shell-ready-prover)
	;; FIXME: check this
	(proof-activate-scripting)))
  (let ((semis))
    (save-excursion
      ;; Give error if no non-whitespace between point and end of locked region.
      (if (proof-only-whitespace-to-locked-region-p)
	  (error "I don't know what I should be doing in this buffer!"))
      ;; NB: (point) has now been moved backwards to first non-whitespace char.
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (null semis))
	  (error "I don't know what I should be doing in this buffer!"))
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
  (interactive)
  (or ignore-proof-process-p 
      (proof-shell-ready-prover))
  (proof-activate-scripting)
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
  "Updates display after proof process has reset its state. See also
the documentation for `proof-retract-until-point'. It optionally
deletes the region corresponding to the proof sequence."
  (let ((start (span-start span))
        (end (span-end span))
	(kill (span-property span 'delete-me)))
    (unless (proof-locked-region-empty-p)
      (proof-set-locked-end start)
      (proof-set-queue-end start))
    (delete-spans start end 'type)
    (delete-span span)
    (if kill (delete-region start end))))

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
  (proof-shell-ready-prover)
  (proof-activate-scripting)
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
  "Callback for proof-try-command."
  (delete-span span)
  (proof-detach-queue))
			
(defun proof-try-command (&optional unclosed-comment-fun) 
  "Process the command at point, but don't add it to the locked region. 
This will only happen if the command satisfies proof-state-preserving-p.

Default action if inside a comment is just to go until the start of
the comment. If you want something different, put it inside
unclosed-comment-fun."
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
    (if (buffer-live-p (car-safe proof-script-buffer-list))
	(progn
	  (set-buffer (car proof-script-buffer-list))
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
  "Prompt for a command in the minibuffer and send it to proof assistant."
  (interactive)
  (let (cmd)
    ;; FIXME note: removed ready-prover call since it's done by
    ;; proof-shell-invisible-command anyway.
    ;; (proof-shell-ready-prover)
    ;; was (proof-check-process-available 'relaxed) 
    (setq cmd (read-string "Command: " nil 'proof-minibuffer-history))
    (proof-shell-invisible-command cmd)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; command history  (unfinished)
;;
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

;;
;; end command history stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	  



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Popup and Pulldown Menu ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Menu commands for the underlying proof assistant

;;; These are defcustom'd so that users may re-configure
;;; the system to their liking.
;;; Functions using the above 

(defun proof-ctxt ()
  "List context."
  (interactive) 
  (proof-shell-invisible-command (concat proof-ctxt-string proof-terminal-string)))

(defun proof-help ()
  "Print help message giving syntax."
  (interactive)
  (proof-shell-invisible-command (concat proof-help-string proof-terminal-string)))

(defun proof-prf ()
  "List proof state."
  (interactive)
  (proof-shell-invisible-command (concat proof-prf-string proof-terminal-string)))



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
	 (funcall proof-goal-command))
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
	 (funcall proof-save-command))
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
(defun proof-menu-invoke-info ()
  "Call info on Proof General."
  (interactive)
  (info "ProofGeneral"))

(defun proof-menu-exit ()
  "Exit Proof-assistant."
  (interactive)
  (proof-restart-script))

(defvar proof-help-menu
  `("Help"
    [,(concat proof-assistant " web page")
     (browse-url proof-assistant-home-page) t]
    ["Proof General home page"
     (browse-url proof-proof-general-home-page) t]
    ["Proof General Info" proof-menu-invoke-info t]
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
     ["Exit proof assistant" proof-menu-exit
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
	  ;; UGLY COMPATIBILITY  FIXME: remove this soon
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
  "Toggle Proof General's active terminator minor mode.
With arg, turn on the Active Terminator minor mode if and only if arg
is positive.

If active terminator mode is enabled, a terminator will process the
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
  proof-mode-name
  "Proof General major mode class for proof scripts.
\\{proof-mode-map}"
  (setq proof-buffer-type 'script)

  ;; Has buffer already been processed?
  (and (member buffer-file-truename proof-included-files-list)
       (proof-mark-buffer-atomic (current-buffer)))

  (make-local-variable 'kill-buffer-hook)
  (add-hook 'kill-buffer-hook
	    (lambda ()
	      (setq proof-script-buffer-list
		    (remove (current-buffer) proof-script-buffer-list))))))

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

  ;; func-menu --- Jump to a goal within a buffer
  (and (boundp 'fume-function-name-regexp-alist)
       (defvar fume-function-name-regexp-proof
	 (cons proof-goal-with-hole-regexp 2))
       (push (cons major-mode 'fume-function-name-regexp-proof)
	     fume-function-name-regexp-alist))
  (and (boundp 'fume-find-function-name-method-alist)
       (push (cons major-mode 'proof-match-find-next-function-name)
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
  ;; (NB: autloads proof-toolbar, which extends proof-menu variable)
  (proof-toolbar-setup)

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
			       (list (customize-menu-create 'proof-general)
				     (customize-menu-create
				      'proof-general-internals
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



(provide 'proof-script)
;; proof-script.el ends here.
