;; proof-script.el  Major mode for proof assistant script files.
;;
;; Copyright (C) 1994-2001 LFCS Edinburgh. 
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

(require 'proof)			; loader
(require 'proof-syntax)			; utils for manipulating syntax
(require 'span)				; abstraction of overlays/extents
(require 'pg-user)			; user-level commands
(require 'proof-menu)			; menus for script mode



;; Nuke some byte-compiler warnings 
;; NB: eval-when (compile) is different to eval-when-compile!!
(eval-when (compile)
  (proof-try-require 'func-menu)
  (require 'comint))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  PRIVATE VARIABLES 
;;
;;  Local variables used by proof-script-mode
;;

;; Scripting variables

(defvar proof-last-theorem-dependencies nil
  "Contains the dependencies of the last theorem.  A list of strings.
Set in proof-shell-process-urgent-message.")

(defvar proof-nesting-depth 0
  "Current depth of a nested proof.  
Zero means outside a proof, 1 means inside a top-level proof, etc.

This variable is maintained in proof-done-advancing; it is zeroed
in proof-shell-clear-state.")

(defvar proof-element-counters nil
  "Table of (name . count) pairs, counting elements in scripting buffer.")


;; Buffer-local variables

(deflocal proof-active-buffer-fake-minor-mode nil
  "An indication in the modeline that this is the *active* script buffer")

(deflocal proof-script-buffer-file-name nil
  ;; NB: if buffer-file-name is nil for some other reason, this may break.
   "A copied value of buffer-file-name to cope with `find-alternative-file'.
The `find-alternative-file' function has a nasty habit of setting the
buffer file name to nil before running kill buffer, which breaks PG's
kill buffer hook.  This variable is used when buffer-file-name is nil.")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Counting and naming proof elements
;;

(defun proof-next-element-count (idiom)
  "Return count for next element of type IDIOM.
This uses and updates `proof-element-counters'."
  (let ((next (1+ (or (cdr-safe (assq idiom proof-element-counters)) 0))))
    (setq proof-element-counters 
	  (cons (cons idiom next) 
		(remassq idiom proof-element-counters)))
    next))

(defun proof-element-id (idiom number)
  "Return a string identifier composed from symbol IDIOM and NUMBER."
  (concat (symbol-name idiom) "-" (int-to-string number)))

(defun proof-next-element-id (idiom)
  (proof-element-id idiom (proof-next-element-count idiom)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Configuration of function-menu (aka "fume")	
;;
;; FIXME: we would like this code only enabled if the user loads
;; func-menu into Emacs.
;;

(deflocal proof-script-last-entity nil
  "Record of last entity found.   
A hack for entities that are named in two places, so that find-next-entity 
doesn't return the same values twice.")

;; FIXME mmw: maybe handle comments/strings by using
;; proof-looking-at-syntactic-context 
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
    (if (proof-re-search-forward anyentity nil t)
	;; We've found some interesting entity, but have to find out
	;; which one, and where it begins.  
	(let ((entity (buffer-substring (match-beginning 0) (match-end 0)))
	      (start (match-beginning 0))
	      (discriminators (cdr fume-function-name-regexp))
	      (p (point))
	      disc res)
	  (while (and (not res) (setq disc (car-safe discriminators)))
	    (if (proof-string-match (car disc) entity)
		(let*
		    ((items (nth 1 disc))
		     (items (if (numberp items) (list items) items))
		     (name ""))
		  (dolist (item items)
		    (setq name
			  (concat name
				  (substring entity
					     (match-beginning item)
					     (match-end item))
				  " ")))
		  (cond
		   ((eq (nth 2 disc) 'backward)
		    (setq start
			  (or (proof-re-search-backward (nth 3 disc) nil t)
			      start))
		    (goto-char p))
		   ((eq (nth 2 disc) 'forward)
		    (proof-re-search-forward (nth 3 disc))))
		  (setq res (cons name start)))
	      (setq discriminators (cdr discriminators))))
	  res))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Basic functions for handling the locked and queue regions
;; 
;; --------------------------------------------------------------
;;
;; Notes on regions in the scripting buffer. (da)
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
;;     'goalsave     A goal..savegoal region in the buffer, a completed proof.
;;     'vanilla      Initialised in proof-semis-to-vanillas, for
;;     'comment      A comment outside a command.
;;     'proverproc   A region closed by the prover, processed outwith PG
;;     'pbp	     A PBP command inserted automatically into the script
;;
;;  All spans except those of type 'comment have a 'cmd property,
;;  which is set to a string of its command.  This is the
;;  text in the buffer stripped of leading whitespace and any comments.
;;

;; ** Variables

(deflocal proof-locked-span nil
  "The locked span of the buffer.
Each script buffer has its own locked span, which may be detached
from the buffer.
Proof General allows buffers in other modes also to be locked;
these also have a non-nil value for this variable.")

(deflocal proof-queue-span nil
  "The queue span of the buffer.  May be detached if inactive or empty.
Each script buffer has its own queue span, although only the active
scripting buffer may have an active queue span.")
;; da: reason for buffer local queue span is because initialisation
;; in proof-init-segmentation can happen when a file is visited.
;; So nasty things might happen if a locked file is visited whilst
;; another buffer has a non-empty queue region being processed.


;; ** Getters and setters

(defun proof-span-read-only (span)
  "Make span be read-only, if proof-strict-read-only is non-nil.
Otherwise make span give a warning message on edits."
  ;; Note: perhaps the queue region should always be locked strictly.
  (if proof-strict-read-only
      (span-read-only span)
    (span-write-warning span)))

;; not implemented yet: presently must toggle via restarting scripting
;; (defun proof-toggle-strict-read-only ()
;;  "Toggle proof-strict-read-only, changing current spans."
;;  (interactive)
;;   map-spans blah
;;  )

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

(defsubst proof-set-locked-end (end)
  "Set the end of the locked region to be END.
If END is at or before (point-min), remove the locked region.
Otherwise set the locked region to be from (point-min) to END."
  ;; FIXME: is it really needed to detach the span here?
  (if (>= (point-min) end)
      (proof-detach-locked)
    (set-span-endpoints 
     proof-locked-span 
     (point-min) 
     (min (point-max) end) ;; safety: sometimes called with end>point-max(?)
    )))

;; Reimplemented this to mirror above because of remaining
;; span problen
(defsubst proof-set-queue-end (end)
  "Set the queue span to end at END."
  (if (or (>= (point-min) end)
	  (<= end (span-start proof-queue-span)))
      (proof-detach-queue)
    (set-span-end proof-queue-span end)))


;; ** Initialise spans for a buffer

(defun proof-init-segmentation ()
  "Initialise the queue and locked spans in a proof script buffer.
Allocate spans if need be.  The spans are detached from the
buffer, so the regions are made empty by this function.
Also clear list of script portions."
  ;; Initialise queue span, remove it from buffer.
  (unless proof-queue-span
      (setq proof-queue-span (make-span 1 1))
      ;; FIXME: span-raise is an GNU hack to make locked span appear.
      ;; overlays still don't work as well as they did/should pre 99.
      (span-raise proof-queue-span))
  (set-span-property proof-queue-span 'start-closed t)
  (set-span-property proof-queue-span 'end-open t)
  (proof-span-read-only proof-queue-span)
  (set-span-property proof-queue-span 'face 'proof-queue-face)
  (detach-span proof-queue-span)
  ;; Initialise locked span, remove it from buffer
  (unless proof-locked-span
      (setq proof-locked-span (make-span 1 1))
      (span-raise proof-locked-span))
  (set-span-property proof-locked-span 'start-closed t)
  (set-span-property proof-locked-span 'end-open t)
  (proof-span-read-only proof-locked-span)
  (set-span-property proof-locked-span 'face 'proof-locked-face)
  (detach-span proof-locked-span)
  (setq proof-last-theorem-dependencies nil)
  (setq proof-element-counters nil)
  (pg-clear-script-portions))


;; ** Restarting and clearing spans 

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
	     (delete-spans (point-min) (point-max) 'type)  ;; remove top-level spans
	     (delete-spans (point-min) (point-max) 'idiom) ;; and embedded spans
	     (setq pg-script-portions nil)		   ;; also the record of them
	     (proof-detach-queue)	                   ;; remove queue and locked
	     (proof-detach-locked)
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

(defun proof-script-clear-queue-spans ()
  "If there is an active scripting buffer, remove the queue span from it.
This is a subroutine used in proof-shell-handle-{error,interrupt}."
  (if proof-script-buffer
      (with-current-buffer proof-script-buffer
	(proof-detach-queue)
	;; FIXME da: point-max seems a bit excessive here,
	;; proof-queue-or-locked-end should be enough.
	(delete-spans (proof-locked-end) (point-max) 'type))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Buffer position functions
;;

(defun proof-unprocessed-begin ()
  "Return end of locked region in current buffer or (point-min) otherwise.
The position is actually one beyond the last locked character."
  (or 
   (and proof-locked-span 
	(span-end proof-locked-span))
   (point-min)))

(defun proof-script-end ()
  "Return the character beyond the last non-whitespace character.
This is the same position proof-locked-end ends up at when asserting
the script.  Works for any kind of buffer."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n")
    (point)))

(defun proof-queue-or-locked-end ()
  "Return the end of the queue region, or locked region, or (point-min).
This position should be the first writable position in the buffer.
An appropriate point to move point to (or make sure is displayed)
when a queue of commands is being processed."
  (or	
   ;; span-end returns nil if span is detatched
   (and proof-queue-span (span-end proof-queue-span))
   (and proof-locked-span (span-end proof-locked-span))
   (point-min)))

;; FIXME: get rid of/rework this function.  Some places expect this to
;; return nil if locked region is empty. Moreover, it confusingly
;; returns the point past the end of the locked region.
(defun proof-locked-end ()
  "Return end of the locked region of the current buffer.
Only call this from a scripting buffer."
  (proof-unprocessed-begin))
  



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Predicates for locked region.  
;;
;; These work on any buffer, so that non-script buffers can be locked
;; (as processed files) too.
;;

(defun proof-locked-region-full-p ()
  "Non-nil if the locked region covers all the buffer's non-whitespace.
Works on any buffer."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n")
    (>= (proof-unprocessed-begin) (point))))

(defun proof-locked-region-empty-p ()
  "Non-nil if the locked region is empty.  Works on any buffer."
  (eq (proof-unprocessed-begin) (point-min)))

(defun proof-only-whitespace-to-locked-region-p ()
  "Non-nil if only whitespace separates char after point from end of locked region.
Point should be after the locked region.
NB: If nil, point is left at first non-whitespace character found.
If non-nil, point is left where it was."
  ;; NB: this function doesn't quite do what you'd expect, but fixing it
  ;; breaks proof-assert-until-point and electric-terminator which
  ;; rely on the side effect.  So careful!
  ;; (unless (eobp)
  ;; (forward-char))
  ;;   (save-excursion  -- no, side effect is expected!
  (not (proof-re-search-backward "\\S-" (proof-unprocessed-begin) t)))

(defun proof-in-locked-region-p ()
  "Non-nil if point is in locked region.  Assumes proof script buffer current."
  (< (point) (proof-unprocessed-begin)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Misc movement functions
;;

(defun proof-goto-end-of-locked (&optional switch)
  "Jump to the end of the locked region, maybe switching to script buffer.
If interactive or SWITCH is non-nil, switch to script buffer first."
  (interactive)
  (proof-with-script-buffer
   (if (and (not (get-buffer-window proof-script-buffer))
	    (or switch (interactive-p)))
       (switch-to-buffer proof-script-buffer)
     (goto-char (proof-unprocessed-begin)))))

;; Careful: movement can happen when the user is typing, not very nice!
(defun proof-goto-end-of-locked-if-pos-not-visible-in-window ()
  "If the end of the locked region is not visible, jump to the end of it.
A possible hook function for proof-shell-handle-error-or-interrupt-hook.
Does nothing if there is no active scripting buffer, or if
`proof-follow-mode' is set to 'ignore."
  (interactive)
  (if (and proof-script-buffer
	   (not (eq proof-follow-mode 'ignore)))
      (let ((pos (with-current-buffer proof-script-buffer
		   (proof-locked-end)))
	    (win (get-buffer-window proof-script-buffer t)))
	(unless (and win (pos-visible-in-window-p pos))
	  (proof-goto-end-of-locked t)))))

;; Simplified version of above for toolbar follow mode -- which wouldn't
;; work with abouve because of proof-shell-handle-error-or-interrupt-hook[?]
(defun proof-goto-end-of-queue-or-locked-if-not-visible ()
  "Jump to the end of the queue region or locked region if it isn't visible.
Assumes script buffer is current"
  (unless (pos-visible-in-window-p
	   (proof-queue-or-locked-end)
	   (get-buffer-window (current-buffer) t))
    (goto-char (proof-queue-or-locked-end))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Names of proofs (and other elements) in a script
;; 
;; New in PG 3.3
;;
;; Each kind of part ("idiom") in a proof script has its own name space.
;; Visibility within a script is then handled with buffer-invisibility-spec
;; controlling appearance of each idiom.
;;
;; TODO:
;;   -- Use fine-scale and large scale control, after all?
;;   -- Deleting spans must remove their entries in pg-script-portions !!
;;   -- Names should be made unique somehow.

;; FIXME: this should be a configuration variable
(defvar pg-idioms '(proof)
  "Vector of script element kinds PG is aware of for this prover.")

(deflocal pg-script-portions nil
  "Table of lists of symbols naming script portions which have been processed so far.")

(defun pg-clear-script-portions ()
  "Clear record of script portion names and types from internal list.
Also clear all visibility specifications."
  (setq pg-script-portions nil)
  (setq buffer-invisibility-spec nil))

(defun pg-add-script-element (elt)
  (add-to-list pg-script-portions elt))

(defun pg-remove-script-element (ns id)
  (let* ((elts	   (cdr-safe (assq ns pg-script-portions)))
	 (newelts  (remq id elts)))
    (setq pg-script-portions
	  (if newelts
	      (cons (cons ns newelts) (remassq ns pg-script-portions))
	    (remassq ns pg-script-portions)))))

(defsubst pg-visname (namespace id)
  "Return a unique symbol made from strings NAMESPACE and unique ID."
  (intern (concat namespace ":" id)))

(defun pg-add-element (idiom id span &optional name)
  "Add element of type IDIOM with identifier ID, referred to by SPAN.
This records the element in `pg-script-portions' and sets span
properties accordingly.  
IDIOM, ID, and optional NAME are all strings.
Identifiers must be unique for a given idiom; the optional NAME
will be recorded as a textual name used instead of ID for users;
NAME does not need to be unique."
  (let* ((idiomsym (intern idiom))
	 (idsym    (intern id))
	 (name	   (or name id))
	 (visname  (pg-visname idiom id))
	 (delfn	   `(lambda () (pg-remove-element (quote ,idiomsym) (quote ,idsym))))
	 (elts	   (cdr-safe (assq idiomsym pg-script-portions))))
    (if elts
	(if (memq id elts)
	    (proof-debug "Element named " name " (type " idiom ") already in buffer.")
	  (nconc elts (list idsym)))
      (setq pg-script-portions (cons (cons idiomsym (list idsym)) 
				     pg-script-portions)))
    ;; Idiom and ID are stored in the span as symbols; name as a string.
    (set-span-property span 'idiom idiomsym)
    (set-span-property span 'id idsym)
    (set-span-property span 'name name)
    (set-span-property span 'span-delete-action delfn)
    (set-span-property span 'invisible visname)
    ;; Bad behaviour if span gets copied: unique ID shouldn't be duplicated.
    (set-span-property span 'duplicable nil)
    ;; Nice behaviour in with isearch: open invisible regions temporarily.
    (set-span-property span 'isearch-open-invisible 
		       'pg-open-invisible-span)
    (set-span-property span 'isearch-open-invisible-temporary
		       'pg-open-invisible-span)))

(defun pg-open-invisible-span (span &optional invisible)
  "Function for `isearch-open-invisible' property."
  (let ((idiom  (span-property span 'idiom))
	(id	(span-property span 'id)))
    (and idiom id 
	 (if invisible
	     (pg-make-element-invisible
	      (symbol-name idiom) id)
	   (pg-make-element-visible
	      (symbol-name idiom) (symbol-name id))))))

(defun pg-remove-element (ns idsym)
  (pg-remove-script-element ns idsym)
  ;; We could leave the visibility note, but that may
  ;; be counterintuitive, so lets remove it.
  (pg-make-element-visible (symbol-name ns) (symbol-name idsym)))

(defun pg-make-element-invisible (idiom id)
  "Make element ID of type IDIOM invisible, with ellipsis."
  (add-to-list 'buffer-invisibility-spec 
	       (cons (pg-visname idiom id) t)))

(defun pg-make-element-visible (idiom id)
  (setq buffer-invisibility-spec
	(remassq (pg-visname idiom id) buffer-invisibility-spec)))

(defun pg-toggle-element-visibility (idiom id)
  (if (and (listp buffer-invisibility-spec) 
	   (assq (pg-visname idiom id) buffer-invisibility-spec))
      (pg-make-element-visible idiom id)
    (pg-make-element-invisible idiom id)))

(defun pg-show-all-portions (idiom &optional hide)
  "Show or hide all portions of kind IDIOM"
  (interactive
   (list 
    (completing-read 
     (concat "Make " (if current-prefix-arg "in" "") "visible all regions of: ")
     (apply 'vector pg-idioms) nil t)
    current-prefix-arg))
  (let ((elts      (cdr-safe (assq (intern idiom) pg-script-portions)))
	(alterfn   (if hide
		       (lambda (arg) (pg-make-element-invisible idiom 
								(symbol-name arg)))
		     (lambda (arg) (pg-make-element-visible idiom 
							    (symbol-name arg))))))
    (mapcar alterfn elts))
  (unless proof-running-on-XEmacs
    ;; GNU Emacs requires redisplay here to see result
    ;; (sit-for 0) not enough
    (redraw-frame (selected-frame))))

;; Next two could be in pg-user.el.  No key-bindings for these.
(defun pg-show-all-proofs ()
  "Display all completed proofs in the buffer."
  (interactive)
  (pg-show-all-portions "proof"))

(defun pg-hide-all-proofs ()
  "Hide all completed proofs in the buffer."
  (interactive)
  (pg-show-all-portions "proof" 'hide))

(defun pg-add-proof-element (name span controlspan)
  "Add a nested span proof element."
  (let ((proofid   (proof-next-element-id 'proof)))
    (pg-add-element "proof"  proofid span name)
    ;; Set id in controlspan
    (set-span-property controlspan 'id (intern proofid))
    ;; Make a navigable link between the two spans.
    (set-span-property span 'controlspan controlspan)
    (set-span-property controlspan 'children
		       (cons span (span-property controlspan 'children)))
    (pg-set-span-helphighlights span 'nohighlight)
    (if proof-disappearing-proofs 
	(pg-make-element-invisible "proof" proofid))))

(defun pg-span-name (span)
  "Return a user-level name for SPAN."
  (let ((type    (span-property span 'type))
	(idiom   (span-property span 'idiom))
	(name    (span-property span 'name)))
    (cond 
     (idiom
      (concat (upcase-initials (symbol-name idiom))
	      (if name (concat ": " name))))
     ((or (eq type 'proof) (eq type 'goalsave))
      (concat "Proof" 
	      (let ((name (span-property span 'name)))
		(if name (concat " of " name)))))
     ((eq type 'comment)   "Comment")
     ((eq type 'vanilla)   "Command")
     ((eq type 'pbp)       "PBP command")
     ((eq type 'proverproc)
		           "Prover-processed region"))))

(defun pg-set-span-helphighlights (span &optional nohighlight)
  "Set the help echo message, default highlight, and keymap for SPAN."
  (let ((helpmsg (pg-span-name span)))
    (set-span-property span 'balloon-help helpmsg)
    (set-span-property span 'help-echo helpmsg)
    (set-span-property span 'keymap pg-span-context-menu-keymap)
    (unless nohighlight
      (set-span-property span 'mouse-face 'proof-mouse-highlight-face))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling
;;
(defun proof-complete-buffer-atomic (buffer)
  "Make sure BUFFER is marked as completely processed, completing with a single step.

If buffer already contains a locked region, only the remainder of the
buffer is closed off atomically.

This works for buffers which are not in proof scripting mode too,
to allow other files loaded by proof assistants to be marked read-only." 
;; NB: this isn't quite right, because not all of the structure in the
;; locked region will be preserved when processing across several
;; files.  In particular, the span for a currently open goal should be
;; removed.  Keeping the structure is an approximation to make up for
;; the fact that that no structure is created by loading files via the
;; proof assistant.  Future ideas: proof assistant could ask Proof
;; General to do the loading, to alleviate file handling there;
;; we could cache meta-data resulting from processing files; 
;; or even, could include parsing inside PG.
  (save-excursion
    (set-buffer buffer)
    (if (< (proof-unprocessed-begin) (proof-script-end))
	(let ((span (make-span (proof-unprocessed-begin) 
			       (proof-script-end)))
	      cmd)
	  (if (eq proof-buffer-type 'script) 
	      ;; For a script buffer
	      (progn
		(goto-char (point-min))
		(proof-goto-command-end)
		(let ((cmd-list (member-if
				 (lambda (entry) (equal (car entry) 'cmd))
				 (proof-segment-up-to (point)))))
		  ;; Reset queue and locked regions.
		  (proof-init-segmentation)
		  (if cmd-list 
		      (progn
			;; FIXME 3.3 da: this can be simplified now,
			;; we don't need to set cmd for proverproc
			(setq cmd (second (car cmd-list)))
			(set-span-property span 'type 'proverproc)
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
	  (proof-set-locked-end (proof-script-end))))))





;; FIXME da: cleanup of odd asymmetry here: we have a nice setting for
;; proof-register-possibly-new-processed-file but something much more
;; complicated for retracting, because we allow a hook function
;; to calculate the new included files list.

(defun proof-register-possibly-new-processed-file (file &optional informprover noquestions)
  "Register a possibly new FILE as having been processed by the prover.

If INFORMPROVER is non-nil, the proof assistant will be told about this,
to co-ordinate with its internal file-management.  (Otherwise we assume
that it is a message from the proof assistant which triggers this call).
In this case, the user will be queried to save some buffers, unless
NOQUESTIONS is non-nil.

No action is taken if the file is already registered.

A warning message is issued if the register request came from the
proof assistant and Emacs has a modified buffer visiting the file."
  (let* ((cfile (file-truename file))
	 (buffer (proof-file-to-buffer cfile)))
    (proof-debug (concat "Registering file " cfile 
			 (if (member cfile proof-included-files-list)
			     " (already registered, no action)." ".")))
    (unless (member cfile proof-included-files-list)
      (and buffer
	   (not informprover)
	   (buffer-modified-p buffer)
	   (proof-warning (concat "Changes to "
				  (buffer-name buffer)
				  " have not been saved!")))
      ;; Add the new file onto the front of the list
      (setq proof-included-files-list
	    (cons cfile proof-included-files-list))
      ;; If the file is loaded into a buffer, make sure it is completely locked
      (if buffer
	  (proof-complete-buffer-atomic buffer))
      ;; Tell the proof assistant, if we should and if we can
      (if (and informprover proof-shell-inform-file-processed-cmd)
	  (progn
	    ;; Markus suggests we should ask if the user wants to save
	    ;; the file now (presumably because the proof assistant
	    ;; might examine the file timestamp, or attempt to visit
	    ;; the file later??).
	    ;; Presumably it would be enough to ask about this file,
	    ;; not all files?
	    (if (and
		 proof-query-file-save-when-activating-scripting
		 (not noquestions))
		(unwind-protect
		    (save-some-buffers)))
	    ;; Tell the prover 
	    (proof-shell-invisible-command 
	     (proof-format-filename proof-shell-inform-file-processed-cmd 
				    cfile) 
	     'wait))))))

(defun proof-inform-prover-file-retracted (rfile)
  (if proof-shell-inform-file-retracted-cmd
      (proof-shell-invisible-command
       (proof-format-filename proof-shell-inform-file-retracted-cmd 
			      rfile)
       'wait)))

(defun proof-auto-retract-dependencies (cfile &optional informprover)
  "Perhaps automatically retract the (linear) dependencies of CFILE.
If proof-auto-multiple-files is nil, no action is taken.
If CFILE does not appear on proof-included-files-list, no action taken.

Any buffers which are visiting files in proof-included-files-list
before CFILE are retracted using proof-protected-process-or-retract.
They are retracted in reverse order.

Since the proof-included-files-list is examined, we expect scripting
to be turned off before calling here (because turning it off could
otherwise change proof-included-files-list).

If INFORMPROVER is non-nil,  the proof assistant will be told about this,
using proof-shell-inform-file-retracted-cmd, to co-ordinate with its 
internal file-management.

Files which are not visited by any buffer are not retracted, on the
basis that we may not have the information necessary to retract them
-- spans that cover the buffer with definition/declaration
information.  A warning message is given for these cases, since it
could cause inconsistency problems.

NB!  Retraction can cause recursive calls of this function.
This is a subroutine for proof-unregister-buffer-file-name."
  (if proof-auto-multiple-files
      (let ((depfiles (reverse
		       (cdr-safe
			(member cfile (reverse proof-included-files-list)))))
	    rfile rbuf)
	(while (setq rfile (car-safe depfiles))
	  ;; If there's a buffer visiting a dependent file, retract it.
	  ;; We test that the file to retract hasn't been retracted
	  ;; already by a recursive call here.  (But since we do retraction
	  ;; in reverse order, this shouldn't happen...)
	  (if (and (member rfile proof-included-files-list) 
		   (setq rbuf (proof-file-to-buffer rfile)))
	      (progn
		(proof-debug "Automatically retracting " rfile)
		(proof-protected-process-or-retract 'retract rbuf)
		(setq proof-included-files-list 
		      (delete rfile proof-included-files-list))
		;; Tell the proof assistant, if we should and we can.
		;; This may be useful if we synchronise the *prover* with
		;; PG's management of multiple files.  If the *prover*
		;; informs PG (better case), then we hope the prover will
		;; retract dependent files and we shouldn't use this
		;; degenerate (linear dependency) code.
		(if informprover
		    (proof-inform-prover-file-retracted rfile)))
	    ;; If no buffer available, issue a warning that nothing was done
	    (proof-warning "Not retracting unvisited file " rfile))
	  (setq depfiles (cdr depfiles))))))

(defun proof-unregister-buffer-file-name (&optional informprover)
  "Remove current buffer's filename from the list of included files.
No effect if the current buffer has no file name.
If INFORMPROVER is non-nil,  the proof assistant will be told about this,
using proof-shell-inform-file-retracted-cmd, to co-ordinate with its 
internal file-management.

If proof-auto-multiple-files is non-nil, any buffers on 
proof-included-files-list before this one will be automatically
retracted using proof-auto-retract-dependencies."
  (if buffer-file-name
      (let ((cfile (file-truename 
		    (or buffer-file-name
			proof-script-buffer-file-name))))
	(proof-debug (concat "Unregistering file " cfile 
			       (if (not (member cfile 
						proof-included-files-list))
				   " (not registered, no action)." ".")))
	(if (member cfile proof-included-files-list)
	    (progn
	      (proof-auto-retract-dependencies cfile informprover)
	      (setq proof-included-files-list
		    (delete cfile proof-included-files-list))
	      ;; Tell the proof assistant, if we should and we can.
	      ;; This case may be useful if there is a combined 
	      ;; management of multiple files between PG and prover.
	      (if informprover
		  (proof-inform-prover-file-retracted cfile)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Activating and Deactivating Scripting
;;
;; The notion of "active scripting buffer" clarifies how 
;; scripting across multiple files is handled.  Only one
;; script buffer is allowed to be active, and actions are
;; taken when scripting is turned off/on.
;;

(defun proof-protected-process-or-retract (action &optional buffer)
  "If ACTION='process, process, If ACTION='retract, retract.
Process or retract the current buffer, which should be the active
scripting buffer, according to ACTION.
Retract buffer BUFFER if set, otherwise use the current buffer.
Gives a message in the minibuffer and busy-waits for the retraction
or processing to complete.  If it fails for some reason, 
an error is signalled here."
  (let ((fn   (cond ((eq action 'process) 'proof-process-buffer)
		    ((eq action 'retract) 'proof-retract-buffer)))
	(name (cond ((eq action 'process) "Processing")
		    ((eq action 'retract) "Retracting")))
	(buf  (or buffer (current-buffer))))
    (if fn
	(unwind-protect
	    (with-current-buffer buf
	      (message "%s buffer %s..." name buf)
	      (funcall fn)
	      (while proof-shell-busy ; busy wait
		(sit-for 1))
	      (message "%s buffer %s...done." name buf)
	      (sit-for 0))
	  ;; Test to see if action was successful
	  (with-current-buffer buf
	    (or (and (eq action 'retract) (proof-locked-region-empty-p))
		(and (eq action 'process) (proof-locked-region-full-p))
		(error "%s of %s failed!" name buf)))))))

(defun proof-deactivate-scripting-auto () 
  "Deactivate scripting without asking questions or raising errors.
If the locked region is full, register the file as processed.
Otherwise retract it.  Errors are ignored"
  (ignore-errors
    (proof-deactivate-scripting
     (proof-with-script-buffer
      (if (proof-locked-region-full-p) 'process 'retract)))))

(defun proof-deactivate-scripting (&optional forcedaction)
  "Deactivate scripting for the active scripting buffer.

Set proof-script-buffer to nil and turn off the modeline indicator.
No action if there is no active scripting buffer.  

We make sure that the active scripting buffer either has no locked
region or a full locked region (everything in it has been processed).
If this is not already the case, we question the user whether to
retract or assert, or automatically take the action indicated in the
user option `proof-auto-action-when-deactivating-scripting.'

If the scripting buffer is (or has become) fully processed, and it is
associated with a file, it is registered on
`proof-included-files-list'.  Conversely, if it is (or has become)
empty, we make sure that it is *not* registered.  This is to be
certain that the included files list behaves as we might expect with
respect to the active scripting buffer, in an attempt to harmonize
mixed scripting and file reading in the prover.

This function either succeeds, fails because the user refused to
process or retract a partly finished buffer, or gives an error message
because retraction or processing failed.  If this function succeeds,
then proof-script-buffer is nil afterwards.

The optional argument FORCEDACTION overrides the user option
`proof-auto-action-when-deactivating-scripting' and prevents
questioning the user.  It is used to make a value for
the kill-buffer-hook for scripting buffers, so that when
a scripting buffer is killed it is always retracted."
  (interactive)
  (if proof-script-buffer
      (with-current-buffer proof-script-buffer
	;; Examine buffer.
	
	;; We must ensure that the locked region is either 
	;; empty or full, to make sense for multiple-file
	;; scripting.  (A proof assistant won't be able to
	;; process just part of a file typically; moreover
	;; switching between buffers during a proof makes
	;; no sense.)
	(if (or (proof-locked-region-empty-p) 
		(proof-locked-region-full-p)
		;; Buffer is partly-processed
		(let*
		    ((action 
		      (or
		       forcedaction
		       proof-auto-action-when-deactivating-scripting
		       (progn
			 (save-window-excursion
			   (unless
			       ;; Test to see whether to display the 
			       ;; buffer or not.
			       ;; Could have user option here to avoid switching
			       ;; or maybe borrow similar standard setting
			       ;; save-some-buffers-query-display-buffer
			       (or
				(eq (current-buffer)
				    (window-buffer (selected-window)))
				(eq (selected-window) (minibuffer-window)))
			     (progn
			       (unless (one-window-p)
				 (delete-other-windows))
			       (switch-to-buffer proof-script-buffer t)))
			   ;; Would be nicer to ask a single question, but
			   ;; a nuisance to define our own dialogue since it
			   ;; doesn't really fit with one of the standard ones.
			   (cond
			    ((y-or-n-p
			      (format
			       "Scripting incomplete in buffer %s, retract? "
			       proof-script-buffer))
			     'retract)
			    ((y-or-n-p
			      (format
			       "Completely process buffer %s instead? "
			       proof-script-buffer))
			     'process)))))))
		  ;; Take the required action
		  (if action
		      (proof-protected-process-or-retract action)
		    ;; Give an acknowledgement to user's choice
		    ;; neither to assert or retract.  
		    (message "Scripting still active in %s" 
			     proof-script-buffer)
		    ;; Delay because this can be followed by an error
		    ;; message in proof-activate-scripting when trying
		    ;; to switch to another scripting buffer.
		    (sit-for 1)
		    nil)))

	    ;; If we get here, then the locked region is (now) either 
	    ;; completely empty or completely full.  
	    (progn
	      ;; We can immediately indicate that there is no active
	      ;; scripting buffer
	      (setq proof-previous-script-buffer proof-script-buffer)
	      (setq proof-script-buffer nil)

	      (if (proof-locked-region-full-p)
		  ;; If locked region is full, make sure that this buffer
		  ;; is registered on the included files list, and
		  ;; let the prover know it can consider it processed.
		  (if (or buffer-file-name proof-script-buffer-file-name)
		      (proof-register-possibly-new-processed-file 
		       (or buffer-file-name proof-script-buffer-file-name)
		       'tell-the-prover
		       forcedaction)))
	      
	      (if (proof-locked-region-empty-p)
		  ;; If locked region is empty, make sure this buffer is
		  ;; *off* the included files list. 
		  ;; FIXME: probably this isn't necessary: the
		  ;; file should be unregistered by the retract
		  ;; action, or in any case since it was only
		  ;; partly processed.
		  ;; FIXME 2: be careful about automatic
		  ;; multiple file handling here, since it calls
		  ;; for activating scripting elsewhere.
		  ;; We move the onus on unregistering now to
		  ;; the activate-scripting action.
		  (proof-unregister-buffer-file-name))

	      ;; Turn off Scripting indicator here.
	      (setq proof-active-buffer-fake-minor-mode nil)

	      ;; Make status of inactive scripting buffer show up
	      ;; FIXME da:
	      ;; not really necessary when called by kill buffer, at least.
	      (if (fboundp 'redraw-modeline)
		  (redraw-modeline)
		(force-mode-line-update)))))))
  
(defun proof-activate-scripting (&optional nosaves queuemode)
  "Ready prover and activate scripting for the current script buffer.

The current buffer is prepared for scripting. No changes are
necessary if it is already in Scripting minor mode. Otherwise, it
will become the new active scripting buffer, provided scripting
can be switched off in the previous active scripting buffer
with `proof-deactivate-scripting'.

Activating a new script buffer may be a good time to ask if the 
user wants to save some buffers; this is done if the user
option `proof-query-file-save-when-activating-scripting' is set
and provided the optional argument NOSAVES is non-nil.

The optional argument QUEUEMODE relaxes the test for a
busy proof shell to allow one which has mode QUEUEMODE.
In all other cases, a proof shell busy error is given.

Finally, the hooks `proof-activate-scripting-hook' are run.  
This can be a useful place to configure the proof assistant for
scripting in a particular file, for example, loading the
correct theory, or whatever.  If the hooks issue commands
to the proof assistant (via `proof-shell-invisible-command')
which result in an error, the activation is considered to
have failed and an error is given."
  (interactive)
  ;; FIXME: the scope of this save-excursion is rather wide.
  ;; Problems without it however: Use button behaves oddly
  ;; when process is started already.
  ;; Where is save-excursion needed?
  ;; First experiment shows that it's the hooks that cause
  ;; problem, maybe even the use of proof-cd-sync (can't see why).
  (save-excursion
    ;; FIXME: proof-shell-ready-prover here s
    (proof-shell-ready-prover queuemode)
    (cond 
     ((not (eq proof-buffer-type 'script)) 
      (error "Must be running in a script buffer!"))
     
     ;; If the current buffer is the active one there's nothing to do.
   ((equal (current-buffer) proof-script-buffer))
     
     ;; Otherwise we need to activate a new Scripting buffer.
   (t
      ;; If there's another buffer currently active, we need to 
      ;; deactivate it (also fixing up the included files list).
      (if proof-script-buffer
	  (progn
	    (proof-deactivate-scripting)
	    ;; Test whether deactivation worked
	    (if proof-script-buffer
		(error 
		 "You cannot have more than one active scripting buffer!"))))
	    
      ;; Now make sure that this buffer is off the included files
      ;; list.  In case we re-activate scripting in an already
      ;; completed buffer, it may be that the proof assistant
      ;; needs to retract some of this buffer's dependencies.
      (proof-unregister-buffer-file-name 'tell-the-prover)

      ;; If automatic retraction happened in the above step, we may
      ;; have inadvertently activated scripting somewhere else.
      ;; Better turn it off again.   This should succeed trivially.
      ;; NB: it seems that we could move the first test for an already
      ;; active buffer here, but it is more subtle: the first
      ;; deactivation can extend the proof-included-files list, which
      ;; would affect what retraction was done in
      ;; proof-unregister-buffer-file-name.
      (if proof-script-buffer
	  (proof-deactivate-scripting))
      (assert (null proof-script-buffer) 
	      "Bug in proof-activate-scripting: deactivate failed.")

      ;; Set the active scripting buffer, and initialise the 
      ;; queue and locked regions if necessary.
      (setq proof-script-buffer (current-buffer))
      (if (proof-locked-region-empty-p)
	  ;; This removes any locked region that was there, but
	  ;; sometimes we switch on scripting in "full" buffers,
	  ;; so mustn't do this.
	  (proof-init-segmentation))

      ;; Turn on the minor mode, make it show up.
      (setq proof-active-buffer-fake-minor-mode t)
      (if (fboundp 'redraw-modeline)
	  (redraw-modeline)
	(force-mode-line-update))
      
      ;; This may be a good time to ask if the user wants to save some
      ;; buffers.  On the other hand, it's jolly annoying to be
      ;; queried on the active scripting buffer if we've started
      ;; writing in it.  So pretend that one is unmodified, at least
      ;; (we certainly don't expect the proof assitant to load it)
      (if (and
	   proof-query-file-save-when-activating-scripting
	   (not nosaves))
	  (let ((modified (buffer-modified-p)))
	    (set-buffer-modified-p nil)
	    (unwind-protect
		(save-some-buffers)
 	      (set-buffer-modified-p modified))))

      ;; Run hooks with a variable which suggests whether or not 
      ;; to block.   NB: The hook function may send commands to the
      ;; process which will re-enter this function, but should exit 
      ;; immediately because scripting has been turned on now.
      (if proof-activate-scripting-hook
	  (let
	      ((activated-interactively	(interactive-p)))
	    ;; Clear flag in case no hooks run shell commands
	    (setq proof-shell-error-or-interrupt-seen nil)
	    (run-hooks 'proof-activate-scripting-hook)
	    ;; In case the activate scripting functions
	    ;; caused an error in the proof assistant, we'll
	    ;; consider activating scripting to have failed,
	    ;; and raise an error here.
	    ;; (Since this behaviour is intimate with the hook functions,
	    ;;  it could be removed and left to implementors of 
	    ;;  specific instances of PG).
	    ;; FIXME: we could consider simply running the hooks
	    ;; as the last step before turning on scripting properly,
	    ;; provided the hooks don't inspect proof-script-buffer.
	    (if proof-shell-error-or-interrupt-seen
		(progn
		  (proof-deactivate-scripting) ;; turn it off again!
		  ;; Give an error to prevent further actions.
		  (error "Proof General: Scripting not activated because of error or interrupt.")))))))))


(defun proof-toggle-active-scripting (&optional arg)
  "Toggle active scripting mode in the current buffer.
With ARG, turn on scripting iff ARG is positive."
  (interactive "P")
  ;; A little less obvious than it may seem: toggling scripting in the
  ;; current buffer may involve turning it off in some other buffer
  ;; first!
  (if (if (null arg)
	  (not (eq proof-script-buffer (current-buffer)))
	(> (prefix-numeric-value arg) 0))
      (progn
	(if proof-script-buffer 
	    (call-interactively 'proof-deactivate-scripting))
	(call-interactively 'proof-activate-scripting))
    (call-interactively 'proof-deactivate-scripting)))

;;
;;  End of activating and deactivating scripting section
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Processing the script management queue -- PART 1: "advancing"
;;
;; The proof-action-list contains a list of (span,command,action)
;; triples. The loop looks like: Execute the command, and if it's
;; successful, do action on span.  If the command's not successful, we
;; bounce the rest of the queue and do some error processing.
;;
;; When a span has been processed, it is classified as 
;; 'comment, 'goalsave, 'vanilla, etc. 
;;
;; The main function for dealing with processed spans is
;; `proof-done-advancing'

(defun proof-done-advancing (span)
  "The callback function for assert-until-point."
  ;; FIXME da: if the buffer dies, this function breaks horribly.
  (if (not (span-live-p span))
      ;; NB: Sometimes this function is called with a destroyed
      ;; extent as argument.  Seems odd.
      (proof-debug 
       "Proof General idiosyncrasy: proof-done-advancing called with a dead span!")
    ;; 
    (let ((end     (span-end span))
	  (cmd     (span-property span 'cmd)))
      ;; State of spans after advancing: 
      (proof-set-locked-end end)
      ;; FIXME: buglet here, can sometimes arrive with queue span already detached.
      ;; (I think when complete file process is requested during scripting)
      (if (span-live-p proof-queue-span)
	  (proof-set-queue-start end))

      (cond
       ;; CASE 1: Comments just get highlighted
       ((eq (span-property span 'type) 'comment)
	(proof-done-advancing-comment span))

       ;; CASE 2: Save command seen, now we may amalgamate spans.
       ((and proof-save-command-regexp
	     (proof-string-match proof-save-command-regexp cmd)
	     ;; FIXME: would like to get rid of proof-really-save-command-p
	     ;; and use nested goals mechanism instead.
	     (funcall proof-really-save-command-p span cmd)
	     (decf proof-nesting-depth) ;; [always non-nil/true]
	     (if proof-nested-goals-history-p
		 ;; For now, we only support this nesting behaviour: 
		 ;; don't amalgamate unless the nesting depth is 0,
		 ;; i.e. we're in a top-level proof.
		 ;; This assumes prover keeps history for nested proofs.
		 ;; (True for Isabelle/Isar).
		 (eq proof-nesting-depth 0)
	       t))
	(proof-done-advancing-save span))

       ;; CASE 3: Proof completed one step or more ago, non-save
       ;; command seen, no nested goals allowed.
       ;; 
       ;; We make a fake goal-save from any previous 
       ;; goal to the command before the present one.
       ;;
       ;; This allows smooth undoing in proofs which have no "qed"
       ;; statements.  If your proof assistant doesn't allow these
       ;; "unclosed" proofs, then you can safely set
       ;; proof-completed-proof-behaviour.
       ((and
	 proof-shell-proof-completed
	 (or (and (eq proof-completed-proof-behaviour 'extend)
		  (>= proof-shell-proof-completed 0))
	     (and (eq proof-completed-proof-behaviour 'closeany)
		  (> proof-shell-proof-completed 0))
	     (and (eq proof-completed-proof-behaviour 'closegoal)
		  (funcall proof-goal-command-p cmd))))
	(proof-done-advancing-autosave span))
      
     ;; CASE 4:  Some other kind of command (or a nested goal).
     (t
      (proof-done-advancing-other span))))

  ;; Finally: state of scripting may have changed now, run hooks.
  (run-hooks 'proof-state-change-hook)))



(defun proof-done-advancing-comment (span)
  "A subroutine of `proof-done-advancing'"
  ;; Add an element for a new span, which should span
  ;; the text of the comment.
  ;; FIXME: might be better to use regexps for matching
  ;; start/end of comments, rather than comment-start-skip
  (let ((bodyspan  (make-span 
		    (+ (length comment-start) (span-start span))
		    (- (span-end span) (length comment-end))))
	(id        (proof-next-element-id 'comment)))
    (pg-add-element "comment" id bodyspan)
    (set-span-property span 'id (intern id))
    (set-span-property span 'idiom 'comment)
    (pg-set-span-helphighlights span)))


(defun proof-done-advancing-save (span)
  "A subroutine of `proof-done-advancing'"
  (unless (eq proof-shell-proof-completed 1)
    ;; We expect saves to succeed only for recently completed proofs.
    ;; Give a hint to the proof assistant implementor in case something
    ;; odd is going on.  (NB: this is normal for nested proofs, though).
    (proof-debug 
     (format
      "PG: save command with proof-shell-proof-completed=%s, proof-nesting-depth=%s"
      proof-shell-proof-completed proof-nesting-depth)))

  (setq proof-shell-proof-completed nil)

  ;; FIXME: need subroutine here:
  (let ((gspan     span)		  ; putative goal span
	(savestart (span-start span))
	(saveend   (span-end span))
	(cmd       (span-property span 'cmd))
	lev nestedundos nam next ncmd)
    
    ;; Try to set the name of the theorem from the save
    ;; (message "%s" cmd)   3.4: remove this message.
    
    (and proof-save-with-hole-regexp
	 (proof-string-match proof-save-with-hole-regexp cmd)
	 ;; Give a message of a name if one can be determined
	 (message "%s"
		  (setq nam 
			(if (stringp proof-save-with-hole-result)
			    (replace-match proof-save-with-hole-result nil nil cmd)
			  (match-string proof-save-with-hole-result cmd)))))

    ;; Search backwards for matching goal command, deleting spans
    ;; along the way: they will be amalgamated into a single
    ;; goal-save region, which corresponds to the prover
    ;; discarding the proof history.
    ;; Provers without flat history yet nested proofs (i.e. Coq)
    ;; need to keep a record of the undo count for nested goalsaves.
    ;; FIXME: should also remove nested 'idiom spans, perhaps.
    (setq lev 1)
    (setq nestedundos 0)
    (while (and gspan (> lev 0))
      (setq next (prev-span gspan 'type))
      (delete-span gspan)
      (setq gspan next)
      (if gspan 
	  (progn
	    (setq cmd (span-property gspan 'cmd))
	    (cond
	     ;; Ignore comments [may have null cmd setting]
	     ((eq (span-property gspan 'type) 'comment))	
	     ;; Nested goal saves: add in any nestedcmds
	     ((eq (span-property gspan 'type) 'goalsave)
	      (setq nestedundos
		    (+ nestedundos 1
		       (or (span-property gspan 'nestedundos) 0))))
	     ;; Increment depth for a nested save, in case
	     ;; prover supports history of nested proofs
	     ((and proof-nested-goals-history-p
		   proof-save-command-regexp
		   (proof-string-match proof-save-command-regexp cmd))
	      (incf lev))
	     ;; Decrement depth when a goal is hit
	     ((funcall proof-goal-command-p cmd)
	      (decf lev))
	     ;; Remainder cases: see if command matches something we
	     ;; should count for a global undo
	     ((and proof-nested-undo-regexp
		   (proof-string-match proof-nested-undo-regexp cmd))
	      (incf nestedundos))
	     ))))

    (if (not gspan)
	;; No goal span found!  Issue a warning and do nothing more.
	(proof-warning
	 "Proof General: script management confused, couldn't find goal span for save.")

      ;; If the name isn't set, try to set it from the goal,
      ;; or as a final desparate attempt, set the name to
      ;; proof-unnamed-theorem-name (Coq actually uses a default
      ;; name for unnamed theorems, believe it or not, and issues
      ;; a name-binding error for two unnamed theorems in a row!).
      (setq nam (or nam
		    (proof-get-name-from-goal gspan)
		    proof-unnamed-theorem-name))

      (proof-make-goalsave gspan (span-end gspan) 
			   savestart saveend nam nestedundos)

      ;; *** Theorem dependencies ***
      (if proof-last-theorem-dependencies
	  (proof-depends-process-dependencies nam gspan)))))

(defun proof-make-goalsave (gspan goalend savestart saveend nam &optional nestedundos)
  "Make new goal-save span, using GSPAN. Subroutine of `proof-done-advancing-save'"
  (set-span-end gspan saveend)
  (set-span-property gspan 'type 'goalsave)
  (set-span-property gspan 'idiom 'proof);; links to nested proof element
  (set-span-property gspan 'name nam)
  (and nestedundos (set-span-property gspan 'nestedundos nestedundos))
  (pg-set-span-helphighlights gspan)
  ;; Now make a nested span covering the purported body of the
  ;; proof, and add to buffer-local list of elements.  
  (let ((proofbodyspan
	 (make-span goalend (if proof-script-integral-proofs 
				saveend savestart))))
    (pg-add-proof-element nam proofbodyspan gspan)))
  
(defun proof-get-name-from-goal (gspan)
  "Try to return a goal name from GSPAN.  Subroutine of `proof-done-advancing-save'"
  (let ((cmdstr (span-property gspan 'cmd)))
    (and proof-goal-with-hole-regexp
	 (proof-string-match proof-goal-with-hole-regexp cmdstr)
	 (if (stringp proof-goal-with-hole-result)
	     (replace-match proof-goal-with-hole-result nil nil cmdstr)
	   (match-string proof-goal-with-hole-result cmdstr)))))


;; FIXME: this next function should be more like proof-done-advancing-save,
;; perhaps simplifying the proof-completed-proof-behaviour functionality,
;; which isn't seriously used in any prover.  At the moment the behaviour
;; here is incomplete compared with proof-done-advancing-save.
;; NB: in this function we assume non-nested proofs, which explains
;; some of the logic.  There is no attempt to fix up proof-nesting-depth.
;; NB: 'extend behaviour is not currently compatible with appearance of
;; save commands, since proof-done-advancing-save allow for goalspan
;; already existing.
(defun proof-done-advancing-autosave (span)
  "A subroutine of `proof-done-advancing'"

  ;; In the extend case, the context of proof grows until hit a save
  ;; or new goal.
  (if (eq proof-completed-proof-behaviour 'extend)
      (incf proof-shell-proof-completed)
    (setq proof-shell-proof-completed nil))

  (let* ((swallow  (eq proof-completed-proof-behaviour 'extend))
	 (gspan    (if swallow span (prev-span span 'type)))
	 (newend   (if swallow (span-end span) (span-start span)))
	 (cmd      (span-property span 'cmd))
	 (newgoal  (funcall proof-goal-command-p cmd))
	 nam hitsave dels ncmd)
    ;; Search backwards to see if we can find a previous goal
    ;; before a save or the start of the buffer.
    ;; FIXME: this should really do the work done in 
    ;; proof-done-advancing-save above, too, with nested undos, etc.
    (while ;; YUK!
	(and 
	 gspan
	 (or 
	  (eq (span-property gspan 'type) 'comment)
	  (and
	   (setq ncmd (span-property gspan 'cmd))
	   (not (funcall proof-goal-command-p (setq cmd ncmd)))
	   (not
	    (and proof-save-command-regexp
		 (proof-string-match proof-save-command-regexp cmd)
		 (funcall proof-really-save-command-p span cmd)
		 (setq hitsave t))))))
      (setq dels (cons gspan dels))
      (setq gspan (prev-span gspan 'type)))
    (cond
     ((or hitsave (null gspan))
      (proof-debug
	 "Proof General strangeness: unclosed proof completed, but couldn't find its start!")
      (pg-set-span-helphighlights span))
     ((and swallow newgoal)
      ;; If extending the region, goalsave already there; just highlight new region
      (setq proof-shell-proof-completed nil)
      (pg-set-span-helphighlights span))
     (t
      ;; If, search back through spans, we haven't hit a save or the
      ;; start of the buffer, we make a fake goal-save region.

      ;; Delete spans between the previous goal and new command
      (mapcar 'delete-span dels)

      ;; Try to set the name from the goal... [as above]
      (setq nam (or (proof-get-name-from-goal gspan)
		    proof-unnamed-theorem-name))

      ;; NB: if extending an already closed region, ought to delete
      ;; the body and extend that too: currently we make multiple nested 
      ;; bodies, a bit messy.
      ;; (NB: savestart used for nested region: here use saveend)
      (proof-make-goalsave gspan
			   (+ (span-start gspan) 
			      (length (or (span-property-safe gspan 'cmd))))
			   newend newend nam)))))

(defun proof-done-advancing-other (span)
  ;; We might add hidable regions also for commands: the problem
  ;; is that they have no natural surrounding region, so makes
  ;; it difficult to define a region for revealing again.
  ;; [ best solution would be to support clicking on ellipsis]
  (if (funcall proof-goal-command-p (span-property span 'cmd))
	  (incf proof-nesting-depth))

  (if proof-shell-proof-completed
      (incf proof-shell-proof-completed))
      
  (pg-set-span-helphighlights span))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Parsing functions for parsing commands in script
;;
;; Command parsing is suprisingly subtle with various possibilities of
;; command syntax (terminated, not terminated, or lisp-style); whether
;; or not PG silently ignores comments, etc.

;; FIXME: currently there's several sets of functions.  We need to be
;; more general and a bit more clear, but the latest versions are a
;; much better attempt.

(defun proof-segment-up-to-parser (pos &optional next-command-end)
  "Parse the script buffer from end of locked to POS.
Return a list of (type, string, int) tuples (in reverse order).

Each tuple denotes the command and the position of its final character,
type is one of 'comment, or 'cmd.

The behaviour around comments is set by
`proof-script-fly-past-comments', which see.

This version is used when `proof-script-parse-function' is set,
to the function which parses the script segment by segment."
  (save-excursion
    (let* ((start (goto-char (proof-queue-or-locked-end)))
	   (cur   (1- start))
	   (seg   t)
	   prevtype realstart cmdseen segs)
      ;; Keep parsing until:
      ;;   - we fail to find a segment   (seg = nil)
      ;;   - we go beyond the stop point (cur >= end)
      ;;      - unless we're flying past comments, in which case
      ;;        wait for a command (cmdseen<>nil)
      (while (and seg 
		  (or (< cur pos) 
		      (and proof-script-fly-past-comments
			   (not cmdseen))))
	;; Skip whitespace before this element
	(skip-chars-forward " \t\n")
	(setq realstart (point))
	(let* ((type  (funcall proof-script-parse-function)))
	  (setq seg nil)
	  (cond
	   ((eq type 'comment)
	    (setq seg (list 'comment "" (point))))
	   ((eq type 'cmd)
	    (setq cmdseen t)
	    (setq seg (list 
		       'cmd 
		       (buffer-substring realstart (point)) 
		       (point))))
	   ((null type))		; nothing left in buffer
	   (t 
	    (error 
  "proof-segment-up-to-parser: bad TYPE value from proof-script-parse-function.")))
	  ;;
	  (if seg 
	      (progn
		;; Add the new segment, coalescing comments if
		;; the user likes it that way.  I first made
		;; coalescing a separate configuration option, but
		;; it works well used in tandem with the fly-past
		;; behaviour.
		(if (and proof-script-fly-past-comments
			 (eq type 'comment)
			 (eq prevtype 'comment))
		    (setq segs (cons seg (cdr segs)))
		  (setq segs (cons seg segs)))
		;; Update state
		(setq cur (point))
		(setq prevtype type)))))
      ;; Return segment list
      segs)))

(defun proof-script-generic-parse-find-comment-end ()
  "Find the end of the comment point is at the start of. Nil if not found."
  (let ((notout t))
    ;; Find end of comment (NB: doesn't undertand nested comments)
    (while (and notout (re-search-forward 
			proof-script-comment-end-regexp nil 'movetolimit))
      (setq notout (proof-buffer-syntactic-context)))
    (not (proof-buffer-syntactic-context))))
  
(defun proof-script-generic-parse-cmdend ()
  "Used for proof-script-parse-function if proof-script-command-end-regexp is set."
  (if (looking-at proof-script-comment-start-regexp)
      ;; Handle comments
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    ;; Handle non-comments: assumed to be commands
    (let (foundend)
      ;; Find end of command
      (while (and (setq foundend 
			(re-search-forward proof-script-command-end-regexp nil t))
		  (proof-buffer-syntactic-context))
	;; inside a string or comment before the command end
	)
      (if (and foundend 
	       (not (proof-buffer-syntactic-context)))
	  ;; Found command end outside string/comment
	  'cmd
	;; Didn't find command end
	nil))))

(defun proof-script-generic-parse-cmdstart ()
  "For proof-script-parse-function if proof-script-command-start-regexp is set."
  ;; This was added for the fine-grained command structure of Isar
  ;;
  ;; It's is a lot more involved than the case of just scanning for
  ;; the command end; we have to find two successive command starts
  ;; and go backwards from the second.  This coalesces comments
  ;; following commands with commands themselves, and sends them to
  ;; the prover (only case where it does).
  ;;
  ;; To avoid doing that, we would need to scan also for comments but
  ;; it would be difficult to distinguish between:
  ;;   complete command (* that's it *)
  ;; and
  ;;   complete (* almost *) command
  ;;
  ;; Maybe the second case should be disallowed in command-start regexp case?
  ;; 
  ;; Another improvement idea might be to take into account both
  ;; command starts *and* ends, but let's leave that for another day.
  ;;
  (if (looking-at proof-script-comment-start-regexp)
      ;; Find end of comment
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    ;; Handle non-comments: assumed to be commands
    (if (looking-at proof-script-command-start-regexp)
	(progn
	  ;; We've got at least the beginnings of a command, skip past it
	  (re-search-forward proof-script-command-start-regexp nil t)
	  (let (foundstart)
	    ;; Find next command start
	    (while (and (setq 
			 foundstart 
			 (and 
			  (re-search-forward proof-script-command-start-regexp
					     nil 'movetolimit)
			  (match-beginning 0)))
			(proof-buffer-syntactic-context))
	      ;; inside a string or comment before the next command start
	      )
	    (if (not (proof-buffer-syntactic-context))  ; not inside a comment/string
		(if foundstart		             ; found a  second command start
		    (progn
		      (goto-char foundstart)          ; beginning of command start
		      (skip-chars-backward " \t\n")   ; end of previous command
		      'cmd)
		  (if (eq (point) (point-max)) ; At the end of the buffer
		      (progn
			(skip-chars-backward " \t\n") ; benefit of the doubt, let 
			'cmd))))		      ; the PA moan if it's incomplete
	    ;; Return nil in other cases, no complete command found
	    )))))


(defun proof-script-generic-parse-sexp ()
  "Used for proof-script-parse-function if proof-script-sexp-commands is set."
  ;; Usual treatment of comments
  (if (looking-at proof-script-comment-start-regexp)
      ;; Find end of comment
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    (let* ((parse-sexp-ignore-comments t)	; gobble comments into commands
	   (end (scan-sexps (point) 1)))
      (if end
	  (progn (goto-char end) 'cmd)))))
    

;; Parsing functions new in v3.2
;;
;; NB: compared with old code,
;; (1) this doesn't treat comments quite so well, but parsing
;; should be rather more efficient.
;; (2) comments are treated less like commands, and are only
;; coloured blue "in passing" when commands are sent.
;; However, undo still process comments step-by-step.

(defun proof-segment-up-to-cmdstart (pos &optional next-command-end)
  "Parse the script buffer from end of locked to POS.
Return a list of (type, string, int) tuples.

Each tuple denotes the command and the position of its terminator,
type is one of 'comment, or 'cmd.

If optional NEXT-COMMAND-END is non-nil, we include the command
which continues past POS, if any.  (NOT IMPLEMENTED IN THIS VERSION).

This version is used when `proof-script-command-start-regexp' is set."
  (save-excursion
    (let* ((commentre   (concat "[ \t\n]*" proof-script-comment-start-regexp))
	   (commentend   (concat proof-script-comment-end-regexp "[ \t\n]*" ))
	   (add-segment-for-cmd		; local function: advances "prev"
	    (lambda ()
	      (setq tmp (point))
	      ;; Find end of previous command...
	      (goto-char comstart)
	      ;; Special hack: allow terminal char to be included
	      ;; in a command, if it's set.
	      (if (and proof-terminal-char
		       (looking-at 
			(regexp-quote (char-to-string proof-terminal-char))))
		  (goto-char (1+ (point)))
		(skip-chars-backward " \t\n"))
	      (let* ((prev-no-blanks
		      (save-excursion 
			(goto-char prev) 
			(skip-chars-forward " \t\n") 
			(point)))
		     (comend (point))
		     (bufstr (buffer-substring prev-no-blanks comend))
		     (type   (save-excursion
				  ;; The behaviour here is a bit odd: this
				  ;; is a half-hearted attempt to strip comments
				  ;; as we send text to the proof assistant,
				  ;; but it breaks when we have certain bad
				  ;; input:  (* foo *) blah (* bar *) cmd 
				  ;; We check for the case
				  ;; of a comment spanning the *whole*
				  ;; substring, otherwise send the
				  ;; (defective) text as if it were a
				  ;; proper command anyway.
				  ;; This shouldn't cause problems: the 
				  ;; proof assistant is certainly capable
				  ;; of skipping comments itself, and
				  ;; the situation should cause an error.
				  ;; (If it were accepted it could upset the
				  ;; undo behaviour)
			       (goto-char prev-no-blanks)
			       ;; Update: PG 3.4: try to deal with sequences
			       ;; of comments as well, since previous behaviour
			       ;; breaks Isar, in fact, since repeated
			       ;; comments get categorized as commands, 
			       ;; breaking sync.
			       (if (and 
				    (looking-at commentre)
				    (re-search-forward proof-script-comment-end-regexp)
				    (progn
				      (while (looking-at commentre)
					(re-search-forward proof-script-comment-end-regexp))
				      (>= (point) comend)))
				   'comment 'cmd)))
		     (string (if (eq type 'comment) "" bufstr)))
		(setq prev (point))
		(goto-char tmp)
		;; NB: Command string excludes whitespace, span includes it.
		(setq alist (cons (list type string prev) alist)))))
	   alist prev cmdfnd startpos comstart tmp)
      (goto-char (proof-queue-or-locked-end))
      (setq prev (point))
      (skip-chars-forward " \t\n")
      (setq startpos (point))
      (while 
	  (and 
	   (proof-re-search-forward proof-script-command-start-regexp
			      nil t)   ; search for next command
	   (setq comstart (match-beginning 0)); save command start
	   (or (save-excursion
		 (goto-char comstart)
		 ;; continue if inside (or at start of) comment/string
		 (proof-looking-at-syntactic-context))
	       (progn			    ; or, if found command...
		 (setq cmdfnd 
		       (> comstart startpos)); ignore first match
		 (<= prev pos))))
	(if cmdfnd (progn
		     (funcall add-segment-for-cmd)
		     (setq cmdfnd nil))))
      ;; End of parse; see if we found some text at the end of the
      ;; buffer which could be a command.  (NB: With a regexp for 
      ;; start of commands only, we can't be sure it is a complete
      ;; command).
      (if (and comstart			; previous command was found
	       (<= prev pos)		; last command within range
	       (goto-char (point-max))
	       (setq comstart (point))	; pretend there's another cmd here
	       (not (proof-buffer-syntactic-context))) ; buffer ends well
	  (funcall add-segment-for-cmd))
      ; (if (and cmdfnd next-command-end)
      ; (funcall add-segment-for-cmd))
      ;; Return resulting list
      alist)))


;; FIXME: this needs fixing to include final comment in buffer
;; if there is one!!

(defun proof-segment-up-to-cmdend (pos &optional next-command-end)
  "Parse the script buffer from end of locked to POS.
Return a list of (type, string, int) tuples.

Each tuple denotes the command and the position of its terminator,
type is one of 'comment, or 'cmd. 'unclosed-comment may be consed onto
the start if the segment finishes with an unclosed comment.

If optional NEXT-COMMAND-END is non-nil, we include the command
which continues past POS, if any.

This version is used when `proof-script-command-end-regexp' is set."
  (save-excursion
    (let* 
	((commentre   (concat "[ \t\n]*" proof-script-comment-start-regexp))
	 (add-segment-for-cmd		; local function: advances "prev"
	  (lambda ()
	    (let ((cmdend (point)) start)
	      (goto-char prev)
	      ;; String may start with comments, let's strip them off
	      (while 
		  (and
		   (setq start (point))
		   (proof-re-search-forward commentre cmdend t)
		   (or (eq (match-beginning 0) start)
		       ;; In case a comment inside a command was found, make
		       ;; sure we're at the start of the cmd before exiting
		       (progn (goto-char start) nil)))
		;; Look for the end of the comment 
		;; (FIXME: ignore nested comments here, we should
		;; have a consistent policy!)
		(unless
		    (proof-re-search-forward 
		     proof-script-comment-end-regexp cmdend t)
		  (error
		   "PG error: proof-segment-up-to-cmd-end didn't find comment end."))
		(setq alist (cons (list 'comment "" (point)) alist)))
	      ;; There should be something left: a command.
	      (skip-chars-forward " \t\n")
	      (setq alist (cons (list 'cmd 
				      (buffer-substring
				       (point) cmdend) 
				      cmdend) alist))
	      (setq prev cmdend)
	      (goto-char cmdend))))
	 alist prev cmdfnd startpos tmp)
      (goto-char (proof-queue-or-locked-end))
      (setq prev (point))
      (skip-chars-forward " \t\n")
      (setq startpos (point))
      (while 
	  (and 
	   (proof-re-search-forward proof-script-command-end-regexp
			      nil t) ; search for next command
	   (or (proof-buffer-syntactic-context)   ; continue if inside comment/string
	       (progn			    ; or, if found command...
		 (setq cmdfnd t)
		 (<= (point) pos))))
	(if cmdfnd (progn
		     (funcall add-segment-for-cmd)
		     (setq cmdfnd nil))))
      ;; End of parse; if we found a command past POS maybe add it.
      ;; FIXME: also, if we found a *comment* maybe add it!
      (if cmdfnd ; (and cmdfnd next-command-end)
	  (funcall add-segment-for-cmd))
      ;; Return resulting list
      alist)))

(defun proof-semis-to-vanillas (semis &optional callback-fn)
  "Convert a sequence of terminator positions to a set of vanilla extents.
Proof terminator positions SEMIS has the form returned by
the function proof-segment-up-to.
Set the callback to CALLBACK-FN or 'proof-done-advancing by default."
  (let ((ct (proof-queue-or-locked-end)) span alist semi)
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




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Assert-until-point and friends.
;;
;; These functions parse some region of the script buffer into
;; commands, and add the commands into the queue.
;;


;; First: two commands for moving forwards in proof scripts.  Moving
;; forward for a "new" command may insert spaces or new lines.  Moving
;; forward for the "next" command does not.

(defun proof-script-new-command-advance ()
  "Move point to a nice position for a new command.
Assumes that point is at the end of a command."
  (interactive)
; FIXME: pending improvement.2, needs a fix here.
;  (if (eq (proof-locked-end) (point))
;      ;; A hack to fix problem that the locked span
;      ;; is [ ) so sometimes inserting at the end
;      ;; tries to extend it, giving "read only" error.
;      (if (> (point-max) (proof-locked-end))
;	  (progn
;	    (goto-char (1+ (proof-locked-end)))
;	    (backward-char))))
  (if proof-one-command-per-line
      ;; One command per line: move to next new line, creating one if
      ;; at end of buffer or at the start of a blank line.  (This has
      ;; the pleasing effect that blank regions of the buffer are
      ;; automatically extended when inserting new commands).
; unfortunately if we're not at the end of a line to start,
; it skips past stuff to the end of the line!  don't want
; that.
;      (cond
;       ((eq (forward-line) 1)
;	(newline))
;       ((eolp)
;        (newline)
;	(forward-line -1)))
      (newline)
    ;; Multiple commands per line: skip spaces at point, and insert
    ;; the 1/0 number of spaces that were skipped in front of point
    ;; (at least one).  This has the pleasing effect that the spacing
    ;; policy of the current line is copied: e.g.  <command>;
    ;; <command>; Tab columns don't work properly, however.  Instead
    ;; of proof-one-command-per-line we could introduce a
    ;; "proof-command-separator" to improve this.
    (let ((newspace (max (skip-chars-forward " \t") 1))
	  (p (point)))
      (if proof-script-command-separator
	  (insert proof-script-command-separator)
	(insert-char ?\ newspace)
	(goto-char p)))))

(defun proof-script-next-command-advance ()
  "Move point to the beginning of the next command if it's nearby.
Assumes that point is at the end of a command."
  (interactive)
  ;; skip whitespace on this line
  (skip-chars-forward " \t")		
  (if (and proof-one-command-per-line (eolp))
      ;; go to the next line if we have one command per line
      (forward-line)))


;; NB: the "interactive" variant is so that we get a simple docstring.
(defun proof-assert-until-point-interactive ()
  "Process the region from the end of the locked-region until point.
Default action if inside a comment is just process as far as the start of
the comment."
  (interactive)
  (proof-assert-until-point))


;; Assert until point - We actually use this to implement the
;; assert-until-point, electric terminator keypress, and
;; goto-command-end. In different cases we want different things, but
;; usually the information (e.g. are we inside a comment) isn't
;; available until we've actually run proof-segment-up-to (point),
;; hence all the different options when we've done so.

;; FIXME da: this command doesn't behave as the doc string says when
;; inside comments.  Also is unhelpful at the start of commands, and
;; in the locked region.  I prefer the new version below.

;; FIXME: get rid of duplication between proof-assert-next-command and
;; proof-assert-until-point.  Get rid of ignore process nonsense.

;; FIXME: get rid of unclosed-comment-fun nonsense.  It's used
;; in the electric terminator function, but we should probably
;; use something else for that!

(defun proof-assert-until-point (&optional unclosed-comment-fun 
					   ignore-proof-process-p)
  "Process the region from the end of the locked-region until point.
Default action if inside a comment is just process as far as the start of
the comment. 

If you want something different, put it inside
UNCLOSED-COMMENT-FUN. If IGNORE-PROOF-PROCESS-P is set, no commands
will be added to the queue and the buffer will not be activated for
scripting."
  (unless ignore-proof-process-p 
    (proof-activate-scripting nil 'advancing))
  (let ((semis))
    (save-excursion
      ;; Give error if no non-whitespace between point and end of
      ;; locked region.  
      (if (proof-only-whitespace-to-locked-region-p)
	  (error "At the end of the locked region already, there's nothing to do to!"))
      ;; NB: (point) has now been moved backwards to first non-whitespace char.
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (null semis))
	  ;; This is another case that there's nothing to do: maybe
	  ;; because inside a string or something.
	  (if (eq unclosed-comment-fun 'proof-electric-term-incomment-fn)
	    ;; With electric terminator, we shouldn't give an error, but
	    ;; should still insert and pretend it was as if a comment.
	      (proof-electric-term-incomment-fn)
	    (error "I can't find any complete commands to process!"))
	(goto-char (nth 2 (car semis)))
	(and (not ignore-proof-process-p)
	     (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
	       (proof-extend-queue (point) vanillas)))))))


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
  (unless ignore-proof-process-p
    (proof-activate-scripting nil 'advancing))
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
	  (error "I can't see any complete commands to process!"))
      (if (nth 2 (car semis))
	  (goto-char (nth 2 (car semis))))
      (if (not ignore-proof-process-p)
	  (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
	    (proof-extend-queue (point) vanillas)))
      ;; This is done after the queuing to be polite: it means the
      ;; spacing policy enforced here is not put into the locked
      ;; region so the user can re-edit.
      (if (not dont-move-forward)
	  (if for-new-command
	      (proof-script-new-command-advance)
	    (proof-script-next-command-advance))))))

(defun proof-goto-point ()
  "Assert or retract to the command at current position.
Calls proof-assert-until-point or proof-retract-until-point as
appropriate."
  (interactive)
  (if (<= (proof-queue-or-locked-end) (point))
      ;; This asserts only until the next command before point and
      ;; does nothing if whitespace between point and locked region.
      (proof-assert-until-point)
    (proof-retract-until-point)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;      
;; PBP call-backs
;;
(defun proof-insert-pbp-command (cmd)
  "Insert CMD into the proof queue."
  (proof-activate-scripting)
  (let (span)
    (proof-goto-end-of-locked)
    (insert cmd)
    (setq span (make-span (proof-locked-end) (point)))
    (set-span-property span 'type 'pbp)
    (set-span-property span 'cmd cmd)
    (proof-start-queue (proof-unprocessed-begin) (point) 
		       (list (list span cmd 'proof-done-advancing)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Processing the script management queue -- PART 2: retracting
;;

;; Most of the hard work (computing the commands to do the retraction)
;; is implemented in the customisation module (lego.el or coq.el), so
;; code here is fairly straightforward.


;; FIXME: we need to adjust proof-nesting-depth appropriately here.
;; It would help to know the type of retraction which has just
;; occurred: a kill-proof may be assumed to set nesting depth
;; to zero; an undo sequence may alter it some other way.
;; FIXME FIXME: at the moment, the adjustment is made in
;; the wrong place!!

(defun proof-done-retracting (span)
  "Callback for proof-retract-until-point.
We update display after proof process has reset its state.
See also the documentation for `proof-retract-until-point'.
Optionally delete the region corresponding to the proof sequence.
After an undo, we clear the proof completed flag.  The rationale
is that undoing never leaves prover in a \"proof just completed\" 
state, which is true for some proof assistants (but probably not
others)."
  ;; FIXME: need to fixup proof-nesting-depth
  (setq proof-shell-proof-completed nil)
  (if (span-live-p span)
      (let ((start (span-start span))
	    (end (span-end span))
	    (kill (span-property span 'delete-me)))
	;; da: check for empty region seems odd here?
	;; [prevents regions from being detached in set-locked-end]
	(unless (proof-locked-region-empty-p)
	  (proof-set-locked-end start)
	  (proof-set-queue-end start))
	(delete-spans start end 'type)
	(delete-spans start end 'idiom)
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
		  (or (eq (span-property span 'type) 'proof)
		      (eq (span-property span 'type) 'comment)
		      (not (funcall proof-goal-command-p
				    (span-property span 'cmd)))))
	(setq span (prev-span span 'type)))
      span)))

;;
;; NB: Should carefully explain/document this behaviour somewhere.
;; The undo is three-phase:
;;    undo-cmd - ...  - undo-cmd  within proof
;;    kill proof		  exit proof
;;    forget-to-declaration       forget target span
;;
;; It turns out that this behaviour is not quite right for Coq.
;; It might be simpler to just use a single undo/forget 
;; command, which is called in all cases.
;;
(defun proof-retract-target (target delete-region)
  "Retract the span TARGET and delete it if DELETE-REGION is non-nil.
Notice that this necessitates retracting any spans following TARGET,
up to the end of the locked region."
  (let ((end   (proof-unprocessed-begin))
	(start (span-start target))
	(span  (proof-last-goal-or-goalsave))
	actions)

    ;; NB: first section only entered if proof-kill-goal-command is
    ;; non-nill.  Otherwise we expect proof-find-and-forget-fn to do
    ;; all relevent work for arbitrary retractions.  FIXME: clean up

    ;; Examine the last span in the locked region.  
    
    ;; If the last goal or save span is not a proof or
    ;; prover processed file, we examine to see how to remove it.
    (if (and span proof-kill-goal-command 
	     (not (or
		   (memq (span-property span 'type) 
			 '(goalsave proverproc)))))
	;; If the goal or goalsave span ends before the target span,
	;; then we are retracting within the last unclosed proof,
	;; and the retraction just amounts to a number of undo
	;; steps.  
	;; FIXME: really, there shouldn't be more work to do: so
	;;  why call proof-find-and-forget-fn later?
	(if (< (span-end span) (span-end target))
	    (progn
	      ;; Skip comment spans at and immediately following target
	      (setq span target)
	      (while (and span (eq (span-property span 'type) 'comment))
		(setq span (next-span span 'type)))
	      ;; Calculate undos for the current open segment
	      ;; of proof commands
	      (setq actions (proof-setup-retract-action
			     start end 
			     (if (null span) proof-no-command
			       (funcall proof-count-undos-fn span))
			     delete-region)
		    end start))
	  ;; Otherwise, start the retraction by killing off the
	  ;; currently active goal.
	  ;; FIXME: and couldn't we move the end upwards?
	  ;; FIXME: hack proof-nesting-depth here.  This is
	  ;; in the wrong place: it should be done *after* the
	  ;; retraction has succeeded.
	  (setq proof-nesting-depth (1- proof-nesting-depth))
	  (setq actions 
		(proof-setup-retract-action (span-start span) end
					    proof-kill-goal-command
						    delete-region)
		end (span-start span))))
    ;; Check the start of the target span lies before the end
    ;; of the locked region (should always be true since we don't
    ;; make spans outside the locked region at the moment)...
    ;; But end may have moved backwards above: this just checks whether
    ;; there is more retraction to be done.
    (if (> end start) 
	(setq actions
	      ;; Append a retract action to clear the entire
	      ;; start-end region.  Rely on proof-find-and-forget-fn
	      ;; to calculate a command which "forgets" back to
	      ;; the first definition, declaration, or whatever
	      ;; that comes after the target span.
	      ;; FIXME: originally this assumed a linear context, 
	      ;; and that forgetting the first thing  forgets all 
	      ;; subsequent ones.  it might be more general to 
	      ;; allow *several* commands, and even queue these
	      ;; separately for each of the spans following target
	      ;; which are concerned.
	      (nconc actions (proof-setup-retract-action 
			      start end
			      (funcall proof-find-and-forget-fn target)
			      delete-region))))
      
    (proof-start-queue (min start end) (proof-locked-end) actions)))

;; FIXME da:  I would rather that this function moved point to
;; the start of the region retracted?

;; FIXME da: Maybe retraction to the start of
;; a file should remove it from the list of included files?
;; NB: the "interactive" variant is so that we get a simple docstring.
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
  ;; Make sure we're ready
  ;; FIXME: next step in extend regions: (proof-activate-scripting nil 'retracting)
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
    ;; FIXME mmw: make sure we pass by a proof body overlay (is there a better way?)
    ;; FIXME da: why do this??  
    ;; Seems to break expected behaviour.
    ;; (
    ;; (and (eq (span-property span 'type) 'proof)
    ;; (setq span (prev-span span 'type)))
    (proof-retract-target span delete-region)))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Proof General scripting mode definition, part 1.
;;

(eval-and-compile			; to define vars
;;; NB: autoload tag below doesn't work for d-d-m, autoload is in proof.el
;;;###autoload
(define-derived-mode proof-mode fundamental-mode 
  proof-general-name
  "Proof General major mode class for proof scripts.
\\{proof-mode-map}"

  (setq proof-buffer-type 'script)

  ;; font-lock-keywords isn't automatically buffer-local in Emacs 21.2
  (make-local-variable 'font-lock-keywords)

  ;; During write-file it can happen that we re-set the mode for
  ;; the currently active scripting buffer.  The user might also
  ;; do this for some reason.  We could maybe let
  ;; this pass through, but it seems safest to treat it as
  ;; a kill buffer operation (retract and clear spans).
  ;; (NB: other situations seem to cause double successive calls to
  ;; proof-mode).
  (if (eq (current-buffer) proof-script-buffer)
      (proof-script-kill-buffer-fn))

  ;; We set hook functions here rather than in proof-config-done so
  ;; that they can be adjusted by prover specific code if need be.
  (proof-script-set-buffer-hooks)

  (make-local-hook 'after-set-visited-file-name-hooks)
  (add-hook 'after-set-visited-file-name-hooks 'proof-script-set-visited-file-name))

  (make-local-hook 'proof-activate-scripting-hook)
  (add-hook 'proof-activate-scripting-hook 'proof-cd-sync nil t))

;; NB: proof-mode-map declared by define-derived-mode above
(proof-menu-define-keys proof-mode-map)

(defun proof-script-set-visited-file-name ()
  "Called when visited file name is changed.

This is a hook function for `after-set-visited-file-name-hooks'.

For some provers, the file from which script commands are being
processed may be important, and if it is changed with C-x C-w, for
example, we might have to retract the contents or inform the proof
assistant of the new name.  This should be done by adding 
additional functions to `after-set-visited-file-name-hooks'.

At the least, we need to set the buffer local hooks again
with `proof-script-set-buffer-hooks' which is what this function does,
as well as setting `proof-script-buffer-file-name' (which see).

This hook also gives a warning in case this is the active scripting buffer."
  (setq proof-script-buffer-file-true buffer-file-name)
  (if (eq (current-buffer) proof-script-buffer)
      (proof-warning 
"Active scripting buffer changed name; synchronization risked if prover tracks filenames!"))
  (proof-script-set-buffer-hooks))



(defun proof-script-set-buffer-hooks ()
  "Set the hooks for a proof script buffer.
The hooks set here are cleared by write-file, so we use this function
to restore them using `after-set-visited-file-name-hooks'."
  (make-local-hook 'kill-buffer-hook)
  (add-hook 'kill-buffer-hook 'proof-script-kill-buffer-fn t t)
  ;; Reverting buffer is same as killing it as far as PG is concerned
  (make-local-hook 'before-revert-hook)
  (add-hook 'before-revert-hook 'proof-script-kill-buffer-fn t t))

(defun proof-script-kill-buffer-fn ()
  "Value of kill-buffer-hook for proof script buffers.
Clean up before a script buffer is killed.
If killing the active scripting buffer, run proof-deactivate-scripting-auto.
Otherwise just do proof-restart-buffers to delete some spans from memory."
  ;; Deactivate scripting in the current buffer if need be, forcing
  ;; automatic retraction if the buffer is not fully processed.
  (if (eq (current-buffer) proof-script-buffer)
      (proof-deactivate-scripting-auto))
  (proof-restart-buffers (list (current-buffer)))
  ;; Hide away goals, response, and tracing.  This is a hack because
  ;; otherwise we can lead the user to frustration with the
  ;; dedicated windows nonsense.
  (proof-map-buffers 
   (list proof-goals-buffer proof-response-buffer proof-trace-buffer)
   (bury-buffer (current-buffer))))


;; Notes about how to deal with killing/reverting/renaming buffers:
;; (As of XEmacs 21.1.9, see files.el)
;;
;; Killing: easy, set kill-buffer-hook
;; Reverting: ditto, set before-revert-hook to do same as kill.
;; Renaming (write-file): much tricker.  Code for write-file does
;;  several odd things.  It kills off local hook functions, calls
;;  `after-set-visited-file-name-hooks' right at the end to give the
;;  chance to restore them, but then tends to automatically (re-)set
;;  the mode anyway.
  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  Proof General scripting mode definition - part 2
;; 

;; The functions proof-config-done[-related] are called after the
;; derived mode has made its settings.

;; The callback *-config-done mechanism is an irritating hack - there
;; should be some elegant mechanism for computing constants after the
;; child has configured.  Should petition the author of "derived-mode"
;; about this!

(defun proof-config-done-related ()
  "Finish setup of Proof General scripting and related modes.
This is a subroutine of proof-config-done.

This is intended for proof assistant buffers which are similar to
script buffers, but for which scripting is not enabled.  In
particular, we: lock the buffer if it appears on
proof-included-files-list; configure font-lock support from
font-lock-keywords; maybe turn on X-Symbol minor mode.

This is used for Isabelle theory files, which share some scripting 
mode features, but are only ever processed atomically by the proof
assistant."
  (setq proof-script-buffer-file-name buffer-file-name)

  ;; Has buffer already been processed?
  ;; NB: call to file-truename is needed for GNU Emacs which
  ;; chooses to make buffer-file-truename abbreviate-file-name
  ;; form of file-truename.
  (and buffer-file-truename
       (member (file-truename buffer-file-truename)
	       proof-included-files-list)
       (proof-complete-buffer-atomic (current-buffer)))

  ;; calculate some strings and regexps for searching
  (setq proof-terminal-string 
	(if proof-terminal-char
	    (char-to-string proof-terminal-char)
	  ""))

  (make-local-variable 'comment-start)
  (setq comment-start (concat proof-script-comment-start " "))
  (make-local-variable 'comment-end)
  (setq comment-end (concat " " proof-script-comment-end))
  
  (unless proof-script-comment-start-regexp
    (setq proof-script-comment-start-regexp (regexp-quote proof-script-comment-start)))
  (unless proof-script-comment-end-regexp
    (setq proof-script-comment-end-regexp (regexp-quote proof-script-comment-end)))

  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip 
    (concat proof-script-comment-start-regexp "+\\s_?"))

  ;;
  ;; Fontlock support.
  ;;
  ;; Assume font-lock case folding follows proof-case-fold-search
  (proof-font-lock-configure-defaults 'autofontify proof-case-fold-search)
  
  ;; Hack for unfontifying commas (yuck)
  (remove-hook 'font-lock-after-fontify-buffer-hook 'proof-zap-commas-buffer t)
  (remove-hook 'font-lock-mode-hook 'proof-unfontify-separator t)
  (if proof-font-lock-zap-commas
      (progn
	(add-hook 'font-lock-after-fontify-buffer-hook 
		  'proof-zap-commas-buffer nil t)
	(add-hook 'font-lock-mode-hook 'proof-unfontify-separator 
		  nil t)
	;; if we don't have the following in XEmacs, zap-commas fails.
	(if (boundp 'font-lock-always-fontify-immediately)
	    (progn
	      (make-local-variable 'font-lock-always-fontify-immediately)
	      ;; FIXME da: this is pretty nasty.  Disables use of 
	      ;; lazy/caching font lock for large files, and they
	      ;; can take a long time to fontify.
	      (setq font-lock-always-fontify-immediately t)))))

  ;; Maybe turn on x-symbol mode.
  (proof-x-symbol-mode))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic defaults for hooks, based on regexps.
;; 

;; The next step is to use proof-stringfn-match scheme more widely, to
;; allow settings which are string or fn, so we don't need both regexp
;; and function hooks, and so that the other hooks can be functions too.

(defun proof-generic-goal-command-p (str)
  "Is STR a goal?  Decide by matching with proof-goal-command-regexp."
  (proof-string-match-safe proof-goal-command-regexp str))

(defun proof-generic-state-preserving-p (cmd)
  "Is CMD state preserving?  Match on proof-non-undoables-regexp."
  ;; FIXME: logic here is not quite finished: proof-non-undoables are
  ;; certainly not state preserving, but so are a bunch more things,
  ;; i.e. ordinary proof commands which may appear in proof scripts.
  ;; Might be better to add positive and negative regexps for
  ;; state-preserving tests (only one of which needs to be set).
  (not (proof-string-match-safe proof-non-undoables-regexp cmd)))

(defun proof-generic-count-undos (span)
  "Count number of undos in a span, return command needed to undo that far.
Command is set using `proof-undo-n-times-cmd'.

A default value for `proof-count-undos-fn'.

For this function to work properly, you must configure
`proof-undo-n-times-cmd' and `proof-ignore-for-undo-count'."
  (let
      ((case-fold-search proof-case-fold-search)
       (ct 0) str i)
    (while span
      (setq str (span-property span 'cmd))
      (cond ((eq (span-property span 'type) 'vanilla)
	     (unless (proof-stringfn-match proof-ignore-for-undo-count str)
	       (incf ct)))
	    ((eq (span-property span 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length str)) 
	       (if (= (aref str i) proof-terminal-char) (incf ct))
	       (incf i))))
      (setq span (next-span span 'type)))
    (if (= ct 0)
	proof-no-command
      (cond ((stringp proof-undo-n-times-cmd)
	     (format proof-undo-n-times-cmd ct))
	    ((functionp proof-undo-n-times-cmd)
	     (funcall proof-undo-n-times-cmd ct))))))

(defun proof-generic-find-and-forget (span)
  "Calculate a forget/undo command to forget back to SPAN.
This is a long-range forget: we know that there is no
open goal at the moment, so forgetting involves unbinding
declarations, etc, rather than undoing proof steps.

This generic implementation assumes it is enough to find the 
nearest following span with a `name' property, and retract
that using `proof-forget-id-command' with the given name.

If this behaviour is not correct, you must customize the function
with something different."
  ;; Modelled on Isar's find-and-forget function, but less
  ;; general at the moment: will only issue one und command.
  ;; FIXME: would be much cleaner to wrap up the undo behaviour
  ;; also within proofs in this function. 
  (let (str ans typ name answers)
    (while span
      (setq ans nil)
      (setq str (span-property span 'cmd))
      (setq typ (span-property span 'type))
      (cond
       ;; comment, diagnostic, nested proof command: skip
       ((or (eq typ 'comment)
	    (eq typ 'proof)
	    (and proof-ignore-for-undo-count cmd
		 (proof-string-match proof-ignore-for-undo-count cmd))))
       ;; some named element: use generic forget-id function; finish.
       ((setq name (span-property span 'name))
        (setq ans (format proof-forget-id-command name))
	(setq span nil)))
      (if ans (setq answers (cons ans answers)))
      (if span (setq span (next-span span 'type))))
    (if (null answers) proof-no-command (apply 'concat answers))))

;;
;; End of new generic functions
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;
;; Sanity checks on important settings
;;

(defconst proof-script-important-settings
  '(proof-script-comment-start			;
    proof-script-comment-end
    proof-save-command-regexp
;    proof-goal-command-regexp	        ; not needed if proof-goal-command-p is set
;    proof-goal-with-hole-regexp		; non-essential?
;    proof-save-with-hole-regexp		; non-essential?
;    proof-showproof-command		; non-essential
;    proof-goal-command			; non-essential
;    proof-save-command			; do
;    proof-kill-goal-command		; do
    ))

(defun proof-config-done () 
  "Finish setup of Proof General scripting mode.
Call this function in the derived mode for the proof assistant to
finish setup which depends on specific proof assistant configuration."

  (proof-config-done-related)

  ;; Following group of settings only relevant if the current
  ;; buffer is really a scripting buffer.  Isabelle Proof General
  ;; has theory file buffers which share some aspects, they
  ;; just use proof-config-done-related.

  ;; Preamble: make this mode class "pg-sticky" so that renaming file
  ;; to something different doesn't change the mode, no matter what
  ;; the filename.  This is a hack so that write-file will work:
  ;; otherwise Emacs insists (as of XEmacs 21.1.9 at least) on
  ;; re-setting the mode, which leads to problems with synchronization
  ;; and losing extents.  (Attempt to catch this in proof-mode by
  ;; looking for active scripting buffer fails; perhaps because of
  ;; kill buffer function)
  (put major-mode 'mode-class 'pg-sticky)

  ;; First, define some values if they aren't defined already.
  (unless proof-mode-for-script
      (setq proof-mode-for-script major-mode))

  (if (and proof-non-undoables-regexp 
	   (not proof-ignore-for-undo-count))
      (setq proof-ignore-for-undo-count 
	    proof-non-undoables-regexp))

  ;; Give warnings if some crucial settings haven't been made
  (dolist (sym proof-script-important-settings)
    (proof-warn-if-unset "proof-config-done" sym))

  ;; Additional key definitions which depend on configuration for
  ;; specific proof assistant.
  ;; FIXME da: generalize here.  Might have electric terminator for
  ;; other parsing mechanisms too, using new proof-script-parse-function
  ;; Could use a default terminal char
  (if proof-terminal-char
      (progn
	(define-key proof-mode-map
	  (vconcat [(control c)] (vector proof-terminal-char))
	  'proof-electric-terminator-toggle)
	(define-key proof-mode-map (vector proof-terminal-char)
	  'proof-electric-terminator)))
  ;; It's ugly, but every script buffer has a local copy changed in
  ;; sync by the fn proof-electric-terminator-enable 
  (setq proof-electric-terminator proof-electric-terminator-enable)

  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'proof-indent-line)

  ;; Toolbar and scripting menu
  ;; NB: autloads proof-toolbar, which defines proof-toolbar-scripting-menu.
  (proof-toolbar-setup)

  ;; Menus: the Proof-General and the specific menu
  (proof-menu-define-main)
  (proof-menu-define-specific)
  (easy-menu-add proof-mode-menu proof-mode-map)
  (easy-menu-add proof-assistant-menu proof-mode-map)

  ;; Choose parsing mechanism according to different kinds of script syntax.  
  ;; Choice of function depends on configuration setting.
  (unless (fboundp 'proof-segment-up-to)
    (if proof-script-use-old-parser
	;; Configuration for using old parsing mechanism.
	(cond
	 (proof-script-parse-function	;; still allowed to override in 3.2
	  (defalias 'proof-segment-up-to 'proof-segment-up-to-parser))
	 ;; 3.2 mechanism here
	 (proof-script-command-start-regexp
	  (defalias 'proof-segment-up-to 'proof-segment-up-to-cmdstart))
	 (t
	  (defalias 'proof-segment-up-to 'proof-segment-up-to-cmdend)
	  (unless proof-script-command-end-regexp
	    (proof-warn-if-unset "proof-config-done" 'proof-terminal-char)
	    (setq proof-script-command-end-regexp
		  (if proof-terminal-char
		      (regexp-quote (char-to-string proof-terminal-char))
		    "$")))))
      ;; Configuration for using new parsing (3.3 and later)
      (progn
	(defalias 'proof-segment-up-to 'proof-segment-up-to-parser)
	(cond   
	 (proof-script-parse-function
	  ;; already set, nothing to do
	  )
	 (proof-script-sexp-commands
	  (setq proof-script-parse-function 'proof-script-generic-parse-sexp))
	 (proof-script-command-start-regexp
	  (setq proof-script-parse-function 'proof-script-generic-parse-cmdstart))
	 ((or proof-script-command-end-regexp proof-terminal-char)
	  (setq  proof-script-parse-function 'proof-script-generic-parse-cmdend)
	  (unless proof-script-command-end-regexp
	    (proof-warn-if-unset "probof-config-done" 'proof-terminal-char)
	    (setq proof-script-command-end-regexp
		  (if proof-terminal-char
		      (regexp-quote (char-to-string proof-terminal-char))
		    "$"))))
	 (t
	  (error "Configuration error: must set `proof-terminal-char' or one of its friends."))))
      )) ;  default if nothing set is EOL.

  ;; Make sure func menu is configured.  (NB: Ideal place for this and
  ;; similar stuff would be in something evaluated at top level after
  ;; defining the derived mode: normally we wouldn't repeat this
  ;; each time the mode function is run, so we wouldn't need "pushnew").

  (cond ((proof-try-require 'func-menu)
	 ;; FIXME: we'd like to let the library load later, but 
	 ;; it's a bit tricky: this stuff doesn't seem to work
	 ;; in an eval-after-load body (local vars?).
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
	     ;; Enable func-menu for this mode if regexps set now
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
      (setq buffer-offer-save t))

  ;; Localise the invisibility glyph (XEmacs only:
  (let ((img (proof-get-image "hiddenproof" t nil)))
    (cond
     ((and img proof-running-on-XEmacs)
      (set-glyph-image invisible-text-glyph img (current-buffer)))))

  ;; To begin with, make everything visible in the buffer
  ;; (FIXME: this is done via proof-init-segmentation, now,
  ;; when is that called?)
  (setq buffer-invisibility-spec nil)

  ;; Finally, make sure the user has been welcomed!
  ;; [NB: this doesn't work well, gets zapped by loading messages]
  (proof-splash-message))


(provide 'proof-script)
;; proof-script.el ends here.

