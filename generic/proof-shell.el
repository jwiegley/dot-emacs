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

(require 'proof)

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

(defvar proof-action-list nil "action list")




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
  (proof-start-shell)
  (if proof-shell-busy (error "Proof Process Busy!")))

(defun proof-shell-live-buffer ()
  "Return buffer of active proof assistant, or nil if none running."
  (and proof-shell-buffer
       (comint-check-proc proof-shell-buffer)
       proof-shell-buffer))

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
	; (if (not (member (current-buffer) proof-script-buffer-list))
	; (error "Bug in proof-release-lock: Don't own process"))
  (setq proof-shell-busy nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Starting and stopping the proof-system shell                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-start-shell ()
  "Initialise a shell-like buffer for a proof assistant.

Also generates goal and response buffers.
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
	(set-buffer proof-response-buffer)
	(funcall proof-mode-for-response)
	(set-buffer proof-pbp-buffer)
	(funcall proof-mode-for-pbp))

      ;; FIXME: Maybe this belongs outside this function?
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
    (cond ((and (member (current-buffer) proof-script-buffer-list)
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
      (pop-to-buffer (car proof-script-buffer-list))
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
	  (format pbp-change-goal (cdr top-info))))))
    ))


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
      (set-buffer proof-pbp-buffer)
      (erase-buffer)
      (insert (substring out 0 op))
      (proof-display-and-keep-buffer proof-pbp-buffer)

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
  "Displays output from `proof-shell-buffer' in
  `proof-response-buffer'.
The region in `proof-shell-buffer begins with the match for START-REGEXP and is delimited by
END-REGEXP. The match for END-REGEXP is not part of the specified region.
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
    (proof-response-buffer-display string append-face)))

(defun proof-shell-handle-delayed-output ()
  "Display delayed output. 
See the documentation fo `proof-shell-delayed-output' for furter details."
  (let ((ins (car proof-shell-delayed-output))
	(str (cdr proof-shell-delayed-output)))
    (cond 
     ((eq ins 'insert)
      (setq str (proof-shell-strip-annotations str))
      (save-excursion ;current-buffer
	(set-buffer proof-response-buffer)
	(erase-buffer)
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

(defun proof-shell-handle-error (cmd string)
  "React on an error message triggered by the prover.
We first flush unprocessed goals to the goals buffer.
The error message is displayed in the `proof-response-buffer'. Then,
we call `proof-shell-handle-error-hook'. "

  ;; flush goals
  (or (equal proof-shell-delayed-output (cons 'insert "Done."))
      (save-excursion ;current-buffer
	(set-buffer proof-pbp-buffer)
	(erase-buffer)
	(insert (proof-shell-strip-annotations 
		   (cdr proof-shell-delayed-output)))
	(proof-display-and-keep-buffer proof-pbp-buffer)))

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
		  (if proof-script-buffer-list
		      (set-buffer (car proof-script-buffer-list)))
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
  (if proof-script-buffer-list
      (set-buffer (car proof-script-buffer-list))))
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
    (proof-clean-buffer proof-pbp-buffer)
   (setq proof-shell-delayed-output (cons 'insert "\nAborted\n"))
    ())
	 
   ((string-match proof-shell-proof-completed-regexp string)
    (proof-clean-buffer proof-pbp-buffer)
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



; Pass start and end as nil if the cmd isn't in the buffer.

;; FIXME: note: removed optional 'relaxed' arg
(defun proof-start-queue (start end alist)
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
    (if proof-script-buffer-list
	(set-buffer (car proof-script-buffer-list)))
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

;; da: this note seems to be false!
;; ******** NB **********
;;  While we're using pty communication, this code is OK, since all
;; eager annotations are one line long, and we get input a line at a
;; time. If we go over to piped communication, it will break.

(defun proof-shell-message (str)
  "Output STR in minibuffer."
  (message (concat "[" proof-assistant "] " str)))

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
	      'proof-eager-annotation-face))
    (proof-shell-message str))))

(defun proof-files-to-buffers (filenames)
  "Converts a list of FILENAMES into a list of BUFFERS."
  (if (null filenames) nil
    (let* ((buffer (proof-file-to-buffer (car filenames)))
	  (rest (proof-files-to-buffers (cdr filenames))))
      (if buffer (cons buffer rest) rest))))
	  
		  
(defun proof-shell-process-urgent-message (message)
  "Analyse urgent MESSAGE for display, included file, or retracted file."
  
  ;; Is the prover processing a file?
  (cond ((and proof-shell-process-file 
	      (string-match (car proof-shell-process-file) message))
	 (let
	     ((file (funcall (cdr proof-shell-process-file) message)))
	   (if (and proof-script-buffer-list (string= file ""))
	       (setq file (buffer-file-name (car proof-script-buffer-list))))
	   (if file
	       (proof-register-possibly-new-processed-file file))))

  ;; Is the prover retracting across files?
	((and proof-shell-retract-files-regexp
	      (string-match proof-shell-retract-files-regexp message))
	 (let ((current-included proof-included-files-list))
	   (setq proof-included-files-list
		 (funcall proof-shell-compute-new-files-list message))
	   (proof-restart-buffers
	    (remove (car-safe proof-script-buffer-list)
		    (proof-files-to-buffers
		     (set-difference current-included
				     proof-included-files-list))))))
	(t
	 (proof-shell-message message)
	 (proof-response-buffer-display message
					'proof-eager-annotation-face))))

(defvar proof-shell-urgent-message-marker nil
  "Marker in proof shell buffer used for parsing urgent messages.")

(defun proof-shell-process-urgent-messages ()
  "Scan the shell buffer for urgent messages.
Scanning starts from proof-shell-urgent-message-pos and processes
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
	    
;; FIXME da: I suspect this could miss output in the unfortunate
;; circumstance that a prompt consists of more than one character and
;; is split between output chunks.  Really the matching should be
;; based on the buffer contents rather than the string just received.
(defun proof-shell-filter (str) 
  "Filter for the proof assistant shell-process.
We sleep until we get a wakeup-char in the input, then run
proof-shell-process-output, and set proof-marker to keep track of
how far we've got."
  (save-excursion
    (and proof-shell-eager-annotation-start
	 (proof-shell-process-urgent-messages))
       
    (if (or
	 ;; Some proof systems can be hacked to have annotated prompts;
	 ;; for these we set proof-shell-wakeup-char to the annotation special.  
	 (and proof-shell-wakeup-char
	      (string-match (char-to-string proof-shell-wakeup-char) str))
	 ;; Others may rely on a standard top-level (e.g. SML) whose
	 ;; prompt are difficult or impossible to hack.
	 ;; For those we use the annotated prompt regexp.
	 (string-match proof-shell-annotated-prompt-regexp str))
	(if (null (marker-position proof-marker))
	    ;; Set marker to first prompt in output buffer, and sleep again.
	    ;; FIXME da: what happens if we don't get a prompt in the
	    ;; first output chunk?  This needs fixing in case re-search fails.
	    (progn
	      (goto-char (point-min))
	      (re-search-forward proof-shell-annotated-prompt-regexp)
	      (set-marker proof-marker (point)))
	  ;; We've matched against a second prompt in str now.
	  ;; First, the blasphemous situation that the proof-action-list
	  ;; is empty so that the process has output something for
	  ;; some other reason (perhaps it's just being chatty).  
	  ;; We graciously accept the situation nowadays, rather
	  ;; than shrieking out bug reports.
	  (if proof-action-list
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
		   (t (if (proof-shell-exec-loop)
			  (proof-shell-handle-delayed-output)))))))))))

(defun proof-shell-done-invisible (span) ())

;; da: What is the rationale here for making the *command* sent
;; invisible, rather than the stuff returned????
;; doc string makes no sense of this.
;; FIXME: note: removed optional 'relaxed' arg
(defun proof-shell-invisible-command (cmd)
  "Send cmd to the proof process without responding to the user."
  (proof-shell-ready-prover)
  (if (not (string-match proof-re-end-of-cmd cmd))
      (setq cmd (concat cmd proof-terminal-string)))
  (proof-start-queue nil nil (list (list nil cmd
  'proof-shell-done-invisible))))

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
  ))


(easy-menu-define proof-shell-menu
		  proof-shell-mode-map
		  "Menu used in Proof General shell mode."
		  (cons proof-mode-name (cdr proof-shell-menu)))

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
    (set-buffer proof-pbp-buffer)
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
    (accept-process-output (get-buffer-process proof-shell-buffer))

    ;; If the proof process in invoked on a different machine e.g.,
    ;; for proof-prog-name="ssh fastmachine proofprocess", one needs
    ;; to adjust the directory. Perhaps one might even want to issue
    ;; this command whenever a new scripting buffer is active?
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
      (if (accept-process-output (get-buffer-process proof-shell-buffer) 15)
	  ()
	(error "Failed to initialise proof process")))))

(eval-and-compile
(define-derived-mode proof-universal-keys-only-mode fundamental-mode
    proof-mode-name "Universal keymaps only"
    (suppress-keymap proof-universal-keys-only-mode-map 'all)
    (proof-define-keys proof-universal-keys-only-mode-map proof-universal-keys)))

(eval-and-compile			; to define vars
(define-derived-mode pbp-mode proof-universal-keys-only-mode
  proof-mode-name "Proof by Pointing"
  ;; defined-derived-mode pbp-mode initialises pbp-mode-map
  (setq proof-buffer-type 'pbp)
  ;; (define-key pbp-mode-map [(button2)] 'pbp-button-action)
  (erase-buffer)))

(eval-and-compile
(define-derived-mode proof-response-mode proof-universal-keys-only-mode
  "PGResp" "Responses from Proof Assistant"
  (setq proof-buffer-type 'response)))




(provide 'proof-shell)
;; proof-shell.el ends here.