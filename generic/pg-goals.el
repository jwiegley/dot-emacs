;; pg-goals.el  Proof General goals buffer mode.
;;
;; Copyright (C) 1994-2002 LFCS Edinburgh. 
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Goals buffer mode
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-and-compile			; to define proof-goals-mode-map
(define-derived-mode proof-goals-mode proof-universal-keys-only-mode
  proof-general-name 
  "Mode for goals display.  
May enable proof-by-pointing or similar features.
\\{proof-goals-mode-map}"
  ;; defined-derived-mode proof-goals-mode initialises proof-goals-mode-map
  (setq proof-buffer-type 'goals)
  (easy-menu-add proof-goals-mode-menu proof-goals-mode-map)
  (easy-menu-add proof-assistant-menu proof-goals-mode-map)
  (proof-toolbar-setup)
  (erase-buffer)))

;;
;; Keys for goals buffer
;;
(define-key proof-goals-mode-map [q] 'bury-buffer)
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


;;
;; Menu for goals buffer  (identical to response mode menu currently)
;;
(easy-menu-define proof-goals-mode-menu
		  proof-goals-mode-map
		  "Menu for Proof General goals buffer."
		  (cons proof-general-name 
			(append
			 proof-toolbar-scripting-menu
			 proof-shared-menu
			 proof-config-menu
			 proof-bug-report-menu)))

(defun proof-goals-config-done ()
  "Initialise the goals buffer after the child has been configured."
  (proof-font-lock-configure-defaults nil)
  (proof-x-symbol-configure))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Subterm markup and Proof-by-Pointing functionality
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Fairly specific to the mechanism implemented in LEGO
;; To make sense of this code, you should read the
;; relevant LFCS tech report by tms, yb, and djs

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
	;; Get either the proof body or whole goalsave
	(setq span (or 
		    (span-at (point) 'proof)
		    (span-at (point) 'goalsave)))
	(if span (copy-region-as-kill
		  (span-start span) 
		  (span-end span)))))
    (if (and span (not (eq proof-buffer-type 'goals)))
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

;; Using the spans in a mouse behavior is quite simple: from the
;; mouse position, find the relevant span, then get its annotation
;; and produce a piece of text that will be inserted in the right
;; buffer.  

(defun proof-expand-path (string)
  (let ((a 0) (l (length string)) ls)
    (while (< a l) 
      (setq ls (cons (int-to-string 
		      (char-to-int (aref string a)))
		     (cons " " ls)))
      (incf a))
    (apply 'concat (nreverse ls))))

(defun pbp-construct-command ()
  (let* ((span (span-at (point) 'goalsave))
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
					 (span-property span 'goalsave))))))
       ((eq (car top-info) 'hyp)
	(proof-shell-invisible-command
	 (format pbp-hyp-command (cdr top-info))))
       (t
	 (proof-insert-pbp-command
	  (format pbp-change-goal (cdr top-info))))))))

;;
;; Goals buffer processing
;;
;; FIXME: rename next fn proof-display-in-goals or similar
(defun proof-shell-analyse-structure (string)
  "Analyse the term structure of STRING and display it in proof-goals-buffer.
This function converts proof-by-pointing markup into mouse-highlighted
extents."
  (save-excursion
      ;; Response buffer may be out of date. It may contain (error)
      ;; messages relating to earlier proof states
      
      ;; FIXME da: this isn't always the case.  In Isabelle
      ;; we get <WARNING MESSAGE> <CURRENT GOALS> output,
      ;; or <WARNING MESSAGE> <ORDINARY MESSAGE>.  Both times
      ;; <WARNING MESSAGE> would be relevant.
      ;; We should only clear the output that was displayed from
      ;; the *previous* prompt.

      ;; Erase the response buffer if need be, maybe also removing the
      ;; window.  Indicate that it should be erased before the next
      ;; output.
      (proof-shell-maybe-erase-response t t)

      ;; Erase the goals buffer and add in the new string
      (set-buffer proof-goals-buffer)
      (erase-buffer)
      (insert string)
      
      ;; Do term-structure markup if its enabled
      (unless (not proof-shell-goal-char) 
	(proof-shell-analyse-structure1 (point-min) (point-max)))

      ;; Now get fonts and characters right
      ;; FIXME: this may be broken by markup or aided by it!
      (proof-fontify-region (point-min) (point-max))

      ;; Record a cleaned up version of output string
      (setq proof-shell-last-output 
	    (buffer-substring (point-min) (point-max)))

      (set-buffer-modified-p nil)	; nicety

      ;; Keep point at the start of the buffer.  Might be nicer to
      ;; keep point at "current" subgoal a la Isamode, but never mind
      ;; just now.
      (proof-display-and-keep-buffer proof-goals-buffer (point-min))))


(defun proof-shell-analyse-structure1 (start end)
  "Really analyse the structure here."
  (let* 
      ((cur start)
       (len (- end start))
       (ann (make-string len ?x)) ; (more than) enough space for longest ann'n
       (ap  0)
       c stack topl span)

    (while (< cur end)
      (setq c (char-after cur))
      (cond
       ;; Seen goal char: this is the start of a top extent
       ;; (assumption or goal)
       ((= c proof-shell-goal-char)
	(setq topl (cons cur topl))
	(setq ap 0))

       ;; Seen subterm start char: it's followed by at least 
       ;; one subterm pointer byte
       ((= c proof-shell-start-char)
	(incf cur)
	(if proof-analyse-using-stack
	    (setq ap (- ap (- (char-after cur) 128)))
	  (setq ap (- (char-after cur) 128)))
	(incf cur)
	;; Now search for a matching end-annotation char, recording the 
	;; annotation found.
	(while (not (= (setq c (char-after cur)) proof-shell-end-char))
	  (aset ann ap (- c 128))
	  (incf ap)
	  (incf cur))
	;; Push the buffer pos and annotation
	(setq stack (cons cur 
			  (cons (substring ann 0 ap) stack))))

       ;; Seen a field char, which terminates an annotated position
       ;; in the concrete syntax.  We make a highlighting span now.
       ((and (consp stack) (= c proof-shell-field-char))
	;; (consp stack) added to make the code more robust.
	;; [ Condition violated with lego/example.l and GNU Emacs 20.3 ]
	(setq span (make-span (car stack) cur))
	(set-span-property span 'mouse-face 'highlight)
	(set-span-property span 'goalsave (cadr stack));; FIXME: 'goalsave?
	(if proof-analyse-using-stack
	    ;; Pop annotation off stack
	    (progn
	      (setq ap 0)
	      (while (< ap (length (cadr stack)))
		(aset ann ap (aref (cadr stack) ap))
		(incf ap))))
	;; Finish popping annotations
	(setq stack (cdr (cdr stack)))))
      ;; On to next char
      (incf cur))
    
    ;; List of subterm regions (goals) found
    (setq topl (reverse (cons end topl)))
    
    ;; If we want Coq pbp: (setq coq-current-goal 1)
    (if proof-goal-hyp-fn
	(while (setq ip (car topl) 
		     topl (cdr topl))
	  (pbp-make-top-span ip (car topl))))

    ;; Finally: strip the specials.  This should
    ;; leave the spans in exactly the right place.
    (proof-shell-strip-special-annotations-buf start end)))


(defun pbp-make-top-span (start end)
  "Make a top span (goal area) for mouse active output."
  (let (span name)
    (goto-char start)
    ;; We need to skip an annotation here for proof-goal-hyp-fn
    ;; to work again now we don't strip buffers.  Is it
    ;; safe to assume that we're called exactly at proof-goal-char?
    ;; [maybe except for last case?]
    (forward-char)
    (setq name (funcall proof-goal-hyp-fn))
    (beginning-of-line)
    (setq start (point))
    (goto-char end)
    (beginning-of-line)
    (backward-char)
    (setq span (make-span start (point)))
    (set-span-property span 'mouse-face 'highlight)
    (set-span-property span 'proof-top-element name)))


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
			     ;; FIXME: this relies on annotations 
			     ;; being characters between 
			     ;; \200 and \360 (first special char).
			     ;; Why do we not just look for the 
			     ;; field char??
			     (< (aref string ip) 
				proof-shell-first-special-char)
			   (incf ip))))
	    (aset out op (aref string ip))
	    (incf op))
	  (incf ip))
	(substring out 0 op))
    string))

(defun proof-shell-strip-special-annotations-buf (start end)
  "Strip specials and return new END value."
  (let (c)
    (goto-char start)
    (while (< (point) end)
      ;; FIXME: small OBO here: if char at end is special
      ;; it won't be removed.
      (if (>= (setq c (char-after (point))) 
	      proof-shell-first-special-char)
	  (progn
	    (delete-char 1)
	    (decf end)
	    (if (char-equal c proof-shell-start-char)
		(progn 
		  ;; FIXME: could simply replace this by replace
		  ;; match, matching on field-char??
		  (while (and (< (point) end)
			      (< (char-after (point))
				 proof-shell-first-special-char))
		    (delete-char 1)
		    (decf end)))))
	(forward-char)))
    end))


(provide 'pg-goals)
;; pg-goals.el ends here.
