;;; pg-assoc.el --- Functions for associated buffers
;;
;; Copyright (C) 1994-2008 LFCS Edinburgh. 
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;
;; Defines an empty mode inherited by modes of the associated buffers.
;;

;;; Code:

(eval-when-compile 
  (require 'proof-syntax)			; proof-replace-{string,regexp}
  (require 'span)				; spans
  (require 'cl))				; incf

(require 'proof)				; globals


(eval-and-compile ; defines proof-universal-keys-only-mode-map at compile time
  (define-derived-mode proof-universal-keys-only-mode fundamental-mode
    proof-general-name "Universal keymaps only"
    ;; Doesn't seem to supress TAB, RET
    (suppress-keymap proof-universal-keys-only-mode-map 'all)
    (proof-define-keys proof-universal-keys-only-mode-map 
		       proof-universal-keys)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Return a list of associated buffers
;;

;;;###autoload
(defun proof-associated-buffers ()
  "Return a list of the associated buffers.  
Some may be dead/nil."
  (list proof-goals-buffer
	proof-response-buffer
	proof-trace-buffer
	proof-thms-buffer))


;;;###autoload
(defun proof-associated-windows ()
  "Return a list of the associated buffers windows.  
Dead or nil buffers are not represented in the list."
  (let ((bufs (proof-associated-buffers))
	buf wins)
    (while bufs
      (setq buf (car bufs))
      (if (and buf (get-buffer-window buf))
	  (setq wins (cons (get-buffer-window buf) wins)))
      (setq bufs (cdr bufs)))
    wins))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Manipulating prover output
;;

(defun pg-assoc-strip-subterm-markup (string)
  "Return STRING with subterm and pbp annotations removed.
Special annotations are characters with codes higher than
'pg-subterm-first-special-char'.
If pg-subterm-first-special-char is unset, return STRING unchanged."
  (if pg-subterm-first-special-char
      (let* ((ip 0) (op 0) (l (length string)) (out (make-string l ?x )))
	(while (< ip l)
	  (if (>= (aref string ip) pg-subterm-first-special-char)
	      (if (and pg-subterm-start-char
		       (char-equal (aref string ip) pg-subterm-start-char))
		  (progn (incf ip)
			 ;; da: this relies on annotations being
			 ;; characters between \200 and first special
			 ;; char (e.g. \360).  Why not just look for
			 ;; the sep char??
			 (while 
			     (< (aref string ip) 
				pg-subterm-first-special-char)
			   (incf ip))))
	    (aset out op (aref string ip))
	    (incf op))
	  (incf ip))
	(substring out 0 op))
    string))

(defvar pg-assoc-ann-regexp nil
  "Cache of regexp for `pg-assoc-strip-subterm-markup-buf'.")

(defun pg-assoc-strip-subterm-markup-buf (start end)
  "Remove subterm and pbp annotations from region."
  (if pg-subterm-start-char
      (progn
	(unless pg-assoc-ann-regexp
	  (setq pg-assoc-ann-regexp
		(concat 
		 (regexp-quote (char-to-string pg-subterm-start-char))
		 "[^" 
		 (regexp-quote (char-to-string pg-subterm-sep-char))
		 "]*"
		 (regexp-quote (char-to-string pg-subterm-sep-char)))))
	(save-restriction
	  (narrow-to-region start end)
	  (goto-char start)
	  (proof-replace-regexp pg-assoc-ann-regexp "")
	  (goto-char start)
	  (proof-replace-string (char-to-string pg-subterm-end-char) "")
	  (goto-char start)
	  (if pg-topterm-regexp
	      (proof-replace-regexp pg-topterm-regexp ""))))))
	  
	 
(defun pg-assoc-strip-subterm-markup-buf-old (start end)
  "Remove subterm and pbp annotations from region START END."
  (let (c)
    (goto-char start)
    (while (< (point) end)
      ;; FIXME: small OBO here: if char at end is special
      ;; it won't be removed.
      (if (>= (setq c (char-after (point))) 
	      pg-subterm-first-special-char)
	  (progn
	    (delete-char 1)
	    (decf end)
	    (if (char-equal c pg-subterm-start-char)
		(progn 
		  ;; FIXME: could simply replace this by replace
		  ;; match, matching on sep-char??
		  (while (and (< (point) end)
			      (< (char-after (point))
				 pg-subterm-first-special-char))
		    (delete-char 1)
		    (decf end)))))
	(forward-char)))
    end))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Subterm and PBP markup (goals and possibly response buffer)
;;; 

(defun pg-assoc-make-top-span (start end)
  "Make a top span (goal/hyp area) for mouse active output in START END."
  (let (span typname)
    (goto-char start)
    ;; skip the pg-topterm-regexp itself
    (if (looking-at pg-topterm-regexp) 
	(forward-char (- (match-end 0) (match-beginning 0))))
    ;; typname is expected to be a cons-cell of a type (goal/hyp)
    ;; with a name, retrieved from the text immediately following
    ;; the topterm-regexp annotation.
    (let ((topterm (point))) 
      (setq typname (funcall pg-topterm-goalhyplit-fn)) ;; should be non-nil!
      (goto-char topterm))
    (setq start (point))
    (if (eq (car-safe typname) 'lit)
	;; Use length of literal command for end point
	(forward-char (length (cdr typname)))
      ;; Otherwise, use start/end of line before next annotation/buffer end
      (goto-char start)
      (beginning-of-line)
      (setq start (point))
      (goto-char end) ;; next annotation/end of buffer
      (beginning-of-line)
      (backward-char))
    (setq span (span-make start (point)))
    (span-set-property span 'mouse-face 'highlight)
    (span-set-property span 'face 'proof-active-area-face)
    (span-set-property span 'proof-top-element typname)))

(defun pg-assoc-analyse-structure (start end)
  "Analyse the region between START and END for subterm and PBP markup.

For subterms, we can make nested regions in the concrete syntax into
active mouse-highlighting regions, each of which can be used to
communicate a selected term back to the prover.  The output text is
marked up with the annotation scheme:

 	 [  <annotation>      |       <subterm/concrete> ] 

         ^                    ^                          ^
	 |                    |                          |
pg-subterm-start-char  pg-subterm-sep-char  pg-subterm-end-char

The annotation is intended to indicate a node in the abstract syntax
tree inside the prover, which can be used to pick out the internal
representation of the term itself.  We assume that the annotation
takes the form of a sequence of characters:

   <length of shared prefix previous>  <ann1> <ann2> .. <annN>

Where each element <..> is a character which is *less* than
pg-subterm-first-special-char, but *greater* than 128.  Each 
character code has 128 subtracted to yield a number.  The first
character allows a simple optimisation by sharing a prefix of
the previous (left-to-right) subterm's annotation.  (See the
variable `pg-subterm-anns-use-stack' for an alternative 
optimisation.)

For subterm markup without communication back to the prover, the
annotation is not needed, but the first character must still be given.

For proof-by-pointing (PBP) oriented markup, `pg-topterm-regexp' and
`pg-topterm-goalhyplit-fn' should be set.  Together these allow
further active regions to be defined, corresponding to \"top elements\"
in the proof-state display.  A \"top element\" is currently assumed
to be either a hypothesis or a subgoal, and is assumed to occupy 
a line (or at least a line).  The markup is simply
  
                 & <goal or hypthesis line in proof state>
                 ^
		 |
   pg-topterm-regexp

And the function `pg-topterm-goalhyplit-fn' is called to do the
further analysis, to return an indication of the goal/hyp and
record a name value.  These values are used to construct PBP
commands which can be sent to the prover."
  (if (or pg-subterm-start-char pg-topterm-regexp) ;; markup for topterm alone
  (let* 
      ((cur start)
       (len (- end start))
       (ann (make-string len ?x)) ; (more than) enough space for longest ann'n
       (ap  0)
       c stack topl span)

    (while (< cur end)
      (setq c (char-after cur))
      (cond
       ;; Seen goal regexp: this is the start of a top extent
       ;; (assumption, goal, literal command)
       ((save-excursion
	  (goto-char cur)
	  (looking-at pg-topterm-regexp))
	(setq topl (cons cur topl))
	(setq ap 0))

       ;; Seen subterm start char: it's followed by a char
       ;; indicating the length of the annotation prefix
       ;; which can be shared with the previous subterm.
       ((and pg-subterm-start-char ;; ignore if subterm start not set
	     (= c pg-subterm-start-char))
	(incf cur)
	(if pg-subterm-anns-use-stack
	    (setq ap (- ap (- (char-after cur) 128)))
	  (setq ap (- (char-after cur) 128)))
	(incf cur)
	;; Now search for a matching end-annotation char, recording the 
	;; annotation found.
	(while (not (= (setq c (char-after cur)) pg-subterm-sep-char))
	  (aset ann ap (- c 128))
	  (incf ap)
	  (incf cur))
	;; Push the buffer pos and annotation
	(setq stack (cons cur 
			  (cons (substring ann 0 ap) stack))))

       ;; Seen a subterm end char, terminating an annotated region
       ;; in the concrete syntax.  We make a highlighting span now.
       ((and (consp stack) (= c pg-subterm-end-char))
	;; (consp stack) added to make the code more robust.
	;; [ Condition violated with lego/example.l and GNU Emacs 20.3 ]
	(setq span (span-make (car stack) cur))
	(span-set-property span 'mouse-face 'highlight)
	(span-set-property span 'goalsave (cadr stack));; FIXME: 'goalsave?
	;; (span-set-property span 'balloon-help helpmsg)
	(span-set-property span 'help-echo 'pg-goals-get-subterm-help)
	(if pg-subterm-anns-use-stack
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
    
    ;; List of topterm beginning positions (goals/hyps) found
    (setq topl (reverse (cons end topl)))
    
    ;; Proof-by-pointing markup assumes "top" elements which define a
    ;; context for a marked-up (sub)term: we assume these contexts to
    ;; be either a subgoal to be solved or a hypothesis.  
    ;; Top element spans are only made if pg-topterm-goalhyplit-fn is set.
    ;; NB: If we want Coq pbp: (setq coq-current-goal 1) 
    (if pg-topterm-goalhyplit-fn
	(while (setq ap (car topl) 
		     topl (cdr topl))
	  (pg-assoc-make-top-span ap (car topl))))

    ;; Finally: strip the specials.  This should
    ;; leave the spans in exactly the right place.
    (pg-assoc-strip-subterm-markup-buf start end))))



(provide 'pg-assoc)
;;; pg-assoc.el ends here
