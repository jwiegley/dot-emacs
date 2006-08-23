; coq-syntax.el indentation stuff for Coq
;; Copyright (C) 1997, 1998 LFCS Edinburgh. 
;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <courtieu@lri.fr>

;;Pierre: This is experimental, the code is rather ugly for the moment.


(require 'coq-syntax)

(defconst coq-any-command-regexp
  (proof-regexp-alt (proof-ids-to-regexp coq-keywords)))


(defconst coq-indent-inner-regexp
  (proof-regexp-alt "[[]()]" "|" "ö’" ; forall with x-symbol (nomule) 
                                         ; must not be enclosed by \\<and \\>
                                        ;"~" forall x-symb mule but interacts with 'not'

						  (proof-ids-to-regexp   '("as"
;															"ALL"
;															"True"
;															"False"
															"Cases"
															"match"
;															"EX"
															"else"
;															"end"
															"Fix"
															"forall"
															"fun"
															"if"
;															"in"
															"into"
															"let"
;															"of"
															"then"
															"using"
;															"with"
															"after"))))

(defconst coq-comment-start-regexp "(\\(*\\)+")
(defconst coq-comment-end-regexp "\\(*\\)+)")

(defconst coq-indent-open-regexp
  (proof-regexp-alt ;(proof-ids-to-regexp coq-keywords-goal) goal-command-p instead
	(proof-ids-to-regexp '("Cases" "match"))
	"\\s("))

(defconst coq-indent-close-regexp
  (proof-regexp-alt (proof-ids-to-regexp coq-keywords-save) 
						  (proof-ids-to-regexp '("end" "End"))
						  "\\s)"))

(defconst coq-indent-closepar-regexp "\\s)")

(defconst coq-indent-closematch-regexp (proof-ids-to-regexp '("end")))

(defconst coq-indent-openpar-regexp "\\s(")

(defconst coq-indent-openmatch-regexp (proof-ids-to-regexp '("match" "Cases")))

(defconst coq-indent-any-regexp
  (proof-regexp-alt 
	coq-indent-close-regexp 
	coq-indent-open-regexp 
	coq-indent-inner-regexp
	coq-any-command-regexp 
	(proof-ids-to-regexp coq-tacticals)
	(proof-ids-to-regexp coq-tactics)))

(defconst coq-indent-kw 
  (proof-regexp-alt  
	coq-any-command-regexp coq-indent-inner-regexp
	(proof-ids-to-regexp coq-tacticals)
	(proof-ids-to-regexp coq-tactics)))

; pattern matching detection, will be tested only at beginning of a
;line (only white sapces before "|") must not match "|" followed by
;another symbol the following char must not be a symbol (tokens of coq
;are the biggest symbol cocateantions)

(defconst coq-indent-pattern-regexp "\\(|\\(?:\\s-\\|\\w\\|\n\\)\\|with\\)")

;;;; End of regexps

(defun coq-indent-goal-command-p (str)
  "Syntactical detection of a coq goal opening.  Only used in indentation code and in
v8.0 compatibility mode.  Module, Definition and Function needs a special parsing to
detect if they start something or not."
  (let* ((match (coq-count-match "\\<match\\>" str))
         (with (coq-count-match "\\<with\\>" str))
         (letwith (+ (coq-count-match "\\<let\\>" str) (- with match)))
         (affect (coq-count-match ":=" str)))
		  
    (and (proof-string-match coq-goal-command-regexp str)
         (not 
          (and (proof-string-match "\\`\\(Local\\|Definition\\|Lemma\\|Module\\)\\>" str)
               (not (= letwith affect))))
         (not (proof-string-match "\\`Declare\\s-+Module\\(\\w\\|\\s-\\|<\\)*:" str))
         (not 
          (and (proof-string-match "\\`\\(Function\\|GenFixpoint\\)\\>" str)
               (not (proof-string-match "{\\s-*\\(wf\\|measure\\)" str))))
         )))

;; ". " and "... " are command endings, ".. " is not, same as in
;; proof-script-command-end-regexp in coq.el
(defconst coq-end-command-regexp 
  "\\(?:[^.]\\|\\(?:\\.\\.\\)\\)\\(\\.\\)\\(?:\\s-\\|\\'\\)")

(defun coq-looking-at-syntactic-context ()
  (or (proof-looking-at-syntactic-context)
      (when (not (eq (point) (point-min)))
        (save-excursion 
          (forward-char -1)
          (when (proof-looking-at-safe proof-script-comment-start-regexp) 'comment)))))

(defun coq-find-command-end-backward ()
  "Moves to the first end of command found looking up.  The point is put exactly
before the last \".\" of the ending token.  If no end command is found, go as far as
possible and return nil."
  (forward-char 1); because regexp looks one char after last "."
  (when (proof-re-search-backward coq-end-command-regexp nil 'dummy)
    (goto-char (match-beginning 1))))

(defun coq-find-command-end-forward ()
  "Moves to the first end of command found looking down.  The point is put exactly
before the last \".\" of the ending token.  If no end command is found, go as far as
possible and return nil."
;  (if (string-match coq-end-command-regexp (buffer-substring (point) (point-max)))
  (when (proof-re-search-forward coq-end-command-regexp nil 'dummy)
    (goto-char (match-beginning 1))))


(defun coq-find-command-end (direction)
  "Moves to the first end of command found looking at direction.  The point is put
exactly before the last \".\" of the ending token.  If no end command is found, go as
far as possible and return nil."
  (if (< direction 0) (coq-find-command-end-backward)
    (coq-find-command-end-forward)))

(defun coq-find-current-start ()
  "Move to the start of command at point.
The point is put exactly after the end of previous command, or at the (point-min if
there is no previous command)."
  (coq-find-command-end-backward)
  (while (and (proof-looking-at-syntactic-context)
				  (> (point) (point-min)))
    (coq-find-command-end-backward))
  (if (proof-looking-at "\\.\\s-") (forward-char 1))
  (point))

(defun coq-find-real-start ()
  "Move to the start of command at point.
The point is put exactly before first non comment letter of the command."
  (coq-find-current-start)
  (proof-re-search-forward "\\w\\|\\s(\\|\\s)\\|\\'")
  (backward-char 1)
  (while (and (proof-looking-at-syntactic-context)
				  (<= (point) (- (point-max) 1)))
    (proof-re-search-forward "\\*\\s)");this does not deal with nested comments
    (proof-re-search-forward "\\w\\|\\s(\\|\\s)\\|\\'")
    (backward-char 1))
  (point))

(defun coq-command-at-point ()
  "Return the string of the command at point."
  (save-excursion
    (let ((st (coq-find-real-start)) ; va chercher trop loin?
          (nd (or (coq-find-command-end-forward) (- (point-max) 1)))) ; idem?
      (buffer-substring st (+ nd 1)))))

(defun is-at-a-space-or-tab ()
  "t si le caractere courant est un blanc ou un tab, nil sinon"
  (if (or (not (char-after)) (char-equal (char-after) ?\ ) (char-equal (char-after) ?\t ))
      t nil)
  )

(defun only-spaces-on-line ()
  "t if there is only spaces (or nothing) on the current line after point.
Moves point to first non space char if present, to the end of line otherwise."
  (skip-chars-forward " \t" (save-excursion (end-of-line) (point)))
  (eolp)      
  )

(defun find-reg (lim reg)
  "Return non nil if there is an occurrence of reg between point and lim which is not
a comment or a string.  Actually returns the position of the occurrence found.  Point
is moved at the end of the match if found, at LIM otherwise."
  (let ((oldpt (point)) (limit lim))
    (if (= limit (point)) nil
      ;;swap limit and point if necessary
;      (message "find-reg...")
      (when (< limit (point)) (let ((x limit)) (setq limit (point)) (goto-char x)))
      (let ((pos nil))
        (while 
            (and (not pos)
                 (setq pos (proof-string-match reg (buffer-substring (point) limit))))
;          (message "while body...")
          (forward-char (- (match-end 0) 1))          
          (when (save-excursion (forward-char -1)
                                (proof-looking-at-syntactic-context))
            (setq pos nil))
;          (message "while body... done")
          )
;        (message "find-reg... after while")
        (and pos (point))))))


(defun coq-find-no-syntactic-on-line ()
  (let ((bol (save-excursion (beginning-of-line) (point)))
        (eol (save-excursion (end-of-line) (point))))
    (beginning-of-line)
    (back-to-indentation)
    (while (and (or (coq-looking-at-syntactic-context)
                    (is-at-a-space-or-tab))
                    (not (eq (point) eol)))
      (forward-char 1))
    (not (eq (point) eol))))

(defun coq-find-no-syntactic-on-line ()
  (let ((bol (save-excursion (beginning-of-line) (point)))
        (eol (save-excursion (end-of-line) (point))))
    (back-to-indentation)
    (while (and (coq-looking-at-syntactic-context)
                (re-search-forward coq-comment-end-regexp eol 'dummy)))
    (not (eq (point) eol))))


;    (while (and (or (coq-looking-at-syntactic-context)
;                    (is-at-a-space-or-tab))
;                    (not (eq (point) eol)))
;      (forward-char 1))
;    (not (eq (point) eol))))


(defun coq-back-to-indentation-prevline ()
  "Moves point back to previous pertinent line for indentation. Move point to the first non white space character. Returns 0 if top of buffer was reached, 3 if inside a comment or string, 4 if inside the {} of a record, 1 if the line found is not in the same command as the point before the function was called, 2 otherwise (point and previous line are in the same command, and not inside the {} of a record)."
  (if (proof-looking-at-syntactic-context) 3
    (let ((oldpt (point))
          (topnotreached (= (forward-line -1) 0))) ;;; nil if going one line backward
                                                   ;;; is not possible
      
      (while (and topnotreached
                  (not (coq-find-no-syntactic-on-line))
                  t ;;(> (line-number (point)) (line-number (point-min)))
                  )
        (setq topnotreached (= (forward-line -1) 0)))
      (back-to-indentation)
;      (message "coq-back-to-indentation-prevline... after while")
      (if (not topnotreached) 0 ;; returns nil if top of buffer was reached
        ;; if we are at end of a command (dot) find this command
        (if (find-reg oldpt coq-end-command-regexp) 
            (progn (forward-char -2)
;                   (message "coq-back-to-indentation-prevline... coq-find-real-start")
                   (coq-find-real-start)
;                   (message "coq-back-to-indentation-prevline... coq-find-real-start2")
                   1)
          (if (save-excursion 
;                (message "coq-back-to-indentation-prevline... if 3")
                (and (or (forward-char -1) t)
                     (coq-find-real-start)
                     (proof-looking-at-safe "Record")
                     (find-reg oldpt "{"))) 
              4 
            2))))))


(defun coq-find-unclosed (&optional optlvl limit openreg closereg)
  "finds the first unclosed open item (backward), counter starts to optlvl (default 1) and stops when reaching limit (default point-min)"
  
  (let* ((lvl (or optlvl 1))
			(open-re  (if openreg (proof-regexp-alt openreg proof-indent-open-regexp) 
							proof-indent-open-regexp))
			(close-re (if closereg (proof-regexp-alt closereg proof-indent-close-regexp) 
							proof-indent-close-regexp))
			(both-re (proof-regexp-alt "\\`" close-re open-re))
			(nextpt (save-excursion (proof-re-search-backward both-re))))
    (while 
        (and (not (= lvl 0))
             (>= nextpt (or limit (point-min)))
             (not (= nextpt (point-min))))
      (goto-char nextpt)
      (cond
       ((proof-looking-at-syntactic-context) ())
		 ((proof-looking-at-safe proof-indent-close-regexp) 
		  (coq-find-unclosed 1 limit)) ;; recursive call
       ((proof-looking-at-safe close-re) (setq lvl (+ lvl 1)))
       ((proof-looking-at-safe open-re) (setq lvl (- lvl 1))))
      (setq nextpt (save-excursion (proof-re-search-backward both-re))))
    (if (= lvl 0) t 
		(goto-char (or limit (point-min)))
      nil)))


(defun coq-find-at-same-level-zero (limit openreg)
  "Moves to first open or openreg (first found) that is at same parethesis level than point. Returns the point if found."
  (let* ((found nil)
			(open-re (if openreg (proof-regexp-alt openreg proof-indent-open-regexp) 
						  proof-indent-open-regexp))
			(close-re proof-indent-close-regexp)
			(both-re (proof-regexp-alt "\\`" close-re open-re))
			(nextpt (save-excursion (proof-re-search-backward both-re))))  

	 (while 
        (and (not found)
             (>= nextpt (or limit (point-min)))
             (not (= nextpt (point-min))))
		(goto-char nextpt)
		(cond 
		 ((proof-looking-at-syntactic-context) ())
       ((proof-looking-at-safe openreg) (setq found t))
       ((proof-looking-at-safe proof-indent-open-regexp) (setq found t));assert false?
;       ((proof-looking-at-safe closereg) (coq-find-unclosed 1 limit))
       ((proof-looking-at-safe proof-indent-close-regexp) 
		  (coq-find-unclosed 1 limit)))
		(setq nextpt (save-excursion (proof-re-search-backward both-re)))
		)
	 (if found (point) nil)
	 )
  )


(defun coq-find-unopened (&optional optlvl limit)
  "Finds the last unopened close item (looking forward from point), counter starts to optlvl (default 1) and stops when reaching limit (default point-max). This function only works inside an expression."
  
  (let ((lvl (or optlvl 1)) after nextpt endpt)
	 (save-excursion 
		(proof-re-search-forward
		 (proof-regexp-alt "\\'"
								 proof-indent-close-regexp 
								 proof-indent-open-regexp))
		(setq after (point))
		(goto-char (match-beginning 0))
		(setq nextpt (point)))
    (while 
        (and (not (= lvl 0))
             (<= nextpt (or limit (point-max)))
             (not (= nextpt (point-max))))
      (goto-char nextpt)
		(setq endpt (point))
      (cond
       ((proof-looking-at-syntactic-context) ())
       
       ((proof-looking-at-safe proof-indent-close-regexp) 
        (setq lvl (- lvl 1)))
       
       ((proof-looking-at-safe proof-indent-open-regexp) 
        (setq lvl (+ lvl 1)))
       
       )
		(goto-char after)
      (save-excursion
		  (proof-re-search-forward
			(proof-regexp-alt "\\'"
									proof-indent-close-regexp 
									proof-indent-open-regexp))
		  (setq after (point))
		  (goto-char (match-beginning 0))
		  (setq nextpt (point)))
      )
    (if (= lvl 0)
		  (goto-char endpt)
      (goto-char (or limit (point-max)))
      nil)
    )
  )


(defun coq-find-last-unopened (&optional optlvl limit)
  "Backward moves to and returns the point of the last close item that is not opened after limit."
  (let ((last nil))
	 (while (coq-find-unopened optlvl limit)
		(setq last (point))
		(forward-char 1)); shift one to the right, 
                       ; that way the current match won'tbe matched again
	 (if last (goto-char last))
	 last
	 )
  )


(defun coq-end-offset (&optional limit)
  "Find the first unclosed open indent item, and returns its column. Stop when reaching limit (defaults tp point-min)"
  (save-excursion
    (let ((found nil) 
          (anyreg (proof-regexp-alt "\\`" proof-indent-any-regexp)))
      (while 
          (and (not found)
               (> (point) (or limit (point-min))))
        (proof-re-search-backward anyreg)
        (cond
         ((proof-looking-at-syntactic-context) ())
       
         ((proof-looking-at-safe proof-indent-close-regexp) 
          (coq-find-unclosed))
       
         ((proof-looking-at-safe proof-indent-open-regexp)
          (setq found t))
       
         (t ())
         )
        )
      (if found (current-column)
        -1000)                          ; no unclosed found
      )
    )
  )


(defun coq-indent-command-offset (kind prevcol prevpoint)
  "Returns the indentation offset of the current line. This function indents a *command* line (the first line of a command). Use `coq-indent-expr-offset' to indent a line belonging to an expression."
  (cond

   ((proof-looking-at-safe "\\<Proof\\>") 0);; no indentation at "Proof ..."

   ;; we are at an end command -> one ident left
   ;; FIX: we should count the number of closing item on the line
   ((coq-save-command-p (or (coq-command-at-point) "")) 
    (- proof-indent))


   ;; previous command is a goal command -> one indent right
   ;; carreful: this line moves the point
   ((and (goto-char prevpoint)
         (or (and;;"Proof ..." is a proof start (but not really a goal command)
              ;;  unless followed by a term (catch by coq-save-command-p above
              (proof-looking-at-safe "\\<Proof\\>")
              (not (coq-save-command-p (coq-command-at-point))))
             (coq-indent-goal-command-p (coq-command-at-point))
             ))
    proof-indent)

;;	((and (goto-char prevpoint) 
;;         ;"Proof <term>." is actually a Save command
;;         ; catched only if not follwed by"." or "with"
;;			(proof-looking-at-safe "\\<Proof\\>"))
;;	 (- proof-indent))


   ;; otherwise -> same indent as previous command
   (t 0)
   )
  )



;; This function is very complex, indentation of a line (inside an
;; expression) is determined by the beginning of this line (current
;; point) and the indentation items found at previous pertinent (not
;; comment, not string, not empty) line. Sometimes we even need the
;; previous line of previous line.

;; prevcol is the indentation column of the previous line, prevpoint
;; is the indentation point of previous line, record tells if we are
;; inside the accolades of a record.

(defun coq-indent-expr-offset (kind prevcol prevpoint record)
  "Returns the indentation column of the current line.
This function indents a *expression* line (a line inside of a command).  Use
`coq-indent-command-offset' to indent a line belonging to a command.  The fourth
argument must be t if inside the {}s of a record, nil otherwise."

  (let ((pt (point)) real-start)
	 (save-excursion 
		(setq real-start (coq-find-real-start)))
  
	 (cond

  ; at a ) -> same indent as the *line* of corresponding (
	  ((proof-looking-at-safe coq-indent-closepar-regexp)
		(save-excursion (coq-find-unclosed 1 real-start)
							 (back-to-indentation)
							 (current-column)))

  ; at a end -> same indent as the corresponding match or Case
	  ((proof-looking-at-safe coq-indent-closematch-regexp)
     (save-excursion (coq-find-unclosed 1 real-start)
                     (current-column)))

  ; if we find a "|" we indent from the first unclosed 
  ; or from the command start (if we are in an Inductive type)
	  ((proof-looking-at-safe coq-indent-pattern-regexp) 
     (save-excursion 
       (coq-find-unclosed 1 real-start)
       (cond 
        ((proof-looking-at-safe "\\s(")
         (+ (current-indentation) proof-indent))
        ((proof-looking-at-safe (proof-ids-to-regexp coq-keywords-defn))
         (current-column))
         (t (+ (current-column) proof-indent)))))

  ; if we find a "then" we indent from the first unclosed if
  ; or from the command start (should not happen)
	  ((proof-looking-at-safe "\\<then\\>") 
		(save-excursion
		  (coq-find-unclosed 1 real-start "\\<if\\>" "\\<then\\>")
		  (back-to-indentation)
		  (+ (current-column) proof-indent)))

  ; if we find a "else" we indent from the first unclosed if
  ; or from the command start (should not happen)
	  ((proof-looking-at-safe "\\<else\\>") 
		(save-excursion
		  (coq-find-unclosed 1 real-start "\\<then\\>" "\\<else\\>")
		  (coq-find-unclosed 1 real-start "\\<if\\>" "\\<then\\>")
		  (back-to-indentation)
		  (+ (current-column) proof-indent)))

  ; there is an unclosed open in the previous line 
  ; -> same column if match
  ; -> same indent than prev line + indent if (
	  ((coq-find-unclosed 1 prevpoint
								 coq-indent-openmatch-regexp 
								 coq-indent-closematch-regexp)
		(let ((base (if (proof-looking-at-safe coq-indent-openmatch-regexp)
							 (current-column)
						  prevcol)))
		  (+ base proof-indent)))


; there is an unclosed '(' in the previous line -> prev line indent + indent
;	  ((and (goto-char pt) nil)) ; just for side effect: jump to initial point
;	  ((coq-find-unclosed 1 prevpoint 
;								 coq-indent-openpar-regexp 
;								 coq-indent-closepar-regexp)
;		(+ prevcol proof-indent))

	  ((and (goto-char prevpoint) nil)) ; just for side effect: jump to previous line
	
; find the last unopened ) -> indentation of line + indent
	  ((coq-find-last-unopened 1 pt) ; side effect, nil if no unopenned found
		(save-excursion
		  (coq-find-unclosed 1 real-start)
		  (back-to-indentation)
		  (current-column)))

; just for side effect: jumps to end of previous line
	  ((and (goto-char prevpoint) 
			  (or (and (end-of-line) nil) 
					(and (forward-char -1) t)) nil))

	  ((and  (proof-looking-at-safe ";") ;prev line has ";" at the end 
				record)                     ; and we are inside {}s of a record
		(save-excursion (coq-find-unclosed 1 real-start)
							 (back-to-indentation)
							 (+ (current-column) proof-indent)))

; just for side effect: jumps to end of previous line
	  ((and (goto-char prevpoint)  (not (= (coq-back-to-indentation-prevline) 0))
			  (or (and (end-of-line) nil) 
					(and (forward-char -1) t)) nil))

	  ((and  (proof-looking-at-safe ";") ;prev prev line has ";" at the end 
				record)                     ; and we are inside {}s of a record
		(save-excursion (+ prevcol proof-indent)))


	  ((and (goto-char pt) nil)) ; just for side effect: go back to initial point

; There is a indent keyword (fun, forall etc) 
; and we are not in {}s of a record just after a ";"
	  ((coq-find-at-same-level-zero prevpoint coq-indent-kw) (+ prevcol proof-indent))

	  ((and (goto-char prevpoint) nil)) ; just for side effect: go back to previous line

; "|" at previous line
	  ((proof-looking-at-safe coq-indent-pattern-regexp) (+ prevcol proof-indent))

	  (t prevcol)
	  )
	 )
  )



(defun coq-indent-comment-offset ()
  (save-excursion
    (back-to-indentation)
    (let ((oldpt (point))
          ;; atstart is true if the line to indent starts with a comment start
          (atstart (proof-looking-at coq-comment-start-regexp)))
      ;; go back looking for a non empty line
      (if (/= (forward-line -1) 0) 0 ; we are at beginning of buffer
        ;; only-space on a non empty line moves the point to first non space char
        (while (and (only-spaces-on-line) (= (forward-line -1) 0)) ())
        ;; now we found the previous non empty line
        (let ((eol (save-excursion (end-of-line) (point))))
        (cond
         ;; The previous line is a comment start
         ((and (not atstart) (string-match coq-comment-start-regexp 
                                           (buffer-substring (point) eol)))
          (message "indenting... point = %s" (point))
          (proof-re-search-forward coq-comment-start-regexp) 
          (+ 1 (current-column)))

         ((and (not atstart) (proof-looking-at-syntactic-context))
          (message "coq-indent-comment-offset \\S-")
          (proof-re-search-forward "\\S-")
          (goto-char (match-beginning 0))
          (current-column))
         
            ;;we were at the first line of a comment and the current line is the
            ;;previous one
         (t (goto-char oldpt)
            (coq-find-command-end-backward)
            (coq-find-real-start)
            (current-column))))))))


(defun coq-indent-offset (&optional notcomments)
  (let (kind prevcol prevpoint)
	 (save-excursion
		(setq kind (coq-back-to-indentation-prevline) ;go to previous *command* (assert)
				prevcol (current-column)
				prevpoint (point)))
;   (message "coq-indent-offset... kind = %s ; prevcol = %s; prevpoint = %s" kind prevcol prevpoint)
	 (cond 
	  ((= kind 0) 0) ; top of the buffer reached
	  ((= kind 1) ; we are at the command level
     (+ prevcol (coq-indent-command-offset kind prevcol prevpoint)))
	  ((= kind 2) ; we are at the expression level
     (coq-indent-expr-offset kind prevcol prevpoint nil))
	  ((= kind 4) ; we are at the expression level inside {}s of a record
     (coq-indent-expr-offset kind prevcol prevpoint t))
	  ((= kind 3) (if notcomments nil (coq-indent-comment-offset))))))

(defun coq-indent-calculate (&optional notcomments) 
  (coq-indent-offset notcomments)

;  (let ((oldpt (point)) (prvfound nil) (res 0))
;    (setq res
;          (+ (save-excursion 
;               (setq prvfound (coq-back-to-indentation-prevline))
;               (current-column)) ; indentation of previous pertinent line
;             (coq-indent-offset))) ; + offset for the current line
;    (if (= prvfound 0) 0 res) ; if we are at buffer top, then 0 else res
;    )
  )


(defun proof-indent-line ()
  "Indent current line of proof script, if indentation enabled."
  (interactive)
  (unless (not (proof-ass script-indent))
    (save-excursion
      (let ((ind (save-excursion (back-to-indentation) (coq-indent-calculate))))
        (indent-line-to (max 0 ind))))
    (if (< (current-column) (current-indentation))
        (back-to-indentation)))
  (if proof-indent-pad-eol (proof-indent-pad-eol)))

(defun proof-indent-line-not-comments ()
  "Same as  `proof-indent-line' but comments are not indented."
  (interactive)
  (unless (not (proof-ass script-indent))
    (save-excursion
      (let ((ind (save-excursion (back-to-indentation) (coq-indent-calculate t))))
        (when ind (indent-line-to (max 0 ind)))))
    (if (< (current-column) (current-indentation))
        (back-to-indentation)))
  (if proof-indent-pad-eol (proof-indent-pad-eol)))

(defun coq-indent-region (start end)
  (let ((deb (min start end)) (fin (max start end)))
    (goto-char end)
    (setq fin (point-marker)) ; to go back there even if shifted
    (goto-char deb)
    (while (< (point) fin)
      (or (and (bolp) (eolp))
          (proof-indent-line-not-comments))
      (forward-line 1))
    (goto-char fin)))

(setq indent-region-function 'coq-indent-region)

(provide 'coq-indent)

;;;   Local Variables: ***
;;;   tab-width:2 ***
;;;   fill-column: 85 ***
;;;   indent-tabs-mode:nil ***
;;;   End: ***

