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

(defconst coq-indent-pattern-regexp "|\\(?:\\s-\\|\\w\\|\n\\)")

;;;; End of regexps


(defun coq-find-command-start ()
  (proof-re-search-backward "\\.\\B\\|\\`")
  (while (and (proof-looking-at-syntactic-context)
				  (> (point) (point-min)))
    (proof-re-search-backward "\\.\\B\\|\\`"))
  (if (proof-looking-at "\\.\\B") (forward-char 1))
  (point)
  )

(defun coq-find-real-start ()
  (coq-find-command-start)
  (proof-re-search-forward "\\w\\|\\s(\\|\\s)\\|\\'")
  (backward-char 1)
  (while (and (proof-looking-at-syntactic-context)
				  (<= (point) (- (point-max) 1)))
    (proof-re-search-forward "\\*\\s)");this does not deal with nested comments
    (proof-re-search-forward "\\w\\|\\s(\\|\\s)\\|\\'")
    (backward-char 1))
  (point)
  )

(defun coq-find-end ()
  (proof-re-search-forward "\\.\\B\\|\\'")
  (while (and (proof-looking-at-syntactic-context)
				  (<= (point) (point-max)))
    (proof-re-search-forward "\\*\\s)")
    (proof-re-search-forward "\\.\\B\\|\\'"))
;  (backward-char 1)
  (point)
  )

(defun coq-current-command-string ()
  (save-excursion
    (let ((st (coq-find-real-start)) ; va chercher trop loin?
          (nd (coq-find-end))) ; idem?
      (buffer-substring st nd))
    )
  )

(defun is-at-a-space-or-tab ()
  "t si le caractere courant est un blanc ou un tab, nil sinon"
  (if (or (not (char-after)) (char-equal (char-after) ?\ ) (char-equal (char-after) ?\t ))
      t nil)
  )

(defun only-spaces-on-line ()
  "t if there is only spaces (or nothing) on the current line after point"
  (while (and (char-after) (is-at-a-space-or-tab))
    (forward-char 1))
  (if (or (not (char-after)) (char-equal (char-after) ?\n)) t nil)
)

(defun find-reg (lim reg)
  (let ((limit lim))
	 (if (< limit (point)) ;swap limit and point
		  (let ((x limit)) (setq limit (point)) (goto-char x)))
	 (let ((pos nil))
		(while 
			 (and (not pos)
					(setq pos (proof-string-match reg (buffer-substring (point) limit))))
		  (forward-char pos)
		  (if (proof-looking-at-syntactic-context) (setq pos nil)))
		pos)
	 )
  )

(defun coq-back-to-indentation-prevline ()
  "Moves point back to previous pertinent line for indentation. Move point to the first non white space character. Returns 0 if top of buffer was reached, 3 if inside a comment or string, 4 if inside the {} of a record, 1 if the line found is not in the same command as the point before the function was called, 2 otherwise (point and previous line are in the same command, and not inside the {} of a record)."

  (if (proof-looking-at-syntactic-context) 3
	 (let ((oldpt (point))
			 (topnotreached (= (forward-line -1) 0))) ; nil if going one line backward
													 ; is not possible
		(while (and topnotreached
						(or (only-spaces-on-line) (proof-looking-at-syntactic-context))
						t ;(> (line-number (point)) (line-number (point-min)))
						)
		  (setq topnotreached (= (forward-line -1) 0)))
		(back-to-indentation)
		(if (not topnotreached) 0 ; returns nil if top of buffer was reached
		  (if (find-reg oldpt "\\.\\B");; if we are at end of a command (dot) find this command
				(progn (coq-find-real-start) 1)
			 (if (save-excursion 
					 (coq-find-real-start) 
					 (proof-looking-at-safe "Record")
					 (find-reg oldpt "{")) 
				  4 
				2))
		  
		  )
		)
	 )
  )


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

  ; we are at an end command -> one ident left
  ; FIX: we should count the number of closing item on the line
	((coq-save-command-p nil (coq-current-command-string)) 
	 (- proof-indent))

	((proof-looking-at-safe "\\<Proof\\>") 0) ; no indentation at "Proof ..."

  ; previous command is a goal command -> one indent right
  ; carreful: this line moves the point
	((and (goto-char prevpoint) 
			(or (and ;"Proof ..." is a proof start (but not really a goal command)
                  ;  unless followed by a term (catch by coq-save-command-p above
				  (proof-looking-at-safe "\\<Proof\\>")
				  (not (coq-save-command-p nil (coq-current-command-string))))
				 (coq-goal-command-p (coq-current-command-string))))
	 proof-indent)

;	((and (goto-char prevpoint) 
;         ;"Proof <term>." is actually a Save command
;         ; catched only if not follwed by"." or "with"
;			(proof-looking-at-safe "\\<Proof\\>"))
;	 (- proof-indent))


  ; otherwise -> same indent as previous command
	(t 0)
	)
  )



;; This function is very complex, indentation of a line (inside an
;; expression) is determined by the beginning of this line (current
;; point) and the indentation items found at previous pertinent (not
;; comment, not string, not empty) line. Sometimes we even need the
;; previous line of previous line.

;; prevcol is the indentation column of the previous line, prevpoint
;; is the indetation point of previous line, record tells if we are
;; inside a the accolades of a record.

(defun coq-indent-expr-offset (kind prevcol prevpoint record)
  "Returns the indentation column of the current line. This function indents a *expression* line (a line inside of a command). Use `coq-indent-command-offset' to indent a line belonging to a command. The fourth argument must be t if inside the {}s of a record, nil otherwise."

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
		(save-excursion (coq-find-unclosed 1 real-start)
							 (if (proof-looking-at-safe "\\s(")
								  (+ (current-indentation) proof-indent)
								  (+ (current-column) proof-indent))))

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



(defun coq-indent-offset ()
  (let (kind prevcol prevpoint)
	 (save-excursion
		(setq kind (coq-back-to-indentation-prevline) ;go to previous *command* (assert)
				prevcol (current-column)
				prevpoint (point)))
	 (cond 
	  ((= kind 0) 0) ; top of the buffer reached
	  ((= kind 1) ; we are at the command level
		(+ prevcol (coq-indent-command-offset kind prevcol prevpoint)))
	  ((= kind 2) ; we are at the expression level
		(coq-indent-expr-offset kind prevcol prevpoint nil))
	  ((= kind 4) ; we are at the expression level inside {}s of a record
		(coq-indent-expr-offset kind prevcol prevpoint t))
	  ((= kind 3) (+ (current-column) 2))
	  )
		
	 )
  )

(defun coq-indent-calculate () 
  (coq-indent-offset)

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
    (if (< (point) (proof-locked-end))
        (if (< (current-column) (current-indentation))
            (skip-chars-forward "\t "))
      (save-excursion
        (indent-line-to
         (max 
          0 
          (save-excursion
            (back-to-indentation)
            (coq-indent-calculate)))))
      (if (< (current-column) (current-indentation))
          (back-to-indentation))))
  (if proof-indent-pad-eol (proof-indent-pad-eol)))


(provide 'coq-indent)

;;;   Local Variables: ***
;;;   tab-width:2 ***
;;;   fill-column: 85 ***
;;;   indent-tabs-mode:nil ***
;;;   End: ***

