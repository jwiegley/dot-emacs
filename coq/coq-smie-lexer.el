;; Lexer.
;; - We distinguish ":=" from ":= inductive" to avoid the circular precedence
;;   constraint ":= < | < ; < :=" where ":= < |" is due to Inductive
;;   definitions, "| < ;" is due to tactics precedence, "; < :=" is due to
;;   "let x:=3; y:=4 in...".
;; - We distinguish the ".-selector" from the terminator "." for
;;   obvious reasons.
;; - We consider qualified.names as one single token for obvious reasons.
;; - We distinguish the "Module M." from "Module M := exp." since the first
;;   opens a new scope (closed by End) whereas the other doesn't.
;; - We drop "Program" because it's easier to consider "Program Function"
;;   as a single token (which behaves like "Function" w.r.t indentation and
;;   parsing) than to get the parser to handle it correctly.
;; - We identify the different types of bullets (First approximation).
;; - We distinguish "with match" from other "with".

(setq coq-smie-dot-friends '("*." "-*." "|-*." "*|-*."))

; for debuging
(defun coq-time-indent ()
  (interactive)
  (let ((deb (time-to-seconds)))
    (smie-indent-line)
    (message "time: %S"(- (time-to-seconds) deb))))




(defun coq-smie-is-tactic ()
  (save-excursion
    (coq-find-real-start)
    (let ((cfs case-fold-search))
      (setq case-fold-search nil)
      (let ((res (looking-at "[[:upper:]]")))
	(setq case-fold-search cfs)
	(not res)))))


(defun coq-smie-search-token-forward (tokens &optional end ignore-between)
  "Search for one of TOKENS between point and END.
Token \".\" is considered only if followed by a space."
  (unless end (setq end (point-max)))
  (condition-case nil
      (catch 'found
	(while (< (point) end)
	  ;; The default lexer is faster and is good enough for our needs.
	  (let* ((next (smie-default-forward-token))
		 (parop (assoc next ignore-between)))
	    (if parop ; if we find something to ignore, we directly
		(let ((parops ; corresponding matcher may be a list
		       (if (listp parop) (cdr parop)
			 (cons (cdr parop) nil)))) ; go to corresponding closer
		      (coq-smie-search-token-forward parops
						     end ignore-between))
	      ;; Do not consider "." when not followed by a space
	      (when (or (not (equal next "."))
			(looking-at "[[:space:]]"))
		(cond
		 ((zerop (length next)) (forward-sexp 1))
		 ((member next tokens) (throw 'found next))))))))
    (scan-error nil)))

(defun coq-smie-search-token-backward (tokens &optional end ignore-between)
  "Search for one of TOKENS between point and END.
Token \".\" is considered only if followed by a space. optional
IGNORE-BETWEEN defines opener/closer to ignore during search.
Careful: the search for a opener stays inside the current
command. "
  (unless end (setq end (point-min)))
    (condition-case nil
	(catch 'found
	  (while (> (point) end)
	    ;; The default lexer is faster and is good enough for our needs.
	    (let* ((next2 (smie-default-backward-token))
		   (next (if (member next2 coq-smie-dot-friends) "." next2))
		   (parop (rassoc next ignore-between)))
	      ;(message "praop = %S" parop)
	      (if parop ; if we find something to ignore, we directly
		  (let ((p (point))
			(parops ; corresponding matcher may be a list
			 (if (listp (car parop)) (car parop) (cons (car parop) nil))))
		    ; go to corresponding closer or meet "."
		    ;(message "newpatterns = %S" (append parops (cons "." nil)))
		    (when (member
			   (coq-smie-search-token-backward
			    (append parops (cons "." nil)) ;coq-smie-dot-friends
			    end ignore-between)
			   (cons "." nil)) ;coq-smie-dot-friends
		      (goto-char (point))
		      next))
		;; Do not consider "." when not followed by a space
		(when (or (not (equal next "."))
			  (looking-at ".[[:space:]]"))
		  (cond
		   ((zerop (length next)) (forward-sexp -1))
		   ((member next tokens) (throw 'found next))))))))
      (scan-error nil)))

;; This avoids parenthesized expression containing := and let
;; .. := ... in. We consider any other occurrence of := as an
;; evidence of explicit definition by contrast to goal
;; opening.
(defun coq-lonely-:=-in-this-command ()
  "Return t if there is a lonely \":=\" from (point) to end of command.
Non lonely \":=\" are those corresponding to \"let\" or
\"with\" (module declaration) or those inside parenthesis. this
function is used to detect whether a command is a definition or a
proof-mode starter in Coq."
  (equal (coq-smie-search-token-forward
	  '("." ":=") nil
	  '(("with" . (":=" "signature")) ("let" . "in")))
	 "."))

;; Heuristic to detect a goal opening command: there must be a lonely
;; ":=" until command end.
;; \\|\\(Declare\\s-+\\)?Instance is not detected as it is not
;; syntactically decidable to know if some goals are created. Same for
;; Program Fixpoint but with Program Next Obligation is mandatory for
;; each goal.
(defun coq-smie-detect-goal-command ()
  "Return t if the next command is a goal starting to be indented.
The point should be at the beginning of the command name. As
false positive are more annoying than false negative, return t
only if it is FOR SURE a goal opener. Put a \"Proof.\" when you want to
force indentation."
  (save-excursion ; FIXME add other commands that potentialy open goals
    (when (proof-looking-at "\\(Local\\|Global\\)?\
\\(Definition\\|Lemma\\|Theorem\\|Fact\\|Let\\|Class\
\\|Add\\(\\s-+Parametric\\)?\\s-+Morphism\\)\\>")
	(coq-lonely-:=-in-this-command)
	)))

;; Heuristic to detect a goal opening command: there must be a lonely ":="
(defun coq-smie-detect-module-or-section-start-command ()
  "Return t if the next command is a goal starting command.
The point should be at the beginning of the command name."
  (save-excursion ; FIXME Is there other module starting commands?
    (when (proof-looking-at "\\(Module\\|Section\\)\\>")
      (coq-lonely-:=-in-this-command))))


(defconst coq-smie-proof-end-tokens
  ;; '("Qed" "Save" "Defined" "Admitted" "Abort")
  (cons "EndSubproof" (remove "End" coq-keywords-save-strict)))

(defun coq-smie-forward-token ()
  (let ((tok (smie-default-forward-token)))
    (cond
     ;; @ may be  ahead of an id, it is part of the id.
     ((and (equal tok "@") (looking-at "[[:alpha:]_]"))
      (let ((newtok (coq-smie-forward-token))) ;; recursive call
	(concat tok newtok)))
     ;; detecting if some qualification (dot notation) follows that id and
     ;; extend it if yes. Does not capture other alphanumerical token (captured
     ;; below)
     ((and (string-match "@?[[:alpha:]_][[:word:]]*" tok)
	   (looking-at "\\.[[:alpha:]_]")
	   (progn (forward-char 1)
		  (let ((newtok (coq-smie-forward-token))) ; recursive call
		    (concat tok "." newtok)))))
     ((member tok '("." "..."))
      ;; swallow if qualid, call backward-token otherwise
      (cond
       ((member (char-after) '(?w ?_))  ;(looking-at "[[:alpha:]_]") ;; extend qualifier
	(let ((newtok (coq-smie-forward-token))) ;; recursive call
	  (concat tok newtok)))
       (t (save-excursion (coq-smie-backward-token))))) ;; recursive call
     ((member tok
	      '("=>" ":=" "+" "-" "*" "exists" "in" "as" "∀" "∃" "→" ";" "," ":"))
      ;; The important lexer for indentation's performance is the backward
      ;; lexer, so for the forward lexer we delegate to the backward one when
      ;; we can.
      (save-excursion (coq-smie-backward-token)))

     ;; detect "with signature", otherwies use coq-smie-backward-token
     ((equal tok "with")
      (let ((p (point)))
	(if (equal (smie-default-forward-token) "signature")
	    "with signature"
	  (goto-char p)
	  (save-excursion (coq-smie-backward-token)))))

     ((member tok '("transitivity" "symmetry" "reflexivity"))
      (let ((p (point)))
	(if (and (equal (smie-default-forward-token) "proved")
		 (equal (smie-default-forward-token) "by"))
	    "xxx provedby"
	  (goto-char p)
	  tok))) ; by tactical


    ;;  ((equal tok "Program")
    ;;   (let ((pos (point))
    ;;    (next (smie-default-forward-token)))
    ;;  (if (member next '("Fixpoint" "Declaration" "Lemma" "Instance"))
    ;;      next
    ;;    (goto-char pos)
    ;;    tok)))
    ;;  ((member tok  '("Definition" "Lemma" "Theorem" "Local"
    ;;		     "Fact"  "Let" "Program"
    ;;		     "Class" "Instance"))
    ;;   (save-excursion (coq-smie-backward-token)))

     ((member tok '("Module"))
      (let ((pos (point))
	    (next (smie-default-forward-token)))
	(unless (equal next "Type") (goto-char pos))
	(save-excursion (coq-smie-backward-token))))

     ((and (zerop (length tok)) (looking-at "{|")) (goto-char (match-end 0)) "{|")
     ;; this must be after detecting "{|":
     ((and (zerop (length tok)) (looking-at "{"))
      (if (equal (save-excursion (forward-char 1) (coq-smie-backward-token))
		 "{ subproof")
	  (progn (forward-char 1) "{ subproof")
	tok))
     ((and (zerop (length tok)) (looking-at "}"))
      (if (equal (save-excursion (forward-char 1)
				 (coq-smie-backward-token))
		 "} subproof")
	  (progn (forward-char 1) "} subproof")
	tok))
    ;;  ((and (equal tok "|") (eq (char-after) ?\}))
    ;;   (goto-char (1+ (point))) "|}")
     ((member tok coq-smie-proof-end-tokens) "Proof End")
     ((member tok '("Obligation")) "Proof")
    ;; ((equal tok "Proof") ;; put point after with if present
    ;;   (let ((pos (point))
    ;;	    (next (smie-default-forward-token)))
    ;;	(if (equal next "with")
    ;;	    "Proof"
    ;;	  (goto-char pos)
    ;;	  tok)))
    ;;  ((equal tok "Next")
    ;;   (let ((pos (point))
    ;;	    (next (smie-default-forward-token)))
    ;;	(if (equal next "Obligation")
    ;;	    next
    ;;	  (goto-char pos)
    ;;	  tok)))



;
;     ((string-match "[[:alpha:]_]+" tok)
;      (save-excursion
;	(if (equal (coq-smie-backward-token) " upperkw")
;	    " upperkw" tok)))
;

     (tok))))

(defun coq-smie-.-desambiguate ()
  "Return the token of the command terminator of the current command."
  (save-excursion
    (let ((p (point)) (beg (coq-find-real-start))) ; moves to real start of command
      (cond
       ((looking-at "Proof\\>\\|BeginSubproof\\>") ". proofstart")
       ((or (looking-at "Next\\s-+Obligation\\>")
	    (coq-smie-detect-goal-command))
	(save-excursion
	  (goto-char (+ p 1))
	  (if (equal (smie-default-forward-token) "Proof")
	      "." ". proofstart")))
       ((coq-smie-detect-module-or-section-start-command)
	". modulestart")
       (t "."))))
  )


(defun coq-smie-complete-qualid-backward ()
  "Return the qualid finishing at the current point."
  (let ((p (point)))
    (re-search-backward "[^.[:alnum:]_@]")
    (forward-char 1)
    (buffer-substring (point) p)))

(defun coq-smie-backward-token ()
  (let ((tok (smie-default-backward-token)))
    (cond
     ((equal tok ",")
      (save-excursion
	(let ((backtok (coq-smie-search-token-backward
			'("forall" "∀" "∃" "exists" "|" "match" "."))))
	  (cond
	   ((member backtok '("forall" "∀" "∃")) ", quantif")
	   ((equal backtok "exists") ; there is a tactic called exists
	    (if (equal (coq-smie-forward-token) ;; recursive call
		       "quantif exists")
		", quantif" tok))
	   (t tok)))))
     ;; Distinguish between "," from quantification and other uses of
     ;; "," (tuples, tactic arguments)

     ((equal tok ";")
      (save-excursion
	(let ((backtok (coq-smie-search-token-backward '("." "[" "{"))))
	  (cond
	   ((equal backtok ".") "; tactic")
	   ((equal backtok nil)
	    (if (or (looking-back "\\[")
		    (and (looking-back "{")
			 (equal (coq-smie-backward-token) "{ subproof"))) ;; recursive call
		"; tactic"
	      "; record"))))))

    ;;  ((equal tok "Type")
    ;;   (let ((pos (point))
    ;;	    (prev (smie-default-backward-token)))
    ;;	(if (equal prev "Module")
    ;;	    prev
    ;;	  (goto-char pos)
    ;;	  tok)))
     ((equal tok "Module")
      (save-excursion
	(coq-find-real-start)
	(if (coq-smie-detect-module-or-section-start-command)
	    "Module start" "Module def")))
     ((and (equal tok "|") (eq (char-before) ?\{))
      (goto-char (1- (point))) "{|")
    ;;  ;; FIXME: bugs when { } { } happens for some other reason
    ;;  ;; FIXME: it seems to even loop sometime
    ;;  ;; ((and (equal tok "") (member (char-before) '(?\{ ?\}))
    ;;  ;;       (save-excursion
    ;;  ;;         (forward-char -1)
    ;;  ;;         (let ((prev (smie-default-backward-token)))
    ;;  ;;         (or (and (equal prev ".") (looking-at "\\."))
    ;;  ;;             (and (equal prev "") (member (char-before) '(?\{ ?\})))))))
    ;;  ;;  (forward-char -1)
    ;;  ;;  (if (looking-at "{") "BeginSubproof" "EndSubproof"))
    ;;  ((and (equal tok "") (looking-back "|}" (- (point) 2)))
    ;;   (goto-char (match-beginning 0)) "|}")

     ((and (zerop (length tok)) (member (char-before) '(?\{ ?\}))
	   (save-excursion
	     (forward-char -1)
	     (member (coq-smie-backward-token) ;; recursive call
		     '("." ". proofstart" "{ subproof" "} subproof"
		     "- bullet" "+ bullet" "* bullet"))))
      (forward-char -1)
      (if (looking-at "{") "{ subproof" "} subproof"))

     ((and (equal tok ":") (looking-back "\\<\\(constr\\|ltac\\)"))
      ": ltacconstr")

     ((equal tok ":=")
      (save-excursion
	(let ((corresp (coq-smie-search-token-backward
			'("let" "Inductive" "Coinductive" "{|" "." "with")
			nil '(("let" . ":=") ("match" . "with")))))
	  (cond
	   ((member corresp '("Inductive" "CoInductive")) ":="); := inductive
	   ((equal corresp "let") ":= let")
	   ((equal corresp "with") ":= with")
	   ((or (looking-back "{")) ":= record")
	   (t tok)))))

     ((equal tok "=>")
      (save-excursion
	(let ((corresp (coq-smie-search-token-backward
			'("|" "match" "fun" ".")
			nil '(("match" . "end") ("fun" . "=>")))))
	  (cond
	   ((member corresp '("fun")) "=> fun") ; fun
	   (t tok)))))

     ;; FIXME: no token should end with "." except "." itself
     ; for "unfold in *|-*."
     ((member tok '("*." "-*." "|-*." "*|-*.")) (forward-char 1) ".")
     ; for "unfold in *|-*;"
     ((member tok '("*;" "-*;" "|-*;" "*|-*;")) (forward-char 1) "; tactic")
     ((and (member tok '("+" "-" "*"))
	   (save-excursion
	     (let ((prev (coq-smie-backward-token))) ;; recursive call
	       (member prev '("." ". proofstart" "{ subproof" "} subproof")))))
      (concat tok " bullet"))
     ((and (member tok '("exists" "∃"))
	   (save-excursion
	     (not (member
		   (coq-smie-backward-token) ;; recursive call
		   '("." ". proofstart" "; tactic" "[" "]" "|" "{ subproof" "} subproof"))))
	   "quantif exists"))
      ((equal tok "∀") "forall")
      ((equal tok "→") "->")
     ((and (equal tok "with")
	   (save-excursion
	     (equal (coq-smie-search-token-backward '("match" ".")) "match")))
      "with match")
     ((and (equal tok "with")
	   (save-excursion
	     (equal (coq-smie-search-token-backward '("Module" ".")) "Module")))
      "with module")


     ((and (equal tok "signature")
	   (equal (smie-default-backward-token) "with"))
      "with signature")

     ((equal tok "by")
      (let ((p (point)))
	(if (and (equal (smie-default-backward-token) "proved")
		 (member (smie-default-backward-token)
			 '("transitivity" "symmetry" "reflexivity")))
	    "xxx provedby"
	  (goto-char p)
	  tok))) ; by tactical


      ((equal tok "as")
       (save-excursion
	 (let ((prev-interesting
		(coq-smie-search-token-backward
		 '("match" "Morphism" "Relation" "." ". proofstart"
		   "{ subproof" "} subproof" "as")
		 nil
		 '((("match" "let") . "with") ("with" . "signature")))))
	   (cond
	    ((equal prev-interesting "match") "as match")
	    ((member prev-interesting '("Morphism" "Relation")) "as morphism")
	    (t tok)))))

      ((equal tok "in")
       (save-excursion
	 (let ((prev-interesting
		(coq-smie-search-token-backward
		 '("let" "match" "eval" "." ) nil
		 '(("match" . "with") (("let" "eval") . "in")))))
	   (cond
	    ((member prev-interesting '("." nil)) "in tactic")
	    ((equal prev-interesting "let") "in let")
	    ((equal prev-interesting "eval") "in eval")
	    ((equal prev-interesting "match") "in match")
	    (t "in tactic")))))

      ;; Too slow
      ((and (eq (char-before) ?@) (member (char-syntax (char-after)) '(?w ?_)))
       (forward-char -1)
       (concat "@" tok))

     ((member tok coq-smie-proof-end-tokens) "Proof End")

     ;; ((member tok '("." "..."))
     ;;  ;; Distinguish field-selector "." from terminator "." from module
     ;;  ;; qualifier.
     ;;  (if (looking-at "\\.(") ". selector"  ;;Record selector.
     ;; 	(if (looking-at "\\.[[:space:]]")  ;; command terminator
     ;; 	    (coq-smie-.-desambiguate)
     ;; 	  (if (looking-at "\\.[[:alpha:]_]") ;; qualified id
     ;; 	      (let ((newtok (coq-smie-complete-qualid-backward)))
     ;; 		(concat newtok tok))
     ;; 	    ". selector"))))  ;; probably a user defined syntax

     ((member tok '("." "..."))
      ;; Distinguish field-selector "." from terminator "." from module
      ;; qualifier.
      (let ((nxtnxt (char-after (+ (point) (length tok)))))
	(if (eq nxtnxt ?\() ". selector" ;(looking-at "\\.(") ". selector"  ;;Record selector.
	  (if (eq (char-syntax nxtnxt) ?\ ) ;; command terminator
	      (save-excursion (forward-char (- (length tok) 1))
			      (coq-smie-.-desambiguate))
	    (if (eq (char-syntax nxtnxt) ?w) ;(looking-at "\\.[[:alpha:]_]") ;; qualified id
		(let ((newtok (coq-smie-complete-qualid-backward)))
		  (concat newtok tok))
	      ". selector")))))  ;; probably a user defined syntax



     ((and (and (eq (char-before) ?.) (member (char-syntax (char-after)) '(?w ?_))))
      (forward-char -1)
      (let ((newtok (coq-smie-backward-token))) ; recursive call
	(concat newtok "." tok)))

     (tok))))


(defcustom coq-indent-box-style nil
  "If non-nil, Coq mode will try to indent with a box style (SMIE code only).
Box style looke like this:
Lemma foo: forall n,
             n = n.

instead of

Lemma foo: forall n,
  n = n.
"
  :type 'boolean
  :group 'coq)


;; FIXME: This does not know about Notations.
(defconst coq-smie-grammar
  (when (fboundp 'smie-prec2->grammar)
    (smie-prec2->grammar
     (smie-bnf->prec2
      '((exp(assoc "|")
         (exp ":=" exp)
         (exp "|" exp) (exp "=>" exp)
         (exp "xxx provedby" exp)
         (exp "as morphism" exp)
         (exp "with signature" exp)
         ("match" matchexp "with match" exp "end");expssss
         ("let" assigns "in let" exp)
         ("eval" assigns "in eval" exp)
         ("fun" exp "=> fun" exp)
         ("if" exp "then" exp "else" exp)
         ("quantif exists" exp ", quantif" exp)
         ("forall" exp ", quantif" exp)
         ;;;
         ("(" exp ")") ("{|" exps "|}") ("{" exps "}")
         (exp "; tactic" exp) (exp "in tactic" exp) (exp "as" exp)
	 (exp "|-" exp)
         (exp ":" exp) (exp ":<" exp) (exp "," exp)
         (exp "->" exp) (exp "<->" exp) (exp "/\\" exp) (exp "\\/" exp)
         (exp "==" exp) (exp "=" exp) (exp "<>" exp) (exp "<=" exp)
         (exp "<" exp) (exp ">=" exp) (exp ">" exp)
         (exp "=?" exp) (exp "<=?" exp) (exp "<?" exp)
         (exp "^" exp) (exp "+" exp) (exp "-" exp) (exp "*" exp)
         (exp ": ltacconstr" exp)(exp ". selector" exp))
        ;; Having "return" here rather than as a separate rule in `exp' causes
        ;; it to be indented at a different level than "with".
        (matchexp (exp) (exp "as match" exp) (exp "in match" exp)
                  (exp "return" exp) )
        ;(expssss (exp) (expssss "|" expssss) (exp "=>" expssss)) ; (expssss "as" expssss)
        (exps (exp) (exp ":= record" exp) (exps "; record" exps))
        (assigns  (exp ":= let" exp)) ;(assigns "; record" assigns)

        (moduledecl (exp)
                    (exp ":" moduleconstraint))
        (moduleconstraint (exp)
                          (moduleconstraint "with module" moduleconstraint)
                          (exp ":= with" exp))

        ;; To deal with indentation inside module declaration and inside
        ;; proofs, we rely on the lexer. The lexer detects "." terminator of
        ;; goal starter and returns the ". proofstart" and ". moduelstart"
        ;; tokens.
        (bloc ("{ subproof" commands "} subproof")
              (". proofstart" commands  "Proof End")
              (". modulestart" commands  "End")
              (exp))
        (commands (commands "." commands)
                  (commands "- bullet" commands)
                  (commands "+ bullet" commands)
                  (commands "* bullet" commands)
                  (bloc)))


      ;; Resolve the "trailing expression ambiguity" as in "else x -> b".
      ;; each line orders tokens by increasing priority
      ;; | C x => fun a => b | C2 x => ...
      ;;'((assoc "=>") (assoc "|")  (assoc "|-" "=> fun")) ; (assoc ", quantif")
      '((assoc ".") (assoc "Module"))
      '((assoc "- bullet") (assoc "+ bullet") (assoc "* bullet") (assoc "."))
      '((assoc ":=") (assoc "|") (assoc "=>")
	(assoc "xxx provedby")
	(assoc "as morphism") (assoc "with signature") (assoc "with match") (assoc "in let")
	(assoc "in eval") (assoc "=> fun") (assoc "then") (assoc "else") (assoc ", quantif")
	(assoc "; tactic") (assoc "in tactic") (assoc "as")
	(assoc "|-") (assoc ":" ":<") (assoc ",") (assoc "->") (assoc "<->")
	(assoc "/\\") (assoc "\\/")
	(assoc "==") (assoc "=") (assoc "<" ">" "<=" ">=" "<>")
	(assoc "=?") (assoc "<=?") (assoc "<?") (assoc "^") 
	(assoc "+") (assoc "-") (assoc "*")
	(assoc ": ltacconstr") (assoc ". selector") (assoc ""))
      '((assoc ":")(assoc "<"))
      '((assoc "with module") (assoc ":= with") (nonassoc ":"))
      '((assoc "; record")))))
  "Parsing table for Coq.  See `smie-grammar'.")
;; FIXME: {|\n xx:=y; ...|}
;; FIXME:
; Record rec:Set := {
;                   fld1:nat;
;                   fld2:nat;
;                   fld3:bool
;                 }.
; FIXME:
;  - Si Next Obligation suivi de Proof: pas d'indentation sur le Next
;    Obligation
; FIXME:
;  rewrite
;  in
;  H.
; FIXME: same thing with "as"
; FIXME:
; Instance x
; := <- should right shift
; FIXME: idem:
; Lemma x
; : <- should right shift
; FIXME:
;; Add Parametric Morphism (A : Type) : (mu (A:=A))
;;     with signature Oeq ==> Oeq
;;                    as mu_eq_morphism.
;; FIXME:
;; match x with
;; C1 => ..
;; | ...


; This fixes a bug in smie that is not yet in regular emacs distribs??
; To show the bug. Comment this and then try to indent the following:
; Module X.
; Module Y. <-- here -->  Error: (wrong-type-argument integer-or-marker-p nil)
(defun smie-indent--parent ()
  (or smie--parent
      (save-excursion
        (let* ((pos (point))
               (tok (funcall smie-forward-token-function)))
          (unless (numberp (cadr (assoc tok smie-grammar)))
            (goto-char pos))
          (setq smie--parent
                (or (smie-backward-sexp 'halfsexp)
                    (let (res)
                      (while (null (setq res (smie-backward-sexp))))
                      (list nil (point) (nth 2 res)))))))))

(defun coq-smie-rules (kind token)
  "Indentation rules for Coq.  See `smie-rules-function'.
KIND is the situation and TOKEN is the thing w.r.t which the rule applies."
   (case kind
     (:elem (case token
              (basic proof-indent)))
     (:list-intro
      (or (member token '("fun" "forall" "quantif exists"))
          ;; We include "." in list-intro for the ". { .. } \n { .. }" so the
          ;; second {..} is aligned with the first rather than being indented as
          ;; if it were an argument to the first.
          ;; FIXME: this gives a strange indentation for ". { \n .. } \n { .. }"
          (when (member token '("." ". proofstart"))
            (forward-char 1) ; skip de "."
            (equal (coq-smie-forward-token) "{ subproof"))
          ))
     (:after
      (cond
;;       ;; Override the default indent step added because of their presence
;;       ;; in smie-closer-alist.
       ((equal token "with match") 4)
       ((member token '(":" ":=" ":= with"))
;        (if (smie-rule-parent-p "Definition" "Lemma" "Theorem" "Fixpoint"
;                                "Inductive" "Function" "Let" "Record"
;                                "Instance" "Class" "Ltac" "Add" "goalcmd")
;            (smie-rule-parent 2) 2)
        2)

       ((equal token ":= record") 2)
;       ((equal token ". modulestart") 0)
;       ((equal token ". proofstart") 0)
       ((equal token "with module") 2)


       ((equal token "- bullet") (smie-rule-parent 2))
       ((equal token "+ bullet") (smie-rule-parent 2))
       ((equal token "* bullet") (smie-rule-parent 2))

       ((equal token "; tactic") ; "; tactic" maintenant!!
        (cond
         ((smie-rule-parent-p "; tactic") (smie-rule-separator kind))
         (t (smie-rule-parent 2))))

       ; "as" tactical is not idented correctly
       ((equal token "as") (smie-rule-parent 2))
       ((equal token "in let") (smie-rule-parent))


;;       ((equal token "in match") 2)
;;       ((equal token "as match") 2)
;;       ((equal token "return") 2)
;;       ((equal token ":= inductive") 2)
;;       ((equal token ",")
;;        (cond
;;         ;; FIXME: when using utf8 quantifiers, is is better to have 1 instead
;;         ;; of 2 here, workaround: write "∀x" instead of "∀ x".
;;         ((smie-rule-parent-p "forall" "quantif exists") (smie-rule-parent 2))
;;         (t (smie-rule-parent 2))))
;;       ((equal token "Proof") ;; ("BeginSubproof" "Module" "Section" "Proof")
;;        (message "PROOF FOUND")
;;        (smie-rule-parent 2))
     ))

     (:before
      (cond
       ((equal token "with module")
        (if (smie-rule-parent-p "with module")
            (smie-rule-parent)
          (smie-rule-parent 4)))

       ((equal token "as morphism") (smie-rule-parent 2))
       ((member token '("xxx provedby" "with signature"))
        (if (smie-rule-parent-p "xxx provedby" "with signature")
            (smie-rule-parent)
          (smie-rule-parent 4)))


       ((and (member token '("forall" "quantif exists"))
             (smie-rule-parent-p "forall" "exists quantif"))
        (smie-rule-parent))

       ;; This rule allows "End Proof" to align with corresponding ".
       ;; proofstart" PARENT instead of ". proofstart" itself
       ;;  Typically:
       ;;    "Proof" ". proofstart"
       ;;    "Qed" <- parent is ". proofstart" above
       ;; Align with the real command start of the ". xxxstart"
       ((member token '(". proofstart" ". modulestart"))
        (save-excursion (coq-find-real-start)
                        `(column . ,(current-column))))



;;       ((equal token "as") 2)
;;       ((member token '("return" "in match" "as match"))
;;        (if (smie-rule-parent-p "match") 3))
       ((equal token "|")
        (cond ((smie-rule-parent-p "with match")
               (- (funcall smie-rules-function :after "with match") 2))
              ((smie-rule-prev-p ":= inductive")
               (- (funcall smie-rules-function :after ":= inductive") 2))
              (t (smie-rule-separator kind))))
;;       ((and (equal token "Proof End")
;;             (smie-rule-parent-p "Module" "Section" "goalcmd"))
;;        ;; ¡¡Major gross hack!!
;;        ;; This typically happens when a Lemma had no "Proof" keyword.
;;        ;; We should ideally find some other way to handle it (e.g. matching Qed
;;        ;; not with Proof but with any of the keywords like Lemma that can
;;        ;; start a new proof), but we can workaround the problem here, because
;;        ;; SMIE happened to decide arbitrarily that Qed will stop before Module
;;        ;; when parsing backward.
;;        ;; FIXME: This is fundamentally very wrong, but it seems to work
;;        ;; OK in practice.
;;        (smie-rule-parent 2))
       ))))




(provide 'coq-smie-lexer)