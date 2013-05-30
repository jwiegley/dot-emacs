;; Variables to store the tree depth levels

(defvar ml4pg-tdl1 nil)
(defvar ml4pg-tdl2 nil)
(defvar ml4pg-tdl3 nil)
(defvar ml4pg-tdl4 nil)
(defvar ml4pg-tdl5 nil)

;; Variables to store the information about the tactic level

(defvar ml4pg-intro nil)
(defvar ml4pg-case nil)
(defvar ml4pg-simpltrivial nil)
(defvar ml4pg-induction nil)
(defvar ml4pg-simpl nil)
(defvar ml4pg-rewrite nil)
(defvar ml4pg-trivial nil)

(defvar ml4pg-hypothesis nil)

(defvar ml4pg-init 0)

(defun ml4pg-export-theorem ()
  (interactive)
  (progn (setf ml4pg-tdl1 nil 
	       ml4pg-tdl2 nil
	       ml4pg-tdl3 nil
	       ml4pg-tdl4 nil
	       ml4pg-tdl5 nil
	       ml4pg-intro nil
	       ml4pg-case nil
	       ml4pg-simpltrivial nil
	       ml4pg-induction nil
	       ml4pg-simpl nil
	       ml4pg-rewrite nil
	       ml4pg-trivial nil
	       ml4pg-hypothesis nil
	       ml4pg-goal-level nil)
	 (if (equal ml4pg-init 0)
	     (progn (ml4pg-read-lemmas)
		    (setq ml4pg-init 1)))
	 (ml4pg-export-theorem-aux nil nil 1 nil)
	 (proof-shell-invisible-cmd-get-result (format "Unset Printing All"))
	   ))

(defvar ml4pg-saved-theorems nil)
(defvar ml4pg-goal-level-temp nil)
(defvar ml4pg-tactic-level nil)
(defvar ml4pg-proof-tree-level nil)

;; Variables to store the different values associated with the tactics, the
;; types or the rewrite rules

(defvar ml4pg-tactic_id '(("intro"     . 1)
		    ("case"      . 2)
		    ("simpl"     . 3)
		    ("trivial"   . 4)
		    ("induction" . 5)
		    ("rewrite"   . 6)
		    ("simpl; trivial" . 34)))


(defvar ml4pg-types_id '(("nat"  . -2)
		   ("Prop" . -4)
		   ("bool" . -3)
		   ("A"  . -1)
		   ("list" . -5)))

(defvar ml4pg-theorems_id nil)

;; A function to obtain the type associated with an object

(defun ml4pg-get-type-id (object) 
  (let* ((a (proof-shell-invisible-cmd-get-result (format (concat "Check " object))))
	 (pos_jump (search "
" a :start2 (+ 2 (search " " a))))
	 (pos_space (search " " a :start2 (+ 2 (search ": " a))))
	 (type (if pos_space
		   (cdr (assoc (subseq a (+ 2 (search ": " a)) pos_space) ml4pg-types_id))
		 (cdr (assoc (subseq a (+ 2 (search ": " a)) pos_jump) ml4pg-types_id)))))
    (if type type -4)))


;; A function to obtain the value of a top symbol


(defun ml4pg-get-top-symbol ()
  (proof-shell-invisible-cmd-get-result (format "Set Printing All"))
  (let* ((res (proof-shell-invisible-cmd-get-result (format "Focus")))
	(res2 (subseq res (+ 32 (search "============================" res))))
	(fst-symbol (subseq res2 0 (search " " res2))))
    (cond ((string= fst-symbol "forall") 5)
	  ((search "->" res2) 7)
	  ((string= "@eq" fst-symbol) 6)
	  ((string= "and" fst-symbol) 4) ; I have included this
	  ((string= "iff" fst-symbol) 8) ; I have included this
	  ((string= "or" fst-symbol) 3)  ; I have included this
	  (t 0))))

;; In some cases the intro tactic does not have parameters, the following function
;; obtain the type of the object introduced with the intro tactic in those cases

(defun ml4pg-get-obj-intro ()
  (let* ((undo (proof-undo-last-successful-command))
	 (obj (proof-shell-invisible-cmd-get-result (format "Show Intro")))
	 (object (subseq obj 0 (search "
" obj)))
	 (dod (proof-assert-next-command-interactive))
	 (foo (setf ml4pg-hypothesis (append ml4pg-hypothesis (list object)))))
    
    (ml4pg-get-type-id object)
  ))

(defun ml4pg-extract-params (seq res)
  (let ((pos_space (search " " seq))
	(pos_jump (search "
" seq)))
    (if pos_space
	(ml4pg-extract-params (subseq seq (+ 1 pos_space)) (cons (subseq seq 0 pos_space) res))
      (reverse (cons (subseq seq 0 pos_jump) res)))))

(defun ml4pg-extract-params2 (seq res)
  (let ((pos_space (search " " seq))
	(pos_jump (search "." seq)))
    (if pos_space
	(ml4pg-extract-params2 (subseq seq (+ 1 pos_space)) (cons (subseq seq 0 pos_space) res))
      (reverse (cons (subseq seq 0 pos_jump) res)))))

;; Given a list of objects, it obtains the value associated with their types

(defun ml4pg-get-types-list (list res)
  (if (endp list)
      (* -1 res)
    (ml4pg-get-types-list (cdr list) (+ (* -1 (ml4pg-get-type-id (car list)) (expt 10 (- (length list) 1))) res))))

;; To obtain the number of tactics applied

(defun ml4pg-get-number-list (list)
  (if (endp list)
      0
    (+ (expt 10 (- (length list) 1))  (ml4pg-get-number-list (cdr list)))))

;; To obtain the value associated with top symbol in the case of intros

(defun ml4pg-get-top-symbols-list (len res)
  (if (= len 0)
      res
    (let ((gs (ml4pg-get-top-symbol))
	  (ps (proof-shell-invisible-cmd-get-result (format "intro"))))
      (+ (ml4pg-get-top-symbols-list (- len 1) (+ (* gs (expt 10 (- len 1))) res))))))
  
(defun ml4pg-get-top-symbols-seq (seq res)
  (if (endp seq)
      res
    (let ((gs (ml4pg-get-top-symbol))
	  (ps (proof-shell-invisible-cmd-get-result (format (concat "intro " (car seq))))))
      (+ (ml4pg-get-top-symbols-seq (cdr seq) (+ (* gs (expt 10 (- (length seq) 1))) res))))))

;; To obtain the values associated with intros both for the case when parameters are
;; given and the case intros. 

(defun ml4pg-get-obj-intros ()
  (let* ((undo (proof-undo-last-successful-command))
	 (obj (proof-shell-invisible-cmd-get-result (format "Show Intros")))
	 (dod (proof-assert-next-command-interactive))
	 (params (ml4pg-extract-params obj nil))
	 (foo (setf ml4pg-hypothesis (append ml4pg-hypothesis params)))
	 (types (ml4pg-get-types-list params 0))
	 (num (ml4pg-get-number-list params))
	 (undo2 (proof-shell-invisible-cmd-get-result (format "Undo")))
	 (gts (ml4pg-get-top-symbols-list (length params) 0)))
    (list num types (length params) gts)
  ))

(defun ml4pg-get-obj-intros2 (objects)
  (let* ((params (ml4pg-extract-params2 objects nil))
	 (foo (setf ml4pg-hypothesis (append ml4pg-hypothesis params)))
	 (types (ml4pg-get-types-list params 0))
	 (num (ml4pg-get-number-list params))
	 (undo2 (proof-shell-invisible-cmd-get-result (format "Undo")))
	 (gts (ml4pg-get-top-symbols-seq params 0)))
    (list num types (length params) gts)
  ))

;; To obtain the value associated with a theorem

(defun ml4pg-search-in-hyp (obj hyp)
  (if (endp hyp)
      nil
    (if (string= obj (car hyp))
	t
      (ml4pg-search-in-hyp obj (cdr hyp)))))


(defvar ml4pg-add_to 0.1)
(defvar ml4pg-start 100)

(defun ml4pg-extract-theorem-id (cmd)
  (let ((s<- (search "<-" cmd)))
    (if s<-
	(if (assoc (subseq cmd (+ 3 s<-) (search "." cmd)) ml4pg-theorems_id)
	    (cdr (assoc (subseq cmd (+ 3 s<-) (search "." cmd)) ml4pg-theorems_id))
	  (if (ml4pg-search-in-hyp (subseq cmd (+ 3 s<-) (search "." cmd)) ml4pg-hypothesis)
	      1
	    (progn (setf ml4pg-start (+ ml4pg-start ml4pg-add_to)) 
		   (setf ml4pg-theorems_id 
			 (append ml4pg-theorems_id (list (cons (subseq cmd (+ 3 s<-) 
								 (search "." cmd))
							 ml4pg-start))))
		   (ml4pg-save-lemma (subseq cmd (+ 3 s<-) 
				       (search "." cmd)) ml4pg-start)
		   (setf ml4pg-add_to (/ ml4pg-add_to 2))
		   ml4pg-start
		   )))
      (if (assoc (subseq cmd (+ 1 (search " " cmd)) (search "." cmd)) ml4pg-theorems_id)
	  (cdr (assoc (subseq cmd (+ 1 (search " " cmd)) (search "." cmd)) ml4pg-theorems_id))
	(if (ml4pg-search-in-hyp (subseq cmd (+ 1 (search " " cmd)) (search "." cmd)) ml4pg-hypothesis)
	      1
	    (progn (setf ml4pg-start (+ ml4pg-start ml4pg-add_to)) 
		   (ml4pg-save-lemma (subseq cmd (+ 1 (search " " cmd)) (search "." cmd))  ml4pg-start)
		   (setf ml4pg-theorems_id 
			 (append ml4pg-theorems_id (list (cons (subseq cmd (+ 1 (search " " cmd)) (search "." cmd))
							 ml4pg-start))))
		   (setf ml4pg-add_to (/ ml4pg-add_to 2))
		   ml4pg-start
		   ))))))


(defun ml4pg-arg-induction (object)
  (let* ((ps0 (proof-shell-invisible-cmd-get-result (format "Undo")))
	 (res (proof-shell-invisible-cmd-get-result (concat "Check " object)))
	 (ps3 (proof-shell-invisible-cmd-get-result (concat "induction " object)))
	 (err (search "Error" res)))
    (if err -1 1)))

(defun ml4pg-get-type-id-induction (object arg-ind)
  (if (equal arg-ind 1)
      (let ((ps0 (proof-shell-invisible-cmd-get-result (format "Undo")))
	    (gt (ml4pg-get-type-id object))
	    (ps3 (proof-shell-invisible-cmd-get-result (concat "induction " object))))
      gt)
    (let ((ps0 (proof-shell-invisible-cmd-get-result (format "Undo")))
	  (ps (proof-shell-invisible-cmd-get-result (concat "intro " object)))
	  (gt (ml4pg-get-type-id object))
	  (ps2 (proof-shell-invisible-cmd-get-result (format "Undo")))
	  (ps3 (proof-shell-invisible-cmd-get-result (concat "induction " object))))
      gt)))
	   
;; Function to add the information to the corresponding tree depth level

(defun ml4pg-add-info-to-tree (info level)
  (cond ((= ml4pg-level 1) (setf ml4pg-tdl1 (append ml4pg-tdl1 (list info))))
	((= ml4pg-level 2) (setf ml4pg-tdl2 (append ml4pg-tdl2 (list info))))
	((= ml4pg-level 3) (setf ml4pg-tdl3 (append ml4pg-tdl3 (list info))))
	((= ml4pg-level 4) (setf ml4pg-tdl4 (append ml4pg-tdl4 (list info))))
	((= ml4pg-level 5) (setf ml4pg-tdl5 (append ml4pg-tdl5 (list info))))
	(t nil)))

;; Function to add the information to the corresponding tactic

(defun ml4pg-add-info-to-tactic (info tactic)
  (cond ((string= ml4pg-tactic "intro") (setf ml4pg-intro (append ml4pg-intro (list info))))
	((string= ml4pg-tactic "case") (setf ml4pg-case (append ml4pg-case (list info))))
	((string= ml4pg-tactic "simpltrivial") (setf ml4pg-simpltrivial (append ml4pg-simpltrivial (list info))))
	((string= ml4pg-tactic "induction") (setf ml4pg-induction (append ml4pg-induction (list info))))
	((string= ml4pg-tactic "simpl") (setf ml4pg-simpl (append ml4pg-simpl (list info))))
	((string= ml4pg-tactic "rewrite") (setf ml4pg-rewrite (append ml4pg-rewrite (list info))))
	((string= ml4pg-tactic "trivial") (setf ml4pg-trivial (append ml4pg-trivial (list info))))     
	(t nil)))
     


;The first value is the tactic, the second one is the number of tactics,
;the third one is the argument type, the fourth one is if the
;argument is a hypothesis of a theorem, the fifth one is the top-symbol
;and the last one the number of subgoals

(defun ml4pg-get-numbers (cmd tactic ngs ts current-level bot)
  (cond ((and (string= tactic "intro") (not (string= cmd "intro.")))
	 (let* ((object (subseq cmd (1+ (search " " cmd)) (search "." cmd)))
		(type (ml4pg-get-type-id object))
		
		
		(foo (setf ml4pg-hypothesis (append ml4pg-hypothesis (list object))))
		(res (list (cdr (assoc "intro" ml4pg-tactic_id)) 
		 1
		 type
		 -1
		 ts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))
	   res))
	((string= tactic "intro") 
	 (let* ((type (ml4pg-get-obj-intro))
		
		
		(res (list (cdr (assoc "intro" ml4pg-tactic_id)) 
		 1
		 (ml4pg-get-obj-intro)
		 -1
		 ts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))	   
	   res))
	((and (string= tactic "intros") (not (string= cmd "intros.")))
	 (let* ((params (ml4pg-get-obj-intros2 (subseq cmd (1+ (search " " cmd)))))
		(nparams (car params))
		(types-params (cadr params))
		(len (caddr params))
		(gts (cadddr params))
		
		
		(res (list nparams 
                 len
		 types-params
		 -1
		 gts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))
	   res))
	((string= tactic "intros")
	 (let* ((params (ml4pg-get-obj-intros))
		(nparams (car params))
		(types-params (cadr params))
		(len (caddr params))
		(gts (cadddr params))
		
		
		(res (list 	 nparams 
                 len
		 types-params
		 -1
		 gts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp)))) 
	 res))
	((string= tactic "case")
	 (let* ((object (subseq cmd (1+ (search " " cmd)) (search "." cmd)))
		(type (ml4pg-get-type-id object))
		
		
		(res (list (cdr (assoc "case" ml4pg-tactic_id)) 
		 1
		 type
		 1 ts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))
	   res))
	((string= tactic "simpl")
	 (progn 
		
		(setf ml4pg-goal-level-temp (cons (list (cdr (assoc "simpl" ml4pg-tactic_id)) 1 0 0 ts ngs) ml4pg-goal-level-temp))
		(list (cdr (assoc "simpl" ml4pg-tactic_id)) 1 0 0 ts ngs)))
	((string= tactic "trivial")
	 (progn 
		
		(setf ml4pg-goal-level-temp (cons (list (cdr (assoc "trivial" ml4pg-tactic_id)) 1 0 0 ts ngs) ml4pg-goal-level-temp))
		(list (cdr (assoc "trivial" ml4pg-tactic_id)) 1 0 0 ts ngs)))
	((string= tactic "induction")
	 (let* ((object (subseq cmd (1+ (search " " cmd)) (search "." cmd)))
	       (arg-ind (ml4pg-arg-induction object))
	       (type (ml4pg-get-type-id-induction object arg-ind))
	       
	       
	       (ih (setf ml4pg-theorems_id (append ml4pg-theorems_id (list (cons (concat "IH" object) 10)))))
	       (res (list (cdr (assoc "induction" ml4pg-tactic_id)) 
		 1 type arg-ind ts ngs))
	       (foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))
	   res))
	((string= tactic "rewrite")
	 (progn 
		
		(setf ml4pg-goal-level-temp (cons (list (cdr (assoc "rewrite" ml4pg-tactic_id)) 1 -4 
		      (ml4pg-extract-theorem-id cmd) ts ngs) ml4pg-goal-level-temp))
	   (list (cdr (assoc "rewrite" ml4pg-tactic_id)) 1 -4 
		      (ml4pg-extract-theorem-id cmd) ts ngs))
	 )
	((string= cmd "simpl; trivial.")
	 (progn 
		
		(setf goal-level-temp (cons  (list (cdr (assoc "simpl; trivial" ml4pg-tactic_id)) 2 0 0 ts ngs)  ml4pg-goal-level-temp))
		(list (cdr (assoc "simpl; trivial" ml4pg-tactic_id)) 2 0 0 ts ngs))
	 )))

;; Function to obtain the information just about the goals. 

(defun ml4pg-get-numbers2 (cmd tactic ngs ts current-level bot)
  (cond ((and (string= tactic "intro") (not (string= cmd "intro.")))
	 (let* ((object (subseq cmd (1+ (search " " cmd)) (search "." cmd)))
		(type (ml4pg-get-type-id object))
		
		
		(foo (setf ml4pg-hypothesis (append ml4pg-hypothesis (list object))))
		(res (list (cdr (assoc "intro" ml4pg-tactic_id)) 
		 1
		 type
		 -1
		 ts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))
	   res))
	((string= tactic "intro") 
	 (let* ((type (ml4pg-get-obj-intro))
		
		
		(res (list (cdr (assoc "intro" ml4pg-tactic_id)) 
		 1
		 (get-obj-intro)
		 -1
		 ts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))	   
	   res))
	((and (string= tactic "intros") (not (string= cmd "intros.")))
	 (let* ((params (ml4pg-get-obj-intros2 (subseq cmd (1+ (search " " cmd)))))
		(nparams (car params))
		(types-params (cadr params))
		(len (caddr params))
		(gts (cadddr params))
		
		
		(res (list nparams 
                 len
		 types-params
		 -1
		 gts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))
	   res))
	((string= tactic "intros")
	 (let* ((params (ml4pg-get-obj-intros))
		(nparams (car params))
		(types-params (cadr params))
		(len (caddr params))
		(gts (cadddr params))
		
		
		(res (list 	 nparams 
                 len
		 types-params
		 -1
		 gts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp)))) 
	 res))
	((string= tactic "case")
	 (let* ((object (subseq cmd (1+ (search " " cmd)) (search "." cmd)))
		(type (ml4pg-get-type-id object))
		
		
		(res (list (cdr (assoc "case" ml4pg-tactic_id)) 
		 1
		 type
		 1 ts ngs))
		(foo2 (setf ml4pg-goal-level-temp (cons res ml4pg-goal-level-temp))))
	   res))
	((string= tactic "simpl")
	 (progn 
		
	   (list (cdr (assoc "simpl" ml4pg-tactic_id)) 1 0 0 ts ngs)))
	((string= tactic "trivial")
	 (progn 
			
		(list (cdr (assoc "trivial" ml4pg-tactic_id)) 1 0 0 ts ngs)))
	((string= tactic "induction")
	 (let* ((object (subseq cmd (1+ (search " " cmd)) (search "." cmd)))
	       (arg-ind (ml4pg-arg-induction object))
	       (type (ml4pg-get-type-id-induction object arg-ind))
	       
	       
	        (ih (setf ml4pg-theorems_id (append ml4pg-theorems_id (list (cons (concat "IH" object) 10)))))
	       (res (list (cdr (assoc "induction" ml4pg-tactic_id)) 
		 1 type arg-ind ts ngs))
	       (foo2 (setf goal-level-temp (cons res goal-level-temp))))
	   res))
	((string= tactic "rewrite")
	 (progn	  
		
		(list (cdr (assoc "rewrite" ml4pg-tactic_id)) 1 -4 
		      (ml4pg-extract-theorem-id cmd) ts ngs))
	 )
	((string= cmd "simpl; trivial.")
	 (progn 
		
		(list (cdr (assoc "simpl; trivial" ml4pg-tactic_id)) 2 0 0 ts ngs))
	 )))

(defun ml4pg-count-seq (item seq)
  (let ((is? (search item seq)))
    (if is?
	(+ 1 (ml4pg-count-seq item (subseq seq (+ 1 is?))))
	0)))

(defun ml4pg-get-number-of-goals ()
  (let ((r (proof-shell-invisible-cmd-get-result (format "Show Proof"))))
    (ml4pg-count-seq "?" r)))


(defun ml4pg-flat (ll)
  (if (endp ll)
    nil
    (append (car ll) (ml4pg-flat (cdr ll)))))


;; The following function computes the result of the proof tree level

(defun ml4pg-remove-zeros (n)
  (do ((temp n (/ temp 10)))
      ((or (= temp 0) (not (= (mod temp 10) 0))) temp)))

(defun ml4pg-obtain-level (level n)
  (do ((temp (cdr level) (cdr temp))
       (temp2 (if (endp level) (list 0 0 0 0 0 0 0 0 0)
		  (list (* (nth 0 (car level)) (expt 10 (length (cdr level))))
		    (* (nth 1 (car level)) (expt 10 (length (cdr level))))
		    (* (nth 2 (car level)) (expt 10 (length (cdr level))))
		    (* (nth 3 (car level)) (expt 10 (length (cdr level))))
		    (* (nth 4 (car level)) (expt 10 (length (cdr level))))
		    (* (nth 5 (car level)) (expt 10 (length (cdr level))))
		    (* (nth 6 (car level)) (expt 10 (length (cdr level))))
		    (* (nth 7 (car level)) (expt 10 (length (cdr level))))
		    (nth 8 (car level))))))
      ((endp temp) (list (ml4pg-remove-zeros (nth 0 temp2))
			 (ml4pg-remove-zeros (nth 1 temp2))
			 (ml4pg-remove-zeros (nth 2 temp2))
			 (ml4pg-remove-zeros (nth 3 temp2))
			 (ml4pg-remove-zeros (nth 4 temp2))
			 (nth 5 temp2)
			 (ml4pg-remove-zeros (nth 6 temp2))
			 (if (= (nth 7 temp2) 0) (nth 7 temp2) (+ (* n (expt 10 (length level))) (ml4pg-remove-zeros (nth 7 temp2))))
			 (nth 8 temp2)))
    (setf temp2 (list (+ (nth 0 temp2) (* (expt 10 (length (cdr temp))) (nth 0 (car temp))))
		      (+ (nth 1 temp2) (* (expt 10 (length (cdr temp))) (nth 1 (car temp))))
		      (+ (nth 2 temp2) (* (expt 10 (length (cdr temp))) (nth 2 (car temp))))
		      (+ (nth 3 temp2) (* (expt 10 (length (cdr temp))) (nth 3 (car temp))))
		      (+ (nth 4 temp2) (* (expt 10 (length (cdr temp))) (nth 4 (car temp))))
		      (+ (nth 5 temp2) (* (expt 10 (length (cdr temp))) (nth 5 (car temp))))
		      (+ (nth 6 temp2) (* (expt 10 (length (cdr temp))) (nth 6 (car temp))))
		      (+ (nth 7 temp2) (* (expt 10 (length (cdr temp))) (nth 7 (car temp))))
		      (+ (nth 8 temp2) (nth 8 (car temp))))
      )
  ))


(defun ml4pg-compute-proof-result ()
  (append (ml4pg-obtain-level ml4pg-tdl1 1)
	  (ml4pg-obtain-level ml4pg-tdl2 2)
	  (ml4pg-obtain-level ml4pg-tdl3 3)
	  (ml4pg-obtain-level ml4pg-tdl4 4)
	  (ml4pg-obtain-level ml4pg-tdl5 5)))

;; The following function computes the result of the tactic


(defun ml4pg-digits (n)
  (if (= (mod n 10) 0)
      0
    (1+ (ml4pg-digits (/ n 10)))))

(defun ml4pg-first-digit (n digits)
  (/ n (expt 10 (1- digits))))

(defun ml4pg-rest-of-digits (n digits)
  (- n (* (ml4pg-first-digit n digits) (expt 10 (1- digits)))))

(defun ml4pg-obtain-tactic-result (tactic)
  (do ((temp (cdr tactic) (cdr temp))
       (temp2 (if (endp tactic) (list 0 0 0 0 0)
		  (list (ml4pg-first-digit (nth 0 (car tactic)) (ml4pg-digits (nth 0 (car tactic))))
			(* (ml4pg-rest-of-digits (nth 0 (car tactic)) (ml4pg-digits (nth 0 (car tactic)))) (expt 10 (length (cdr tactic))))
			(* (nth 1 (car tactic)) (expt 10 (length (cdr tactic))))
			(nth 2 (car tactic))
			(nth 3 (car tactic))))))
      ((endp temp) temp2)
    (setf temp2 (list (nth 0 temp2)
		      (+ (nth 1 temp2) (* (expt 10 (length (cdr temp))) (nth 0 (car temp))))
		      (+ (nth 2 temp2) (* (expt 10 (length (cdr temp))) (nth 1 (car temp))))
		      (concat (format "%s" (nth 3 temp2)) (format "%s" (nth 2 (car temp))))
		      (+ (nth 4 temp2) (nth 3 (car temp))))
      )
  ))


(defun ml4pg-compute-tactic-result ()
  (append (ml4pg-obtain-tactic-result ml4pg-intro)
	  (ml4pg-obtain-tactic-result ml4pg-case)
	  (ml4pg-obtain-tactic-result ml4pg-simpltrivial)
	  (ml4pg-obtain-tactic-result ml4pg-induction)
	  (ml4pg-obtain-tactic-result ml4pg-simpl)
	  (ml4pg-obtain-tactic-result ml4pg-rewrite)
	  (ml4pg-obtain-tactic-result ml4pg-trivial)))
 

(defvar ml4pg-useless-terms '("Definition" "Defined" "Fixpoint" "Structure" "Section" "Add Ring" "Hypothesis" "Hypotheses" "Include" "Export" "Parameter" "Axiom"
"End" "Notation" "Hint" "Inductive" "Variable" "Implicit" "Import" "Canonical" "Coercion"
"Module" "Ltac" "Let" "Opaque" "Bind" "Scope" "Require" "Infix" "Record" "Fact"))

(defun ml4pg-is-in-search (cmd)
  (do ((temp ml4pg-useless-terms (cdr temp))
       (is nil))
      ((or (endp temp) is) is)
      (if (search (car temp) cmd) (setf is t))))

(defun ml4pg-export-theorem-aux (result name current-level dot-level)
  (let* ((semis (save-excursion
		 (skip-chars-backward " \t\n"
				      (proof-queue-or-locked-end))
		 (proof-segment-up-to-using-cache (point))))
	 (comment (caar semis))
	 (cmd (cadar semis))
	 (pos_dot (search "." cmd))
	 (pos_space (search " " cmd))
	 (ts nil))
    (if semis 
    (cond ((or (string= comment "comment")
	       (ml4pg-is-in-search cmd))
	   (progn (proof-assert-next-command-interactive)
		  (ml4pg-export-theorem-aux result name current-level dot-level)))
	  ((search "Lemma" cmd)
	   (progn (proof-assert-next-command-interactive)
		  (ml4pg-export-theorem-aux result 
				      (subseq cmd (1+ (search " " cmd)) 
					      (search " " cmd :start2 (1+ (search " " cmd))))
				      current-level dot-level)))
	  ((search "Proof" cmd)
	   (progn (proof-assert-next-command-interactive)
		  (ml4pg-export-theorem-aux result name current-level dot-level)))
	  ((search "Theorem" cmd)
	   (progn (proof-assert-next-command-interactive)
		  (ml4pg-export-theorem-aux result 
				      (subseq cmd (1+ (search " " cmd)) 
					      (search " " cmd :start2 (1+ (search " " cmd))))
				      current-level dot-level)))
	  ((search "Qed." cmd)
	   (progn (proof-assert-next-command-interactive)
		  ; (insert (format "\n(* %s *)\n" (reverse result)))
		  (setf ml4pg-proof-tree-level (append ml4pg-proof-tree-level (list (ml4pg-compute-proof-result)))) 
		  (setf ml4pg-tactic-level (append ml4pg-tactic-level (list (ml4pg-compute-tactic-result))))
		  (setf ml4pg-saved-theorems (append ml4pg-saved-theorems 
					       (list (list name (ml4pg-flat (reverse result))))))))
	  (pos_space
	   (progn (setf ts (ml4pg-get-top-symbol))
		  (setf ng (ml4pg-get-number-of-goals))
		  (proof-assert-next-command-interactive)
		  (setf ng2 (ml4pg-get-number-of-goals))
		  (cond ((< ng ng2) (ml4pg-export-theorem-aux 
				     (cons (ml4pg-get-numbers cmd (subseq cmd 0 pos_space) (ml4pg-get-number-of-goals) ts current-level 1) result)
				     name
				     (1+ current-level)
				     (1+ current-level)))
			((< ng2 ng) (ml4pg-export-theorem-aux 
				     (cons (ml4pg-get-numbers cmd (subseq cmd 0 pos_space) (ml4pg-get-number-of-goals) ts current-level 0) result)
				     name
				     dot-level
				     nil))
			(t (ml4pg-export-theorem-aux 
			    (cons (ml4pg-get-numbers cmd (subseq cmd 0 pos_space) (ml4pg-get-number-of-goals) ts current-level 0) result)
			    name
			    (1+ current-level)
			    dot-level)))))
	  (t (progn (setf ts (ml4pg-get-top-symbol))
		    (setf ng (ml4pg-get-number-of-goals))
		    (proof-assert-next-command-interactive)
		    (setf ng2 (ml4pg-get-number-of-goals))
		    (cond ((< ng ng2) (ml4pg-export-theorem-aux
				       (cons (ml4pg-get-numbers cmd (subseq cmd 0 pos_dot) (ml4pg-get-number-of-goals) ts current-level 1) result)
				       name
				       (1+ current-level)
				       (1+ current-level)))
			((< ng2 ng) (ml4pg-export-theorem-aux 
				     (cons (ml4pg-get-numbers cmd (subseq cmd 0 pos_dot) (ml4pg-get-number-of-goals) ts current-level 0) result) 
				     name
				     dot-level
				     nil))
			(t (ml4pg-export-theorem-aux
			    (cons (ml4pg-get-numbers cmd (subseq cmd 0 pos_dot) (ml4pg-get-number-of-goals) ts current-level 0) result)
			    name
			    (1+ current-level)
			    dot-level))
			)
		    ))))))
     




;;; Functions to save the files

(defun ml4pg-save-file-conventions1 ()
  (interactive)
  (let ((file (read-file-name "Save in file (don't include the extension): ")))
    (progn (with-temp-file (concat file "_goals.csv") (insert (ml4pg-extract-features-1)))
	   (with-temp-file (concat file "_proof_tree.csv") (insert (ml4pg-extract-features-2 proof-tree-level)))
	   (with-temp-file (concat file "_tactic.csv") (insert (ml4pg-extract-features-2 tactic-level)))
	   (with-temp-file (concat file (format "_summary.txt")) (insert (ml4pg-extract-names))))))

	 
(defun ml4pg-extract-names ()
  (do ((temp ml4pg-saved-theorems (cdr temp))
       (temp2 "")
       (i 1 (1+ i)))
      ((endp temp) temp2)
    (setf temp2 (concat temp2 (format "%s . %s\n" i (caar temp))) )))


(defun ml4pg-print-list (list)
  (do ((temp list (cdr temp))
       (temp2 ""))
      ((endp temp) (subseq temp2 0 (1- (length temp2))))
    (setf temp2 (concat temp2 (format "%s," (car temp))) )))


(defun ml4pg-extract-features-1 ()
  (let ((fm (ml4pg-find-max-length)))
    (do ((temp ml4pg-saved-theorems (cdr temp))
	 (temp2 ""))
	((endp temp) temp2)
      (if (< (length (cadar temp)) fm)
	  (setf temp2 (concat temp2 
			      (format "%s\n"
				      (ml4pg-print-list (ml4pg-take-30 (append (cadar temp) 
							  (ml4pg-generate-zeros (- fm (length (cadar temp)))))) ))))
	(setf temp2 (concat temp2 (format "%s\n" (ml4pg-print-list (ml4pg-take-30 (cadar temp))) )))))
    ))



(defun ml4pg-extract-features-2 (list)
  (do ((temp list (cdr temp))
       (temp2 ""))
      ((endp temp) temp2)
      (setf temp2 (concat temp2 (format "%s\n" (ml4pg-print-list (car temp)))))))
      


(defun ml4pg-generate-zeros (n)
  (do ((i 0 (1+ i))
       (temp nil (cons 0 temp)))
      ((= i n) temp)))

(defun ml4pg-find-max-length ()
  (do ((temp ml4pg-saved-theorems (cdr temp))
       (i 0))
      ((endp temp) i)
    (if (< i (length (cadar temp)))
	(setf i (length (cadar temp)))
      nil)))

(defun ml4pg-take-30 (list)
  (do ((i 0 (1+ i))
       (temp list (cdr temp))
       (temp2 nil (cons (car temp) temp2)))
      ((= i 30) (reverse temp2))))


;; Function which extract the info of a theorem up to a concrete point

(defun ml4pg-extract-info-up-to-here ()
  (interactive)
  (setf ml4pg-tdl1 nil 
	ml4pg-tdl2 nil
	ml4pg-tdl3 nil
	ml4pg-tdl4 nil
	ml4pg-tdl5 nil
	ml4pg-intro nil
	ml4pg-case nil
	ml4pg-simpltrivial nil
	ml4pg-induction nil
	ml4pg-simpl nil
	ml4pg-rewrite nil
	ml4pg-trivial nil)
  (let ((final (point))
	(result nil)
	(current-level 1))
    (search-backward "Proof.")
    (proof-goto-point)
    (while (< (point) final)
      (let* ((semis (save-excursion
		      (skip-chars-backward " \t\n"
					   (proof-queue-or-locked-end))
		      (proof-segment-up-to-using-cache (point))))
	     (comment (caar semis))
	     (cmd (cadar semis))
	     (pos_dot (search "." cmd))
	     (pos_space (search " " cmd))
	     (ts nil))
	(cond (pos_space
	       (progn (setf ts (ml4pg-get-top-symbol))
		  (setf ng (ml4pg-get-number-of-goals))
		  (proof-assert-next-command-interactive)
		  (setf ng2 (ml4pg-get-number-of-goals))
		  (cond ((< ng ng2) (progn (setf result (cons (ml4pg-get-numbers2 cmd (subseq cmd 0 pos_space) (ml4pg-get-number-of-goals) ts current-level 1) result))
					   (setf current-level (1+ current-level))))
			((< ng2 ng) (progn (setf result (cons (ml4pg-get-numbers2 cmd (subseq cmd 0 pos_space) (ml4pg-get-number-of-goals) ts current-level 0) result))
					   (setf current-level (1+ current-level))))
			(t (progn (setf result (cons (ml4pg-get-numbers2 cmd (subseq cmd 0 pos_space) (ml4pg-get-number-of-goals) ts current-level 0) result))
				  (setf current-level (1+ current-level)))))))
	      (t (progn (setf ts (ml4pg-get-top-symbol))
			(setf ng (ml4pg-get-number-of-goals))
			(proof-assert-next-command-interactive)
			(setf ng2 (ml4pg-get-number-of-goals))
		    (cond ((< ng ng2) (progn (setf result (cons (ml4pg-get-numbers2 cmd (subseq cmd 0 pos_dot) (ml4pg-get-number-of-goals) ts current-level 1) result))
					     (setf current-level (1+ current-level))))
			  ((< ng2 ng) (progn (setf result (cons (ml4pg-get-numbers2 cmd (subseq cmd 0 pos_dot) (ml4pg-get-number-of-goals) ts current-level 0) result))
					     (setf current-level (1+ current-level))))
			  (t (progn (setf result(cons (ml4pg-get-numbers2 cmd (subseq cmd 0 pos_dot) (ml4pg-get-number-of-goals) ts current-level 0) result) )
				    (setf current-level (1+ current-level))))
			)
		    ))))	
    )


    (ml4pg-take-30 (append (ml4pg-flat (reverse result)) (ml4pg-generate-zeros 20) ))
  ))



(defun ml4pg-extract-features-1-bis (thm)
  (let ((fm (ml4pg-find-max-length)))
    (do ((temp ml4pg-saved-theorems (cdr temp))
	 (temp2 ""))
	((endp temp) (concat temp2 (format "%s\n" (ml4pg-print-list thm))))
      (if (< (length (cadar temp)) fm)
	  (setf temp2 (concat temp2 
			      (format "%s\n"
				      (ml4pg-print-list (ml4pg-take-30 (append (cadar temp) 
							  (ml4pg-generate-zeros (- fm (length (cadar temp)))))) ))))
	(setf temp2 (concat temp2 (format "%s\n" (ml4pg-print-list (ml4pg-take-30 (cadar temp))) )))))
    ))


;; Function which extract the information from all the theorems up to a point

(defun ml4pg-extract-feature-theorems ()
  (interactive)
  (let ((final (point))
	(current-level 1)
	(last-point -1))
    (ml4pg-export-theorem)
    (while (and (< (point) final) (not (= (point) last-point)))
      (progn (setq last-point (point))
	     (ml4pg-export-theorem))))
  )
    





(defun ml4pg-extract-theorems-library ()
  (interactive)
  (search-backward "Qed.")
  (forward-char)
  (forward-char)
  (forward-char)
  (forward-char)
  (let ((final (point))
	(last-point -1))
    (beginning-of-buffer)
    (proof-goto-point)
    (ml4pg-export-theorem)
    (while (and (< (point) final) (not (= (point) last-point)))
      (progn (setq last-point (point))
	     (ml4pg-export-theorem)))
    )
  
  )


 
    