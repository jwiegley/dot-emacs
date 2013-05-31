;;; This is the feature vector extraction file for SSReflect

;; Different variables which are used to store information about
;; the numbers associated with tactics, rewrite rules, types, ...

(defvar ml4pg-hypothesis nil)

(defvar ml4pg-saved-theorems nil)
(defvar ml4pg-goal-level-temp nil)
(defvar ml4pg-tactic-level nil)
(defvar ml4pg-proof-tree-level nil)

;; Variables to store the different values associated with the tactics, the
;; types or the rewrite rules

(defvar ml4pg-tactic_id '(("move"    . 1)
		    ("case"      . 2)
		    ("elim"      . 3)
		    ("apply"     . 4)
		    ("apply/"    . 5)
		    ("move/"     . -5)
		    ("case/"     . 6)
		    ("rewrite"    . 7)
		    ("exists"     . 8)
		    ("[]"         . 0)
		    ("exact"         . 9)))


(defvar ml4pg-move nil)
(defvar ml4pg-case nil)
(defvar ml4pg-elim nil)
(defvar ml4pg-apply nil)
(defvar ml4pg-apply/ nil)
(defvar ml4pg-move/ nil)
(defvar ml4pg-case/ nil)
(defvar ml4pg-rewrite nil)
(defvar ml4pg-exists nil)
(defvar ml4pg-done nil)
(defvar ml4pg-exact nil)


(defvar ml4pg-types_id '(("nat"  . -2)
		   ("Prop" . -4)
		   ("bool" . -3)
		   ("T"  . -1)
		   ("seq" . -5)))

(defvar ml4pg-types_id_n -6)
(defvar ml4pg-views_id nil)
(defvar ml4pg-theorems_id nil)

(defvar ml4pg-top-symbol-id 
  '(("forall"      . 5)
    ("@eq"         . 6)
    ("and"         . 4)
    ("iff"         . 8)
    ("or"          . 3)
    ("is_true"     . 2)
    ("reflect"     . 9)
    ))

(defvar ml4pg-top-symbol-n 10)


(defvar ml4pg-add_to 0.1)
(defvar ml4pg-start 100)

(defvar ml4pg-start_view 101)
(defvar ml4pg-start_thm 101)


(defvar ml4pg-init 0)

(defvar ml4pg-current-level 1)
(defvar ml4pg-dot-level nil) 

;;; Proof tree levels

(defvar ml4pg-tdl1 nil) 
(defvar ml4pg-tdl2 nil)
(defvar ml4pg-tdl3 nil)
(defvar ml4pg-tdl4 nil)
(defvar ml4pg-tdl5 nil)

(defun ml4pg-add-info-to-level-aux (info list)
  (if (not list)
      info
    (do ((temp list (cdr temp))
	 (temp1 info (cdr temp1))
	 (temp2 nil))
	((endp temp) temp2)
	(cond ((= (car temp) 0) (setf temp2 (append temp2 (list (car temp1)))))
	      ((= (car temp1) 0) (setf temp2 (append temp2 (list (car temp)))))
	      (t (setf temp2 (append temp2 (list (string-to-number (format "%s%s" (car temp) (car temp1)))))))))))

(defun ml4pg-add-info-to-level (info level)
  (cond ((= level 1) (setf ml4pg-tdl1 (ml4pg-add-info-to-level-aux info ml4pg-tdl1)))
	((= level 2) (setf ml4pg-tdl2 (ml4pg-add-info-to-level-aux info ml4pg-tdl2)))
	((= level 3) (setf ml4pg-tdl3 (ml4pg-add-info-to-level-aux info ml4pg-tdl3)))
	((= level 4) (setf ml4pg-tdl4 (ml4pg-add-info-to-level-aux info ml4pg-tdl4)))
	((= level 5) (setf ml4pg-tdl5 (ml4pg-add-info-to-level-aux info ml4pg-tdl5)))
	(t nil)
  ))

;;; Main function of this file, it is in charge of extracting the
;;; information associated with a theorem 


(defun ml4pg-export-theorem ()
  (interactive)
  (progn (setf ml4pg-tdl1 nil 
	       ml4pg-tdl2 nil
	       ml4pg-tdl3 nil
	       ml4pg-tdl4 nil
	       ml4pg-tdl5 nil
	       ml4pg-move nil
	       ml4pg-case nil
	       ml4pg-elim nil
	       ml4pg-apply nil
	       ml4pg-apply/ nil
	       ml4pg-move/ nil
	       ml4pg-case/ nil
	       ml4pg-rewrite nil
	       ml4pg-exists nil
	       ml4pg-done nil
	       ml4pg-exact nil
	       ml4pg-current-level 1
	       ml4pg-dot-level nil
	       ml4pg-hypothesis nil
	       ml4pg-goal-level nil)
	 (if (equal ml4pg-init 0)
	     (progn (ml4pg-read-lemmas)
		    (ml4pg-read-views)
		    (setq ml4pg-init 1)))
	 (ml4pg-export-theorem-aux nil nil)
	 (proof-shell-invisible-cmd-get-result (format "Unset Printing All"))
	   ))



;; A function to obtain the type associated with an object

(defun ml4pg-remove-jumps-aux (string res)
  (let ((jump (search "
" string)))
    (if jump
	(ml4pg-remove-jumps-aux (subseq string (1+ jump)) (concatenate 'string res (subseq string 0 jump)))
      (concatenate 'string res string))))

(defun ml4pg-remove-jumps (string)
  (ml4pg-remove-jumps-aux string ""))


(defun ml4pg-get-type-id (object)
  (if (string= "(" (subseq object 0 1))
      -4
  (let* ((a (ml4pg-remove-jumps (proof-shell-invisible-cmd-get-result (concat "Check " object))))
	 (pos_jump (search "
" a :start2 (+ 2 (search " " a))))
	 (pos_space (search " " a :start2 (+ 2 (search ": " a))))
	 (type (if pos_space
		   (cdr (assoc (subseq a (+ 2 (search ": " a)) pos_space) ml4pg-types_id))
		 (cdr (assoc (subseq a (+ 2 (search ": " a)) pos_jump) ml4pg-types_id)))))
    (if type type 
      (progn (setf ml4pg-types_id
		   (append ml4pg-types_id  (list (cons  (if pos_space
						      (subseq a (+ 2 (search ": " a)) pos_space)
						    (subseq a (+ 2 (search ": " a)) pos_jump))
						  ml4pg-types_id_n))))
	     
	     (setf ml4pg-types_id_n (1- ml4pg-types_id_n))
	     (1+ ml4pg-types_id_n))
      ))))

(defun ml4pg-get-type-id2 (object)
  (let* ((a (proof-shell-invisible-cmd-get-result (concat "Check " object)))
	 (pos_jump (search "
" a :start2 (+ 2 (search " " a))))
	 (pos_space (search " " a :start2 (+ 2 (search ": " a))))
	 (type (if pos_space
		   (cdr (assoc (subseq a (+ 2 (search ": " a)) pos_space) ml4pg-types_id))
		 (cdr (assoc (subseq a (+ 2 (search ": " a)) pos_jump) ml4pg-types_id)))))
    (if type type 
      (progn (setf ml4pg-types_id
		   (append ml4pg-types_id  (list (cons  (if pos_space
						      (subseq a (+ 2 (search ": " a)) pos_space)
						    (subseq a (+ 2 (search ": " a)) pos_jump))
						  ml4pg-types_id_n))))
	     
	     (setf ml4pg-types_id_n (1- ml4pg-types_id_n))
	     (1+ ml4pg-types_id_n))
      )))


;; A function to obtain the value of a top symbol

(defun ml4pg-get-top-symbol ()
  (proof-shell-invisible-cmd-get-result (format "Set Printing All"))
  (let* ((res (proof-shell-invisible-cmd-get-result (format "Focus")))
	(res2 (subseq res (+ 32 (search "============================" res))))
	(fst-symbol (subseq res2 0 (search " " res2))))
    (cond ((search "->" res2) 7)
	  (t (let ((is (assoc fst-symbol ml4pg-top-symbol-id)))
	       (if is
		   (cdr is)
		 (progn (setf ml4pg-top-symbol-id
			      (append  ml4pg-top-symbol-id  (list (cons fst-symbol ml4pg-top-symbol-n))))
			
			(setf ml4pg-top-symbol-n (1+ ml4pg-top-symbol-n))
			(1- ml4pg-top-symbol-n))))))))



 
;; In some cases the intro tactic does not have parameters, the following function
;; obtain the type of the object introduced with the intro tactic in those cases
;; Sobra
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
    (if (search "_" (car list))
	(ml4pg-get-types-list (cdr list) res)
    (ml4pg-get-types-list (cdr list) (+ (* -1 (ml4pg-get-type-id (car list)) (expt 10 (- (length list) 1))) res)))))


(defun ml4pg-get-types-list-exists (list res)
  (if (endp list)
      (* -1 res)
    (ml4pg-get-types-list-exists (cdr list) (+ (* -1 (ml4pg-get-type-id2 (car list)) (expt 10 (- (length list) 1))) res))))

;; To obtain the number of tactics applied

(defun ml4pg-get-number-list (list)
  (if (endp list)
      0
    (+ (expt 10 (- (length list) 1))  (ml4pg-get-number-list (cdr list)))))

(defun ml4pg-get-number-list2 (list n)
  (if (endp list)
      0
    (+ (* n (expt 10 (- (length list) 1)))  (ml4pg-get-number-list2 (cdr list) n))))

;; To obtain the value associated with top symbol in the case of move

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

;; To obtain the value associated with a theorem

(defun ml4pg-search-in-hyp (obj hyp)
  (if (endp hyp)
      nil
    (if (string= obj (car hyp))
	t
      (ml4pg-search-in-hyp obj (cdr hyp)))))

;;; Auxiliary functions 

(defun ml4pg-remove=> (string)
  (let ((d (search "=>" string)))
    (if d
	(ml4pg-remove=> (concatenate 'string (subseq string 0 d) (subseq string (+ 2 d))))
      string)))


(defun ml4pg-extract-views (list)
  (do ((temp list (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (if (and (string= (subseq (car temp) 0 1) "/") (not (string= (car temp) "//")) (not (string= (car temp) "/=")) (not (string= (car temp) "//=")))
	  (if (not (string= (subseq (car temp) 0 2) "/("))
	      (setf temp2 (append temp2 (list (subseq (car temp) 1))))
	    (setf temp2 (append temp2 (list (subseq (car temp) 2 (search " " (car temp))))))))))


(defun ml4pg-extract-real-params (list)
  (do ((temp list (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (if (not (or (string= (subseq (car temp) 0 1) "/") (string= (car temp) "//") (string= (car temp) "_") 
		   (search "->" (car temp)) (search "<-" (car temp)) (string= (car temp) "/=") (string= (car temp) "//=")))
	  (setf temp2 (append temp2 (list (car temp)))))))

(defun ml4pg-extract-rewrites (list)
  (do ((temp list (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (if (or (search "->" (car temp)) (search "<-" (car temp)))
	  (setf temp2 (append temp2 (list (car temp)))))))

(defun ml4pg-extract-simplifications (list)
  (do ((temp list (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (if (or (string= (car temp) "//") (string= (car temp) "/=") (string= (car temp) "//="))
	  (setf temp2 (append temp2 (list (car temp)))))))

(defun ml4pg-compute-value-simpl (list)
  (list 0 (length list) 0 0))


(defun ml4pg-extract-views-id (list)
  (do ((temp list (cdr temp))
       (temp2 ""))
      ((endp temp) temp2)
      (if (assoc (car temp) ml4pg-views_id)
	  (setf temp2 (concatenate 'string temp2 (format "%s" (cdr (assoc (car temp) ml4pg-views_id))) ))
	(progn (setf ml4pg-start_view (+ ml4pg-start_view 1)) 
	       (ml4pg-save-view (car temp) ml4pg-start_view)
	       (setf ml4pg-views_id 
		     (append ml4pg-views_id (list (cons (car temp) ml4pg-start_view))))
	       (setf temp2 (concatenate 'string temp2 (format "%s" (cdr (assoc (car temp) ml4pg-views_id)))))))))



(defun ml4pg-compute-values-rewrite-tactic (list)
  (do ((temp (ml4pg-extract-real-params list) (cdr temp))
       (temp2 ""))
      ((endp temp) (string-to-number temp2))
      (let* ((obj1 (if (string= "-" (subseq (car temp) 0 1)) (subseq (car temp) 1) (car temp)))
	     (obj (if (string= "(" (subseq obj1 0 1)) (subseq obj1 1 (search " " obj1)) obj1)))
      (if (assoc obj ml4pg-theorems_id)
	  (setf temp2 (concatenate 'string temp2 (format "%s" (cdr (assoc obj ml4pg-theorems_id)))) )
	(progn (setf ml4pg-start_thm (+ ml4pg-start_thm 1)) 
	       (ml4pg-save-lemma obj ml4pg-start_thm)
	       (setf ml4pg-theorems_id 
		     (append ml4pg-theorems_id (list (cons obj ml4pg-start_thm))))
	       (setf temp2 (concatenate 'string temp2 (format "%s" (cdr (assoc obj ml4pg-theorems_id))))))))))


(defun ml4pg-compute-values-apply-tactic (list)
  (do ((temp list (cdr temp))
       (temp2 ""))
      ((endp temp) (string-to-number temp2))
      (let ((obj (if (string= "(" (subseq (car temp) 0 1)) (subseq (car temp) 1) (car temp))))
	(if (member obj ml4pg-hypothesis)
	    (setf temp2 (concatenate 'string temp2 "1"))
	  (if (assoc obj ml4pg-theorems_id)
	      (setf temp2 (concatenate 'string temp2 (format "%s" (cdr (assoc obj ml4pg-theorems_id)))) )
	    (progn (setf ml4pg-start_thm (+ ml4pg-start_thm 1)) 
		   (setf ml4pg-theorems_id 
			 (append ml4pg-theorems_id (list (cons obj ml4pg-start_thm))))
		   (setf temp2 (concatenate 'string temp2 (format "%s" (cdr (assoc obj ml4pg-theorems_id)))))))))))


(defun ml4pg-compute-value-views-move (list)
  (list (* -1 (ml4pg-get-number-list2 list 5)) (length list) (* -1 (ml4pg-get-number-list2 list 4)) (string-to-number (ml4pg-extract-views-id list))))

(defun ml4pg-compute-value-views-apply (list)
  (list  (ml4pg-get-number-list2 list 5) (length list) (* -1 (ml4pg-get-number-list2 list 4)) (string-to-number (ml4pg-extract-views-id list))))

(defun ml4pg-compute-value-views-case (list)
  (list  (ml4pg-get-number-list2 list 6) (length list) (* -1 (ml4pg-get-number-list2 list 4)) (string-to-number (ml4pg-extract-views-id list))))

(defun ml4pg-compute-value-views-exact (list)
  (list  (ml4pg-get-number-list2 list 9) (length list) (* -1 (ml4pg-get-number-list2 list 4)) (string-to-number (ml4pg-extract-views-id list))))

(defun ml4pg-compute-value-rewrites (list)
  (list (ml4pg-get-number-list2 list 7) (length list) (* -1 (ml4pg-get-number-list2 list 4)) (ml4pg-get-number-list list)))



(defun ml4pg-remove-empties (list)
  (do ((temp list (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (if (not (string= (car temp) ""))
	  (setf temp2 (append temp2 (list (car temp)))))))



(defun ml4pg-occurrences (c string)
  (do ((temp string)
       (n 0))
      ((not (search c temp)) n)
      (progn (setf n (1+ n))
	     (setf temp (subseq temp (1+ (search c temp)))))))
       

(defun ml4pg-put-together-parenthesis (list)
  (do ((temp list (cdr temp))
       (n 0)
       (temp2 nil)
       (aux ""))
      ((endp temp) temp2)
      (cond ((search "(" (car temp)) 
	     (progn (setf n (1+ n))
		    (setf aux (concatenate 'string aux (car temp) " "))))
	    ((and (search ")" (car temp)) (not (= (- n (ml4pg-occurrences ")" (car temp))) 0)))
	     (progn (setf n (- n (ml4pg-occurrences ")" (car temp))))
		    (setf aux (concatenate 'string aux (car temp) " "))))
	    ((search ")" (car temp))
	     (progn (setf n (1- n))
		    (setf aux (concatenate 'string aux (car temp)))
		    (setf temp2 (append temp2 (list aux)))
		    (setf aux "")))
	    ((not (= n 0))
	     (progn (setf aux (concatenate 'string aux (car temp) " "))))
	    (t (setf temp2 (append temp2 (list (car temp))))
	    ))))
	    
		     
(defun ml4pg-remove-squared-parenthesis (string res)
  (let ((pos1 (search "[" string))
	(pos2 (search "{" string)))
    (cond ((and pos1 pos2)
	   (if (< pos1 pos2)
	       (ml4pg-remove-squared-parenthesis
		(subseq string (1+ (search "]" string :start2 pos1)))
		(concatenate 'string res (subseq string 0 pos1)))
	     (ml4pg-remove-squared-parenthesis
	      (subseq string (1+ (search "}" string :start2 pos2)))
	      (concatenate 'string res (subseq string 0 pos2)))))
	  (pos1 (ml4pg-remove-squared-parenthesis
		(subseq string (1+ (search "]" string :start2 pos1)))
		(concatenate 'string res (subseq string 0 pos1))))
	  (pos2 (ml4pg-remove-squared-parenthesis
		 (subseq string (1+ (search "}" string :start2 pos2)))
		 (concatenate 'string res (subseq string 0 pos2))))
	  (t (concatenate 'string res string)))))


(defun ml4pg-remove-iterations (string)
  (do ((temp string)
       (temp2 ""))
      ((= (length temp) 0) temp2)
      (if (or (string= (subseq temp 0 1) "!") (string= (subseq temp 0 1) "?"))
	  (setf temp (subseq temp 1))
	(progn (setf temp2 (concatenate 'string temp2 (subseq temp 0 1)))
	       (setf temp (subseq temp 1))
	       ))))


      
(defun ml4pg-remove-squared-parenthesis2 (string)
  (do ((temp string)
       (temp2 ""))
      ((= (length temp) 0) temp2)
      (if (or (string= (subseq temp 0 1) "[") (string= (subseq temp 0 1) "]") (string= (subseq temp 0 1) "|"))
	  (setf temp (subseq temp 1))
	(progn (setf temp2 (concatenate 'string temp2 (subseq temp 0 1)))
	       (setf temp (subseq temp 1))
	       ))))
		
	   
(defun ml4pg-extract-params3 (cmd)
 (let* ((res (ml4pg-extract-params2 (ml4pg-remove-iterations (ml4pg-remove-squared-parenthesis cmd "") ) nil))
	(res1 (ml4pg-remove-empties res)))
   (ml4pg-put-together-parenthesis res1)))


(defun ml4pg-extract-params4 (cmd)
 (let* ((res (ml4pg-extract-params2 (ml4pg-remove-squared-parenthesis2 cmd) nil))
	(res1 (ml4pg-remove-empties res)))
   (ml4pg-put-together-parenthesis res1)))



;;; The following functions provide the numbers associated with a concrete tactic


(defun ml4pg-numbers-move=> (cmd top level)
  (let* ((params (ml4pg-extract-params3 (ml4pg-remove=> (subseq cmd (+ 2 (search "=>" cmd)))) ))
	 (views (ml4pg-extract-views params))
	 (simpl (ml4pg-extract-simplifications params))
	 (rewrites (ml4pg-extract-rewrites params))
	 (rewrites-nums (ml4pg-compute-value-rewrites rewrites))
	 (simpl-nums (ml4pg-compute-value-simpl simpl))
	 (views-nums (ml4pg-compute-value-views-move views))
	 (real-params (ml4pg-extract-real-params params))
	 (foo (setf ml4pg-hypothesis (append ml4pg-hypothesis real-params)))
	 (types-params (ml4pg-get-types-list real-params 0))
	 (foo3 (ml4pg-add-info-to-level (list (ml4pg-get-types-list real-params 0) 0 0 0 0 0 0 0 0 0 0 0 0) level))
	 (foo2 (setf ml4pg-move (append ml4pg-move (list (list (ml4pg-get-types-list (if real-params (list (car real-params)) nil) 0)  (ml4pg-get-types-list (cdr real-params) 0)
						   (* -1 (ml4pg-get-number-list real-params)) top))))))
    (append (list (list (ml4pg-get-number-list2 real-params (cdr (assoc "move" ml4pg-tactic_id))) (length real-params) types-params (* -1 (ml4pg-get-number-list real-params))))
	  (if simpl (list simpl-nums) nil)
	  (if views (list views-nums) nil)
	  (if rewrites (list rewrites-nums) nil))))

(defun ml4pg-numbers-move/ (cmd top level)
  (let* ((params (ml4pg-extract-params3 (ml4pg-remove=> (subseq cmd 4)) ))
	 (views (ml4pg-extract-views params))
	 (simpl (ml4pg-extract-simplifications params))
	 (rewrites (ml4pg-extract-rewrites params))
	 (rewrites-nums (ml4pg-compute-value-rewrites rewrites))
	 (simpl-nums (ml4pg-compute-value-simpl simpl))
	 (views-nums (ml4pg-compute-value-views-move views))
	 (real-params (ml4pg-extract-real-params params))
	 (foo (setf ml4pg-hypothesis (append ml4pg-hypothesis real-params)))
	 (foo3 (ml4pg-add-info-to-level (list 0 0 0 0 0 (nth 2 views-nums) 0 0 0 0 0 0 0) level))
	 (foo2 (setf ml4pg-move/ (append ml4pg-move/ (list (list -4  (* -4 (ml4pg-get-number-list real-params))  (nth 3 views-nums) top)))))
	 (types-params (ml4pg-get-types-list real-params 0)))
    (append (list views-nums) 
	    (if real-params (list (list (ml4pg-get-number-list2 real-params (cdr (assoc "move" ml4pg-tactic_id))) (length real-params) types-params (* -1 (ml4pg-get-number-list real-params)))))
	    (if simpl (list simpl-nums) nil)
	    (if rewrites (list rewrites-nums) nil)))
)

(defun ml4pg-numbers-move: (cmd top level)
  (let* ((params (ml4pg-extract-params3 (subseq cmd (+ 1 (search ":" cmd)))) )
	 (views (ml4pg-extract-views params))
	 (simpl (ml4pg-extract-simplifications params))
	 (rewrites (ml4pg-extract-rewrites params))
	 (rewrites-nums (ml4pg-compute-value-rewrites rewrites))
	 (simpl-nums (ml4pg-compute-value-simpl simpl))
	 (views-nums (ml4pg-compute-value-views-move views))
	 (real-params (ml4pg-extract-real-params params))
	 (types-params (ml4pg-get-types-list real-params 0))
	 (foo3 (ml4pg-add-info-to-level (list (ml4pg-get-types-list real-params 0) 0 0 0 0 0 0 0 0 0 0 0 0) level))
	 (foo2 (setf ml4pg-move (append ml4pg-move (list (list (ml4pg-get-types-list (if real-params (list (car real-params)) nil) 0)  (ml4pg-get-types-list (cdr real-params) 0)
						   (* 1 (ml4pg-get-number-list real-params)) top))))))
    (append (list (list (* -1 (ml4pg-get-number-list2 real-params (cdr (assoc "move" ml4pg-tactic_id)))) (length real-params) types-params (* -1 (ml4pg-get-number-list real-params))))
	    (if views (list views-nums) nil)
	    (if simpl (list simpl-nums) nil)
	    (if rewrites (list rewrites-nums) nil)))

)

(defun ml4pg-numbers-move< (cmd top level)
  (let* ((foo (list (ml4pg-compute-value-rewrites (list 1))))
	 (foo3 (ml4pg-add-info-to-level (list 0 0 0 0 0 0 0 top 0 0 0 0 0) level))
	 (foo2 (setf ml4pg-rewrite (append ml4pg-rewrite (list (list 4 0 1 top))))))
    foo
    )
)

(defun ml4pg-numbers-apply: (cmd top level)
  (if (string= cmd "apply")
      (list (list (cdr (assoc "apply" ml4pg-tactic_id)) 1 0 0))
  (let ((moves (search "=>" cmd))
	(foo3 (ml4pg-add-info-to-level (list 0 0 0 100 0 0 0 0 0 0 0 0 0) level))
	(foo2 (setf ml4pg-apply (append ml4pg-apply (list (list -4  0 100 top))))))
    (if (not moves)
	(list (list (cdr (assoc "apply" ml4pg-tactic_id))
	      1 
	      -4
	      (ml4pg-compute-values-apply-tactic (ml4pg-extract-real-params (ml4pg-extract-params3 (subseq cmd (+ 1 (if (search ":" cmd) (search ":" cmd) (search " " cmd)))))))))
      (let* ((args0 (ml4pg-extract-params4 (subseq cmd (+ 2 moves))))
	    (simpl (ml4pg-extract-simplifications args0))
	    (simpl-nums (ml4pg-compute-value-simpl simpl))
	    (args (ml4pg-extract-real-params args0))
	    )
      (append (list (list (cdr (assoc "apply" ml4pg-tactic_id))
			  1 -4 
			  (ml4pg-compute-values-apply-tactic (ml4pg-extract-real-params (ml4pg-extract-params3 (subseq cmd (+ 1 (if (search ":" cmd) (search ":" cmd) (search " " cmd))) moves))))
			  ))
	      (list (list (* -1 (ml4pg-get-number-list2 args (cdr (assoc "move" ml4pg-tactic_id)))) (length args) (ml4pg-get-types-list args 0) (* -1 (ml4pg-get-number-list args))))
	      (if simpl (list simpl-nums) nil)))))
))

(defun ml4pg-numbers-elim (cmd top level)
  (let* ((moves (search "=>" cmd))
	 (foo3 (ml4pg-add-info-to-level (list 0 0 (ml4pg-get-types-list (list (car (ml4pg-extract-real-params (ml4pg-extract-params3 (subseq cmd (+ 1 (search ":" cmd)) moves))))) 0) 0 0 0 0 0 0 0 0 0 0) level))
	(foo2 (setf ml4pg-elim (append ml4pg-elim (list (list (ml4pg-get-types-list (list (car (ml4pg-extract-real-params (ml4pg-extract-params3 (subseq cmd (+ 1 (search ":" cmd)) moves))))) 0)  0 -1 top))))))
    (if (not moves)
	(list (list (cdr (assoc "elim" ml4pg-tactic_id))
	      1 (ml4pg-get-types-list (ml4pg-extract-real-params (ml4pg-extract-params3 (subseq cmd (+ 1 (search ":" cmd))))) 0) -1))
      (let* ((args0 (ml4pg-extract-params4 (subseq cmd (+ 2 moves))))
	    (simpl (ml4pg-extract-simplifications args0))
	    (simpl-nums (ml4pg-compute-value-simpl simpl))
	    (args (ml4pg-extract-real-params args0)))
      (append (list (list (cdr (assoc "elim" ml4pg-tactic_id))
			  1 (ml4pg-get-types-list (ml4pg-extract-real-params (ml4pg-extract-params3 (subseq cmd (+ 1 (search ":" cmd)) moves))) 0) -1))
	      (list (list (* -1 (ml4pg-get-number-list2 args (cdr (assoc "move" ml4pg-tactic_id)))) (length args) (ml4pg-get-types-list args 0) (* -1 (ml4pg-get-number-list args))))
	      (if simpl (list simpl-nums) nil))))))

(defun ml4pg-numbers-case (cmd top level)
  (if (string= cmd "case")
      (list (list (cdr (assoc "case" ml4pg-tactic_id)) 1 0 0))
  (let ((moves (search "=>" cmd))
	(foo3 (ml4pg-add-info-to-level (list 0 (if (ml4pg-extract-real-params (ml4pg-extract-params3 (if (search ":" cmd) (subseq cmd (+ 1 (search ":" cmd))) (subseq cmd (+ 1 (search " " cmd))))))
						   (ml4pg-get-types-list (list (car (ml4pg-extract-real-params (ml4pg-extract-params3 (if (search ":" cmd) (subseq cmd (+ 1 (search ":" cmd))) (subseq cmd (+ 1 (search " " cmd)))))))) 0) 1) 0 0 0 0 0 0 0 0 0 0 0) level))
	(foo2 (setf ml4pg-case (append ml4pg-case (list (list (if (ml4pg-extract-real-params (ml4pg-extract-params3 (if (search ":" cmd) (subseq cmd (+ 1 (search ":" cmd))) (subseq cmd (+ 1 (search " " cmd))))))
						      (ml4pg-get-types-list (list (car (ml4pg-extract-real-params (ml4pg-extract-params3 (if (search ":" cmd) (subseq cmd (+ 1 (search ":" cmd))) (subseq cmd (+ 1 (search " " cmd)))))))) 0) 1)
  0 -1 top))))))
    (if (not moves)
	(list (list (cdr (assoc "case" ml4pg-tactic_id))
	      1 (ml4pg-get-types-list (ml4pg-extract-real-params (ml4pg-extract-params3 (if (search ":" cmd) (subseq cmd (+ 1 (search ":" cmd))) (subseq cmd (+ 1 (search " " cmd)))))) 0) -1))
      (let* ((args0 (ml4pg-extract-params4 (subseq cmd (+ 2 moves))))
	    (simpl (ml4pg-extract-simplifications args0))
	    (simpl-nums (ml4pg-compute-value-simpl simpl))
	    (args (ml4pg-extract-real-params args0)))
	(if (ml4pg-extract-params3 (if (search ":" cmd) (subseq cmd (+ 1 (search ":" cmd))) (subseq cmd (+ 1 (search " " cmd)))))
	    (append (list (list (cdr (assoc "case" ml4pg-tactic_id))
				1 (ml4pg-get-types-list (ml4pg-extract-real-params (ml4pg-extract-params3 (if (search ":" cmd) (subseq cmd (+ 1 (search ":" cmd))) (subseq cmd (+ 1 (search " " cmd)))))) 0) -1))
		    (list (list (* -1 (ml4pg-get-number-list2 args (cdr (assoc "move" ml4pg-tactic_id)))) (length args) (ml4pg-get-types-list args 0) (* -1 (ml4pg-get-number-list args))))
		    (if simpl (list simpl-nums) nil))
	  (append (list (list (cdr (assoc "case" ml4pg-tactic_id))
				1 0 0))
		    (list (list (* -1 (ml4pg-get-number-list2 args (cdr (assoc "move" ml4pg-tactic_id)))) (length args) (ml4pg-get-types-list args 0) (* -1 (ml4pg-get-number-list args))))
		    (if simpl (list simpl-nums) nil))))))))

(defun ml4pg-numbers-case/ (cmd top level)
  (let* ((params (ml4pg-extract-params4 (ml4pg-separate-/ (ml4pg-remove=> (subseq cmd 5)) "")))
	 (views (ml4pg-extract-views params))
	 (simpl (ml4pg-extract-simplifications params))
	 (rewrites (ml4pg-extract-rewrites params))
	 (rewrites-nums (ml4pg-compute-value-rewrites rewrites))
	 (simpl-nums (ml4pg-compute-value-simpl simpl))
	 (views-nums (ml4pg-compute-value-views-case views))
	 (real-params (ml4pg-extract-real-params params))
	 (foo (setf ml4pg-hypothesis (append ml4pg-hypothesis real-params)))
	 (types-params (ml4pg-get-types-list real-params 0))
	 (foo3 (ml4pg-add-info-to-level (list 0 0 0 0 0 0 (nth 2 views-nums) 0 0 0 0 0 0) level))
	 (foo2 (setf ml4pg-case/ (append ml4pg-case/ (list (list -4  (/ (nth 2 views-nums) 10)  (nth 3 views-nums) top))))))
    (append (list views-nums)
	    (if real-params (list (list (ml4pg-get-number-list2 real-params (cdr (assoc "move" ml4pg-tactic_id))) (length real-params) types-params (* -1 (ml4pg-get-number-list real-params)))))
	    (if simpl (list simpl-nums) nil)
	    (if rewrites (list rewrites-nums) nil)))
)

(defun ml4pg-separate-/ (string res)
  (let ((pos (search "/" string)))
    (if (not pos)
	(concatenate 'string res string)
      (cond ((= pos 0) (ml4pg-separate-/ (subseq string (1+ pos)) (concatenate 'string "/" res (subseq string 0 pos))))
	    ((not (string= " " (subseq string (1- pos) pos))) 
	     (ml4pg-separate-/ (subseq string (1+ pos)) (concatenate 'string res (subseq string 0 pos) " /")))
	    (t (ml4pg-separate-/ (subseq string (1+ pos)) (concatenate 'string res (subseq string 0 pos))))))))
     

(defun ml4pg-numbers-apply/ (cmd top level)
  (let* ((params (ml4pg-extract-params4 (ml4pg-separate-/ (ml4pg-remove=> (subseq cmd 5)) "")))
	 (views (ml4pg-extract-views params))
	 (simpl (ml4pg-extract-simplifications params))
	 (rewrites (ml4pg-extract-rewrites params))
	 (rewrites-nums (ml4pg-compute-value-rewrites rewrites))
	 (simpl-nums (ml4pg-compute-value-simpl simpl))
	 (views-nums (ml4pg-compute-value-views-apply views))
	 (real-params (ml4pg-extract-real-params params))
	 (foo (setf ml4pg-hypothesis (append ml4pg-hypothesis real-params)))
	 (types-params (ml4pg-get-types-list real-params 0))
	 (foo3 (ml4pg-add-info-to-level (list 0 0 0 0 (nth 2 views-nums) 0 0 0 0 0 0 0 0) level))
	 (foo2 (setf ml4pg-apply/ (append ml4pg-apply/ (list (list -4  (/ (nth 2 views-nums) 10)  (nth 3 views-nums) top))))))
    (append (list views-nums)
	    (if real-params (list (list (ml4pg-get-number-list2 real-params (cdr (assoc "move" ml4pg-tactic_id))) (length real-params) types-params (* -1 (ml4pg-get-number-list real-params)))))
	    (if simpl (list simpl-nums) nil)
	    (if rewrites (list rewrites-nums) nil)))
)

(defun ml4pg-numbers-exact (cmd top level)
  (if (string= cmd "exact")
      (list (list (cdr (assoc "exact" ml4pg-tactic_id)) 1 0 0))
  (let* ((params (ml4pg-extract-params3 (cond ((search ":" cmd) (subseq cmd (+ 1 (search ":" cmd))))
					((search "/" cmd) (subseq cmd (search "/" cmd)))
					(t (subseq cmd (+ 1 (search " " cmd)))))))
	(views (ml4pg-extract-views params))
	(views-nums (ml4pg-compute-value-views-exact views))
	(foo3 (ml4pg-add-info-to-level (list 0 0 0 0 0 0 0 0 0 0 100 0 0) level))
	(foo2 (setf ml4pg-exact (append ml4pg-exact (list (list -4  0 100 top))))))
    (if views 
	(list views-nums)
    (list (list (cdr (assoc "exact" ml4pg-tactic_id))
	      1 
	      -4
	      (ml4pg-compute-values-apply-tactic (ml4pg-extract-real-params params))))))))

(defun ml4pg-numbers-rewrite (cmd top level)
  (let* ((params (ml4pg-extract-params3 (subseq cmd (+ 1 (search " " cmd)))) )
	 (views (ml4pg-extract-views params))
	 (simpl (ml4pg-extract-simplifications params))
	 (simpl-nums (ml4pg-compute-value-simpl simpl))
	 (views-nums (ml4pg-compute-value-views-move views))
	 (foo3 (ml4pg-add-info-to-level (list 0 0 0 0 0 0 0 (ml4pg-get-number-list2 (cdr params) 4) 0 0 0 0 0) level))
	 (foo2 (setf ml4pg-rewrite (append ml4pg-rewrite (list (list -4  (ml4pg-get-number-list2 (cdr params) 4) (ml4pg-compute-values-rewrite-tactic params) top))))))
    (append (list (list (ml4pg-get-number-list2 params (cdr (assoc "rewrite" ml4pg-tactic_id)))
			(length params)
			(ml4pg-get-number-list2 params 4)
			(ml4pg-compute-values-rewrite-tactic params)))
	    (if simpl (list simpl-nums) nil)
	    ))  
)

(defun ml4pg-numbers-exists (cmd top level)
  (let ((moves (search "=>" cmd))
	(foo3 (ml4pg-add-info-to-level (list 0 0 0 0 0 0 0 0 1 0 0 0 0) level))
	(foo2 (setf ml4pg-exists (append ml4pg-exists (list (list 8 0 1 top))))))
    (if (not moves)
	(let* ((params (ml4pg-extract-params3 (subseq cmd 7)) )
	       (types-params (ml4pg-get-types-list-exists params 0))
	       )
	  (list (list (cdr (assoc "exists" ml4pg-tactic_id)) 1 types-params 0)))
      (let* ((args0 (ml4pg-extract-params4 (subseq cmd (+ 2 moves))))
	    (simpl (ml4pg-extract-simplifications args0))
	    (simpl-nums (cml4pg-ompute-value-simpl simpl))
	    (args (ml4pg-extract-real-params args0)))
      (append (list (list (cdr (assoc "exists" ml4pg-tactic_id))
			  1 (ml4pg-get-types-list-exists  (ml4pg-extract-params3 (subseq cmd 7 moves)) 0) -1))
	      (list (list (* -1 (ml4pg-get-number-list2 args (cdr (assoc "move" ml4pg-tactic_id)))) (length args) (ml4pg-get-types-list args 0) (* -1 (ml4pg-get-number-list args))))
	      (if simpl (list simpl-nums) nil)))))
  )
    

(defun ml4pg-numbers-done (cmd top level)
  (progn 
    (ml4pg-add-info-to-level (list 0 0 0 0 0 0 0 0 0 top 0 0 0) level)
    (setf ml4pg-done (append ml4pg-done (list (list 0 0 0 top))))
    (list (list (cdr (assoc "[]" ml4pg-tactic_id)) 1 0 0) ) )
)


(defun ml4pg-remove-multiple-spaces (string)
  (let ((d (search "  " string)))
    (if d
	(ml4pg-remove-multiple-spaces (concatenate 'string (subseq string 0 d) (subseq string (1+ d))))
      string)))
  


(defun ml4pg-compute-numbers-cmd (cmd top level)
  (let* ((cmd1 (ml4pg-remove-multiple-spaces cmd)))
    (cond ((search "symmetry" cmd) nil)	  
	  ((search "last by" cmd) (ml4pg-compute-numbers-cmd (subseq cmd (+ 3 (search "by" cmd))) top level))
	  ((search "first by" cmd) (ml4pg-compute-numbers-cmd (subseq cmd (+ 3 (search "by" cmd))) top level))
	  ((string= "try" (subseq cmd 0 2)) (ml4pg-compute-numbers-cmd (subseq cmd (+ 4 (search "try" cmd))) top level))
	  ((string= "do" (subseq cmd 0 2)) (ml4pg-compute-numbers-cmd (subseq cmd (cond ((search "!" cmd) (1+ (search "!" cmd)))
								    ((search "?" cmd) (1+ (search "?" cmd)))
								    (t (+ 3 (search "do" cmd))))) top level)) 
	  ((search "have" cmd) nil)
	  ((or (search "move=>" cmd1) (search "move =>" cmd1)) (ml4pg-numbers-move=> cmd1 top level))
	  ((or (search "move:" cmd1) (search "move :" cmd1)) (ml4pg-numbers-move: cmd1 top level))
	  ((or (search "move/" cmd1) (search "move /" cmd1)) (ml4pg-numbers-move/ cmd1 top level))
	  ((or (search "move<-" cmd1) (search "move->" cmd1) (search "move ->" cmd1) (search "move <-" cmd1)) (ml4pg-numbers-move< cmd1 top level))
	  ((or (search "apply/" cmd1) (search "apply /" cmd1)) (ml4pg-numbers-apply/ cmd1 top level))
	  ((or (search "apply:" cmd1) (search "apply :" cmd1) (search "apply" cmd1)) (ml4pg-numbers-apply: cmd1 top level))
	  ((or (search "elim:" cmd1) (search "elim :" cmd1)) (ml4pg-numbers-elim cmd1 top level))
	  ((or (search "case/" cmd1) (search "case /" cmd1)) (ml4pg-numbers-case/ cmd1 top level))
	  ((or (search "case:" cmd1) (search "case" cmd1)) (ml4pg-numbers-case cmd1 top level))
	  ((or (search "exact" cmd1) (search "exact :" cmd1)) (ml4pg-numbers-exact cmd1 top level))
	  ((search "rewrite" cmd1) (ml4pg-numbers-rewrite cmd1 top level))
	  ((search "exists" cmd1) (ml4pg-numbers-exists cmd1 top level))
	  ((or (search "[]" cmd1) (search "done" cmd1) (search "constructor" cmd1)) (ml4pg-numbers-done cmd1 top level))
	  
	  ((string= (subseq cmd1 0 4) "pose") nil)
	  ((string= (subseq cmd1 0 3) "set") nil)
	  ((string= (subseq cmd1 0 4) "left") nil)
	  ((string= (subseq cmd1 0 4) "righ") nil)
	  )
    )  
  ) 


(defun ml4pg-split-command (cmd result end)
  (if (or (string= " " (subseq cmd 0 1)) (string= "-" (subseq cmd 0 1)))
	  (ml4pg-split-command (subseq cmd 1) result end)
  (let ((is_by (string= "by" (subseq cmd 0 2))))
    (if is_by
	(ml4pg-split-command (subseq cmd 3) result 1)
      (let ((comma (search ";" cmd)))
	(if comma
	    (ml4pg-split-command (subseq cmd (1+ comma)) (append result (list (subseq cmd 0 comma))) end)
	  (list (append result (list (subseq cmd 0 (1- (length cmd))))) end)))))))


    
     
(defun ml4pg-add-tactics (tactics end top level)
  (do ((temp tactics (cdr temp))
       (temp2 nil))
      ((endp temp) (if (> end 0) (append temp2 (list (list 0 1 0 0))) temp2))
      (let ((res (ml4pg-compute-numbers-cmd (car temp) top level)))
	(if res (setf temp2 (append temp2 res))))))


;The first value is the tactic, the second one is the number of tactics,
;the third one is the argument type, the fourth one is if the
;argument is a hypothesis of a theorem, the fifth one is the top-symbol
;and the last one the number of subgoals


(defun ml4pg-get-numbers (cmd top level)
  (let* ((res (ml4pg-split-command cmd nil 0))
	 (tactics (car res))
	 (end (cadr res))
	 (nums (ml4pg-add-tactics tactics end top level)))
    (if nums (do ((temp (cdr nums) (cdr temp))
	 (temp2 (list (format "%s" (nth 0 (car nums))) (nth 1 (car nums))   (format "%s" (nth 2 (car nums))) (format "%s" (nth 3 (car nums))))))
	((endp temp) (list (string-to-number (nth 0 temp2)) (nth 1 temp2)  (string-to-number (nth 2 temp2)) (string-to-number (nth 3 temp2))) )
	(setf temp2 (list (if (or (< (string-to-number(nth 0 temp2)) 0) (< (nth 0 (car temp)) 0))
			      (concatenate 'string (format "-%s" (abs (string-to-number(nth 0 temp2)))) (format "%s" (abs (nth 0 (car temp)))))
			    (concatenate 'string (format "%s" (abs (string-to-number(nth 0 temp2))) ) (format "%s" (abs (nth 0 (car temp))))))
			  (+ (nth 1 temp2) (nth 1 (car temp)))
			  (if (or (< (abs (string-to-number(nth 2 temp2))) 0) (< (nth 2 (car temp)) 0))
			      (concatenate 'string (format "-%s" (abs (abs (string-to-number(nth 2 temp2))))) (format "%s" (abs (nth 2 (car temp)))))
			    (concatenate 'string (format "%s" (abs (abs (string-to-number(nth 2 temp2))))) (format "%s" (abs (nth 2 (car temp))))))
			  (if (or (< (string-to-number (nth 3 temp2)) 0) (< (nth 3 (car temp)) 0))
			      (concatenate 'string (format "-%s" (abs (string-to-number (nth 3 temp2)))) (format "%s" (abs (nth 3 (car temp)))))
			    (concatenate 'string (format "%s" (abs (string-to-number (nth 3 temp2)))) (format "%s" (abs (nth 3 (car temp))))))
			 ))
	)
    )))

;; Function to obtain the information just about the goals. 

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




(defvar ml4pg-useless-terms '("Definition" "Defined" "Fixpoint" "Structure" "Section" "Add Ring" "Hypothesis" "Hypotheses" "Include" "Export" "Parameter" "Axiom"
"End" "Notation" "Hint" "Inductive" "Variable" "Implicit" "Import" "Canonical" "Coercion"
"Module" "Ltac" "Let" "Opaque" "Bind" "Scope" "Require" "Infix" "Record" "Fact" "Print"))

(defun ml4pg-is-in-search (cmd)
  (do ((temp ml4pg-useless-terms (cdr temp))
       (is nil))
      ((or (endp temp) is) is)
      (if (search (car temp) cmd) (setf is t))))



(defun ml4pg-compute-tactic-value (list)
  (if (not list) (list 0 0 0 0 0)
  (let ((len (length list))
	(arg0 (car (car list)))
	(arg1 (format "%s" (nth 1 (car list))))
	(hyp (format "%s" (nth 2 (car list))))
	(top (format "%s" (nth 3 (car list)))))
    (do ((temp (cdr list) (cdr temp)))
	((endp temp) (list arg0 (string-to-number arg1) (string-to-number hyp) (string-to-number top) len))
	(progn (setf arg1 (format "%s%s%s" arg1 (nth 0 (car temp)) (nth 1 (car temp))))
	       (setf hyp (format "%s%s" hyp (nth 2 (car temp))))
	       (setf top (format "%s%s" top (nth 3 (car temp))))
	      )))))



(defun ml4pg-compute-tactic-result (name)
  (append (list name) (list (append
	(ml4pg-compute-tactic-value ml4pg-move)
	(ml4pg-compute-tactic-value ml4pg-case)
	(ml4pg-compute-tactic-value ml4pg-elim)
	(ml4pg-compute-tactic-value ml4pg-apply/)
	(ml4pg-compute-tactic-value ml4pg-move/)
	(ml4pg-compute-tactic-value ml4pg-case/)
	(ml4pg-compute-tactic-value ml4pg-rewrite)
	(ml4pg-compute-tactic-value ml4pg-exists)
	(ml4pg-compute-tactic-value ml4pg-done)
	(ml4pg-compute-tactic-value ml4pg-exact)))))
	 
(defun ml4pg-compute-proof-tree-result (name)
  (append (list name) (list (append
	(if ml4pg-tdl1 ml4pg-tdl1 (ml4pg-generate-zeros 13))
	(if ml4pg-tdl2 ml4pg-tdl2 (ml4pg-generate-zeros 13))
	(if ml4pg-tdl3 ml4pg-tdl3 (ml4pg-generate-zeros 13))
	(if ml4pg-tdl4 ml4pg-tdl4 (ml4pg-generate-zeros 13))
	(if ml4pg-tdl5 ml4pg-tdl5 (ml4pg-generate-zeros 13))))))
	




(defun ml4pg-export-theorem-aux (result name)
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
		  (ml4pg-export-theorem-aux result name)))
	  ((search "Lemma" cmd)
	   (progn (proof-assert-next-command-interactive)
		  (ml4pg-export-theorem-aux result 
				      (subseq cmd (1+ (search " " cmd)) 
					      (search " " cmd :start2 (1+ (search " " cmd))))
				      )))
	  ((search "Proof" cmd)
	   (progn (proof-assert-next-command-interactive)
		  (ml4pg-export-theorem-aux result name )))
	  ((search "Theorem" cmd)
	   (progn (proof-assert-next-command-interactive)
		  (ml4pg-export-theorem-aux result 
				      (subseq cmd (1+ (search " " cmd)) 
					      (search " " cmd :start2 (1+ (search " " cmd))))
				     )))
	  ((search "Qed." cmd)
	   (progn (proof-assert-next-command-interactive)
		  ; (insert (format "\n(* %s *)\n" (reverse result)))
		  ;(setf proof-tree-level (append proof-tree-level (list (compute-proof-result)))) 
		  ;(setf tactic-level (append tactic-level (list (compute-tactic-result))))
		  (setf ml4pg-tactic-level (append ml4pg-tactic-level (list (ml4pg-compute-tactic-result name))))
		  (setf ml4pg-proof-tree-level (append ml4pg-proof-tree-level (list (ml4pg-compute-proof-tree-result name))))
		  (if name
		   ;   (split-feature-vector name (flat (reverse result)))
		      (setf ml4pg-saved-theorems (append ml4pg-saved-theorems 
					       (list (list name (ml4pg-flat (reverse result))))))
		      )))
	  (t (progn (setf ts (ml4pg-get-top-symbol))
		    (setf ng (ml4pg-get-number-of-goals))
		    (proof-assert-next-command-interactive)
		    (setf ng2 (ml4pg-get-number-of-goals))
		    (ml4pg-export-theorem-aux (cons (append (ml4pg-get-numbers cmd ts ml4pg-current-level) (list ts) (list ng2)) result)
				       name)
		    (ml4pg-add-info-to-level (list 0 0 0 0 0 0 0 0 0 0 0 ng2 (if (< ng2 ng) 1 0)) ml4pg-current-level)
		    (setf ml4pg-current-level (1+ ml4pg-current-level))
		    
		    ))))))
     



(defun ml4pg-split-feature-vector (name fv)
  (let ((len (1+ (floor (length fv) 30))))
    (do ((i 0 (+ i 1)))
	((equal i len) nil)
	(setf ml4pg-saved-theorems (append ml4pg-saved-theorems 
				     (list (list name (ml4pg-take-30-from fv i))))))
    ))


(defun ml4pg-take-30-from (list pos)
  (let ((j (* 30 pos)))
  (do ((i j (1+ i))
       (temp2 nil (if (nth i list) (cons (nth i list) temp2) (cons 0 temp2))))
      ((= i (+ j 30)) (reverse temp2)))))




;;; Functions to save the files

(defun ml4pg-save-file-conventions1 ()
  (interactive)
  (let ((file (read-file-name "Save in file (don't include the extension): ")))
    (progn (with-temp-file (concat file "_goals.csv") (insert (ml4pg-extract-features-1)))
	   (with-temp-file (concat file "_tactics.csv") (insert (ml4pg-extract-features-2 tactic-level)))
	   (with-temp-file (concat file (format "_summary.txt")) (insert (ml4pg-extract-names))))))

	 
(defun ml4pg-extract-names ()
  (do ((temp ml4pg-saved-theorems (cdr temp))
       (temp2 "")
       (i 1 (1+ i)))
      ((endp temp) temp2)
    (setf temp2 (concat temp2 (format "%s %s\n" i (ml4pg-remove_last_colon (caar temp)))) )))





(defun ml4pg-print-list (list)
  (do ((temp list (cdr temp))
       (temp2 ""))
      ((endp temp) (subseq temp2 0 (1- (length temp2))))
    (setf temp2 (concat temp2 (format "%s," (car temp))) )))


(defun ml4pg-last-part-of-lists (list)
  (do ((temp list (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (setf temp2 (append temp2 (list (cadar temp))))))




(defun ml4pg-extract-features-1 ()
  (let ((fm (ml4pg-find-max-length)))
    (do ((temp (ml4pg-last-part-of-lists ml4pg-saved-theorems) (cdr temp))
	 (temp2 ""))
	((endp temp) temp2)
	(setf temp2 (concat temp2 
			      (format "%s\n"
				      (ml4pg-print-list  (ml4pg-take-30 (append (car temp) 
								   (ml4pg-generate-zeros 30))) ))))
      )
    ))






(defun ml4pg-extract-features-2 (list)
  (do ((temp (ml4pg-last-part-of-lists (cdr list)) (cdr temp))
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

(defvar ml4pg-tactic-temp nil)
(defvar ml4pg-proof-tree-temp nil)

(defun ml4pg-extract-info-up-to-here ()
  (interactive)
  (setf ml4pg-move nil
	ml4pg-case nil
	ml4pg-elim nil
	ml4pg-apply nil
	ml4pg-apply/ nil
	ml4pg-move/ nil
	ml4pg-case/ nil
	ml4pg-rewrite nil
	ml4pg-exists nil
	ml4pg-done nil
	ml4pg-exact nil
	ml4pg-tactic-temp nil
	ml4pg-tdl1 nil 
	ml4pg-tdl2 nil
	ml4pg-tdl3 nil
	ml4pg-tdl4 nil
	ml4pg-tdl5 nil
	ml4pg-current-level 1
	ml4pg-dot-level nil)
  (let ((final (point))
	(result nil)
	(end nil))
    (search-backward "Proof.")
    (proof-goto-point)
    (while (< (point) final) 
      (let* ((semis (save-excursion
		      (skip-chars-backward " \t\n"
					   (proof-queue-or-locked-end))
		      (proof-segment-up-to-using-cache (point))))
	     (comment (caar semis))
	     (cmd (cadar semis))
	     (ts nil))
	(progn (setf ts (ml4pg-get-top-symbol))
	       (setf ng (ml4pg-get-number-of-goals))
	       (proof-assert-next-command-interactive)
	       (setf ng2 (ml4pg-get-number-of-goals))
	       (if cmd 
	       (setf result (cons (append (ml4pg-get-numbers cmd ts ml4pg-current-level) (list ts) (list ng2)) result)))
	       (ml4pg-add-info-to-level (list 0 0 0 0 0 0 0 0 0 0 0 ng2 (if (< ng2 ng) 1 0)) ml4pg-current-level)
	       (setf ml4pg-current-level (1+ ml4pg-current-level))
		    )
	  
	)	
    )
    (setf ml4pg-tactic-temp (cadr (ml4pg-compute-tactic-result "")))
    (setf ml4pg-proof-tree-temp (cadr (ml4pg-compute-proof-tree-result "")))
    (ml4pg-take-30 (append (ml4pg-flat (reverse result)) (ml4pg-generate-zeros 30) ))
    (proof-shell-invisible-cmd-get-result (format "Unset Printing All"))
  ))



(defun ml4pg-extract-features-1-bis (thm)
  (let ((fm (ml4pg-find-max-length)))
    (do ((temp (append (ml4pg-last-part-of-lists ml4pg-saved-theorems) (list thm)) (cdr temp))
	 (temp2 ""))
	((endp temp) temp2)
	(setf temp2 (concat temp2 
			      (format "%s\n"
				      (ml4pg-print-list (ml4pg-take-30 (append (car temp) 
								   (ml4pg-generate-zeros 30))) ))))
      )
    ))


(defun ml4pg-extract-features-2-bis (thm list)
  (let ((fm (find-max-length)))
    (do ((temp (append (ml4pg-last-part-of-lists (cdr list)) (list thm)) (cdr temp))
	 (temp2 ""))
	((endp temp) temp2)
	(setf temp2 (concat temp2 
			      (format "%s\n"
				      (ml4pg-print-list (car temp)))))
      )
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
	     (ml4pg-export-theorem)))))





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
    


;;; Function to normalize the results

(defun ml4pg-max-two-lists (list1 list2)
  (do ((temp1 (ml4pg-take-30 (append list1 (ml4pg-generate-zeros 24))) (cdr temp1))
       (temp2 (ml4pg-take-30 (append list2 (ml4pg-generate-zeros 24))) (cdr temp2))
       (temp nil))
      ((endp temp1) temp)
      (if (< (car temp1) (car temp2))
	  (setf temp (append temp (list (car temp2))))
	(setf temp (append temp (list (car temp1))))
	)))

(defun ml4pg-min-two-lists (list1 list2)
  (do ((temp1 (ml4pg-take-30 (append list1 (ml4pg-generate-zeros 24))) (cdr temp1))
       (temp2 (ml4pg-take-30 (append list2 (ml4pg-generate-zeros 24))) (cdr temp2))
       (temp nil))
      ((endp temp1) temp)
      (if (> (car temp1) (car temp2))
	  (setf temp (append temp (list (car temp2))))
	(setf temp (append temp (list (car temp1))))
	)))

(defun ml4pg-max-position (list )
  (do ((temp list (cdr temp))
       (max (ml4pg-generate-zeros (length (car list)))))
      ((endp temp) max)
      (setf max (ml4pg-max-two-lists max (car temp)))))

(defun ml4pg-min-position (list )
  (do ((temp list (cdr temp))
       (min (ml4pg-generate-zeros (length (car list)))))
      ((endp temp) min)
      (setf min (ml4pg-min-two-lists min (car temp)))))


(defun ml4pg-normalize-list (list max min)
  (do ((temp (ml4pg-take-30 (append list (ml4pg-generate-zeros 24))) (cdr temp))
       (temp-max max (cdr temp-max))
       (temp-min min (cdr temp-min))
       (temp2 nil))
      ((endp temp) temp2)
      (cond ((< 0 (car temp)) (setf temp2 (append temp2 (list (/ (+ (car temp) .0) (car temp-max))))))
	    ((= 0 (car temp)) (setf temp2 (append temp2 (list 0))))
	    (t (setf temp2 (append temp2 (list (- (/ (+ (car temp) .0) (car temp-min))))))))))

(defun ml4pg-normalize (list)
  
  (let ((max (ml4pg-max-position list))
	(min (ml4pg-min-position list)))
   (do ((temp list (cdr temp))
	 (temp2 nil))
	((endp temp) temp2)
	(setf temp2 (append temp2 (list (ml4pg-normalize-list (car temp) max min)))))))






 
    
