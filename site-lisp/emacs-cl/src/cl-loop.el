;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements the LOOP macro from chapter 6, Iteration.

(IN-PACKAGE "EMACS-CL")

(cl:defmacro LOOP (&rest forms)
  (if (every #'consp forms)
      `(DO () (nil) ,@forms)
      (expand-extended-loop forms)))

(defstruct (loop-state
	     (:conc-name nil)
	     (:constructor make-loop-state
			   (loop-forms &optional loop-accumulator)))
  loop-forms
  loop-name
  loop-bindings
  loop-accumulator
  loop-prologue
  loop-tests
  loop-setters
  loop-body
  loop-steps
  loop-epilogue
  loop-result)

(defun copy-loop-state (state)
  (let ((s (make-loop-state (loop-forms state))))
    (setf (loop-accumulator s) (loop-accumulator state))
    s))

(defun merge-loop-states (s1 s2)
  (setf (loop-forms s1)    (loop-forms s2))
  (when (loop-name s2)     (setf (loop-name s1) (loop-name s2)))
  (setf (loop-bindings s1) (append (loop-bindings s2) (loop-bindings s1)))
  (when (loop-accumulator s2)
    (setf (loop-accumulator s1) (loop-accumulator s2)))
  (setf (loop-prologue s1) (append (loop-prologue s2) (loop-prologue s1)))
  (setf (loop-tests s1)    (append (loop-tests s2) (loop-tests s1)))
  (setf (loop-setters s1)  (append (loop-setters s2) (loop-setters s1)))
  (setf (loop-steps s1)    (append (loop-steps s2) (loop-steps s1)))
  (setf (loop-epilogue s1) (append (loop-epilogue s2) (loop-epilogue s1)))
  (when (loop-result s2)   (setf (loop-result s1) (loop-result s2)))
  s1)

(defmacro merge-loop-state (state)
  `(progn
    (setq forms (loop-forms ,state))
    (when (loop-name ,state)
      (setq name (loop-name ,state)))
    (setq bindings
     (append (loop-bindings ,state) bindings))
    (when (loop-accumulator ,state)
      (setq accumulator (loop-accumulator ,state)))
    (setq prologue
     (append (loop-prologue ,state) prologue))
    (setq tests
     (append (loop-tests ,state) tests))
    (setq setters
     (append (loop-setters ,state) setters))
    (setq steps
     (append (loop-steps ,state) steps))
    (setq epilogue
     (append (loop-epilogue ,state) epilogue))
    (when (loop-result ,state)
      (setq result (loop-result ,state)))))

(defvar *loop-clause-handlers* (make-hash-table :test #'equal))

(defmacro* define-loop-clause (names () &body body)
  (with-gensyms (state)
    `(dolist (name ',(ensure-list names))
      (setf (gethash name *loop-clause-handlers*)
            (lambda (,state)
	      (let ((forms		(loop-forms ,state))
		    (name		(loop-name ,state))
		    (bindings		(loop-bindings ,state))
		    (accumulator	(loop-accumulator ,state))
		    (prologue		(loop-prologue ,state))
		    (tests		(loop-tests ,state))
		    (setters		(loop-setters ,state))
		    (body		(loop-body ,state))
		    (steps		(loop-steps ,state))
		    (epilogue		(loop-epilogue ,state))
		    (result		(loop-result ,state)))
		,@body
		(setf (loop-forms ,state) forms)
		(setf (loop-name ,state) name)
		(setf (loop-bindings ,state) bindings)
		(setf (loop-accumulator ,state) accumulator)
		(setf (loop-prologue ,state) prologue)
		(setf (loop-tests ,state) tests)
		(setf (loop-setters ,state) setters)
		(setf (loop-body ,state) body)
		(setf (loop-steps ,state) steps)
		(setf (loop-epilogue ,state) epilogue)
		(setf (loop-result ,state) result)
		,state))))))

(defmacro peek= (&rest names)
  `(member (symbol-name (first forms)) ',names))

(defmacro next= (&rest names)
  `(member (symbol-name (pop forms)) ',names))

(define-loop-clause "NAMED" ()
  (setq name (pop forms)))

(define-loop-clause "WITH" ()
  (let ((bs nil)
	(more t))
    (while more
      (let* ((var (pop forms))
	     (val (when (peek= "=")
		    (pop forms)
		    (pop forms))))
	(push `(,var ,val) bs))
      (setq more (prog1 (peek= "AND")))
      (when more
	(pop forms)))
    (push bs bindings)))

;; (defun destructuring-setq-form (lambda-list form)
;;   `(MULTIPLE-VALUE-SETQ ,(lambda-list-variables lambda-list)
;;      (DESTRUCTURING-BIND ,lambda-list ,form
;;        (VALUES ,@(lambda-list-variables lambda-list)))))

(defun assignment-form (var form)
  (cond
    ((null var)
     nil)
    ((symbolp var)
     `(SETQ ,var ,form))
    ((consp var)
     (let ((val (gensym)))
       `(LET ((,val ,form))
	  ,@(do ((forms nil)
		 (vars var (rest vars)))
		((atom vars)
		 (unless (null vars)
		   (push `(SETQ ,vars ,val) forms))
		 (nreverse forms))
	      (push (assignment-form (first vars) `(POP ,val)) forms)))))
;;        `(LET ((,val ,form))
;; 	 ,(assignment-form (car var) `(CAR ,val))
;; 	 ,(assignment-form (cdr var) `(CDR ,val)))))
;;      `(MULTIPLE-VALUE-SETQ ,(lambda-list-variables lambda-list)
;;         (DESTRUCTURING-BIND ,lambda-list ,form
;; 	  (VALUES ,@(lambda-list-variables lambda-list)))))
    (t
     (type-error var '(OR SYMBOL CONS)))))

(define-loop-clause ("FOR" "AS") ()
  (let* ((var (pop forms))
	 (form (pop forms))
	 (k (symbol-name form)))
    (cond
      ((member k '("FROM" "UPFROM" "TO" "UPTO" "BELOW" "DOWNTO"
		   "ABOVE" "DOWNFROM"))
       (parse-for-arithmetic var form))
       
      ((string= k "IN")
       (let ((list (gensym))
	     (form (pop forms))
	     (by-fn '(FUNCTION CDR)))
	 (when (and forms
		    (symbolp (first forms))
		    (equal (symbol-name (first forms)) "BY"))
	   (pop forms)
	   (setq by-fn (pop forms)))
	 (push `((,list ,form)
		 ,@(if (atom var) (list var) (lambda-list-variables var)))
	       bindings)
	 (push `(ENDP ,list) tests)
	 (push (assignment-form var `(CAR ,list)) setters)
;; 	 (push (if (atom var)
;; 		   `(SETQ ,var (CAR ,list))
;; 		   (destructuring-setq-form var `(CAR ,list)))
;; 	       setters)
	 (push `(SETQ ,list (FUNCALL ,by-fn ,list)) steps)))

      ((string= k "ON")
       (let ((list (gensym))
	     (form (pop forms))
	     (by-fn '(FUNCTION CDR)))
	 (when (and forms
		    (symbolp (first forms))
		    (equal (symbol-name (first forms)) "BY"))
	   (pop forms)
	   (setq by-fn (pop forms)))
	 (push `((,list ,form)
		 ,@(if (atom var) (list var) (lambda-list-variables var)))
	       bindings)
	 (push `(ATOM ,list) tests)
	 (push (assignment-form var list) setters)
;; 	 (push (if (atom var)
;; 		   `(SETQ ,var ,list)
;; 		   (destructuring-setq-form var list))
;; 	       setters)
	 (push `(SETQ ,list (FUNCALL ,by-fn ,list)) steps)))
;; 	 (push `((,var ,form)) bindings)
;; 	 (push `(ATOM ,var) tests)
;; 	 (push `(SETQ ,var (FUNCALL ,by-fn ,var)) steps)))

      ((string= k "=")
       (let ((form1 (pop forms)))
	 (cond
	   ((peek= "THEN")
	    (pop forms)
	    (let ((form2 (pop forms)))
	      (push `((,var ,form1)) bindings)
	      (push (assignment-form var form2) steps)))
;; 	      (push (if (atom var)
;; 			`(SETQ ,var ,form2)
;; 			(destructuring-setq-form var form2))
;; 		    steps)))
	   (t
	    (push (if (atom var) (list var) (lambda-list-variables var))
		  bindings)
	    (push (assignment-form var form1) setters)))))
;; 	    (push (if (atom var)
;; 		      `(SETQ ,var ,form1)
;; 		      (destructuring-setq-form var form1))
;; 		  setters)))))

      ((string= k "ACROSS")
       (with-gensyms (vector index length)
	 (push `(,var (,index 0) (,vector ,(pop forms))) bindings)
	 (push `((,length (just-one (ARRAY-DIMENSIONS ,vector)))) bindings)
	 (push `(EQ ,index ,length) tests)
	 (push (assignment-form var `(AREF ,vector ,index)) setters)
;;	 (push `(SETQ ,var (AREF ,vector ,index)) setters)
	 (push `(INCF ,index) steps)))

      ((string= k "BEING")
       (setq k (symbol-name (pop forms)))
       (when (or (string= k "THE") (string= k "EACH"))
	 (setq k (symbol-name (pop forms))))
       (let ((k (symbol-name (pop forms))))
	 (unless (or (string= k "IN") (string= k "OF"))
	   (ERROR "Unknown LOOP BEING keyword: ~A" k)))
       (let ((list (gensym)))
	 (push `((,list (package-symbols
			 (OR (FIND-PACKAGE ,(pop forms))
			     (ERROR (QUOTE PACKAGE-ERROR)))
			 ,(cond
			   ((or (string= k "SYMBOL")
				(string= k "SYMBOLS"))
			    `(QUOTE (,kw:EXTERNAL
				     ,kw:INTERNAL
				     ,kw:INHERITED)))
			   ((or (string= k "PRESENT-SYMBOL")
				(string= k "PRESENT-SYMBOLS"))
			    `(QUOTE (,kw:EXTERNAL
				     ,kw:INTERNAL)))
			   ((or (string= k "EXTERNAL-SYMBOL")
				(string= k "EXTERNAL-SYMBOLS"))
			    `(QUOTE (,kw:EXTERNAL)))
			   (t
			    (ERROR "Invalid LOOP keyword: ~A" k)))))
		 ,var)
	       bindings)
	 (push `(NULL ,list) tests)
	 (push `(SETQ ,var (CAAR ,list)) setters)
	 (push `(SETQ ,list (CDR ,list)) steps)))))
  ;; TODO: this is a gross hack!
  (when (and forms
	     (symbolp (first forms))
	     (string= (symbol-name (first forms)) "AND"))
    (pop forms)
    (push 'FOR forms)))

(defun parse-for-arithmetic (var k)
  (let ((start-key nil)
	(start-form nil)
	(end-key nil)
	(end-form nil)
	(by-form 1)
	(step-fn nil)
	(test-fn nil)
	(incf (INTERN "INCF" *cl-package*))
	(decf (INTERN "DECF" *cl-package*))
	(lt (INTERN "<" *cl-package*))
	(gt (INTERN ">" *cl-package*))
	(le (INTERN "<=" *cl-package*))
	(ge (INTERN ">=" *cl-package*)))
    (flet ((parse-preposition (form)
	     (let ((k (symbol-name form)))
	       (cond
		 ((string= k "FROM")
		  (when start-key
		    (ERROR "Only one of FROM, DOWNFROM, or UPFROM allowed"))
		  (setq start-form (pop forms))
		  (setq start-key k))
		 ((string= k "DOWNFROM")
		  (when start-key
		    (ERROR "Only one of FROM, DOWNFROM, or UPFROM allowed"))
		  (if (eq step-fn incf)
		      (ERROR "DOWNFROM implies decrementing stepping")
		      (setq step-fn decf))
		  (setq start-form (pop forms))
		  (setq start-key k))
		 ((string= k "UPFROM")
		  (when start-key
		    (ERROR "Only one of FROM, DOWNFROM, or UPFROM allowed"))
		  (if (eq step-fn decf)
		      (ERROR "UPFROM implies incrementing stepping")
		      (setq step-fn incf))
		  (setq start-key k)
		  (setq start-form (pop forms)))
		 ((string= k "TO")
		  (when end-key
		    (ERROR
		     "Only one of TO, DOWNTO, UPTO, BELOW, or ABOVE allowed"))
		  (setq end-form (pop forms))
		  (setq end-key k))
		 ((string= k "DOWNTO")
		  (when end-key
		    (ERROR
		     "Only one of TO, DOWNTO, UPTO, BELOW, or ABOVE allowed"))
		  (if (eq step-fn incf)
		      (ERROR "UPTO implies incrementing stepping")
		      (setq step-fn decf))
		  (setq test-fn lt)
		  (setq end-form (pop forms))
		  (setq end-key k))
		 ((string= k "UPTO")
		  (when end-key
		    (ERROR
		     "Only one of TO, DOWNTO, UPTO, BELOW, or ABOVE allowed"))
		  (if (eq step-fn decf)
		      (ERROR "UPTO implies incrementing stepping")
		      (setq step-fn incf))
		  (setq test-fn gt)
		  (setq end-form (pop forms))
		  (setq end-key k))
		 ((string= k "BELOW")
		  (when end-key
		    (ERROR
		     "Only one of TO, DOWNTO, UPTO, BELOW, or ABOVE allowed"))
		  (if (eq step-fn decf)
		      (ERROR "BELOW implies incrementing stepping")
		      (setq step-fn incf))
		  (setq test-fn ge)
		  (setq end-form (pop forms))
		  (setq end-key k))
		 ((string= k "ABOVE")
		  (when end-key
		    (ERROR
		     "Only one of TO, DOWNTO, UPTO, BELOW, or ABOVE allowed"))
		  (if (eq step-fn incf)
		      (ERROR "BELOW implies decremental stepping")
		      (setq step-fn decf))
		  (setq test-fn le)
		  (setq end-form (pop forms))
		  (setq end-key k))
		 ((string= k "BY")
		  (setq by-form (pop forms))
		  t)
		 (t
		  (push form forms)
		  nil)))))
      (parse-preposition k)
      (while (and forms (parse-preposition (pop forms))))
      (setq step-fn (or step-fn incf))
      (setq start-form (or start-form (when (eq step-fn incf) 0)))
      (unless test-fn
	(setq test-fn (if (string= start-key "DOWNFROM") lt gt)))
      ;(print (format "%s %s %s %s %s BY %s %s" start-key start-form end-key test-fn end-form step-fn by-form))
      ;(FORMAT T "~S ~S ~S ~S ~S BY ~S ~S" start-key start-form end-key test-fn end-form step-fn by-form)
      (when end-form
	(with-gensyms (end)
	  (push `((,end ,end-form)) bindings)
	  (push `(,test-fn ,var ,end) tests)))
      (push `((,var ,start-form)) bindings)
      (push `(,step-fn ,var ,by-form) steps))))

(defvar *loop-collect* (gensym))
(defvar *loop-append* (gensym))
(defvar *loop-nconc* (gensym))
(defvar *loop-count* (gensym))
(defvar *loop-sum* (gensym))
(defvar *loop-max* (gensym))
(defvar *loop-min* (gensym))

(define-loop-clause ("COLLECT" "COLLECTING") ()
  (let ((form (pop forms)))
    (if accumulator
	(unless (eq accumulator *loop-collect*)
	  (ERROR "LOOP accumulator error"))
	(setq accumulator *loop-collect*))
    (push `((,accumulator nil)) bindings)
    (push `(PUSH ,form ,accumulator) body)
    (setf result `(NREVERSE ,accumulator))))

(define-loop-clause ("APPEND" "APPENDING") ()
  (let ((form (pop forms)))
    (if accumulator
	(unless (eq accumulator *loop-append*)
	  (ERROR "LOOP accumulator error"))
	(setq accumulator *loop-append*))
    (push `((,accumulator nil)) bindings)
    (push `(SETQ ,accumulator (APPEND ,accumulator ,form)) body)
    (setf result accumulator)))

(define-loop-clause ("NCONC" "NCONCING") ()
  (let ((form (pop forms)))
    (if accumulator
	(unless (eq accumulator *loop-nconc*)
	  (ERROR "LOOP accumulator error"))
	(setq accumulator *loop-nconc*))
    (push `((,accumulator nil)) bindings)
    (push `(SETQ ,accumulator (NCONC ,accumulator ,form)) body)
    (setf result accumulator)))

(define-loop-clause ("COUNT" "COUNTING") ()
  (let ((form (pop forms)))
    (if accumulator
	(unless (eq accumulator *loop-count*)
	  (ERROR "LOOP accumulator error"))
	(setq accumulator *loop-count*))
    (push `((,accumulator 0)) bindings)
    (push `(WHEN ,form (INCF ,accumulator)) body)
    (setf result accumulator)))

(define-loop-clause ("SUM" "SUMMING") ()
  (let ((form (pop forms)))
    (if accumulator
	(unless (eq accumulator *loop-sum*)
	  (ERROR "LOOP accumulator error"))
	(setq accumulator *loop-sum*))
    (push `((,accumulator 0)) bindings)
    (push `(INCF ,accumulator ,form) body)
    (setf result accumulator)))

(define-loop-clause ("MAXIMIZE" "MAXIMIZING") ()
  (let ((form (pop forms))
	(val (gensym)))
    (if accumulator
	(unless (eq accumulator *loop-max*)
	  (ERROR "LOOP accumulator error"))
	(setq accumulator *loop-max*))
    (push `((,accumulator nil)) bindings)
    (push `(SETQ ,accumulator (LET ((,val ,form))
				(IF ,accumulator
				    (MAX ,accumulator ,val)
				    ,val)))
	  body)
    (setf result accumulator)))

(define-loop-clause ("MINIMIZE" "MINIMIZING") ()
  (let ((form (pop forms))
	(val (gensym)))
    (if accumulator
	(unless (eq accumulator *loop-min*)
	  (ERROR "LOOP accumulator error"))
	(setq accumulator *loop-min*))
    (push `((,accumulator nil)) bindings)
    (push `(SETQ ,accumulator (LET ((,val ,form))
				(IF ,accumulator
				    (MIN ,accumulator ,val)
				    ,val)))
	  body)
    (setf result accumulator)))

(define-loop-clause "REPEAT" ()
  (let ((end (pop forms))
	(var (gensym)))
    (push `((,var 0)) bindings)
    (push `(,(INTERN ">=") ,var ,end) tests)
    (push `(SETQ ,var (,(INTERN "1+" *cl-package*) ,var)) setters)))

(define-loop-clause "ALWAYS" ()
  (let ((val (gensym)))
    (setf result T)
    (push `(UNLESS ,(pop forms) (RETURN-FROM ,name nil)) body)))

(define-loop-clause "NEVER" ()
  (let ((val (gensym)))
    (setf result T)
    (push `(WHEN ,(pop forms) (RETURN-FROM ,name nil)) body)))

(define-loop-clause "THEREIS" ()
  (let ((val (gensym)))
    (setf result nil)
    (push `(LET ((,val ,(pop forms)))
	    (WHEN ,val (RETURN-FROM ,name ,val)))
	  body)))

(define-loop-clause "WHILE" ()
  (push `(NOT ,(pop forms)) tests))

(define-loop-clause "UNTIL" ()
  (push (pop forms) tests))

(define-loop-clause ("IF" "WHEN") ()
  (let ((condition (pop forms))
	(then nil)
	(else nil))
   (let ((s (parse-loop-clause (make-loop-state forms accumulator))))
     (setq then (loop-body s))
     (setf (loop-body s) nil)
     (merge-loop-state s))
   (when (string= (symbol-name (first forms)) "ELSE")
     (pop forms)
     (let ((s (parse-loop-clause (make-loop-state forms accumulator))))
       (setq else (loop-body s))
       (setf (loop-body s) nil)
       (merge-loop-state s)))
   (push `(IF ,condition
	      (PROGN ,@then)
	      ,(when else `(PROGN ,@else)))
	 body)))

(define-loop-clause "UNLESS" ()
  (let ((form (pop forms)))
    (setq forms `(WHEN (NOT ,form) ,@forms))))

(define-loop-clause ("DO" "DOING") ()
  (while (consp (first forms))
    (push (pop forms) body)))

(define-loop-clause "RETURN" ()
  (push `(RETURN-FROM ,name ,(pop forms)) body))

(define-loop-clause "INITIALLY" ()
  (while (consp (first forms))
    (push (pop forms) prologue)))

(define-loop-clause "FINALLY" ()
  (while (consp (first forms))
    (push (pop forms) epilogue)))

(defun parse-loop-clause (state)
  (let* ((k (symbol-name (pop (loop-forms state))))
	 (fn (gethash k *loop-clause-handlers*)))
    (if fn
	(funcall fn state)
	(ERROR "Unknown LOOP keyword: ~A" k))))

(defun expand-extended-loop (forms)
  (let ((state (make-loop-state forms))
	(start (gensym))
	(end (gensym)))
    (do ()
	((null (loop-forms state)))
      (setq state (parse-loop-clause state)))
    `(BLOCK ,(loop-name state)
      ,(expand-bindings (nreverse (loop-bindings state))
        `(PROGN
	  ,@(nreverse (loop-prologue state))
	  (CATCH (QUOTE ,end)
	    (MACROLET ((LOOP-FINISH () (QUOTE (THROW (QUOTE ,end) nil))))
	      (TAGBODY
		 ,start
		 ,@(when (loop-tests state)
		     `((WHEN (OR ,@(loop-tests state)) (LOOP-FINISH))))
		 ,@(nreverse (loop-setters state))
		 ,@(nreverse (loop-body state))
		 ,@(nreverse (loop-steps state))
		 (GO ,start))))
	  ,@(nreverse (loop-epilogue state))
	  ,(loop-result state))))))

(defun expand-bindings (bindings body)
  (cond
    ((null bindings)
     body)
    ((or (atom (caar bindings))
	 (atom (caaar bindings)))
     `(LET ,(first bindings)
        ,(expand-bindings (rest bindings) body)))
    (t
     `(DESTRUCTURING-BIND ,(caaar bindings) ,(cadaar bindings)
        ,(expand-bindings (rest bindings) body)))))
