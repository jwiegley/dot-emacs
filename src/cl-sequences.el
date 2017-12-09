;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 17, Sequences.

(IN-PACKAGE "EMACS-CL")

;;; System Class SEQUENCE

(defun COPY-SEQ (sequence)
  (cond
    ((listp sequence)
     (copy-list sequence))
    ((or (stringp sequence) (bit-vector-p sequence) (SIMPLE-VECTOR-P sequence))
     (copy-sequence sequence))
    ((vector-and-typep sequence 'VECTOR)
     (let ((storage (vector-storage sequence))
	   (vector (make-vector
		    (1+ (or (FILL-POINTER sequence) (LENGTH sequence)))
		    'SIMPLE-VECTOR)))
       (do ((i 1 (1+ i)))
	   ((= i (length vector)))
	 (aset vector i (aref storage (1- i))))
       vector))
    ((VECTORP sequence)
     (subseq (vector-storage sequence) 0 (FILL-POINTER sequence)))
    (t
     (type-error sequence 'SEQUENCE))))

(defun ELT (sequence index)
  (cond
    ((listp sequence)
     (nth index sequence))
    ((VECTORP sequence)
     (if (ARRAY-HAS-FILL-POINTER-P sequence)
	 (if (cl:< index (FILL-POINTER sequence))
	     (AREF sequence index)
	     (error "error"))
	 (AREF sequence index)))
    (t
     (type-error sequence 'SEQUENCE))))

(defsetf ELT (sequence index) (obj)
  `(if (listp ,sequence)
       (setf (nth ,index ,sequence) ,obj)
       (setf (AREF ,sequence ,index) ,obj)))

(DEFSETF ELT (sequence index) (obj)
  `(IF (LISTP ,sequence)
       (SETF (NTH ,index ,sequence) ,obj)
       (SETF (AREF ,sequence ,index) ,obj)))

(cl:defun FILL (seq obj &KEY (START 0) END)
  ;; TODO: use fillarray when possible
  (unless END
    (setq END (LENGTH seq)))
  (do ((i START (1+ i)))
      ((eq i END))
    (setf (ELT seq i) obj))
  seq)

(cl:defun MAKE-SEQUENCE (type size &KEY INITIAL-ELEMENT)
  ;; TODO: An error of type type-error should be signaled if the
  ;; result type specifies the number of elements and size is
  ;; different from that number.
  (subtypecase type
    (nil
     (ERROR "Can't make sequence of type nil."))
    (LIST
     (make-list size INITIAL-ELEMENT))
    (BIT-VECTOR
     (make-bit-vector size (or INITIAL-ELEMENT 0)))
    (STRING
     (make-string size (if INITIAL-ELEMENT (CHAR-CODE INITIAL-ELEMENT) 0)))
    (VECTOR
     (make-simple-vector size INITIAL-ELEMENT))
    (T
     (type-error type '(MEMBER LIST BIT-VECTOR STRING VECTOR)))))

(defun SUBSEQ (seq start &optional end)
  (unless end
    (setq end (LENGTH seq)))
  (cond
    ((SIMPLE-STRING-P seq)
     (substring seq start end))
    ((STRINGP seq)
     (substring (vector-storage seq) start end))
    ((listp seq)
     (if (eq start end)
	 nil
	 (let* ((new (copy-list (nthcdr start seq)))
		(last (nthcdr (- end start 1) new)))
	   (when last
	     (setcdr last nil))
	   new)))
    ((VECTORP seq)
     (let ((len (- end start))
	   (i0 0))
       (when (eq (aref seq 0) 'SIMPLE-VECTOR)
	 (incf i0)
	 (incf len)
	 (incf start))
       (let ((new (if (BIT-VECTOR-P seq)
		      (make-bit-vector len 0)
		      (make-vector len 'SIMPLE-VECTOR)))
	     (storage (if (or (bit-vector-p seq)
			      (stringp seq)
			      (SIMPLE-VECTOR-P seq))
			  seq
			  (vector-storage seq))))
	 (do ((i i0 (1+ i))
	      (j start (1+ j)))
	     ((eq i len))
	   (aset new i (aref storage j)))
	 new)))
    (t
     (type-error seq 'SEQUENCE))))

(DEFSETF SUBSEQ (seq1 start &optional end) (seq2)
  `(PROGN
     (REPLACE ,seq1 ,seq2 ,(kw START1) ,start ,(kw END1) ,end)
     ,seq2))

(defun* MAP (type fn &rest sequences)
  (let ((len (apply #'min (mapcar #'LENGTH sequences)))
	(i 0)
	(result nil))
    (loop
      (when (eq i len)
	(return-from MAP
	  (when type
	    (setq result (nreverse result))
	    (subtypecase type
	      (LIST	
	       result)
	      (STRING
	       (if (null result)
		   ""
		   (apply #'string (mapcar #'CHAR-CODE result))))
	      (BIT-VECTOR
	       (apply #'make-bit-vector result))
	      (VECTOR
	       (apply #'vector 'SIMPLE-VECTOR result))
	      (SEQUENCE
	       result)
	      (T
	       (ERROR "Type specifier ~S is not a subtype of SEQUENCE."
		      type))))))
      (let ((item (APPLY fn (mapcar (lambda (seq) (ELT seq i)) sequences))))
	(when type
	  (push item result)))
      (incf i))))

(defun* MAP-INTO (result fn &rest sequences)
  (let ((len (apply #'min (mapcar #'LENGTH (cons result sequences))))
	(i 0))
    (loop
      (when (eq i len)
	(return-from MAP-INTO result))
      (setf (ELT result i)
	    (APPLY fn (mapcar (lambda (seq) (ELT seq i)) sequences)))
      (incf i))))

(cl:defun REDUCE (fn seq &KEY KEY FROM-END (START 0) END
			      (INITIAL-VALUE nil initial-value-p))
  (unless KEY
    (setq KEY (cl:function IDENTITY)))
  (unless END
    (setq END (LENGTH seq)))
  (let ((len (- END START))
	result)
    (cond
      ((and (eq len 1) (not initial-value-p))
       (ELT seq START))
      ((zerop len)
       (if initial-value-p
	   INITIAL-VALUE
	   (FUNCALL fn)))
      (t
       (if FROM-END
	   (progn
	     (when initial-value-p
	       (decf END)
	       (setq result (FUNCALL fn INITIAL-VALUE
				     (FUNCALL KEY (ELT seq END)))))
	     (do ((i (1- END) (1- i)))
		 ((< i START))
	       (setq result (FUNCALL fn (FUNCALL KEY (ELT seq i)) result))))
	   (progn
	     (when initial-value-p
	       (setq result (FUNCALL fn INITIAL-VALUE
				     (FUNCALL KEY (ELT seq START))))
	       (incf START))
	     (do ((i START (1+ i)))
		 ((>= i END))
	       (setq result (FUNCALL fn result (FUNCALL KEY (ELT seq i)))))))
       result))))

(cl:defun COUNT (obj seq &KEY FROM-END TEST TEST-NOT (START 0) END KEY)
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST (cl:function EQL)))
  (COUNT-IF (lambda (x) (FUNCALL TEST obj x)) seq
	    (kw FROM-END) FROM-END (kw START) START
	    (kw END) END (kw KEY) KEY))

(cl:defun COUNT-IF (predicate seq &KEY FROM-END (START 0) END KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (unless END
    (setq END (LENGTH seq)))
  (let ((n 0))
    (if FROM-END
	(do ((i (1- END) (1- i)))
	    ((eq i (1- START)))
	  (let ((elt (ELT seq i)))
	    (when (FUNCALL predicate (FUNCALL KEY elt))
	      (incf n))))
	(do ((i START (1+ i)))
	    ((eq i END))
	  (let ((elt (ELT seq i)))
	    (when (FUNCALL predicate (FUNCALL KEY elt))
	      (incf n)))))
    n))

(cl:defun COUNT-IF-NOT (predicate &REST args)
  (apply (cl:function COUNT-IF) (COMPLEMENT predicate) args))

(defun LENGTH (sequence)
  (cond
    ((or (listp sequence)
	 (bit-vector-p sequence)
	 (stringp sequence))
     (length sequence))
    ((SIMPLE-VECTOR-P sequence)
     (1- (length sequence)))
    ((VECTORP sequence)
     (or (and (ARRAY-HAS-FILL-POINTER-P sequence)
	      (FILL-POINTER sequence))
	 (vector-size sequence)))
    (t
     (type-error sequence 'SEQUENCE))))

(defun REVERSE (seq)
  (cond
   ((listp seq)
    (reverse seq))
   ((VECTORP seq)
    (NREVERSE (COPY-SEQ seq)))
   (t
    (type-error seq 'SEQUENCE))))

(defun NREVERSE (seq)
  (cond
    ((listp seq)
     (nreverse seq))
    ((VECTORP seq)
     (do* ((len (LENGTH seq))
	   (end (/ len 2))
	   (i 0 (1+ i))
	   (j (1- len) (1- j)))
	  ((eq i end)
	   seq)
       (rotatef (AREF seq i) (AREF seq j))))
    (t
     (type-error seq 'SEQUENCE))))

(cl:defun SORT (sequence predicate &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (cond 
    ((listp sequence)
     (sort sequence (lambda (x y)
		      (FUNCALL predicate (FUNCALL KEY x) (FUNCALL KEY y)))))
    ((VECTORP sequence)
     (MAP-INTO sequence
	       #'IDENTITY
	       (SORT (MAP 'LIST #'IDENTITY sequence) predicate (kw KEY) KEY)))
    (t
     (type-error sequence 'SEQUENCE))))

(fset 'STABLE-SORT (symbol-function 'SORT))

(cl:defun FIND (obj seq &KEY FROM-END TEST TEST-NOT (START 0) END KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST (cl:function EQL)))
  (FIND-IF (lambda (x) (FUNCALL TEST obj x)) seq
	   (kw FROM-END) FROM-END (kw START) START
	   (kw END) END (kw KEY) KEY))

(cl:defun FIND-IF (predicate seq &KEY FROM-END (START 0) END KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (let ((len (LENGTH seq)))
    (unless END
      (setq END len))
    (catch 'FIND
      (if FROM-END
	  (do ((i (1- END) (1- i)))
	      ((eq i -1))
	    (let ((elt (ELT seq i)))
	      (when (FUNCALL predicate (FUNCALL KEY elt))
		(throw 'FIND elt))))
	  (do ((i START (1+ i)))
	      ((eq i END))
	    (let ((elt (ELT seq i)))
	      (when (FUNCALL predicate (FUNCALL KEY elt))
		(throw 'FIND elt)))))
      nil)))

(cl:defun FIND-IF-NOT (predicate &REST args)
  (apply (cl:function FIND-IF) (COMPLEMENT predicate) args))

(cl:defun POSITION (obj seq &KEY FROM-END TEST TEST-NOT (START 0) END KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST (cl:function EQL)))
  (POSITION-IF (lambda (x) (FUNCALL TEST obj x)) seq
	       (kw FROM-END) FROM-END (kw START) START
	       (kw END) END (kw KEY) KEY))

(cl:defun POSITION-IF (predicate seq &KEY FROM-END (START 0) END KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (let ((len (LENGTH seq)))
    (unless END
      (setq END len))
    (catch 'POSITION
      (if FROM-END
	  (do ((i (1- END) (1- i)))
	      ((eq i -1))
	    (when (FUNCALL predicate (FUNCALL KEY (ELT seq i)))
	      (throw 'POSITION i)))
	  (do ((i START (1+ i)))
	      ((eq i END))
	    (when (FUNCALL predicate (FUNCALL KEY (ELT seq i)))
	      (throw 'POSITION i))))
      nil)))

(cl:defun POSITION-IF-NOT (predicate &REST args)
  (apply (cl:function POSITION-IF) (COMPLEMENT predicate) args))

(defun subseq-p (seq1 start1 end1 seq2 start2 end2 TEST KEY)
  (catch 'subseq-p
    (do ((i start1 (1+ i))
	 (j start2 (1+ j)))
	((or (eq i end1) (eq j end2))
	 (eq i end1))
      (unless (FUNCALL TEST (FUNCALL KEY (ELT seq1 i))
		            (FUNCALL KEY (ELT seq2 j)))
	(throw 'subseq-p nil)))))

(cl:defun SEARCH (seq1 seq2 &KEY FROM-END TEST TEST-NOT KEY
		                 (START1 0) (START2 0) END1 END2)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (unless END1
    (setq END1 (LENGTH seq1)))
  (unless END2
    (setq END2 (LENGTH seq2)))
  (catch 'SEARCH
    (if FROM-END
	(do ((i (1- END2) (1- i)))
	    ((minusp i))
	  (when (subseq-p seq1 START1 END1 seq2 i END2 TEST KEY)
	    (throw 'SEARCH i)))
	(do ((i START2 (1+ i)))
	    ((eq i END2))
	  (when (subseq-p seq1 START1 END1 seq2 i END2 TEST KEY)
	    (throw 'SEARCH (+ i (- END1 START1) -1)))))
    nil))

(cl:defun MISMATCH (seq1 seq2 &KEY FROM-END TEST TEST-NOT KEY
				   (START1 0) (START2 0) END1 END2)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (unless END1
    (setq END1 (LENGTH seq1)))
  (unless END2
    (setq END2 (LENGTH seq2)))
  (catch 'MISMATCH
    (if FROM-END
	(do ((i (1- END1) (1- i))
	     (j (1- END2) (1- j)))
	    ((or (< i START1) (< j START2))
	     (unless (and (< i START1) (< j START2)) i))
	  (unless (FUNCALL TEST (FUNCALL KEY (ELT seq1 i))
				(FUNCALL KEY (ELT seq2 j)))
	    (throw 'MISMATCH i)))
	(do ((i START1 (1+ i))
	     (j START2 (1+ j)))
	    ((or (eq i END1) (eq j END2))
	     (unless (and (eq i END1) (eq j END2)) i))
	  (unless (FUNCALL TEST (FUNCALL KEY (ELT seq1 i))
				(FUNCALL KEY (ELT seq2 j)))
	    (throw 'MISMATCH i))))))

(cl:defun REPLACE (seq1 seq2 &KEY (START1 0) (START2 0) END1 END2)
  (unless END1
    (setq END1 (LENGTH seq1)))
  (unless END2
    (setq END2 (LENGTH seq2)))
  (do ((i START1 (1+ i))
       (j START2 (1+ j)))
      ((or (eq i END1) (eq j END2)))
    (setf (ELT seq1 i) (ELT seq2 j)))
  seq1)

(cl:defun NSUBSTITUTE (new old seq &KEY FROM-END TEST TEST-NOT (START 0) END
					COUNT KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (ERROR 'ERROR))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (NSUBSTITUTE-IF new (lambda (x) (FUNCALL TEST old x)) seq
		  (kw FROM-END) FROM-END (kw START) START
		  (kw END) END (kw COUNT) COUNT (kw KEY) KEY))

(cl:defun NSUBSTITUTE-IF (obj predicate seq &KEY FROM-END (START 0) END COUNT
						 KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (unless END
    (setq END (LENGTH seq)))
  (if FROM-END
      (do ((i (1- END) (1- i)))
	  ((or (minusp i) (and COUNT (<= COUNT 0))))
	(when (FUNCALL predicate (FUNCALL KEY (ELT seq i)))
	  (setf (ELT seq i) obj))
	(when COUNT (decf COUNT)))
      (do ((i START (1+ i)))
	  ((or (eq i END) (and COUNT (<= COUNT 0))))
	(when (FUNCALL predicate (FUNCALL KEY (ELT seq i)))
	  (setf (ELT seq i) obj))
	(when COUNT (decf COUNT))))
  seq)

(cl:defun NSUBSTITUTE-IF-NOT (predicate &REST args)
  (apply (cl:function NSUBSTITUTE-IF) (COMPLEMENT predicate) args))

(cl:defun SUBSTITUTE (new old seq &REST keys)
  (apply (cl:function NSUBSTITUTE) new old (COPY-SEQ seq) keys))

(cl:defun SUBSTITUTE-IF (obj predicate seq &REST keys)
  (apply (cl:function NSUBSTITUTE-IF) obj predicate (COPY-SEQ seq) keys))

(cl:defun SUBSTITUTE-IF-NOT (obj predicate seq &REST keys)
  (apply (cl:function NSUBSTITUTE-IF)
	 obj (COMPLEMENT predicate) (COPY-SEQ seq) keys))

(defun CONCATENATE (type &rest sequences)
  (subtypecase type
    (nil
     (ERROR "Can't concatenate to type nil."))
    (LIST
     (let ((result nil))
       (dolist (seq sequences (nreverse result))
	 (dosequence (x seq)
           (push x result)))))
    (STRING
     (let ((string (make-string (reduce #'+ (mapcar #'LENGTH sequences)) 0))
	   (i -1))
       (dolist (seq sequences)
	 (dosequence (x seq)
	   (aset string (incf i) (CHAR-CODE x))))
       string))
    (BIT-VECTOR
     (let ((vector (vector (reduce #'+ (mapcar #'LENGTH sequences)) 0))
	   (i -1))
       (dolist (seq sequences)
	 (dosequence (x seq)
	   (setf (bref vector (incf i)) x)))
       vector))
    (VECTOR
     (let ((vector (make-vector (1+ (reduce #'+ (mapcar #'LENGTH sequences)))
				'SIMPLE-VECTOR))
	   (i 0))
       (dolist (seq sequences)
	 (dosequence (x seq)
	   (aset vector (incf i) x)))
       vector))
    (T
     (ERROR "~S is not a recognizable subtype of LIST or VECTOR." type))))

(cl:defun MERGE (type seq1 seq2 predicate &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (let* ((len1 (LENGTH seq1))
	 (len2 (LENGTH seq2))
	 (len (+ len1 len2))
	 (result (subtypecase type
		   (nil		(ERROR "Can't merge to type nil."))
		   (LIST	(make-list len nil))
		   (STRING	(make-string len 0))
		   (BIT-VECTOR	(make-bit-vector len 0))
		   (VECTOR	(make-vector (1+ len) 'SIMPLE-VECTOR))
		   (T		(type-error type '(MEMBER LIST VECTOR))))))
    (do ((i 0 (1+ i))
	 (j 0)
	 (k 0))
	((= i len))
      (setf (ELT result i)
	    (if (or (eq j len1)
		    (and (not (eq k len2))
			 (FUNCALL predicate (FUNCALL KEY (ELT seq2 k))
				            (FUNCALL KEY (ELT seq1 j)))))
		(prog1 (ELT seq2 k) (incf k))
		(prog1 (ELT seq1 j) (incf j)))))
    result))

(cl:defun REMOVE (obj seq &KEY FROM-END TEST TEST-NOT (START 0) END COUNT KEY)
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (REMOVE-IF (lambda (x) (FUNCALL TEST obj x)) seq (kw FROM-END) FROM-END
	     (kw START) START (kw END) END (kw COUNT) COUNT (kw KEY) KEY))

(defun list-remove (predicate list end count key)
  (cond
    ((or (null list) (zerop end) (when count (zerop count)))
     nil)
    ((FUNCALL predicate (FUNCALL key (first list)))
     (list-remove predicate (rest list) (1- end) (when count (1- count)) key))
    (t
     (cons (first list)
	   (list-remove predicate (rest list) (1- end) count key)))))

(cl:defun REMOVE-IF (predicate seq &KEY FROM-END (START 0) END COUNT KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (cond
    ((listp seq)
     (if FROM-END
	 (ERROR "REMOVE-IF doesn't implement :FROM-END T.")
	 (list-remove predicate (nthcdr START seq) (or END (LENGTH seq))
		      COUNT KEY)))
    ((VECTORP seq)
     (ERROR "REMOVE-IF not implemented for vectors."))
    (t
     (type-error seq 'SEQUENCE))))

(cl:defun REMOVE-IF-NOT (predicate &REST args)
  ;;(apply (cl:function REMOVE-IF) (COMPLEMENT predicate) args))
  (apply #'REMOVE-IF (COMPLEMENT predicate) args))

(cl:defun DELETE (obj seq &KEY FROM-END TEST TEST-NOT (START 0) END COUNT KEY)
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (DELETE-IF (lambda (x) (FUNCALL TEST obj x)) seq (kw FROM-END) FROM-END
	     (kw START) START (kw END) END (kw COUNT) COUNT (kw KEY) KEY))

(defun list-delete (predicate list end count key)
  (cond
    ((or (null list) (zerop end) (when count (zerop count)))
     nil)
    ((FUNCALL predicate (FUNCALL key (first list)))
     (let ((rest (list-delete predicate (rest list) (1- end)
			      (when count (1- count)) key)))
       (if (null rest)
	   nil
	 (RPLACA list (car rest))
	 (RPLACD list (cdr rest)))))
    (t
     (RPLACD list (list-delete predicate (rest list) (1- end) count key)))))

(cl:defun DELETE-IF (predicate seq &KEY FROM-END (START 0) END COUNT KEY)
  (cond
    ((listp seq)
     (progn
       (unless KEY
	 (setq KEY #'IDENTITY))
       (if FROM-END
	   (REMOVE-IF predicate seq (kw FROM-END) FROM-END (kw KEY) KEY
		      (kw START) START (kw END) END (kw COUNT) COUNT)
	   (list-delete predicate (nthcdr START seq) (or END (LENGTH seq))
			COUNT KEY))))
    ((VECTORP seq)
     (if (ARRAY-HAS-FILL-POINTER-P seq)
	 (ERROR "DELETE-IF not implemented for vectors with fill pointers.")
	 (REMOVE-IF predicate seq (kw FROM-END) FROM-END (kw KEY) KEY
		    (kw START) START (kw END) END (kw COUNT) COUNT)))
    (t
     (type-error seq 'SEQUENCE))))

(cl:defun DELETE-IF-NOT (predicate &REST args)
  (apply (cl:function DELETE-IF) (COMPLEMENT predicate) args))

(cl:defun REMOVE-DUPLICATES (seq &KEY FROM-END TEST TEST-NOT (START 0) END KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (let ((i START))
    (REMOVE-IF (lambda (x)
		 (POSITION x seq (kw TEST) TEST (kw KEY) KEY
				 (kw START) (incf i) (kw FROM-END) FROM-END))
	       seq (kw KEY) KEY (kw START) START (kw END) END)))

(cl:defun DELETE-DUPLICATES (seq &KEY FROM-END TEST TEST-NOT (START 0) END KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (let ((i START))
    (DELETE-IF (lambda (x)
		 (POSITION x seq (kw TEST) TEST (kw KEY) KEY
				 (kw START) (incf i) (kw FROM-END) FROM-END))
	       seq (kw KEY) KEY (kw START) START (kw END) END)))



(defmacro* dovector ((var vector &optional result) &body body)
  (with-gensyms (i len vec)
    `(let* (,var (,i 0) (,vec ,vector) (,len (LENGTH ,vec)))
       (while (< ,i ,len)
	 (setq ,var (AREF ,vec ,i))
	 ,@body
	 (incf ,i))
       ,result)))

(defmacro* dosequence ((var sequence &optional result) &body body)
  (let ((seq (gensym)))
    `(let ((,seq ,sequence))
       (if (listp ,seq)
	   (dolist (,var ,seq ,result) ,@body)
	   (dovector (,var ,seq ,result) ,@body)))))
