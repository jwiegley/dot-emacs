;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 15, Arrays.

(IN-PACKAGE "EMACS-CL")

;;; System Class	ARRAY
;;; Type		SIMPLE-ARRAY
;;; System Class	VECTOR
;;; Type		SIMPLE-VECTOR
;;; System Class	BIT-VECTOR
;;; Type		SIMPLE-BIT-VECTOR

(define-storage-layout array (dims storage offset))

(define-storage-layout vector (size storage offset fp))

(defun set-initial-contents (n i storage contents fn)
  (cond
    ((zerop n)	(aset storage 0 (funcall fn contents)))
    ((eq n 1)	(dosequence (x contents i)
		  (aset storage i (funcall fn x))
		  (incf i)))
    (t		(dosequence (x contents i)
		  (setq i (set-initial-contents (1- n) i storage x fn))))))

(defun bit-bool (bit)
  (ecase bit
    (0 nil)
    (1 t)))

(if (fboundp 'make-bit-vector)
    (progn
      (defmacro bref (vector index)
	`(aref ,vector ,index))
      (defsetf bref (vector index) (bit)
	`(aset ,vector ,index ,bit)))
    (progn
      (defun make-bit-vector (length bit)
	(make-bool-vector length (bit-bool bit)))
      (defmacro bit-vector-p (object)
	`(bool-vector-p ,object))
      (defmacro bref (vector index)
	`(if (aref ,vector ,index) 1 0))
      (defsetf bref (vector index) (bit)
	`(aset ,vector ,index (bit-bool ,bit)))))

(defun make-simple-vector (size initial-element)
  (let ((vector (make-vector (1+ size) initial-element)))
    (aset vector 0 'SIMPLE-VECTOR)
    vector))

(cl:defun MAKE-ARRAY (dimensions &KEY (ELEMENT-TYPE T) INITIAL-ELEMENT
		      INITIAL-CONTENTS ADJUSTABLE FILL-POINTER
		      DISPLACED-TO DISPLACED-INDEX-OFFSET)
  (setq dimensions (ensure-list dimensions))
  (when (eq FILL-POINTER T)
    (setq FILL-POINTER (just-one dimensions)))
  (let* ((size (apply #'cl:* dimensions))
	 (start-index 0)
	 (ndims (length dimensions))
	 (vectorp (eq ndims 1))
	 (simplep (not (or ADJUSTABLE
			   FILL-POINTER
			   DISPLACED-TO
			   (not vectorp)))))
    (multiple-value-bind (initial-element make-fn convert-fn
			  vector-type array-type)
	(ecase (UPGRADED-ARRAY-ELEMENT-TYPE ELEMENT-TYPE)
	  (BIT
	   (values (or INITIAL-ELEMENT 0)
		   ;; TODO: clean up
		   (if (fboundp 'make-bool-vector)
				#'make-bool-vector
				#'make-bit-vector)
		   (if (fboundp 'make-bool-vector) #'bit-bool #'IDENTITY)
		   'BIT-VECTOR
		   'bit-array))
	  (CHARACTER
	   (values (or INITIAL-ELEMENT (ch 0))
		   #'make-string
		   (if use-character-type-p #'IDENTITY #'CHAR-CODE)
		   'STRING
		   'char-array))
	  ((T)
	   (when simplep
	     (setq start-index 1))
	   (values INITIAL-ELEMENT
		   (if simplep #'make-simple-vector #'make-vector)
		   #'IDENTITY
		   'VECTOR
		   'ARRAY)))
      (let ((storage (or DISPLACED-TO
			 (funcall make-fn size
				  (funcall convert-fn initial-element)))))
	(when INITIAL-CONTENTS
	  (set-initial-contents
	   ndims start-index storage INITIAL-CONTENTS convert-fn))
	(cond
	  (simplep	storage)
	  (vectorp	(vector vector-type (just-one dimensions) storage
				DISPLACED-INDEX-OFFSET FILL-POINTER))
	  (t		(vector array-type dimensions storage
				DISPLACED-INDEX-OFFSET)))))))


(defun cl-vector (vector)
  (unless (vectorp vector)
    (type-error vector 'vector))
  (vector 'VECTOR (length vector) vector 0 nil))

(defun el-vector (vector)
  (unless (VECTORP vector)
    (type-error vector 'VECTOR))
  (if (and (eq (aref vector 0) 'VECTOR)
	   (eq (vector-size vector) (length (vector-storage vector)))
	   (zerop (vector-offset vector)))
      (vector-storage vector)
      (let* ((size (LENGTH vector))
	     (new (make-vector size nil)))
	(dotimes (i size)
	  (aset new i (AREF vector i)))
	new)))

(defun el-string (string)
  (unless (STRINGP string)
    (type-error string 'STRING))
  (cond
    ((stringp string)
     string)
    ((and (eq (vector-size string) (length (vector-storage string)))
	  (zerop (vector-offset string)))
     (vector-storage string))
    (t
     (let* ((size (LENGTH string))
	    (new (make-string size (ch 0))))
       (dotimes (i size)
	 (aset new i (CHAR string i)))
       new))))

(if (eval-when-compile (featurep 'xemacs))
    (defun el-bit-vector (bit-vector)
      (unless (BIT-VECTOR-P bit-vector)
	(type-error bit-vector 'BIT-VECTOR))
      (cond
	((bit-vector-p bit-vector)
	 bit-vector)
	((and (eq (vector-size bit-vector)
		  (length (vector-storage bit-vector)))
	      (zerop (vector-offset bit-vector)))
	 (vector-storage bit-vector))
	(t
	 (let* ((size (LENGTH bit-vector))
		(new (make-bit-vector size 0)))
	   (dotimes (i size)
	     (aset new i (BIT bit-vector i)))
	   new))))
    (defun el-bool-vector (bool-vector)
      (unless (BIT-VECTOR-P bool-vector)
	(type-error bool-vector 'BIT-VECTOR))
      (cond
	((bool-vectorp bool-vector)
	 bool-vector)
	((and (eq (vector-size bool-vector)
		  (length (vector-storage bool-vector)))
	      (zerop (vector-offset bool-vector)))
	 (vector-storage bool-vector))
	(t
	 (let* ((size (LENGTH bool-vector))
		(new (make-bool-vector size 0)))
	   (dotimes (i size)
	     (aset new i (not (zerop (BIT bool-vector i)))))
	   new)))))

(cl:defun ADJUST-ARRAY (array new-dimensions
			&KEY ELEMENT-TYPE INITIAL-ELEMENT INITIAL-CONTENTS
			     FILL-POINTER DISPLACED-TO DISPLACED-INDEX-OFFSET)
  (if (ADJUSTABLE-ARRAY-P array)
      (error "TODO")
      (MAKE-ARRAY new-dimensions
		  (kw ELEMENT-TYPE) ELEMENT-TYPE
		  (kw INITIAL-ELEMENT) INITIAL-ELEMENT
		  (kw INITIAL-CONTENTS) INITIAL-CONTENTS
		  (kw FILL-POINTER) FILL-POINTER
		  (kw DISPLACED-TO) DISPLACED-TO
		  (kw DISPLACED-INDEX-OFFSET) DISPLACED-INDEX-OFFSET)))

(defun ADJUSTABLE-ARRAY-P (array)
  (and (vectorp array)
       (case (aref array 0)
	 ((BIT-VECTOR bit-array STRING char-array VECTOR ARRAY) T))))

(defun AREF (array &rest subscripts)
  (cond
    ((BIT-VECTOR-P array)
     (BIT array (just-one subscripts)))
    ((STRINGP array)
     (CHAR array (just-one subscripts)))
    ((vector-and-typep array 'SIMPLE-VECTOR)
     (SVREF array (just-one subscripts)))
    ((vector-and-typep array 'VECTOR)
     (aref (array-storage array) (just-one subscripts)))
    ((vector-and-typep array 'ARRAY)
     (aref (array-storage array) (apply #'ARRAY-ROW-MAJOR-INDEX array subscripts)))
    ((vector-and-typep array 'bit-array)
     (BIT (array-storage array) (apply #'ARRAY-ROW-MAJOR-INDEX array subscripts)))
    ((vector-and-typep array 'char-array)
     (CHAR (array-storage array) (apply #'ARRAY-ROW-MAJOR-INDEX array subscripts)))
    (t
     (type-error array 'ARRAY))))

(defsetf AREF (array &rest subscripts) (obj)
  `(ASET ,obj ,array ,@subscripts))

(DEFINE-SETF-EXPANDER AREF (array &rest subscripts)
  (let ((obj (gensym))
	(atemp (gensym))
	(stemps (map-to-gensyms subscripts)))
    (cl:values (cons atemp stemps)
	       (cons array subscripts)
	       (list obj)
	       `(ASET ,obj ,atemp ,@stemps)
	       `(AREF ,atemp ,@stemps))))

(defun ASET (object array &rest subscripts)
  (cond
    ((BIT-VECTOR-P array)
     (setf (BIT array (just-one subscripts)) object))
    ((STRINGP array)
     (setf (CHAR array (just-one subscripts)) object))
    ((vector-and-typep array 'SIMPLE-VECTOR)
     (setf (SVREF array (just-one subscripts)) object))
    ((vector-and-typep array 'VECTOR)
     (aset (array-storage array) (just-one subscripts) object))
    ((vector-and-typep array 'ARRAY)
     (aset (array-storage array)
	   (apply #'ARRAY-ROW-MAJOR-INDEX array subscripts)
	   object))
    ((vector-and-typep array 'bit-array)
     (aset (array-storage array)
	   (apply #'ARRAY-ROW-MAJOR-INDEX array subscripts)
	   (bit-bool object)))
    ((vector-and-typep array 'char-array)
     (aset (array-storage array)
	   (apply #'ARRAY-ROW-MAJOR-INDEX array subscripts)
	   (CHAR-CODE object)))
    (t
     (type-error array 'ARRAY))))

(defun ARRAY-DIMENSION (array axis)
  (let ((dims (ARRAY-DIMENSIONS array)))
    (if (< axis (length dims))
	(nth axis dims)
	(ERROR "ARRAY-DIMENSION axis out of range."))))

(defun ARRAY-DIMENSIONS (array)
  (cond
    ((or (stringp array)
	 (bit-vector-p array))	(list (length array)))
    ((SIMPLE-VECTOR-P array)	(list (1- (length array))))
    ((VECTORP array)		(list (vector-size array)))
    ((ARRAYP array)		(array-dims array))
    (t				(type-error array 'ARRAY))))

(defun ARRAY-ELEMENT-TYPE (array)
  (cond
    ((stringp array)			'CHARACTER)
    ((bit-vector-p array)		'BIT)
    ((vectorp array)
     (case (aref array 0)
       ((BIT-VECTOR bit-array)		'BIT)
       ((STRING char-array)		'CHARACTER)
       ((SIMPLE-VECTOR VECTOR ARRAY)	'T)
       (t				(type-error array 'ARRAY))))
    (t					(type-error array 'ARRAY))))

(defun ARRAY-HAS-FILL-POINTER-P (array)
  (unless (ARRAYP array)
    (type-error array 'ARRAY))
  (and (vectorp array)
       (memq (aref array 0) '(VECTOR STRING BIT-VECTOR))))

(defun ARRAY-DISPLACEMENT (array)
  (unless (ARRAYP array)
    (type-error array 'ARRAY))
  (if (or (bit-vector-p array)
	  (stringp array)
	  (eq (aref array 0) 'SIMPLE-VECTOR))
      (cl:values nil 0)
      (cl:values (array-storage array) (array-offset array))))

(defun ARRAY-IN-BOUNDS-P (array &rest subscripts)
  (unless (ARRAYP array)
    (type-error array 'ARRAY))
  (and (not (some #'MINUSP subscripts))
       (every #'cl:< subscripts (ARRAY-DIMENSIONS array))))

(defun ARRAY-RANK (array)
  (unless (ARRAYP array)
    (type-error array 'ARRAY))
  (length (ARRAY-DIMENSIONS array)))

(defun ARRAY-ROW-MAJOR-INDEX (array &rest subscripts)
  (unless (ARRAYP array)
    (type-error array 'ARRAY))
  (apply #'cl:+ (maplist (lambda (x y) (cl:* (car x) (apply #'cl:* (cdr y))))
			 subscripts (ARRAY-DIMENSIONS array))))

(defun ARRAY-TOTAL-SIZE (array)
  (unless (ARRAYP array)
    (type-error array 'ARRAY))
  (reduce #'* (ARRAY-DIMENSIONS array)))

(defun ARRAYP (object)
  (or (stringp object)
      (bit-vector-p object)
      (and (vectorp object)
	   (case (aref object 0)
	     ((BIT-VECTOR bit-array STRING char-array
	       SIMPLE-VECTOR VECTOR ARRAY) T)))))

(defun FILL-POINTER (vector)
  (unless (ARRAY-HAS-FILL-POINTER-P vector)
    (ERROR 'TYPE-ERROR))
  (vector-fp vector))

(defsetf FILL-POINTER (vector) (fill-pointer)
  `(setf (vector-fp ,vector) ,fill-pointer))

(DEFSETF FILL-POINTER (vector) (fill-pointer)
  `(aset ,vector 4 ,fill-pointer))

(defun ROW-MAJOR-AREF (array index)
  (cond
    ((VECTORP array)
     (AREF array index))
    ((ARRAYP array)
     (aref (array-storage array) index))
    (t
     (type-error array 'ARRAY))))

(defsetf ROW-MAJOR-AREF (array index) (new)
  `(cond
    ((VECTORP ,array)
     (setf (AREF ,array ,index) ,new))
    ((ARRAYP array)
     (aset (array-storage ,array) ,index ,new))
    (t
     (type-error array 'ARRAY))))

(defun UPGRADED-ARRAY-ELEMENT-TYPE (type &optional env)
  (case type
    ((nil)		nil)
    (BIT		'BIT)
    (CHARACTER		'CHARACTER)
    (T			'T)
    (t
     (subtypecase type
       (BIT		'BIT)
       (CHARACTER	'CHARACTER)
       (T		'T)))))

(DEFCONSTANT ARRAY-DIMENSION-LIMIT (/ MOST-POSITIVE-FIXNUM 10))
(DEFCONSTANT ARRAY-RANK-LIMIT 100) ;(/ MOST-POSITIVE-FIXNUM 10))
(DEFCONSTANT ARRAY-TOTAL-SIZE-LIMIT (/ MOST-POSITIVE-FIXNUM 10))

(defun SIMPLE-VECTOR-P (object)
  (vector-and-typep object 'SIMPLE-VECTOR))

(defun SVREF (vector index)
  (aref vector (1+ index)))

(defsetf SVREF (vector index) (object)
  `(setf (aref ,vector (1+ ,index)) ,object))

(DEFINE-SETF-EXPANDER SVREF (vector index)
  (let ((object (gensym))
	(vtemp (gensym))
	(itemp (gensym)))
    (cl:values (list vtemp itemp)
	       (list vector index)
	       (list object)
	       `(SET-SVREF ,object ,vtemp ,itemp)
	       `(SVREF ,vtemp ,itemp))))

(defun SET-SVREF (object vector index)
  (aset vector (1+ index) object))

(defun VECTOR (&rest objects)
  (let ((vector (make-simple-vector (length objects) nil))
	(i 0))
    (dolist (obj objects vector)
      (aset vector (incf i) obj))))

(defun VECTOR-POP (vector)
  (unless (and (VECTORP vector)
	       (ARRAY-HAS-FILL-POINTER-P vector)
	       (plusp (FILL-POINTER vector)))
    (error "error"))
  (aref (vector-storage vector) (decf (vector-fp vector))))

(defun VECTOR-PUSH (object vector)
  (unless (and (VECTORP vector) (ARRAY-HAS-FILL-POINTER-P vector))
    (error "error"))
  (let ((ptr (FILL-POINTER vector))
	(storage (vector-storage vector)))
    (unless (eq ptr (vector-size vector))
      (aset storage ptr (ecase (aref vector 0)
			  (BIT-VECTOR	(if object 1 0))
			  (STRING	(CHAR-CODE object))
			  (VECTOR	object)))
      (setf (vector-fp vector) (1+ ptr)))))

(defun VECTOR-PUSH-EXTEND (object vector &optional extension)
  (unless (and (VECTORP vector) (ARRAY-HAS-FILL-POINTER-P vector))
    (type-error vector '(AND VECTOR (NOT SIMPLE-VECTOR))))
  (let ((storage (vector-storage vector))
	(len (vector-size vector))
	(ptr (FILL-POINTER vector)))
    (when (eq ptr len)
      (let ((new-storage (make-vector (+ len (or extension len)) nil)))
	(dotimes (i len)
	  (aset new-storage i (aref storage i)))
	(setf (vector-storage vector) (setq storage new-storage))))
    (aset storage ptr (ecase (aref vector 0)
			(BIT-VECTOR	(if object 1 0))
			(STRING		(CHAR-CODE object))
			(VECTOR		object)))
    (setf (vector-fp vector) (1+ ptr))))

(defun VECTORP (object)
  (or (stringp object)
      (bit-vector-p object)
      (and (vectorp object)
	   (case (aref object 0)
	     ((STRING BIT-VECTOR VECTOR SIMPLE-VECTOR) T)))))

(defun BIT (array &rest subscripts)
  (cond
    ((SIMPLE-BIT-VECTOR-P array)
     (bref array (just-one subscripts)))
    ((BIT-VECTOR-P array)
     (bref (array-storage array) (just-one subscripts)))
    ((vector-and-typep array 'bit-array)
     (bref (array-storage array) (apply #'ARRAY-ROW-MAJOR-INDEX subscripts)))
    (t
     (type-error array '(ARRAY ,star BIT)))))

(defsetf BIT set-bit)

(DEFSETF BIT set-bit)

(defun set-bit (array index bit)
  (cond
    ((SIMPLE-BIT-VECTOR-P array)
     (setf (SBIT array index) bit))
    ((BIT-VECTOR-P array)
     (setf (SBIT (array-storage array) index) bit))
    ((vector-and-typep array 'bit-array)
     (setf (SBIT (array-storage array) index) bit))
    (t
     (type-error array '(ARRAY ,star BIT)))))

(defun SBIT (array index)
  (bref array index))

(defsetf SBIT set-sbit)

(DEFSETF SBIT set-sbit)

(defun set-sbit (array index bit)
  (setf (bref array index) bit))

(defun bit-array-p (object)
  (or (bit-vector-p object)
      (vector-and-typep object 'bit-array)))

(defun default-result (array result)
  (cond
    ((bit-array-p result)	result)
    ((eq result T)		array)
    (t				(if (BIT-VECTOR-P array)
				    (make-bit-vector (LENGTH array) 0)
				    (vector 'bit-array
					    (ARRAY-DIMENSIONS array)
					    (make-bit-vector
					     (ARRAY-TOTAL-SIZE array) 0))))))

(defun BIT-AND (array1 array2 &optional result)
  (let ((result (default-result array1 result))
	(storage1 (if (bit-vector-p array1) array1 (array-storage array1)))
	(storage2 (if (bit-vector-p array2) array2 (array-storage array2))))
    (dotimes (i (ARRAY-TOTAL-SIZE result))
      (aset result i (and (aref storage1 i) (aref storage2 i))))))

(defun BIT-ANDC1 (array1 array2 &optional result)
  (BIT-AND (BIT-NOT array1) array2 result))

(defun BIT-ANDC2 (array1 array2 &optional result)
  (BIT-AND (BIT-NOT array1) array2 result))

(defun BIT-EQV (array1 array2 &optional result)
  (BIT-NOT (BIT-XOR array1 array2 result)))

(defun BIT-IOR (array1 array2 &optional result)
  (let ((result (default-result array1 result))
	(storage1 (if (bit-vector-p array1) array1 (array-storage array1)))
	(storage2 (if (bit-vector-p array2) array2 (array-storage array2))))
    (dotimes (i (ARRAY-TOTAL-SIZE result))
      (aset result i (or (aref storage1 i) (aref storage2 i))))))

(defun BIT-NAND (array1 array2 &optional result)
  (BIT-NOT (BIT-AND array1 array2 result)))

(defun BIT-NOR (array1 array2 &optional result)
  (BIT-NOT (BIT-IOR array1 array2 result)))

(defun BIT-ORC1 (array1 array2 &optional result)
  (BIT-IOR (BIT-NOT array1) array2 result))

(defun BIT-ORC2 (array1 array2 &optional result)
  (BIT-IOR array1 (BIT-NOT array2) result))

(defun binary-xor (x y)
  (and (or x y)
       (not (and x y))))

(defun BIT-XOR (array1 array2 &optional result)
  (let ((result (default-result array1 result))
	(storage1 (if (bit-vector-p array1) array1 (array-storage array1)))
	(storage2 (if (bit-vector-p array2) array2 (array-storage array2))))
    (dotimes (i (ARRAY-TOTAL-SIZE result))
      (aset result i (binary-xor (aref storage1 i) (aref storage2 i))))))

(defun BIT-NOT (array &optional result)
  (let ((result (default-result array result))
	(storage (if (bit-vector-p array) array (array-storage array))))
    (dotimes (i (ARRAY-TOTAL-SIZE array))
      (aset result i (not (aref storage i))))))

(defun BIT-VECTOR-P (object)
  (or (bit-vector-p object)
      (vector-and-typep object 'BIT-VECTOR)))

(defun SIMPLE-BIT-VECTOR-P (object)
  (bit-vector-p object))
