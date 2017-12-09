;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 22, Printer.

(IN-PACKAGE "EMACS-CL")

(cl:defun COPY-PPRINT-DISPATCH (&OPTIONAL (table *PRINT-PPRINT-DISPATCH*))
  (unless table
    (setq table *initial-pprint-dispatch*))
  (let ((copy (make-hash-table :test #'equal)))
    (maphash (lambda (k v) (setf (gethash k copy) (cons (car v) (cdr v)))
		     table)
    copy)))

;;; FORMATTER is defined in cl-format.el.

(cl:defun PPRINT-DISPATCH (object &OPTIONAL (table *PRINT-PPRINT-DISPATCH*))
  (unless table
    (setq table *initial-pprint-dispatch*))
  (let ((fn nil)
	(priority nil))
    (maphash (lambda (k v)
	       (when (and (TYPEP object k)
			  (or (null priority)
			      (cl:> (cdr v) priority)))
		 (setq fn (car v)
		       priority (cdr v))))
	     table)
    (cl:values fn priority)))

;;; TODO: Local Macro PPRINT-EXIT-IF-LIST-EXHAUSTED

;;; TODO: Function PPRINT-FILL
;;; TODO:          PPRINT-LINEAR
;;; TODO:          PPRINT-TABULAR

;;; TODO: Function PPRINT-INDENT

;;; TODO: Macro PPRINT-LOGICAL-BLOCK

;;; TODO: Function PPRINT-NEWLINE

;;; TODO: Local Macro PPRINT-POP

;;; TODO: Function PPRINT-TAB

(defvar *print-circle-table* nil)
(defvar *print-circle-counter* 0)

(defun check-circles (object)
  (unless (or (symbolp object)
	      (and (vectorp object) (eql (length object) 0))
	      (INTEGERP object))
    (let ((n (gethash object *print-circle-table*)))
      (cond
	((null n)
	 (setf (gethash object *print-circle-table*) t)
	 (cond
	   ((consp object)
	    (check-circles (car object))
	    (check-circles (cdr object)))
	   ((arrayp object)
	    (dotimes (i (length object))
	      (check-circles (aref object i))))))
	((eq n 0))
	(t
	 (setf (gethash object *print-circle-table*) 0))))))

(defun write-object (object stream)
  (if *PRINT-CIRCLE*
      (if *print-circle-table*
	  (let ((n (gethash object *print-circle-table*)))
	    (cond
	      ((eq n 0)
	       (WRITE-CHAR (ch 35) stream)
	       (print-integer (setf (gethash object *print-circle-table*)
				    (incf *print-circle-counter*))
			      stream 10)
	       (WRITE-CHAR (ch 61) stream)
	       (PRINT-OBJECT object stream))
	      ((integerp n)
	       (WRITE-CHAR (ch 35) stream)
	       (print-integer n stream 10)
	       (WRITE-CHAR (ch 35) stream))
	      (t
	       (PRINT-OBJECT object stream))))
	  (let ((*print-circle-table* (make-hash-table))
		(*print-circle-counter* 0))
	    (check-circles object)
	    (write-object object stream)))
      (or (and *PRINT-PRETTY*
	       (MULTIPLE-VALUE-BIND (fn found) (PPRINT-DISPATCH object)
		 (when found
		   (FUNCALL fn stream object)
		   t)))
	  (PRINT-OBJECT object stream))))

(defun positive-integer-p (object)
  (and (integerp object) (plusp object)))

;;; TODO: PRINT-OBJECT should be a generic function
(defun built-in-print-object (object stream)
  (cond
    ((INTEGERP object)
     (print-integer object stream *PRINT-BASE* *PRINT-RADIX*))
    ((floatp object)
     ;; http://www.common-lisp.net/paste/display/743
     (print-float object stream))
    ((symbolp object)
     (let ((name (SYMBOL-NAME object)))
       (if (printer-escaping-p)
	   (progn
	     (print-symbol-prefix object stream)
	     (print-symbol-name name stream))
	   (cond
	     ((eq *PRINT-CASE* (kw UPCASE))
	      (WRITE-STRING name stream))
	     ((eq *PRINT-CASE* (kw DOWNCASE))
	      (WRITE-STRING (STRING-DOWNCASE name) stream))
	     ((eq *PRINT-CASE* (kw CAPITALIZE))
	      (WRITE-STRING (symbol-name-capitalize name) stream))
	     (t
	      (type-error *PRINT-CASE* `(MEMBER ,(kw UPCASE) ,(kw DOWNCASE)
						,(kw CAPITALIZE))))))))
    ((CHARACTERP object)
     (if (printer-escaping-p)
	 (progn
	   (WRITE-STRING "#\\" stream)
	   (WRITE-STRING (or (and (ch= object 32) " ")
			     (CHAR-NAME object)
			     (string (CHAR-CODE object)))
			 stream))
	 (WRITE-CHAR object stream)))
    ((consp object)
     (let ((n 0))
       (WRITE-STRING "(" stream)
       (write-object (car object) stream)
       (setq object (cdr object))
       (while (consp object)
	 (if (and *print-circle-table*
		  (positive-integer-p (gethash object *print-circle-table*)))
	     (progn
	       (WRITE-STRING " . " stream)
	       (write-object object stream)
	       (setq object nil))
	     (progn
	       (WRITE-STRING " " stream)
	       (write-object (car object) stream)
	       (setq object (cdr object))
	       (when (and *PRINT-LENGTH* (cl:>= (incf n) *PRINT-LENGTH*))
		 (WRITE-STRING " ..." stream)
		 (setq object nil)))))
       (unless (null object)
	 (WRITE-STRING " . " stream)
	 (write-object object stream)))
     (WRITE-STRING ")" stream))
    ((FUNCTIONP object)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t (kw IDENTITY) t)
       (PRINC (function-name object) stream)))
    ((ratiop object)
     (WRITE (NUMERATOR object) (kw STREAM) stream)
     (WRITE-STRING "/" stream)
     (WRITE (DENOMINATOR object) (kw STREAM) stream (kw RADIX) nil))
    ((COMPLEXP object)
     (WRITE-STRING "#C(" stream)
     (WRITE (REALPART object) (kw STREAM) stream)
     (WRITE-STRING " " stream)
     (WRITE (IMAGPART object) (kw STREAM) stream)
     (WRITE-STRING ")" stream))
    ((BIT-VECTOR-P object)
     (cond
       (*PRINT-ARRAY*
	(WRITE-STRING "#*" stream)
	(dotimes (i (LENGTH object))
	  (PRIN1 (AREF object i) stream)))
       (t
	(PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t
						(kw IDENTITY) t)))))
    ((STRINGP object)
     (cond
       (*PRINT-ESCAPE*
	(WRITE-CHAR (ch 34) stream)
	(dotimes (i (LENGTH object))
	  (let ((char (CHAR object i)))
	    (case (CHAR-CODE char)
	      (34	(WRITE-STRING "\\\"" stream))
	      (92	(WRITE-STRING "\\\\" stream))
	      (t	(WRITE-CHAR char stream)))))
	(WRITE-CHAR (ch 34) stream))
       (t
	(WRITE-STRING object stream))))
    ((VECTORP object)
     (if *PRINT-ARRAY*
	 (let ((*PRINT-LENGTH* (if (BIT-VECTOR-P object) nil *PRINT-LENGTH*)))
	   (WRITE-STRING "#(" stream)
	   (catch 'too-long
	     (dotimes (i (LENGTH object))
	       (when (> i 0)
		 (WRITE-STRING " " stream))
	       (PRIN1 (AREF object i) stream)
	       (when (and *PRINT-LENGTH* (>= i *PRINT-LENGTH*))
		 (WRITE-STRING " ..." stream)
		 (throw 'too-long nil))))
	   (WRITE-STRING ")" stream))
	 (PRINT-UNREADABLE-OBJECT (object stream
				   (kw TYPE) t (kw IDENTITY) t))))
    ((ARRAYP object)
     (cond
       (*PRINT-ARRAY*
	(print-array object stream))
       (t
	(PRINT-UNREADABLE-OBJECT (object stream
				  (kw TYPE) t (kw IDENTITY) t)))))
    ((PACKAGEP object)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t)
       (PRIN1 (PACKAGE-NAME object) stream)))
    ((READTABLEP object)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t (kw IDENTITY) t)))
    ((TYPEP object 'FILE-STREAM)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t (kw IDENTITY) t)
       (PRIN1 (FILE-STREAM-filename object) stream)))
    ((STREAMP object)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t (kw IDENTITY) t)))
    ((TYPEP object 'CONDITION)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t (kw IDENTITY) t)))
    ((restartp object)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t (kw IDENTITY) t)
       (PRIN1 (RESTART-NAME object) stream)
       (when (RESTART-condition object)
	 (WRITE-STRING " " stream)
	 (PRIN1 (RESTART-condition object) stream))))
    ((PATHNAMEP object)
     (WRITE-STRING "#P" stream)
     (PRIN1 (NAMESTRING object) stream))
    ((structurep object)
     (WRITE-STRING "#S(" stream)
     (PRIN1 (TYPE-OF object) stream)
     (let ((index 0))
       (dolist (slot (struct-slots (aref object 0)))
	 (FORMAT stream " :~A ~S"
		 (SYMBOL-NAME (first slot)) (aref object (incf index)))))
     (WRITE-CHAR (ch 41) stream))
    ((classp object)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t)
       (PRIN1 (class-name object) stream)))
    ((subclassp (CLASS-OF object) +standard-object+)
     (PRINT-UNREADABLE-OBJECT (object stream (kw TYPE) t (kw IDENTITY) t)))
    (t
     ;; TODO:
     (if *PRINT-READABLY*
	 (ERROR 'PRINT-NOT-READABLE (kw OBJECT) object)
	 (WRITE-STRING "#<FIXME:UNPRINTABLE>" stream))))
  (cl:values object))

(defvar *object-identities* (make-hash-table :test #'eq :weakness t))

(defvar *identity-counter* 12345)

(defun object-identity (object)
  ;; TODO: Perhaps flush a non-weak hash table occasionally.
  (or (gethash object *object-identities*)
      (setf (gethash object *object-identities*) (incf *identity-counter*))))

(defmacro* PRINT-UNREADABLE-OBJECT ((object stream &rest keys) &body body)
  `(print-unreadable-object ,object ,stream (lambda () ,@body) ,@keys))

(cl:defmacro PRINT-UNREADABLE-OBJECT ((object stream &rest keys) &body body)
  `(print-unreadable-object ,object ,stream (LAMBDA () ,@body) ,@keys))

(cl:defun print-unreadable-object (object stream fn &KEY TYPE IDENTITY)
  (when *PRINT-READABLY*
    (ERROR 'PRINT-NOT-READABLE (kw OBJECT) object))
  (WRITE-STRING "#<" stream)
  (when TYPE
    (PRIN1 (TYPE-OF object) stream)
    (WRITE-STRING " " stream))
  (FUNCALL fn)
  (when IDENTITY
    (WRITE-STRING " {" stream)
    (PRIN1 (object-identity object) stream)
    (WRITE-STRING "}" stream))
  (WRITE-STRING ">" stream)
  nil)

(cl:defun SET-PPRINT-DISPATCH (type fn
			       &OPTIONAL (priority 0)
					 (table *PRINT-PPRINT-DISPATCH*))
  (if (null fn)
      (remhash type table)
      (setf (gethash type table) (cons fn priority)))
  nil)

(defun external-symbol-p (symbol)
  (eq (NTH-VALUE 1 (FIND-SYMBOL (SYMBOL-NAME symbol) (SYMBOL-PACKAGE symbol)))
      kw:EXTERNAL))

(defun print-symbol-prefix (symbol stream)
  (cond
    ((eq (SYMBOL-PACKAGE symbol) *keyword-package*)
     (WRITE-STRING ":" stream))
    ((eq (NTH-VALUE 0 (FIND-SYMBOL (SYMBOL-NAME symbol) *PACKAGE*)) symbol))
    ((null (SYMBOL-PACKAGE symbol))
     (when *PRINT-GENSYM*
       (WRITE-STRING "#:" stream)))
    (t
     (WRITE-STRING (PACKAGE-NAME (SYMBOL-PACKAGE symbol)) stream)
     (WRITE-STRING (if (external-symbol-p symbol) ":" "::") stream))))

(defun print-symbol-name (name stream)
  (let* ((read-sym (unless (EQUAL name "")
		     (READ-FROM-STRING name)))
	 (escape (not (and (symbolp read-sym)
			   (string= name (SYMBOL-NAME read-sym))))))
    (when escape
      (WRITE-STRING "|" stream))
    (WRITE-STRING (cond
		    (escape
		     name)
		    ((eq *PRINT-CASE* (kw UPCASE))
		     name)
		    ((eq *PRINT-CASE* (kw DOWNCASE))
		     (STRING-DOWNCASE name))
		    ((eq *PRINT-CASE* (kw CAPITALIZE))
		     (symbol-name-capitalize name))
		    (t
		     (type-error *PRINT-CASE*
				 `(MEMBER ,(kw UPCASE) ,(kw DOWNCASE)
					  ,(kw CAPITALIZE)))))
		  stream)
    (when escape
      (WRITE-STRING "|" stream))))

(defun printer-escaping-p ()
  (or *PRINT-READABLY* *PRINT-ESCAPE*))

(cl:defun WRITE (object &KEY
		 (ARRAY *PRINT-ARRAY*)
		 (BASE *PRINT-BASE*)
		 (CASE *PRINT-CASE*)
		 (CIRCLE *PRINT-CIRCLE*)
		 (ESCAPE *PRINT-ESCAPE*)
		 (GENSYM *PRINT-GENSYM*)
		 (LENGTH *PRINT-LENGTH*)
		 (LEVEL *PRINT-LEVEL*)
		 (LINES *PRINT-LINES*)
		 (MISER-WIDTH *PRINT-MISER-WIDTH*)
		 (PPRINT-DISPATCH *PRINT-PPRINT-DISPATCH*)
		 (PRETTY *PRINT-PRETTY*)
		 (RADIX *PRINT-RADIX*)
		 (READABLY *PRINT-READABLY*)
		 (RIGHT-MARGIN *PRINT-RIGHT-MARGIN*)
		 STREAM)
  (let ((stream (output-stream STREAM))
	(*PRINT-ARRAY* ARRAY)
	(*PRINT-BASE* BASE)
	(*PRINT-CASE* CASE)
	(*PRINT-CIRCLE* CIRCLE)
	(*PRINT-ESCAPE* ESCAPE)
	(*PRINT-GENSYM* GENSYM)
	(*PRINT-LENGTH* LENGTH)
	(*PRINT-LEVEL* LEVEL)
	(*PRINT-LINES* LINES)
	(*PRINT-MISER-WIDTH* MISER-WIDTH)
	(*PRINT-PPRINT-DISPATCH* PPRINT-DISPATCH)
	(*PRINT-PRETTY* PRETTY)
	(*PRINT-RADIX* RADIX)
	(*PRINT-READABLY* READABLY)
	(*PRINT-RIGHT-MARGIN* RIGHT-MARGIN))
    (write-object object stream))
  (cl:values object))

(defun symbol-name-capitalize (string)
  (setq string (copy-sequence string))
  (do ((i 0 (1+ i))
       (in-word-p nil))
      ((eq i (length string))
       string)
    (let* ((char (CHAR string i))
	   (alnump (ALPHANUMERICP char)))
      (when (UPPER-CASE-P char)
	(setf (CHAR string i)
	      (if in-word-p (CHAR-DOWNCASE char) (CHAR-UPCASE char))))
      (setq in-word-p alnump))))

(cl:defun print-integer (number stream &OPTIONAL (base 10) radix)
  (when radix
    (case base
      (2	(WRITE-STRING "#b" stream))
      (8	(WRITE-STRING "#o" stream))
      (10)
      (16	(WRITE-STRING "#x" stream))
      (t	(WRITE-CHAR (ch 35) stream)
		(print-integer base stream)
		(WRITE-STRING (ch 114) stream))))
  (cond
    ((ZEROP number)
     (WRITE-STRING "0" stream))
    ((MINUSP number)
     (WRITE-STRING "-" stream)
     (setq number (cl:- number))))
  (print-digits number stream base)
  (when (and radix (eq base 10))
    (WRITE-STRING "." stream)))

(defun print-digits (number stream base)
  (when (PLUSP number)
    (MULTIPLE-VALUE-BIND (number digit) (TRUNCATE number base)
      (print-digits number stream base)
      (WRITE-CHAR (AREF "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ" digit)
		  stream))))

(defun write-char-to-*standard-output* (char)
  (WRITE-CHAR (cl-char char) *STANDARD-OUTPUT*))

(defun print-float (float stream)
  ;; http://www.common-lisp.net/paste/display/743
  (let ((*STANDARD-OUTPUT* stream)
	(standard-output #'write-char-to-*standard-output*))
    (prin1 float)))

(defun print-array (array stream)
  (let ((dims (ARRAY-DIMENSIONS array)))
    (WRITE-CHAR (ch 35) stream)
    (print-integer (LENGTH dims) stream)
    (WRITE-CHAR (ch 65) stream)
    (if (zerop (LENGTH dims))
	(WRITE-CHAR (ch 48) stream)
	(print-array-elts array stream dims '()))))

(defun print-array-elts (array stream dims indices)
  (if (null dims)
      (PRIN1 (apply #'AREF array indices))
      (progn
	(WRITE-CHAR (ch 40) stream)
	(dotimes (i (first dims))
	  (when (> i 0)
	    (WRITE-STRING " " stream))
	  (print-array-elts array stream (rest dims)
			    (append indices (list i))))
	(WRITE-CHAR (ch 41) stream))))

(defun PRIN1 (object &optional stream)
  (WRITE object (kw STREAM) stream (kw ESCAPE) t))

(defun PRINT (object &optional stream)
  (TERPRI stream)
  (PRIN1 object stream)
  (WRITE-CHAR (ch 32) stream)
  object)

(cl:defun PPRINT (object &OPTIONAL stream)
  (TERPRI stream)
  (WRITE object (kw STREAM) stream (kw ESCAPE) t (kw PRETTY) t)
  (cl:values))

(cl:defun PRINC (object &OPTIONAL stream)
  (WRITE object (kw STREAM) stream (kw ESCAPE) nil (kw READABLY) nil))

(cl:defun WRITE-TO-STRING (object &REST keys)
  (WITH-OUTPUT-TO-STRING (stream)
    (apply (cl:function WRITE) object (kw STREAM) stream keys)))

(cl:defun PRIN1-TO-STRING (object)
  (WITH-OUTPUT-TO-STRING (stream)
    (PRIN1 object stream)))

(cl:defun PRINC-TO-STRING (object)
  (WITH-OUTPUT-TO-STRING (stream)
    (PRINC object stream)))

(DEFVAR *PRINT-ARRAY* T)

(DEFVAR *PRINT-BASE* 10)

(DEFVAR *PRINT-RADIX* nil)

(DEFVAR *PRINT-CASE* (kw UPCASE))

(DEFVAR *PRINT-CIRCLE* nil)

(DEFVAR *PRINT-ESCAPE* nil)

(DEFVAR *PRINT-GENSYM* T)

(DEFVAR *PRINT-LEVEL* nil)

(DEFVAR *PRINT-LENGTH* nil)

(DEFVAR *PRINT-LINES* nil)

(DEFVAR *PRINT-MISER-WIDTH* nil)

(defvar *initial-pprint-dispatch*
  (let ((table (make-hash-table :test #'equal)))
    (SET-PPRINT-DISPATCH '(CONS (EQL QUOTE) (CONS T NULL))
			 (lambda (stream object)
			   (WRITE-CHAR (ch 39) stream)
			   (write-object (second object) stream))
			 100 table)
    (SET-PPRINT-DISPATCH '(CONS (EQL FUNCTION) (CONS T NULL))
			 (lambda (stream object)
			   (WRITE-STRING "#'" stream)
			   (write-object (second object) stream))
			 100 table)
    (SET-PPRINT-DISPATCH '(CONS (EQL LAMBDA) CONS)
			 (lambda (stream object)
			   (WRITE-STRING "(LAMBDA " stream)
			   (if (null (second object))
			       (WRITE-STRING "()" stream)
			       (write-object (second object) stream))
			   (dolist (x (cddr object))
			     (WRITE-CHAR (ch 32) stream)
			     (write-object x stream))
			   (WRITE-CHAR (ch 41) stream))
			 100 table)
    (SET-PPRINT-DISPATCH '(CONS (EQL DEFUN) (CONS T (CONS LIST LIST)))
			 (lambda (stream object)
			   (WRITE-STRING "(DEFUN " stream)
			   (write-object (second object) stream)
			   (WRITE-CHAR (ch 32) stream)
			   (if (null (third object))
			       (WRITE-STRING "()" stream)
			       (write-object (third object) stream))
			   (dolist (x (cdddr object))
			     (FORMAT stream "~%  ")
			     (write-object x stream))
			   (WRITE-CHAR (ch 41) stream))
			 100 table)
    (SET-PPRINT-DISPATCH '(CONS (EQL BACKQUOTE) (CONS T NULL))
			 (lambda (stream object)
			   (WRITE-STRING "`" stream)
			   (write-object (second object) stream))
			 100 table)
    (SET-PPRINT-DISPATCH '(CONS (EQL COMMA) (CONS T NULL))
			 (lambda (stream object)
			   (WRITE-STRING "," stream)
			   (let ((obj (second object)))
			     (when (and (symbolp obj)
					(find (aref (symbol-name obj) 0) ".@"))
			       (WRITE-CHAR (ch 32) stream))
			     (write-object obj stream)))
			 100 table)
    (SET-PPRINT-DISPATCH '(CONS (EQL COMMA-AT) (CONS T NULL))
			 (lambda (stream object)
			   (WRITE-STRING ",@" stream)
			   (write-object (second object) stream))
			 100 table)
    table))

(DEFVAR *PRINT-PPRINT-DISPATCH* *initial-pprint-dispatch*)

(DEFVAR *PRINT-PRETTY* nil)

(DEFVAR *PRINT-READABLY* nil)

(DEFVAR *PRINT-RIGHT-MARGIN* nil)

;;; PRINT-NOT-READABLE and PRINT-NOT-READABLE-OBJECT defined in
;;; cl-conditions.el.
