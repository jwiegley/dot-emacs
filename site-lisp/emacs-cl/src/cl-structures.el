;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 8, Structures.

(IN-PACKAGE "EMACS-CL")

(defvar *initial-classes* nil)

;;; Redefined later.
(defun ENSURE-CLASS (name &rest keys)
  (unless (memq (kw METACLASS) keys)
    (setq keys (list* (kw METACLASS) 'STANDARD-CLASS keys)))
  (push (cons name keys) *initial-classes*)
  (ensure-type
   name
   (byte-compile `(lambda (obj env)
		    (and (vectorp obj)
			 (struct-subtypep (aref obj 0) ',name))))))

;;; A hash table keyed on a structure name.  The data is a cons which
;;; car is a list of structure names that are subtypes of the key.
;;; The cdr is a list of slot descriptions in the form `(,name
;;; ,initval ,type ,read-only).
(defvar *structure-info* (make-hash-table))

(defun struct-subtypep (type1 type2)
  (or (eq type1 type2)
      (let ((subtypes (car (gethash type2 *structure-info*))))
	(if (memq type1 subtypes)
	    T
	    (some (lambda (type)
		    (and (struct-subtypep type1 type)
			 (struct-subtypep type type2)))
		  subtypes)))))

(defun add-struct-subtype (struct sub)
  (maphash (lambda (key val)
	     (setf (car val) (delete sub (car val))))
	   *structure-info*)
  (push sub (car (gethash struct *structure-info*))))

(defun structurep (object)
  (and (vectorp object)
       (gethash (aref object 0) *structure-info*)))

(defun struct-slots (struct)
  (cdr (gethash struct *structure-info*)))

(defsetf struct-slots (struct) (slots)
  `(setf (gethash ,struct *structure-info*) (cons nil ,slots)))

(defun slot-name (slot)
  (first slot))

(defun slot-initval (slot)
  (second slot))

(defun slot-type (slot)
  (third slot))

(defun slot-read-only-p (slot)
  (fourth slot))

(defun canonicalize-slot (slot)
  (cond
    ((atom slot)
     (list slot unbound t nil))
    ((= (length slot) 1)
     (list (first slot) unbound t nil))
    (t
     (list (first slot) (second slot)
	   (getf (cddr slot) (kw TYPE) T)
	   (getf (cddr slot) (kw READ-ONLY))))))

(defun param-with-default (param slots)
  (cond
    ((consp param)
     (if (> (length param) 1)
	 param
	 (param-with-default (first param) slots)))
    ((let ((slot (find param slots :key #'slot-name)))
       (when slot
	 (list param (slot-initval slot)))))
    (t
     param)))

(defun lambda-list-with-defaults (lambda-list slots)
  (let ((required t))
    (mapcar
     (lambda (param)
       (cond
	 ;; A lambda list keyword is passed
	 ;; through unchanged.
	 ((member param LAMBDA-LIST-KEYWORDS)
	  (setq required nil)
	  param)
	 ;; A required argument is passed
	 ;; through unchanged.
	 (required
	  param)
	 ;; If a non-required argument
	 ;; doesn't have a default value,
	 ;; supply the default value of the
	 ;; slot.
	 (t
	  (param-with-default param slots))))
     lambda-list)))

(defun slot-name-or-initval (slot constructor)
  (let ((name (slot-name slot))
	(initval (slot-initval slot))
	(lambda-list (second constructor)))
    (if ;(member name lambda-list)
        (some (lambda (parm)
		(or (eq name parm)
		    (and (consp parm) (eq name (car parm)))))
	      lambda-list)
	name
	initval)))


;;; The defstruct macro proper.
(defmacro* DEFSTRUCT (name &rest slots)
  (multiple-value-bind (name options) (if (consp name)
					  (values (first name) (rest name))
					  (values name nil))
    (let ((conc-name		(strcat name "-"))
	  (constructors		nil)
	  (no-constructor	nil)
	  (copier		(symcat "COPY-" name))
	  (include		nil)
	  (initial-offset	nil)
	  (named		nil)
	  (predicate		nil)
	  (print-object		nil)
	  (print-function	nil)
	  (type			nil)
	  (struct-size		nil)
	  (unbound		nil))

      ;; Process structure options.
      (dolist (option options)
	(multiple-value-bind (name args) (if (atom option)
					     (values option nil)
					     (values (first option)
						     (rest option)))
	  (ecase name
	    (:conc-name		(setq conc-name (STRING (or (first args) ""))))
	    (:constructor	(ecase (length args)
				  (0)
				  (1	(if (null (first args))
					    (setq no-constructor t)
					    (push (first args)
						  constructors)))
				  (2	(push args constructors))))
	    (:copier		(setq copier (first args)))
	    (:include		(setq include args))
	    (:initial-offset	(setq initial-offset (first args)))
	    (:named		(setq named t))
	    (:predicate		(setq predicate (first args)))
	    (:print-object	(setq print-object (first args)))
	    (:print-function	(setq print-function (first args)))
	    (:type		(setq type (first args))))))

      ;; Provide a default constructor if appropriate.
      (when (and (null constructors) (not no-constructor))
	(setq constructors (list (symcat "MAKE-" name))))

      ;; Calculate the effective slot list.
      (setq slots (mapcar #'canonicalize-slot slots))
      (when include
	(let ((included-slots (struct-slots (first include))))
	  (dolist (slot (rest include))
	    (setq slot (canonicalize-slot slot))
	    (setq included-slots
		  (nsubstitute
		   slot
		   (find (slot-name slot) included-slots :key #'slot-name)
		   included-slots)))
	  (setq slots (append included-slots slots))))

      ;; Calculate initial-offset and structure size.
      (when (and initial-offset (not type))
	(error ":initial-offset used without :type"))
      (unless initial-offset
	(setq initial-offset 0))
      (setq struct-size (+ initial-offset (length slots)))
      (unless (and type (not named))
	(incf struct-size))

      ;; Provide a default predicate if appropriate.
      (when (and type (not named) predicate)
	(error "error"))
      (unless predicate
	(setq predicate (symcat name "-P")))

      ;; Generate or process the lambda lists of the constructors.
      (setq constructors
	    (mapcar (lambda (constructor)
		      (if (atom constructor)
			  `(,constructor
			    ,(lambda-list-with-defaults
			      `(&KEY ,@(mapcar #'slot-name slots)) slots))
			  `(,(first constructor)
			    ,(lambda-list-with-defaults
			      (second constructor) slots))))
		    constructors))

      ;; Macro expansion.
      `(eval-when (:load-toplevel :execute)

	;; Constructors.
	,@(mapcar
	    (lambda (constructor)
	      `(cl:defun ,@constructor
		 ,(ecase type
		    ((nil)
		     `(let ((object (make-vector ,struct-size ',name)))
		        ,@(let ((index initial-offset))
			    (mapcar (lambda (slot)
				      `(aset object ,(incf index)
					     ,(slot-name-or-initval
					       slot constructor)))
				    slots))
		        object))
		    (vector
		     `(let ((object (MAKE-ARRAY ,struct-size)))
		        ,@(let ((index (1- initial-offset)))
			    `(,@(when named
				  `((setf (AREF object ,(incf index)) ',name)))
			      ,@(mapcar (lambda (slot)
					  `(setf (AREF object ,(incf index))
					         ,(slot-name-or-initval
						   slot constructor)))
					slots)))
		        object))
		    (list
		     `(list ,@(make-list initial-offset nil)
		            ,@(when named (list (list 'quote name)))
		            ,@(mapcar (lambda (slot)
					(slot-name-or-initval
					 slot constructor))
				      slots))))))
	    constructors)

	;; Copier.
	,@(when copier
	   `((defun ,copier (object)
	       (copy-sequence object))))

	;; Predicate.
	,@(when predicate
	    (multiple-value-bind (type-predicate get-type)
		(ecase type
		  ((nil)      (values 'vectorp '(aref object 0)))
		  (vector     (values 'VECTORP `(AREF object ,initial-offset)))
		  (list	      (values 'listp   `(nth ,initial-offset object))))
	      `((defun ,predicate (object)
		  (and (,type-predicate object)
		       (struct-subtypep ,get-type ',name))))))

	;; Remember information about the slots.
	(setf (struct-slots ',name) ',slots)

	;; Register the structure as a subtype of an included structure,
	,@(when include
	    `((add-struct-subtype ',(first include) ',name)))

	;; Define a new class (and type).
	,@(unless type
	   `((ENSURE-CLASS
	       ',name
	       (keyword "METACLASS") 'STRUCTURE-CLASS
	       (keyword "DIRECT-SUPERCLASSES")
	       '(,(if include (first include) 'STRUCTURE-OBJECT)))))

	;; Accessors.
	,@(let ((index initial-offset))
	    (when (or named (not type))
	      (incf index))
	    (mappend
	     (lambda (slot)
	       (multiple-value-bind (getter setter)
		   (ecase type
		     ((nil)
		      (values `(aref object ,index)
			      `(list 'aset object ,index new)))
		     (vector
		      (values `(AREF object ,index)
			      `(list 'setf (list 'AREF object ,index) new)))
		     (list
		      (values `(nth ,index object)
			      `(list 'setf (list 'nth ,index object) new))))
		 (incf index)
		 (let ((name (symcat conc-name (slot-name slot))))
		   `((defun ,name (object) ,getter)
		     ,@(unless (slot-read-only-p slot)
		         `((defsetf ,name (object) (new) ,setter)
		           (DEFSETF ,name (object) (new) ,setter)))))))
	       slots))

	;; Finally, return structure name.
	',name))))

;;; The defstruct macro proper.
(cl:defmacro DEFSTRUCT (name &rest slots)
  (multiple-value-bind (name options) (if (consp name)
					  (values (first name) (rest name))
					  (values name nil))
    (let ((conc-name		(strcat name "-"))
	  (constructors		nil)
	  (no-constructor	nil)
	  (copier		(cl:symcat "COPY-" name))
	  (include		nil)
	  (initial-offset	nil)
	  (named		nil)
	  (predicate		nil)
	  (print-object		nil)
	  (print-function	nil)
	  (type			nil)
	  (struct-size		nil)
	  (unbound		nil))

      ;; Process structure options.
      (dolist (option options)
	(multiple-value-bind (name args) (if (atom option)
					     (values option nil)
					     (values (first option)
						     (rest option)))
	  (cond
	    ((eq name (kw CONC-NAME))
	     (setq conc-name (STRING (or (first args) ""))))
	    ((eq name (kw CONSTRUCTOR))
	     (ecase (length args)
	       (0)
	       (1	(if (null (first args))
			    (setq no-constructor t)
			    (push (first args)
				  constructors)))
	       (2	(push args constructors))))
	    ((eq name (kw COPIER))
	     (setq copier (first args)))
	    ((eq name (kw INCLUDE))
	     (setq include args))
	    ((eq name (kw INITIAL-OFFSET))
	     (setq initial-offset (first args)))
	    ((eq name (kw NAMED))
	     (setq named t))
	    ((eq name (kw PREDICATE))
	     (setq predicate (first args)))
	    ((eq name (kw PRINT-OBJECT))
	     (setq print-object (first args)))
	    ((eq name (kw PRINT-FUNCTION))
	     (setq print-function (first args)))
	    ((eq name (kw TYPE))
	     (setq type (first args)))
	    (t
	     (ERROR "Unknown DEFSTRUCT option: ~S" name)))))

      (unless (SUBTYPEP type '(OR LIST VECTOR))
	(ERROR "Invalid defstruct option :type ~S." type))

      ;; Provide a default constructor if appropriate.
      (when (and (null constructors) (not no-constructor))
	(setq constructors (list (cl:symcat "MAKE-" name))))

      ;; Calculate the effective slot list.
      (setq slots (mapcar #'canonicalize-slot slots))
      (when include
	(let ((included-slots (struct-slots (first include))))
	  (dolist (slot (rest include))
	    (setq slot (canonicalize-slot slot))
	    (setq included-slots
		  (nsubstitute
		   slot
		   (find (slot-name slot) included-slots :key #'slot-name)
		   included-slots)))
	  (setq slots (append included-slots slots))))

      ;; Calculate initial-offset and structure size.
      (when (and initial-offset (not type))
	(ERROR ":initial-offset used without :type"))
      (unless initial-offset
	(setq initial-offset 0))
      (setq struct-size (+ initial-offset (length slots)))
      (unless (and type (not named))
	(incf struct-size))

      ;; Provide a default predicate if appropriate.
      (when (and type (not named) predicate)
	(ERROR "error"))
      (unless predicate
	(setq predicate (cl:symcat name "-P")))

      ;; Generate or process the lambda lists of the constructors.
      (setq constructors
	    (mapcar (lambda (constructor)
		      (if (atom constructor)
			  `(,constructor
			    ,(lambda-list-with-defaults
			      `(&KEY ,@(mapcar #'slot-name slots)) slots))
			  `(,(first constructor)
			    ,(lambda-list-with-defaults
			      (second constructor) slots))))
		    constructors))

      ;; Macro expansion.
      `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))

	;; Constructors.
	,@(mapcar
	    (lambda (constructor)
	      `(DEFUN ,@constructor
		 ,(subtypecase type
		    (nil
		     `(LET ((object (make-vector ,struct-size (QUOTE ,name))))
		        ,@(let ((index initial-offset))
			    (mapcar (lambda (slot)
				      `(aset object ,(incf index)
					     ,(slot-name-or-initval
					       slot constructor)))
				    slots))
		        object))
		    (VECTOR
		     `(LET ((object (MAKE-ARRAY ,struct-size)))
		        ,@(let ((index (1- initial-offset)))
			    `(,@(when named
				  `((SETF (AREF object ,(incf index))
				          (QUOTE ,name))))
			      ,@(mapcar (lambda (slot)
					  `(SETF (AREF object ,(incf index))
					         ,(slot-name-or-initval
						   slot constructor)))
					slots)))
		        object))
		    (LIST
		     `(LIST ,@(make-list initial-offset nil)
		            ,@(when named (list (list 'QUOTE name)))
		            ,@(mapcar (lambda (slot)
					(slot-name-or-initval
					 slot constructor))
				      slots))))))
	    constructors)

	;; Copier.
	,@(when copier
	   `((DEFUN ,copier (object)
	       (copy-sequence object))))

	;; Predicate.
	,@(when predicate
	    (multiple-value-bind (type-predicate get-type)
		(subtypecase type
		  (nil        (values 'vectorp '(aref object 0)))
		  (VECTOR     (values 'VECTORP `(AREF object ,initial-offset)))
		  (LIST	      (values 'LISTP   `(NTH ,initial-offset object))))
	      `((DEFUN ,predicate (object)
		  (AND (,type-predicate object)
		       (struct-subtypep ,get-type (QUOTE ,name)))))))

	;; Remember information about the slots.
	(puthash (QUOTE ,name) (QUOTE (nil ,@slots)) *structure-info*)

	;; Register the structure as a subtype of an included structure,
	,@(when include
	    `((add-struct-subtype (QUOTE ,(first include)) (QUOTE ,name))))

	;; Define a new class (and type).
	,@(unless type
	    `((ENSURE-CLASS
	       (QUOTE ,name)
	       ,(kw METACLASS) (QUOTE STRUCTURE-CLASS)
	       ,(kw DIRECT-SUPERCLASSES)
	       (QUOTE (,(if include (first include) 'STRUCTURE-OBJECT))))))

	;; Accessors.
	,@(let ((index initial-offset))
	    (when (or named (not type))
	      (incf index))
	    (mappend
	     (lambda (slot)
	       (multiple-value-bind (getter setter)
		   (ecase type
		     ((nil)
		      (values `(aref object ,index)
			      `(BACKQUOTE
				(aset (COMMA object) ,index (COMMA new)))))
		     (VECTOR
		      (values `(AREF object ,index)
			      `(BACKQUOTE
				(SETF (AREF (COMMA object) ,index)
				      (COMMA new)))))
		     (LIST
		      (values `(NTH ,index object)
			      `(BACKQUOTE
				(SETF (NTH ,index (COMMA object))
				      (COMMA new))))))
		 (incf index)
		 (let ((name (cl:symcat conc-name (slot-name slot))))
		   `((DEFUN ,name (object) ,getter)
		     ,@(unless (slot-read-only-p slot)
		         `((DEFSETF ,name (object) (new) ,setter)))))))
	       slots))

	;; Finally, return structure name.
	(QUOTE ,name)))))

(defun COPY-STRUCTURE (object)
  (copy-sequence object))
