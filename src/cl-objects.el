;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 7, Objects.

;; Important CLOS classes:
;;   CLASS
;;	BUILT-IN-CLASS, STANDARD-CLASS, STANDARD-OBJECT, STRUCTURE-CLASS,
;;	STRUCTURE-OBJECT
;;   GENERIC-FUNCTION
;;	STANDARD-GENERIC-FUNCTION
;;   METHOD
;;	STANDARD-METHOD
;;   METHOD-COMBINATION

(defmacro define-class-layout (type slots)
  (let ((index -1))
    `(progn
       ,@(mapcar (lambda (slot)
		   `(defmacro ,(symcat type "-" slot) (class)
		      (list 'aref (list 'aref class 1) ,(incf index))))
		 slots)
       ',type)))

;;; Potential class slots:
;; default-initargs direct-default-initargs direct-slots
;; direct-subclasses direct-superclasses finalized-p name
;; precedence-list prototype slots
(define-class-layout class (name superclasses slots default-initargs
			    precedence-list finalized-p subclasses
			    direct-slots direct-default-initargs))

(defun make-class (metaclass name superclasses slots)
  (when (vectorp metaclass)
    (setq metaclass (class-name metaclass)))
  (vector metaclass (vector name superclasses slots
			    nil nil nil nil nil nil nil)))

(let ((fn (vector)))
  (defconst +gf-template+
    (byte-compile `(lambda (&rest args) (apply ,fn args))))
  (defconst +gf-template-fn-pos+
    (position fn (cfref +gf-template+ 2))))

;;; Potential generic-function slots:
;; name lambda-list declarations
;; methods method-class method-combination
;; arguments-precedence-order
(defun make-gf (name lambda-list)
  (let* ((placeholder (list))
 	 (fn (COMPILE nil `(LAMBDA (&REST args)
 			     (APPLY (FUNCTION NO-APPLICABLE-METHOD)
 			            ,placeholder args))))
	 (index (position placeholder (cfref fn 2)))
	 (gf (make-byte-code (cfref +gf-template+ 0)
			     (cfref +gf-template+ 1)
			     (copy-sequence (cfref +gf-template+ 2))
			     (cfref +gf-template+ 3))))
    (SET-FUNCALLABLE-INSTANCE-FUNCTION gf fn)
    (aset (cfref fn 2) index gf)
    (setf (gethash gf *funcallable-objects*)
	  (cons 'STANDARD-GENERIC-FUNCTION
		(vector name lambda-list nil)))
    (cl:values gf)))

(defvar *funcallable-objects* (make-hash-table :test #'eq))

(defun gf-slots (gf)
  (cdr (gethash gf *funcallable-objects*)))

(defmacro gf-name (gf)		`(aref (gf-slots ,gf) 0))
(defmacro gf-lambda-list (gf)	`(aref (gf-slots ,gf) 1))
(defmacro gf-methods (gf)	`(aref (gf-slots ,gf) 2))

;;; MOP
(defun GENERIC-FUNCTION-LAMBDA-LIST (gf)
  (gf-lambda-list gf))

;;; MOP
(defun GENERIC-FUNCTION-METHODS (gf)
  (gf-methods gf))

(define-class-layout method (lambda-list body function generic-function
			     specializers qualifiers environment))

(defun make-method (lambda-list specializers body)
  (vector 'STANDARD-METHOD
	  (vector lambda-list body nil nil specializers nil nil)))

;;; These are redefined later.
(defun FIND-CLASS (name &optional errorp env) nil)
(defun CLASS-OF (object) nil)
(defvar +built-in-class+ t)

;;; MOP
(defun ADD-DIRECT-SUBCLASS (superclass subclass)
  ;; Nothing to do, as long as CLASS-DIRECT-SUBCLASSES does all the work.
  nil)

;;; MOP
(defun ENSURE-CLASS (name &rest keys)
  (apply #'ENSURE-CLASS-USING-CLASS (FIND-CLASS name nil) name keys))

;;; MOP
(cl:defun ENSURE-CLASS-USING-CLASS (class name &KEY
				    DIRECT-SUPERCLASSES
				    DIRECT-SLOTS
				    DIRECT-DEFAULT-INITARGS
				    (METACLASS 'STANDARD-CLASS))
  (when (some #'built-in-class-p DIRECT-SUPERCLASSES)
    (ERROR "Can't make subclass of a built-in class."))
  (unless (symbolp METACLASS)
    (setq METACLASS (CLASS-NAME METACLASS)))
  (unless (eq METACLASS 'BUILT-IN-CLASS)
    (setq *subtypep-objects* (nconc *subtypep-objects* (list (vector name)))))
  (case METACLASS
    (BUILT-IN-CLASS)	;Do nothing.
    (STANDARD-CLASS
     (ensure-type name
		  (byte-compile
		   `(lambda (object env)
		      (and (vectorp object)
			   (subclassp (CLASS-OF object)
				      (FIND-CLASS ',name)))))))
    (STRUCTURE-CLASS
     (ensure-type name
		  (byte-compile
		   `(lambda (obj env)
		     (and (vectorp obj)
		          (struct-subtypep (aref obj 0) ',name)))))))
  (let ((class (make-class METACLASS name DIRECT-SUPERCLASSES DIRECT-SLOTS)))
    (puthash name class *classes*)
    class))

;;; MOP
(defun CLASS-DIRECT-SUPERCLASSES (class)
  (let ((classes (class-superclasses class)))
    (cond
      ((eq class +t-class+)
			nil)
      ((null classes)	(list +t-class+))
      (t		(mapcar #'FIND-CLASS (class-superclasses class))))))

;;; MOP
(defun CLASS-DIRECT-SUBCLASSES (class)
  (let ((classes nil))
    (maphash (lambda (name class2)
	       (when (or (and (eq class +t-class+)
			      (not (eq class2 +t-class+))
			      (null (class-superclasses class2)))
			 (memq (class-name class) (class-superclasses class2)))
		 (pushnew class2 classes)))
	     *classes*)
    classes))

;;; MOP
(defun CLASS-SLOTS (class)
  (class-slots class))

(defun make-built-in-class (name &optional superclasses)
  (ENSURE-CLASS name (kw METACLASS) 'BUILT-IN-CLASS
		     (kw DIRECT-SUPERCLASSES) superclasses))

(defun make-standard-class (name &optional superclasses slots)
  (when (null superclasses)
    (setq superclasses
	  (if (eq name 'STANDARD-OBJECT) '(T) '(STANDARD-OBJECT))))
  (ENSURE-CLASS name (kw DIRECT-SUPERCLASSES) superclasses
		     (kw DIRECT-SLOTS) slots))

(defun make-structure-class (name &optional superclasses)
  (ENSURE-CLASS name (kw METACLASS) 'STRUCTURE-CLASS
		     (kw DIRECT-SUPERCLASSES) superclasses))

(defun make-funcallable-standard-class (name superclasses)
  (ENSURE-CLASS name (kw METACLASS) 'FUNCALLABLE-STANDARD-CLASS
		     (kw DIRECT-SUPERCLASSES) superclasses))

(defconst +unbound+ (make-symbol "UNBOUND"))

;;; Figure 4-8. Classes that correspond to pre-defined type specifiers
;;; These are required to exist, and most may be built-in.
;; arithmetic-error                 GENERIC-FUNCTION   simple-error
;; array                            hash-table         simple-type-error
;; bit-vector                       integer            simple-warning
;; broadcast-stream                 list               STANDARD-CLASS
;; BUILT-IN-CLASS                   logical-pathname  STANDARD-GENERIC-FUNCTION
;; cell-error                       METHOD             STANDARD-METHOD
;; character                        METHOD-COMBINATION STANDARD-OBJECT
;; CLASS                            null               storage-condition
;; complex                          number             stream
;; concatenated-stream              package            stream-error
;; condition                        package-error      string
;; cons                             parse-error        string-stream
;; control-error                    pathname           STRUCTURE-CLASS
;; division-by-zero                 print-not-readable STRUCTURE-OBJECT
;; echo-stream                      program-error      style-warning
;; end-of-file                      random-state       symbol
;; error                            ratio              synonym-stream
;; file-error                       rational           t
;; file-stream                      reader-error       two-way-stream
;; float                            readtable          type-error
;; floating-point-inexact           real               unbound-slot
;; floating-point-invalid-operation restart            unbound-variable
;; floating-point-overflow          sequence           undefined-function
;; floating-point-underflow         serious-condition  vector
;; function                         simple-condition   warning

;;; These classes are optional, and may be built-in.
;; atom			nil?
;; base-char		short-float
;; base-string		signed-byte
;; bignum		simple-array
;; bit			simple-base-string
;; compiled-function	simple-bit-vector
;; double-float		simple-string
;; extended-char	simple-vector
;; fixnum		single-float
;; keyword		standard-char
;; long-float		unsigned-byte

(defun built-in-class-p (class) nil)
(defvar *classes* (make-hash-table :test #'eq))
(defconst +array-class+	       (make-built-in-class 'ARRAY))
(defconst +bit-vector-class+   (make-built-in-class 'BIT-VECTOR '(VECTOR)))
(defconst +built-in-class+     (make-standard-class 'BUILT-IN-CLASS '(CLASS)))
(defconst +character-class+    (make-built-in-class 'CHARACTER))
(defconst +class-class+	       (make-standard-class 'CLASS '(SPECIALIZER)))
(defconst +complex-class+      (make-built-in-class 'COMPLEX '(NUMBER)))
;(defconst +condition-class+   (make-standard-class 'CONDITION))
(defconst +cons-class+	       (make-built-in-class 'CONS '(LIST)))
(defconst +eql-specializer-class+
			       (make-standard-class 'EQL-SPECIALIZER
						    '(SPECIALIZER)))
(defconst +float-class+	       (make-built-in-class 'FLOAT '(REAL)))
(defconst +funcallable-standard-class+
			       (make-standard-class 'FUNCALLABLE-STANDARD-CLASS
						    '(CLASS)))
(defconst +funcallable-standard-object+
			       (make-standard-class
				'FUNCALLABLE-STANDARD-OBJECT
				'(STANDARD-OBJECT FUNCTION)))
(defconst +function-class+     (make-built-in-class 'FUNCTION))
(defconst +generic-function-class+
			       (make-funcallable-standard-class
				'GENERIC-FUNCTION
				'(METAOBJECT FUNCALLABLE-STANDARD-OBJECT)))
(defconst +hash-table-class+   (make-built-in-class 'HASH-TABLE))
(defconst +integer-class+      (make-built-in-class 'INTEGER '(RATIONAL)))
(defconst +list-class+	       (make-built-in-class 'LIST '(SEQUENCE)))
(defconst +logical-pathname-class+
			       (make-built-in-class 'LOGICAL-PATHNAME
						    '(PATHNAME)))
(defconst +metaobject-class+   (make-standard-class 'METAOBJECT))
(defconst +method-class+       (make-standard-class 'METHOD '(METAOBJECT)))
(defconst +method-combination-class+
			       (make-standard-class 'METHOD-COMBINATION
						    '(METAOBJECT)))
(defconst +null-class+	       (make-built-in-class 'NULL '(SYMBOL LIST)))
(defconst +number-class+       (make-built-in-class 'NUMBER))
(defconst +package-class+      (make-built-in-class 'PACKAGE))
(defconst +pathname-class+     (make-built-in-class 'PATHNAME))
(defconst +ratio-class+	       (make-built-in-class 'RATIO '(RATIONAL)))
(defconst +rational-class+     (make-built-in-class 'RATIONAL '(REAL)))
(defconst +real-class+	       (make-built-in-class 'REAL '(NUMBER)))
(defconst +readtable-class+    (make-built-in-class 'READTABLE))
;(defconst +restart-class+     (make-standard-class 'RESTART))
(defconst +sequence-class+     (make-built-in-class 'SEQUENCE))
(defconst +slot-definition-class+
			       (make-standard-class 'SLOT-DEFINITION
						    '(METAOBJECT)))
(defconst +specializer-class+  (make-standard-class 'SPECIALIZER
						    '(METAOBJECT)))
(defconst +standard-class+     (make-standard-class 'STANDARD-CLASS '(CLASS)))
(defconst +standard-generic-function-class+
			       (make-funcallable-standard-class
				'STANDARD-GENERIC-FUNCTION
				'(GENERIC-FUNCTION)))
(defconst +standard-method+    (make-standard-class 'STANDARD-METHOD
						    '(METHOD)))
(defconst +standard-accessor-method+
			       (make-standard-class 'STANDARD-ACCESSOR-METHOD
						    '(STANDARD-METHOD)))
(defconst +standard-reader-method+
			       (make-standard-class
				'STANDARD-READER-METHOD
				'(STANDARD-ACCESSOR-METHOD)))
(defconst +standard-writer-method+
			       (make-standard-class
				'STANDARD-WRITER-METHOD
				'(STANDARD-ACCESSOR-METHOD)))
(defconst +standard-object+    (make-standard-class 'STANDARD-OBJECT))
;(defconst +stream-class+      (make-standard-class 'STREAM))
(defconst +string-class+       (make-built-in-class 'STRING '(VECTOR)))
(defconst +structure-class+    (make-standard-class 'STRUCTURE-CLASS '(CLASS)))
(defconst +structure-object+   (make-structure-class 'STRUCTURE-OBJECT))
(defconst +symbol-class+       (make-built-in-class 'SYMBOL))
(defconst +t-class+	       (make-built-in-class 'T))
(defconst +vector-class+       (make-built-in-class 'VECTOR '(ARRAY SEQUENCE)))
(dolist (args *initial-classes*)
  (apply #'ENSURE-CLASS args))
(defun built-in-class-p (class)
  (when (symbolp class)
    (setq class (FIND-CLASS class)))
  (eq (CLASS-OF class) +built-in-class+))

(defun funcallable-object-p (object)
  (and (COMPILED-FUNCTION-P object)
       (gethash object *funcallable-objects*)))

(defun generic-function-p (object &optional env)
  (and (funcallable-object-p object)
       (subclassp (CLASS-OF object) +generic-function-class+)))

(ensure-type 'GENERIC-FUNCTION #'generic-function-p)

;;; TODO: Standard Generic Function FUNCTION-KEYWORDS

;;; MOP
(cl:defun ENSURE-GENERIC-FUNCTION-USING-CLASS (gf name &KEY LAMBDA-LIST)
  (cond
    ((null gf)
     (setq gf (make-gf name LAMBDA-LIST))
     (set-fun name gf))
    (*DEBUG-IO*
     (FRESH-LINE *DEBUG-IO*)
     (WRITE-STRING "Redefinition of generic function " *DEBUG-IO*)
     (WRITE-STRING (SYMBOL-NAME (gf-name gf)) *DEBUG-IO*)
     (WRITE-STRING " not properly implemented." *DEBUG-IO*)))
  gf)

(defun gf-or-error (name)
  (when (FBOUNDP name)
    (let ((fn (FDEFINITION name)))
      (if (generic-function-p fn)
	  fn
	  (ERROR "~A is not a generic function." name)))))

;;; TODO: Function ENSURE-GENERIC-FUNCTION
(defun ENSURE-GENERIC-FUNCTION (name &rest keys)
  (apply #'ENSURE-GENERIC-FUNCTION-USING-CLASS (gf-or-error name) name keys))

;;; MOP
(defun FINALIZE-INHERITANCE (class)
  (setf (class-finalized-p class) 'T))

;;; MOP
(defun CLASS-FINALIZED-P (class)
  (class-finalized-p class))

;;; TODO: Standard Generic Function ALLOCATE-INSTANCE
(defun ALLOCATE-INSTANCE (class &rest initargs)
  (unless (CLASS-FINALIZED-P class)
    (FINALIZE-INHERITANCE class))
  (vector (CLASS-NAME class)
	  (make-vector (length (CLASS-SLOTS class)) +unbound+)))

;;; TODO: Standard Generic Function REINITIALIZE-INSTANCE

;;; TODO: Standard Generic Function SHARED-INITIALIZE
(defun SHARED-INITIALIZE (instance slot-names &rest initargs)
  (when (eq slot-names 'T)
    (setq slot-names (CLASS-SLOTS (CLASS-OF instance))))
  instance)

;;; TODO: Standard Generic Function UPDATE-INSTANCE-FOR-DIFFERENT-CLASS
;;; TODO: Standard Generic Function UPDATE-INSTANCE-FOR-REDEFINED-CLASS
;;; TODO: Standard Generic Function CHANGE-CLASS

;;; TODO: Function SLOT-BOUNDP
(defun SLOT-BOUNDP (object slot)
  (SLOT-BOUNDP-USING-CLASS (CLASS-OF object) object slot))

(defun slot-index (class object slot)
  (or (position slot (class-slots class))
      (SLOT-MISSING class object slot)))

;;; MOP
(defun SLOT-BOUNDP-USING-CLASS (class object slot)
  (if (eq (CLASS-OF class) +standard-class+)
      (not (eq (aref (aref object 1) (slot-index class object slot))
	       +unbound+))
      (ERROR "SLOT-BOUNDP-USING-CLASS not implemented for ~A." class)))

;;; TODO: Function SLOT-EXISTS-P
(defun SLOT-EXISTS-P (object slot)
  (position slot (class-slots (CLASS-OF object))))

;;; TODO: Function SLOT-MAKUNBOUND
(defun SLOT-MAKUNBOUND (object slot)
  (aset (aref object 1) (slot-index (CLASS-OF object) object slot) +unbound+))

;;; TODO: Standard Generic Function SLOT-MISSING
(defun SLOT-MISSING (class instance slot-name type &optional value)
  (ERROR "SLOT-MISSING"))

;;; TODO: Standard Generic Function SLOT-UNBOUND
(defun SLOT-UNBOUND (class instance slot-name)
  (ERROR "SLOT-UNBOUND"))

(defun FUNCALLABLE-STANDARD-INSTANCE-ACCESS (object location)
  (aref (gf-slots object) location))

;;; TODO: Function SLOT-VALUE
(defun SLOT-VALUE (object slot)
  (let ((class (CLASS-OF object)))
    (cond
      ((funcallable-object-p object)
       (let ((value (FUNCALLABLE-STANDARD-INSTANCE-ACCESS
		     object (slot-index class object slot))))
	 (if (eq value +unbound+)
	     (SLOT-UNBOUND class object slot)
	     value)))
      ((eq (CLASS-OF class) +standard-class+)
       (let ((value (aref (aref object 1) (slot-index class object slot))))
	 (if (eq value +unbound+)
	     (SLOT-UNBOUND class object slot)
	     value)))
      (t
       (SLOT-VALUE-USING-CLASS class object slot)))))

(DEFSETF SLOT-VALUE set-slot-value)

(defun set-slot-value (object slot value)
  (let ((class (CLASS-OF object)))
    (cond
      ((funcallable-object-p object)
       (aset (gf-slots object) (slot-index class object slot) value))
      ((eq (CLASS-OF class) +standard-class+)
       (aset (aref object 1) (slot-index class object slot) value))
      (t
       (FUNCALL '(SETF SLOT-VALUE-USING-CLASS) value class object slot)))))

;;; TODO: Standard Generic Function METHOD-QUALIFIERS

;;; TODO: Standard Generic Function NO-APPLICABLE-METHOD
(defun NO-APPLICABLE-METHOD (gf &rest args)
  (ERROR "No applicable method for ~A called with arguments ~A." gf args))

;;; TODO: Standard Generic Function NO-NEXT-METHOD
;;; TODO: Standard Generic Function REMOVE-METHOD

;;; TODO: Standard Generic Function MAKE-INSTANCE
(defun MAKE-INSTANCE (class &rest initargs)
  (when (symbolp class)
    (setq class (FIND-CLASS class)))
  (when (built-in-class-p class)
    (ERROR "Can't make instance of a built-in class."))
  ;; TODO: Augment initargs with default initargs.
  (let ((instance (apply #'ALLOCATE-INSTANCE class initargs)))
    (apply #'INITIALIZE-INSTANCE instance initargs)
    instance))

;;; TODO: Standard Generic Function MAKE-INSTANCES-OBSOLETE

;;; MOP
(defun SLOT-NAME (slot)
  ;; TODO:
  slot)

;;; TODO: Function MAKE-LOAD-FORM-SAVING-SLOTS
(cl:defun MAKE-LOAD-FORM-SAVING-SLOTS (object &KEY SLOT-NAMES ENVIRONMENT)
  (if (structurep object)
      (cl:values
       `(make-vector ,(length object) (QUOTE ,(aref object 0)))
       `(LET ((object ,object))
	  ,@(do ((result nil)
		 (length (length object))
		 (i 1 (1+ i)))
		((>= i length)
		 (nreverse result))
	      (push `(aset object ,i (QUOTE ,(aref object i))) result))))
      (let ((class (CLASS-OF object)))
	(when (null SLOT-NAMES)
	  (setq SLOT-NAMES (mapcar #'SLOT-NAME (CLASS-SLOTS class))))
	(cl:values
	 `(ALLOCATE-INSTANCE (FIND-CLASS (QUOTE ,(CLASS-NAME class))))
	 `(LET ((object ,object))
	    ,@(mapcar (lambda (slot)
			(if (SLOT-BOUNDP object slot)
			    `(SETF (SLOT-VALUE object (QUOTE ,slot))
			           (QUOTE ,(SLOT-VALUE object slot)))
			    `(SLOT-MAKUNBOUND object (QUOTE ,slot))))
		      SLOT-NAMES)
	    (INITIALIZE-INSTANCE object))))))

;;; TODO: Macro WITH-ACCESSORS
;;; TODO: Macro WITH-SLOTS

;;; TODO: Macro DEFCLASS
(cl:defmacro DEFCLASS (name superclasses slots &rest options)
  (when (null superclasses)
    (setq superclasses '(STANDARD-OBJECT)))
  `(ENSURE-CLASS (QUOTE ,name)
		 ,(kw DIRECT-SUPERCLASSES) (QUOTE ,superclasses)
		 ,(kw DIRECT-SLOTS) (QUOTE ,slots)))

;;; TODO: Macro DEFGENERIC
(cl:defmacro DEFGENERIC (name lambda-list &rest stuff)
  `(ENSURE-GENERIC-FUNCTION (QUOTE ,name)
			    ,(kw LAMBDA-LIST) (QUOTE ,lambda-list)))

(defmacro cl:defgeneric (name lambda-list &rest stuff)
  (when byte-compile-warnings
    (byte-compile-log-1 (format "cl:defgeneric %s" name)))
  `(ENSURE-GENERIC-FUNCTION ',name ',(kw LAMBDA-LIST) ',lambda-list))

;;; TODO: Macro DEFMETHOD
(cl:defmacro DEFMETHOD (name lambda-list &rest forms)
  (when (not (listp lambda-list))
    (ERROR "Only primary methods are implemented."))
  `(ensure-method (QUOTE ,name) (QUOTE ,lambda-list) (QUOTE ,forms)))

(defmacro cl:defmethod (name lambda-list &rest forms)
  (when byte-compile-warnings
    (byte-compile-log-1 (format "cl:defmethod %s" name)))
  `(ensure-method ',name ',lambda-list ',forms))

;;; MOP
(defun EXTRACT-LAMBDA-LIST (lambda-list)
  (let* ((lambda-list (copy-list lambda-list))
	 (not-required (MEMBER-IF #'lambda-list-keyword-p lambda-list))
	 (required (LDIFF lambda-list not-required)))
    (append
     (mapcar (lambda (x)
	       (typecase x
		 (symbol	x)
		 (cons		(car x))
		 (t		(type-error x '(OR SYMBOL CONS)))))
	     required)
     not-required)))

;;; MOP
(defun EXTRACT-SPECIALIZER-NAMES (lambda-list)
  (let* ((lambda-list (copy-list lambda-list))
	 (required (LDIFF lambda-list
			  (MEMBER-IF #'lambda-list-keyword-p lambda-list))))
    (mapcar (lambda (x)
	      (typecase x
		(symbol		'T)
		(cons		(second x))
		(t		(type-error x '(OR SYMBOL CONS)))))
	    required)))

(defun specializer (name)
  (cond
    ((symbolp name)	(FIND-CLASS name))
    ((and (listp name)
	  (= (length name) 2)
	  (eq (first name) 'EQL))
			(INTERN-EQL-SPECIALIZER (second name)))
    (t			(type-error name '(OR SYMBOL CONS)))))

(defconst +eql-fn+ (if (featurep 'xemacs) #'eql #'EQL))
(defvar *eql-specializers* (make-hash-table :test +eql-fn+))

(defun INTERN-EQL-SPECIALIZER (object)
  (or (gethash object *eql-specializers*)
      (puthash object (make-eql-specializer object) *eql-specializers*)))

(defun EQL-SPECIALIZER-OBJECT (eql-specializer)
  (aref (aref eql-specializer 1) 0))

(defun make-eql-specializer (object)
  (vector 'EQL-SPECIALIZER (vector object)))

(defun ensure-method (name lambda-list forms)
  (MULTIPLE-VALUE-BIND (body decls doc) (parse-body forms t)
    (let ((gf (ENSURE-GENERIC-FUNCTION name (kw LAMBDA-LIST) lambda-list))
	  (method (make-method
		   (EXTRACT-LAMBDA-LIST lambda-list)
		   (mapcar #'specializer
			   (EXTRACT-SPECIALIZER-NAMES lambda-list))
		   body)))
      (ADD-METHOD gf method)
      method)))

;;; TODO: Accessor FIND-CLASS
(cl:defun FIND-CLASS (name &OPTIONAL (errorp t) env)
  (let ((class (gethash name *classes*)))
    (when (and (null class) errorp)
      (ERROR "No such class ~A." name))
    class))

(set-fun '(SETF FIND-CLASS)
	 (lambda (class name &optional errorp env)
	   (puthash name class *classes*)))

;;; TODO: Local Function NEXT-METHOD-P
;;; TODO: Local Macro CALL-METHOD,
;;; TODO:             MAKE-METHOD
;;; TODO: Local Function CALL-NEXT-METHOD
;;; TODO: Standard Generic Function COMPUTE-APPLICABLE-METHODS
;;; TODO: Macro DEFINE-METHOD-COMBINATION
;;; TODO: Standard Generic Function FIND-METHOD

;;; MOP
(defun SET-FUNCALLABLE-INSTANCE-FUNCTION (gf fn)
  (aset (cfref gf 2) +gf-template-fn-pos+ fn))

;;; TODO: Standard Generic Function ADD-METHOD
(defun ADD-METHOD (gf method)
  ;; (i)
  (push method (gf-methods gf))
  (setf (method-generic-function method) gf)
  ;; (ii) (ADD-DIRECT-METHOD ...)
  ;; (iii)
  (SET-FUNCALLABLE-INSTANCE-FUNCTION gf (COMPUTE-DISCRIMINATING-FUNCTION gf))
  ;; (iv) Update dependents.
  gf)

(defun more-specializing-p (s1 s2)
  (or (eq (type-of s1) 'EQL-SPECIALIZER)
      (and (classp s2)
	   (subclassp s1 s2))))

(defun sort-methods (methods)
  (let ((result nil)
	(least-specific-method nil))
    (while methods
      (setq least-specific-method (first methods))
      (dolist (method (rest methods))
	(when (more-specializing-p
	       (first (method-specializers least-specific-method))
	       (first (method-specializers method)))
	  (setq least-specific-method method)))
      (setq methods (delq least-specific-method methods))
      (push least-specific-method result))
    result))

;;; MOP
(defun METHOD-SPECIALIZERS (method)
  (method-specializers method))

;;; MOP
(defun COMPUTE-DISCRIMINATING-FUNCTION (gf)
  (with-gensyms (args)
    (COMPILE nil `(LAMBDA (&REST ,args)
		   (TYPECASE (car ,args)
		     ,@(mapcar
			(lambda (method)
			  `(,(first (method-specializers method))
			    (APPLY (LAMBDA ,(method-lambda-list method)
				     ,@(method-body method))
			           ,args)))
			(sort-methods (copy-list (gf-methods gf))))
		     (T (APPLY (FUNCTION NO-APPLICABLE-METHOD)
			       ,gf ,args)))))))

;; (lambda (arg &rest rest)
;;   (flet ((call-next-method ()
;; 	   (if (typep arg 'bar)
;; 	       (call-method ...)	;Around method 2
;; 	       ...)))
;;     (if (typep arg 'foo)
;; 	   (call-method ...)		;Around method 1
;; 	   (apply #'call-next-method arg rest))))

;; (lambda (arg &rest rest)
;;   (when (typep arg 'foo)
;;     (call-method ...))		;Before method 1
;;   (when (typep arg 'bar)
;;     (call-method ...))		;Before method 2
;;   (typecase arg
;;     (foo (call-method ...))		;Primary method 1
;;     (bar (call-method ...))		;Primary method 2
;;     (t (no-applicable-method ...)))
;;   (when (typep arg 'bar)
;;     (call-method ...))		;After method 1
;;   (when (typep arg 'foo)
;;     (call-method ...)))		;After method 2

;;; TODO: Standard Generic Function INITIALIZE-INSTANCE
(defun INITIALIZE-INSTANCE (instance &rest initargs)
  (apply #'SHARED-INITIALIZE instance 'T initargs))

;;; TODO: Standard Generic Function CLASS-NAME
(defun CLASS-NAME (class)
  (class-name class))

;;; TODO: Standard Generic Function (SETF CLASS-NAME)
(set-fun '(SETF CLASS-NAME)
	 (lambda (name class)
	   (setf (class-name class) name)))

;;; TODO: Function CLASS-OF
(defun CLASS-OF (object)
  (if (null object)
      +null-class+
      (ecase (type-of object)
	;; This is supposed to be an exhaustive enumeration of all
	;; possible return values for Emacs Lisp type-of.
	((bit-vector bool-vector)
			+bit-vector-class+)
	(subr		+function-class+)
	(compiled-function
			(let ((info (gethash object *funcallable-objects*)))
			  (if info
			      (FIND-CLASS (car info))
			      +function-class+)))
	(character	+character-class+)
	(cons		+cons-class+)
	(float		+float-class+)
	(hash-table	+hash-table-class+)
	(integer	+integer-class+)
	(string		+string-class+)
	(symbol		+symbol-class+)
	(vector
	 (let ((class (FIND-CLASS (aref object 0) nil)))
	   (or class
	       (ecase (aref object 0)
		 ((bit-array char-array)
				+array-class+)
		 (BIGNUM	+integer-class+)
		 (INTERPRETED-FUNCTION
				+function-class+)
		 (SIMPLE-VECTOR	+vector-class+)))))
	;; For now, throw an error on these.
	((buffer char-table frame marker overlay process
		 subr window window-configuration)
			(error "Unknown type: %s" (type-of object))))))

(defun subclassp (class1 class2)
  (or (eq class2 +t-class+)
      (eq class1 class2)
      (some (lambda (name) (subclassp (FIND-CLASS name) class2))
	    (class-superclasses class1))))

(defun classp (object)
  (subclassp (CLASS-OF object) +class-class+))

;;; UNBOUND-SLOT and UNBOUND-SLOT-INSTANCE defined in cl-conditions.el.

;;; TODO:
(set-fun '(SETF DOCUMENTATION) (lambda (value object type) value))

(cl:defmethod MAKE-LOAD-FORM  ((object T) &OPTIONAL env)
  (built-in-make-load-form object env))
(cl:defmethod MAKE-LOAD-FORM  ((object STANDARD-OBJECT) &OPTIONAL env)
  (ERROR (QUOTE ERROR)))
(cl:defmethod MAKE-LOAD-FORM  ((object STRUCTURE-OBJECT) &OPTIONAL env)
  (ERROR (QUOTE ERROR)))
(cl:defmethod MAKE-LOAD-FORM  ((object STRUCTURE-OBJECT) &OPTIONAL env)
  (BACKQUOTE (FIND-CLASS (QUOTE (COMMA (CLASS-NAME object))))))

(cl:defmethod PRINT-OBJECT ((object T) stream)
  (built-in-print-object object stream))

(cl:defmethod DOCUMENTATION ((object FUNCTION) type)
  (WHEN (> (length object) 4)
    (aref object 4)))
