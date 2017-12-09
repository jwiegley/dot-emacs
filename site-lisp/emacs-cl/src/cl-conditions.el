;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 9, Conditions.

(defvar *condition-constructors* (make-hash-table))

(defmacro* DEFINE-CONDITION (name parents slots &rest options)
  ;(with-gensyms (constructor)
  (let ((constructor (symcat "condition-constructor-" name)))
    `(progn
      (DEFSTRUCT (,name
		   (:copier nil)
		   (:constructor ,constructor)
		   ,@(when parents
		       `((:include ,(first parents)))))
	,@slots)
      (puthash ',name #',constructor *condition-constructors*)
      ',name)))

(cl:defmacro DEFINE-CONDITION (name parents slots &rest options)
  `(DEFCLASS ,name ,parents ,slots ,@options))

;; (defun ensure-condition (name parents slots options)
;;   (ENSURE-CLASS name
;; 		(kw DIRECT-SUPERCLASSES) parents
;; 		(kw DIRECT-SLOTS) slots)
;;   (let ((*PACKAGE* *emacs-cl-package*))
;;     (dolist (slot slots)
;;       (when (listp slot)
;; 	(setq slot (first slot)))
;;       (ensure-method (symcat name "-" slot)
;; 		     '(condition)
;; 		     `((SLOT-VALUE condition (QUOTE ,slot)))))))

(DEFINE-CONDITION CONDITION () ())

(DEFINE-CONDITION WARNING (CONDITION) ())

(DEFINE-CONDITION STYLE-WARNING (WARNING) ())

(DEFINE-CONDITION SERIOUS-CONDITION (CONDITION) ())

(DEFINE-CONDITION ERROR (SERIOUS-CONDITION) ())

(DEFINE-CONDITION CELL-ERROR (ERROR) (NAME))

(DEFINE-CONDITION PARSE-ERROR (ERROR) ())

(DEFINE-CONDITION STORAGE-CONDITION (SERIOUS-CONDITION) ())

(cl:defmacro ASSERT (form &optional places datum &rest args)
  (with-gensyms (continue)
    `(DO ()
         (,form)
       (RESTART-BIND ((CONTINUE (LAMBDA () (GO ,continue))))
	 (ERROR ,@(if datum `(,datum ,@args) '((QUOTE ERROR)))))
       ,continue
       (PRINC "\nFix the error already!"))))

(defun condition (datum args default-type)
  (cond
    ((TYPEP datum 'CONDITION)
     datum)
    ((symbolp datum)
     (apply #'MAKE-CONDITION datum args))
    ((STRINGP datum)
     ;; TODO: (kw FORMAT-CONTROL) and (kw FORMAT-ARGUMENTS)
     (MAKE-CONDITION default-type (kw format) datum (kw args) args))
    (t
     (ERROR "Invalid condition designator: ~S ~S."))))

(defun ERROR (datum &rest args)
  (let ((condition (condition datum args 'SIMPLE-ERROR)))
    (SIGNAL condition)
    (INVOKE-DEBUGGER condition)))

(defmacro* restart-bind (bindings &body body)
  `(let ((*restart-alist*
	  (append (list ,@(mapcar (lambda (binding)
				    `(CONS ',(first binding)
				           ,(second binding)))
				  bindings))
		  *restart-alist*)))
     ,@body))

(defun* CERROR (format datum &rest args)
  (restart-bind ((CONTINUE (lambda () (return-from CERROR))))
    (apply #'ERROR datum args)))

(cl:defmacro CHECK-TYPE (place type &optional string)
  `(UNLESS (TYPEP ,place (QUOTE ,type))
     ;; TODO...
     (type-error ,place (QUOTE ,type))))

;; TODO: inherit from SIMPLE-CONDITION
(DEFINE-CONDITION SIMPLE-ERROR (ERROR) (format args))

(defun INVALID-METHOD-ERROR (method format &rest args)
  (apply #'ERROR format args))

(defun METHOD-COMBINATION-ERROR (format &rest args)
  (apply #'ERROR format args))

(DEFVAR *condition-handler-alist* nil)

(defun SIGNAL (datum &rest args)
  (let ((condition (condition datum args 'SIMPLE-CONDITION)))
    (when (TYPEP condition *BREAK-ON-SIGNALS*)
      (INVOKE-DEBUGGER condition))
    (let ((handler (ASSOC condition *condition-handler-alist*
			  (kw TEST) #'TYPEP)))
      (when handler
	(let ((*condition-handler-alist* (cddr handler)))
	  (FUNCALL (cadr handler) condition))))
    nil))

(DEFINE-CONDITION SIMPLE-CONDITION (CONDITION) (format args))

(defun SIMPLE-CONDITION-FORMAT-CONTROL (condition)
  (cond
    ((TYPEP condition 'SIMPLE-CONDITION)  (SIMPLE-CONDITION-format condition))
    ((TYPEP condition 'SIMPLE-ERROR)      (SIMPLE-ERROR-format condition))
    ((TYPEP condition 'SIMPLE-WARNING)    (SIMPLE-WARNING-format condition))
    ((TYPEP condition 'SIMPLE-TYPE-ERROR) (SIMPLE-TYPE-ERROR-format condition))
    (t					  (error "this sucks"))))

(defun SIMPLE-CONDITION-FORMAT-ARGUMENTS (condition)
  (cond
    ((TYPEP condition 'SIMPLE-CONDITION)  (SIMPLE-CONDITION-args condition))
    ((TYPEP condition 'SIMPLE-ERROR)      (SIMPLE-ERROR-args condition))
    ((TYPEP condition 'SIMPLE-WARNING)    (SIMPLE-WARNING-args condition))
    ((TYPEP condition 'SIMPLE-TYPE-ERROR) (SIMPLE-TYPE-ERROR-args condition))
    (t					  (error "this sucks"))))

(defun* WARN (datum &rest args)
  (let ((condition (condition datum args 'SIMPLE-WARNING)))
    (restart-bind ((MUFFLE-WARNING (lambda () (return-from WARN))))
      (SIGNAL condition))
    (if (TYPEP condition 'SIMPLE-WARNING)
	(progn
	  (FORMAT *ERROR-OUTPUT* "~&WARNING: ")
	  (apply #'FORMAT *ERROR-OUTPUT*
		 (SIMPLE-CONDITION-FORMAT-CONTROL condition)
		 (SIMPLE-CONDITION-FORMAT-ARGUMENTS condition)))
	(PRINT condition *ERROR-OUTPUT*))
    nil))

;; TODO: inherit from SIMPLE-CONDITION
(DEFINE-CONDITION SIMPLE-WARNING (WARNING) (format args))

(defun INVOKE-DEBUGGER (condition)
  (let* ((hook *DEBUGGER-HOOK*)
	 (*DEBUGGER-HOOK* nil))
    (when hook
      (FUNCALL hook condition hook))
    (FORMAT T "~&~%Debugger invoked on condition ~A" condition)
    (when (eq (TYPE-OF condition) 'SIMPLE-ERROR)
      (FORMAT T ":~%  ")
      (apply #'FORMAT T (SIMPLE-ERROR-format condition)
	     (SIMPLE-ERROR-args condition)))
    (FORMAT T "~&Available restarts:")
    (do ((restarts (COMPUTE-RESTARTS) (cdr restarts))
	 (i 0 (1+ i)))
	((null restarts))
      (FORMAT T "~&  ~D  ~A" i (RESTART-NAME (car restarts))))
    (FORMAT T "~&Type \"r <n>\" or just \"<n>\" to in invoke a restart,~@
                 and \"b\" to print a backtrace.~%")
    (let ((n -1) c)
      (while (minusp n)
	(message "Debugger command: ")
	(case (setq c (if (eval-when-compile (featurep 'xemacs))
			  (char-to-int (read-char-exclusive))
			  (read-char-exclusive)))
	  ((114 48 49 50 51 52 53 54 55 56 57)
	   (cond
	     ((eq c 114)
	      (setq n (read-minibuffer "Restart number: "))
	      (unless (integerp n)
		(setq n -1)))
	     (t
	      (setq n (- c 48)))))
	  (98
	   (FORMAT T "~&Backtrace: ~%~A~%"
		   (with-output-to-string (backtrace))))
	  (t
	   (message "Invalid debugger command.")
	   (sit-for 1))))
      (INVOKE-RESTART (nth n (COMPUTE-RESTARTS))))))

(defun* BREAK (&optional format &rest args)
  (restart-bind ((CONTINUE (lambda () (return-from BREAK))))
    (debug)))

(DEFVAR *DEBUGGER-HOOK* nil)

(DEFVAR *BREAK-ON-SIGNALS* nil)

(defmacro* HANDLER-BIND (bindings &body body)
  `(let ((*condition-handler-alist*
	  (append (list ,@(mapcar (lambda (binding)
				    `(list* ',(first binding)
				            ,(second binding)
					    *condition-handler-alist*))
				  bindings))
		  *condition-handler-alist*)))
     ,@body))

(cl:defmacro HANDLER-BIND (bindings &body body)
  `(LET ((*condition-handler-alist*
	  (APPEND (LIST ,@(mapcar (lambda (binding)
				    `(LIST* (QUOTE ,(first binding))
				            ,(second binding)
				            *condition-handler-alist*))
				  bindings))
		  *condition-handler-alist*)))
     ,@body))

(cl:defmacro HANDLER-CASE (form &rest clauses)
  (with-gensyms (block)
    `(BLOCK ,block
       (HANDLER-BIND
	   ,(mapcar
	      (lambda (clause)
		(destructuring-bind
		      (typespec (&optional var) &body body) clause
		  (unless var
		    (setq var (gensym)))
		  `(,typespec (LAMBDA (,var)
				(RETURN-FROM ,block (PROGN ,@body))))))
	      clauses)
	 ,form))))

(cl:defmacro IGNORE-ERRORS (&rest forms)
  (with-gensyms (block)
    `(BLOCK ,block
       (HANDLER-BIND ((ERROR (LAMBDA (c) (RETURN-FROM ,block (VALUES nil c)))))
	 ,@forms))))

(defun MAKE-CONDITION (type &rest args)
  (let ((fn (gethash type *condition-constructors*)))
    (if fn
	(APPLY fn args)
	(error "no such condition type"))))

;; (defun MAKE-CONDITION (type &rest args)
;;   (apply #'MAKE-INSTANCE type args))

(DEFSTRUCT (RESTART
	     (:constructor make-restart (NAME handler &OPTIONAL condition))
	     (:predicate restartp))
  NAME handler condition)

(DEFVAR *restart-alist* nil)

(defun COMPUTE-RESTARTS (&optional condition)
  (mapcar (lambda (cons) (make-restart (car cons) (cdr cons)))
	  *restart-alist*))

(defun FIND-RESTART (restart &optional condition)
  ;; TODO: consider condition
  (cond
    ((restartp restart)		restart)
    ((null restart)		(error "TODO"))
    ((symbolp restart)		(let ((cons (assq restart *restart-alist*)))
				  (when cons
				    (make-restart restart (cdr cons)))))
    (t				(type-error restart '(OR RESTART SYMBOL)))))

(defun INVOKE-RESTART (restart-designator &rest args)
  (let ((restart (FIND-RESTART restart-designator)))
    (if restart
	(APPLY (RESTART-handler restart) args)
	(ERROR 'CONTROL-ERROR))))

;;; TODO: INVOKE-RESTART-INTERACTIVELY

(cl:defmacro RESTART-BIND (bindings &body forms)
  `(LET ((*restart-alist*
	  (APPEND (LIST ,@(mapcar (lambda (binding)
				    `(CONS (QUOTE ,(first binding))
				           ,(second binding)))
				  bindings))
		  *restart-alist*)))
     ,@forms))

;;; TODO: RESTART-CASE

;;; RESTART-NAME defined by defstruct.

;;; TODO: WITH-CONDITION-RESTARTS

;;; TODO: WITH-SIMPLE-RESTART
; (cl:defmacro WITH-SIMPLE-RESTART ((name format &rest args)
; 				  &body body)
;   `(RESTART-CASE (PROGN ,@body)
;      (,name ()
;        :report (LAMBDA (stream) (FORMAT stream ,format ,@args))
;        (cl:values nil T))))

(defun ABORT (&optional condition)
  (INVOKE-RESTART 'ABORT))

(defun CONTINUE (&optional condition)
  (let ((restart (FIND-RESTART 'CONTINUE)))
    (when restart
      (INVOKE-RESTART restart))))

(defun MUFFLE-WARNING (&optional condition)
  (INVOKE-RESTART 'MUFFLE-WARNING))

(defun STORE-VALUE (value &optional condition)
  (let ((restart (FIND-RESTART 'STORE-VALUE)))
    (when restart
      (INVOKE-RESTART restart value))))

(defun USE-VALUE (value &optional condition)
  (let ((restart (FIND-RESTART 'USE-VALUE)))
    (when restart
      (INVOKE-RESTART restart value))))


(DEFINE-CONDITION PROGRAM-ERROR (ERROR) ())
(DEFINE-CONDITION CONTROL-ERROR (ERROR) ())

(DEFINE-CONDITION TYPE-ERROR (ERROR) (DATUM EXPECTED-TYPE))
;; TODO: inherit from SIMPLE-CONDITION
(DEFINE-CONDITION SIMPLE-TYPE-ERROR (TYPE-ERROR) (format args))

(DEFINE-CONDITION UNBOUND-VARIABLE (CELL-ERROR) ())
(DEFINE-CONDITION UNDEFINED-FUNCTION (CELL-ERROR) ())
(DEFINE-CONDITION UNBOUND-SLOT (CELL-ERROR) (INSTANCE))

(DEFINE-CONDITION PACKAGE-ERROR (ERROR) (PACKAGE))

(DEFINE-CONDITION STREAM-ERROR (ERROR) (STREAM))
(DEFINE-CONDITION END-OF-FILE (STREAM-ERROR) ())
(DEFINE-CONDITION READER-ERROR (STREAM-ERROR) ()) ;Also PARSE-ERROR.

(DEFINE-CONDITION FILE-ERROR (ERROR) (PATHNAME))

(DEFINE-CONDITION ARITHMETIC-ERROR (ERROR) (OPERATION OPERANDS))
(DEFINE-CONDITION DIVISION-BY-ZERO (ARITHMETIC-ERROR) ())
(DEFINE-CONDITION FLOATING-POINT-INVALID-OPERATION (ARITHMETIC-ERROR) ())
(DEFINE-CONDITION FLOATING-POINT-INEXACT (ARITHMETIC-ERROR) ())
(DEFINE-CONDITION FLOATING-POINT-OVERFLOW (ARITHMETIC-ERROR) ())
(DEFINE-CONDITION FLOATING-POINT-UNDERFLOW (ARITHMETIC-ERROR) ())

(DEFINE-CONDITION PRINT-NOT-READABLE (ERROR) (OBJECT))
