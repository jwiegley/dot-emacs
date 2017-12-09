;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements EVAL and environment objects.

;;; Possible future implementation:
;;; (defun EVAL (form)
;;;   (funcall (cl:values (COMPILE nil `(LAMBDA () ,form)))))

(IN-PACKAGE "EMACS-CL")

(defvar *special-operator-evaluators* (make-hash-table))

(defmacro* define-special-operator (name (&rest args) env &body body)
  `(progn
     (unless (fboundp ',name)
       (fset ',name nil))
     (setf (gethash ',name *special-operator-evaluators*)
           (function* (lambda (,env ,@args) ,@body)))))

(defun eval-body (forms env)
  (let ((lastval nil))
    (cl:values nil)
    (dolist (form forms lastval)
      (setq lastval (eval-with-env form env)))))

;;; Definitions for all special operators follows.

(define-special-operator BLOCK (tag &rest forms) env
  (let* ((catch-tag (gensym))
	 (new-env (augment-environment env :block (cons tag catch-tag))))
    (catch catch-tag
      (eval-body forms new-env))))

(define-special-operator CATCH (tag &rest forms) env
  (catch (eval-with-env tag env)
    (eval-body forms env)))

(define-special-operator EVAL-WHEN (situations &body body) env
  (when (or (memq (kw EXECUTE) situations) (memq 'EVAL situations))
    (eval-body body env)))

(define-special-operator FLET (fns &rest forms) env
  (let ((new-env (augment-environment env :function (mapcar #'first fns))))
    (dolist (fn fns)
      (setf (lexical-function (first fn) new-env)
	    (MULTIPLE-VALUE-BIND (body decls doc) (parse-body (cddr fn) t)
	      (enclose `(LAMBDA ,(second fn)
			  ,@(when decls `((DECLARE ,@decls)))
			  (BLOCK ,(function-block-name (first fn))
			    ,@body))
		       env (first fn) doc))))
    (MULTIPLE-VALUE-BIND (body declarations) (parse-body forms)
      (eval-body body new-env))))

(defun lexical-or-global-function (name env)
  (multiple-value-bind (type localp decl) (function-information name env)
    (if (eq type :function)
	(if localp (lexical-function name env) (FDEFINITION name))
	(ERROR 'UNDEFINED-FUNCTION (kw NAME) name))))

(define-special-operator FUNCTION (form) env
  (cl:values
    (cond
      ((SYMBOLP form)		(lexical-or-global-function form env))
      ((ATOM form)		(not-function-name-error form))
      ((case (first form)
	 (LAMBDA		(enclose form env form))
	 (SETF			(lexical-or-global-function form env))
	 (t			(not-function-name-error form)))))))

(define-special-operator GO (tag) env
  (let ((info (tagbody-information tag env)))
    (if info
	(throw info tag)
	(ERROR 'PROGRAM-ERROR))))

(define-special-operator IF (condition then &optional else) env
  (if (eval-with-env condition env)
      (eval-with-env then env)
      (eval-with-env else env)))

(define-special-operator LABELS (fns &rest forms) env
  (let ((new-env (augment-environment env :function (mapcar #'first fns))))
    (dolist (fn fns)
      (setf (lexical-function (first fn) new-env)
	    (MULTIPLE-VALUE-BIND (body decls doc) (parse-body (cddr fn) t)
	      (enclose `(LAMBDA ,(second fn)
			  ,@(when decls `((DECLARE ,@decls)))
			  (BLOCK ,(function-block-name (first fn))
			    ,@body))
		       new-env (first fn) doc))))
    (MULTIPLE-VALUE-BIND (body decls) (parse-body forms)
      (eval-body body new-env))))

(defun lexical-variable-p (var env)
  (eq (nth-value 0 (variable-information var env)) :lexical))

(defun special-variable-p (var env)
  (not (lexical-variable-p var env)))

;;; TODO: let* bindings shouldn't be evaluated in an environment where
;;; succeeding bindings exist.
(defun eval-let (bindings forms env old-env)
  (MULTIPLE-VALUE-BIND (body decls) (parse-body forms)
    (let* ((vars (mapcar #'first-or-identity bindings))
	   (new-env (augment-environment env :variable vars :declare decls))
	   (oldvals nil))
      (dolist (binding bindings)
	(multiple-value-bind (var val) (if (symbolp binding)
					   (values binding nil)
					   (values (first binding)
						   (eval-with-env
						    (second binding)
						    (or old-env new-env))))
	  (if (lexical-variable-p var new-env)
	      (setf (lexical-value var new-env) val)
	      (progn
		(push (if (boundp var) (symbol-value var) unbound) oldvals)
		(setf (symbol-value var) val)))))
      (unwind-protect
	   (eval-body body new-env)
	(setq oldvals (nreverse oldvals))
	(dolist (binding bindings)
	  (let ((var (if (symbolp binding) binding (first binding))))
	    (unless (lexical-variable-p var new-env)
	      (let ((val (pop oldvals)))
		(if (eq val unbound)
		    (makunbound var)
		    (setf (symbol-value var) val))))))))))

(define-special-operator LET (bindings &rest forms) env
  (eval-let bindings forms env env))

(define-special-operator LET* (bindings &rest forms) env
  (eval-let bindings forms env nil))

(define-special-operator LOAD-TIME-VALUE (form &optional read-only-p) env
  (cl:values (eval-with-env form nil)))

(define-special-operator LOCALLY (&rest forms) env
  (MULTIPLE-VALUE-BIND (body declarations) (parse-body forms)
    (eval-body body env)))

(defun macro-body (lambda-list decls body fvar form)
  (if (eq (first lambda-list) '&WHOLE)
      (unless (eql (length lambda-list) 2)
	(push (gensym) (cddr lambda-list)))
      (setq form `(CDR ,fvar)))
  (unless (null lambda-list)
    (setq body `((DESTRUCTURING-BIND ,lambda-list ,form
		   ,@(when decls `((DECLARE ,@decls)))
		   ,@body))))
  (cl:values body form))

(defun compiler-macro-body (lambda-list decls body fvar form)
  (let ((wvar nil))
    (when (eq (first lambda-list) '&WHOLE)
      (setq wvar (second lambda-list))
      (setq lambda-list (cddr lambda-list)))
    (unless (null lambda-list)
      (setq body `((SETQ ,fvar
		         (IF (EQ (CAR ,fvar) (QUOTE FUNCALL))
			     (CDDR ,fvar)
			     (CDR ,fvar)))
		   (DESTRUCTURING-BIND ,lambda-list ,fvar
		     ,@(when decls `((DECLARE ,@decls)))
		     ,@body))))
    (when wvar
      (setq body `((LET ((,wvar ,fvar)) ,@body))))
    (cl:values body form)))

(defun* make-macro-function (name lambda-list forms &optional env
			     &key type)
  (with-gensyms (fvar evar)
    (let ((e (memq '&ENVIRONMENT lambda-list))
	  (form fvar))
      (when e
	(when (null (cdr e))
	  (ERROR 'PROGRAM-ERROR))
	(setq evar (second e))
	(let ((x lambda-list))
	  (while x
	    (when (eq (cadr x) '&ENVIRONMENT)
	      (setf (cdr x) (cdddr x)))
	    (setq x (cdr x)))))
      (MULTIPLE-VALUE-BIND (body decls doc) (parse-body forms t)
	(MULTIPLE-VALUE-SETQ (body form)
	  (if (eq type 'COMPILER-MACRO)
	      (compiler-macro-body lambda-list decls body fvar form)
	      (macro-body lambda-list decls body fvar form)))
	(setq body `(,@(when doc (list doc))
		     (BLOCK ,name ,@body)))
	(let ((fn `(LAMBDA (,fvar ,evar) ,@body)))
	  (when env
	    (setq fn (enclose fn env name)))
	  fn)))))

(defun env-with-macros (env macros decls)
  (let ((new-env (augment-environment env :macro (mapcar #'first macros)
				      :declare decls)))
    (dolist (macro macros)
      (destructuring-bind (name lambda-list &rest body) macro
	(setf (MACRO-FUNCTION name new-env)
	      (make-macro-function name lambda-list body env))))
    new-env))

(define-special-operator MACROLET (macros &rest forms) env
  (MULTIPLE-VALUE-BIND (body decls) (parse-body forms)
    (let ((new-env (env-with-macros env macros decls)))
      (eval-body body new-env))))

(define-special-operator MULTIPLE-VALUE-CALL (fn &rest forms) env
  (let ((values nil))
    (dolist (form forms)
      (setq values (append values
			   (MULTIPLE-VALUE-LIST (eval-with-env form env)))))
    (APPLY (eval-with-env fn env) values)))

(define-special-operator MULTIPLE-VALUE-PROG1 (form &rest forms) env
  (let ((values (MULTIPLE-VALUE-LIST (eval-with-env form env))))
    (eval-body forms env)
    (VALUES-LIST values)))

(define-special-operator PROGN (&rest forms) env
  (eval-body forms env))

(defmacro defun-do-progv ()
  (with-gensyms (sym syms vals fn temp state)
  `(defun do-progv (,syms ,vals ,fn)
    (let ((,state nil))
      (unwind-protect
	   (progn
	     (dolist (,sym ,syms)
	       (let ((,temp (boundp ,sym)))
		 (when ,temp
		   (push (symbol-value ,sym) ,state))
		 (push ,temp ,state))
	       (if (null ,vals)
		   (makunbound ,sym)
		   (set ,sym (pop ,vals))))
	     (FUNCALL ,fn))
	(dolist (,sym ,syms)
	  (if (pop ,state)
	      (set ,sym (pop ,state))
	      (makunbound ,sym))))))))

(defun-do-progv)

(define-special-operator PROGV (symbols values &rest forms) env
  (do-progv (eval-with-env symbols env)
            (eval-with-env values env)
	    (enclose `(LAMBDA () ,@forms) env)))

(define-special-operator QUOTE (form) env
  (cl:values form))

(define-special-operator RETURN-FROM (tag &optional form) env
  (let ((info (block-information tag env)))
    (if info
	(throw (cdr info) (eval-with-env form env))
	(ERROR 'PROGRAM-ERROR))))

(define-special-operator SETQ (&rest forms) env
  (when (oddp (length forms))
    (ERROR "Odd number of forms in SETQ"))
  (do ((lastval nil)
       (forms forms (cddr forms)))
      ((null forms)
       (cl:values lastval))
    (let* ((var (first forms))
	   (vals (MULTIPLE-VALUE-LIST (eval-with-env (second forms) env)))
	   (val (first vals)))
      (unless (symbolp var)
	(ERROR "Setting non-symbol ~S" var))
      (setq lastval
	    (ecase (nth-value 0 (variable-information var env))
	      (:lexical		(setf (lexical-value var env) val))
	      (:special		(set var val))
	      ((nil)		(WARN "Setting undefined variable ~S" var)
				(set var val))
	      (:symbol-macro	(eval-with-env
				 `(SETF ,(MACROEXPAND var env)
				        (VALUES-LIST (QUOTE ,vals)))
				 env))
	      (:constant	(ERROR "Setting constant ~S" var)))))))

(define-special-operator SYMBOL-MACROLET (macros &rest forms) env
  (MULTIPLE-VALUE-BIND (body decls) (parse-body forms)
    (let ((new-env (augment-environment env :symbol-macro
					(mapcar #'first macros))))
      (dolist (macro macros)
	(setf (lexical-value (first macro) new-env)
	      (enclose `(LAMBDA (form env) (QUOTE ,(second macro)))
		       env (first macro))))
      (eval-body body new-env))))

(defun go-tag-p (object)
  (or (INTEGERP object) (symbolp object)))

(define-special-operator TAGBODY (&rest forms) env
  (let* ((catch-tag (gensym))
	 (new-env (augment-environment
		   env :tagbody
		   (cons catch-tag (remove-if-not #'go-tag-p forms))))
	 (exe forms)
	 (no-tag 0.0))
    (while exe
      (let ((form (first exe)))
	(cond
	  ((go-tag-p form)
	   (setq exe (rest exe)))
	  ((consp form)
	   (let ((tag (catch catch-tag
			(eval-with-env form new-env)
			no-tag)))
	     (if (eq tag no-tag)
		 (setq exe (rest exe))
		 (setq exe (member tag forms)))))
	  (t
	   (ERROR "Syntax error: ~S in tagbody is neither a go tag ~
		   nor a compound expression" form))))))
  (cl:values nil))

(define-special-operator THE (type form) env
  (eval-with-env form env))

(define-special-operator THROW (tag form) env
  (throw (eval-with-env tag env) (eval-with-env form env)))

(define-special-operator UNWIND-PROTECT (protected &rest cleanups) env
  (let (ntmp mtmp)
    (prog1 (unwind-protect (prog1 (eval-with-env protected env)
			     (setq ntmp nvals mtmp mvals))
	     (eval-body cleanups env))
      (setq nvals ntmp mvals mtmp))))



(defun variable-information (var &optional env)
  (unless env
    (setq env *global-environment*))
  (values
    (let ((info (assoc var (aref env 1))))
      (cond
	(info			(cdr info))
	((boundp var)		(if (CONSTANTP var env) :constant :special))
	((memq var *constants*)	:constant)
	((memq var *specials*)	:special)))
    (member var (aref env 2))
    nil))

(defun lexical-value (var env)
  (cdr (assq var (aref env 3))))

(defsetf lexical-value (var env) (val)
  `(setf (cdr (assq ,var (aref ,env 3))) ,val))

(defun function-information (fn &optional env)
  (unless env
    (setq env *global-environment*))
  (values
   (let ((info (assoc fn (aref env 4))))
     (if info
	 (cdr info)
	 (cond
	   ((gethash fn *macro-functions*)	:macro)
	   ((FBOUNDP fn)			:function)
	   ((and (symbolp fn)
		 (SPECIAL-OPERATOR-P fn))	:special-operator))))
   (member fn (aref env 5))
   nil))

(defun lexical-function (name env)
  (cdr-safe (assoc name (aref env 6))))

(defsetf lexical-function (name env) (fn)
  `(let ((cons (assoc ,name (aref ,env 6))))
     (if cons
	 (setf (cdr cons) ,fn)
	 (progn (aset ,env 6 (acons ,name ,fn (aref ,env 6)))
		,fn))))

(defun block-information (tag env)
  (when env
    (assoc tag (aref env 7))))

(defun tagbody-information (tag env)
  (when env
    (let ((tagbody (find-if (lambda (x) (member tag (rest x))) (aref env 8))))
      (first tagbody))))

(defun* augment-environment (env &key variable symbol-macro function
				      macro declare block tagbody)
  (unless env
    (setq env *global-environment*))
  (let ((lexicals (remove-if (lambda (var) (memq var *specials*)) variable))
	(var-info (aref env 1))
	(var-local (aref env 2))
	(var-storage (aref env 3))
	(fn-info (aref env 4))
	(fn-local (aref env 5))
	(fn-storage (aref env 6))
	(block-info (aref env 7))
	(tagbody-info (aref env 8)))
    (setq var-local (append lexicals symbol-macro var-local))
    (dolist (decl declare)
      (when (eq (first decl) 'SPECIAL)
	(dolist (var (rest decl))
	  (setq var-info (acons var :special var-info))
	  (setq lexicals (delq var lexicals)))))
    (setq var-info (reduce (lambda (env var) (acons var :lexical env))
			   lexicals
			   :initial-value var-info))
    (setq var-info (reduce (lambda (env var) (acons var :symbol-macro env))
			   symbol-macro
			   :initial-value var-info))
    (dolist (var lexicals)
      (push (cons var nil) var-storage))
    (dolist (var symbol-macro)
      (push (cons var nil) var-storage))
    (setq fn-info (reduce (lambda (env fn) (acons fn :function env))
			  function
			  :initial-value fn-info))
    (setq fn-info (reduce (lambda (env mac) (acons mac :macro env))
			  macro
			  :initial-value fn-info))
    (setq fn-local (append function macro fn-local))
    (dolist (fn function)
      (push (cons fn nil) fn-storage))
    (dolist (fn macro)
      (push (cons fn nil) fn-storage))
    (setq block-info (cons block block-info))
    (setq tagbody-info (cons tagbody tagbody-info))
  (vector 'environment var-info var-local var-storage
	               fn-info fn-local fn-storage
	               block-info tagbody-info)))

(cl:defun enclose (lambda-exp &OPTIONAL env (name ""))
  (unless env
    (setq env *global-environment*))
  (MULTIPLE-VALUE-BIND (body decls doc) (parse-body (cddr lambda-exp) t)
    (vector 'INTERPRETED-FUNCTION
	    `(LAMBDA ,(second lambda-exp) (DECLARE ,@decls) ,@body)
	    env name doc)))

(defun INTERPRETED-FUNCTION-P (object)
  (vector-and-typep object 'INTERPRETED-FUNCTION))

(defun function-name (fn)
  (cond
    ((INTERPRETED-FUNCTION-P fn)
     (interp-fn-name fn))
    ((byte-code-function-p fn)
     "")
    ((subrp fn)
     (let ((string (prin1-to-string fn)))
       (substring string 7 (1- (length string)))))
    ((listp fn)
     "")
    (t
     (type-error fn 'FUNCTION))))

(defsetf function-name set-function-name)

(DEFSETF function-name set-function-name)

(defun set-function-name (fn name)
  (cond
    ((INTERPRETED-FUNCTION-P fn)
     (setf (interp-fn-name fn) name))
    ((byte-code-function-p fn)
     name)
    ((subrp fn)
     name)
    ((listp fn)
     name)
    (t
     (type-error fn 'FUNCTION))))



(defun* parse-body (forms &optional doc-allowed)
  (do ((decl nil)
       (doc nil)
       (body forms (rest body)))
      ((null forms)
       (cl:values nil decl doc))
    (flet ((done () (return-from parse-body (cl:values body decl doc))))
      (let ((form (first body)))
	(cond
	  ((STRINGP form)
	   (if (and doc-allowed (not doc) (rest body))
	       (setq doc form)
	       (done)))
	  ((and (consp form) (eq (first form) 'DECLARE))
	   (dolist (d (rest form))
	     (push d decl)))
	  (t
	   (done)))))))

(defun set-local-macro (name fn env)
  (augment-environment env :macro (list name))
  (setf (lexical-function name env) fn))

(defun eval-lambda-expr (lambda-expr args old-env)
  (MULTIPLE-VALUE-BIND (body decls doc) (parse-body (cddr lambda-expr) t)
    (let* ((lambda-list (second lambda-expr))
	   (new-env
	    (augment-environment old-env
	      :variable (lambda-list-variables lambda-list)
	      :declare decls))
	  (other-keys-p nil)
	  (allow-other-keys-p (memq '&ALLOW-OTHER-KEYS lambda-list)))
      (do-lambda-list (((key var) default supplied) kind lambda-list)
	;; TODO: special variables.
	(case kind
	  (:required
	   (unless args
	     (ERROR "No value for required parameter."))
	   (setf (lexical-value var new-env) (pop args)))
	  (&OPTIONAL
	   (when supplied
	     (setf (lexical-value supplied new-env) args))
	   (setf (lexical-value var new-env)
		 (if args
		     (pop args)
		     (eval-with-env default env))))
	  (&REST
	   (setf (lexical-value var new-env) (copy-list args))
	   (unless (memq '&KEY lambda-list)
	     (setq args nil)))
	  (&KEY
	   (let ((arg (memq key args)))
	     (cond
	       (arg
		(setf (lexical-value var new-env) (second arg))
		(when supplied (setf (lexical-value supplied new-env) 'T))
		(remf args (first arg)))
	       (t
		(setf (lexical-value var new-env) (eval-with-env default env))
		(when supplied (setf (lexical-value supplied new-env) nil))))))
	  (&AUX
	   (setf (lexical-value var new-env)
		 (eval-with-env default new-env)))))
      (when (and args (not (or allow-other-keys-p
			       (memq (kw ALLOW-OTHER-KEYS) args))))
	(ERROR 'PROGRAM-ERROR))
      (eval-body body new-env))))

(defun eval-forms (forms env)
  (mapcar (lambda (form) (eval-with-env form env))
	  forms))

(defun eval-with-env (form env)
  (unless env
    (setq env *global-environment*))
  (setq form (cl:values (MACROEXPAND form env)))
  (cond
    ((SYMBOLP form)
     (ecase (nth-value 0 (variable-information form env))
       ((nil)		(ERROR 'UNBOUND-VARIABLE (kw NAME) form))
       (:special	(SYMBOL-VALUE form))
       (:lexical	(lexical-value form env))
       (:symbol-macro	(error "shouldn't happen"))
       (:constant	(SYMBOL-VALUE form))))
    ((ATOM form)
     form)
    ((consp (car form))
     (if (eq (caar form) 'LAMBDA)
	 (eval-lambda-expr (first form) (eval-forms (rest form) env) env)
	 (ERROR 'PROGRAM-ERROR)))
    (t
     (let* ((name (first form))
	    (fn (gethash name *special-operator-evaluators*)))
       (cond
	 (fn
	  (apply fn env (rest form)))
	 ((setq fn (lexical-or-global-function name env))
	  (let ((args (eval-forms (rest form) env)))
	    (setq nvals 1 mvals nil)
	    (if (listp fn)
		;; Special hack for interpreted Emacs Lisp function.
		(apply fn args)
		(APPLY fn args)))))))))

(defun cl-debugger (&optional error args)
  (unless (eval-when-compile (featurep 'xemacs))
    (incf num-nonmacro-input-events))
  ;; error:
  ;;   lambda - function entry, debug-on-next-call
  ;;   debug - function entry, breakpoint
  ;;   t - evaluation of list form
  ;;   exit - exit of marked stack frame
  ;;   error - error or quit signalled
  ;;   nil - enter explicitly
  (unless (eq error 'error)
    (debug))
  (case (car args)
    (quit	(debug))
    (range-error
		nil)
    (void-variable
		(ERROR 'UNBOUND-VARIABLE))
    ((void-function invalid-function)
		(ERROR 'UNDEFINED-FUNCTION))
    ((wrong-type-argument)
		(ERROR 'TYPE-ERROR))
    (no-catch
		(ERROR 'CONTROL-ERROR))
    ((wrong-number-of-arguments no-catch wrong-type-argument)
		(ERROR 'PROGRAM-ERROR))
    (setting-constant
		(ERROR 'ERROR))
    (error	(ERROR "~A." (cadr args)))
    (t		(ERROR "Error: ~A ~S" error args))))

(defun EVAL (form)
  (let ((debug-on-error t)
	(debug-on-quit t)
	(debug-on-signal t)
	(debug-ignored-errors nil)
	(debugger 'cl-debugger))
    (eval-with-env form nil)))
