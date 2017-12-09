;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 14, Conses.

(IN-PACKAGE "EMACS-CL")

;;; System Class LIST
;;; System Class NULL
;;; System Class CONS
;;; Type ATOM

(dolist (sym '(cons consp atom))
  (apply (lambda (to from) (fset to (symbol-function from)))
	 (list (intern (upcase (symbol-name sym))) sym)))

(defun RPLACA (cons object)
  (setcar cons object)
  cons)

(defun RPLACD (cons object)
  (setcdr cons object)
  cons)

(fset 'CAR (symbol-function 'car))

(DEFSETF CAR (cons) (car)
  `(PROGN
     (RPLACA ,cons ,car)
     ,car))

(fset 'CDR (symbol-function 'cdr))

(DEFSETF CDR (cons) (cdr)
  `(PROGN
     (RPLACD ,cons ,cdr)
     ,cdr))

(defun build-cxr (string index var fn)
  (case (aref string index)
    (?A		(funcall fn 'CAR (build-cxr string (1+ index) var fn)))
    (?D		(funcall fn 'CDR (build-cxr string (1+ index) var fn)))
    (t		var)))

(defun plain-cxr (fn arg)
  `(,fn ,arg))

(defun backquoted-cxr (fn arg)
  `(list ',fn ,arg))

(macrolet ((def (sym)
	     (let ((name (symbol-name sym)))
	       `(progn
		 (defun ,sym (cons)
		   ,(build-cxr name 1 'cons #'plain-cxr))
		 (DEFSETF ,sym (cons) (obj)
		   (list ',(if (eq (aref name 1) ?A) 'setcar 'setcdr)
			 ,(build-cxr name 2 'cons #'backquoted-cxr)
			 obj))))))
  (def CAAR) (def CADR) (def CDAR) (def CDDR)
  (def CAAAR) (def CAADR) (def CADAR) (def CADDR)
  (def CDAAR) (def CDADR) (def CDDAR) (def CDDDR)
  (def CAAAAR) (def CAAADR) (def CAADAR) (def CAADDR)
  (def CADAAR) (def CADADR) (def CADDAR) (def CADDDR)
  (def CDAAAR) (def CDAADR) (def CDADAR) (def CDADDR)
  (def CDDAAR) (def CDDADR) (def CDDDAR) (def CDDDDR))

(defun COPY-TREE (tree)
  (if (CONSP tree)
      (CONS (COPY-TREE (CAR tree)) (COPY-TREE (CDR tree)))
      tree))

(cl:defun SUBLIS (alist tree &KEY KEY TEST TEST-NOT)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (let ((pair (ASSOC tree alist (kw KEY) KEY (kw TEST) TEST)))
    (cond
      (pair		(CDR pair))
      ((ATOM tree)	tree)
      (t		(CONS
			 (SUBLIS alist (CAR tree) (kw KEY) KEY (kw TEST) TEST)
			 (SUBLIS alist (CDR tree) (kw KEY) KEY (kw TEST) TEST))))))

(cl:defun NSUBLIS (alist tree &KEY KEY TEST TEST-NOT)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (let ((pair (ASSOC tree alist (kw KEY) KEY (kw TEST) TEST)))
    (cond
      (pair		(CDR pair))
      ((ATOM tree)	tree)
      (t
       (progn
	 (RPLACA tree (NSUBLIS alist (CAR tree) (kw KEY) KEY (kw TEST) TEST))
	 (RPLACD tree (NSUBLIS alist (CDR tree) (kw KEY) KEY (kw TEST) TEST)))))))

(cl:defun SUBST (new old tree &KEY KEY TEST TEST-NOT)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (cond
    ((FUNCALL TEST old (FUNCALL KEY tree))
     new)
    ((ATOM tree)
     tree)
    (t
     (CONS (SUBST new old (CAR tree) (kw KEY) KEY (kw TEST) TEST)
	   (SUBST new old (CDR tree) (kw KEY) KEY (kw TEST) TEST)))))

(cl:defun SUBST-IF (new predicate tree &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (cond
    ((FUNCALL predicate (FUNCALL KEY tree))
     new)
    ((ATOM tree)
     tree)
    (t
     (CONS (SUBST-IF new predicate (CAR tree) (kw KEY) KEY)
	   (SUBST-IF new predicate (CDR tree) (kw KEY) KEY)))))

(cl:defun SUBST-IF-NOT (new predicate tree &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (cond
    ((not (FUNCALL predicate (FUNCALL KEY tree)))
     new)
    ((ATOM tree)
     tree)
    (t
     (CONS (SUBST-IF new predicate (CAR tree) (kw KEY) KEY)
	   (SUBST-IF new predicate (CDR tree) (kw KEY) KEY)))))

(cl:defun NSUBST (new old tree &KEY KEY TEST TEST-NOT)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (cond
    ((FUNCALL TEST old (FUNCALL KEY tree))
     new)
    ((ATOM tree)
     tree)
    (t
     (RPLACA tree (NSUBST new old (CAR tree) (kw KEY) KEY (kw TEST) TEST))
     (RPLACD tree (NSUBST new old (CDR tree) (kw KEY) KEY (kw TEST) TEST)))))

(cl:defun NSUBST-IF (new predicate tree &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (cond
    ((FUNCALL predicate (FUNCALL KEY tree))
     new)
    ((ATOM tree)
     tree)
    (t
     (RPLACA tree (NSUBST-IF new predicate (CAR tree) (kw KEY) KEY))
     (RPLACD tree (NSUBST-IF new predicate (CDR tree) (kw KEY) KEY)))))

(cl:defun NSUBST-IF-NOT (new predicate tree &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (cond
    ((not (FUNCALL predicate (FUNCALL KEY tree)))
     new)
    ((ATOM tree)
     tree)
    (t
     (RPLACA tree (NSUBST-IF new predicate (CAR tree) (kw KEY) KEY))
     (RPLACD tree (NSUBST-IF new predicate (CDR tree) (kw KEY) KEY)))))

(cl:defun TREE-EQUAL (tree1 tree2 &KEY TEST TEST-NOT)
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (cond
    ((and (ATOM tree1) (ATOM tree2))
     (cl:values (FUNCALL TEST tree1 tree2)))
    ((and (CONSP tree1) (CONSP tree2))
     (and (TREE-EQUAL (CAR tree1) (CAR tree2) (kw TEST) TEST)
	  (TREE-EQUAL (CDR tree1) (CDR tree2) (kw TEST) TEST)))))

(fset 'COPY-LIST (symbol-function 'copy-list))

(fset 'LIST (symbol-function 'list))

(fset 'LIST* (symbol-function 'list*))

(fset 'LIST-LENGTH (symbol-function 'list-length))

(fset 'LISTP (symbol-function 'listp))

(cl:defun MAKE-LIST (size &KEY INITIAL-ELEMENT)
  (make-list size INITIAL-ELEMENT))

(cl:defmacro PUSH (object place)
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION place nil) ;TODO: environment
    (with-gensyms (obj)
      `(LET* ((,obj ,object)
	      ,@(MAPCAR #'list temps values)
	      (,(first variables) (CONS ,obj ,getter)))
	 ,setter))))

(cl:defmacro POP (place)
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION place nil) ;TODO: environment
    (with-gensyms (car get)
      `(LET* (,@(MAPCAR #'list temps values)
	      (,get ,getter)
	      (,car (CAR ,get))
	      (,(first variables) (CDR ,get)))
	 ,setter
	 ,car))))

(fset 'FIRST (symbol-function 'car))

(DEFSETF FIRST (list) (new)
  `(PROGN
     (RPLACA ,list ,new)
     ,new))

(defun SECOND (list)
  (CADR list))

(DEFSETF SECOND (list) (new)
  `(PROGN
     (RPLACA (CDR ,list) ,new)
     ,new))

(defun THIRD (list)
  (CADDR list))

(DEFSETF THIRD (list) (new)
  `(PROGN
     (RPLACA (CDDR ,list) ,new)
     ,new))

(defun FOURTH (list)
  (CADDDR list))

(DEFSETF FOURTH (list) (new)
  `(PROGN
     (RPLACA (CDDDR ,list) ,new)
     ,new))

(defun FIFTH (list)
  (CAR (CDDDDR list)))

(DEFSETF FIFTH (list) (new)
  `(PROGN
     (RPLACA (CDDDDR ,list) ,new)
     ,new))

(defun SIXTH (list)
  (CADR (CDDDDR list)))

(DEFSETF SIXTH (list) (new)
  `(PROGN
     (RPLACA (CDR (CDDDDR ,list)) ,new)
     ,new))

(defun SEVENTH (list)
  (CADDR (CDDDDR list)))

(DEFSETF SEVENTH (list) (new)
  `(PROGN
     (RPLACA (CDDR (CDDDDR ,list)) ,new)
     ,new))

(defun EIGHTH (list)
  (CADDDR (CDDDDR list)))

(DEFSETF EIGHTH (list) (new)
  `(PROGN
     (RPLACA (CDDDR (CDDDDR ,list)) ,new)
     ,new))

(defun NINTH (list)
  (CAR (CDDDDR (CDDDDR list))))

(DEFSETF NINTH (list) (new)
  `(PROGN
     (RPLACA (CDDDDR (CDDDDR ,list)) ,new)
     ,new))

(defun TENTH (list)
  (CADR (CDDDDR (CDDDDR list))))

(DEFSETF TENTH (list) (new)
  `(PROGN
     (RPLACA (CDR (CDDDDR (CDDDDR ,list))) ,new)
     ,new))

(fset 'NTH (symbol-function 'nth))

(DEFSETF NTH (n list) (new)
  (with-gensyms (cons)
    `(LET ((,cons (NTHCDR ,n ,list)))
       (WHEN ,cons
	 (RPLACA ,cons ,new))
       ,new)))

(defun ENDP (object)
  (cond
    ((null object)	'T)
    ((consp object)	nil)
    (t			(type-error object 'LIST))))

(defun NULL (list)
  (if list nil 'T))

(fset 'NCONC (symbol-function 'nconc))

(fset 'APPEND (symbol-function 'append))

(defun REVAPPEND (list tail)
  (nconc (reverse list) tail))

(defun NRECONC (list tail)
  (nconc (nreverse list) tail))

(cl:defun BUTLAST (list &OPTIONAL (n 1))
  (LDIFF list (LAST list n)))

(cl:defun NBUTLAST (list &OPTIONAL (n 1))
  (unless (listp list)
    (type-error list 'LIST))
  (unless (TYPEP n '(INTEGER 0))
    (type-error n '(INTEGER 0)))
  (do ((l list (cdr l))
       (r nil)
       (i 0 (binary+ i 1)))
      ((atom l)
       (when (consp r)
	 (setcdr r nil)
	 list))
    (cond
      ((binary= n i) (setq r list))
      ((binary< n i) (pop r)))))

(cl:defun LAST (list &OPTIONAL (n 1))
  (unless (listp list)
    (type-error list 'LIST))
  (unless (TYPEP n '(INTEGER 0))
    (type-error n '(INTEGER 0)))
  (do ((l list (cdr l))
       (r list)
       (i 0 (binary+ i 1)))
      ((atom l) r)
    (if (binary<= n i) (pop r))))

(defun LDIFF (list object)
  (unless (listp list)
    (type-error list 'LIST))
  (catch 'LDIFF
    (do ((list list (cdr list))
	 (r '() (cons (car list) r)))
	((atom list)
	 (if (EQL list object) (nreverse r) (NRECONC r list)))
      (when (EQL object list)
	(throw 'LDIFF (nreverse r))))))

(defun TAILP (object list)
  (unless (listp list)
    (type-error list 'LIST))
  (catch 'TAILP
    (do ((list list (cdr list)))
	((atom list) (EQL list object))
      (if (EQL object list)
	  (throw 'TAILP T)))))

(fset 'NTHCDR (symbol-function 'nthcdr))

(fset 'REST (symbol-function 'cdr-safe))

(DEFSETF REST (cons) (cdr)
  `(setcdr ,cons ,cdr))

(cl:defun MEMBER (object list &KEY KEY TEST TEST-NOT)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (catch 'MEMBER
    (do ((list list (cdr list)))
	((null list) nil)
      (when (FUNCALL TEST object (FUNCALL KEY (car list)))
	(throw 'MEMBER list)))))

(cl:defun MEMBER-IF (predicate list &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (catch 'MEMBER-IF
    (do ((list list (cdr list)))
	((null list) nil)
      (when (FUNCALL predicate (FUNCALL KEY (car list)))
	(throw 'MEMBER-IF list)))))

(cl:defun MEMBER-IF-NOT (predicate list &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (catch 'MEMBER-IF-NOT
    (do ((list list (cdr list)))
	((null list) nil)
      (unless (FUNCALL predicate (FUNCALL KEY (car list)))
	(throw 'MEMBER-IF-NOT list)))))

(defun MAPC (fn &rest lists)
  (when (null lists)
    (ERROR 'PROGRAM-ERROR))
  (let ((result (car lists)))
    (while (notany (cl:function ENDP) lists)
      (APPLY fn (mapcar (cl:function car) lists))
      (setq lists (mapcar (cl:function cdr) lists)))
    result))

(defun MAPCAR (fn &rest lists)
  (when (null lists)
    (ERROR 'PROGRAM-ERROR))
  (let ((result nil))
    (while (notany (cl:function ENDP) lists)
      (push (APPLY fn (mapcar (cl:function car) lists)) result)
      (setq lists (mapcar 'cdr lists)))
    (nreverse result)))

(defun MAPCAN (fn &rest lists)
  (apply (cl:function nconc)
	 (apply (cl:function MAPCAR) fn lists)))

(defun MAPL (fn &rest lists)
  (when (null lists)
    (ERROR 'PROGRAM-ERROR))
  (let ((result (car lists)))
    (while (notany (cl:function ENDP) lists)
      (APPLY fn lists)
      (setq lists (mapcar (cl:function cdr) lists)))
    result))

(defun MAPLIST (fn &rest lists)
  (when (null lists)
    (ERROR 'PROGRAM-ERROR))
  (let ((result nil))
    (while (notany (cl:function ENDP) lists)
      (push (APPLY fn lists) result)
      (setq lists (mapcar 'cdr lists)))
    (nreverse result)))

(defun MAPCON (fn &rest lists)
  (apply (cl:function nconc)
	 (apply (cl:function MAPLIST) fn lists)))

(defun ACONS (key datum alist)
  (CONS (CONS key datum) alist))

(cl:defun ASSOC (item alist &KEY KEY TEST TEST-NOT)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (catch 'ASSOC
    (dolist (pair alist)
      (when (and pair (FUNCALL TEST item (FUNCALL KEY (car pair))))
	(throw 'ASSOC pair)))))

(cl:defun ASSOC-IF (predicate alist &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (catch 'ASSOC-IF
    (dolist (pair alist)
      (when (and pair (FUNCALL predicate (FUNCALL KEY (car pair))))
	(throw 'ASSOC-IF pair)))))

(cl:defun ASSOC-IF-NOT (predicate alist &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (catch 'ASSOC-IF-NOT
    (dolist (pair alist)
      (when (and pair (not (FUNCALL predicate (FUNCALL KEY (car pair)))))
	(throw 'ASSOC-IF-NOT pair)))))

(defun COPY-ALIST (alist)
  (mapcar (lambda (pair) (CONS (CAR pair) (CDR pair))) alist))

(defun PAIRLIS (keys data &optional alist)
  (NCONC (MAPCAR #'CONS keys data) alist))

(cl:defun RASSOC (item alist &KEY KEY TEST TEST-NOT)
  (unless KEY
    (setq KEY #'IDENTITY))
  (when (and TEST TEST-NOT)
    (error "error"))
  (when TEST-NOT
    (setq TEST (COMPLEMENT TEST-NOT)))
  (unless TEST
    (setq TEST #'EQL))
  (catch 'RASSOC
    (dolist (pair alist)
      (when (and pair (FUNCALL TEST item (FUNCALL KEY (cdr pair))))
	(throw 'RASSOC pair)))))

(cl:defun RASSOC-IF (predicate alist &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (catch 'RASSOC-IF
    (dolist (pair alist)
      (when (and pair (FUNCALL predicate (FUNCALL KEY (cdr pair))))
	(throw 'RASSOC-IF pair)))))

(cl:defun RASSOC-IF-NOT (predicate alist &KEY KEY)
  (unless KEY
    (setq KEY #'IDENTITY))
  (catch 'RASSOC-IF-NOT
    (dolist (pair alist)
      (when (and pair (not (FUNCALL predicate (FUNCALL KEY (cdr pair)))))
	(throw 'RASSOC-IF pair)))))

(defun* GET-PROPERTIES (plist indicators)
  (do ((plist plist (cddr plist)))
      ((null plist)
       (cl:values nil nil nil))
    (when (memq (car plist) indicators)
      (return-from GET-PROPERTIES
	(cl:values (car plist) (cadr plist) plist)))))

(defun* GETF (plist indicator &optional default)
  (do ((plist plist (cddr plist)))
      ((null plist)
       default)
    (when (eq (car plist) indicator)
      (return-from GETF (cadr plist)))))

(DEFINE-SETF-EXPANDER GETF (plist indicator &optional default)
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION plist nil) ;TODO: env
    (with-gensyms (itemp dtemp obj)
      (let (ilist)
	(unless (null default)
	  (push dtemp temps)
	  (push default values))
	(if (CONSTANTP indicator)
	    (setq itemp (eval-with-env indicator nil) ;TODO: env
		  ilist `(QUOTE (,itemp)))
	    (setq temps (cons itemp temps)
		  values (cons indicator values)
		  ilist `(LIST ,itemp)))
	(cl:values temps
		   values
		   (list obj)
		   `(MULTIPLE-VALUE-BIND (ind val tail)
			(GET-PROPERTIES ,getter ,ilist)
		      (IF (NULL tail)
			  (MULTIPLE-VALUE-BIND ,variables 
			      (LIST* ,itemp ,obj ,getter)
			    ,setter)
			  (SETF (SECOND tail) ,obj)))
		   `(GETF ,getter ,itemp))))))

(defun delete-property (plist indicator)
  (cond
    ((null plist)			nil)
    ((eq (car plist) indicator)		(cddr plist))
    (t					(RPLACD (cdr plist)
						(delete-property (cddr plist)
								 indicator))
					plist)))

(cl:defmacro REMF (place indicator) ;TODO: &environment
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION place nil)
    `(LET* (,@(MAPCAR #'list temps values)
	    (,(first variables) (delete-property ,getter ,indicator)))
       ,setter)))

(cl:defun INTERSECTION (list1 list2 &REST keys)
  (let ((result nil))
    (dolist (x list1 result)
      (when (apply #'MEMBER x list2 keys)
	(push x result)))))

(fset 'NINTERSECTION (symbol-function 'INTERSECTION))

(cl:defun ADJOIN (object list &REST keys)
  (if (apply #'MEMBER object list keys)
      list
      (cons object list)))

(cl:defmacro PUSHNEW (object place &rest keys)
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION place nil) ;TODO: environment
    (with-gensyms (obj)
      `(LET* ((,obj ,object)
	      ,@(MAPCAR #'list temps values)
	      (,(first variables) (ADJOIN ,obj ,getter ,@keys)))
	 ,setter))))

(cl:defun SET-DIFFERENCE (list1 list2 &REST keys)
  (let ((result nil))
    (dolist (x list1 result)
      (unless (apply #'MEMBER x list2 keys)
	(push x result)))))

(fset 'NSET-DIFFERENCE (symbol-function 'SET-DIFFERENCE))

(cl:defun SET-EXCLUSIVE-OR (list1 list2 &REST keys)
  (let ((result nil))
    (dolist (x list1)
      (unless (apply #'MEMBER x list2 keys)
	(push x result)))
    (dolist (x list2 result)
      (unless (apply #'MEMBER x list1 keys)
	(push x result)))))

(fset 'NSET-EXCLUSIVE-OR (symbol-function 'SET-EXCLUSIVE-OR))

(cl:defun SUBSETP (list1 list2 &REST keys)
  (EVERY (lambda (x) (apply #'MEMBER x list2 keys))
	 list1))

(cl:defun UNION (list1 list2 &REST keys)
  (let ((result nil))
    (dolist (x list1)
      (setq result (apply #'ADJOIN x result keys)))
    (dolist (x list2 result)
      (setq result (apply #'ADJOIN x result keys)))))

(fset 'NUNION (symbol-function 'UNION))
