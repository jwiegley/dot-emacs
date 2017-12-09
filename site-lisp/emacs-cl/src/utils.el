;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file provides various small utilities.

(defun map-to-gensyms (list)
  (mapcar (lambda (x) (gensym)) list))

(defmacro* with-gensyms (syms &body body)
  ;;`(let ,(mapcar #'list syms '#1=((gensym) . #1#))
  `(let ,(mapcar (lambda (sym) `(,sym ',(gensym))) syms)
     ,@body))

(defun cl:string (x)
  (cond
    ((stringp x)	x)
    ((symbolp x)	(symbol-name x))
    (t			(error "type error"))))

(defun strcat (&rest string-designators)
  (apply #'concat (mapcar #'cl:string string-designators)))

(defun symcat (&rest string-designators)
  (let ((sym (intern (apply #'strcat string-designators))))
    (when (fboundp 'SYMBOL-PACKAGE)
      (setf (SYMBOL-PACKAGE sym) *PACKAGE*))
    sym))

(defun cl:symcat (&rest string-designators)
  (let ((sym (INTERN (apply #'strcat string-designators))))
    ;(when (fboundp 'SYMBOL-PACKAGE)
      (setf (SYMBOL-PACKAGE sym) *PACKAGE*);)
    sym))

(defun just-one (list)
  (cond
    ((atom list)	list)
    ((cdr list)		(error "error"))
    (t			(car list))))

(defun mappend (fn &rest lists)
  (apply #'append
   (if (null (cdr lists))
       (mapcar fn (car lists))
       (cl-mapcar-many fn lists))))

(defun vector-and-typep (object type)
  (and (vectorp object)
       (eq (aref object 0) type)))

(defun curry (fn &rest args1)
  `(lambda (&rest args2)
     (apply ',fn ,@(mapcar (lambda (x) (list 'quote x)) args1) args2)))

(defun rcurry (fn &rest args2)
  `(lambda (&rest args1) (apply ',fn (append args1 ',args2))))

(defmacro compose (&rest fns)
  (if fns
      (let ((fn1 (car (last fns)))
	    (fns (butlast fns)))
	`(lambda (&rest args)
	  ,(reduce (lambda (f1 f2) `(,f1 ,f2)) fns
		   :from-end t :initial-value `(apply ',fn1 args))))
      #'identity))

(defun ensure-list (object)
  (if (listp object)
      object
      (list object)))

(defmacro* do-list-designator ((var list &optional result) &body body)
  `(dolist (,var (ensure-list ,list) ,result)
     ,@body))

(defmacro* do-plist ((prop val plist &optional result) &body body)
  (with-gensyms (list)
    `(do ((,list ,plist)
	  ,prop ,val)
         ((null ,list)
	  ,result)
      (setq ,prop (pop ,list) ,val (pop ,list))
      ,@body)))

(defun el-keyword (symbol)
  (intern (concat ":" (symbol-name symbol))))

;;; Bootstrap magic: this list of symbols will later be imported into
;;; the KEYWORD package.
(defvar *initial-keywords* nil)

;;; Initially, this function pushes all created symbols onto
;;; *initial-keywords*.  Later, it will be redefined to intern symbols
;;; into the KEYWORD package directly.
(defun keyword (name)
  (let ((sym (find name *initial-keywords* :key 'symbol-name :test 'string=)))
    (or sym
	(let ((sym (make-symbol name)))
	  (push sym *initial-keywords*)
	  (set sym sym)
	  sym))))

(if (eval-when-compile (featurep 'xemacs))
    (defmacro kw (name) `(keyword ,(symbol-name name)))
    (defmacro kw (name) `(load-time-value (keyword ,(symbol-name name)))))

(defun type-error (datum type)
  (ERROR 'TYPE-ERROR (kw DATUM) datum (kw EXPECTED-TYPE) type))

(defconst use-character-type-p (eq (type-of ?A) 'character))

(if use-character-type-p
    (progn
      (defmacro ch (code) (int-char code))
      (defmacro ch= (char code) `(char= ,char ,(int-char code)))
      (defmacro cl-char (char) char)
      (defmacro el-char (char) char))
    (progn
      (defmacro ch (code) (vector 'CHARACTER code))
      (defmacro ch= (char code) `(eq (aref ,char 1) ,code))
      (defmacro cl-char (char) `(vector 'CHARACTER ,char))
      (defmacro el-char (char) `(aref ,char 1))))

(defmacro define-storage-layout (type slots)
  (let ((index 0))
    `(progn
       ,@(mapcar (lambda (slot)
		   `(defmacro ,(symcat type "-" slot) (object)
		      (list 'aref object ,(incf index))))
		 slots)
       ',type)))

;;; This macro can be used instead of VALUES.
(defmacro cl:values (&rest vals)
  (let ((n (length vals)))
    (case n
      (0	`(setq nvals 0 mvals nil))
      (1	`(prog1 ,(car vals) (setq nvals 1 mvals nil)))
      (t	`(prog1
		   ,(car vals)
		   (setq nvals ,n mvals (list ,@(cdr vals))))))))

(defun expand-tagbody-forms (body start end)
  (do ((clauses nil)
       (clause (list (list start)))
       (forms body (cdr forms)))
      ((null forms)
       (setq clause (append clause (list (list 'go end))))
       (setq clauses (append clauses `(,clause)))
       clauses)
    (let ((form (first forms)))
      (cond
	((atom form)
	 (setq clause (append clause `((go ,form))))
	 (setq clauses (append clauses `(,clause)))
	 (setq clause `((,form))))
	(t
	 (setq clause (append clause `(,form))))))))

(defmacro* tagbody (&body body)
  (let ((pc (gensym))
	(start (gensym))
	(end (gensym))
	(throw-tag (gensym)))
    `(let ((,pc ',start))
      (macrolet ((go (tag)
		   (list 'throw
			 (list 'quote ',throw-tag)
			 (list 'quote tag))))
	(while (not (eq ,pc ',end))
	  (setq ,pc
		(catch ',throw-tag
		  (case ,pc
		    ,@(expand-tagbody-forms body start end))))))
      nil)))

;(defun tagbody-blocks (body start)
;  (do ((n 0)
;       (blocks nil)
;       (block (list start))
;       (forms body (cdr forms)))
;      ((null forms)
;       (setq block (append block (list -1)))
;       (setq blocks (append blocks `(,block)))
;       blocks)
;    (let ((form (first forms)))
;      (cond
;	((atom form)
;	 (incf n)
;	 (setq block (append block `(,n)))
;	 (setq blocks (append blocks `(,block)))
;	 (setq block (list form)))
;	(t
;	 (setq block (append block `(,form))))))))

;(defun tagbody-functions (blocks)
;  (let ((tags (do ((blocks blocks (cdr blocks))
;		   (tags nil)
;		   (n 0))
;		  ((null blocks) tags)
;		(push (cons (pop (car blocks)) n) tags)
;		(incf n)))
;	(catch (gensym)))
;    (mapcar (lambda (block)
;	      `(lambda ()
;		(macrolet ((go (tag)
;			     (list 'throw
;				   (list 'quote ',catch)
;				   (list 'quote (cdr (assq tag ',tags))))))
;		  (catch ',catch
;		    ,@block))))
;	    blocks)))

;(defmacro* tagbody (&body body)
;  (let* ((pc (gensym))
;	 (start (if (atom (first body)) (pop body) (gensym)))
;	 (blocks (tagbody-blocks body start)))
;    `(let ((,pc 0))
;	(while (not (minusp ,pc))
;	  (setq ,pc (funcall (aref (eval-when-compile
;				    (vector ,@(tagbody-functions blocks)))
;				   ,pc)))))))

(defun mapcar2 (fn list)
  (when list
    (cons (funcall fn (first list) (second list))
	  (mapcar2 fn (cddr list)))))

(defun tree-count (object tree) ; &KEY TEST KEY
  (cond
    ((eq object tree)	1)
    ((atom tree)	0)
    (t			(+ (tree-count object (car tree))
			   (tree-count object (cdr tree))))))

(defmacro destructuring-lambda (lambda-list &rest body)
  (with-gensyms (args)
    `(lambda (&rest ,args)
       (destructuring-bind ,lambda-list ,args ,@body))))

(defmacro* define-case (name &key test)
  (setq test (if (and (consp test) (eq (car test) 'function))
		 (cdr test)
		 (cons 'funcall (cdr test))))
  `(progn
     (defmacro ,name (object &rest clauses)
       (with-gensyms (value)
	 (let ((fn ',test))
	   `(let ((,value ,object))
	      (cond
		,@(mapcar (destructuring-lambda ((x &rest forms))
			    `((cl:values (,@fn ,value ',x))
			      (progn ,@forms)))
			  clauses))))))
;;      (defmacro ,(intern (concat "e" (symbol-name name))) (object &rest clauses)
;;        (with-gensyms (value)
;; 	 (let ((,value ,object))
;; 	   `(,name ,value
;; 	      ,@clauses
;; 	      (t (ERROR "No match for ~S in ~S." ,value ',name))))))
     ',name))

(define-case subtypecase :test #'SUBTYPEP)

;; (defmacro with-collector (name &rest body)
;;   (with-gensyms (result end)
;;     `(let* ((,result (list nil))
;; 	    (,end ,result))
;;        (macrolet ((,name (x)
;; 		    (list 'setq ',end (list 'setcdr ',end (list 'list x)))))
;; 	 ,@body
;; 	 (cdr ,result)))))

(defmacro with-collector (name &rest body)
  (with-gensyms (result)
    `(let ((,result nil))
       (macrolet ((,name (x) (list 'push x ',result)))
	 ,@body
	 (nreverse ,result)))))

(defun interned-p (symbol)
  (and (symbolp symbol)
       (eq (intern-soft (symbol-name symbol)) symbol)))
