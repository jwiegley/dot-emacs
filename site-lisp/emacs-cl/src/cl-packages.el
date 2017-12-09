;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 11, Packages.

(IN-PACKAGE "EMACS-CL")

;;; A note about the EMACS-LISP package: This package isn't
;;; implemented the same way all other packages are.  It doesn't have
;;; a hash table or a list of exported symbols.  Instead, symbols are
;;; searched with intern-soft, and all symbols are exported.

(defconst kw:EXTERNAL (keyword "EXTERNAL"))
(defconst kw:INTERNAL (keyword "INTERNAL"))
(defconst kw:INHERITED (keyword "INHERITED"))

;;; The PACKAGE system class is built in.

(defun PACKAGE-NAME (package)
  (aref (FIND-PACKAGE package) 1))

(defun PACKAGE-NICKNAMES (package)
  (aref (FIND-PACKAGE package) 2))

(defun PACKAGE-SHADOWING-SYMBOLS (package)
  (aref (FIND-PACKAGE package) 3))

(defun PACKAGE-USE-LIST (package)
  (aref (FIND-PACKAGE package) 4))

(defun PACKAGE-USED-BY-LIST (package)
  (aref (FIND-PACKAGE package) 5))

(defun package-table (package)
  (aref package 6))

(defun package-exported (package)
  (aref package 7))

(defun PACKAGEP (package)
  (vector-and-typep package 'PACKAGE))

(DEFVAR *all-packages* nil)

(defun* EXPORT (symbols &optional (package-designator *PACKAGE*))
  (let ((package (FIND-PACKAGE package-designator)))
    (do-list-designator (sym symbols (cl:values T))
      (MULTIPLE-VALUE-BIND (s status) (FIND-SYMBOL (SYMBOL-NAME sym) package)
	(cond
	  ((eq status kw:INHERITED)
	   (IMPORT sym package))
	  ((null status)
	   (ERROR 'PACKAGE-ERROR (kw PACKAGE) package))))
      (pushnew sym (aref package 7)))))

(defun FIND-PACKAGE (name)
  (if (PACKAGEP name)
      name
      (let ((string (STRING name)))
	(find-if 
	 (lambda (p)
	   (or (STRING= string (PACKAGE-NAME p))
	       (find string (PACKAGE-NICKNAMES p) :test 'equal)))
	 *all-packages*))))

(cl:defun MAKE-PACKAGE (name &KEY NICKNAMES USE)
  (let ((package (make-vector 8 'PACKAGE))
	(use-packages (mapcar #'FIND-PACKAGE USE)))
    (aset package 1 (STRING name))			;name
    (aset package 2 (mapcar #'STRING NICKNAMES))	;nicknames
    (aset package 3 nil)				;shadowing symbols
    (aset package 4 use-packages)			;use-list
    (aset package 5 nil)				;used-by-list
    (aset package 6 (make-hash-table :test 'equal))	;table
    (aset package 7 nil)				;exported symbols
    (dolist (p use-packages)
      (push package (aref p 5)))
    (push package *all-packages*)
    package))

(defvar *keyword-package*
  (MAKE-PACKAGE "KEYWORD"))
(defvar *emacs-lisp-package*
  (MAKE-PACKAGE "EMACS-LISP" (kw NICKNAMES) '("EL")))
(defvar *emacs-cl-package*
  (MAKE-PACKAGE "EMACS-COMMON-LISP" (kw NICKNAMES) '("EMACS-CL")))
(defvar *mop-package*
  (MAKE-PACKAGE "EMACS-COMMON-LISP-MOP" (kw NICKNAMES) '("MOP")))
(defvar *cl-package*
  (MAKE-PACKAGE "COMMON-LISP" (kw NICKNAMES) '("CL")))
(defvar *cl-user-package*
  (MAKE-PACKAGE "COMMON-LISP-USER"
		(kw NICKNAMES) '("CL-USER") (kw USE) '("CL" "EMACS-CL")))

(defconst not-found (cons nil nil))

(defvar *find-symbol-searched-packages* nil)

(defun* FIND-SYMBOL (string &optional (package-designator *PACKAGE*))
  (let ((package (FIND-PACKAGE package-designator)))
    (when (memq package *find-symbol-searched-packages*)
      (return-from FIND-SYMBOL (cl:values nil nil)))
    (cond
      ((null package)
       (ERROR "Package ~S not found" package-designator))
      ;; Special EMACS-LISP magic: EMACS-LISP doesn't have a separate
      ;; table, use intern-soft to find symbols instead.
      ((eq package *emacs-lisp-package*)
       (let ((symbol (intern-soft string)))
	 (if symbol
	     (progn
	       (unless (SYMBOL-PACKAGE symbol)
		 (setf (SYMBOL-PACKAGE symbol) *emacs-lisp-package*))
	       (cl:values symbol kw:EXTERNAL))
	     (cl:values nil nil))))
      (t
       (let* ((table (package-table package))
	      (symbol (gethash string table not-found)))
	 (if (not (eq symbol not-found))
	     (cl:values symbol
			(if (memq symbol (package-exported package))
			    kw:EXTERNAL
			    kw:INTERNAL))
	     (let ((*find-symbol-searched-packages*
		    (cons package *find-symbol-searched-packages*)))
	       (dolist (p (PACKAGE-USE-LIST package) (cl:values nil nil))
		 (MULTIPLE-VALUE-BIND (symbol found) (FIND-SYMBOL string p)
		   (when (eq found kw:EXTERNAL)
		     (return-from FIND-SYMBOL
		       (cl:values symbol kw:INHERITED))))))))))))

(defun FIND-ALL-SYMBOLS (name)
  (let ((string (STRING name))
	(syms nil))
    (dolist (p *all-packages* (cl:values syms))
      (MULTIPLE-VALUE-BIND (sym status) (FIND-SYMBOL string p)
	(if (or (eq status :internal) (eq status kw:EXTERNAL))
	    (push sym syms))))))

(defun* IMPORT (symbols &optional (package-designator *PACKAGE*))
  (let ((package (FIND-PACKAGE package-designator)))
    (do-list-designator (symbol symbols (cl:values T))
      (MULTIPLE-VALUE-BIND (sym found)
	  (FIND-SYMBOL (SYMBOL-NAME symbol) package)
	(when (and found (not (eq sym symbol)))
	  (ERROR "Importing ~S into ~S clash with existing symbol"
		 sym package)))
      (setf (gethash (SYMBOL-NAME symbol) (package-table package)) symbol)
      (when (null (SYMBOL-PACKAGE symbol))
	(setf (SYMBOL-PACKAGE symbol) package)))))

(defun LIST-ALL-PACKAGES ()
  (copy-list *all-packages*))

(defun RENAME-PACKAGE (package-designator name &optional new-nicknames)
  (let ((package (FIND-PACKAGE package-designator)))
    (aset package 1 (if (PACKAGEP name)
			(PACKAGE-NAME name)
			(STRING name)))
    (aset package 2 (mapcar #'STRING new-nicknames))))

(defun* SHADOW (symbol-names &optional (package-designator *PACKAGE*))
  (let ((package (FIND-PACKAGE package-designator)))
    (do-list-designator (name symbol-names (cl:values T))
      (setq name (STRING name))
      (MULTIPLE-VALUE-BIND (sym status) (FIND-SYMBOL name package)
	(when (or (null status) (eq status kw:INHERITED))
	  (setq sym (INTERN name package)))
	(pushnew sym (aref package 3))))))

(defun* SHADOWING-IMPORT (symbols &optional (package-designator *PACKAGE*))
  (let ((package (FIND-PACKAGE package-designator)))
    (do-list-designator (symbol symbols (cl:values T))
      (MULTIPLE-VALUE-BIND (sym found)
	  (FIND-SYMBOL (SYMBOL-NAME symbol) package)
	(when found
	  (UNINTERN sym package)))
      (setf (gethash (SYMBOL-NAME symbol) (package-table package)) symbol)
      (when (null (SYMBOL-PACKAGE symbol))
	(setf (SYMBOL-PACKAGE symbol) package)))))

(defun DELETE-PACKAGE (package-designator)
  (let ((package (FIND-PACKAGE package-designator)))
    (if (null (aref package 1))
	nil
	(let ((package (FIND-PACKAGE package-designator)))
	  (unless package
	    (ERROR "Package ~S not found" package-designator))
	  (when (PACKAGE-USED-BY-LIST package)
	    (ERROR 'PACKAGE-ERROR))
	  (dolist (p (PACKAGE-USE-LIST package))
	    (aset p 5 (delete package (PACKAGE-USED-BY-LIST p))))
	  (setq *all-packages* (delete package *all-packages*))
	  (aset package 1 nil)
	  T))))

(defun package-symbols (package types)
  (unless (null package)
    (let ((result nil))
      (maphash (lambda (ignore symbol)
		 (MULTIPLE-VALUE-BIND (sym status)
		     (FIND-SYMBOL (SYMBOL-NAME symbol) package)
		   (when (and status (member status types))
		     (push (cons sym status) result))))
	       (package-table package))
      (when (memq kw:INHERITED types)
	(dolist (p (PACKAGE-USE-LIST package))
	  (dolist (s (package-exported p))
	    (push (cons s kw:INHERITED) result))))
      result)))

(cl:defmacro WITH-PACKAGE-ITERATOR ((name packages &rest types) &body body)
  (with-gensyms (p s)
    `(LET* ((,p (MAPCAR (FUNCTION FIND-PACKAGE) (ensure-list ,packages)))
	    (,s (package-symbols (CAR ,p) (QUOTE ,types))))
       (MACROLET ((,name ()
		    (QUOTE
		      (IF (AND (NULL ,s) (NULL (CDR ,p)))
			  nil
			  (PROGN
			    (WHEN (NULL ,s)
			      (SETQ ,p (CDR ,p))
			      (SETQ ,s (package-symbols (CAR ,p)
							(QUOTE ,types))))
			    (LET ((cons (POP ,s)))
			      (cl:values T
					 (CAR cons) (CDR cons) (CAR ,p))))))))
	  ,@body))))

(cl:defun UNEXPORT (symbols &OPTIONAL (package-designator *PACKAGE*))
  (let ((package (FIND-PACKAGE package-designator)))
    (do-list-designator (symbol symbols)
      (MULTIPLE-VALUE-BIND (sym found)
	  (FIND-SYMBOL (symbol-name symbol) package)
	(if (and found (eq sym symbol))
	    (aset package 7 (delete symbol (aref package 7)))
	    (ERROR 'PACKAGE-ERROR (kw PACKAGE) package)))))
  (cl:values T))

(cl:defun UNINTERN (symbol &OPTIONAL (package-designator *PACKAGE*))
  (let ((package (FIND-PACKAGE package-designator)))
    (when (eq (SYMBOL-PACKAGE symbol) package)
      (setf (SYMBOL-PACKAGE symbol) nil))
    (let* ((table (package-table package))
	   (name (symbol-name symbol))
	   (sym (gethash name table not-found)))
      (unless (eq sym not-found)
	(remhash name table)))
    (aset package 3 (delete symbol (aref package 3)))
    (aset package 7 (delete symbol (aref package 7))))
  'T)

;;; Emacs' load function doesn't restore *PACKAGE* after loading a file.
; (defmacro IN-PACKAGE (package)
;   `(eval-when (:compile-toplevel :load-toplevel :execute)
;     (setq *PACKAGE* (FIND-PACKAGE ,package))))

(cl:defmacro IN-PACKAGE (package)
  `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
     (LET ((p (FIND-PACKAGE (QUOTE ,package))))
       (IF p
	   (SETQ *PACKAGE* p)
	   (ERROR (QUOTE PACKAGE-ERROR) ,(kw PACKAGE) (QUOTE ,package))))))

(cl:defun UNUSE-PACKAGE (packages-to-unuse &OPTIONAL (package *PACKAGE*))
  (let ((package (FIND-PACKAGE package)))
    (do-list-designator (p packages-to-unuse)
      (let ((p (FIND-PACKAGE p)))
	(aset package 4 (delete p (PACKAGE-USE-LIST package)))
	(aset p 5 (delete package (PACKAGE-USED-BY-LIST p))))))
  T)

(cl:defun USE-PACKAGE (packages-to-use &OPTIONAL (package *PACKAGE*))
  (let ((package (FIND-PACKAGE package)))
    (do-list-designator (p packages-to-use)
      (pushnew (FIND-PACKAGE p) (aref package 4))))
  T)

(cl:defmacro DEFPACKAGE (name &rest options)
  (let ((nicknames nil)
	(documentation nil)
	(use-list nil)
	(shadow-list nil)
	(shadowing-import nil)
	(import-list nil)
	(intern-list nil)
	(export-list nil)
	(doc nil))
    (dolist (option options)
      (let ((keyword (first option)))
	(cond
	  ((eq keyword (kw NICKNAMES))
	   (dolist (i (rest option))
	     (push (STRING i) nicknames)))
	  ((eq keyword (kw DOCUMENTATION))
	   (setq doc (second option)))
	  ((eq keyword (kw SHADOW))
	   (dolist (i (rest option))
	     (push (STRING i) shadow-list)))
	  ((eq keyword (kw SHADOWING-IMPORT-FROM))
	   (push (mapcar #'STRING (rest option)) shadowing-import))
	  ((eq keyword (kw USE))
	   (dolist (i (rest option))
	     (push (STRING i) use-list)))
	  ((eq keyword (kw IMPORT-FROM))
	   (push (mapcar #'STRING (rest option)) shadowing-import))
	  ((eq keyword (kw INTERN))
	   (dolist (i (rest option))
	     (push (STRING i) intern-list)))
	  ((eq keyword (kw EXPORT))
	   (dolist (i (rest option))
	     (push (STRING i) export-list)))
	  ((eq keyword (kw SIZE))
	   nil)
	  (t
	   (ERROR "Unknown DEFPACKAGE option: ~S" option)))))
    (with-gensyms (x package)
      `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
	(%defpackage
	 ,(STRING name)
	 (QUOTE ,nicknames)
	 (QUOTE ,shadow-list)
	 (QUOTE ,shadowing-import)
	 (QUOTE ,use-list)
	 (QUOTE ,import-list)
	 (QUOTE ,intern-list)
	 (QUOTE ,export-list))))))

(defun %defpackage (name nicknames shadow-list shadowing-import
		    use-list import-list intern-list export-list)
  (let ((package (FIND-PACKAGE name)))
    (if package
	(aset package 2 (mapcar #'STRING nicknames))
	(setq package (MAKE-PACKAGE name (kw NICKNAMES) nicknames)))
    (SHADOW shadow-list package)
    (dolist (list shadowing-import)
      (let ((p (FIND-PACKAGE (first list))))
	(dolist (name (rest list))
	  (SHADOWING-IMPORT (FIND-SYMBOL name p) package))))
    (dolist (p use-list)
      (USE-PACKAGE p package))
    (dolist (list import-list)
      (let ((p (FIND-PACKAGE (first list))))
	(dolist (name (rest list))
	  (IMPORT (FIND-SYMBOL name p) package))))
    (dolist (x intern-list)
      (INTERN x package))
    (dolist (name export-list)
      (EXPORT (INTERN name package) package))
    package))

(defun el-maphash (fn hash)
  (maphash (lambda (k v) (FUNCALL fn k v)) hash))

(defmacro* DO-SYMBOLS ((var &optional package result) &body body)
  (with-gensyms (p1 p2 p3 ignore)
    `(let* ((,p1 ,package)
	    (,p2 (if ,p1 (FIND-PACKAGE ,p1) *PACKAGE*)))
       (dolist (,p3 (cons ,p2 (PACKAGE-USE-LIST ,p2)))
	 (el-maphash (lambda (,ignore ,var) ,@body)
		     (package-table ,p3)))
       ,result)))

(cl:defmacro DO-SYMBOLS ((var &optional package result) &body body)
  (with-gensyms (p1 p2 p3 ignore)
    `(LET* ((,p1 ,package)
	    (,p2 (IF ,p1 (FIND-PACKAGE ,p1) *PACKAGE*)))
       (DOLIST (,p3 (CONS ,p2 (PACKAGE-USE-LIST ,p2)))
	 (el-maphash (LAMBDA (,ignore ,var) ,@body)
		     (package-table ,p3)))
       ,result)))

(cl:defmacro DO-EXTERNAL-SYMBOLS ((var &optional package result) &body body)
  (with-gensyms (p1 p2)
    `(LET* ((,p1 ,package)
	    (,p2 (IF ,p1 (FIND-PACKAGE ,p1) *PACKAGE*)))
       (DOLIST (,var (aref ,p2 7) ,result)
	 ,@body))))

(cl:defmacro DO-ALL-SYMBOLS ((var &optional result) &body body)
  (with-gensyms (p ignore)
    `(DOLIST (,p *all-packages* ,result)
       (el-maphash (LAMBDA (,ignore ,var) ,@body)
	           (package-table ,p)))))

(cl:defun INTERN (name &OPTIONAL (package-designator *PACKAGE*))
  (let ((package (FIND-PACKAGE package-designator)))
    (when (null package)
      (ERROR "Package ~S not found" package-designator))
    (MULTIPLE-VALUE-BIND (symbol found) (FIND-SYMBOL name package)
      (if found
	  (cl:values symbol found)
	  (let ((symbol (if (eq package *emacs-lisp-package*)
			    (intern name)
			    (make-symbol name))))
	    (setf (SYMBOL-PACKAGE symbol) package)
	    (unless (eq package *emacs-lisp-package*)
	      (setf (gethash name (package-table package)) symbol))
	    (when (eq package *keyword-package*)
	      (set symbol symbol)
	      (pushnew symbol (aref package 7)))
	    (cl:values symbol nil))))))

(DEFVAR *PACKAGE* *cl-user-package*)

;;; PACKAGE-ERROR and PACKAGE-ERROR-PACKAGE are defined in cl-conditions.el.



;;; Bootstrap magic: take the list of symbols created by the old
;;; keyword function, and import them into the KEYWORD package.
(dolist (sym *initial-keywords*)
  (IMPORT sym *keyword-package*)
  (EXPORT sym *keyword-package*))

;;; Redefine the keyword function (initially defined in utils.el).
(defun keyword (name)
  (cl:values (INTERN name *keyword-package*)))
