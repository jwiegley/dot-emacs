;;;; -*- lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.

(defpackage :emacs-cl-tests (:use "CL"))
(in-package :emacs-cl-tests)

(setq *readtable* (copy-readtable))
(defconstant +true+ (make-symbol "TRUE"))
(set-dispatch-macro-character #\# #\t (constantly +true+))

(defparameter *pass* 0)
(defparameter *fail-eval* 0)
(defparameter *fail-comp* 0)
(defparameter *fail-exe* 0)

(defvar *emacs-version*
  (let ((n (position #\. el:|emacs-version|)))
    (values (read-from-string (subseq el:|emacs-version| 0 n)))))

(defmacro ignore-all-errors (form)
  `(ignore-errors (ignore-elisp-error (lambda () ,form))))

(defmacro el-defun (symbol string)
  `(setf (symbol-function ',symbol)
         (el:|byte-compile| (car (el:|read-from-string| ,string)))))

(el-defun ignore-elisp-error
  "(lambda (fn)
     (condition-case cond (FUNCALL fn)
       (error nil)))")

(defun deftest-equal (x y)
  (cond
    ((eq x +true+)
     y)
    ((eq y +true+)
     x)
    ((and (consp x) (consp y))
     (and (deftest-equal (car x) (car y))
	  (deftest-equal (cdr x) (cdr y))))
    ((and (vectorp x) (vectorp y))
     (every #'deftest-equal x y))
    (t
     (equal x y))))

(defmacro deftest (name form result)
  `(try-test ,(string name) ',form ',result))

(defun try-test (name form result)
  (let ((pass t))
    (format t "~&Test ~A: " name)
    (write-string "                                        " nil
		  :start (length name))
    (if (deftest-equal (ignore-errors (eval form)) result)
	(incf *pass*)
	(progn
	  (princ "FAIL evaluation ")
	  (incf *fail-eval*)
	  (setq pass nil)))
    ;;(format t "~& -> ~A <-~%" (el:|compile2| `(lambda () ,form)))
    (let ((fn (ignore-all-errors (compile nil `(lambda () ,form)))))
      (cond
	(fn
	 (incf *pass*)
	 (if (deftest-equal (ignore-errors (funcall fn)) result)
	     (incf *pass*)
	     (progn
	       (incf *fail-exe*)
	       (princ "FAIL execution")
	       (setq pass nil))))
	(t
	 (incf *fail-comp*)
	 (princ "FAIL compilation ")
	 (setq pass nil))))
    (when pass
      (princ "pass"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest "bignum arithmetic"
  (list
   (+ 67108864 67108864)
   (+ 134217727 1)
   (+ -134217728 -1)
   (+ -134217728 -134217728)
   (+ 268435455 268435455)
   (+ -268435456 -268435456)
   (+ 536870912 -268435456)
   (+ -268435456 536870912)
   (+ 268435456 -536870912)
   (+ -536870912 268435456)
   (+ 536870914 -536870913)
   (+ 536870914 -536870915)
   (+ 1824724491 4579695115)
   (+ 3330866858093 8219800381946)
   (+ 671088640 -1)
   (+ 26843545600000000 26843545600000000)
   (+ 27658482871109005 27658482871109005))
  (134217728
   134217728
   -134217729
   -268435456
   536870910
   -536870912
   268435456
   268435456
   -268435456
   -268435456
   1
   -1
   6404419606
   11550667240039
   671088639
   53687091200000000
   55316965742218010))

(deftest "SETF CADR"
  (let ((x (list 1 2 3)))
    (setf (cadr x) 42)
    x)
  (1 42 3))

(deftest "#- at end of list"
  (read-from-string "(#-emacs-cl 1)")
  nil)

(deftest "#| |# at end of list"
  (read-from-string "(1 #| 2 |#)")
  (1))

(deftest "reading dotted lists"
  (let ((x (read-from-string "(1 . 2)")))
    (cons (car x) (cdr x)))
  (1 . 2))

(deftest "binding global special variable"
  (progn
    (makunbound '*foo*)
    (defvar *foo* 10)
    (defun foo () *foo*)
    (list
     (let ((*foo* 20)) (foo))
     (foo)))
  (20 10))

(deftest "setting global special variable"
  (progn
    (makunbound '*foo*)
    (defvar *foo*)
    (defun foo () *foo*)
    (setq *foo* 30)
    (foo))
  30)

;;; XEmacs' byte-compiler is known to fail on this.
(deftest "binding local special variable"
  (progn
    (defun bar () (declare (special %bar%)) %bar%)
    (let ((%bar% 99)) (declare (special %bar%)) (bar)))
  99)

(deftest "passing &optional and &key arguments"
  (progn
    (defun foo (a &optional b (c 100) &key d (e 101))
      (list a b c d e))
    (append
     (foo 1)
     (foo 1 2)
     (foo 1 2 3)
     (foo 1 2 3 :d 4)
     (foo 1 2 3 :e 5 :d 4)))
  (1 nil 100 nil 101
   1  2  100 nil 101
   1  2   3  nil 101
   1  2   3   4  101
   1  2   3   4   5))

(deftest "passing &rest and &key arguments"
  (progn
    (defun foo (&rest a) a)
    (defun bar (&rest a &key b c) (list a b c))
    (list
     (foo)
     (foo 1)
     (foo 1 2 3)
     (bar)
     (bar :b 1)
     (bar :c 1 :b 2)))
  (()
   (1)
   (1 2 3)
   (() nil nil)
   ((:b 1) 1 nil)
   ((:c 1 :b 2) 2 1)))

(deftest "returning the right number of multiple values"
  (list
   (length (multiple-value-list (1+ (values 1 2))))
   (length (multiple-value-list (values (progn 1) (progn 2))))
   (length (multiple-value-list (values (values 1 2))))
   (length (multiple-value-list (unwind-protect (values 1 2) (values 1 2 3)))))
  (1 2 1 2))

(deftest "backquoting"
  (let ((a 1) (b '(2 3)) (c '(4 5)))
    (list `(a b c)
	  `(a ,b ,c)
	  `(a ,b ,@c)
	  `(a ,@b ,c)
	  `(a ,@b ,@c)
	  `(a `(b ,',a c) d)))
  ((a b c)
   (a (2 3) (4 5))
   (a (2 3) 4 5)
   (a 2 3 (4 5))
   (a 2 3 4 5)
   (a '(b 1 c) d)))

(deftest "reading character constants"
  (concatenate 'string '(#\A #\Space #\( #\) #\* #\# #\\ #\"))
  "A ()*#\\\"")

(deftest "suppressing undefined reader macros"
  (read-from-string "#-emacs-cl #% 1 2")
  2)

(unless (el:|featurep| 'el:|xemacs|)
  (deftest "accessing hash tables"
    (let ((eq-ht (make-hash-table :test #'eq))
	  (eql-ht (make-hash-table))
	  (equal-ht (make-hash-table :test #'equal)))
      ;;(equalp-ht (make-hash-table :test #'equalp)))
      (setf (gethash 'foo eq-ht) 1)
      (setf (gethash #\A eql-ht) 2)
      (setf (gethash (list 1 2 3) equal-ht) 3)
      ;;(setf (gethash "foo" equalp-ht) 4)
      (list (gethash 'foo eq-ht)
	    (gethash #\A eql-ht)
	    (gethash (list 1 2 3) equal-ht)))
      ;;(gethash "FOO" equalp-ht)))
    (1 2 3))) ;4)))

(deftest "declare in do and dolist"
  (list
   (do ((i 0 (1+ i)))
       ((>= i 10)
	42)
     (declare (fixnum i)))
   (dolist (x '(1 2 3) 17)
     (declare (fixnum x))
     x))
  (42 17))

(defun compose (fn1 fn2)
  (lambda (&rest args)
    (funcall fn1 (apply fn2 args))))

(defun curry (fn &rest args1)
  (lambda (&rest args2)
    (apply fn (append args1 args2))))

(defun rcurry (fn &rest args2)
  (lambda (&rest args1)
    (apply fn (append args1 args2))))

(deftest "merging pathname directories"
  ;;(pathname-directory (merge-pathnames "a/b/c.d" "/x/y/z"))
  (mapcar (compose #'pathname-directory (curry #'apply #'merge-pathnames))
	  '(("a.b"     "x/y/z")
	    ("a/b/c.d" "/x/y/z")))
  ((:relative "x" "y")
   (:absolute "x" "y" "a" "b")))

(deftest "butlast"
  (list (butlast (list 1 2))
	(butlast (list 1))
	(butlast nil))
  ((1) nil nil))

(deftest "case"
  (list (case 'white
	  (black 'red)
	  (white 'green))
	(case 'bar
	  ((1 2 3) 42)
	  ((foo bar baz) 17)))
  (green 17))

(deftest "remove-if-not"
  (remove-if-not #'oddp '(1 2 3 4 5 6))
  (1 3 5))

(deftest "destructuring-bind"
  (list
   (destructuring-bind (&rest a) nil
     a)
   (destructuring-bind (a &optional b (c 42 d) &rest e) '(1 2 3 4 5)
     (list a b c d e))
   (destructuring-bind (a &optional b (c 42 d) &body e) '(1)
     (list a b c d e))
   (destructuring-bind (foo &key bar baz) '(1 :bar 2 :baz 3)
     (list baz bar foo))
   (destructuring-bind (&rest foo &key bar baz) '(:bar 2 :baz 3)
     (list foo bar baz))
   (destructuring-bind (&key (foo 10) (bar 20)) '(:foo 30)
     (list foo bar))
   (destructuring-bind (&key (foo 10 foop) (bar 20 barp)) '(:bar 30)
     (list foo foop bar barp))
   (destructuring-bind (&key ((foo bar))) '(foo 42) bar)
   (destructuring-bind (x . y) '(1 2 3) (list x y))
   (destructuring-bind (&whole w) () w)
   (destructuring-bind (&whole w) 42  w)
   (destructuring-bind (&whole w) '(42)  w)
   (destructuring-bind (&whole w &rest x) () (list w x))
   (destructuring-bind (&whole w x) '(42) (list w x)))
  (nil
   (1 2 3 t (4 5))
   (1 nil 42 nil nil)
   (3 2 1)
   ((:bar 2 :baz 3) 2 3)
   (30 20)
   (10 nil 30 t)
   42
   (1 (2 3))
   ()
   42
   (42)
   (() ())
   ((42) 42)))

(deftest "butlast"
  (let (lst foo)
    (list
     (setq lst '(1 2 3 4 5 6 7 8 9))
     (butlast lst)
     (butlast lst 5)
     (butlast lst (+ 5 5))
     lst
     (progn
       (setq lst (list 1 2 3 4 5 6 7 8 9))
       (nbutlast lst 3))
     lst
     (nbutlast lst 99)
     lst
     (butlast '(a b c d))
     (butlast '((a b) (c d)))
     (butlast '(a))
     (butlast nil)
     (setq foo (list 'a 'b 'c 'd))
     (progn
       (setq foo (list 'a 'b 'c 'd))
       (nbutlast foo))
     foo
     (nbutlast (list 'a))
     (nbutlast '())
     (butlast '(1 2 3 . 4) 0)
     (butlast '(1 2 3 . 4) 1)
     (butlast '(1 2 3 . 4) 2)))
  ((1 2 3 4 5 6 7 8 9)
   (1 2 3 4 5 6 7 8)
   (1 2 3 4)
   nil
   (1 2 3 4 5 6 7 8 9)
   (1 2 3 4 5 6)
   (1 2 3 4 5 6)
   nil
   (1 2 3 4 5 6)
   (a b c)
   ((a b))
   nil
   nil
   (a b c d)
   (a b c)
   (a b c)
   nil
   nil
   (1 2 3)
   (1 2)
   (1)))

(deftest "last"
  (let (x)
    (list
     (last nil)
     (last '(1 2 3))
     (last '(1 2 . 3))
     (setq x (list 'a 'b 'c 'd))
     (last x)
     (progn
       (setq x (list 'a 'b 'c 'd))
       (rplacd (last x) (list 'e 'f))
       x)
     (last x)
     (last '(a b c))
     (last '(a b c) 0)
     (last '(a b c) 1)
     (last '(a b c) 2)
     (last '(a b c) 3)
     (last '(a b c) 4)
     (last '(a . b) 0)
     (last '(a . b) 1)
     (last '(a . b) 2)))
  (nil
   (3)
   (2 . 3)
   (a b c d)
   (d)
   (a b c d e f)
   (f)
   (c)
   ()
   (c)
   (b c)
   (a b c)
   (a b c)
   b
   (a . b)
   (a . b)))

(deftest "ldiff and tailp"
  (let ((lists '#((a b c) (a b c . d)))
	(result nil))
    (dotimes (i (length lists) (nreverse result))
      (let ((list (aref lists i)))
	(let ((objects (vector list (cddr list) (copy-list (cddr list))
			       '(f g h) '() 'd 'x)))
	  (dotimes (j (length objects))
	    (let ((object (aref objects j)))
	      (push (tailp object list) result)
	      (push (ldiff list object) result)))))))
  (#t	nil
   #t	(a b)
   nil	(a b c)
   nil	(a b c)
   #t	(a b c)
   nil	(a b c)
   nil	(a b c)
   #t	nil
   #t	(a b)
   nil	(a b c . d)
   nil	(a b c . d)
   nil	(a b c . d)
   #t	(a b c)
   nil	(a b c . d)))

(deftest "every, some, notevery, and notany"
  (list
   (every #'characterp "abc")
   (some #'= '(1 2 3 4 5) '(5 4 3 2 1))
   (notevery #'< '(1 2 3 4) '(5 6 7 8) '(9 10 11 12))
   (notany #'> '(1 2 3 4) '(5 6 7 8) '(9 10 11 12)))
  (#t #t nil #t))

(deftest "printing a symbol named ||"
  (prin1-to-string '||)
  "||")

(deftest "reading escaped gensyms"
  (princ-to-string
   (list (read-from-string "#:|foo|") (read-from-string "#:||")))
  "(foo )")

(deftest "nested macrolets"
  (macrolet ((foo () ''win))
    (macrolet ((foo () ''lose)) nil)
    (foo))
  win)

(deftest "reading a zero length bit vector"
  (prin1-to-string (read-from-string "#*"))
  "#*")

(deftest "array-dimensions"
  (array-dimensions "abc")
  (3))

(deftest "multiple-value-setq"
  (let (x y z)
    (multiple-value-setq (x y z) (values 1 2 3))
    (list x y z))
  (1 2 3))

(unless (el:|featurep| 'el:|xemacs|)
  (deftest "rational"
    (rational 8.0e20)
    800000000000000000000))

(unless (el:|featurep| 'el:|xemacs|)
  (deftest "truncate"
    (truncate 5075863620026369.0)
    5075863620026369))

(deftest "floor and ceiling"
  (list (floor -1/2)
	(floor 1/2)
	(ceiling -1/2)
	(ceiling 1/2))
  (-1 0 0 1))

(deftest "plusp and minusp"
  (list (plusp 1/2)
	(plusp 100000000000000000/3)
	(plusp -100000000000000000/3)
	(minusp 100000000000000000/3)
	(minusp -100000000000000000/3))
  (#t #t nil nil #t))

(deftest "logand, logior, and logxor"
  (list
   (logand 8236387328762348762138787623487 1234978634857634056)
   (logior 8236387328762348762138787623487 1234978634857634056)
   (logxor 8236387328762348762138787623487 1234978634857634056))
  (72761281498746888
   8236387328763510979492146510655
   8236387328763438218210647763767))
  
(deftest "typep"
  (list
   (typep 42 '(unsigned-byte 9))

   (typep #() 'vector)
   (typep #() '(vector *))
   (typep #() '(vector t))
   (typep #() '(vector bit))
   (typep #() '(vector * 0))
   (typep #() '(vector * 1))

   (typep #() 'array)
   (typep #() '(array *))
   (typep #() '(array * *))
   (typep #() '(array * 1))
   (typep #() '(array * (*)))
   (typep #() '(array * (0)))
   (typep #() '(array * (1))))
  (#t
   #t #t #t nil #t nil
   #t #t #t #t #t #t nil))

(deftest "expt"
  (expt 1/2 -1)
  2)

(deftest "length"
  (length (make-array 3 :adjustable t))
  3)

(deftest "compile-file"
  (progn
    (with-open-file (f "temporary.lisp" :direction :output)
      (format f "(defun foo () #*11111111111010110101)~@
                 (defvar *bar* '#1=(1 . 1))~@
		 (defun bar () (let ((*bar* t)) (foo)))~@
		 (defvar *baz* #'foo)"))
    (let ((*compile-print* nil)
	  (*compile-verbose* nil)
	  (*load-print* nil)
	  (*load-verbose* nil))
      (compile-file "temporary.lisp")
      (load "temporary.elc")
      (bar))
    (mapc #'delete-file '("temporary.lisp" "temporary.elc"))
    (foo))
  #*11111111111010110101)

(deftest "symbol-macrolet"
  (symbol-macrolet ((x y))
    (let ((y nil))
      (setf x 42)
      y))
  42)

(deftest "not and null"
  (list (not nil) (null nil))
  (t t))

(deftest "nested handler-bind"
  (block foo
    (handler-bind ((error (lambda (c) (return-from foo 'lose))))
      (handler-bind ((error (lambda (c) (return-from foo 'win))))
	(error "error"))))
  win)

(deftest "load-time-value"
  (list (load-time-value (list 1 2 3))
	(progn
	  (fmakunbound '*value*)
	  (with-open-file (f "temporary.lisp" :direction :output)
	    (format f "(defparameter *value* (list 1 2 3))~@
                       (defparameter *load-time-value*~@
				     (load-time-value *value*))"))
	  (let ((*compile-print* nil)
		(*compile-verbose* nil)
		(*load-print* nil)
		(*load-verbose* nil))
	    (compile-file "temporary.lisp")
	    (load "temporary.elc"))
	  *load-time-value*))
  ((1 2 3)
   (1 2 3)))

(deftest "complement"
  (list (funcall (complement (lambda () t)))
	(funcall (complement #'zerop) 0)
	(funcall (complement '=) 1 1))
  (nil nil nil))

(deftest "defclass"
  (let ((foo-class (defclass foo () ()))
	(bar-class (defclass bar (foo) () ()))
	(foo-instance (make-instance 'foo))
	(bar-instance (make-instance 'bar)))
    (and (typep foo-class t)
	 (typep foo-class 'standard-class)
	 (typep foo-instance t)
	 (typep foo-instance 'standard-object)
	 (typep foo-instance 'foo)
	 (typep bar-class t)
	 (typep bar-class 'standard-class)
	 (typep bar-instance t)
	 (typep bar-instance 'standard-object)
	 (typep bar-instance 'foo)
	 (typep bar-instance 'bar)))
  #t)

(deftest "slot-value"
  (let ((test-class (defclass test () (x y)))
	(test-instance (make-instance 'test)))
    (and (slot-exists-p test-instance 'x)
	 (slot-exists-p test-instance 'y)
	 (not (slot-exists-p test-instance 'z))
	 (not (slot-boundp test-instance 'x))
	 (not (slot-boundp test-instance 'y))
	 (setf (slot-value test-instance 'x) 42)
	 (slot-boundp test-instance 'x)
	 (not (slot-boundp test-instance 'y))
	 (eql (slot-value test-instance 'x) 42)
	 (slot-makunbound test-instance 'x)
	 (not (slot-boundp test-instance 'x))
	 (not (slot-boundp test-instance 'y))))
  t)

(deftest "find-symbol"
  (let* ((foo-package (make-package "foo" :use ()))
	 (bar-package (make-package "bar" :use ())))
    (use-package foo-package bar-package)
    (use-package bar-package foo-package)
    (prog1 (find-symbol "foo" foo-package)
      (unuse-package foo-package bar-package)
      (delete-package foo-package)
      (delete-package bar-package)))
  nil)

(deftest "shadowing-import"
  (let* ((foo-package (make-package "foo" :use ()))
	 (bar-package (make-package "bar" :use ()))
	 (baz-package (make-package "baz" :use '("foo")))
	 (foo-x (intern "x" foo-package))
	 (bar-x (intern "x" bar-package)))
    (shadowing-import foo-x bar-package)
    (shadowing-import foo-x baz-package)
    (prog1 (and (eq (find-symbol "x" "foo") (find-symbol "x" "bar"))
		(eq (find-symbol "x" "foo") (find-symbol "x" "baz")))
      (delete-package baz-package)
      (delete-package bar-package)
      (delete-package foo-package)))
  #t)

(deftest "defconstant"
  (progn
    (makunbound '+foo+)
    (fmakunbound 'foo)
    (defconstant +foo+ '(1 . 2))
    (defun foo () +foo+)
    (foo))
  (1 . 2))

(deftest "parsing function bodies"
  (macrolet
      ((test-bodies ()
	 `(list
	   ,@(let ((result nil))
	       (dolist (decl1 '(nil ((declare (optimize speed)))))
		 (dolist (doc '(nil ("doc")))
		   (dolist (decl2 '(nil ((declare (special *package*)))))
		     (dolist (form '(nil ("str") (42)))
		       (push `(let ((fn (lambda ()
					  ,@decl1 ,@doc ,@decl2 ,@form)))
			       (list (funcall fn) (documentation fn t)))
			     result)))))
	       (nreverse result)))))
    (test-bodies))
  ((nil   nil)   ("str" nil)   (42 nil)
   (nil   nil)   ("str" nil)   (42 nil)
   ("doc" nil)   ("str" "doc") (42 "doc")
   (nil   "doc") ("str" "doc") (42 "doc")
   (nil   nil)   ("str" nil)   (42 nil)
   (nil   nil)   ("str" nil)   (42 nil)
   ("doc" nil)   ("str" "doc") (42 "doc")
   (nil   "doc") ("str" "doc") (42 "doc")))

(deftest "coerce"
  (let ((list '(#\a #\b))
	(vector #(#\c #\d))
	(string "ef")
	(result nil))
    (dolist (object (list list vector string))
      (dolist (type '(list vector simple-vector string simple-string))
	(push (coerce object type) result)))
    (nreverse result))
  ((#\a #\b) #(#\a #\b) #(#\a #\b) "ab" "ab"
   (#\c #\d) #(#\c #\d) #(#\c #\d) "cd" "cd"
   (#\e #\f) "ef" "ef" "ef" "ef"))

(deftest "make-sequence"
  (list (make-sequence 'list 2 :initial-element t)
	(make-sequence 'simple-bit-vector 2 :initial-element 1)
	(make-sequence 'simple-string 2 :initial-element #\a)
	(make-sequence 'simple-vector 2 :initial-element t))
  ((t t) #*11 "aa" #(t t)))

(deftest "concatenate"
  (let ((list '(#\a #\b))
	(vector #(#\c #\d))
	(string "ef")
	(result nil))
    (dolist (type '(list vector simple-vector string simple-string))
      (push (concatenate type list vector string) result))
    (nreverse result))
  ((#\a #\b #\c #\d #\e #\f)
   #(#\a #\b #\c #\d #\e #\f)
   #(#\a #\b #\c #\d #\e #\f)
   "abcdef"
   "abcdef"))

(deftest "subtypep"
  (list
   ;; These should be subtypes.
   (loop for (t1 t2)
	 on '((simple-vector 3)		sequence
	      integer			number
	      (integer 1 3)		number
	      null			symbol)
	 by #'cddr
	 unless (subtypep t1 t2) collect (list t1 t2))
   ;; These should not be subtypes.
   (loop for (t1 t2)
	 on '(simple-vector		string)
	 by #'cddr
	 when (subtypep t1 t2) collect (list t1 t2))
   ;; These should be type-equal.
   (loop for (t1 t2)
	 on '((or fixnum bignum)	integer
	      (or integer ratio)	rational
	      (or rational float)	real
	      (or real complex)		number
	      (or null cons)		list
	      (or list vector)		sequence
	      (array * (*))		vector
	      (simple-array t (3 4))	(and (array t (3 *))
					     (simple-array * (* 4))))
	 by #'cddr
	 unless (and (subtypep t1 t2) (subtypep t2 t1))
	 collect (list t1 t2)))
  (nil nil nil))

(deftest "flet and labels"
  (macrolet
      ((test (flet)
	 `(,flet ((foo () 42))
	    (list (functionp #'foo)
	          (foo)))))
    (list
     (test flet)
     (test labels)
     (labels ((foo () #'foo))
       (eq #'foo (foo)))))
  ((#t 42)
   (#t 42)
   #t))

(defmacro foo1 (&whole w) (cdr w))
(defmacro foo2 (&whole w x) `(cons ',x ',w))
(defmacro foo3 (&rest x) `',x)

(deftest "defmacro"
  (list
   (foo1 . 42)
   (foo2 42)
   (foo3 . 42)
   (foo3 42))
  (42 (42 foo2 42) 42 (42)))

(define-compiler-macro bar1 (&whole w) `',w)
(define-compiler-macro bar2 (&whole w x) `'(,x . ,w))
(define-compiler-macro bar3 (&rest x) `',x)
(define-compiler-macro (setf bar4) (&whole w) `',w)

(deftest "define-compiler-macro"
  (funcall (compile nil '(lambda ()
			  (list
			   (bar1 42)
			   (funcall #'bar1 42)
			   (bar2 42)
			   (funcall 'bar2 42)
			   (bar3 42)
			   (funcall #'bar3 42)
			   (funcall #'(setf bar4) 42)))))
  ((bar1 42)		(funcall #'bar1 42)
   (42 bar2 42)		(42 funcall 'bar2 42)
   (42)			(42)
   (funcall #'(setf bar4) 42)))

(deftest "string-left-trim and string-right-trim"
  (list
   (string-left-trim " " " foo ")
   (string-left-trim '(#\O #\F) 'foobar)
   (string-left-trim " " "   ")
   (string-right-trim " " " foo ")
   (string-right-trim '(#\A #\R) 'foobar)
   (string-right-trim " " "   "))
  ("foo " "BAR" ""
   " foo" "FOOB" ""))

(deftest "string comparisons"
  (mapcar (lambda (fn) (mapcar fn '("ab" "abc" "abcd")
			          '("abc" "abc" "abc")))
	  (list #'string< #'string> #'string<= #'string>=))
  ((2 nil nil)
   (nil nil 3)
   (2 3 nil)
   (nil 3 3)))

; (unless (or (= *emacs-version* 20)
; 	    (el:|featurep| 'el:|xemacs|))
;   (deftest "printing circular structures"
;     (mapcar (rcurry #'write-to-string :circle t)
;   	  (list
;   	    (let ((x (list 1 2 3))) (setf (cdddr x) x))
;   	    (let ((x (list 1 2 3))) (setf (car x) x))
;   	    (let ((x (list 1 2 3))) (setf (second x) (cddr x)) x)
;   	    (let ((x (cons t t))) (setf (car x) (setf (cdr x) x)))))
;     ("#1=(1 2 3 . #1#)" "#1=(#1# 2 3)" "(1 #1=(3) . #1#)" "#1=(#1# . #1#)")))

(format t "~&~@
  All tests completed.~@
  ~@
  PASS:              ~D~@
  FAIL evaluation:   ~D~@
  FAIL compilation:  ~D~@
  FAIL execution:    ~D~%~%"
  *pass* *fail-eval* *fail-comp* *fail-exe*)
