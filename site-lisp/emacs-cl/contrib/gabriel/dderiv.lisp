;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/dderiv.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; DDERIV -- Symbolic derivative benchmark written by Vaughn Pratt.  

;;; This benchmark is a variant of the simple symbolic derivative program 
;;; (DERIV). The main change is that it is `table-driven.'  Instead of using a
;;; large COND that branches on the CAR of the expression, this program finds
;;; the code that will take the derivative on the property list of the atom in
;;; the CAR position. So, when the expression is (+ . <rest>), the code
;;; stored under the atom '+ with indicator DERIV will take <rest> and
;;; return the derivative for '+. The way that MacLisp does this is with the
;;; special form: (DEFUN (FOO BAR) ...). This is exactly like DEFUN with an
;;; atomic name in that it expects an argument list and the compiler compiles
;;; code, but the name of the function with that code is stored on the
;;; property list of FOO under the indicator BAR, in this case. You may have
;;; to do something like:

;;; :property keyword is not Common Lisp.

(defun dderiv-aux (a) 
  (list '// (dderiv a) a))

(defun +dderiv (a)
  (cons '+ (mapcar 'dderiv a)))

(defun -dderiv (a)
  (cons '- (mapcar 'dderiv a)))

(defun *dderiv (a)
  (list '* (cons '* a)
	(cons '+ (mapcar 'dderiv-aux a))))

(defun //dderiv (a)
  (list '- 
	(list '// 
	      (dderiv (car a)) 
	      (cadr a))
	(list '// 
	      (car a) 
	      (list '*
		    (cadr a)
		    (cadr a)
		    (dderiv (cadr a))))))

(mapc #'(lambda (op fun) (setf (get op 'dderiv) (symbol-function fun)))
      '(+ - * //)
      '(+dderiv -dderiv *dderiv //dderiv))

(defun dderiv (a)
  (cond 
    ((atom a)
     (cond ((eq a 'x) 1) (t 0)))
    (t (let ((dderiv (get (car a) 'dderiv)))
	 (cond (dderiv (funcall dderiv (cdr a)))
	       (t 'error))))))

(defun dderiv-run ()
  (do ((i 0 (the fixnum (1+ i))))
      ((= (the fixnum i) 1000.))
    (declare (type fixnum i))
    (dderiv '(+ (* 3 x x) (* a x x) (* b x) 5))
    (dderiv '(+ (* 3 x x) (* a x x) (* b x) 5))
    (dderiv '(+ (* 3 x x) (* a x x) (* b x) 5))
    (dderiv '(+ (* 3 x x) (* a x x) (* b x) 5))
    (dderiv '(+ (* 3 x x) (* a x x) (* b x) 5))))

(defun testdderiv ()
  (print (time (dderiv-run))))
