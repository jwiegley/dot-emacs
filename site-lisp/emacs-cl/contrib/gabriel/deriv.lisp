;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/deriv.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; DERIV -- Symbolic derivative benchmark written by Vaughn Pratt.  
;;; It uses a simple subset of Lisp and does a lot of  CONSing. 

(defun deriv-aux (a) (list '/ (deriv a) a))

(defun deriv (a)
  (cond 
    ((atom a)
     (cond ((eq a 'x) 1) (t 0)))
    ((eq (car a) '+)	
     (cons '+ (mapcar #'deriv (cdr a))))
    ((eq (car a) '-) 
     (cons '- (mapcar #'deriv (cdr a))))
    ((eq (car a) '*)
     (list '* 
	   a 
	   (cons '+ (mapcar #'deriv-aux (cdr a)))))
    ((eq (car a) '/)
     (list '- 
	   (list '/ 
		 (deriv (cadr a)) 
		 (caddr a))
	   (list '/ 
		 (cadr a) 
		 (list '*
		       (caddr a)
		       (caddr a)
		       (deriv (caddr a))))))
    (t 'error)))

(defun deriv-run ()
  (do ((i 0 (the fixnum (1+ i))))
      ((= (the fixnum i) 1000.))	;runs it 5000 times
    (declare (type fixnum i))		;improves the code a little
    (deriv '(+ (* 3 x x) (* a x x) (* b x) 5))
    (deriv '(+ (* 3 x x) (* a x x) (* b x) 5))
    (deriv '(+ (* 3 x x) (* a x x) (* b x) 5))
    (deriv '(+ (* 3 x x) (* a x x) (* b x) 5))
    (deriv '(+ (* 3 x x) (* a x x) (* b x) 5))))

(defun testderiv ()
  (print (time (deriv-run))))
