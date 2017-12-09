;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/browse.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; BROWSE -- Benchmark to create and browse through an AI-like data base
;;; of units.

;;; n is # of symbols
;;; m is maximum amount of stuff on the plist
;;; npats is the number of basic patterns on the unit
;;; ipats is the instantiated copies of the patterns

(eval-when (eval compile)
  (defvar *browse-rand* 21)
  (proclaim '(type fixnum *browse-rand*))
  (defconstant *browse-star* (code-char 42))
  (defconstant *browse-questionmark* (code-char 63)))

(eval-when (eval compile)
  ;; maybe SYMBOL-NAME
  (defmacro browse-char1 (x) `(schar (symbol-name ,x) 0)))


(defun browse-init (n m npats ipats)
  (declare (type fixnum n m npats))
  (setq *browse-rand* 21)
  (let ((ipats (copy-tree ipats)))
    (do ((p ipats (cdr p)))
	((null (cdr p)) (rplacd p ipats)))	
    (do ((n n (the fixnum (1- n)))
	 (i m (cond ((= i 0) m)
		    (t (the fixnum (1- i)))))
	 (name (gentemp) (gentemp))
	 (a ()))
	((= n 0) a)
      (declare (type fixnum n i)) 
      (push name a)
      (do ((k i (the fixnum (1- k))))
	  ((= k 0))
	(declare (type fixnum k))
	(setf (get name (gensym)) nil))
      (setf (get name 'pattern)
	    (do ((i npats (the fixnum (1- i)))
		 (ipats ipats (cdr ipats))
		 (a ()))
		((= i 0) a)
	      (declare (type fixnum i))
	      (push (car ipats) a)))
      (do ((j (the fixnum (- m i)) (the fixnum (1- j))))
	  ((= j 0))
	(declare (type fixnum j))
	(setf (get name (gensym)) nil)))))  


(defun browse-random ()
  (setq *browse-rand* (rem (the fixnum (* *browse-rand* 17)) 251)))

(defun browse-randomize (l)
  (do ((a ()))
      ((null l) a)
    (let ((n (rem (the fixnum (browse-random)) (the fixnum (length l)))))
      (declare (type fixnum n))
      (cond ((= n 0)
	     (push (car l) a)
	     (setq l (cdr l)))
	    (t 
	     (do ((n n (the fixnum (1- n)))
		  (x l (cdr x)))
		 ((= n 1)
		  (push (cadr x) a)
		  (rplacd x (cddr x)))
	       (declare (type fixnum n))))))))

(defun match (pat dat alist)
  (cond ((null pat)
	 (null dat))
	((null dat) ())
	((or (eq (car pat) '?)
	     (eq (car pat)
		 (car dat)))
	 (match (cdr pat) (cdr dat) alist))
	((eq (car pat) '*)
	 (or (match (cdr pat) dat alist)
	     (match (cdr pat) (cdr dat) alist)
	     (match pat (cdr dat) alist)))
	(t (cond ((atom (car pat))
			;;replace eq by 'eql for char	
		  (cond ((eql (browse-char1 (car pat))
			     *browse-questionmark*)
			 (let ((val (assoc (car pat) alist)))
			   (cond (val (match (cons (cdr val)
						   (cdr pat))
					     dat alist))
				 (t (match (cdr pat)
					   (cdr dat)
					   (cons (cons (car pat)
						       (car dat))
						 alist))))))
			((eql (browse-char1 (car pat)) *browse-star*)
			 (let ((val (assoc (car pat) alist)))
			   (cond (val (match (append (cdr val)
						     (cdr pat))
					     dat alist))
				 (t 
				  (do ((l () (nconc l (cons (car d) nil)))
				       (e (cons () dat) (cdr e))
				       (d dat (cdr d)))
				      ((null e) ())
				    (cond ((match (cdr pat) d
						  (cons (cons (car pat) l)
							alist))
					   (return t))))))))))
		 (t (and 
		      (not (atom (car dat)))
		      (match (car pat)
			     (car dat) alist)
		      (match (cdr pat)
			     (cdr dat) alist)))))))

(defun browse ()
  (investigate (browse-randomize 
		 (browse-init 100 10 4 '((a a a b b b b a a a a a b b a a a)
					 (a a b b b b a a
					  (a a)(b b))
					 (a a a b (b a) b a b a))))
	       '((*a ?b *b ?b a *a a *b *a)
		 (*a *b *b *a (*a) (*b))
		 (? ? * (b a) * ? ?))))

(defun investigate (units pats)
  (do ((units units (cdr units)))
      ((null units))
    (do ((pats pats (cdr pats)))
	((null pats))
      (do ((p (get (car units) 'pattern)
	      (cdr p)))
	  ((null p))
	(match (car pats) (car p) ())))))

(defun testbrowse ()
  (print (time (browse))))
