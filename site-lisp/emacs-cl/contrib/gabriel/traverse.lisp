;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/traverse.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; TRAVERSE --  Benchmark which creates and traverses a tree structure.


(eval-when (eval compile load)
  (defstruct node
    (parents ())
    (sons ())
    (sn (snb))
    (entry1 ())
    (entry2 ())
    (entry3 ())
    (entry4 ())
    (entry5 ())
    (entry6 ())
    (mark ()))
)
(defvar traverse-sn 0)
(defvar traverse-rand 21.)
(defvar traverse-count 0)
(proclaim `(type fixnum traverse-sn traverse-rand traverse-count))
(defvar traverse-marker nil)
(defvar traverse-root)

(setq traverse-sn 0 traverse-rand 21 traverse-count 0 traverse-marker nil)

(defun snb ()
  (setq traverse-sn (the fixnum (1+ traverse-sn))))

(defun traverse-seed ()
  (setq traverse-rand 21.))

(defun traverse-random ()
  (setq traverse-rand
	(the fixnum (rem (the fixnum (* traverse-rand 17)) 251))))

(defun traverse-remove (n q)
  (declare (type fixnum n))
  (cond ((eq (cdr (car q)) (car q))
	 (prog2 () (caar q) (rplaca q ())))
	((= n 0)
	 (prog2 () (caar q)
		(do ((p (car q) (cdr p)))
		    ((eq (cdr p) (car q))
		     (rplaca q
			     (rplacd p (cdr (car q))))))))
	(t (do ((n n (the fixnum (1- n)))
		(q (car q) (cdr q))
		(p (cdr (car q)) (cdr p)))
	       ((= n 0) (prog2 () (car q) (rplacd q p)))
	     (declare (type fixnum n))))))

(defun traverse-select (n q)
  (declare (type fixnum n))
  (do ((n n (the fixnum (1- n)))
       (q (car q) (cdr q)))
      ((= n 0) (car q))
    (declare (type fixnum n))))

(defun traverse-add (a q)
  (cond ((null q)
	 `(,(let ((x `(,a)))
	      (rplacd x x) x)))
	((null (car q))
	 (let ((x `(,a)))
	   (rplacd x x)
	   (rplaca q x)))
	(t (rplaca q
		   (rplacd (car q) `(,a .,(cdr (car q))))))))

(defun traverse-create-structure (n)
  (declare (type fixnum n))
  (let ((a `(,(make-node))))
    (do ((m (the fixnum (1- n)) (the fixnum (1- m)))
	 (p a))
	((= m 0) (setq a `(,(rplacd p a)))
	 (do ((unused a)
	      (used (traverse-add (traverse-remove 0 a) ()))
	      (x) (y))
	     ((null (car unused))
	      (find-root (traverse-select 0 used) n))
	   (setq x (traverse-remove
		    (the fixnum (rem (the fixnum (traverse-random)) n))
		    unused))
	   (setq y (traverse-select 
		    (the fixnum (rem (the fixnum (traverse-random)) n))
		    used))
	   (traverse-add x used)
	   (setf (node-sons y) `(,x .,(node-sons y)))
	   (setf (node-parents x) `(,y .,(node-parents x))) ))
      (declare (type fixnum m))
      (push (make-node) a))))

(defun find-root (node n)
  (declare (type fixnum n))
  (do ((n n (the fixnum (1- n))))
      ((= n 0) node)
    (declare (type fixnum n))
    (cond ((null (node-parents node))
	   (return node))
	  (t (setq node (car (node-parents node)))))))

(defun travers (node mark)
  (cond ((eq (node-mark node) mark) ())
	(t (setf (node-mark node) mark)
	   (setq traverse-count (the fixnum (1+ traverse-count)))
	   (setf (node-entry1 node) (not (node-entry1 node)))
	   (setf (node-entry2 node) (not (node-entry2 node)))
	   (setf (node-entry3 node) (not (node-entry3 node)))
	   (setf (node-entry4 node) (not (node-entry4 node)))
	   (setf (node-entry5 node) (not (node-entry5 node)))
	   (setf (node-entry6 node) (not (node-entry6 node)))
	   (do ((sons (node-sons node) (cdr sons)))
	       ((null sons) ())
	     (travers (car sons) mark)))))



(defun traverse (traverse-root)
  (let ((traverse-count 0))
    (declare (type fixnum traverse-count))
    (travers traverse-root
	     (setq traverse-marker (not traverse-marker)))
    traverse-count))

(defun init-traverse()
  (setq traverse-root (traverse-create-structure 100.))
  nil)

(defun run-traverse ()
  (do ((i 50 (the fixnum (1- (the fixnum i)))))
      ((= (the fixnum i) 0))
    (declare (type fixnum i))
    (traverse traverse-root)
    (traverse traverse-root)
    (traverse traverse-root)
    (traverse traverse-root)
    (traverse traverse-root))) 

(defun testtraverse ()
  (testtraverse-init)
  (testtraverse-run))

(defun testtraverse-init ()
  (print (time (init-traverse))))

(defun testtraverse-run ()
  (print (time (run-traverse))))
