;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/triang-old-mod.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; TRIANG -- Board game benchmark.

(proclaim '(special board sequence a b c))

(proclaim '(type (vector fixnum) a b c))
(defmacro fref (v i) `(the fixnum (aref (the (vector fixnum) ,v) ,i)))

(defvar answer)
(defvar final)

(defun triang-setup ()
  (setq board (make-array 16 :initial-element 1))
  (setq sequence (make-array 14 :initial-element 0))
  (setq a
    (make-array
      37
      :element-type 'fixnum :initial-contents
      '(1 2 4 3 5 6 1 3 6 2 5 4 11 12 13 7 8 4 4 7 11 8 12
	13 6 10 15 9 14 13 13 14 15 9 10 6 6)))
  (setq b (make-array
	    37       :element-type 'fixnum :initial-contents
	    '(2 4 7 5 8 9 3 6 10 5 9 8 12 13 14 8 9 5
	      2 4 7 5 8 9 3 6 10 5 9 8 12 13 14 8 9 5 5)))
  (setq c (make-array
	    37       :element-type 'fixnum :initial-contents
	    '(4 7 11 8 12 13 6 10 15 9 14 13 13 14 15 9 10 6
	      1 2 4 3 5 6 1 3 6 2 5 4 11 12 13 7 8 4 4)))
  (setf (svref board 5) 0))


(defun last-position ()
  (do ((i 1 (the fixnum (+ i 1))))
      ((= i 16) 0)
    (declare (type fixnum i))
    (if (eq 1 (svref board i))
	(return i))))
(proclaim '(function try (fixnum fixnum) t))
(defun try (i depth)
  (declare (type fixnum i depth))
  (cond ((= depth 14) 
	 (let ((lp (last-position)))
	   (unless (member lp final :test #'eq)
	     (push lp final)))
	 (push (cdr (simple-vector-to-list sequence))
	       answer) t) 		; this is a hack to replace LISTARRAY
	((and (eq 1 (svref board (fref a i)))
	      (eq 1 (svref board (fref b i)))
	      (eq 0 (svref board (fref c i))))
	 (setf (svref board (fref a i)) 0)
	 (setf (svref board (fref b i)) 0)
	 (setf (svref board (fref c i)) 1)
	 (setf (svref sequence depth) i)
	 (do ((j 0 (the fixnum (+ j 1)))
	      (depth (the fixnum (+ depth 1))))
	     ((or (= j 36)
		  (try j depth)) ())
	   (declare (type fixnum j depth)))
	 (setf (svref board (fref a i)) 1) 
	 (setf (svref board (fref b i)) 1)
	 (setf (svref board (fref c i)) 0) ())))

(defun simple-vector-to-list (seq)
  (do ((i (- (length seq) 1) (1- i))
       (res))
      ((< i 0)
       res)
    (declare (type fixnum i))
    (push (svref seq i) res)))
		
(defun gogogo (i)
  (let ((answer ())
	(final ()))
    (try i 1)))

(defun testtriang ()
  (triang-setup)
  (print (time (gogogo 22))))
