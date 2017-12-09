;;; -*- Mode:Common-Lisp; Base:10 -*-
;;;; *-* Last-edit: Sunday, April 30, 1995  20:30:03; Edited-By: anderson *-* 

;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/fft-mod.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;; FFT -- This is an FFT benchmark written by Harry Barrow.
;; It tests a variety of floating point operations, including array references.

(defvar **fft-re**
  (make-array 1025. :element-type
	      #+excl 'single-float #+lucid 'float #+KCL 'single-float 
	      #+Explorer 'single-float
	      #+Lispworks 'single-float
	      :initial-element 0.0))

(defvar **fft-im**
  (make-array 1025. :element-type
	      #+excl 'single-float #+lucid 'single-float #+KCL 'single-float
	      #+Explorer 'single-float
	      #+Lispworks 'single-float
	      :initial-element 0.0))

(defmacro ff+ (a b) 
 `(the single-float (+ (the single-float ,a) (the single-float ,b))))

(defmacro ff*(a b) 
 `(the single-float (* (the single-float ,a) (the single-float ,b))))
(defmacro ff-(a b) 
 `(the single-float (- (the single-float ,a) (the single-float ,b))))


(proclaim '(type (#+KCL vector #-KCL simple-array
		  #+excl single-float
		  #+lucid single-float
		  #+KCL single-float
		  #+Explorer single-float
		  #+Lispworks single-float
		  (*))
		 **fft-re** **fft-im**))

(defvar s-pi (float pi 0.0))
(proclaim '(type #+excl single-float
		 #+KCL single-float
		 #+lucid single-float
		 #+Explorer single-float
		 #+Lispworks single-float
		 s-pi))

(defun fft (areal aimag)
  (declare (type (simple-array single-float (*)) areal aimag))
  (prog* ((ar areal)
	  (ai aimag)
	  (i 1)
	  (j 0)
	  (k 0)
	  (m 0) 			;compute m = log(n)
	  (n (1- (array-dimension ar 0)))
	  (nv2 (floor n 2))
	  (le 0) (le1 0) (ip 0)
	  (ur 0.0) (ui 0.0) (wr 0.0) (wi 0.0) (tr 0.0) (ti 0.0))
     (declare (type fixnum i j k n nv2 m le le1 ip))
     (declare (type (simple-array single-float (*)) ar ai))
     (declare (type single-float ur ui wr wi tr ti))
     l1 (cond ((< i n)
	       (setq m (the fixnum (1+ m))
		     i (the fixnum (+ i i)))
	       (go l1)))
     (cond ((not (equal n (the fixnum (expt 2 m))))
	    (princ "error ... array size not a power of two.")
	    (read)
	    (return (terpri))))
     (setq j 1 				;interchange elements
	   i 1) 			;in bit-reversed order
     l3 (cond ((< i j)
	       (setq tr (aref ar j)
		     ti (aref ai j))
	       (setf (aref ar j) (aref ar i))
	       (setf (aref ai j) (aref ai i))
	       (setf (aref ar i) tr)
	       (setf (aref ai i) ti)))
     (setq k nv2)
     l6 (cond ((< k j)
	       (setq j (the fixnum (- j k))
		     k (the fixnum (/ k 2)))
	       (go l6)))
     (setq j (the fixnum (+ j k))
	   i (the fixnum (1+ i)))
     (cond ((< i n)
	    (go l3)))
     (do ((l 1 (the fixnum (1+ (the fixnum l)))))
	 ((> (the fixnum l) m)) 	;loop thru stages
       (declare (type fixnum l))
       (setq le (the fixnum (expt 2 l))
	     le1 (the (values fixnum fixnum) (floor le 2))
	     ur 1.0
	     ui 0.0
	     wr (cos (/ s-pi (float le1)))
	     wi (sin (/ s-pi (float le1))))
       (do ((j 1 (the fixnum (1+ (the fixnum j)))))
	   ((> (the fixnum j) le1)) 	;loop thru butterflies
	 (declare (type fixnum j))
	 (do ((i j (+ (the fixnum i) le)))
	     ((> (the fixnum i) n)) 	;do a butterfly
	   (declare (type fixnum i))
	   (setq ip (the fixnum (+ i le1))
		 tr (ff- (ff* (aref ar ip) ur)
		       (ff* (aref ai ip) ui))
		 ti (ff+ (ff* (aref ar ip) ui)
		       (ff* (aref ai ip) ur)))
	   (setf (aref ar ip) (ff- (aref ar i) tr))
	   (setf (aref ai ip) (ff- (aref ai i) ti))
	   (setf (aref ar i) (ff+ (aref ar i) tr))
	   (setf (aref ai i) (ff+ (aref ai i) ti))))
       (setq tr (ff- (ff* ur wr) (ff* ui wi))
	     ti (ff+ (ff* ur wi) (ff* ui wr))
	     ur tr
	     ui ti))
     (return t)))


(defun fft-bench ()
  (dotimes (i 10)
    (fft **fft-re** **fft-im**)))

(defun testfft ()
  (print (time (fft-bench))))


;;;
;;; the following are for verifying that the implementation gives the
;;; correct result
;;;

(defun clear-fft ()
  (dotimes (i 1025)
    (setf (aref **fft-re** i) 0.0
	  (aref **fft-im** i) 0.0))
  (values))

(defun setup-fft-component (theta &optional (phase 0.0))
  (let ((f (f* 2 pi theta))
	(c (cos (f* 0.5 pi phase)))
	(s (sin (f* 0.5 pi phase))))
    (dotimes (i 1025)
      (let ((x (sin (* f (/ i 1024.0)))))
	(incf (aref **fft-re** i) (float (* c x) 0.0))
	(incf (aref **fft-im** i) (float (* s x) 0.0)))))
  (values))

(defvar fft-delta 0.0001)

(defun print-fft ()
  (dotimes (i 1025)
    (let ((re (aref **fft-re** i))
	  (im (aref **fft-im** i)))
      (unless (and (< (abs re) fft-delta) (< (abs im) fft-delta))
	(format t "~4d  ~10f ~10f~%" i re im))))
  (values))
