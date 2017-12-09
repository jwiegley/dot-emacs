;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/control.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;;
;; benchmark control

(setf (comp:target-fpp) :m68881)
(setq comp::*target-architecture* :mc68020)
(setf (sys:gsgc-parameter :generation-spread) 4)

(require :foreign)
(use-package :ff)
(load "time.o")

(defforeign 'get_time
    :entry-point (convert-to-lang "get_time" :language :c)
    :arguments '(t))

(import '(lisp::time-utime-sec lisp::time-utime-usec lisp::time-stime-sec
	  lisp::time-stime-usec lisp::time-stime-minflt
	  lisp::time-stime-majflt lisp::time-stime-maxrss
	  lisp::time-real-sec lisp::time-real-usec))

(defcstruct time
  (utime-sec :unsigned-long)
  (utime-usec :unsigned-long)
  (stime-sec :unsigned-long)
  (stime-usec :unsigned-long)
  (stime-minflt :unsigned-long)
  (stime-majflt :unsigned-long)
  (stime-maxrss :unsigned-long)
  (real-sec :unsigned-long)
  (real-usec :unsigned-long))

(defmacro bm-time-macro (form)
  `(let ((start (make-time)) (end (make-time)))
    (get_time start)
    (multiple-value-prog1 ,form
      (get_time end)
      (print-time start end))))

(defun print-time (start end)
  (let* ((u1 (truncate (+ (* 1000000 (time-utime-sec start))
			  (time-utime-usec start))
		       1000))
	 (s1 (truncate (+ (* 1000000 (time-stime-sec start))
			  (time-stime-usec start))
		       1000))
	 (u2 (truncate (+ (* 1000000 (time-utime-sec end))
			  (time-utime-usec end))
		       1000))
	 (s2 (truncate (+ (* 1000000 (time-stime-sec end))
			  (time-stime-usec end))
		       1000))
	 (r1 (truncate (+ (* 1000000 (time-real-sec start))
			  (time-real-usec start))
		       1000))
	 (r2 (truncate (+ (* 1000000 (time-real-sec end))
			  (time-real-usec end))
		       1000))
	 (page-faults (- (+ (time-stime-majflt end)
			    (time-stime-minflt end))
			 (+ (time-stime-minflt start)
			    (time-stime-majflt start))))
	 (real (- r2 r1))
	 (user (- u2 u1))
	 (system (- s2 s1)))
    (format *trace-output*
      "
 (~10:<~d~> ;; non-gc user
  ~10:<~d~> ;; non-gc system
  ~10:<~d~> ;; gc user
  ~10:<~d~> ;; gc system
  ~10:<~d~> ;; total user
  ~10:<~d~> ;; total gc
  ~10:<~d~> ;; real
  ~10:<~d~> ;; max rss size (pages)
  ~10:<~d~> ;; page faults
  )"
      user system 0 0 user 0 real
      (time-stime-maxrss end) page-faults)))

(defparameter *benches*
  '(boyer
    browse
    ctak
    dderiv
    deriv
    destru
    (div2 div2-iter div2-recur)
    fft
    fprint
    fread
    (frpoly frpoly-1 frpoly-2 frpoly-3 frpoly-4)
    puzzle
    stak
    tak
    takl
    takr
    tprint
    (traverse traverse-init traverse-run)
    triang))

(defun compile-all-bms (&optional (result-file "results.compile"))
  (let ((old-time (macro-function 'time)))
    (setf (macro-function 'time) (macro-function 'bm-time-macro))
    (let ((*trace-output*
	   (open result-file :direction :output :if-exists :supersede)))
      (format *trace-output* "(:benchmark-compilation~%")
      (gc :tenure)
      (bm-time-macro
	(dolist (bench *benches*)
	  (if (consp bench) (setq bench (car bench)))
	  (setq bench (string-downcase (string bench)))
	  (compile-file (merge-pathnames (make-pathname :type "cl") bench))))
      (format *trace-output* ")~%")
      (close *trace-output*))
    (setf (macro-function 'time) old-time)
    nil))

(defun run-all-bms (&optional (result-file "results.run"))
  (let ((*trace-output*
	 (open result-file :direction :output :if-exists :append)))
    (dolist (bench *benches*)
      (run-bench bench))
    (close *trace-output*)))

(defun run-bench (bench &aux name function)
  (cond
    ((consp bench)
     ;; the form of bench is
     ;;  (file name1 name2 ...)
     (load (string-downcase (symbol-name (car bench))))
     (dolist (name (cdr bench))
       (run-bench-1 name (find-symbol (format nil "~a~a" 'test name)))))
    (t (load (string-downcase (symbol-name bench)))
       (run-bench-1 bench (find-symbol (format nil "~a~a" 'test bench))))))

(defun run-bench-1 (bench function)
  (format *trace-output* "~%(:~a~%" bench)
  (dotimes (n 3)
    (gc :tenure)
    (funcall function))
  (format *trace-output* ")~%")
  (force-output *trace-output*))

(defun run-benches (&rest bench-list)
  (mapc #'(lambda (bench) (apply #'run-bench bench)) bench-list))
