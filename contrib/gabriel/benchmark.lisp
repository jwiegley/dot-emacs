;;;; -*- Mode:Common-Lisp; Package:cl-user; Fonts:(medfnt courierfb hl12i tr12 medfnb cptfonti hl12b); Base:10 -*-
;;;; *-* File: /usr/users/eksl/systems/mess/gabriel/benchmark.lisp *-*
;;;; *-* Last-edit: Friday, June 2, 1995  15:07:05; Edited-By: anderson *-* 
;;;; *-* Machine: Christa (Explorer II, Microcode 489) *-*
;;;; *-* Software: TI Common Lisp System 6.49 *-*
;;;; *-* Lisp: TI Common Lisp System 6.49  *-*

;;;; **************************************************************************
;;;; **************************************************************************
;;;; *                                                                        *
;;;; *                      Running Gabriel's Benchmarks                      *
;;;; *                                                                        *
;;;; **************************************************************************
;;;; **************************************************************************
;;;
;;; Written by: Scott D. Anderson
;;;             Experimental Knowledge Systems Laboratory
;;;             Paul R. Cohen, Principal Investigator
;;;             David L. Westbrook, Systems Manager
;;;             David M. Hart, Laboratory Manager
;;;             Department of Computer Science
;;;             University of Massachusetts
;;;             Amherst, Massachusetts 01003.
;;;
;;; * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
;;;
;;;  02-18-95 File Created.  (anderson)
;;;  09-97    Made some changes to make things easier to use.  (Westy)
;;;
;;; * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
;;; --*--

(in-package :COMMON-LISP-USER)

;;; --*--
;;; ***************************************************************************
;;; This file is similar to the makefile that is distributed with Gabriel's
;;; benchmarks.  I wrote it because the Makefile approach will not work with the
;;; Explorer, and I don't know how the Explorer timings were gotten, if, indeed,
;;; any Explorer timings were done.  It iterates over all the test files,
;;; proclaiming them, compiling them, loading them, and running the test
;;; functions.  All of this is pretty much as the makefile does.

;;; Since I want to control what package the test file is compiled and loaded
;;; in, I needed to modify the code in test-help.lsp.  Rather than make a
;;; separate file, I implemented that code in this file, so this file duplicates
;;; the test-help file in addition to the makefile.

;;; Thus, this is the master file for getting timings on almost any Lisp system.
;;; To use it, do the following:

;;; 1. Load this file
;;; 2. Run (benchmarks) to output to standard-output or
;;;        (benchmarks :output <output-filename>) to send output to a file.

;;; The pathname tells Lisp what to merge the filename with to get a pathname
;;; acceptable to `compile' or `load.' The output filename says where to print
;;; the results; the default is standard output.  The `package' is the package
;;; to compile and load the benchmarks in.

(defparameter *files*
  '(boyer browse ctak dderiv deriv destru-mod destru div2 fft-mod
	  fft #+ignore fprint #+ignore fread frpoly 
	  ;; puzzle-mod puzzle
	  puzzle-mod-noproclaim puzzle-noproclaim
	  stak tak-mod tak takl takr #+ignore tprint traverse triang-mod
	  triang)
  "Names of the files of benchmark functions.")

(defparameter *gabriel-root-pathname* 
  (let ((pathname-dir
         (cond (*load-truename* (pathname-directory *load-truename*))
               #+MCL
               ((pathname-directory *loading-file-source-file*))
               (t nil))))
    (when pathname-dir (make-pathname :directory pathname-dir))))

(defun benchmark (&key (directory *gabriel-root-pathname*) output)
  "`directory' is merged with the filenames to yield a pathname to load the benchmark code from; it defaults
to the directory this file is loaded in. `Output' is a filename where the results are put; it's also
merged with the `directory.' If it is omitted, the results go to standard output."
  (let ((pkg :common-lisp-user)) ; changed from user - Westy - 3/27/96
    (let ((*package* (find-package pkg)))
      (make-compile directory)
      (let ((stream (if output
			(open (merge-pathnames output directory) :direction :output)
			*standard-output*)))
	(unwind-protect
	    (progn 
	      (format stream "~&------------- SESSION --------------------~%")
	      (format stream "Lisp implementation type: ~s~%" (lisp-implementation-type))
	      (format stream "Lisp implementation version: ~s~%" (lisp-implementation-version))
	      (format stream "Machine type: ~s~%" (machine-type))
	      (format stream "Machine version: ~s~%" (machine-version))
	      (format stream "Machine instance: ~s~%" (machine-instance))
	      (format stream "Software type: ~s~%" (software-type))
	      (format stream "Software version: ~s~%" (software-version))
	      (format stream "Short site name: ~s~%" (short-site-name))
	      (format stream "In Package: ~s~2%" pkg)
	      (format stream "~2%")
	      (make-test stream))
	  (if output (close stream)))))))

(defun make-compile (dirname)
  (load (merge-pathnames "make-declare.lsp" dirname))
  (dolist (v *files*)
    (let ((f (merge-pathnames (format nil "~(~a~).cl" v) dirname)))
      (let (#+Explorer (SI:INHIBIT-FDEFINE-WARNINGS t))
	(format t "~&Proclaiming ~s~%" f)
	(proclaim-file f)
	(format t "~&Compiling and loading ~s~%" f)
	(load (compile-file f))))
    #+ignore
    (y-or-n-p "Go on?")))

(defun make-test (stream)
  (dolist (v *files*)
    (do-test v stream)))

(defvar *repeats* '((destru 4) (destru-mod 4) (fprint 4) (fread 4)
		     (stak 4) (takr 4) (tprint 4)))

(defparameter *repetitions* 1)

(defparameter *all-or-summary* :summary)

(defun do-test (file stream)
  (let ((command (let ((pos (position #\- (string file))))
		   (intern 
		     (concatenate 'string "TEST" 
				  (if pos
				      (subseq (string file) 0 pos)
				      (string file)))
		     *package*))))
    #+Explorer
    (gc-immediately)
    #+Lispworks
    (mark-and-sweep 0)
    #+Allegro
    (excl:gc t)
    #+MCL
    (gc)
    (if (= *repetitions* 1)
        (format stream "~%~:@(~a~)~,12t~,3f" file (timeit command file))
	(loop repeat *repetitions*
                 collect (timeit command file) into times
                 finally
                 (setf times (sort times #'<))
                 (ecase *all-or-summary*
                   (:all
                    (format stream "~%~:@(~a~)~,12t~{ ~,3f~}" file times))
                   (:summary
                    (format stream "~%~:@(~a~)~,12t~,3f  ~,3f  ~,3f"
                            file
                            (nth 0 times)
                            (nth (1- *repetitions*) times)
                            ;; median
                            (if (oddp *repetitions*)
			        (nth (floor *repetitions* 2) times)
			        (/ (+ (nth (1- (floor *repetitions* 2)) times)
				      (nth (floor *repetitions* 2) times))
			           2)))))))))

(defun timeit (command file)
  (let ((n (or (cadr (assoc file *repeats*)) 1)))
    (format t "~&Calling ~s ~d time~:p~%" command n)
    (let ((start (get-internal-run-time)))
      (dotimes (i n) (funcall command))
      (/ (/ (float (- (get-internal-run-time) start)) n)
         (float internal-time-units-per-second)))))

;;; ================================================================

#+OLD
(defun min-max-median ()
  (with-open-file (cl1 "lw-cl-1.text")
    (with-open-file (cl2 "lw-cl-2.text")
      (with-open-file (tcl "lw-tcl-1.text")
        (with-open-file (tcw "lw-cw-1.text")
        (loop repeat 10 do
              (read-line cl1)
              (read-line cl2)
              (read-line tcl)
              (read-line tcw))
        (loop for cl1x = (read cl1 nil)
              for cl2x = (read cl2 nil)
              for tclx = (read tcl nil)
              for tcwx = (read tcw nil)
              for cl1y = (read cl1 nil)
              for cl2y = (read cl2 nil)
              for tcly = (read tcl nil)
              for tcwy = (read tcw nil)
              do
              (when (null cl1x) (loop-finish))
              (unless (and (eq cl1x cl2x) (eq cl2x tclx) (eq tclx tcwx))
                (error "out of synch: ~s ~s ~s ~s" cl1x cl2x tclx tcwx))
              (format t "~(~a~) ~25t & ~5,3f & ~5,3f & ~5,3f & ~5,3f & ~3,1f & ~3,1f \\\\~%"
                      cl1x
                      cl1y
                      cl2y
                      tcly
                      tcwy
                      (/ tcly (/ (+ cl1y cl2y) 2))
                      (/ tcwy (/ (+ cl1y cl2y) 2)))))))))

;;; ***************************************************************************
;;; EOF
