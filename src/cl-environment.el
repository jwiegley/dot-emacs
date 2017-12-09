;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 25, Environment.

(IN-PACKAGE "EMACS-CL")

(defun leap-year-p (year)
  (and (zerop (REM year 4))
       (or (not (zerop (REM year 100)))
	   (zerop (REM year 400)))))

(defun days-to-month (month year)
  (+ (ecase month
       (1	0)
       (2	31)
       (3	59)
       (4	90)
       (5	120)
       (6	151)
       (7	181)
       (8	212)
       (9	243)
       (10	273)
       (11	304)
       (12	334))
     (if (and (leap-year-p year) (> month 2)) 1 0)))

(defun days-to-year (year)
  (do* ((days 0)
	(y 1900 (1+ y)))
       ((EQL y year)
	days)
    (incf days (if (leap-year-p y) 366 365))))

(defun DECODE-UNIVERSAL-TIME (universal-time &optional time-zone)
  (do ((next-year 1900 (1+ next-year))
       (year 1900 next-year)
       (next-time universal-time
		  (binary- next-time
			   (cl:* 3600 24 (if (leap-year-p next-year) 366 365))))
       (time universal-time next-time))
      ((MINUSP next-time)
       (do ((month 1 (1+ month)))
	   ((or (eq month 13)
		(> (* 3600 24 (days-to-month month year)) time))
	    (decf month)
	    (decf time (* 3600 24 (days-to-month month year)))
	    (MULTIPLE-VALUE-BIND (date time) (TRUNCATE time (* 3600 24))
	      (MULTIPLE-VALUE-BIND (hour time) (TRUNCATE time 3600)
		(MULTIPLE-VALUE-BIND (minute second) (TRUNCATE time 60)
		  ;; TODO:
		  (let (day daylight-p zone)
		    (cl:values second minute hour (1+ date) month year
			       day daylight-p zone))))))))))

(defun encode-days (date month year)
  (+ date -1 (days-to-month month year) (days-to-year year)))

(defun ENCODE-UNIVERSAL-TIME (second minute hour date month year
			      &optional time-zone)
  (let* ((days (encode-days date month year))
	 (hours (binary+ hour (binary* 24 days)))
	 (minutes (binary+ minute (binary* 60 hours))))
    (cl:+ second
	  (binary* 60 minutes)
	  (if time-zone (* 3600 time-zone) 0))))

;;; Difference between Unix time and Common Lisp universal time is 70 years.
(defconst universal-time-offset (ENCODE-UNIVERSAL-TIME 0 0 0 1 1 1970 0))

(defun GET-UNIVERSAL-TIME ()
  (let* ((time (current-time))
	 (high (first time))
	 (low (second time)))
    (cl:+ (binary* high 65536) low universal-time-offset)))

(defun GET-DECODED-TIME ()
  (DECODE-UNIVERSAL-TIME (GET-UNIVERSAL-TIME)))

(defun SLEEP (seconds)
  (sleep-for (if (or (integerp seconds) (floatp seconds))
		 seconds
		 (FLOAT seconds)))
  nil)

(defun APROPOS (string &optional package)
  (dolist (symbol (APROPOS-LIST string package))
    (PRINT symbol))
  (cl:values))

(defun APROPOS-LIST (string-designator &optional package)
  (let ((string (STRING string-designator))
	(packages (if (null package)
		      *all-packages*
		      (list (FIND-PACKAGE package))))
	(result nil))
    (dolist (p packages)
      (DO-SYMBOLS (symbol p)
	(when (SEARCH string (SYMBOL-NAME symbol))
	  (push symbol result))))
    result))

(defun DESCRIBE (object &optional stream-designator)
  (let ((stream (output-stream stream-designator)))
    (DESCRIBE-OBJECT object stream)
    (cl:values)))

;;; TODO: DESCRIBE-OBJECT should be a generic function.
(defun DESCRIBE-OBJECT (object stream)
  (cond
    ((symbolp object)
     (cond
       ((SYMBOL-PACKAGE object)
	(FORMAT stream
		"~&~S is an ~:[internal~;external~] symbol in ~S."
		object (external-symbol-p object) (SYMBOL-PACKAGE object))
	(FORMAT stream "~%It is also accessible in packages ~{~A~^, ~}"
		(let ((name (SYMBOL-NAME object))
		      (home (SYMBOL-PACKAGE object))
		      (packages nil))
		  (dolist (p *all-packages* packages)
		    (MULTIPLE-VALUE-BIND (sym found) (FIND-SYMBOL name p)
		      (when (and found (eq sym object) (not (eq p home)))
			(push (PACKAGE-NAME p) packages)))))))
       (t
	(FORMAT stream "~&~S is an uninterned symbol." object)))
     (when (SPECIAL-OPERATOR-P object)
       (FORMAT stream "~%It is a special operator."))
     (when (boundp object)
       (FORMAT stream "~%~:[Constant ~]Value: ~S"
	       (not (CONSTANTP object)) (symbol-value object)))
     (cond
       ((MACRO-FUNCTION object)
	(FORMAT stream "~%Macro Function: ~S" (MACRO-FUNCTION object)))
       ((fboundp object)
	(FORMAT stream "~%Function: ~S" (SYMBOL-FUNCTION object))))
     (when (COMPILER-MACRO-FUNCTION object)
       (FORMAT stream "~%Compiler Macro Function: ~S"
	       (COMPILER-MACRO-FUNCTION object)))
     (when (symbol-plist object)
       (FORMAT stream "~%Property list: ~S" (symbol-plist object))))
    ((integerp object)
     (FORMAT stream "~&~A is a fixnum." object))
    ((bignump object)
     (FORMAT stream "~&~A is a bignum." object)
     (FORMAT stream "~%It is encoded in ~D fixnums." (1- (length object))))
    ((ratiop object)
     (FORMAT stream "~&~A is a ratio." object)
     (FORMAT stream "~%Numerator: ~D" (NUMERATOR object))
     (FORMAT stream "~%Denominator: ~D" (DENOMINATOR object)))
    ((floatp object)
     ;; TODO: better description
     (FORMAT stream "~&~A is a float." object))
    ((COMPLEXP object)
     (FORMAT stream "~&~A is a complex." object)
     (FORMAT stream "~%Real part: ~A" (REALPART object))
     (FORMAT stream "~%Imaginary part: ~A" (IMAGPART object)))
    ((INTERPRETED-FUNCTION-P object)
     (FORMAT stream "~&~A is an interpreted function." object)
     (FORMAT stream "~%Lambda expression: ~S"
	     (FUNCTION-LAMBDA-EXPRESSION object))
     (when (function-name object)
       (FORMAT stream "~%Name: ~A" (function-name object))))
    ((byte-code-function-p object)
     (FORMAT stream "~&~A is a byte-compiled function." object)
     (when (function-name object)
       (FORMAT stream "~%Name: ~A" (function-name object)))
     (FORMAT stream "~%Lambda list: ~A" (aref object 0))
     (FORMAT stream "~%Byte code: ...")
     (when (> (length object) 2)
       (FORMAT stream "~%Constants: ..."))
     (when (> (length object) 3)
       (FORMAT stream "~%Maximum stack size: ~D" (aref object 3)))
     (when (documentation object)
       (FORMAT stream "~%Documentation: ~A" (documentation object)))
     (when (> (length object) 5)
       (FORMAT stream "~%Interactive: ~S" (aref object 5))))
    ((subrp object)
     (FORMAT stream "~&~A is a built-in subroutine." object)
     (FORMAT stream "~%Name: ~A" (function-name object))
     (when (documentation object)
       (FORMAT stream "~%Documentation: ~A" (documentation object))))
    ((PACKAGEP object)
     (FORMAT stream "~&~A is a package." object)
     (FORMAT stream "~%Nicknames:~{ ~S~}" (PACKAGE-NICKNAMES object))
     (let* ((ext (length (package-exported object)))
	    (int (- (hash-table-count (package-table object)) ext)))
       (FORMAT stream "~%Internal symbols: ~D" int)
       (FORMAT stream "~%External symbols: ~D" ext))
     (FORMAT stream "~%Shadowing symbols: ~D"
	     (length (PACKAGE-SHADOWING-SYMBOLS object)))
     (FORMAT stream "~%Use list: ~S" (PACKAGE-USE-LIST object))
     (FORMAT stream "~%Used by list: ~S" (PACKAGE-USED-BY-LIST object)))
    ((BIT-VECTOR-P object)
     (FORMAT stream "~&~S is a bit vector of length ~D."
	     object (LENGTH object))
     (when (ARRAY-HAS-FILL-POINTER-P object)
       (FORMAT stream "~%Fill pointer: ~A" (FILL-POINTER object))))
    ((STRINGP object)
     (FORMAT stream "~&~S is a string of length ~D." object (LENGTH object))
     (when (ARRAY-HAS-FILL-POINTER-P object)
       (FORMAT stream "~%Fill pointer: ~A" (FILL-POINTER object))))
    ((VECTORP object)
     (FORMAT stream "~&~S is a vector of length ~D." object (LENGTH object))
     (when (vectorp object)
       (FORMAT stream "~%Fill pointer: ~A" (FILL-POINTER object))))
    ((ARRAYP object)
     (FORMAT stream "~&~S is an array with dimensions ~A."
	     object (ARRAY-DIMENSIONS object))
     (FORMAT stream "~@[~%It is specialized to hold ~A.~]"
	     (case (aref object 0)
	       (bit-array "bits")
	       (char-array "characters"))))
    ((consp object)
     (catch 'done
       (HANDLER-BIND
	   ((ERROR (lambda (c)
		     (if (atom (cdr object))
			 (FORMAT stream "~&~S is a cons cell." object)
			 (FORMAT stream "~&~S is a dotted list." object))
		     (throw 'done nil))))
	 (if (LIST-LENGTH object)
	     (FORMAT stream "~&~S is a list of length ~D."
		     object (length object))
	     (FORMAT stream "~&~S is a circular list." object)))))
    ((vectorp object)
     ;; TODO:
     (FORMAT stream "~&FIXME: This is a fall-back description.")
     (FORMAT stream "~%~A is an instance of ~S" object (TYPE-OF object))
     (FORMAT stream "~%The values of its slots are:")
     (do* ((len (length object))
	   (i 1 (1+ i)))
	  ((eq i len))
       (FORMAT stream "~%  Slot ~D: ~S" i (aref object i))))
    (t
     (FORMAT stream "~&Don't know how to describe ~A" object))))

(defvar *traced-functions* nil)

(defun traced-fn (name)
  `(lambda (&rest args)
     (PRINT (format ,(format "Trace: %s %%s" name) args) *TRACE-OUTPUT*)
     (APPLY ,(FDEFINITION name) args)))

(defun trace-fn (name)
  (unless (assoc name *traced-functions*)
    (push (cons name (FDEFINITION name)) *traced-functions*)
    (setf (FDEFINITION name) (traced-fn name))))

(cl:defmacro TRACE (&rest names)
  (if (null names)
      `(QUOTE ,(mapcar #'car *traced-functions*))
      `(DOLIST (name (QUOTE ,names))
	 (trace-fn name))))
      
(defun untrace-fn (name)
  (let ((fn (assoc name *traced-functions*)))
    (when fn
      (setq *traced-functions* (delq fn *traced-functions*))
      (setf (FDEFINITION name) (cdr fn)))))

(cl:defmacro UNTRACE (&rest names)
  `(MAPC (FUNCTION untrace-fn) ,(if (null names) '(TRACE) `(QUOTE ,names))))

(cl:defmacro STEP (form)
  ;; TODO: stepping
  `(LET () ,form))

(cl:defmacro TIME (form)
  (with-gensyms (start val end time)
    `(LET* ((,start (GET-INTERNAL-REAL-TIME))
	    (,val (MULTIPLE-VALUE-LIST ,form))
	    (,end (GET-INTERNAL-REAL-TIME))
	    (,time (,(INTERN "-" "CL") ,end ,start)))
       (FORMAT *TRACE-OUTPUT* "~&Elapsed real time: ~A seconds"
	       (,(INTERN "*" "CL")
		(ROUND (,(INTERN "*" "CL") ,time
			 ,(/ 1000.0 INTERNAL-TIME-UNITS-PER-SECOND)))
		0.001))
       (VALUES-LIST ,val))))

(DEFCONSTANT INTERNAL-TIME-UNITS-PER-SECOND 1000000)

(defun GET-INTERNAL-REAL-TIME ()
  (let* ((time (current-time))
	 (high (first time))
	 (low (second time))
	 (microsec (third time)))
    (binary+ (binary* (binary+ (binary* high 65536) low) 1000000) microsec)))

;;; TODO: Function GET-INTERNAL-RUN-TIME
(if (fboundp 'get-internal-run-time)
    (defun GET-INTERNAL-RUN-TIME ()
      (let* ((time (get-internal-run-time))
	     (high (first time))
	     (low (second time))
	     (microsec (third time)))
	(binary+ (binary* (binary+ (binary* high 65536) low) 1000000)
		 microsec)))
    (defun GET-INTERNAL-RUN-TIME ()
      (GET-INTERNAL-REAL-TIME)))

(defun DISASSEMBLE (fn)
  (when (or (symbolp fn) (setf-name-p fn))
    (setq fn (FDEFINITION fn)))
  (when (INTERPRETED-FUNCTION-P fn)
    (setq fn (COMPILE nil fn)))
  (disassemble fn)
  nil)

;;; TODO: Standard Generic Function DOCUMENTATION, (SETF DOCUMENTATION)

(cl:defun ROOM (&OPTIONAL (x (kw DEFAULT)))
  (let* ((info (garbage-collect))
         (foo '("conses" "symbols" "misc" "string chars"
                "vector slots" "floats" "intervals" "strings"))
         (cons-info (first info))
         (sym-info (second info))
         (misc-info (third info))
         (used-string-chars (fourth info))
         (used-vector-slots (fifth info))
         (float-info (sixth info))
         (interval-info (seventh info))
         (string-info (eighth info)))
    (cond
      ((eq x nil))
      ((eq x (kw DEFAULT))
       (do ((i info (cdr i))
            (j foo (cdr j)))
           ((null i) nil)
         (PRINC (format "\nUsed %-13s:  " (car j)))
         (cond
           ((null (car i)))
           ((atom (car i))
            (PRINC (format "%7d." (car i))))
           (t
            (PRINC (format "%7d, free %-10s: %7d"
                           (caar i) (car j) (cdar i)))))))
      ((eq x 'T)
       (ROOM)
       (PRINC "\nConsed so far:")
       (PRINC (format "\n%d conses," cons-cells-consed))
       (PRINC (format "\n%d floats," floats-consed))
       (PRINC (format "\n%d vector cells," vector-cells-consed))
       (PRINC (format "\n%d symbols," symbols-consed))
       (PRINC (format "\n%d string chars," string-chars-consed))
       (PRINC (format "\n%d misc objects," misc-objects-consed))
       (PRINC (format "\n%d intervals" intervals-consed))
       (if (boundp 'strings-consed)
	   ;; Use symbol-value to shut up compiler warnings.
	   (PRINC (format "\n%d strings." (symbol-value 'strings-consed)))
	   (PRINC ".")))
      (t
       (type-error x `(OR BOOLEAN (EQL ,(kw DEFAULT))))))))

(defun ED (&optional x)
  (cond
    ((null x)
     (switch-to-buffer (generate-new-buffer "*ED*")))
    ((or (PATHNAMEP x) (STRINGP x))
     (find-file (NAMESTRING (PATHNAME x))))
    ((or (SYMBOLP x) (setf-name-p x))
     (find-tag (prin1-to-string x)))
    (t
     (type-error x '(OR NULL PATHNAME STRING SYMBOL
		        (CONS (EQ SETF) (CONS SYMBOL NULL)))))))

;;; TODO: Function INSPECT

;;; TODO: Function DRIBBLE

(defvar cl:- nil)
(defvar cl:+ nil)
(defvar ++ nil)
(defvar +++ nil)
(defvar cl:* nil)
(defvar ** nil)
(defvar *** nil)
(defvar cl:/ nil)
(defvar // nil)
(defvar /// nil)

(defun LISP-IMPLEMENTATION-TYPE ()
  "Emacs Common Lisp")

(defun LISP-IMPLEMENTATION-VERSION ()
  "0.8")

(defun SHORT-SITE-NAME ()
  nil)

(defun LONG-SITE-NAME ()
  nil)

(defun MACHINE-INSTANCE ()
  (system-name))

(defun MACHINE-TYPE ()
  (subseq system-configuration 0 (position 45 system-configuration)))

(defun MACHINE-VERSION ()
  nil)

(defun SOFTWARE-TYPE ()
  (STRING system-type))

(defun SOFTWARE-VERSION ()
  nil)

(defun USER-HOMEDIR-PATHNAME (&optional host)
  ;; TODO: look at host
  (PATHNAME "~/"))
