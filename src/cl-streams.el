;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 21, Streams.

(IN-PACKAGE "EMACS-CL")

(DEFSTRUCT (STREAM (:predicate STREAMP) (:copier nil))
  (openp T)
  (ELEMENT-TYPE 'CHARACTER)
  direction
  content
  (position 0)
  end
  fresh-line-p
  (unread-buffer nil)
  read-fn
  write-fn)

(defmacro defstream (name &rest slots)
  `(DEFSTRUCT (,name (:include STREAM)
	             (:predicate nil)
	             (:copier nil)
	             (:constructor
		      ,(intern (concat "mk-" (symbol-name name)))))
     ,@slots))

(defstream BROADCAST-STREAM STREAMS)
(defstream CONCATENATED-STREAM STREAMS)
(defstream ECHO-STREAM INPUT-STREAM OUTPUT-STREAM)
(defstream FILE-STREAM filename)
(defstream STRING-STREAM string)
(defstream SYNONYM-STREAM SYMBOL)
(defstream TWO-WAY-STREAM INPUT-STREAM OUTPUT-STREAM)

(defun stream-error (stream)
  (ERROR 'STREAM-ERROR (kw STREAM) stream))

(DEFVAR *STANDARD-INPUT* nil)

(DEFVAR *STANDARD-OUTPUT* nil)

(DEFVAR *TERMINAL-IO* nil)

(defun input-stream (designator)
  (case designator
    ((nil)	*STANDARD-INPUT*)
    ((t)	*TERMINAL-IO*)
    (t		designator)))

(defun output-stream (designator)
  (case designator
    ((nil)	*STANDARD-OUTPUT*)
    ((t)	*TERMINAL-IO*)
    (t		designator)))

(defun INPUT-STREAM-P (stream)
  (let ((direction (STREAM-direction stream)))
    (or (eq direction (kw INPUT))
	(eq direction (kw IO)))))

(defun OUTPUT-STREAM-P (stream)
  (let ((direction (STREAM-direction stream)))
    (or (eq direction (kw OUTPUT))
	(eq direction (kw IO)))))

(defun INTERACTIVE-STREAM-P (stream)
  (ecase (TYPE-OF stream)
    (STREAM			T)
    (BROADCAST-STREAM		nil)
    (CONCATENATED-STREAM	nil)
    (ECHO-STREAM		(INTERACTIVE-STREAM-P
				 (ECHO-STREAM-INPUT-STREAM stream)))
    (FILE-STREAM		nil)
    (STRING-STREAM		nil)
    (SYNONYM-STREAM		(INTERACTIVE-STREAM-P
				 (symbol-value
				  (SYNONYM-STREAM-SYMBOL stream))))
    (TWO-WAY-STREAM		(and
				 (INTERACTIVE-STREAM-P
				  (TWO-WAY-STREAM-INPUT-STREAM stream))
				 (INTERACTIVE-STREAM-P
				  (TWO-WAY-STREAM-OUTPUT-STREAM stream))))))

(defun OPEN-STREAM-P (stream)
  (STREAM-openp stream))

;;; STREAM-ELEMENT-TYPE defined by defstruct.

;;; STREAMP defined by defstruct.

(defun READ-BYTE (&rest args)
  (CHAR-CODE (apply #'READ-CHAR args)))

(defun WRITE-BYTE (byte &rest args)
  (apply #'WRITE-CHAR (CHAR-CODE byte) args))

(defun* PEEK-CHAR (&optional peek-type stream (eof-error-p T)
			     eof-value recursive-p)
  (loop
   (let ((char (READ-CHAR stream eof-error-p eof-value recursive-p)))
     (cond
       ((EQL char eof-value)
	(return-from PEEK-CHAR eof-value))
       ((or (eq peek-type nil)
	    (and (eq peek-type T) (not (whitespacep char)))
	    (and (not (eq peek-type T)) (CHAR= char peek-type)))
	(UNREAD-CHAR char stream)
	(return-from PEEK-CHAR char))))))

(defun* READ-CHAR (&optional stream-designator (eof-error-p T)
			     eof-value recursive-p)
  (let ((stream (input-stream stream-designator)))
    (when (STREAM-unread-buffer stream)
      (return-from READ-CHAR (pop (STREAM-unread-buffer stream))))
    (let* ((fn (STREAM-read-fn stream))
	   (char (funcall (or fn (stream-error stream)) stream)))
      (if (eq char :eof)
	  (if eof-error-p
	      (ERROR 'END-OF-FILE (kw STREAM) stream)
	      eof-value)
	  char))))

(cl:defun read-char-exclusive-ignoring-arg (arg)
  (let ((char (read-char-exclusive)))
    (cl-char (if (eq char 13) 10 char))))

(cl:defun READ-CHAR-NO-HANG (&OPTIONAL stream-designator (eof-error-p T)
				       eof-value recursive-p)
  (let ((stream (input-stream stream-designator)))
    (if (eq (STREAM-read-fn stream)
	    (cl:function read-char-exclusive-ignoring-arg))
	(when (LISTEN stream)
	  (READ-CHAR stream stream eof-error-p eof-value recursive-p))
	(READ-CHAR stream stream eof-error-p eof-value recursive-p))))

(cl:defun TERPRI (&OPTIONAL stream-designator)
  (let ((stream (output-stream stream-designator)))
    (WRITE-CHAR (ch 10) stream))
  nil)

(cl:defun FRESH-LINE (&OPTIONAL stream-designator)
  (let ((stream (output-stream stream-designator)))
    (unless (if (bufferp (STREAM-content stream))
		(with-current-buffer (STREAM-content stream)
		  (eql (char-before (point)) (ch 10)))
		(STREAM-fresh-line-p stream))
      (TERPRI stream))))

(cl:defun UNREAD-CHAR (char &OPTIONAL stream-designator)
  (let ((stream (input-stream stream-designator)))
    (if (STREAM-position stream)
	(when (> (STREAM-position stream) 0)
	  (decf (STREAM-position stream)))
	(push char (STREAM-unread-buffer stream)))))

(cl:defun WRITE-CHAR (char &OPTIONAL stream-designator)
  (let* ((stream (output-stream stream-designator))
	 (fn (STREAM-write-fn stream)))
    (unless fn
      (stream-error stream))
    (funcall fn char stream)
    (setf (STREAM-fresh-line-p stream) (ch= char 10))
    char))

(cl:defun READ-LINE (&OPTIONAL stream-designator (eof-error-p T)
			       eof-value recursive-p)
  (let ((stream (input-stream stream-designator))
	(line ""))
    (catch 'READ-LINE
      (loop
       (let ((char (READ-CHAR stream eof-error-p eof-value recursive-p)))
	 (cond
	   ((EQL char eof-value)
	    (throw 'READ-LINE
	      (cl:values (if (= (length line) 0) eof-value line) t)))
	   ((ch= char 10)
	    (throw 'READ-LINE (cl:values line nil))))
	 (setq line (concat line (list (CHAR-CODE char)))))))))

(cl:defun WRITE-STRING (string &OPTIONAL stream-designator &KEY (START 0) END)
  (unless END
    (setq END (LENGTH string)))
  (do ((stream (output-stream stream-designator))
       (i START (1+ i)))
      ((>= i END) string)
    (WRITE-CHAR (CHAR string i) stream)))

(cl:defun WRITE-LINE (string &OPTIONAL stream-designator &KEY (START 0) END)
  (let ((stream (output-stream stream-designator)))
    (WRITE-STRING string stream (kw START) START (kw END) END)
    (TERPRI stream)
    string))

(cl:defun READ-SEQUENCE (seq stream &KEY (START 0) END)
  (unless END
    (setq END (LENGTH seq)))
  (catch 'READ-SEQUENCE
    (do ((i START (1+ i)))
	((eq i END)
	 i)
      (let ((char (READ-CHAR stream nil)))
	(if (null char)
	    (throw 'READ-SEQUENCE i)
	    (setf (ELT seq i) char))))))

(cl:defun WRITE-SEQUENCE (seq stream &KEY (START 0) END)
  (unless END
    (setq END (LENGTH seq)))
  (do ((i START (1+ i)))
      ((eq i END)
       seq)
    (WRITE-CHAR (ELT seq i) stream)))

(defun FILE-LENGTH (stream)
  (unless (TYPEP stream 'FILE-STREAM)
    (type-error stream 'FILE-STREAM))
  (let ((len (file-attributes (FILE-STREAM-filename stream))))
    (cond
      ((integerp len)	len)
      ((null len)	nil)
      ;; TODO: return integer
      ((floatp len)	len)
      (t		(error "?")))))

(defun FILE-POSITION (stream &optional position)
  (if position
      ;; TODO: implement setting position
      (progn
	(setf (STREAM-position stream))
	T)
      (STREAM-position stream)))

(defun FILE-STRING-LENGTH (stream object)
  (LENGTH (let ((s (MAKE-STRING-OUTPUT-STREAM)))
	    (unwind-protect
		 (PRINT object s)
	      (CLOSE s)))))

(cl:defun OPEN (filespec &KEY (DIRECTION (kw INPUT)) (ELEMENT-TYPE 'CHARACTER)
		              IF-EXISTS IF-DOES-NOT-EXIST
			      (EXTERNAL-FORMAT (kw DEFAULT)))
  (setq filespec (NAMESTRING (MERGE-PATHNAMES filespec)))
  (mk-FILE-STREAM
   (kw direction) DIRECTION
   (kw filename) filespec
   (kw content) (let ((buffer (create-file-buffer filespec)))
		  (when (eq DIRECTION (kw INPUT))
		    (save-current-buffer
		      (set-buffer buffer)
		      (insert-file-contents-literally filespec)))
		  buffer)
   (kw position) 0
   (kw read-fn)
     (lambda (stream)
       (save-current-buffer
	 (set-buffer (STREAM-content stream))
	 (if (= (STREAM-position stream) (buffer-size))
	     :eof
	     (cl-char (char-after (incf (STREAM-position stream)))))))
   (kw write-fn)
     (lambda (char stream)
       (with-current-buffer (STREAM-content stream)
	 (goto-char (incf (STREAM-position stream)))
	 (insert (el-char char))))))

(defun STREAM-EXTERNAL-FORMAT (stream)
  (kw DEFAULT))

(defmacro* WITH-OPEN-FILE ((stream filespec &rest options) &body body)
  `(WITH-OPEN-STREAM (,stream (OPEN ,filespec ,@options))
     ,@body))

(cl:defmacro WITH-OPEN-FILE ((stream filespec &rest options) &body body)
  `(WITH-OPEN-STREAM (,stream (OPEN ,filespec ,@options))
     ,@body))

(cl:defun CLOSE (stream &KEY ABORT)
  (cond
    ((STREAM-openp stream)
     (when (and (TYPEP stream 'FILE-STREAM)
		(OUTPUT-STREAM-P stream))
       (save-current-buffer
	 (set-buffer (STREAM-content stream))
	 (write-region 1 (1+ (buffer-size)) (FILE-STREAM-filename stream))))
     (when (bufferp (STREAM-content stream))
       (kill-buffer (STREAM-content stream)))
     (setf (STREAM-openp stream) nil)
     T)
    (t
     nil)))

(cl:defmacro WITH-OPEN-STREAM ((var stream) &body body)
  `(LET ((,var ,stream))
     (UNWIND-PROTECT
	  (PROGN ,@body)
       (CLOSE ,var))))

(defmacro* WITH-OPEN-STREAM ((var stream) &body body)
  `(let ((,var ,stream))
     (unwind-protect
	  (progn ,@body)
       (CLOSE ,var))))

(cl:defun LISTEN (&OPTIONAL stream-designator)
  (let ((stream (input-stream stream-designator)))
     (if (eq (STREAM-read-fn stream)
	     (cl:function read-char-exclusive-ignoring-arg))
	 (not (sit-for 0))
	 (not (eq (PEEK-CHAR nil stream :eof) :eof)))))

(defun CLEAR-INPUT (&optional stream-designator)
  (let ((stream (input-stream stream-designator)))
    (when (eq (STREAM-read-fn stream)
	      (cl:function read-char-exclusive-ignoring-arg))
      (while (LISTEN stream)
	(READ-CHAR stream)))))

(defun FINISH-OUTPUT (&optional stream-designator)
  (let ((stream (output-stream stream-designator)))
    nil))

(defun FORCE-OUTPUT (&optional stream-designator)
  (let ((stream (output-stream stream-designator)))
    nil))

(defun CLEAR-OUTPUT (&optional stream-designator)
  (let ((stream (output-stream stream-designator)))
    nil))

(defun Y-OR-N-P (&optional format &rest args)
  (when format
    (FRESH-LINE *QUERY-IO*)
    (apply #'FORMAT *QUERY-IO* format args))
  (catch 'Y-OR-N-P
    (loop
     (let ((char (READ-CHAR *QUERY-IO*)))
       (cond
	 ((CHAR-EQUAL char (ch 89))
	  (throw 'Y-OR-N-P T))
	 ((CHAR-EQUAL char (ch 78))
	  (throw 'Y-OR-N-P nil))
	 (t
	  (WRITE-LINE "Please answer 'y' or 'n'. ")))))))

(defun YES-OR-NO-P (&optional format &rest args)
  (when format
    (FRESH-LINE *QUERY-IO*)
    (apply #'FORMAT *QUERY-IO* format args))
  (catch 'YES-OR-NO-P
    (loop
     (let ((line (READ-LINE *QUERY-IO*)))
       (cond
	 ((STRING-EQUAL line "yes")
	  (throw 'YES-OR-NO-P T))
	 ((STRING-EQUAL line "no")
	  (throw 'YES-OR-NO-P nil))
	 (t
	  (WRITE-LINE "Please answer 'yes' or 'no'. ")))))))

(defun MAKE-SYNONYM-STREAM (symbol)
  (mk-SYNONYM-STREAM
   (kw SYMBOL) symbol
   (kw read-fn)
     (lambda (stream)
       (let ((s (symbol-value (SYNONYM-STREAM-SYMBOL stream))))
	 (funcall (STREAM-read-fn s) s)))
   (kw write-fn)
     (lambda (char stream)
       (let ((s (symbol-value (SYNONYM-STREAM-SYMBOL stream))))
	 (funcall (STREAM-read-fn s) char s)))))

;;; SYNONYM-STREAM-SYMBOL defined by defstruct.

;;; BROADCAST-STREAM-STREAMS defined by defstruct.

(defun MAKE-BROADCAST-STREAM (&rest streams)
  (mk-BROADCAST-STREAM
   (kw direction) (kw OUTPUT)
   (kw STREAMS) streams
   (kw write-fn) (lambda (char stream)
		   (dolist (s (BROADCAST-STREAM-STREAMS stream))
		     (WRITE-CHAR char s)))))

(defun MAKE-TWO-WAY-STREAM (input output)
  (mk-TWO-WAY-STREAM
   (kw direction) (kw IO)
   (kw INPUT-STREAM) input
   (kw OUTPUT-STREAM) output
   (kw read-fn)
     (lambda (stream)
       (READ-CHAR (TWO-WAY-STREAM-INPUT-STREAM stream)))
   (kw write-fn)
     (lambda (char stream)
       (WRITE-CHAR char (TWO-WAY-STREAM-OUTPUT-STREAM stream)))))

;;; TWO-WAY-STREAM-INPUT-STREAM and TWO-WAY-STREAM-OUTPUT-STREAM
;;; defined by defstruct.

;;; ECHO-STREAM-INPUT-STREAM and ECHO-STREAM-OUTPUT-STREAM defined
;;; by defstruct.

(defun MAKE-ECHO-STREAM (input output)
  (mk-ECHO-STREAM
   (kw direction) (kw INPUT)
   (kw INPUT-STREAM) input
   (kw OUTPUT-STREAM) output
   (kw read-fn)
     (lambda (stream)
       (let ((char (READ-CHAR (ECHO-STREAM-INPUT-STREAM stream))))
	 (WRITE-CHAR char (ECHO-STREAM-OUTPUT-STREAM stream))
	 char))))

;;; CONCATENATED-STREAM-STREAMS defined by defstruct.

(defun MAKE-CONCATENATED-STREAM (&rest streams)
  (mk-CONCATENATED-STREAM
   (kw direction) (kw INPUT)
   (kw STREAMS) streams
   (kw read-fn)
     (lambda (stream)
       (let ((streams (CONCATENATED-STREAM-STREAMS stream)))
	 (if (null streams)
	     :eof
	     (let ((char (READ-CHAR (first streams) nil)))
	       (if (null char)
		   (progn
		     (pop (CONCATENATED-STREAM-STREAMS stream))
		     (funcall (STREAM-read-fn stream) stream))
		   char)))))))

(defun GET-OUTPUT-STREAM-STRING (stream)
  (STRING-STREAM-string stream))

(cl:defun MAKE-STRING-INPUT-STREAM (string &OPTIONAL (start 0) end)
  (mk-STRING-STREAM
   (kw direction) (kw INPUT)
   (kw string) (if (> (length string) 0) string :eof)
   (kw position) start
   (kw end) (or end (LENGTH string))
   (kw read-fn)
     (lambda (stream)
       (cond
	 ((eq (STRING-STREAM-string stream) :eof)
	  :eof)
	 ((= (STREAM-position stream) (STREAM-end stream))
	  (setf (STRING-STREAM-string stream) :eof))
	 (t
	  (CHAR (STRING-STREAM-string stream)
		(1- (incf (STREAM-position stream)))))))))

(cl:defun MAKE-STRING-OUTPUT-STREAM (&KEY (ELEMENT-TYPE 'CHARACTER))
  (mk-STRING-STREAM
   (kw direction) (kw OUTPUT)
   (kw string) ""
   (kw write-fn)
     (lambda (char stream)
       (setf (STRING-STREAM-string stream)
	     (concat (STRING-STREAM-string stream)
		     (list (el-char char)))))))

(cl:defmacro WITH-INPUT-FROM-STRING ((var string &key INDEX START END)
				     &body body)
  ;; TODO: INDEX
  (when (null START)
    (setq START 0))
  `(WITH-OPEN-STREAM (,var (MAKE-STRING-INPUT-STREAM ,string ,START ,END))
     ,@body))

(defmacro* WITH-OUTPUT-TO-STRING ((var &optional string) &body body)
  (if string
      `(WITH-OPEN-STREAM (,var (make-fill-pointer-output-stream ,string))
	 ,@body)
      `(WITH-OPEN-STREAM (,var (MAKE-STRING-OUTPUT-STREAM))
	 ,@body
	 (GET-OUTPUT-STREAM-STRING ,var))))

(cl:defmacro WITH-OUTPUT-TO-STRING ((var &optional string &key ELEMENT-TYPE)
				    &body body)
  (when (null ELEMENT-TYPE)
    (setq ELEMENT-TYPE '(QUOTE CHARACTER)))
  (if string
      `(WITH-OPEN-STREAM (,var (make-fill-pointer-output-stream ,string))
	 ,@body)
      `(WITH-OPEN-STREAM (,var (MAKE-STRING-OUTPUT-STREAM
				,(kw ELEMENT-TYPE) ,ELEMENT-TYPE))
	 ,@body
	 (GET-OUTPUT-STREAM-STRING ,var))))

(DEFVAR *DEBUG-IO* nil)
(DEFVAR *ERROR-OUTPUT* nil)
(DEFVAR *QUERY-IO* nil)
;;; *STANDARD-INPUT* defined above.
;;; *STANDARD-OUTPUT* defined above.
(DEFVAR *TRACE-OUTPUT* nil)
;;; *TERMINAL-IO* defined above.

;;; STREAM-ERROR, STREAM-ERROR-STREAM, and END-OF-FILE defined by
;;; cl-conditions.el.


(defun make-buffer-output-stream (buffer)
  (MAKE-STREAM (kw direction) (kw OUTPUT)
	       (kw content) buffer
	       (kw write-fn) (lambda (char stream)
			       (with-current-buffer (STREAM-content stream)
				 (insert (el-char char)))
			       (when (ch= char 10)
				 (sit-for 0)))))

(defun make-buffer-input-stream (buffer)
  (MAKE-STREAM
   (kw direction) (kw INPUT)
   (kw content) buffer
   (kw position) 0
   (kw read-fn)
   (lambda (stream)
     (with-current-buffer (STREAM-content stream)
       (if (= (STREAM-position stream) (buffer-size))
	   :eof
	   (cl-char (char-after (incf (STREAM-position stream)))))))))

(defun make-read-char-exclusive-input-stream ()
  (MAKE-STREAM (kw direction) (kw INPUT)
	       (kw read-fn) (cl:function read-char-exclusive-ignoring-arg)
	       (kw position) nil))

(defun make-fill-pointer-output-stream (string)
  (mk-STRING-STREAM (kw direction) (kw OUTPUT)
		    (kw string) string
		    (kw write-fn) (lambda (char stream)
				    (VECTOR-PUSH-EXTEND
				     char
				     (STRING-STREAM-string stream)))))

(defun make-princ-stream ()
  (MAKE-STREAM (kw direction) (kw OUTPUT)
	       (kw write-fn)
	         (lambda (char stream) (princ (string (el-char char))))))
