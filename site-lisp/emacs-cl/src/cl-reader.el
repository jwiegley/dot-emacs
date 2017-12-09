;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 23, Reader.

(IN-PACKAGE "EMACS-CL")

(defvar *backquote-level* 0)

(DEFSTRUCT (READTABLE (:predicate READTABLEP) (:copier nil))
  CASE
  SYNTAX-TYPE
  MACRO-TABLE
  DISPATCH-TABLE)

(defun* COPY-READTABLE (&optional (from *READTABLE*) to)
  (unless from
    (setq from *standard-readtable*))
  (unless to
    (setq to (MAKE-READTABLE)))
  (setf (READTABLE-CASE to) (READTABLE-CASE from))
  (setf (READTABLE-SYNTAX-TYPE to)
	(copy-sequence (READTABLE-SYNTAX-TYPE from)))
  (setf (READTABLE-MACRO-TABLE to)
	(copy-sequence (READTABLE-MACRO-TABLE from)))
  (setf (READTABLE-DISPATCH-TABLE to)
	(let ((hash (make-hash-table :test #'equal)))
	  (maphash (lambda (key val) (setf (gethash key hash) val))
		   (READTABLE-DISPATCH-TABLE from))
	  hash))
  to)

(cl:defun MAKE-DISPATCH-MACRO-CHARACTER (char &OPTIONAL non-terminating-p
					      (readtable *READTABLE*))
  (SET-MACRO-CHARACTER char #'dispatch-reader non-terminating-p readtable)
  T)

(defun* read-token (stream)
  (let (char
	(escape nil)
	(package nil)
	(colons 0)
	(token nil))
    (tagbody
      STEP-1
       (setq char (READ-CHAR stream t nil t))

      (case (char-syntx char)
	(:whitespace
	 (go STEP-1))
	((:terminating-macro :non-terminating-macro)
	 (let* ((fn (GET-MACRO-CHARACTER char))
		(list (MULTIPLE-VALUE-LIST (FUNCALL fn stream char))))
	   (return-from read-token (cl:values (first list)))))
	(:single-escape
	 (setq escape t)
	 (setq char (READ-CHAR stream T nil T))
	 (setq token (concat token (list (CHAR-CODE char))))
	 (go STEP-8))
	(:multiple-escape
	 (go STEP-9))
	(:constituent
	 (setq char (char-convert-case char))))

      STEP-8a
      (cond
	((ch= char 58)
	 (incf colons)
	 (when (or (and package (not (zerop (length token))))
		   (> colons 2))
	   (ERROR 'READER-ERROR))
	 (if (= colons 1)
	     (setq package token))
	 (setq escape nil)
	 (setq token nil))
	(t
	 (setq token (concat token (list (CHAR-CODE char))))))
      STEP-8
      (setq char (READ-CHAR stream nil nil T))
      (when (null char)
	(go STEP-10))
      (case (char-syntx char)
	((:constituent :non-terminating-macro)
	 (setq char (char-convert-case char))
	 (go STEP-8a))
	(:single-escape
	 (setq escape t)
	 (setq char (READ-CHAR stream T nil T))
	 (setq token (concat token (list (CHAR-CODE char))))
	 (go STEP-8))
	(:multiple-escape
	 (go STEP-9))
	(:terminating-macro
	 (UNREAD-CHAR char stream)
	 (go STEP-10))
	(:whitespace
	 (UNREAD-CHAR char stream)
	 (go STEP-10)))

      STEP-9
      (setq escape t)
      (setq char (READ-CHAR stream nil nil T))
      (when (null char)
	(ERROR 'READER-ERROR))
      (case (char-syntx char)
	((:constituent :non-terminating-macro :terminating-macro :whitespace)
	 (setq token (concat token (list (CHAR-CODE char))))
	 (go STEP-9))
	(:single-escape
	 (setq char (READ-CHAR stream T nil T))
	 (setq token (concat token (list (CHAR-CODE char))))
	 (go STEP-9))
	(:multiple-escape
	 (when (null token)
	   (setq token ""))
	 (go STEP-8)))

      STEP-10
      (cl:values package colons token escape))))

(defun* read1 (stream eof-error-p eof-value recursive-p preserve-whitespace
	       &optional return-when-nothing)
  (let (char
	(escape nil)
	(package nil)
	(colons 0)
	(token nil))
    (tagbody
      STEP-1
       (setq char (READ-CHAR stream eof-error-p eof-value recursive-p))
       (when (EQL char eof-value)
	 (return-from read1 eof-value))

      (case (char-syntx char)
	(:whitespace
	 (go STEP-1))
	((:terminating-macro :non-terminating-macro)
	 (let* ((fn (GET-MACRO-CHARACTER char))
		(list (MULTIPLE-VALUE-LIST (FUNCALL fn stream char))))
	   (if (null list)
	       (if return-when-nothing
		   (return-from read1 (cl:values nil t))
		   (go STEP-1))
	       (return-from read1 (cl:values (first list))))))
	(:single-escape
	 (setq escape t)
	 (setq char (READ-CHAR stream T nil T))
	 (setq token (concat token (list (CHAR-CODE char))))
	 (go STEP-8))
	(:multiple-escape
	 (go STEP-9))
	(:constituent
	 (setq char (char-convert-case char))))

      STEP-8a
      (cond
	((ch= char 58)
	 (incf colons)
	 (when (or (and package (not (zerop (length token))))
		   (> colons 2))
	   (ERROR 'READER-ERROR))
	 (if (= colons 1)
	     (setq package token))
	 (setq escape nil)
	 (setq token nil))
	(t
	 (setq token (concat token (list (CHAR-CODE char))))))
      STEP-8
      (setq char (READ-CHAR stream nil nil T))
      (when (null char)
	(go STEP-10))
      (case (char-syntx char)
	((:constituent :non-terminating-macro)
	 (setq char (char-convert-case char))
	 (go STEP-8a))
	(:single-escape
	 (setq escape t)
	 (setq char (READ-CHAR stream T nil T))
	 (setq token (concat token (list (CHAR-CODE char))))
	 (go STEP-8))
	(:multiple-escape
	 (go STEP-9))
	(:terminating-macro
	 (UNREAD-CHAR char stream)
	 (go STEP-10))
	(:whitespace
	 (when preserve-whitespace
	   (UNREAD-CHAR char stream))
	 (go STEP-10)))

      STEP-9
      (setq escape t)
      (setq char (READ-CHAR stream nil nil T))
      (when (null char)
	(ERROR 'READER-ERROR))
      (case (char-syntx char)
	((:constituent :non-terminating-macro :terminating-macro :whitespace)
	 (setq token (concat token (list (CHAR-CODE char))))
	 (go STEP-9))
	(:single-escape
	 (setq char (READ-CHAR stream T nil T))
	 (setq token (concat token (list (CHAR-CODE char))))
	 (go STEP-9))
	(:multiple-escape
	 (when (null token)
	   (setq token ""))
	 (go STEP-8)))

      STEP-10
      (unless *READ-SUPPRESS*
	(return-from read1 (process-token package colons token escape))))))

(defmacro* let-unless (condition bindings &body body)
  `(if ,condition
       ,@body
       (let ,bindings
	 ,@body)))

(cl:defun READ (&OPTIONAL stream (eof-error-p T) eof-value recursive-p)
  (let-unless recursive-p
	    ((*sharp-equal-table* (make-hash-table :test #'equal)))
    (read1 stream eof-error-p eof-value recursive-p nil)))

(cl:defun READ-PRESERVING-WHITESPACE (&OPTIONAL stream (eof-error-p T)
				      eof-value recursive-p)
  (let-unless recursive-p
	    ((*sharp-equal-table* (make-hash-table :test #'equal)))
    (read1 stream eof-error-p eof-value recursive-p t)))

(defmacro* unless-read-suppress-let ((var form) &body body)
  `(let ((,var ,form))
     (unless *READ-SUPPRESS*
       ,@body)))

(defun* READ-DELIMITED-LIST (delimiter &optional (stream *STANDARD-INPUT*)
			                         recursive-p)
  (do ((list nil)
       (char (PEEK-CHAR T stream T nil recursive-p)
	     (PEEK-CHAR T stream T nil recursive-p)))
      ((CHAR= char delimiter)
       (READ-CHAR stream t nil recursive-p)
       (nreverse list))
    (unless-read-suppress-let (object (READ stream t nil recursive-p))
      (push object list))))

(cl:defun READ-FROM-STRING (string &OPTIONAL (eof-error-p T) eof-value
			           &KEY (START 0) END PRESERVE-WHITESPACE)
  (let ((stream (MAKE-STRING-INPUT-STREAM string START END)))
    (cl:values (if PRESERVE-WHITESPACE
		   (READ-PRESERVING-WHITESPACE stream eof-error-p eof-value)
		   (READ stream eof-error-p eof-value))
	       (STREAM-position stream))))

;;; READTABLE-CASE defined by defstruct.

;;; READTABLEP defined by defstruct.

(defun* SET-DISPATCH-MACRO-CHARACTER (disp-char sub-char new-function
				      &optional (readtable *READTABLE*))
  (let ((string (concat (list (CHAR-CODE disp-char) (CHAR-CODE sub-char)))))
    (setf (gethash string (READTABLE-DISPATCH-TABLE readtable))
	  new-function))
  T)

(defun* GET-DISPATCH-MACRO-CHARACTER (disp-char sub-char
				      &optional (readtable *READTABLE*))
  (let ((string (concat (list (CHAR-CODE disp-char) (CHAR-CODE sub-char)))))
    (gethash string (READTABLE-DISPATCH-TABLE readtable))))

(defun* SET-MACRO-CHARACTER (char new-function
			     &optional non-terminating-p
			               (readtable *READTABLE*))
  (setf (aref (READTABLE-MACRO-TABLE readtable) (CHAR-CODE char)) new-function)
  (setf (aref (READTABLE-SYNTAX-TYPE readtable) (CHAR-CODE char))
	(if non-terminating-p
	    :non-terminating-macro
	    :terminating-macro))
  T)

(defun* char-syntx (char &optional (readtable *READTABLE*))
  (aref (READTABLE-SYNTAX-TYPE readtable) (CHAR-CODE char)))

(defun* GET-MACRO-CHARACTER (char &optional (readtable *READTABLE*))
  (cl:values (aref (READTABLE-MACRO-TABLE readtable) (CHAR-CODE char))
	     (eq (char-syntx char readtable) :non-terminating-macro)))

(defun* SET-SYNTAX-FROM-CHAR (to-char from-char
			      &optional (to-readtable *READTABLE*)
			                (from-readtable *standard-readtable*))
  (setf (aref (READTABLE-SYNTAX-TYPE to-readtable) (CHAR-CODE to-char))
	(char-syntx from-char from-readtable))
  T)

(cl:defmacro WITH-STANDARD-IO-SYNTAX (&body body)
  `(LET ((*PACKAGE*			*cl-user-package*)
	 (*PRINT-ARRAY*			T)
	 (*PRINT-BASE*			10)
	 (*PRINT-CASE*			(kw UPCASE))
	 (*PRINT-CIRCLE*		nil)
	 (*PRINT-ESCAPE*		T)
	 (*PRINT-GENSYM*		T)
	 (*PRINT-LENGTH*		nil)
	 (*PRINT-LEVEL*			nil)
	 (*PRINT-LINES*			nil)
	 (*PRINT-MISER-WIDTH*		nil)
	 (*PRINT-PPRINT-DISPATCH*	*initial-pprint-dispatch*)
	 (*PRINT-PRETTY*		nil)
	 (*PRINT-RADIX*			nil)
	 (*PRINT-READABLY*		T)
	 (*PRINT-RIGHT-MARGIN*		nil)
	 (*READ-BASE*			10)
	 (*READ-DEFAULT-FLOAT-FORMAT*	'SINGLE-FLOAT)
	 (*READ-EVAL*			T)
	 (*READ-SUPPRESS*		nil)
	 (*READTABLE*			*standard-readtable*))
     ,@body))

(DEFVAR *READ-BASE* 10)

(DEFVAR *READ-DEFAULT-FLOAT-FORMAT* 'SINGLE-FLOAT)

(DEFVAR *READ-EVAL* T)

(DEFVAR *READ-SUPPRESS* nil)

(message "Loading (defvar *standard-readtable* ...)")

(defvar *standard-readtable*
  (let ((readtable (MAKE-READTABLE)))
    (setf (READTABLE-CASE readtable) (kw UPCASE))

    (setf (READTABLE-SYNTAX-TYPE readtable) (make-vector 256 :constituent))

    (do-plist (char type '(32 :whitespace
			   92 :single-escape
			   124 :multiple-escape))
      (setf (aref (READTABLE-SYNTAX-TYPE readtable) char) type))

    (dolist (char (mapcar #'CODE-CHAR '(9 10 12 13)))
      (SET-SYNTAX-FROM-CHAR char (ch 32) readtable readtable))

    (setf (READTABLE-MACRO-TABLE readtable) (make-vector 256 nil))
    (MAKE-DISPATCH-MACRO-CHARACTER (ch 35) T readtable)

    (do-plist (char fn (list (ch 34) #'double-quote-reader
			     (ch 39) #'quote-reader
			     (ch 40) #'left-paren-reader
			     (ch 41) #'right-paren-reader
			     (ch 44) #'comma-reader
			     (ch 59) #'semicolon-reader
			     (ch 96) #'backquote-reader))
      (SET-MACRO-CHARACTER char fn nil readtable))

    (setf (READTABLE-DISPATCH-TABLE readtable) (make-hash-table :test #'equal))

    (do-plist (char fn (list 92 #'sharp-backslash-reader
			     39 #'sharp-quote-reader
			     40 #'sharp-left-paren-reader
			     42 #'sharp-asterisk-reader
			     58 #'sharp-colon-reader
			     46 #'sharp-dot-reader
			     98 #'sharp-b-reader
			     66 #'sharp-b-reader
			     111 #'sharp-o-reader
			     79 #'sharp-o-reader
			     120 #'sharp-x-reader
			     88 #'sharp-x-reader
			     114 #'sharp-r-reader
			     82 #'sharp-r-reader
			     99 #'sharp-c-reader
			     67 #'sharp-c-reader
			     97 #'sharp-a-reader
			     65 #'sharp-a-reader
			     115 #'sharp-s-reader
			     83 #'sharp-s-reader
			     112 #'sharp-p-reader
			     80 #'sharp-p-reader
			     61 #'sharp-equal-reader
			     35 #'sharp-sharp-reader
			     43 #'sharp-plus-reader
			     45 #'sharp-minus-reader
			     124 #'sharp-bar-reader
			     60 #'sharp-less-reader
			     32 #'sharp-space-reader
			     41 #'sharp-right-paren-reader))
      (SET-DISPATCH-MACRO-CHARACTER (ch 35) (CODE-CHAR char) fn readtable))

    readtable))

(message "Loaded (defvar *standard-readtable* ...)")

(DEFVAR *READTABLE* (COPY-READTABLE nil))

;;; READER-ERROR defined in cl-conditions.el.

(defun whitespacep (char)
  (eq (char-syntx char) :whitespace))

(defun constituentp (char)
  (eq (char-syntx char) :constituent))



(defun dispatch-reader (stream char1)
  (do* ((param nil)
	(char (READ-CHAR stream T nil T) (READ-CHAR stream T nil T))
	(digit (DIGIT-CHAR-P char 10) (DIGIT-CHAR-P char 10)))
      ((not digit)
       (let ((fn (GET-DISPATCH-MACRO-CHARACTER char1 char)))
	 (cond
	   (fn			(FUNCALL fn stream char param))
	   (*READ-SUPPRESS*	(cl:values))
	   (t			nil))))
    (setq param (binary+ (binary* (or param 0) 10) digit))))

(defun double-quote-reader (stream double-quote-char)
  (do ((string "")
       (char (READ-CHAR stream T nil T) (READ-CHAR stream T nil T)))
      ((CHAR= char double-quote-char)
       (cl:values (if *READ-SUPPRESS* nil string)))
    (when (eq (char-syntx char) :single-escape)
      (setq char (READ-CHAR stream T nil T)))
    (unless *READ-SUPPRESS*
      (setq string (concat string (list (CHAR-CODE char)))))))

(defun quote-reader (stream ch)
  (let ((object (READ stream T nil T)))
    (unless *READ-SUPPRESS*
      (cl:values (list 'QUOTE object)))))

(defun* left-paren-reader (stream char)
  (do ((list nil)
       (char (PEEK-CHAR T stream) (PEEK-CHAR T stream)))
      ((ch= char 41)
       (READ-CHAR stream)
       (cl:values (nreverse list)))
    (MULTIPLE-VALUE-BIND (object nothingp) (read1 stream t nil t t t)
      (unless (or *READ-SUPPRESS* nothingp)
	(if (and (symbolp object) (string= (SYMBOL-NAME object) "."))
	    (let ((cdr (READ stream T nil T)))
	      (unless (ch= (READ-CHAR stream) 41)
		(ERROR 'READER-ERROR))
	      (return-from left-paren-reader
		(cl:values (nconc (nreverse list) cdr))))
	    (push object list))))))

(defun right-paren-reader (stream char)
  (unless *READ-SUPPRESS*
    (ERROR "Unbalanced '~A'." char)))

(defun comma-reader (stream char)
  (unless (or (plusp *backquote-level*) *READ-SUPPRESS*)
    (ERROR "Comma outside backquote."))
  (let ((next-char (READ-CHAR stream T nil T)))
    (let ((*backquote-level* (1- *backquote-level*)))
      (cond
	((ch= next-char 64)
	 (unless-read-suppress-let (object (READ stream T nil T))
	   (cl:values (list 'COMMA-AT object))))
	((ch= next-char 46)
	 (unless-read-suppress-let (object (READ stream T nil T))
	   (cl:values (list 'COMMA-DOT object))))
	(t
	 (UNREAD-CHAR next-char stream)
	 (unless-read-suppress-let (object (READ stream T nil T))
	   (cl:values (list 'COMMA object))))))))

(defun semicolon-reader (stream ch)
  (do ()
      ((ch= (READ-CHAR stream nil (ch 10) T) 10)
       (cl:values))))

(defun backquote-reader (stream char)
  (let* ((*backquote-level* (1+ *backquote-level*))
	 (form (READ stream T nil T)))
    (unless *READ-SUPPRESS*
      (cl:values (list 'BACKQUOTE form)))))

(defun no-param (char n)
  (when n
    (WARN "Parameter ~D ignored in #~C." n char)))

(defun sharp-backslash-reader (stream char n)
  (no-param (ch 92) n)
  (do ((token (concat (list (CHAR-CODE (READ-CHAR stream nil (ch 32) T)))))
       (char (READ-CHAR stream nil (ch 32) T)
	     (READ-CHAR stream nil (ch 32) T)))
      ((not (constituentp char))
       (UNREAD-CHAR char stream)
       (cl:values (cond
		    (*READ-SUPPRESS*		nil)
		    ((= (length token) 1)	(CHAR token 0))
		    (t				(NAME-CHAR token)))))
    (unless *READ-SUPPRESS*
      (setq token (concat token (list (CHAR-CODE char)))))))

(defun sharp-quote-reader (stream char n)
  (no-param (ch 39) n)
  (unless-read-suppress-let (object (READ stream T nil T))
    (cl:values (list 'FUNCTION object))))

(defun sharp-left-paren-reader (stream char n)
  (unless-read-suppress-let (list (READ-DELIMITED-LIST (ch 41) stream t))
    (cl:values
      (if (and n (plusp n))
	  (MAP-INTO (MAKE-ARRAY n (kw INITIAL-ELEMENT) (car (last list)))
		    #'IDENTITY list)
	  (CONCATENATE 'VECTOR list)))))

(defun bit-vector (contents n)
  (let* ((len (or n (length contents)))
	 (vec (make-bit-vector len (if (plusp len)
				       (car (last contents))
				       0))))
    (dotimes (i (min len (length contents)) vec)
      (setf (bref vec i) (nth i contents)))))

(defun sharp-asterisk-reader (stream char n)
  (do ((contents nil)
       (char (READ-CHAR stream nil (ch 32) T)
	     (READ-CHAR stream nil (ch 32) T)))
      ((not (constituentp char))
       (UNREAD-CHAR char stream)
       (cl:values (unless *READ-SUPPRESS* (bit-vector (nreverse contents) n))))
    (unless *READ-SUPPRESS*
      (push (ecase (CHAR-CODE char) (48 0) (49 1)) contents))))

(defun sharp-colon-reader (stream char n)
  (no-param (ch 58) n)
  (MULTIPLE-VALUE-BIND (package colons token escape) (read-token stream)
    (cl:values (unless *READ-SUPPRESS* (make-symbol token)))))

(defun sharp-dot-reader (stream char n)
  (no-param (ch 46) n)
  (unless-read-suppress-let (object (READ stream T nil T))
    (if *READ-EVAL*
	(cl:values (EVAL object))
	(ERROR 'READER-ERROR))))

(defun read-in-base (stream base)
  (let* ((*READ-BASE* base)
	 (num (READ stream T nil T)))
    (unless *READ-SUPPRESS*
      (if (RATIONALP num)
	  (cl:values num)
	  (ERROR 'READER-ERROR)))))

(defun sharp-b-reader (stream char n)
  (no-param (ch 66) n)
  (read-in-base stream 2))

(defun sharp-o-reader (stream char n)
  (no-param (ch 66) n)
  (read-in-base stream 8))

(defun sharp-x-reader (stream char n)
  (no-param (ch 66) n)
  (read-in-base stream 16))

(defun sharp-r-reader (stream char n)
  (when (or (null n)
	    (not (cl:<= 2 n 36)))
    (ERROR 'READER-ERROR))
  (read-in-base stream n))

(defun sharp-c-reader (stream char n)
  (no-param (ch 67) n)
  (let ((list (READ stream T nil T)))
    (unless *READ-SUPPRESS*
      (if (and (consp list) (= (length list) 2))
	  (cl:values (COMPLEX (first list) (second list)))
	  (ERROR "#C~S is not valid syntax for complex." list)))))

(defun array-content-dimensions (n contents)
  (cond
    ((zerop n)	nil)
    ((eq n 1)	(list (LENGTH contents)))
    (t		(cons (LENGTH contents)
		      (array-content-dimensions (1- n) (ELT contents 0))))))

(defun sharp-a-reader (stream char n)
  (unless-read-suppress-let (contents (READ stream T nil T))
    (unless n
      (ERROR 'READER-ERROR))
    (MAKE-ARRAY (array-content-dimensions n contents)
		(kw INITIAL-CONTENTS) contents)))

(message "Loading (defun sharp-s-reader ...)")

(defun sharp-s-reader (stream char n)
  (no-param (ch 83) n)
  (unless-read-suppress-let (contents (READ stream T nil T))
    (let ((type (first contents)))
      ;; TODO: Verify that there really is a constructor for the structure.
      (setq contents (cdr contents))
      (do ((list contents (cddr list)))
	  ((null list))
	(setf (car list) (INTERN (STRING (car list)) *keyword-package*)))
      (APPLY (INTERN (concat "MAKE-" (STRING type)) (SYMBOL-PACKAGE type))
	     contents))))

(message "Loaded (defun sharp-s-reader ...)")

(defun sharp-p-reader (stream char n)
  (no-param (ch 80) n)
  (unless-read-suppress-let (string (READ stream T nil T))
    (unless (STRINGP string)
      (ERROR 'READER-ERROR))
    (PARSE-NAMESTRING string)))

(defvar *sharp-equal-table* nil)

(defun replace-sharp-equal (tree object temp)
  (cond
    ((eq tree temp)
     object)
    ((consp tree)
     (RPLACA tree (replace-sharp-equal (car tree) object temp))
     (RPLACD tree (replace-sharp-equal (cdr tree) object temp)))
    ((arrayp tree)
     (dotimes (i (length tree) tree)
       (aset tree i
	     (replace-sharp-equal (aref tree i) object temp))))
    (t
     tree)))

(defun sharp-equal-reader (stream char n)
  (let ((temp nil))
    (unless *READ-SUPPRESS*
      (setf (gethash n *sharp-equal-table*)
	    (setq temp (cons nil nil))))
    (unless-read-suppress-let (object (READ stream T nil T))
      (replace-sharp-equal object object temp)
      (setf (gethash n *sharp-equal-table*) object))))

(defun sharp-sharp-reader (stream char n)
  (unless *READ-SUPPRESS*
    (let ((object (gethash n *sharp-equal-table* not-found)))
      (if (eq object not-found)
	  (ERROR "There is no object labelled #~D#" n)
	  object))))

(defun eval-feature-test (expr)
  (cond
    ((symbolp expr)
     (member expr *FEATURES*))
    ((atom expr)
     (ERROR "~S is not valid syntax in a feature test."))
    ((eq (first expr) (kw NOT))
     (not (eval-feature-test (second expr))))
    ((eq (first expr) (kw AND))
     (every #'eval-feature-test (rest expr)))
    ((eq (first expr) (kw OR))
     (some #'eval-feature-test (rest expr)))
    (t
     (ERROR 'READER-ERROR))))

(defun sharp-plus-reader (stream char n)
  (no-param (ch 43) n)
  (if (eval-feature-test (let ((*PACKAGE* *keyword-package*))
			   (READ stream T nil T)))
      (cl:values (READ stream T nil T))
      (let ((*READ-SUPPRESS* T))
	(READ stream T nil T)
	(cl:values))))

(defun sharp-minus-reader (stream char n)
  (no-param (ch 45) n)
  (if (eval-feature-test (let ((*PACKAGE* *keyword-package*))
			   (READ stream T nil T)))
      (let ((*READ-SUPPRESS* T))
	(READ stream T nil T)
	(cl:values))
      (cl:values (READ stream T nil T))))

(defun sharp-bar-reader (stream char n)
  (no-param (ch 124) n)
  (let ((level 1)
	(last nil)
	(char nil))
    (while (plusp level)
      (setq last char)
      (setq char (READ-CHAR stream T nil T))
      (when (and last (ch= last 35) (ch= char 124))
	(incf level))
      (when (and last (ch= last 124) (ch= char 35))
	(decf level)))
    (cl:values)))

(defun sharp-less-reader (stream char n)
  (ERROR "syntax error"))
(defun sharp-space-reader (stream char n)
  (ERROR "syntax error"))
(defun sharp-right-paren-reader (stream char n)
  (ERROR "syntax error"))



(cl:defmacro BACKQUOTE (form)
  (let ((result (expand-bq form)))
    (if t
	(optimize-bq result)
	result)))

(defun expand-bq (form)
  (cond
    ((consp form)
     (case (car form)
       (COMMA
	(second form))
       ((COMMA-AT COMMA-DOT)
	(ERROR "Syntax error in backquote."))
       (t
	(cons 'APPEND (expand-bq-list form)))))
    ((SIMPLE-VECTOR-P form)
     `(APPLY (FUNCTION VECTOR) ,(expand-bq (MAP 'LIST #'IDENTITY form))))
    (t
     `(QUOTE ,form))))

(defun* expand-bq-list (list)
  (let ((car (car list))
	(cdr (cdr list)))
    (cons
     (if (consp car)
	 (case (first car)
	   (COMMA			`(LIST ,(second car)))
	   ((COMMA-AT COMMA-DOT)	(second car))
	   (t				`(LIST ,(expand-bq car))))
	 (case car
	   (COMMA			(return-from expand-bq-list
					  (list (second list))))
	   ((COMMA-AT COMMA-DOT)	(ERROR "Syntax error in backquote."))
	   (t				`(LIST ,(expand-bq car)))))
     (if (consp cdr)
	 (expand-bq-list cdr)
	 `((QUOTE ,cdr))))))

(defun optimize-bq (form)
  (if (and (consp form)
	   (eq (first form) 'APPEND))
      (progn
	(setf (rest form) (remove-if (lambda (x)
				       (or (null x)
					   (equal x '(QUOTE nil))))
				     (rest form)))
	(let ((list (butlast (rest form)))
	      (tail (car (last (rest form)))))
	  (if (every (lambda (x) (and (consp x) (eq (first x) 'LIST))) list)
	      (progn
		(setq list (mapcar (lambda (x) (optimize-bq (second x)))
				   list))
		(if (and (consp tail) (eq (first tail) 'LIST))
		    `(LIST ,@list ,(second tail))
		    `(LIST* ,@list ,tail)))
	      form)))
      form))



(defun char-convert-case (char)
  (let ((case (READTABLE-CASE *READTABLE*)))
    (cond
      ((eq case (kw PRESERVE))	char)
      ((eq case (kw UPCASE))	(CHAR-UPCASE char))
      ((eq case (kw DOWNCASE))	(CHAR-DOWNCASE char))
      ((eq case (kw INVERT))	(ERROR "TODO: readtable case :invert."))
      (t			(type-error case `(MEMBER ,(kw PRESERVE)
							  ,(kw UPCASE)
							  ,(kw DOWNCASE)
							  ,(kw INVERT)))))))

(defun* process-token (package colons token escape)
  "Process a token and return the corresponding Lisp object.
   PACKAGE is a string, or nil if there was no package prefix.
   COLONS is the number of colons before the token.
   TOKEN is a string, or nil if there was no token after the colons.
   ESCAPE is t if any character in TOKEN was escaped, and nil otherwise."
  (when (and (zerop colons) (not escape))
    (let ((n (parse-number token)))
      (when n
	(return-from process-token n))))
  (when (null package)
    (case colons
      (0 (setq package *PACKAGE*))
      (1 (setq package *keyword-package*))
      (2 (ERROR "Too many colons in token."))))
  (when (null token)
    (ERROR "Token terminated by colon."))
  (MULTIPLE-VALUE-BIND (sym status) (FIND-SYMBOL token package)
    (cl:values
      (cond
	((or (eq status kw:EXTERNAL) (eq status kw:INHERITED))
	 sym)
	((eq status kw:INTERNAL)
	 (if (and (< colons 2) (not (eq package *PACKAGE*)))
	     (ERROR "Internal symbol.")
	     sym))
	((null status)
	 (NTH-VALUE 0 (INTERN token package)))))))

(defun potential-number-p (string)
  (and
   (every (lambda (char)
	    (or (DIGIT-CHAR-P (CODE-CHAR char) *READ-BASE*)
		(find char "+-/.^_DEFLSdefls")))
	  string)
   (or (some ;;(lambda (char) (DIGIT-CHAR-P (CODE-CHAR char)))
	     (compose DIGIT-CHAR-P CODE-CHAR)
	     string)
       (and (some (lambda (char)
		    (DIGIT-CHAR-P (CODE-CHAR char) *READ-BASE*))
		  string)
	    (not (find 46 string))))
   (let ((char (aref string 0)))
     (or (DIGIT-CHAR-P (CODE-CHAR char) *READ-BASE*)
	 (find char "+-.^_")))
   (not (find (aref string (1- (length string))) "+-"))))

(cl:defun parse-number (string)
  (catch 'parse-number
    ;; Cheap test to avoid many expensive computations below.
    (when (and (eq *READ-BASE* 10)
	       (not (string-match "^[-+0-9.]" string)))
      (throw 'parse-number (cl:values nil)))

    (MULTIPLE-VALUE-BIND (integer end)
	(PARSE-INTEGER string (kw RADIX) 10 (kw JUNK-ALLOWED) T)
      ;; First, is it a string of decimal digits followed by a period or an
      ;; exponent marker?  If so, can be either a decimal integer or a float.
      ;; TODO: PARSE-INTEGER doesn't differentiate between 0 and -0, so
      ;; e.g. -0.5 comes out wrong.
      (when (and integer
		 (< end (LENGTH string))
		 (FIND (CHAR string end) ".DEFLSdefls"))
	(if (and (eq (1+ end) (LENGTH string))
		 (ch= (CHAR string end) 46))
	    (throw 'parse-number (cl:values integer))
	    (let ((fraction 0)
		  (exponent 0)
		  (end2 end))
	      (when (ch= (CHAR string end) 46)
		(MULTIPLE-VALUE-SETQ (fraction end2)
		  (PARSE-INTEGER string (kw RADIX) 10 (kw START) (incf end)
				 (kw JUNK-ALLOWED) T))
		(when (eq end end2)
		  (setq fraction 0)))
	      (when (< end2 (LENGTH string))
		(unless (FIND (CHAR string end2) "DEFLSdefls")
		  (ERROR 'READ-ERROR))
		(MULTIPLE-VALUE-SETQ (exponent end2)
		  (PARSE-INTEGER string (kw RADIX) 10
				 (kw START) (1+ end2)
				 (kw JUNK-ALLOWED) T)))
	      (when (= end2 (LENGTH string))
		(case *READ-DEFAULT-FLOAT-FORMAT*
		  ((SHORT-FLOAT SINGLE-FLOAT DOUBLE-FLOAT LONG-FLOAT))
		  (t (ERROR 'PARSE-ERROR)))
		(throw 'parse-number
		  (cl:values
		   (* (+ (FLOAT integer)
			 (* (if (MINUSP integer) -1 1)
			    (FLOAT fraction)
			    (expt 10.0 (- end end2))))
		      (expt 10.0 (FLOAT exponent)))))))))
      ;; Second, is it a period followed by a string of decimal digits?
      ;; TODO: minus sign.
      ;; TODO: exponent.
      (when (and (eq end 0)
		 (> (LENGTH string) 1)
		 (ch= (CHAR string 0) 46))
	(MULTIPLE-VALUE-BIND (fraction end2)
	    (PARSE-INTEGER string (kw RADIX) 10 (kw START) 1
			   (kw JUNK-ALLOWED) T)
	  (when (and integer (= end2 (LENGTH string)))
	    (throw 'parse-number
	      (cl:values
	       (* (FLOAT fraction) (expt 10.0 (- 1 (LENGTH string))))))))))
    ;; Third, try parsing as a number in current input radix.  It can
    ;; be either an integer or a ratio.
    (MULTIPLE-VALUE-BIND (integer end)
	(PARSE-INTEGER string (kw RADIX) *READ-BASE* (kw JUNK-ALLOWED) T)
      (unless integer
	(throw 'parse-number (cl:values nil)))
      (cond
	((= end (LENGTH string))
	 (throw 'parse-number (cl:values integer)))
	((ch= (CHAR string end) 47)
	 (MULTIPLE-VALUE-BIND (denumerator end2)
	     (PARSE-INTEGER string (kw RADIX) *READ-BASE*
			    (kw START) (1+ end) (kw JUNK-ALLOWED) T)
	   (when (and denumerator (= end2 (LENGTH string)))
	     (cl:values (cl:/ integer denumerator)))))))))
