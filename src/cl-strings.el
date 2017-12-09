;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 16, Strings.

(IN-PACKAGE "EMACS-CL")

;;; System Class STRING

;;; Type BASE-STRING

;;; Type SIMPLE-STRING

;;; Type SIMPLE-BASE-STRING

(defun SIMPLE-STRING-P (object)
  (stringp object))

(defun CHAR (string index)
  (cond
    ((SIMPLE-STRING-P string)
     (SCHAR string index))
    ((STRINGP string)
     (SCHAR (aref string 2) index))
    (t
     (type-error string 'STRING))))

(defsetf CHAR (string index) (char)
  `(cond
    ((SIMPLE-STRING-P ,string)
     (setf (SCHAR ,string ,index) ,char))
    ((STRINGP ,string)
     (setf (SCHAR (aref ,string 2) ,index) ,char))
    (t
     (type-error ,string 'STRING))))

(DEFINE-SETF-EXPANDER CHAR (string index)
  (let ((obj (gensym))
	(stemp (gensym))
	(itemp (gensym)))
    (cl:values (list stemp itemp)
	       (list string index)
	       (list obj)
	       `(SET-CHAR ,obj ,stemp ,itemp)
	       `(CHAR ,stemp ,itemp))))

(defun SET-CHAR (char string index)
  (cond
    ((SIMPLE-STRING-P string)
     (SET-SCHAR char string index))
    ((STRINGP string)
     (SET-SCHAR char (aref string 2) index))
    (t
     (type-error string 'STRING))))

(if use-character-type-p
    (defun SCHAR (string index)
      (aref string index))
    (defun SCHAR (string index)
      (CODE-CHAR (aref string index))))

(if use-character-type-p
    (defsetf SCHAR (string index) (char)
      `(aset ,string ,index ,char))
    (defsetf SCHAR (string index) (char)
      (let ((temp (gensym)))
	`(let ((,temp ,char))
	   (aset ,string ,index (CHAR-CODE ,temp))
	   ,temp))))
	

(DEFINE-SETF-EXPANDER SCHAR (string index)
  (let ((obj (gensym))
	(stemp (gensym))
	(itemp (gensym)))
    (cl:values (list stemp itemp)
	       (list string index)
	       (list obj)
	       `(SET-SCHAR ,obj ,stemp ,itemp)
	       `(SCHAR ,stemp ,itemp))))

(if use-character-type-p
    (defun SET-SCHAR (char string index)
      (aset string index char))
    (defun SET-SCHAR (char string index)
      (aset string index (CHAR-CODE char))
      char))

(defun STRING (x)
  (cond
    ((STRINGP x)	x)
    ((SYMBOLP x)	(SYMBOL-NAME x))
    ((CHARACTERP x)	(MAKE-STRING 1 (kw INITIAL-ELEMENT) x))
    (t			(type-error x '(OR STRING SYMBOL CHARACTER)))))

(cl:defun STRING-UPCASE (string &KEY (START 0) END)
  (NSTRING-UPCASE (COPY-SEQ (STRING string)) (kw START) START (kw END) END))

(cl:defun STRING-DOWNCASE (string &KEY (START 0) END)
  (NSTRING-DOWNCASE (COPY-SEQ (STRING string)) (kw START) START (kw END) END))

(cl:defun STRING-CAPITALIZE (string &KEY (START 0) (END (LENGTH string)))
  (NSTRING-CAPITALIZE (COPY-SEQ (STRING string))
		      (kw START) START (kw END) END))

(cl:defun NSTRING-UPCASE (string &KEY (START 0) END)
  (setq string (STRING string))
  (unless END
    (setq END (LENGTH string)))
  (do ((i START (1+ i)))
      ((eq i END) string)
    (setf (CHAR string i) (CHAR-UPCASE (CHAR string i)))))

(cl:defun NSTRING-DOWNCASE (string &KEY (START 0) END)
  (setq string (STRING string))
  (unless END
    (setq END (LENGTH string)))
  (do ((i START (1+ i)))
      ((eq i END) string)
    (setf (CHAR string i) (CHAR-DOWNCASE (CHAR string i)))))

(cl:defun NSTRING-CAPITALIZE (string &KEY (START 0) (END (LENGTH string)))
  (setq string (STRING string))
  (do* ((i START (1+ i))
	(in-word-p nil))
       ((eq i END)
	string)
    (let* ((char (CHAR string i))
	   (alnump (ALPHANUMERICP char)))
      (when alnump
	(setf (CHAR string i)
	      (if in-word-p (CHAR-DOWNCASE char) (CHAR-UPCASE char))))
      (setq in-word-p alnump))))

(defun STRING-TRIM (chars string)
  (STRING-LEFT-TRIM chars (STRING-RIGHT-TRIM chars string)))

(defun STRING-LEFT-TRIM (chars string)
  (setq string (STRING string))
  (let ((i 0)
	(len (LENGTH string)))
    (while (and (< i len) (FIND (CHAR string i) chars))
      (incf i))
    (SUBSEQ string i)))

(defun STRING-RIGHT-TRIM (chars string)
  (setq string (STRING string))
  (let* ((i (1- (LENGTH string))))
    (while (and (>= i 0) (FIND (CHAR string i) chars))
      (decf i))
    (SUBSEQ string 0 (1+ i))))

(cl:defun STRING= (string1 string2 &KEY (START1 0) END1 (START2 0) END2)
  (setq string1 (STRING string1))
  (setq string2 (STRING string2))
  (string= (substring string1 START1 END1)
	   (substring string2 START2 END2)))

(cl:defun STRING/= (string1 string2 &KEY (START1 0) END1 (START2 0) END2)
  (not (STRING= string1 string2 (kw START1) START1 (kw END1) END1
				(kw START2) START2 (kw END2) END2)))

(defun cl-string-cmp (string1 string2)
  (let ((len1 (LENGTH string1))
	(len2 (LENGTH string2))
	(i 0))
    (loop
     (when (= i len1)
       (return (cl:values i (if (= i len2) 0 -1))))
     (when (= i len2)
       (return (cl:values i 1)))
     (let ((c1 (CHAR string1 i))
	   (c2 (CHAR string2 i)))
       (cond
	 ((CHAR< c1 c2) (return (cl:values i -1)))
	 ((CHAR> c1 c2) (return (cl:values i 1)))
	 (t (incf i)))))))

(cl:defun STRING< (string1 string2 &KEY (START1 0) END1 (START2 0) END2)
  (MULTIPLE-VALUE-BIND (index cmp)
      (cl-string-cmp (SUBSEQ (STRING string1) START1 END1)
		     (SUBSEQ (STRING string2) START2 END2))
    (when (minusp cmp)
      index)))

(cl:defun STRING> (string1 string2 &KEY (START1 0) END1 (START2 0) END2)
  (MULTIPLE-VALUE-BIND (index cmp)
      (cl-string-cmp (SUBSEQ (STRING string1) START1 END1)
		     (SUBSEQ (STRING string2) START2 END2))
    (when (plusp cmp)
      index)))

(cl:defun STRING<= (string1 string2 &KEY (START1 0) END1 (START2 0) END2)
  (MULTIPLE-VALUE-BIND (index cmp)
      (cl-string-cmp (SUBSEQ (STRING string1) START1 END1)
		     (SUBSEQ (STRING string2) START2 END2))
    (when (not (plusp cmp))
      index)))

(cl:defun STRING>= (string1 string2 &KEY (START1 0) END1 (START2 0) END2)
  (MULTIPLE-VALUE-BIND (index cmp)
      (cl-string-cmp (SUBSEQ (STRING string1) START1 END1)
		     (SUBSEQ (STRING string2) START2 END2))
    (when (not (minusp cmp))
      index)))

(cl:defun STRING-EQUAL (string1 string2 &KEY (START1 0) END1 (START2 0) END2)
  (string= (substring (STRING-UPCASE string1) START1 END1)
	   (substring (STRING-UPCASE string2) START2 END2)))

(cl:defun STRING-NOT-EQUAL (string1 string2 &KEY (START1 0) END1
			                         (START2 0) END2)
  (not (STRING-EQUAL string1 string2 (kw START1) START1 (kw END1) END1
				     (kw START2) START2 (kw END2) END2)))

(cl:defun STRING-LESSP (string1 string2 &KEY (START1 0) END1 (START2 0) END2)
  (STRING< (substring (STRING-UPCASE string1) START1 END1)
	   (substring (STRING-UPCASE string2) START1 END1)))

(cl:defun STRING-GREATERP (string1 string2 &KEY (START1 0) END1
						(START2 0) END2)
  (STRING> (substring (STRING-UPCASE string1) START1 END1)
	   (substring (STRING-UPCASE string2) START1 END1)))

(cl:defun STRING-NOT-GREATERP (string1 string2 &KEY (START1 0) END1
						    (START2 0) END2)
  (STRING<= (substring (STRING-UPCASE string1) START1 END1)
	    (substring (STRING-UPCASE string2) START1 END1)))

(cl:defun STRING-NOT-LESSP (string1 string2 &KEY (START1 0) END1
						 (START2 0) END2)
  (STRING>= (substring (STRING-UPCASE string1) START1 END1)
	    (substring (STRING-UPCASE string2) START1 END1)))

(defun STRINGP (object)
  (or (stringp object)
      (vector-and-typep object 'STRING)))

(if use-character-type-p
    (cl:defun MAKE-STRING (size &KEY INITIAL-ELEMENT ELEMENT-TYPE)
      (make-string size (or INITIAL-ELEMENT ?\000)))
    (cl:defun MAKE-STRING (size &KEY INITIAL-ELEMENT ELEMENT-TYPE)
      (make-string size (if INITIAL-ELEMENT (CHAR-CODE INITIAL-ELEMENT) 0))))
