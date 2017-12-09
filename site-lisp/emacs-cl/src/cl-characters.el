;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003 Lars Brinkhoff.
;;; This file implements operators in chapter 13, Characters.

(IN-PACKAGE "EMACS-CL")

;;; System Class CHARACTER
;;; Type BASE-CHAR
;;; Type STANDARD-CHAR
;;; Type EXTENDED-CHAR

(unless use-character-type-p
  (define-storage-layout char (code)))

(defun CHAR= (&rest chars)
  (apply #'cl:= (mapcar #'CHAR-CODE chars)))

(defun CHAR/= (&rest chars)
  (apply #'cl:/= (mapcar #'CHAR-CODE chars)))

(defun CHAR< (&rest chars)
  (apply #'cl:< (mapcar #'CHAR-CODE chars)))

(defun CHAR> (&rest chars)
  (apply #'cl:> (mapcar #'CHAR-CODE chars)))

(defun CHAR<= (&rest chars)
  (apply #'cl:<= (mapcar #'CHAR-CODE chars)))

(defun CHAR>= (&rest chars)
  (apply #'cl:>= (mapcar #'CHAR-CODE chars)))

(defun char-upcase-code (char)
  (CHAR-CODE (CHAR-UPCASE char)))

(defun CHAR-EQUAL (&rest chars)
  (apply #'cl:= (mapcar #'char-upcase-code chars)))

(defun CHAR-NOT-EQUAL (&rest chars)
  (apply #'cl:/= (mapcar #'char-upcase-code chars)))

(defun CHAR-LESSP (&rest chars)
  (apply #'cl:< (mapcar #'char-upcase-code chars)))

(defun CHAR-GREATERP (&rest chars)
  (apply #'cl:> (mapcar #'char-upcase-code chars)))

(defun CHAR-NOT-GREATERP (&rest chars)
  (apply #'cl:<= (mapcar #'char-upcase-code chars)))

(defun CHAR-NOT-LESSP (&rest chars)
  (apply #'cl:>= (mapcar #'char-upcase-code chars)))

(defun CHARACTER (x)
  (cond
    ((CHARACTERP x)			x)
    ((and (STRINGP x) (= (LENGTH x) 1))	(AREF x 0))
    ((SYMBOLP x)			(CHARACTER (SYMBOL-NAME x)))
    (t
     (error "invalid character designator"))))

(if use-character-type-p
    (fset 'CHARACTERP (symbol-function 'characterp))
    (defun CHARACTERP (char)
      (vector-and-typep char 'CHARACTER)))

(defun ALPHA-CHAR-P (char)
  (or (cl:<= 65 (CHAR-CODE char) 90)
      (cl:<= 97 (CHAR-CODE char) 122)))

(defun ALPHANUMERICP (char)
  (or (DIGIT-CHAR-P char) (ALPHA-CHAR-P char)))

(defun* DIGIT-CHAR (weight &optional (radix 10))
  (when (cl:< weight radix)
    (CODE-CHAR (if (< weight 10)
		   (+ 48 weight)
		   (+ 65 weight -10)))))

(defun* DIGIT-CHAR-P (char &optional (radix 10))
  (let* ((code (CHAR-CODE char))
	 (n (cond
	      ((cl:<= 48 code 57) (- code 48))
	      ((cl:<= 65 code 90) (- code 65 -10))
	      ((cl:<= 95 code 122) (- code 95 -10))
	      (t 99))))
    (if (< n radix) n nil)))

(defun GRAPHIC-CHAR-P (char)
  (let ((code (CHAR-CODE char)))
    (and (>= code 32) (<= code 126))))

(defconst standard-chars
    "\n abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!$\"'(),_-./:;?+<=>#%&*@[\\]{|}`^~")

(if use-character-type-p
    (defun STANDARD-CHAR-P (char)
      (find char standard-chars))
    (defun STANDARD-CHAR-P (char)
      (find (CHAR-CODE char) standard-chars)))

(defun CHAR-UPCASE (char)
  (if (LOWER-CASE-P char)
      (CODE-CHAR (- (CHAR-CODE char) 32))
      char))

(defun CHAR-DOWNCASE (char)
  (if (UPPER-CASE-P char)
      (CODE-CHAR (+ (CHAR-CODE char) 32))
      char))

(defun UPPER-CASE-P (char)
  (cl:<= 65 (CHAR-CODE char) 90))

(defun LOWER-CASE-P (char)
  (cl:<= 97 (CHAR-CODE char) 122))

(defun BOTH-CASE-P (char)
  (or (UPPER-CASE-P char) (LOWER-CASE-P char)))

(if use-character-type-p
    (fset 'CHAR-CODE (symbol-function 'char-to-int))
    (defun CHAR-CODE (char)
      (char-code char)))

(fset 'CHAR-INT (symbol-function 'CHAR-CODE))

(if use-character-type-p
    (defun CODE-CHAR (code)
      (if (and (integerp code) (< code CHAR-CODE-LIMIT))
	  (int-char code)
	  nil))
    (defun CODE-CHAR (code)
      (if (and (integerp code) (< code CHAR-CODE-LIMIT))
	  (vector 'CHARACTER code)
	  nil)))

(DEFCONSTANT CHAR-CODE-LIMIT 256)

(defun NAME-CHAR (name)
  (let ((string (STRING name)))
    (cond
      ((equalp string "Backspace")	(ch 8))
      ((equalp string "Tab")		(ch 9))
      ((equalp string "Newline")	(ch 10))
      ((equalp string "Linefeed")	(ch 10))
      ((equalp string "Page")		(ch 12))
      ((equalp string "Return")		(ch 13))
      ((equalp string "Space")		(ch 32))
      ((equalp string "Rubout")		(ch 127)))))

(defun CHAR-NAME (char)
  (case (CHAR-CODE char)
    (8		"Backspace")
    (9		"Tab")
    (10		"Newline")
    (12		"Page")
    (13		"Return")
    (32		"Space")
    (127	"Rubout")))
