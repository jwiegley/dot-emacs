;; By W. Schelter
;; Usage: (si::proclaim-file "foo.lsp") (compile-file "foo.lsp")

;; Was 'si, but I changed it to :user.  Scott D. Anderson, 2/28/95
(in-package :user)

;; You may wish to adjust the following to output the proclamations
;; for inclusion in a file.  All fixed arg functions should be proclaimed
;; before their references for maximum efficiency.

;; CAVEAT: The following code only checks for fixed args, it does
;; not check for single valuedness BUT does make a proclamation
;; to that efect.  Unfortunately it is impossible to tell about
;; multiple values without doing a full compiler type pass over 
;; all files in the relevant system.   However the AKCL compiler should
;; warn if you inadvertantly proclaim foo to be single valued and then try
;; to use more than one value.  

(DEFVAR *DECLARE-T-ONLY* NIL)
(DEFUN PROCLAIM-FILE (NAME &OPTIONAL *DECLARE-T-ONLY*)
  (WITH-OPEN-FILE 
      (FILE NAME
            :DIRECTION :INPUT)
    (LET ((EOF (CONS NIL NIL)))
      (LOOP
       (LET ((FORM (READ FILE NIL EOF)))
         (COND ((EQ EOF FORM) (RETURN NIL))
               ((MAKE-DECLARE-FORM FORM ))))))))

(DEFUN MAKE-DECLARE-FORM (FORM)
; !!!
  (WHEN
        (LISTP FORM)
   (COND ((MEMBER (CAR FORM) '(EVAL-WHEN ))
          (DOLIST (V (CDDR FORM)) (MAKE-DECLARE-FORM V)))
         ((MEMBER (CAR FORM) '(PROGN ))
          (DOLIST (V (CDR FORM)) (MAKE-DECLARE-FORM V)))
         ((MEMBER (CAR FORM) '(IN-PACKAGE DEFCONSTANT))
          (EVAL FORM))
         ((MEMBER (CAR FORM) '(DEFUN))
          (COND
           ((AND
             (CONSP (CADDR FORM))
             (NOT (MEMBER '&REST (CADDR FORM)))
             (NOT (MEMBER '&BODY (CADDR FORM)))
             (NOT (MEMBER '&KEY (CADDR FORM)))
             (NOT (MEMBER '&OPTIONAL (CADDR FORM))))
             ;;could print  declarations here.
	    (print (list (cadr form) (ARG-DECLARES (THIRD FORM) (cdddr FORM))))
            ;; The following in not legal Common Lisp syntax.  Scott D. Anderson 3/1/95
            #+old
            (FUNCALL 'PROCLAIM
                     (LIST  'FUNCTION
                            (CADR FORM)
			    (ARG-DECLARES (THIRD FORM) (cdddr FORM))
                            T))
            ;; The following is my substitution.  Scott D. Anderson 3/1/95
            (funcall 'proclaim
                     `(ftype (function ,(arg-declares (third form) (cdddr form)) t)
			     ,(cadr form)))))))))

(DEFUN ARG-DECLARES (ARGS DECLS &AUX ANS)
  (COND ((STRINGP (CAR DECLS)) (SETQ DECLS (CADR DECLS)))
	(T (SETQ DECLS (CAR DECLS))))
  (COND ((AND (not *declare-t-only*)
	       (CONSP DECLS) (EQ (CAR DECLS ) 'DECLARE))
	 (DO ((V ARGS (CDR V)))
	     ((OR (EQ (CAR V) '&AUX)
		  (NULL V))
	      (NREVERSE ANS))
	     (PUSH (DECL-TYPE (CAR V) DECLS) ANS)))
	(T (MAKE-LIST (- (LENGTH args)
			 (LENGTH (MEMBER '&AUX args)))
		      :INITIAL-ELEMENT T))))

(DEFUN DECL-TYPE (V DECLS)
  (DOLIST (D (CDR DECLS))
	  (CASE (CAR D)
		(TYPE (IF (MEMBER V (CDDR D))
			(RETURN-FROM DECL-TYPE (SECOND D))))
		((FIXNUM CHARACTER FLOAT LONG-FLOAT SHORT-FLOAT )
		 (IF (MEMBER V (CDR D)) (RETURN-FROM DECL-TYPE (CAR D))))))
  T)
			    
	      