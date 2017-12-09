;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 6, Iteration.

(IN-PACKAGE "EMACS-CL")

(defun var-inits (vars)
  (mapcar (lambda (var)
	    (if (symbolp var)
		var
		`(,(first var) ,(second var))))
	  vars))

(defun var-steps (vars)
  (mappend (lambda (var)
	     (when (and (consp var) (= (length var) 3))
	       `(,(first var) ,(third var))))
	   vars))

(defun expand-do (let setq vars test result forms)
  (with-gensyms (start)
    (MULTIPLE-VALUE-BIND (body decls) (parse-body forms)
      (let ((block `(TAGBODY
		      ,start
		      ,@(when test `((WHEN ,test (RETURN (PROGN ,@result)))))
		      ,@(if decls
		    	    `((LOCALLY (DECLARE ,@decls) ,@body))
		    	    body)
		      ,@(when vars `((,setq ,@(var-steps vars))))
		      (GO ,start))))
	`(BLOCK nil
	   ,(cond
	     (vars	`(,let ,(var-inits vars)
			   ,@(when decls `((DECLARE ,@decls))) ,block))
	     (decls	`(LOCALLY (DECLARE ,@decls) ,block))
	     (t		block)))))))

(cl:defmacro DO (vars (test &rest result) &body body)
  (expand-do 'LET 'PSETQ vars test result body))

(cl:defmacro DO* (vars (test &rest result) &body body)
  (expand-do 'LET* 'SETQ vars test result body))

(cl:defmacro DOTIMES ((var count &optional result) &body body)
  (with-gensyms (end)
    `(DO ((,var 0 (,(INTERN "1+" "CL") ,var))
	  (,end ,count))
         ((,(INTERN ">=" *cl-package*) ,var ,end)
	  (LET ((,var (MAX ,count 0)))
	    ,result))
       ,@body)))

(cl:defmacro DOLIST ((var list &optional result) &body forms)
  (with-gensyms (glist)
    (MULTIPLE-VALUE-BIND (body decls) (parse-body forms)
      `(DO (,var
	    (,glist ,list (CDR ,glist)))
	  ((NULL ,glist)
	   (LET ((,var nil))
	     ,result))
	 (DECLARE ,@decls)
	 (SETQ ,var (CAR ,glist))
	 ,@body))))

;;; LOOP and LOOP-FINISH are implemented in cl-loop.el.
