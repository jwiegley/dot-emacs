;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 20, Files.

(IN-PACKAGE "EMACS-CL")

(defun file-error (pathname)
  (ERROR 'FILE-ERROR (kw PATHNAME) pathname))

(defun wild-directories (name dir pathname files)
  (if (null dir)
      (nconc (DIRECTORY (MERGE-PATHNAMES name pathname)) files)
      (let ((component (first dir)))
	(setq dir (rest dir))
	(cond
	  ((eq component (kw WILD))
	   (dolist (file (directory-files name) files)
	     (unless (or (string= file ".") (string= file ".."))
	       (setq file (concat name file "/"))
	       (when (file-directory-p file)
		 (setq files (wild-directories file dir pathname files))))))
	  ((eq component (kw WILD-INFERIORS))
	   (setq files (wild-directories name dir pathname files))
	   (dolist (file (directory-files name) files)
	     (unless (or (string= file ".") (string= file ".."))
	       (setq file (concat name file "/"))
	       (when (file-directory-p file)
		 (setq files (wild-directories
			      file (cons (kw WILD-INFERIORS) dir)
			      pathname files))))))
	  ((eq component (kw UP))
	   (wild-directories (concat name "../") dir pathname files))
	  ((eq component (kw BACK))
	   (ERROR ":BACK isn't supported"))
	  (t
	   (let ((file (concat name component "/")))
	     (if (file-directory-p file)
		 (wild-directories file dir pathname files)
		 files)))))))

(defun DIRECTORY (pathname-designator)
  (let ((pathname (MERGE-PATHNAMES pathname-designator)))
    (if (WILD-PATHNAME-P pathname (kw DIRECTORY))
	(let* ((dir (PATHNAME-DIRECTORY pathname))
	       (x (pop dir))
	       (name (cond
		       ((eq x (kw ABSOLUTE)) "/")
		       ((or (null x) (eq x (kw RELATIVE))) "./")
		       (t (error "error")))))
	  (wild-directories name dir pathname nil))
	(let ((result nil)
	      (dir (MAKE-PATHNAME (kw DIRECTORY)
				  (PATHNAME-DIRECTORY pathname))))
	  (dolist (file (directory-files (DIRECTORY-NAMESTRING pathname)))
	    (setq file (MERGE-PATHNAMES file dir))
	    (when (PATHNAME-MATCH-P file pathname)
	      (push file result)))
	  result))))

(defun PROBE-FILE (pathname-designator)
  (let ((pathname (MERGE-PATHNAMES pathname-designator)))
    (when (file-exists-p (NAMESTRING pathname))
      (TRUENAME pathname))))

(cl:defun ENSURE-DIRECTORIES-EXIST (pathname-designator &KEY VERBOSE)
  (let* ((pathname (MERGE-PATHNAMES pathname-designator))
	 (dir (DIRECTORY-NAMESTRING pathname)))
    (when (or (eq (PATHNAME-HOST pathname) (kw WILD))
	      (eq (PATHNAME-DEVICE pathname) (kw WILD))
	      (or (memq (kw WILD) (PATHNAME-DIRECTORY pathname))
		  (memq (kw WILD-INFERIORS) (PATHNAME-DIRECTORY pathname))))
      (ERROR 'FILE-ERROR))
    (cl:values pathname-designator
	       (unless (file-exists-p dir)
		 (make-directory dir t)
		 T))))

(defun TRUENAME (pathname-designator)
  (let ((pathname (MERGE-PATHNAMES pathname-designator)))
    (PATHNAME (file-truename (NAMESTRING pathname)))))

(defun FILE-AUTHOR (pathname-designator)
  (let ((pathname (MERGE-PATHNAMES pathname-designator)))
    (user-login-name (nth 2 (file-attributes (NAMESTRING pathname))))))

(defun FILE-WRITE-DATE (pathname-designator)
  (let* ((pathname (MERGE-PATHNAMES pathname-designator))
	 (filename (NAMESTRING pathname))
	 (x (nth 5 (file-attributes filename)))
	 (y (first x))
	 (z (second x)))
    (when (null x)
      (file-error pathname))
    (cl:+ (binary* y 65536) z universal-time-offset)))

(defun RENAME-FILE (old-pathname-designator new-pathname-designator)
  (let* ((old-pathname (MERGE-PATHNAMES old-pathname-designator))
	 (new-pathname (MERGE-PATHNAMES new-pathname-designator old-pathname)))
    (rename-file (NAMESTRING old-pathname) (NAMESTRING new-pathname) t)
    (cl:values new-pathname (TRUENAME old-pathname) (TRUENAME new-pathname))))

(defun DELETE-FILE (pathname-designator)
  (let* ((pathname (MERGE-PATHNAMES pathname-designator))
	 (filename (NAMESTRING pathname)))
    (if (file-exists-p filename)
	(delete-file filename)
	(file-error pathname))
    T))

;;; FILE-ERROR and FILE-ERROR-PATHNAME are defined in cl-conditions.el.
