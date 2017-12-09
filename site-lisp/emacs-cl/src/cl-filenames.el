;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 19, Filenames.

(IN-PACKAGE "EMACS-CL")

(define-storage-layout pathname (host device directory name type version))

(defun PATHNAME (pathspec)
  (cond
    ((PATHNAMEP pathspec)
     pathspec)
    ((STRINGP pathspec)
     ;; TODO: parse logical pathnames
     (cl:values (PARSE-NAMESTRING pathspec)))
    ((STREAMP pathspec)
     (PATHNAME (FILE-STREAM-filename pathspec)))
    (t
     (type-error pathspec '(OR PATHNAME STRING STREAM)))))

(defun mkpathname (host device directory name type version)
  (vector 'PATHNAME host device directory name type version))

(defun mklogpathname (host device directory name type version)
  (vector 'LOGICAL-PATHNAME host device directory name type version))

(cl:defun MAKE-PATHNAME (&KEY HOST DEVICE DIRECTORY NAME
			      TYPE VERSION DEFAULTS CASE)
  (unless DEFAULTS
    (setq DEFAULTS (mkpathname (PATHNAME-HOST *DEFAULT-PATHNAME-DEFAULTS*)
			       nil nil nil nil nil)))
  (when (eq DIRECTORY (kw WILD))
    (setq DIRECTORY `(,(kw ABSOLUTE) ,(kw WILD-INFERIORS))))
  (MERGE-PATHNAMES (mkpathname HOST DEVICE DIRECTORY NAME TYPE VERSION)
		   DEFAULTS nil))

(defun PATHNAMEP (object)
  (and (vectorp object)
       (or (eq (aref object 0) 'PATHNAME)
	   (eq (aref object 0) 'LOGICAL-PATHNAME))))

(defun PATHNAME-HOST (pathname-designator)
  (pathname-host (PATHNAME pathname-designator)))

(defun PATHNAME-DEVICE (pathname-designator)
  (pathname-device (PATHNAME pathname-designator)))

(defun PATHNAME-DIRECTORY (pathname-designator)
  (pathname-directory (PATHNAME pathname-designator)))

(defun PATHNAME-NAME (pathname-designator)
  (pathname-name (PATHNAME pathname-designator)))

(defun PATHNAME-TYPE (pathname-designator)
  (pathname-type (PATHNAME pathname-designator)))

(defun PATHNAME-VERSION (pathname-designator)
  (pathname-version (PATHNAME pathname-designator)))

;;; TODO: LOAD-LOGICAL-PATHNAME-TRANSLATIONS

(defvar *logical-pathname-translations* (make-hash-table))

(defun LOGICAL-PATHNAME-TRANSLATIONS (host)
  (gethash host *logical-pathname-translations*))

(defsetf LOGICAL-PATHNAME-TRANSLATIONS (host) (trans)
  `(puthash ,host ,trans *logical-pathname-translations*))

(DEFSETF LOGICAL-PATHNAME-TRANSLATIONS (host) (trans)
  `(puthash ,host ,trans *logical-pathname-translations*))

;;; *DEFAULT-PATHNAME-DEFAULTS* defined below.

(defun maybe-empty (component)
  (cond
    ((null component)			"")
    ((eq component (kw UNSPECIFIC))	"")
    ((eq component (kw NEWEST))		"")
    ((eq component (kw WILD))		"*")
    ((eq component (kw PREVIOUS))	"~")
    ((INTEGERP component)		(format ".~%d~" component))
    (t					component)))

(defun NAMESTRING (pathname-designator)
  (let* ((pathname (PATHNAME pathname-designator))
	 (dir (DIRECTORY-NAMESTRING pathname))
	 (name (FILE-NAMESTRING pathname))
	 (type (maybe-empty (PATHNAME-TYPE pathname)))
	 (ver (maybe-empty (PATHNAME-VERSION pathname))))
    (concat
     dir
     name
     (if (zerop (length type)) "" ".")
     type ver)))

(defun FILE-NAMESTRING (pathname-designator)
  (let* ((pathname (PATHNAME pathname-designator)))
    (maybe-empty (PATHNAME-NAME pathname))))

(defun DIRECTORY-NAMESTRING (pathname-designator)
  (let* ((pathname (PATHNAME pathname-designator))
	 (dir (PATHNAME-DIRECTORY pathname))
	 (string (cond
		   ((null dir) nil)
		   ((atom dir) (error "error"))
		   ((eq (first dir) (kw ABSOLUTE)) "/")
		   ((equal dir (list (kw RELATIVE))) "./")
		   (t ""))))
    (dolist (x (rest dir) string)
      (setq string
	    (concat string
		    (cond
		      ((STRINGP x)	x)
		      ((eq x (kw UP))	"..")
		      ((eq x (kw WILD))	"*")
		      ((eq x (kw WILD-INFERIORS))
					"**")
		      ((eq x (kw BACK))	(ERROR 'ERROR))
		      (t		(type-error
					 x `(OR STRING
					     (MEMBER
					      ,(kw BACK) ,(kw WILD) ,(kw UP)
					      ,(kw WILD-INFERIORS))))))
		    "/")))))

(defun HOST-NAMESTRING (pathname-designator)
  (let* ((pathname (PATHNAME pathname-designator)))
    (maybe-empty (PATHNAME-HOST pathname))))

(defun dir-subtract (dir1 dir2)
  (cond
    ((null dir1)
     (cons (kw RELATIVE) dir2))
    ((null dir2)
     nil)
    ((EQUAL (first dir1) (first dir2))
     (dir-subtract (rest dir1) (rest dir2)))))

(cl:defun ENOUGH-NAMESTRING (pathname-designator &OPTIONAL
			     (defaults *DEFAULT-PATHNAME-DEFAULTS*))
  ;; It is required that
  ;;   (merge-pathnames (enough-namestring pathname defaults) defaults)
  ;;   == (merge-pathnames (parse-namestring pathname nil defaults) defaults)
  (let ((pathname (PATHNAME pathname-designator)))
    (let ((candidates (list (NAMESTRING pathname)))
	  (shortest nil))
      (when (and (EQUAL (PATHNAME-HOST pathname) (PATHNAME-HOST defaults))
		 (EQUAL (PATHNAME-DEVICE pathname) (PATHNAME-DEVICE defaults))
		 (consp (PATHNAME-DIRECTORY pathname))
		 (eq (first (PATHNAME-DIRECTORY pathname)) (kw ABSOLUTE)))
	(let ((dir (dir-subtract (PATHNAME-DIRECTORY defaults)
				 (PATHNAME-DIRECTORY pathname))))
	  (when dir
	    (push (NAMESTRING (MAKE-PATHNAME (kw DIRECTORY) dir
					     (kw DEFAULTS) pathname))
		  candidates))))
      (FIND-IF (lambda (len)
		 (or (null shortest)
		     (when (< len shortest)
		       (setq shortest len))))
	       candidates (kw KEY) #'LENGTH))))

(defun slashp (char)
  (ch= char 47))

(defun parse-dir (string)
  (when string
    (when (ch= (CHAR string 0) 126)
      (setq string (expand-file-name string)))
    (let* ((start 0)
	   (dir (if (slashp (CHAR string 0))
		    (progn (incf start)
			   (list (kw ABSOLUTE)))
		    (list (kw RELATIVE)))))
      (do ((i start)
	   (j 1 (1+ j)))
	  ((eq j (LENGTH string))
	   (when (> j i)
	     (push (SUBSEQ string i j) dir)))
	(when (slashp (CHAR string j))
	  (let ((component (SUBSEQ string i j)))
	    (cond
	      ((STRING= component "*")		(push (kw WILD) dir))
	      ((STRING= component "**")		(push (kw WILD-INFERIORS) dir))
	      ((STRING= component "..")		(push (kw UP) dir))
	      ((STRING= component "."))		;Nothing.
	      (t				(push component dir))))
	  (setq i (1+ j))))
      (nreverse dir))))

(DEFVAR *DEFAULT-PATHNAME-DEFAULTS*
  (mkpathname nil nil (parse-dir default-directory) nil nil nil))

(defun parse-ver (name string)
  (if (STRING= name "")
      nil
      (cond
	((STRING= string "")		(kw NEWEST))
	((STRING= string "~")		(kw PREVIOUS))
	((and (ch= (CHAR string 0) 46)
	      (ch= (CHAR string 1) 126)
	      (ch= (CHAR string (1- (LENGTH string))) 126))
					(PARSE-INTEGER string (kw START) 2
						       (kw JUNK-ALLOWED) t))
	(t				(error "invalid version")))))

(defun maybe-wild (string)
  (cond
    ((null string)		nil)
    ((STRING= string "")	nil)
    ((STRING= string "*")	(kw WILD))
    (t				string)))

(cl:defun PARSE-NAMESTRING (thing &OPTIONAL host
			    (default *DEFAULT-PATHNAME-DEFAULTS*)
			    &KEY (START 0) END JUNK-ALLOWED)
  (cond
    ((STREAMP thing)
     (PARSE-NAMESTRING (FILE-STREAM-filename thing) host default
		       (kw START) START (kw END) END
		       (kw JUNK-ALLOWED) JUNK-ALLOWED))
    ((PATHNAMEP thing)
     (if (EQUAL (PATHNAME-HOST thing) host)
	 (cl:values thing START)
	 (ERROR 'ERROR)))
    ((STRINGP thing)
     ;; TODO: parse logical pathnames
     (let* ((string (SUBSEQ thing START END))
	    (dir (parse-dir (file-name-directory string)))
	    (name+ver (file-name-nondirectory string))
	    (name-ver (file-name-sans-versions name+ver))
	    (ver (parse-ver name-ver (substring name+ver (length name-ver))))
	    (name (maybe-wild (file-name-sans-extension name-ver)))
	    (type (maybe-wild (file-name-extension name+ver))))
;        (FORMAT T "~&dir=~S name+ver=~S name-ver=~S ver=~S name=~S type=~S"
; 	       dir name+ver name-ver ver name type)
       (cond
	 ((string= name+ver ".")
	  (when (null dir)
	    (setq dir (list (kw RELATIVE))))
	  (setq name nil))
	 ((string= name+ver "..")
	  (setq dir (if (null dir)
			(list (kw RELATIVE) (kw UP))
			(append dir (list (kw UP)))))
	  (setq name nil))
	 ((null name)
	  (setq name name-ver
		type nil))
	 ((null type)
	  (unless (string= name-ver "*.")
	    (setq name name-ver))))
       (when (string= name "")
	 (setq name nil))
       (cl:values (mkpathname nil nil dir name type ver)
		  (or END (LENGTH thing)))))
    (t
     (type-error thing '(OR PATHNAME STRING STREAM)))))

(cl:defun WILD-PATHNAME-P (pathname-designator &OPTIONAL field)
  (let ((pathname (PATHNAME pathname-designator)))
    (cond
      ((eq field (kw HOST))
       (eq (PATHNAME-HOST pathname) (kw WILD)))
      ((eq field (kw DEVICE))
       (eq (PATHNAME-DEVICE pathname) (kw WILD)))
      ((eq field (kw DIRECTORY))
       (or (memq (kw WILD) (PATHNAME-DIRECTORY pathname))
	   (memq (kw WILD-INFERIORS) (PATHNAME-DIRECTORY pathname))))
      ((eq field (kw NAME))
       (eq (PATHNAME-NAME pathname) (kw WILD)))
      ((eq field (kw TYPE))
       (eq (PATHNAME-TYPE pathname) (kw WILD)))
      ((eq field (kw VERSION))
       (eq (PATHNAME-VERSION pathname) (kw WILD)))
      ((null field)
       (some (lambda (f) (WILD-PATHNAME-P pathname f))
	     `(,(kw HOST) ,(kw DEVICE) ,(kw DIRECTORY)
	       ,(kw NAME) ,(kw TYPE) ,(kw VERSION))))
      (t
       (type-error field `(MEMBER NULL ,(kw HOST) ,(kw DEVICE) ,(kw DIRECTORY)
			          ,(kw NAME) ,(kw TYPE) ,(kw VERSION)))))))

(defmacro wild-test (fn pathname wildcard)
  `(or (eq (,fn ,wildcard) (kw WILD))
       (equal (,fn ,wildcard) (,fn ,pathname))
       ,@(when (or (eq fn 'PATHNAME-NAME) (eq fn 'PATHNAME-TYPE))
	   `((and (or (null (,fn ,pathname)) (string= (,fn ,pathname) ""))
	          (string= (,fn ,wildcard) ""))))))

(defun directories-match-p (pathname wildcard)
  (cond
    ((null pathname)
     (null wildcard))
    ((null wildcard)
     nil)
    ((eq (first wildcard) (kw WILD-INFERIORS))
     (if (null (rest wildcard))
	 T
	 (some (lambda (p) (directories-match-p p (rest wildcard)))
	       (maplist #'IDENTITY pathname))))
    ((wild-test first pathname wildcard)
     (directories-match-p (rest pathname) (rest wildcard)))))

(defvar *wild-pathname* (mkpathname (kw WILD) (kw WILD) (kw WILD)
				    (kw WILD) (kw WILD) (kw WILD)))

(defun PATHNAME-MATCH-P (pathname-designator wildcard)
  (let ((pathname (PATHNAME pathname-designator))
	(wildcard (MERGE-PATHNAMES wildcard *wild-pathname* (kw WILD))))
    (and (wild-test PATHNAME-HOST pathname wildcard)
	 (wild-test PATHNAME-DEVICE pathname wildcard)
	 (or (wild-test PATHNAME-DIRECTORY pathname wildcard)
	     (directories-match-p (PATHNAME-DIRECTORY pathname)
				  (PATHNAME-DIRECTORY wildcard)))
	 (wild-test PATHNAME-NAME pathname wildcard)
	 (wild-test PATHNAME-TYPE pathname wildcard)
	 (wild-test PATHNAME-VERSION pathname wildcard))))

;;; TODO: TRANSLATE-LOGICAL-PATHNAME

(defun wild-or-nil (x y)
  (if (or (null x) (eq x (kw WILD)))
      y
      x))

(defun translate-dir (source from to)
  (cond
    ((null to)
     nil)
    ((eq (first to) (kw WILD))
     (let ((pos (position (kw WILD) from)))
       (if pos
	   (cons (nth pos source)
		 (translate-dir (nthcdr (incf pos) source)
				(nthcdr pos from) (rest to)))
	   (ERROR 'ERROR))))
    (t
     (cons (first to) (translate-dir source from (rest to))))))

(defun TRANSLATE-PATHNAME (source from-wildcard to-wildcard)
  (let ((source (PATHNAME source))
	(from-wildcard (PATHNAME from-wildcard))
	(to-wildcard (PATHNAME to-wildcard)))
    (mkpathname
     (wild-or-nil (PATHNAME-HOST to-wildcard) (PATHNAME-HOST source))
     (wild-or-nil (PATHNAME-DEVICE to-wildcard) (PATHNAME-DEVICE source))
     (translate-dir (PATHNAME-DIRECTORY source)
		    (PATHNAME-DIRECTORY from-wildcard)
		    (PATHNAME-DIRECTORY to-wildcard))
     (wild-or-nil (PATHNAME-NAME to-wildcard) (PATHNAME-NAME source))
     (wild-or-nil (PATHNAME-TYPE to-wildcard) (PATHNAME-TYPE source))
     (wild-or-nil (PATHNAME-VERSION to-wildcard) (PATHNAME-VERSION source)))))

(defun merge-directories (dir1 dir2)
  ;; TODO: Proper handling of directory component.
  (cond
    ((null dir1)
     dir2)
    ((and (consp dir1) (eq (first dir1) (kw RELATIVE))
	  (consp dir2) (eq (first dir2) (kw ABSOLUTE)))
     (append dir2 (rest dir1)))
    (t
     dir1)))

(cl:defun MERGE-PATHNAMES (pathname-designator
			   &OPTIONAL
			   (default-designator *DEFAULT-PATHNAME-DEFAULTS*)
			   (default-version (kw NEWEST)))
  (let ((pathname (PATHNAME pathname-designator))
	(default (PATHNAME default-designator)))
    ;; TODO: read spec more closely.
    (mkpathname (or (PATHNAME-HOST pathname) (PATHNAME-HOST default))
		(or (PATHNAME-DEVICE pathname) (PATHNAME-DEVICE default))
		(merge-directories (PATHNAME-DIRECTORY pathname) (PATHNAME-DIRECTORY default))
		(or (PATHNAME-NAME pathname) (PATHNAME-NAME default))
		(or (PATHNAME-TYPE pathname) (PATHNAME-TYPE default))
		(or (PATHNAME-VERSION pathname)
		    (if (PATHNAME-NAME pathname)
			default-version
			(or (PATHNAME-VERSION default) default-version))))))
