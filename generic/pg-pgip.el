;; pg-pgip.el	 Functions for processing PGIP for Proof General
;;
;; Copyright (C) 200-2001 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; Proof General Kit uses PGIP, an XML-message protocol
;; for interactive proof.  This file contains functions 
;; to process PGIP commands sent from the proof assistant.
;;

(defun pg-pgip-process-cmd (pgip) 
  "Process the command in PGIP, which should be parsed XML according to pg-xml-parse-*."
  (while (pgip)
    (let ((elt   (caar  pgip))
	  (attrs (cdar  pgip)))
      (cond 
       ;; <pgip> 
       ((eq elt 'pgip))			;; ignore pgip attributes for now
       ;; <usespgml>
       ((eq elt 'usespgml)
	(message "Received usespgml message, version %s"
		 (pg-pgip-get-version "usespgml" attrs)))
       ;; <haspref>
       ((eq elt 'haspref)
	(pg-pgip-haspref attrs) ;; (cadr pgip))
	(setq pgip (cdr pgip)))
       ;; <prefval>
       ((eq elt 'prefval)
	)
       ;; <idtable>
       ((eq elt 'idtable)
	)
       ;; <addid>
       ((eq elt 'addid)
	)
       ;; <delid>
       ((eq elt 'delid)
	)
       ;; <menuadd>
       ((eq elt 'menuadd)
	)
       ((eq elt 'menudel)
	))
      ;; Move on to next element
      (setq pgip (cdr pgip)))))

(defun pg-pgip-haspref (attrs)
  "Issue a defpacustom from a <haspref> element with attributes ATTRS"
  (let*
      ((type	 (pg-pgip-get-type attrs))
       (default  (or (pg-pgip-get-attr "haspref" "default" attrs t)
		     ;; If no default is supplied, make one
		     (pg-pgip-default-for type)))
       (kind	 (intern
		  (or 
		   (pg-pgip-get-attr "haspref" "kind" attrs t)
		   ;; Default to kind user
		   "user")))
       (name     (intern (pg-pgip-get-attr "haspref" "name")))
       (subst    (pg-pgip-subst-for type))
       (setting  (concat "<pgip><setpref name=\"" name "\">" subst "</setpref></pgip>")))
    (eval
     (list 'defpacustom name default 
	   ;; FIXME: better docstring
	   "Setting configured by <haspref> PGIP message"
	   :type type
	   :setting setting))))
    
(defun pg-pgip-default-for (type)
  "Synthesize a default value for type TYPE."
  (cond
   ((eq type 'boolean) nil)
   ((eq type 'integer) 0)
   ((eq type 'string)  "")
   ((eq (car-safe type) 'choice)
	(car-safe (cdr-safe type)))
   (t
    (error "pg-pgip-default-for: unrecognized type passed in"))))

(defun pg-pgip-subst-for (type)
  "Return a substitution string for type TYPE."
  (cond
   ((eq type 'boolean) "%b")
   ((eq type 'integer) "%i")
   (t "%s")))

(defun pg-pgip-get-type (attrs)
  "Extract and check type value from ATTRS.  Normalize to custom format."
  (let ((rawtype (pg-pgip-get-attr "haspref" "type" attrs)))
    (cond
     ((string-match "choice(\\(.*\\))" rawtype)
      (let* ((choiceslist (match-string 1 rawtype))
	     (choices	  (split-string choiceslist "[ \f\t\n\r\v]*,[ \f\t\n\r\v]*")))
	(list 'choice choices)))
     ((equal rawtype "boolean")
      'boolean)
     ((equal rawtype "int")
      'integer)
     ((equal rawtype "nat")		;; nat treated as int 
      'integer)
     ((equal rawtype "string")
      'string)
     (t
      (error "pg-pgip-get-type: unrecognized type %s" rawtype)))))
    

;; Auxiliary functions for parsing

(defun pg-pgip-get-attr (elt attrnm attrs &optional optional)
  (let ((vrs (assoc attrnm attrs)))
    (if optional
	vrs
      (or vrs
	  (error "Didn't find %s attribute in %s element" attrnm elt)))))

(defun pg-pgip-get-version (elt attrs &optional optional)
  (pg-pgip-get-attr elt "version" attrs optional))


      




;; End of `pg-pgip.el'


