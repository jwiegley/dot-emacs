;; pg-pgip.el	 Functions for processing PGIP for Proof General
;;
;; Copyright (C) 2000-2002 LFCS Edinburgh. 
;; Author:   David Aspinall <da@dcs.ed.ac.uk>
;; License:  GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; STATUS: Experimental
;;
;; Proof General Kit uses PGIP, an XML-message protocol
;; for interactive proof.  This file contains functions 
;; to process PGIP commands sent from the proof assistant.
;;

;; Halt on errors during development: later may accumulate and ignore.
(defalias 'pg-pgip-error 'error)	

;;;###autoload
(defun pg-pgip-process-cmd (pgips) 
  "Process the command in PGIP, which should be parsed XML according to pg-xml-parse-*."
  (while pgips
    (let* ((pgip  (car pgips))
	   (elt   (or (car-safe (car pgip))         ; normalise to symbol
		      (car pgip)))
	   (attr  (cdr-safe (car pgip)))
	   (attrs (and attr (if (listp (cdr attr)) ; normalise to list
				attr (list attr))))
	   (body  (cdr pgip)))
      (cond 
       ;; <pgip> 
       ((eq elt 'pgip))			;; ignore pgip attributes for now
       ;; <usespgml>
       ((eq elt 'usespgml)
	(proof-debug "Received usespgml message, version %s"
		     (pg-pgip-get-version "usespgml" attrs)))
       ;; <haspref>
       ((eq elt 'haspref)
	(pg-pgip-haspref attrs (car-safe body)))

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
      (setq pgips (cdr pgips)))))


;; test: (pg-pgip-haspref '((type . "boolean") (kind . "user")) "verbose_flag")
(defun pg-pgip-haspref (attrs name)
  "Issue a defpacustom from a <haspref> element with attributes ATTRS, name NAME."
  (unless (stringp name)
    (pg-pgip-error "pg-pgip-haspref: missing NAME in <haspref>NAME</haspref>."))
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
       (subst    (pg-pgip-subst-for type))
       (setting  
	;; FIXME: deal with provers that don't understand PGIP here.
	(concat "<pgip><setpref name=\"" name "\">" subst "</setpref></pgip>"))
       (symname  (intern name))) ;; FIXME: consider Emacs ID normalising
    (eval
     `(defpacustom ,symname ,default 
	;; FIXME: better docstring
	"Setting configured by <haspref> PGIP message"
	:type (quote ,type)
	:setting ,setting))))
    
(defun pg-pgip-default-for (type)
  "Synthesize a default value for type TYPE."
  (cond
   ((eq type 'boolean) nil)
   ((eq type 'integer) 0)
   ((eq type 'string)  "")
   ((eq (car-safe type) 'choice)
	(car-safe (cdr-safe type)))
   (t
    (pg-pgip-error "pg-pgip-default-for: unrecognized type passed in"))))

(defun pg-pgip-subst-for (type)
  "Return a substitution string for type TYPE."
  (cond
   ((eq type 'boolean) "%b")
   ((eq type 'integer) "%i")
   (t "%s")))

(defun pg-pgip-get-type (attrs)
  "Extract and check type value from ATTRS.  Normalize to custom format."
  (let 
      ((rawtype (pg-pgip-get-attr "haspref" 'type attrs)))
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
  (let ((vrs (cdr-safe (assoc attrnm attrs))))
    (if optional
	vrs
      (or vrs
	  (error "Didn't find %s attribute in %s element" attrnm elt)))))

(defun pg-pgip-get-version (elt attrs &optional optional)
  (pg-pgip-get-attr elt "version" attrs optional))




(provide 'pg-pgip)
;; End of `pg-pgip.el'
