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
(defun pg-pgip-process-packet (pgip)
  "Process the command packet PGIP, which is parsed XML according to pg-xml-parse-*"
  ;; PGIP processing is split into two steps:
  ;; (1) process each command, altering internal data structures
  ;; (2) post-process for each command type, affecting external interface (menus, etc).
  (mapcar 'pg-pgip-post-process 
	  (pg-pgip-process-cmds pgip)))

(defun pg-pgip-process-cmds (pgips)
  "Process the command(s) in PGIP, returning list of command symbols processed."
  (let (cmdtys)
    (while pgips
      (let* ((pgip  (car pgips))
	     (elt   (or (car-safe (car pgip))         ; normalise to symbol
			(car pgip)))
	     (attr  (cdr-safe (car pgip)))
	     (attrs (and attr (if (listp (cdr attr)) ; normalise to list
				  attr (list attr))))
	     (body  (cdr pgip)))
	(add-to-list 'cmdtys elt)
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
	(setq pgips (cdr pgips))))
    ;; Return list  of command types processed.
    cmdtys))

(defun pg-pgip-post-process (pgip)
  "Perform post-processing for a PGIP command type PGIP-ELT."
  (cond
   ((eq pgip 'pgip))
   ((eq pgip 'usespgml))
   ((or
     (eq pgip 'haspref)
     (eq pgip 'prefval))
    ;; Update preferences view/menu
    (proof-assistant-menu-update))
   ((or
     (eq pgip 'idtable)
     (eq pgip 'addid)
     (eq pgip 'delid))
    ;; Update completion tables/view
    )
   ((or
     (eq pgip 'menuadd)
     (eq pgip 'menudel))
    ;; Update menus
    )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; <haspref default="d" kind="k" description="d" class="c">name</haspref>
;; 

(defun pg-pgip-haspref (attrs name)
  "Issue a defpacustom from a <haspref> element with attributes ATTRS, name NAME."
  (unless (stringp name)
    (pg-pgip-error "pg-pgip-haspref: missing NAME in <haspref>NAME</haspref>."))
  (let*
      ((type	 (pg-pgip-get-type attrs))
       (default  (or (pg-pgip-get-attr "haspref" 'default attrs t)
		     ;; If no default is supplied, make one 
		        ;; [NB: boolean default is nil anyway]
		     (pg-pgip-default-for type)))
       (kind	 (intern
		  (or 
		   (pg-pgip-get-attr "haspref" 'kind attrs t)
		   ;; Default to kind user
		   "user")))
       (descr    (or (pg-pgip-get-attr "haspref" 'descr attrs t) ""))
       (subst    (pg-pgip-subst-for type))
       (setting  
	(pg-prover-interpret-pgip-command
	 (concat "<pgip><setpref name=\"" name "\">" subst "</setpref></pgip>")))
       (symname  (intern name))) ;; FIXME: consider Emacs ID normalising
    (ignore-errors 
      ;; FIXME: allow rest of PGIP to be processed, would be better to
      ;; accumulate errors somehow.
      (proof-debug "haspref calling defpacustom: name:%s default:%s type:%s setting:%s" symname default type setting)
      (eval
       `(defpacustom ,symname ,default 
	  (concat descr (if descr "\n")
	   "Setting configured by <haspref> PGIP message")
	  :type (quote ,type)
	  :setting ,setting)))))
    


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Dealing with <pgiptype>
;; 

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
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Auxiliary functions for parsing
;;

(defun pg-pgip-get-attr (elt attrnm attrs &optional optional)
  (let ((vrs (cdr-safe (assoc attrnm attrs))))
    (if optional
	vrs
      (or vrs
	  (error "Didn't find %s attribute in %s element" attrnm elt)))))

(defun pg-pgip-get-version (elt attrs &optional optional)
  (pg-pgip-get-attr elt "version" attrs optional))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Function to interface PGIP commands sent to prover.
;;
(defun pg-prover-interpret-pgip-command (pgip)
  (if proof-shell-issue-pgip-cmd
      (format proof-shell-issue-pgip-cmd pgip)
    "")) ;; Empty setting: might be better to send a comment
         ;; for debugging purposes.



(provide 'pg-pgip)
;; End of `pg-pgip.el'
