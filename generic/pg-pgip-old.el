;; pg-pgip-old.el	 Functions for processing PGIP for Proof General
;;
;; This file contains some backwards compatiblity functions for
;; dealing with PGIP 1.X messages.  The only case that these are
;; needed is for interim backward compatibility with Isabelle2003 and
;; Isabelle2004, for processing preference settings.
;;

;; FIXME: resurrect pg-prover-interpret-pgip-command (could try with pg-pgip-string-of-command)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; Message processing: BACKWARD COMPATIBILITY
;;
;; <haspref default="d" kind="k" type="t"
;;	    description="d" class="c">name</haspref>

(defun pg-pgip-process-oldhaspref (node) ;; for Isabelle 2004
  (pg-pgip-process-haspref node))

(defun pg-pgip-process-haspref (node)    ;; for Isabelle 2003
  "Issue a defpacustom from a <haspref> element with attributes ATTRS, name NAME."
  (let*
      ((name     (pg-xml-get-text-content node))  ;; old PGIP: <haspref>name<haspref>
       (type	 (pg-pgip-old-get-type node))
       (defattr  (pg-xml-get-attr 'default node t))
       (default  (if defattr 
		     (pg-pgip-old-interpret-value defattr type)
		   (pg-pgip-old-default-for type)))
       (kind	 (intern
		  (pg-xml-get-attr 'kind node t "user")))
       (descr    (pg-xml-get-attr 'descr node t ""))
       (subst    (pg-pgip-subst-for type))
       (setting  
	(pg-pgip-string-of-command
	 (concat "<setpref name=\"" name "\">" subst "</setpref>")))
       (symname  (intern name)))
    (ignore-errors 
      ;; FIXME: allow rest of PGIP to be processed, would be better to
      ;; accumulate errors somehow.
      (proof-debug "haspref calling defpacustom: name:%s default:%s type:%s setting:%s" symname default type setting)
      (eval
       ;; FIXME: would like unique custom group for settings introduced by haspref.
       ;; (preferences or something).
       `(defpacustom ,symname ,default 
	  (concat descr (if descr "\n")
	   "Setting configured by <haspref> PGIP message")
	  :type (quote ,type)
	  :setting ,setting)))))
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Interpretation of types in old format
;;

(defun pg-pgip-old-interpret-bool (value)
  (cond 
   ((string-equal value "true") t)
   ((string-equal value "false") nil)
   ;; Non-boolean value: return false, give debug message.
   (t (progn
	(proof-debug "pg-pgip-old-interpret-bool: received non-bool value %s" value)
	nil))))

(defun pg-pgip-old-interpret-int (value)
  ;; FIXME: string-to-number returns zero for non int string,
  ;; should have better validation here.
  (string-to-number value))

(defun pg-pgip-old-interpret-string (value)
  value)

(defun pg-pgip-old-interpret-choice (choices value)
  ;; Untagged union types: test for each type in turn.
  ;; FIXME: nested unions not supported here.
  (cond
   ((and 
     (memq 'boolean choices)
     (or (string-equal value "true") (string-equal value "false")))
    (pg-pgip-old-interpret-value value 'boolean))
   ((and 
     (memq 'integer choices)
     (string-match "[0-9]+$" value))
    (pg-pgip-old-interpret-value value 'integer))
   ((memq 'string choices)
    ;; FIXME: No special syntax for string inside PGIP yet, should be?
    (pg-pgip-old-interpret-value value 'string))
   (t
    (pg-pgip-old-error 
     "pg-pgip-old-interpret-choice: mismatching value %s for choices %s" 
     value choices))))

(defun pg-pgip-old-interpret-value (value type)
  (cond
   ((eq type 'boolean)
    (pg-pgip-old-interpret-bool value))
   ((eq type 'integer)
    (pg-pgip-old-interpret-int value))
   ((eq type 'string)
    (pg-pgip-old-interpret-string value))
   ((and (consp type) (eq (car type) 'choice))
    (pg-pgip-old-interpret-choice (cdr type) value))
   (t
    (pg-pgip-old-error "pg-pgip-old-interpret-value: unkown type %s" type))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Dealing with <pgiptype> in old format
;; 

(defun pg-pgip-old-default-for (type)
  "Synthesize a default value for type TYPE."
  (cond
   ((eq type 'boolean) nil)
   ((eq type 'integer) 0)
   ((eq type 'string)  "")
   ((eq (car-safe type) 'choice)
	(car-safe (cdr-safe type)))
   (t
    (pg-pgip-old-error "pg-pgip-old-default-for: unrecognized type passed in"))))

(defun pg-pgip-old-subst-for (type)
  "Return a substitution string for type TYPE."
  (cond
   ((eq type 'boolean) "%b")
   ((eq type 'integer) "%i")
   (t "%s")))

(defun pg-pgip-old-get-type (node)
  "Extract and check type value from NODE.  Return type in internal (custom) format."
  (let 
      ((rawtype (pg-xml-get-attr 'type node)))
    (pg-pgip-old-pgiptype rawtype)))
 

(defun pg-pgip-old-pgiptype (rawtype)
  "Return internal (custom format) representation for <pgiptype> element."
    (cond
     ((string-match "choice\(\\(.*\\)\)" rawtype)
      (let* ((choiceslist (match-string 1 rawtype))
	     ;; FIXME: nested choices not supported yet
	     (choices	  (split-string choiceslist "[ \f\t\n\r\v]*,[ \f\t\n\r\v]*")))
	(list 'choice (mapcar 'pg-pgip-old-pgiptype choices))))
     ((equal rawtype "boolean")
      'boolean)
     ((equal rawtype "int")
      'integer)
     ((equal rawtype "nat")		;; nat treated as int 
      'integer)
     ((equal rawtype "string")
      'string)
     (t
      (error "pg-pgip-old-pgiptype: unrecognized type %s" rawtype))))




(provide 'pg-pgip-old)
;; End of `pg-pgip-old.el'
