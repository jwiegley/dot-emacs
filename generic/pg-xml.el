;; pg-xml.el	 XML functions for Proof General
;;
;; Copyright (C) 2000-2002 LFCS Edinburgh. 
;; Author:     David Aspinall <David.Aspinall@ed.ac.uk>
;; License:    GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; XML functions for Proof General.
;;

(require 'proof-utils) ;; for pg-internal-warning

(require 'xml) ;; Emmanuel Briot's XML parser, updated by Mark A. Hershberger
	       ;; (bundled with PG in directory lib/ to try to avoid incompatible versions)



;; Elisp format of XML trees (see xml.el)
;;
;;    xml-list   ::= (node node ...)
;;    node       ::= (qname attribute-list . child_node_list)
;;    child_node_list ::= child_node child_node ...
;;    child_node ::= node | string
;;    qname      ::= (:namespace-uri . "name") | "name"
;;    attribute_list ::= ((qname . "value") (qname . "value") ...)
;;                       | nil
;;    string     ::= "..."
;;
;; NB [da]: without namespace aware parsing, qnames are symbols.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Parsing function: pg-xml-parse-buffer
;;

;;;###autoload
(defun pg-xml-parse-string (arg)
  "Parse string in ARG, same as pg-xml-parse-buffer."
  (let
      ((tempbuffer (get-buffer-create " *xml-parse*")))
    (save-excursion 
      (set-buffer tempbuffer)
      (delete-region (point-min) (point-max))
      (insert-string arg)
      (pg-xml-parse-buffer (current-buffer) 'nomessage))))


(defun pg-xml-parse-buffer (&optional buffer nomsg)
  "Parse an XML documment in BUFFER (defaulting to current buffer).
Parsing according to `xml-parse-file' of xml.el."
  (unless nomsg
    (message "Parsing %s..." (buffer-name buffer)))
  (let ((xml (xml-parse-region (point-min)
				 (point-max)
				 (current-buffer)
				 nil)))
      (unless nomsg
	(message "Parsing %s...done" (buffer-name buffer)))
      xml))

;; Check that the empty parsing bug isn't present
(if (xml-node-children (car (pg-xml-parse-string "<foo/>")))
    (pg-internal-warning "An old version of xml.el was loaded!  It is buggy. See Proof General FAQ."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Helper functions for parsing
;;

(defun pg-xml-get-attr (attribute node &optional optional defaultval)
  (let ((val (cdr (assoc attribute (xml-node-attributes node)))))
    (or val
	(if optional
	    defaultval
	  (pg-pgip-error "pg-xml-get-attr: Didn't find required %s attribute in %s element" 
		 attribute (xml-node-name node))))))

(defun pg-xml-child-elts (node)
  "Return list of *element* children of NODE (ignoring strings)."
  (let ((children (xml-node-children node)))
    (mapcan (lambda (x) (if (listp x) (list x))) children)))

(defun pg-xml-child-elt (node)
  "Return unique element child of NODE."
  (let ((children (pg-xml-child-elts node)))
    (if (= (length children) 1)
	(car children)
      (pg-internal-warning  "pg-xml-child-elt: expected single element child of %s" 
			    (xml-node-name node)))))

(defun pg-xml-get-child (child node)
  "Return single element CHILD of node, give error if more than one."
  (let ((children (xml-get-children node child)))
    (if (> (length children) 1)
	 (progn
	   (pg-internal-warning "pg-xml-get-child: got more than one %s child of %s node, ignoring rest"
				child (xml-node-name node))
	   (car children))
      children)))
     
(defun pg-xml-get-text-content (node)
  "Return the concatenation of all the text children of node NODE."
  (mapconcat (lambda (x) (if (stringp x) x "")) (xml-node-children node) ""))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Producing functions: constructing an XML tree in xml.el format
;;			and converting to a string

(defmacro pg-xml-attr (name val) `(cons (quote ,name) ,val))

(defmacro pg-xml-node (name atts children) 
  `(cons (quote ,name) (cons ,atts ,children)))

(defconst pg-xml-header 
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")


(defun pg-xml-string-of (xmls)
  "Convert the XML trees in XMLS into a string (without additional indentation)."
  (let ((insertfn    (lambda (&rest args)
		       (setq strs (cons (reduce 'concat args) strs))))
	strs)
    (dolist (xml xmls) 
      (pg-xml-output-internal xml nil insertfn))
    (reduce 'concat (reverse strs))))

;; based on xml-debug-print from xml.el

(defun pg-xml-output-internal (xml indent-string outputfn)
  "Outputs the XML tree using OUTPUTFN, which should accept a list of args.
Output with indentation INDENT-STRING (or none if nil)."
  (let ((tree xml)
	attlist)
    (funcall outputfn (or indent-string "") "<" (symbol-name (xml-node-name tree)))
    
    ;;  output the attribute list
    (setq attlist (xml-node-attributes tree))
    (while attlist
      (funcall outputfn " ")
      (funcall outputfn (symbol-name (caar attlist)) "=\"" (cdar attlist) "\"")
      (setq attlist (cdr attlist)))
    
    (setq tree (xml-node-children tree))

    (if tree
	(progn
	  (funcall outputfn ">")
	  ;;  output the children
	  (dolist (node tree)
	    (cond
	     ((listp node)
	      (if indent-string (funcall outputfn "\n"))
	      (pg-xml-output-internal node (if indent-string (concat indent-string "  ")) outputfn))
	     ((stringp node) (funcall outputfn node))
	     (t
	      (error "pg-xml-output-internal: Invalid XML tree"))))
	  
	  (funcall outputfn (if indent-string (concat "\n" indent-string) "")
		   "</" (symbol-name (xml-node-name xml)) ">"))
      (funcall outputfn "/>"))))


(provide 'pg-xml)
;; End of `pg-xml.el'
