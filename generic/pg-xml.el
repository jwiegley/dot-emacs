;; pg-xml.el	 XML functions for Proof General
;;
;; Copyright (C) 2000-2001 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; XML functions for Proof General
;;
;; Proof General Kit uses PGIP, an XML-message protocol
;; for interactive proof.  The simple functions here allow
;; parsing and writing of XML documents.  Little attempt
;; is made for efficiency, since PGIP documents are intended
;; to be small.  No attempt at validation or handling
;; unicode characters is made.
;;

;; TODO:
;; * Fix identifiers
;; * Fix whitespace handling
;; * Ignore prologues


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Parsing function: pg-xml-parse-buffer
;;

(defconst pg-xml-name  "[a-zA-Z_:][a-zA-Z0-9._:-]*")
(defconst pg-xml-space "[ \t\n]")
(defconst pg-xml-ref   (concat "&" pg-xml-name ";"))  ; FIXME: charrefs
			
(defconst pg-xml-start-open-elt-regexp 
  (concat pg-xml-space "*" "<\\(" pg-xml-name "\\)"))
(defconst pg-xml-end-open-elt-regexp 
  (concat pg-xml-space "*" "\\(/?\\)>"))
(defconst pg-xml-close-elt-regexp 
  (concat pg-xml-space "*" "</\\(" pg-xml-name "\\)>"))
(defconst pg-xml-attribute-regexp 
  (concat pg-xml-space "+" "\\(" pg-xml-name "\\)"))
(defconst pg-xml-attribute-val-regexp 
  (concat pg-xml-space "*" "=" pg-xml-space "*" 
	  "\"\\(\\([^<&\"]\\|" pg-xml-ref "\\)*\\)\"")) ; FIXME or 's
(defconst pg-xml-comment-start-regexp "<!--")
(defconst pg-xml-comment-end-regexp "-->")
(defconst pg-xml-anymarkup-regexp "<")
(defconst pg-xml-special-elts
  '(xml)
  "List of special elements which don't require closing.")

(defvar xmlparse nil
  "Used to store parse result.")

(defun pg-xml-add-text (text)		
  "If TEXT is non empty, add it to subtree at top of `xmlparse'."
  (unless (string-equal text "")
    (setq xmlparse (cons (cons text (car xmlparse))
			 (cdr xmlparse)))))
	   

(defun pg-xml-parse-buffer (&optional buffer nomsg)
  "Parse an XML documment in BUFFER (defaulting to current buffer).
Return a lisp structure with symbols representing the element 
names, so that the result of parsing 
   <elt attr=\"blah\">text</elt> 
is 
  (elt ((attr . \"blah\")) (text))"
  (unless nomsg
    (message "Parsing %s..." (buffer-name buffer)))
  (save-excursion
    (if buffer (set-buffer buffer))
    (goto-char (point-min))
    (let ((xmlparse nil)
	  (pos	    (point))
	  openelts elt)
      (unless (looking-at pg-xml-start-open-elt-regexp)
	(warn "pg-xml-parse-buffer: Junk at start of document: %s"
	      (buffer-substring 
	       (point-min)
	       (min (save-excursion
		      (re-search-forward pg-xml-anymarkup-regexp nil t)
		      (match-beginning 0))
		    (+ 10 (point-min))))))
      (while (re-search-forward pg-xml-anymarkup-regexp nil t)
	(goto-char (match-beginning 0))
	(cond
	 ;; CASE 1: element opening
	 ((looking-at pg-xml-start-open-elt-regexp)
	  (setq elt (intern (match-string 1)))
	  ;; Add text before here to the parse, if non-empty
	  ;; FIXME: maybe unless last elt was opening too and 
	  ;; only white space?
	  (pg-xml-add-text (buffer-substring pos (match-beginning 0)))
	  ;; Now look for any attributes
	  (goto-char (match-end 0))
	  (let ((attrs nil) attr)
	    (while (looking-at pg-xml-attribute-regexp)
	      (setq attr (intern (match-string 1)))
	      (goto-char (match-end 0))
	      (if (looking-at pg-xml-attribute-val-regexp)
		  (progn
		    (setq attr (cons attr (match-string 1)))
		    (goto-char (match-end 0))))
	      (setq attrs (cons attr attrs)))
	    ;; Retain order in document
	    (setq attrs (reverse attrs))
	    ;; Now we ought to be at the end of the element opening
	    (unless (looking-at pg-xml-end-open-elt-regexp)
	      (error "pg-xml-parse-buffer: Invalid XML in element opening %s" 
		     (symbol-name elt)))
	    ;; Stack the element unless it's self closing
	    (if (> (length (match-string 1)) 0)
		;; Add element without nesting
		(setq xmlparse (cons (cons (cons elt attrs)
					   (car xmlparse))
				     (cdr xmlparse)))
	      ;; Otherwise stack and nest
	      (setq openelts (cons elt openelts))
	      (setq xmlparse (cons (list (cons elt attrs)) 
				   xmlparse))))
	    (goto-char (match-end 0))
	    (setq pos (point)))

	 ;; CASE 2: element closing
	 ((looking-at pg-xml-close-elt-regexp)
	  (setq elt (intern (match-string 1)))
	  ;; It better be the top thing on the stack
	  (unless (eq elt (car-safe openelts))
	    (error "pg-xml-parse-buffer: Invalid XML at element closing </%s> (expected </%s>)"
		   (symbol-name elt)
		   (if openelts
		       (symbol-name (car openelts))
		     "no closing element")))
	  ;; Add text before here to the parse
	  (pg-xml-add-text (buffer-substring pos (match-beginning 0)))
	  ;; Unstack the element and close subtree
	  (setq openelts (cdr openelts))
	  (setq xmlparse (cons (cons
				(reverse (car xmlparse))
				(cadr xmlparse))
			       (cddr xmlparse)))
	  (goto-char (match-end 0))
	  (setq pos (point)))
	 
	 ;; CASE 3: comment
	 ((looking-at pg-xml-comment-start-regexp)
	  (unless (re-search-forward pg-xml-comment-end-regexp nil t)
	    (error "pg-xml-parse-buffer: Unclosed comment beginning at line %s"
		   (1+ (count-lines (point-min) (point))))))))
	
      ;; We'd better have nothing on the stack of open elements now.
      (unless (null openelts)
	(error "pg-xml-parse-buffer: Unexpected end of document, expected </%s>"
	       (symbol-name (car openelts))))
      ;; And we'd better be at the end of the document.
      (unless (and (looking-at "[ \t\n]*")
		   (eq (match-end 0) (point-max)))
	(warn "pg-xml-parse-buffer: Junk at end of document: %s"
	      (buffer-substring (point)
				(min (point-max) (+ 30 (point-max))))))
      ;; Return the parse
      ;; FIXME: 
      (unless nomsg
	(message "Parsing %s...done" (buffer-name buffer)))
      (caar xmlparse))))

(defun pg-xml-parse-string (arg)
  "Parse string in ARG, same as pg-xml-parse-buffer."
  (let
      ((tempbuffer (get-buffer-create " *xml-parse*")))
    (save-excursion 
      (set-buffer tempbuffer)
      (delete-region (point-min) (point-max))
      (insert-string arg)
      (pg-xml-parse-buffer))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Producing functions: state-based writing of an XML doc,
;;			built up in pg-xml-doc


(defvar pg-xml-doc nil
  "Current document being written")

(defvar pg-xml-openelts nil
  "Stack of openelements")

(defvar pg-xml-indentp nil
  "Whether to indent written XML documents")

(defun pg-xml-begin-write ()
  (setq pg-xml-doc nil
	pg-xml-openelts nil))

(defun pg-xml-indent ()
  (if pg-xml-indentp
      (substring "\n                              " 
		 1 (length pg-xml-openelts))
    ""))

(defun pg-xml-openelt (element &optional attributes)
  (setq pg-xml-openelts (cons element pg-xml-openelts))
  (let (string)
    (setq string (concat (pg-xml-indent)
			 "<" (symbol-name element)))
    (while attributes
      (if (consp (car attributes))
	  (setq string (concat 
			string
			" " 
			(symbol-name (caar attributes))
			"="
			(cdar attributes)))
	(setq string (concat string
			     " " (symbol-name (car attributes)))))
      (setq attributes (cdr attributes)))
    (setq pg-xml-doc
	  (cons (concat string ">") pg-xml-doc))))

(defun pg-xml-closeelt ()
  (unless pg-xml-openelts
    (error "pg-xml-closelt: no open elements"))
  (setq pg-xml-doc 
	(cons
	 (concat
	  (pg-xml-indent)
	  "</" (symbol-name (car pg-xml-openelts)) ">")
	 pg-xml-doc))
  (setq pg-xml-openelts (cdr pg-xml-openelts)))


(defun pg-xml-writetext (text)
  (setq pg-xml-doc (cons (concat (pg-xml-indent) text) pg-xml-doc)))

(defun pg-xml-doc ()
  (apply 'concat (reverse pg-xml-doc)))

;; Test document:
;;(progn
;;  (pg-xml-begin-write)
;;  (pg-xml-openelt 'root)
;;  (pg-xml-openelt 'a '((class . "1B")))
;;  (pg-xml-writetext "text a")
;;  (pg-xml-closeelt)
;;  (pg-xml-closeelt)
;;  (pg-xml-doc))

(provide 'pg-xml)
;; End of `pg-xml.el'
