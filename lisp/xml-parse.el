;;; xml-parse --- code to efficiently read/write XML data with Elisp
;;;
;;; $Id: xml-parse.el,v 1.4 2001/05/12 22:36:13 ryants Exp $

;; Copyright (C) 2001 John Wiegley.

;; Author: John Wiegley <johnw@gnu.org>
;; Version: 1.5
;; Created: Feb 15, 2001
;; Keywords: convenience languages lisp xml parse data
;; URL: http://www.gci-net.com/~johnw/emacs.html

;; This file is NOT (yet) part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;;
;; XML is yet another way of expressing recursive, attributed data
;; structures -- something which Lisp has had the capacity to do for
;; decades.
;;
;; The approach taken by xml-parse.el is to read XML data into Lisp
;; structures, and allow those same Lisp structures to be written out
;; as XML.  It should facilitate the manipulation and use of XML by
;; Elisp programs.

;; NOTE: This is not a validating parser, and makes no attempt to read
;; DTDs.  See psgml.el if you need that kind of power.
;;
;; Also, tags beginning with <? or <! are not parsed, but merely
;; included in the resulting data structure as separate string
;; entries.  These may be tested for using the function
;; `xml-tag-special-p'.  If present, they are treated just like normal
;; text, and will be inserted along with everything else.  If they
;; occur *before* the opening tag of an XML tree, they will not appear
;; in the parsed data, since such "pre-tags" are not the child of any
;; tag.

;; Here is the format of the Lisp data structure used:
;;
;;   (TAG CHILD...)
;;
;; Where TAG is either a string (naming the tag) or a list.  The list
;; form is used to identify attributes, and has the format:
;;
;;   (TAG-NAME (ATTR-NAME . ATTR-VALUE)...)
;;
;; After the TAG, there can be zero or more child structures, which
;; are either literal strings, or the same "TAG CHILD..." structure as
;; the parent.  See `insert-xml' for an EBNF grammar of this layout.

;; EXAMPLE: Given the following DocBook XML data:
;;
;;   <book id="compiler">
;;     <bookinfo>
;;       <bookbiblio>
;;         <title>My own book!</title>
;;         <edition>First</edition>
;;         <authorgroup>
;;           <author>
;;             <firstname>John</firstname>
;;             <surname>Wiegley</surname>
;;           </author>
;;         </authorgroup>
;;       </bookbiblio>
;;     </bookinfo>
;;     <chapter>
;;       <title>A very small chapter</title>
;;       <para>Wonder where the content is...</para>
;;     </chapter>
;;   </book>
;;
;; It would be parsed into this Lisp structure:
;;
;;   '(("book" ("id" . "compiler"))
;;     ("bookinfo"
;;      ("bookbiblio"
;;       ("title" "My own book!")
;;       ("edition" "FIrst")
;;       ("authorgroup"
;;        ("author"
;;         ("firstname" "John")
;;         ("surname" "Wiegley")))))
;;     ("chapter"
;;      ("title" "A very small chapter")
;;      ("para" "Wonder where the content is...")))
;;
;; Now it can easily be modified and interpreted using ordinary Lisp
;; code, without the ordeal of manipulating textual XML.  When you're
;; done modifying it, you can write it back out (complete with proper
;; indentation and newlines) using:
;;
;;   (insert-xml <DATA> t)
;;
;; See the documentation for `read-xml' and `insert-xml' for more
;; information.
;;
;; There are also a set of helper functions for accessing parts of a
;; parsed tag:
;;
;;   xml-tag-name       get the name of a tag
;;   xml-tag-attrlist   returns a tag's attribute alist
;;   xml-tag-attr       lookup a specific tag attribute
;;   xml-tag-children   returns a tag's child list
;;   xml-tag-child      lookup a specific child tag by name
;;
;; Also, the attribute list and child lists can be searched using
;; `assoc', since they roughly have the same format as an alist.

;;;###autoload
(defun read-xml (&optional progress-callback)
  "Parse XML data at point into a Lisp structure.
See `insert-xml' for a description of the format of this structure.
Point is left at the end of the XML structure read."
  (cdr (xml-parse-read progress-callback)))

(defsubst xml-tag-with-attributes-p (tag)
  "Does the TAG have attributes or not?"
  (listp (car tag)))

(defsubst xml-tag-name (tag)
  "Return the name of an xml-parse'd XML TAG."
  (cond ((xml-tag-text-p tag)
	 (car tag))
	((xml-tag-with-attributes-p tag)
	 (caar tag))
	(t (car tag))))

(defun xml-tag-text-p (tag)
  "Is the given TAG really just a text entry?"
  (stringp tag))

(defsubst xml-tag-special-p (tag)
  "Return the name of an xml-parse'd XML TAG."
  (and (xml-tag-text-p tag)
       (eq (aref tag 0) ?\<)))

(defsubst xml-tag-attrlist (tag)
  "Return the attribute list of an xml-parse'd XML TAG."
  (and (not (stringp (car tag)))
       (cdar tag)))

(defsubst xml-tag-attr (tag attr)
  "Return a specific ATTR of an xml-parse'd XML TAG."
  (cdr (assoc attr (xml-tag-attrlist tag))))

(defsubst xml-tag-children (tag)
  "Return the list of child tags of an xml-parse'd XML TAG."
  (cdr tag))

(defun xml-tag-child (tag name)
  "Return the first child matching NAME, of an xml-parse'd XML TAG."
  (catch 'found
    (let ((children (xml-tag-children tag)))
      (while children
	(if (string= name (xml-tag-name (car children)))
	    (throw 'found (car children)))
	(setq children (cdr children))))))

;;;###autoload
(defun insert-xml (data &optional add-newlines public system depth ret-depth)
  "Insert DATA, a recursive Lisp structure, at point as XML.
DATA has the form:

  ENTRY       ::=  (TAG CHILD*)
  CHILD       ::=  STRING | ENTRY
  TAG         ::=  TAG_NAME | (TAG_NAME ATTR+)
  ATTR        ::=  (ATTR_NAME . ATTR_VALUE)
  TAG_NAME    ::=  STRING
  ATTR_NAME   ::=  STRING
  ATTR_VALUE  ::=  STRING

If ADD-NEWLINES is non-nil, newlines and indentation will be added to
make the data user-friendly.

If PUBLIC and SYSTEM are non-nil, a !DOCTYPE tag will be added at the
top of the document to identify it as an XML document.

DEPTH is normally for internal use only, and controls the depth of the
indentation."
  (when (and (not depth) public system)
    (insert "<?xml version=\"1.0\"?>\n")
    (insert "<!DOCTYPE " (if (stringp (car data))
			     (car data)
			   (caar data))
	    " PUBLIC \"" public "\"\n  \"" system "\">\n"))
  (if (stringp data)
      (insert data)
    (let ((node (car data)) (add-nl t))
      (and depth (bolp)
	   (insert (make-string (* depth 2) ? )))
      (if (stringp node)
	  (insert "<" node)
	(setq node (caar data))
	(insert "<" node)
	(let ((attrs (cdar data)))
	  (while attrs
	    (insert " " (caar attrs) "=\"" (cdar attrs) "\"")
	    (setq attrs (cdr attrs)))))
      (if (null (cdr data))
	  (insert "/>")
	(insert ">")
	(setq data (cdr data))
	(while data
	  (and add-newlines add-nl
	       (not (stringp (car data)))
	       (insert ?\n))
	  (setq add-nl (insert-xml (car data) add-newlines
				   nil nil (1+ (or depth 0)))
		data (cdr data)))
	(when add-nl
	  (and add-newlines (insert ?\n))
	  (and depth (insert (make-string (* depth 2) ? ))))
	(insert "</" node ">"))
      t)))

;;;###autoload
(defun xml-reformat-tags ()
  "If point is on the open bracket of an XML tag, reformat that tree.
Note that this only works if the opening tag starts at column 0."
  (interactive)
  (save-excursion
    (let* ((beg (point)) (tags (read-xml)))
      (delete-region beg (point))
      (insert-xml tags t))))

;;; Internal Functions


;;; RTS did this 30/04/2001
(if (featurep 'xemacs)
    (defalias 'match-string-no-properties 'match-string))


(defun xml-parse-profile ()
  (interactive)
  (let ((elp-function-list
	 '(buffer-substring-no-properties
	   char-after
	   char-before
	   forward-char
	   looking-at
	   match-string-no-properties
	   match-beginning
	   match-end
	   point
	   re-search-forward
	   read-xml
	   xml-parse-read
	   search-forward
	   string=
	   stringp
	   substring
	   xml-parse-concat)))
    (elp-instrument-list)))

(defsubst xml-parse-skip-tag ()
  (cond
   ((eq (char-after) ??)
    (search-forward "?>"))
   ((looking-at "!--")
    (search-forward "-->"))
   (t					; must be <!...>
    (re-search-forward "[[>]")
    (if (eq (char-before) ?\[)
	(let ((depth 1))
	  (while (and (> depth 0)
		      (if (re-search-forward "[][]")
			  t
			(error "Pos %d: Unclosed open bracket in <! tag")))
	    (if (eq (char-before) ?\[)
		(setq depth (1+ depth))
	      (setq depth (1- depth))))
	  (search-forward ">"))))))

(defsubst xml-parse-add-non-ws (text lst)
  (let ((i 0) (l (length text)) non-ws)
    (while (< i l)
      (unless (memq (aref text i) '(?\n ?\t ? ))
	(setq i l non-ws t))
      (setq i (1+ i)))
    (if (not non-ws)
	lst
      (setcdr lst (list text))
      (cdr lst))))

(defsubst xml-parse-concat (beg end lst)
  "Add the string from BEG to END to LST, ignoring pure whitespace."
  (save-excursion
    (goto-char beg)
    (while (search-forward "<" end t)
      (setq lst (xml-parse-add-non-ws
		 (buffer-substring-no-properties beg (1- (point))) lst)
	    beg (1- (point)))
      (xml-parse-skip-tag)
      (setq lst (xml-parse-add-non-ws
		 (buffer-substring-no-properties beg (point)) lst)
	    beg (point)))
    (if (/= beg end)
	(setq lst (xml-parse-add-non-ws
		   (buffer-substring-no-properties beg end) lst)))
    lst))

(defun xml-parse-read (&optional progress-callback)
  (let ((beg (search-forward "<" nil t)) after)
    (if progress-callback
	(funcall progress-callback 
		 (* (/ (float (point)) (float (point-max))) 100)))
    (while (and beg (memq (setq after (char-after)) '(?! ??)))
      (xml-parse-skip-tag)
      (setq beg (search-forward "<" nil t)))
    (when beg
      (if (eq after ?/)
	  (progn
	    (search-forward ">")
	    (cons (1- beg)
		  (buffer-substring-no-properties (1+ beg) (1- (point)))))
	(skip-chars-forward "^ \t\n/>")
	(cons
	 (1- beg)
	 (progn
	   (setq after (point))
	   (skip-chars-forward " \t\n")
	   (let* ((single (eq (char-after) ?/))
		  (tag (buffer-substring-no-properties beg after))
		  attrs data-beg data)
	     ;; handle the attribute list, if present
	     (cond
	      (single
	       (skip-chars-forward " \t\n/>"))
	      ((eq (char-after) ?\>)
	       (forward-char 1))
	      (t
	       (let* ((attrs (list t))
		      (lastattr attrs)
		      (end (search-forward ">")))
		 (goto-char after)
		 (while (re-search-forward
			 "\\([^ \t\n=]+\\)=\"\\([^\"]+\\)\"" end t)
		   (let ((attr (cons (match-string-no-properties 1)
				     (match-string-no-properties 2))))
		     (setcdr lastattr (list attr))
		     (setq lastattr (cdr lastattr))))
		 (goto-char end)
		 (setq tag (cons tag (cdr attrs))
		       single (eq (char-before (1- end)) ?/)))))
	     ;; return the tag and its data
	     (if single
		 (list tag)
	       (setq tag (list tag))
	       (let ((data-beg (point)) (tag-end (last tag)))
		 (while (and (setq data (xml-parse-read progress-callback))
			     (not (stringp (cdr data))))
		   (setq tag-end (xml-parse-concat data-beg (car data)
						   tag-end)
			 data-beg (point))
		   (setcdr tag-end (list (cdr data)))
		   (setq tag-end (cdr tag-end)))
		 (xml-parse-concat data-beg (or (car data)
						(point-max)) tag-end)
		 tag)))))))))

(provide 'xml-parse)

;;; xml-parse.el ends here
