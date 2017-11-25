;;; ebdb-vcard.el --- vCard export and import routine for EBDB  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Free Software Foundation, Inc.

;; Author: Eric Abrahamsen <eric@ericabrahamsen.net>

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file contains formatting and parsing functions used to export
;; EBDB contacts to vcard format, and to create contacts from vcard
;; files.  It only supports VCard versions 3.0 and 4.0.

;; https://tools.ietf.org/html/rfc6350

;;; Code:

(require 'ebdb-format)

(autoload 'calendar-gregorian-from-absolute "calendar")

(defclass ebdb-formatter-vcard (ebdb-formatter)
  ((coding-system :initform 'utf-8-dos)
   (version-string
    :type string
    :allocation :class
    :documentation "The string to insert for this formatter's
    version."))
  :abstract t
  :documentation "Base formatter for vCard export.")

(defclass ebdb-formatter-vcard-30 (ebdb-formatter-vcard)
  ((version-string
    :initform "3.0"))
  :documentation "Formatter for vCard format 3.0.")

(defclass ebdb-formatter-vcard-40 (ebdb-formatter-vcard)
  ((version-string
    :initform "4.0"))
  :documentation "Formatter for vCard format 4.0.")

(defgroup ebdb-vcard nil
  "Customization options for EBDB vCard support."
  :group 'ebdb)

(defcustom ebdb-vcard-default-40-formatter
  (make-instance 'ebdb-formatter-vcard-40
		 :object-name "VCard 4.0 (default)"
		 :combine nil
		 :collapse nil
		 :include '(ebdb-field-uuid
			    ebdb-field-timestamp
			    ebdb-field-mail
			    ebdb-field-name
			    ebdb-field-address
			    ebdb-field-url
			    ebdb-field-role
			    ebdb-field-anniversary
			    ebdb-field-relation
			    ebdb-field-phone
			    ebdb-field-notes
			    ebdb-field-tags)
		 :header nil)
  "The default formatter for VCard 4.0 exportation."
  :group 'ebdb-vcard
  :type 'ebdb-formatter-vcard)

(defcustom ebdb-vcard-default-30-formatter
  (make-instance 'ebdb-formatter-vcard-30
		 :object-name "VCard 3.0 (default)"
		 :combine nil
		 :collapse nil
		 :include '(ebdb-field-uuid
			    ebdb-field-timestamp
			    ebdb-field-mail
			    ebdb-field-name
			    ebdb-field-address
			    ebdb-field-url
			    ebdb-field-role
			    ebdb-field-anniversary
			    ebdb-field-relation
			    ebdb-field-phone
			    ebdb-field-notes
			    ebdb-field-tags)
		 :header nil)
  "The default formatter for VCard 3.0 exportation."
  :group 'ebdb-vcard
  :type 'ebdb-formatter-vcard)

(defcustom ebdb-vcard-label-alist
  '(("REV" . ebdb-field-timestamp)
    ("NOTE" . ebdb-field-notes)
    ("X-CREATION-DATE" . ebdb-field-creation-date)
    ("UID" . ebdb-field-uuid)
    ("EMAIL" . ebdb-field-mail)
    ("TEL" . ebdb-field-phone)
    ("RELATED" . ebdb-field-relation)
    ("CATEGORIES" . ebdb-field-tags)
    ("BDAY" . ebdb-field-anniversary)
    ("ANNIVERSARY" . ebdb-field-anniversary)
    ("URL" . ebdb-field-url)
    ("ADR" . ebdb-field-address)
    ("NICKNAME" . ebdb-field-name-complex))
  "Correspondences between VCard properties and EBDB field classes.

This alist is neither exhaustive nor authoritative.  It's purpose
is to simplify property labeling during the export process, and
to classify properties during import.  The import process does
not always respect these headings."

  :group 'ebdb-vcard
  :type '(repeat
	  (cons string symbol)))

(defsubst ebdb-vcard-escape (str)
  "Escape commas, semi-colons and newlines in STR."
  (replace-regexp-in-string
   "\\([^\\]\\)\\([\n]+\\)" "\\1\\\\n"
   (replace-regexp-in-string "\\([^\\]\\)\\([,;]\\)" "\\1\\\\\\2" str)))

(defsubst ebdb-vcard-unescape (str)
  "Unescape escaped commas, semicolons and newlines in STR."
  (replace-regexp-in-string
   "\\\\n" "\n"
   (replace-regexp-in-string
    "\\\\\\([,;]\\)" "\\1" str)))

;; The RFC says fold any lines longer than 75 octets, excluding the
;; line break.  Folded lines are delineated by a CRLF plus a space or
;; tab.  Multibyte characters must not be broken.

;; TODO: This implementation assumes that Emacs' internal coding
;; system is similar enough to the utf-8 that the file will eventually
;; be written in that `string-bytes' (which returns a length according
;; to Emacs' own coding) will map accurately to what eventually goes
;; in the file.  Eli notes this is not really true, and could result
;; in unexpected behavior, and he recommends using
;; `filepos-to-bufferpos' instead.  Presumably that would involve
;; /first/ writing the vcf file, then backtracking and checking for
;; correctness.
(defun ebdb-vcard-fold-lines (text)
  "Fold lines in TEXT, which represents a vCard contact."
  (let ((lines (split-string text "\n"))
	outlines)
    (dolist (l lines)
      (while (> (string-bytes l) 75)	; Line is too long.
	(if (> (string-bytes l) (length l))
	    ;; Multibyte characters.
	    (let ((acc (string-to-vector l)))
	      (setq l nil)
	      (while (> (string-bytes (concat acc)) 75)
		;; Pop characters off the end of acc and stick them
		;; back in l, until acc is short enough to go in
		;; outlines.  Probably hideously inefficient.
		(push (aref acc (1- (length acc))) l)
		(setq acc (substring acc 0 -1)))
	      (push acc outlines)
	      (setq l (concat " " l)))
	  ;; No multibyte characters.
	  (push (substring l 0 75) outlines)
	  (setq l (concat " " (substring l 75)))))
      (push l outlines))
    (mapconcat #'identity (nreverse outlines) "\n")))

(defun ebdb-vcard-unfold-lines (text)
  "Unfold lines in TEXT, which represents a vCard contact."
  (replace-regexp-in-string "\n[\s\t]" "" text))

(cl-defmethod ebdb-fmt-process-fields ((_f ebdb-formatter-vcard)
				       (_record ebdb-record)
				       field-list)
  field-list)

(cl-defmethod ebdb-fmt-process-fields ((fmt ebdb-formatter-vcard)
				       (record ebdb-record-person)
				       field-list)
  "Process fields in FIELD-LIST.

All this does is split role instances into multiple fields."
  (let (org out-list)
    (dolist (f field-list)
      (if (object-of-class-p f 'ebdb-field-role)
	  ;; Split it apart.
	  (with-slots (org-uuid mail fields defunct) f
	    (unless defunct
	      (setq org (ebdb-gethash org-uuid 'uuid))
	      ;; Store the name of the organization in the TYPE
	      ;; parameter of the various properties.  I'd rather
	      ;; stick a UUID somewhere, but haven't immediately
	      ;; figured out how that would be done.
	      (push (cons "ORG"
			  (ebdb-record-name org))
		    out-list)
	      (push (cons (format "TITLE;TYPE=\"%s\"" (ebdb-record-name org))
			  (slot-value f 'object-name))
		    out-list)
	      (when (or mail fields)
		(dolist (elt (cons mail fields))
		  (push (cons
			 (format "%s;%s"
				 (ebdb-fmt-field-label fmt elt 'normal record)
				 (format "TYPE=\"%s\"" (ebdb-record-name org)))
			 (ebdb-fmt-field fmt elt 'normal record))
			out-list)))))
	(push f out-list)))
    out-list))

(cl-defmethod ebdb-fmt-record ((f ebdb-formatter-vcard)
			       (r ebdb-record))
  "Format a single record R in VCARD format."
  ;; Because of the simplicity of the VCARD format, we only collect
  ;; the fields, there's no need to sort them, and the only processing
  ;; that happens is for role fields.
  (let ((fields (ebdb-fmt-process-fields
		 f r
		 (ebdb-fmt-collect-fields f r)))
	header-fields body-fields)
    (setq header-fields
	  (list (slot-value r 'name))
	  body-fields
	  (mapcar
	   (lambda (fld)
	     ;; This is a silly hack, but...
	     (if (consp fld)
		 fld
	       (cons (ebdb-fmt-field-label f fld 'normal r)
		     (ebdb-fmt-field f fld 'normal r))))
	   fields))
    (concat
     (format "BEGIN:VCARD\nVERSION:%s\n"
	     (slot-value f 'version-string))
     (ebdb-fmt-record-header f r header-fields)
     (ebdb-fmt-record-body f r body-fields)
     "\nEND:VCARD\n")))

(cl-defmethod ebdb-fmt-record-header ((f ebdb-formatter-vcard)
				      (r ebdb-record)
				      (fields list))
  "Format the header of a VCARD record.

VCARDs don't really have the concept of a \"header\", so this
method is just responsible for formatting the record name."
  (let ((name (car fields)))
   (concat
    (format "FN:%s\n" (ebdb-string name))
    (format "N;SORT-AS=\"%s\":%s\n"
	    (ebdb-record-sortkey r)
	    (ebdb-fmt-field f name 'normal r)))))

(cl-defmethod ebdb-fmt-record-body ((_f ebdb-formatter-vcard)
				    (_r ebdb-record)
				    (fields list))
  (mapconcat
   (lambda (f)
     (format "%s:%s"
	     (car f) (cdr f)))
   fields
   "\n"))

(cl-defmethod ebdb-fmt-record-body :around ((_f ebdb-formatter-vcard-40)
					    (_r ebdb-record-person)
					    (_fields list))
  (let ((str (cl-call-next-method)))
    (concat str "\nKIND:individual")))

(cl-defmethod ebdb-fmt-record-body :around ((_f ebdb-formatter-vcard-40)
					    (_r ebdb-record-organization)
					    (_fields list))
  (let ((str (cl-call-next-method)))
    (concat str "\nKIND:org")))

(cl-defmethod ebdb-fmt-field ((_f ebdb-formatter-vcard)
			      (field ebdb-field)
			      _style
			      _record)
  (ebdb-vcard-escape (ebdb-string field)))

(cl-defmethod ebdb-fmt-field-label ((_f ebdb-formatter-vcard)
				    (field ebdb-field)
				    _style
				    _record)
  (car (rassoc (eieio-class-name
		(eieio-object-class field))
	       ebdb-vcard-label-alist)))

(cl-defmethod ebdb-fmt-field ((_f ebdb-formatter-vcard)
			      (mail ebdb-field-mail)
			      _style
			      _record)
  (slot-value mail 'mail))

(cl-defmethod ebdb-fmt-field ((_f ebdb-formatter-vcard)
			      (ts ebdb-field-timestamp)
			      _style
			      _record)
  (format-time-string "%Y%m%dT%H%M%S%z" (slot-value ts 'timestamp) t))

(cl-defmethod ebdb-fmt-field ((_f ebdb-formatter-vcard)
			      (name ebdb-field-name-complex)
			      _style
			      _record)
  (with-slots (surname given-names prefix suffix) name
    (format
     "%s;%s;%s;%s"
     (or surname "")
     (if given-names (mapconcat #'identity given-names ","))
     (or prefix "")
     (or suffix ""))))

(cl-defmethod ebdb-fmt-field-label ((_f ebdb-formatter-vcard)
				    (_field ebdb-field-uuid)
				    _style
				    _record)
  (concat (cl-call-next-method) ":urn:uuid"))

(cl-defmethod ebdb-fmt-field-label ((_f ebdb-formatter-vcard)
				    (mail ebdb-field-mail)
				    _style
				    _record)
  (with-slots (priority) mail
    (concat
     (cl-call-next-method)
     (cl-case priority
       ('primary ";PREF=1")
       ('normal ";PREF=10")
       ('defunct ";PREF=100")
       (t "")))))

(cl-defmethod ebdb-fmt-field-label ((_f ebdb-formatter-vcard)
			 	    (field ebdb-field-labeled)
				    _style
				    _record)
  (let ((ret (cl-call-next-method))
	(lab (slot-value field 'object-name)))
    (if lab
	(concat ret
		";TYPE=" (ebdb-vcard-escape lab))
      ret)))

(cl-defmethod ebdb-fmt-field ((_f ebdb-formatter-vcard)
			      (addr ebdb-field-address)
			      _style
			      _record)
  (with-slots (streets locality region postcode country) addr
    (concat ";;"
	    (mapconcat
	     #'ebdb-vcard-escape
	     streets ",")
	    (format
	     ";%s;%s;%s;%s"
	     (or locality "")
	     (or region "")
	     (or postcode "")
	     (or country "")))))

(cl-defmethod ebdb-fmt-field ((_f ebdb-formatter-vcard)
			      (rel ebdb-field-relation)
			      _style
			      _record)
  (concat "urn:uuid:" (slot-value rel 'rel-uuid)))

(cl-defmethod ebdb-fmt-field ((_f ebdb-formatter-vcard)
			      (tags ebdb-field-tags)
			      _style
			      _record)
  (ebdb-concat "," (slot-value tags 'tags)))

(cl-defmethod ebdb-fmt-field-label ((_f ebdb-formatter-vcard)
				    (ann ebdb-field-anniversary)
				    _style
				    _record)
  (let* ((label (slot-value ann 'object-name))
	 (label-string
	  (if (string= label "birthday")
	      "BDAY"
	    (concat "ANNIVERSARY;TYPE=" label))))
    (concat label-string (format ";CALSCALE=%s"
				 (slot-value ann 'calendar)))))

(cl-defmethod ebdb-fmt-field ((_f ebdb-formatter-vcard)
			      (ann ebdb-field-anniversary)
			      _style
			      _record)
  (pcase-let ((`(,month ,day ,year)
	       (calendar-gregorian-from-absolute
		(slot-value ann 'date))))
    (format "%d%02d%02d" year month day)))

(provide 'ebdb-vcard)
;;; ebdb-vcard.el ends here
