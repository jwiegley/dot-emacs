;;; ebdb-format.el --- Formatting/exporting EBDB records  -*- lexical-binding: t; -*-

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

;; This file contains code for take record objects and turning them
;; into text, somehow.  It provides the basic framework that is used
;; for creating the *EBDB* buffer as well as exporting to vcard,
;; latex, and html formats.

;;; Code:

(require 'ebdb)
(declare-function ebdb-do-records "ebdb-com")
(declare-function ebdb-display-records "ebdb-com")
;; qp = quoted-printable, might not end up needing this.
(require 'qp)

(defvar ebdb-formatter-tracker nil
  "Variable for holding all instantiated formatters.")

(defclass ebdb-formatter (eieio-named eieio-instance-tracker)
  ((tracking-symbol :initform ebdb-formatter-tracker)
   (coding-system
    :type symbol
    :initarg :coding-system
    ;; "`," is used to trick EIEIO into evaluating the form.
    :initform `,buffer-file-coding-system
    :documentation "The coding system for the formatted
    file/buffer/stream.")
   ;; TODO: Provide for "psuedo field classes" like 'primary-mail and
   ;; 'role-mail.
   (include
    :type list
    :initarg :include
    :initform nil
    :documentation "A list of field classes to include.  If
    \"include\" and \"exclude\" conflict, \"exclude\" loses.")
   (exclude
    :type list
    :initarg :exclude
    :initform '(ebdb-field-uuid ebdb-field-timestamp ebdb-field-creation-date)
    :documentation "A list of field classes to exclude.")
   (sort
    :type list
    :initarg :sort
    :initform '(ebdb-field-mail ebdb-field-phone ebdb-field-address "_" ebdb-field-notes)
    :documentation "How field instances should be sorted.  Field
    classes should be listed in their proper sort order.  A \"_\"
    placeholder indicates where all other fields should go." )
   (primary
    :type boolean
    :initarg :primary
    :initform nil)
   (header
    :type list
    :initarg :header
    :initform  '((ebdb-record-person ebdb-field-role ebdb-field-image)
		 (ebdb-record-organization ebdb-field-domain ebdb-field-image))
    :documentation "A list of field classes which will be output
    in the header of the record, grouped by record class type.")
   (combine
    :type list
    :initarg :combine
    :initform '(ebdb-field-mail ebdb-field-phone)
    :documentation "A list of field classes which should be
    output with all instances grouped together.")
   (collapse
    :type list
    :initarg :collapse
    :initform '(ebdb-field-address)
    :documentation "A list of field classes which should be
    \"collapsed\". What this means is up to the formatter, but it
    generally indicates that most of the field contents will
    hidden unless the user takes some action, such as clicking or
    hitting <TAB>.  (Currently unimplemented.)")
   (post-format-function
    :type (or null function)
    :initarg :post-format-function
    :initform nil
    :documentation "A function to be called after formatting is
    complete.  Probably a major mode."))
  :abstract t
  :documentation "Abstract base class for EBDB formatters.
  Subclass this to produce real formatters.")

(cl-defmethod ebdb-string ((fmt ebdb-formatter))
  (slot-value fmt 'object-name))

(cl-defgeneric ebdb-fmt-header (fmt records)
  "Insert a string at the beginning of the list of records.")

(cl-defgeneric ebdb-fmt-footer (fmt records)
  "Insert a string at the end of the list of records.")

(cl-defgeneric ebdb-fmt-record (fmt record)
  "Handle the insertion of formatted RECORD.

This method collects all the fields to be output for RECORD,
groups them into header fields and body fields, and then calls
`ebdb-fmt-record-header' and `ebdb-fmt-record-body' with the two
lists, respectively.")

(cl-defgeneric ebdb-fmt-record-header (fmt record fields)
  "Format a header for RECORD, using the fields in FIELDS.")

(cl-defgeneric ebdb-fmt-record-body (fmt record fields)
  "Format the body of RECORD, using the fields in FIELDS.")

(cl-defgeneric ebdb-fmt-collect-fields (fmt record &optional fields)
  "Return a list of RECORD's FIELDS to be formatted.")

(cl-defgeneric ebdb-fmt-process-fields (fmt record &optional fields)
  "Process the FIELDS belonging to RECORD.
This means grouping them into lists containing various formatting
information, mostly drawn from FMT's `combine' and `collapse'
slots.")

(cl-defgeneric ebdb-fmt-sort-fields (fmt record &optional fields)
  "Sort FIELDS belonging to RECORD according to FMT.")

;; Do we still need this now that formatters and specs are collapsed?
(cl-defgeneric ebdb-fmt-compose-field (fmt field-cons record)
  "Convert the lists produced by `ebdb-fmt-process-fields'.
The lists of class instances and formatting information are
turned into lists holding labels strings and instance strings.")

(cl-defgeneric ebdb-fmt-field (fmt field style record)
  "Format FIELD value of RECORD.

This method only returns the string value of FIELD itself,
possibly with text properties attached.")

(cl-defgeneric ebdb-fmt-field-label (fmt field-or-class style record)
  "Format a field label, using formatter FMT.

FIELD-OR-CLASS is a field class or a field instance, and STYLE is
a symbol indicating a style of some sort, such as 'compact or
'expanded.")

;;; Basic method implementations

(cl-defmethod ebdb-fmt-header (_fmt _records)
  "")

(cl-defmethod ebdb-fmt-footer (_fmt _records)
  "")

(cl-defmethod ebdb-fmt-compose-field ((fmt ebdb-formatter)
				      field-plist
				      (record ebdb-record))
  "Turn FIELD-PLIST into a list structure suitable for formatting.

The FIELD-PLIST structure is that returned by
`ebdb-fmt-collect-fields'.  It is a plist with three
keys: :class, :style, and :inst.

This function passes the class and field instances to FMT, which
formats them appropriately, and returns a list of (LABEL
FIELD-STRING1 FIELD-STRING2 ..)."
  (let* ((style (plist-get field-plist :style))
	 (inst (plist-get field-plist :inst))
	 (label (ebdb-fmt-field-label fmt
				      (if (= 1 (length inst))
					  (car inst)
					(plist-get field-plist :class))
				      style
				      record)))
    (cons label
	  (mapcar
	   (lambda (f)
	     (ebdb-fmt-field fmt f style record))
	   inst))))

(cl-defmethod ebdb-fmt-field-label ((_fmt ebdb-formatter)
				    (cls (subclass ebdb-field))
				    _style
				    (_record ebdb-record))
  (ebdb-field-readable-name cls))

(cl-defmethod ebdb-fmt-field-label ((_fmt ebdb-formatter)
				    (field ebdb-field)
				    _style
				    (_record ebdb-record))
  (ebdb-field-readable-name field))

(cl-defmethod ebdb-fmt-field-label ((_fmt ebdb-formatter)
				    (field ebdb-field-labeled)
				    _style
				    (_record ebdb-record))
  (eieio-object-name-string field))

(cl-defmethod ebdb-fmt-field-label ((_fmt ebdb-formatter)
				    (field ebdb-field-labeled)
				    (_style (eql compact))
				    (_record ebdb-record))
  (ebdb-field-readable-name field))

(cl-defmethod ebdb-fmt-field ((fmt ebdb-formatter)
			      (field ebdb-field-labeled)
			      (_style (eql compact))
			      (record ebdb-record))
  (format "(%s) %s"
	  (eieio-object-name-string field)
	  (ebdb-fmt-field fmt field 'oneline record)))

(cl-defmethod ebdb-fmt-field ((_fmt ebdb-formatter)
			      (field ebdb-field)
			      (_style (eql oneline))
			      (_record ebdb-record))
  (car (split-string (ebdb-string field) "\n")))

(cl-defmethod ebdb-fmt-field ((fmt ebdb-formatter)
			      (field ebdb-field)
			      (_style (eql collapse))
			      (record ebdb-record))
  "For now, treat collapse the same as oneline."
  (ebdb-fmt-field fmt field 'oneline record))

(cl-defmethod ebdb-fmt-field ((_fmt ebdb-formatter)
			      (field ebdb-field)
			      _style
			      (_record ebdb-record))
  "The base implementation for FIELD simply returns the value of
  `ebdb-string'."
  (ebdb-string field))

(cl-defmethod ebdb-fmt-collect-fields ((fmt ebdb-formatter)
				       (record ebdb-record)
				       &optional field-list)
  "Collect all fields of RECORD, and filter according to FMT."
  ;; Remove the `name' slot entry from the list.
  (let ((fields (append
		 field-list
		 (mapcar #'cdr
			 (seq-remove
			  ;; The or (null (cdr elt)) is there to
			  ;; protect against an earlier bug with
			  ;; timestamps and creation-dates, it could
			  ;; be removed at some point.
			  (lambda (elt) (or (eql (car elt) 'name)
					    (null (cdr elt))))
 			  (ebdb-record-current-fields record nil t)))))
	f-class)
    (with-slots (exclude include) fmt
      (seq-filter
       (lambda (f)
	 (setq f-class (eieio-object-class-name f))
	 (if include
	     (ebdb-class-in-list-p f-class include)
	   (null (ebdb-class-in-list-p f-class exclude))))
       fields))))

(cl-defmethod ebdb-fmt-collect-fields ((fmt ebdb-formatter)
				       (record ebdb-record-organization)
				       &optional field-list)
  (cl-call-next-method
   fmt record
   (append field-list (gethash (ebdb-record-uuid record) ebdb-org-hashtable))))

(cl-defmethod ebdb-fmt-sort-fields ((fmt ebdb-formatter)
				    (_record ebdb-record)
				    field-list)
  (let ((sort (slot-value fmt 'sort))
	f acc outlist class)
    (when sort
      (dolist (s sort)
	(if (symbolp s)
	    (progn
	      (setq class (cl--find-class s))
	      (while (setq f (pop field-list))
		(if (same-class-p f class)
		    (push f outlist)
		  (push f acc)))
	      (setq field-list acc
		    acc nil))
	  ;; We assume this is the "_" value.  Actually, anything
	  ;; would do as a catchall placeholder.
	  (dolist (fld field-list)
	    (setq class (eieio-object-class-name fld))
	    (unless (memq class sort)
	      ;; This isn't enough -- field still need to be grouped
	      ;; by field class.
	      (push fld outlist)))))
      (setq field-list (nreverse outlist)))
    field-list))

(cl-defmethod ebdb-fmt-process-fields ((fmt ebdb-formatter)
				       (_record ebdb-record)
				       field-list)
  "Process FIELD-LIST for FMT.

At present that means handling the combine and collapse slots of
FMT.

This method assumes that fields in FIELD-LIST have already been
grouped by field class."
  (let (outlist cls f acc)
    (with-slots (combine collapse) fmt
      (when combine
	(while (setq f (pop field-list))
	  (setq cls (eieio-object-class-name f))
	  (if (null (ebdb-class-in-list-p cls combine))
	      (push f outlist)
	    (push f acc)
	    (while (and field-list (same-class-p (car field-list) (eieio-object-class f)))
	      (push (setq f (pop field-list)) acc))
	    (push `(:class ,cls :style compact :inst ,acc) outlist)
	    (setq acc nil)))
	(setq field-list (nreverse outlist)
	      outlist nil))
      (dolist (f field-list)
	(if (listp f)
	    (push f outlist)
	  (setq cls (eieio-object-class-name f))
	  (push (list :class cls
		      :inst (list f)
		      :style
		      (cond
		       ((ebdb-class-in-list-p cls collapse) 'collapse)
		       (t 'normal)))
		outlist)))
      outlist)))

;;; Basic export routines

(defcustom ebdb-format-buffer-name "*EBDB Format*"
  "Default name of buffer in which to display formatted records."
  :type 'string
  :group 'ebdb-record-display)

(defun ebdb-prompt-for-formatter ()
  (interactive)
  (let ((collection
	 (mapcar
	  (lambda (formatter)
	    (cons (slot-value formatter 'object-name) formatter))
	  ebdb-formatter-tracker)))
    (cdr (assoc (completing-read "Use formatter: " collection)
		collection))))

;;;###autoload
(defun ebdb-format-to-tmp-buffer (&optional formatter records)
  (interactive
   (list (ebdb-prompt-for-formatter)
	 (ebdb-do-records)))
  (let ((buf (get-buffer-create ebdb-format-buffer-name))
	(fmt-coding (slot-value formatter 'coding-system))
	(ebdb-p (object-of-class-p formatter 'ebdb-formatter-ebdb)))
    ;; If the user has chosen an ebdb formatter, we need to
    ;; special-case it.  First because the ebdb formatters handle
    ;; insertion themselves and the other formatters don't, which was
    ;; arguably a bad choice.  Second because ebdb formatting should
    ;; behave differently here -- we assume that what the user
    ;; actually wants is a text-mode buffer containing the text that
    ;; *would have been* displayed in an *EBDB* buffer, but with all
    ;; properties removed.
    (if ebdb-p
	(save-window-excursion
	  (ebdb-display-records records formatter nil nil nil " *EBDB Fake Output*")
	  (let ((str (buffer-substring-no-properties
		      (point-min) (point-max))))
	    (with-current-buffer buf
	      (erase-buffer)
	      (insert str))))
      (with-current-buffer buf
	(erase-buffer)
	(insert (ebdb-fmt-header formatter records))
	(dolist (r records)
	  (insert (ebdb-fmt-record formatter r)))
	(insert (ebdb-fmt-footer formatter records))
	(set-buffer-file-coding-system fmt-coding)))
    (pop-to-buffer buf)
    (let ((f (slot-value formatter 'post-format-function)))
      (when (fboundp f)
	(funcall f)))))

;;;###autoload
(defun ebdb-format-all-records (&optional formatter)
  (interactive
   (list (ebdb-prompt-for-formatter)))
  (ebdb-format-to-tmp-buffer formatter (ebdb-records)))

(provide 'ebdb-format)
;;; ebdb-format.el ends here
