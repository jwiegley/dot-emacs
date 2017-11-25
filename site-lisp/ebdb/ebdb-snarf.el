;;; ebdb-snarf.el --- Creating or displaying records based on free-form pieces of text  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Free Software Foundation, Inc.

;; Author: Eric Abrahamsen <eric@ericabrahamsen.net>
;; Keywords: mail

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

;; This file provides functions for reading arbitrary bits of text,
;; interpreting them as records and fields, and then using them to
;; search/display/update/create records.

;; The main entry point is the interactive command `ebdb-snarf'.  It
;; figures out what text we're dealing with, puts the text in a temp
;; buffer, and calls three nested functions: `ebdb-snarf-collect',
;; which finds likely field-related strings in the buffer and groups
;; them, then `ebdb-snarf-collapse', which tries to match that
;; information to existing records, and finally `ebdb-snarf-query',
;; which queries the user about how to handle leftover
;; information. Any resulting records are then displayed.

;; The option `ebdb-snarf-routines' contains regexps that can be used
;; to construct field instances.  `ebdb-snarf-collect' uses the
;; elements of this list to search for relevant strings.

;; Country-specific internationalization libraries are highly
;; encouraged to add values to `ebdb-snarf-routines', locating field
;; information specific to that country/region/language.

;;; Code:

(require 'ebdb-com)

(defcustom ebdb-snarf-routines
  `((ebdb-field-mail "[[:blank:]([<\"]*\\([^[:space:]\":\n<[]+@[^]:[:space:])>\"\n]+\\)")
    (ebdb-field-url ,(concat "\\("
			     (regexp-opt ebdb-url-valid-schemes)
			     "//[^ \n\t]+\\)"))
    (ebdb-field-phone "\\(\\+?[[:digit:]]\\{1,3\\}[ )-.]?[[:digit:] -.()]+\\)"))

  "An alist of EBDB field classes and related regexps.

Each alist element is an EBDB field class symbol, followed by a
list of regular expressions that can be used to produce instances
of that class when passed to `ebdb-parse'.  Each regular
expression should contain at least one parenthetical group: the
`ebdb-parse' method of the class will receive the results of
\(match-string 1\)."

  :group 'ebdb-snarf
  :type 'list)

(defcustom ebdb-snarf-name-re
  (list "\\(?:[[:upper:]][[:lower:]'-]+[,.[:space:]]*\\)\\{2,\\}")

  "A list of regular expressions matching names.

This is a separate option from `ebdb-snarf-routines' because
snarfing doesn't search for names separately, only in conjunction
with other field types.

Regular expressions in this list should not include parenthetical
groups."

  :group 'ebdb-snarf
  :type 'list)

;;;###autoload
(defun ebdb-snarf (&optional string start end recs ret)
  "Snarf text and attempt to display/update/create a record from it.

If STRING is given, snarf the string.  If START and END are given
in addition to STRING, assume they are 0-based indices into it.
If STRING is nil but START and END are given, assume they are
buffer positions, and snarf the region between.  If all three
arguments are nil, snarf the entire current buffer.

If RECORDS is present, it is a list of records that we assume may
be relevant to snarfed field data.

If RET is non-nil, return the records.  Otherwise display them."
  (interactive)
  (let* ((str
	  (cond ((use-region-p)
		 (buffer-substring-no-properties
		  (region-beginning) (region-end)))
		((and (or start end) string)
		 (substring string start end))
		((and start end (null string))
		 (buffer-substring-no-properties start end))
		(string
		 string)
		(t
		 (buffer-string))))
	 (records
	  (ebdb-snarf-query
	   (ebdb-snarf-collapse
	    (ebdb-snarf-collect str recs)))))

    (if (null ret)
	(if records
	    (ebdb-display-records records nil t nil (list (selected-window)))
	  (message "No snarfable data found"))
      records)))

(defun ebdb-snarf-collect (str &optional records)
  "Collect EBDB record information from string STR.

This function will find everything that looks like field
information, and do its best to organize it into likely groups.
If RECORDS is given, it should be a list of records that we think
have something to do with the text in the buffer.

This function returns a list of vectors.  Each vector contains
three elements: a record, a list of name-class instances, and a
list of other field instances.  Any element can be nil."
  (let ((case-fold-search nil)
	;; BUNDLES is the list of vectors.  If RECORDS is given, then
	;; we have something to start with.
	(bundles (when records
		   (mapcar (lambda (r)
			     (vector r nil nil))
			   records)))
	;; We are looking for text like this:

	;; John Bob <john@bob.com>

	;; Try calling John Bob: (555) 555-5555

	;; John Bob
	;; John@bob.com
	;; (555) 555-5555
	;; 1111 Upsidedown Drive
	;; Nowhere, Massachusetts, 55555

	;; (Also see the snarfing tests in ebdb-test.el.)

	;; The tactic is: Make a big regexp that finds any probable
	;; field data.  Once there's a hit, search *backwards* for a
	;; name, and *forwards* for more fields.  All contiguous field
	;; data is grouped into the same bundle.  If the first field
	;; found is at bol, assume "block" style data, as in the third
	;; example above.  If it is not at bol, assume "inline" style
	;; data, as in the second example.

	;; Snarfing mail message data is very common, it would be nice
	;; to somehow disregard left-hand quotation characters and
	;; indendation.  A problem for another day.
	(big-re
	 (concat
	  "\\(?:"
	  (mapconcat
	   (lambda (r)
	     (if (stringp (cadr r))
		 (cadr r)
	       (mapconcat #'identity (cadr r) "\\|")))
	   ebdb-snarf-routines
	   "\\|")
	  "\\)"))
	bundle block name)

    (with-temp-buffer
      (insert str)
      (goto-char (point-min))
      (while (re-search-forward big-re nil t)
	(goto-char (match-beginning 0))
	(setq block (= (point) (point-at-bol)))
	(when (setq name
		    (save-excursion
		      (when (re-search-backward
			     (concat
			      "\\("
			      (mapconcat #'identity
					 ebdb-snarf-name-re "\\|")
			      "\\)")
			     (save-excursion
			       (if block
				   (progn (forward-line -1)
					  (line-beginning-position))
				 (point-at-bol)))
			     t)
			;; If something goes wrong with the
			;; name, don't worry about it.
			(ignore-errors
			  (ebdb-parse
			   'ebdb-field-name
			   (string-trim (match-string-no-properties 0)))))))
	  ;; If NAME matches one of the records that are already in
	  ;; BUNDLES, then assume we should be working with that record.
	  (dolist (b bundles)
	    (when (and (aref b 0)
		       (string-match-p (ebdb-string name)
				       (ebdb-string (aref b 0))))
	      (setq bundle b))))

	(unless bundle
	  (setq bundle (make-vector 3 nil))
	  (when name
	    (push name (aref bundle 1))))

	(dolist (class ebdb-snarf-routines)
	  (dolist (re (cdr class))
	    (while (re-search-forward re (if block
					     (save-excursion
					       (forward-line)
					       (line-end-position))
					   (point-at-eol))
				      t)
	      (condition-case nil
		  (push (ebdb-parse
			 (car class)
			 (match-string-no-properties 1))
			(aref bundle 2))

		;; If a regular expression matches but the result is
		;; unparseable, that means the regexp is bad and should be
		;; changed.  Later, report these errors if `ebdb-debug' is
		;; true.
		(ebdb-unparseable nil)))))
	(when bundle
	  (push bundle bundles)
	  (setq bundle nil))
	(when block
	  (beginning-of-line 2))))
    bundles))

(defun ebdb-snarf-collapse (input)
  "Process INPUT, which is a list of bundled field information.

INPUT is probably produced by `ebdb-snarf-collect'.  It should be
a list of vectors, each with three elements: a single record, a
list of name field instances, and a list of other field
instances.  Any of the three elements can be nil.

Compare each bundle against the database, and where possible find
existing records that match information in the bundle.  Discard
redundant fields, or fields that are incompatible with the record
they're grouped with.  Return the same list of (possibly altered)
vectors, usually to `ebdb-snarf-query'."
  (let (output rec slot-val)
    (pcase-dolist (`[,record ,names ,fields] input)
      (let (out-fields out-names)
	(unless record
	  (when (setq rec (car-safe
			   (ebdb-search
			    (ebdb-records)
			    (mapcar
			     (lambda (f)
			       (list (eieio-object-class-name f)
				     (ebdb-string f)))
			     (append fields names)))))
	    (setq record rec)))
	(if record
	    (let (slot)
	      (dolist (f fields)
		(condition-case nil
		    (progn
		      (setq slot (car (ebdb-record-field-slot-query
				       (eieio-object-class record)
				       `(nil . ,(eieio-object-class f)))))
		      ;; Make sure that record can accept field, and doesn't
		      ;; already have it.
		      (unless
			  (when (setq slot-val (ignore-errors
						 (ebdb-record-field record slot)))
			    (member (ebdb-string f)
				    (mapcar #'ebdb-string
					    (if (listp slot-val)
						slot-val
					      (list slot-val)))))
			(push f out-fields)))
		  (ebdb-unacceptable-field nil)))
	      (dolist (name names)
		(unless (ebdb-record-search
			 record 'ebdb-field-name (ebdb-string name))
		  (push name out-names))))
	  (setq out-names names
		out-fields fields))
	(push (vector record out-names out-fields) output)))
    output))

(defun ebdb-snarf-query (input)
  "Query the user about INPUT, which is a list of vectors of
  bundled information representing records.

Ask about field instances that we haven't been able to handle
automatically."
  (let (leftovers records record)
    (pcase-dolist (`[,record ,names ,fields] input)
      (unless record
	;; There's no record, query-create a new one.
	(when (yes-or-no-p
	       (format "Create new record%s? "
		       (if (or fields names)
			   (format " for fields %s"
				   (mapconcat #'ebdb-string
					      (append fields names)
					      "/"))
			 "")))
	  ;; Which name do we use?
	  (let* ((name-alist
		  (when names
		    (mapcar (lambda (n)
			      (cons (ebdb-string n)
				    n))
			    names)))
		 (name
		  ;; I hate completing read.
		  (cond ((= 1 (length name-alist))
			 (cdar name-alist))
			(name-alist
			 (cdr
			  (assoc-string
			   (completing-read
			    "Use name: "
			    name-alist)
			   name-alist)))
			(t nil))))
	    (setq record
		  (make-instance
		   ebdb-default-record-class
		   :name (ebdb-read
			  ebdb-default-name-class nil
			  name)))
	    (when name
	      (setq names (delq name names)))
	    (ebdb-db-add-record (car ebdb-db-list) record)
	    (ebdb-init-record record))))
      (if record
	  ;; We have a record, which of the fields and names should we
	  ;; add to it?
	  (progn (dolist (elt fields)
		   (if (yes-or-no-p (format "Add %s to %s? "
					    (ebdb-string elt)
					    (ebdb-string record)))
		       (condition-case nil
			   (ebdb-record-insert-field
			    record elt)
			 (ebdb-init-field elt record)
			 (ebdb-unacceptable-field nil))
		     (push elt leftovers)))
		 (dolist (n names)
		   (if (yes-or-no-p (format "Add %s as an aka for %s? "
					    (ebdb-string n)
					    (ebdb-string record)))
		       (progn (ebdb-record-insert-field
			       record n 'aka)
			      (ebdb-init-field n record))
		     (push n leftovers))))
	;; We have no record, dump all the fields into LEFTOVERS.
	(setq leftovers (append fields names leftovers)
	      fields nil
	      names nil))
      (when record
	(push record records)))
    ;; Handle fields in LEFTOVERS.
    (dolist (f (delete-dups leftovers))
      (when (setq record
		  (cond ((yes-or-no-p
			  (format "Add %s to existing record? "
				  (ebdb-string f)))
			 (ebdb-prompt-for-record))
			((yes-or-no-p
			  (format "Add %s to new record? "
				  (ebdb-string f)))
			 (ebdb-init-record
			  (ebdb-db-add-record
			   (car ebdb-db-list)
			   (ebdb-read ebdb-default-record-class))))
			(t nil)))
	(condition-case nil
	    (progn
	      (ebdb-record-insert-field record f)
	      (ebdb-init-field f record)
	      (add-to-list records record))
	  (ebdb-unacceptable-field nil))))
    records))

(provide 'ebdb-snarf)
;;; ebdb-snarf.el ends here
