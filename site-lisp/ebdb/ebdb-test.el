;;; ebdb-test.el --- Tests for EBDB                  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Free Software Foundation, Inc.

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

;; Tests for EBDB.  Tests for EBDB's internationalization support are
;; in a separate file, since loading ebdb-i18n.el overloads a bunch of
;; methods, and un-overloading them is difficult.

;;; Code:

(require 'ert)
(require 'ebdb)
(require 'ebdb-com)
(require 'ebdb-snarf)
(require 'ebdb-vcard)

;; Testing macros.

(defmacro ebdb-test-with-database (db-and-filename &rest body)
  "Macro providing a temporary database to work with."
  (declare (indent 1) (debug ((symbolp symbolp) body)))
  `(let ((,(car db-and-filename) (make-instance 'ebdb-db-file
						:file ,(nth 1 db-and-filename)
						:dirty t))
	 ebdb-db-list)
     ;; Save sets sync-time.
     (ebdb-db-save ,(car db-and-filename) nil t)
     ;; Load adds to `ebdb-db-list'.
     (ebdb-db-load ,(car db-and-filename))
     ;; `ebdb-db-load' used to add db to `ebdb-db-list', but now that
     ;; happens in `edbd-load'.  Do it manually.
     (push ,(car db-and-filename) ebdb-db-list)
     (unwind-protect
	 (progn
	   ,@body)
       (delete-file ,(nth 1 db-and-filename)))))

(defmacro ebdb-test-with-records (&rest body)
  "Don't let EBDB tests pollute `ebdb-record-tracker'."
  (declare (indent 0) (debug t))
  `(let ((ebdb-hashtable (make-hash-table :test 'equal))
	 (ebdb-org-hashtable (make-hash-table :test 'equal))
	 ebdb-record-tracker)
     ,@body))

;; Test database file name.
(defvar ebdb-test-database-1 (make-temp-name
			      (expand-file-name
			       "emacs-ebdb-test-db-1-"
			       temporary-file-directory)))

(defvar ebdb-test-database-2 (make-temp-name
			      (expand-file-name
			       "emacs-ebdb-test-db-2-"
			       temporary-file-directory)))

(ert-deftest ebdb-make-database ()
  "Make a database and save it to disk."
  (ebdb-test-with-database (db ebdb-test-database-1)
    (should (file-exists-p ebdb-test-database-1))
    (should (null (slot-value db 'dirty)))))

(ert-deftest ebdb-read-database ()
  "Read a database from file."
  (ebdb-test-with-database (db ebdb-test-database-1)
    (let ((reloaded
	   (eieio-persistent-read ebdb-test-database-1 'ebdb-db t)))
      (should (object-of-class-p reloaded 'ebdb-db-file)))))

(ert-deftest ebdb-database-unsynced ()
  "Make sure database knows it's unsynced."
  (ebdb-test-with-database (db ebdb-test-database-1)
    ;; Apparently the call to `ebdb-db-load' and the test are too
    ;; close together to register a difference in time, which I find
    ;; weird.
    (sit-for 0.1)
    (append-to-file "\n;; Junk string" nil (slot-value db 'file))
    (should (ebdb-db-unsynced db))))

(ert-deftest ebdb-make-record ()
  (ebdb-test-with-records
   (let ((rec (make-instance ebdb-default-record-class)))
     (should (object-of-class-p rec 'ebdb-record)))))

(ert-deftest ebdb-add-record ()
  "Create a record, add it to DB, and make sure it has a UUID."
  (ebdb-test-with-records
    (ebdb-test-with-database (db ebdb-test-database-1)
      (let ((rec (make-instance 'ebdb-record-person)))
	(should (null (ebdb-record-uuid rec)))
	(ebdb-db-add-record db rec)
	(should (stringp (ebdb-record-uuid rec)))
	(should (ebdb-gethash (ebdb-record-uuid rec) 'uuid))))))

(ert-deftest ebdb-load-record-multiple-databases ()
  "Test loading of a record into multiple databases."
  (ebdb-test-with-records
    (ebdb-test-with-database (db1 ebdb-test-database-1)
      (ebdb-test-with-database (db2 ebdb-test-database-2)
	(let ((rec (make-instance 'ebdb-record-person)))
	  (ebdb-db-add-record db1 rec)
	  (ebdb-db-add-record db2 rec)
	  (should (= 1 (length ebdb-record-tracker)))
	  (should (equal rec (ebdb-gethash (ebdb-record-uuid rec) 'uuid))))))))

(ert-deftest ebdb-load-record-multiple-databases-error ()
  "Test that record can't be edited when one of its databases is
  read-only."
  (ebdb-test-with-records
    (ebdb-test-with-database (db1 ebdb-test-database-1)
      (ebdb-test-with-database (db2 ebdb-test-database-2)
	(let ((rec (make-instance 'ebdb-record-person)))
	  (ebdb-db-add-record db1 rec)
	  (ebdb-db-add-record db2 rec)
	  (setf (slot-value db1 'read-only) t)
	  (should-error
	   (ebdb-record-insert-field
	    rec (ebdb-parse 'ebdb-field-mail "none@such.com"))
	   :type 'ebdb-readonly-db))))))

(ert-deftest ebdb-auto-insert-timestamp-creation ()
  "Test the creation of timestamp and creation-date fields.
Actually exercises the `initialize-instance' methods of records."
  (ebdb-test-with-records
    (ebdb-test-with-database (db ebdb-test-database-1)
      (let* ((r1 (make-instance ebdb-default-record-class))
	     (r2 (make-instance ebdb-default-record-class
				:timestamp nil
				:creation-date nil))
	     (r2-date (slot-value (slot-value r2 'creation-date) 'timestamp)))
	;; `make-instance' with no :timestamp or :creation-date values
	;; should get the fields correctly.
	(should (and (stringp (ebdb-string (slot-value r1 'timestamp)))
		     (stringp (ebdb-string (slot-value r1 'creation-date)))))
	(delete-instance r1)
	;; `make-instance' with tags set to nil should still get
	;; correct fields (can happen in migration).
	(should (and (stringp (ebdb-string (slot-value r2 'timestamp)))
		     (stringp (ebdb-string (slot-value r2 'creation-date)))))
	;; Creating a record, saving it to the database, then
	;; re-loading it shouldn't change the creation date.
	(ebdb-db-add-record db r2)
	(ebdb-db-save db)
	(sleep-for 2)
	(ebdb-db-unload db)
	(setq db (eieio-persistent-read (slot-value db 'file) 'ebdb-db t))
	(should (equal r2-date
		       (slot-value
			(slot-value
			 (car ebdb-record-tracker)
			 'creation-date)
			'timestamp)))))))

(ert-deftest ebdb-cant-find-related-role ()
  "Find org record from a role field.
If it doesn't exist, raise `ebdb-related-unfound'."
  (ebdb-test-with-records
   (let ((rec (make-instance
	       'ebdb-record-person
	       :uuid (make-instance 'ebdb-field-uuid :uuid "bob")))
	 (role
	  (make-instance
	   'ebdb-field-role :record-uuid "bob"
	   :org-uuid "bogus")))
     (ebdb-record-insert-field rec role)
     (should-error
      (ebdb-record-related rec role)
      :type 'ebdb-related-unfound))))

(ert-deftest ebdb-unload-db-with-relations ()
  "Cross-db relations break correctly when a db is unloaded."
  (ebdb-test-with-records
    (ebdb-test-with-database (db1 ebdb-test-database-1)
      (ebdb-test-with-database (db2 ebdb-test-database-2)
	(let ((rec1 (make-instance 'ebdb-record-person))
	      (rec2 (make-instance 'ebdb-record-person))
	      rel-f)
	  (ebdb-db-add-record db1 rec1)
	  (ebdb-db-add-record db2 rec2)
	  (setq rel-f (make-instance
		       'ebdb-field-relation :rel-uuid (ebdb-record-uuid rec2)))
	  (ebdb-record-insert-field rec1 rel-f)
	  (ebdb-db-unload db2)
	  (should-error
	   (ebdb-record-related rec1 rel-f)
	   :type 'ebdb-related-unfound)
	  (should
	   (string=
	    (ebdb-fmt-field
	     ebdb-default-multiline-formatter
	     rel-f 'oneline rec1)
	    "record not loaded")))))))

(ert-deftest ebdb-test-with-record-edits ()
  "Test the `ebdb-with-record-edits' macro."
  (ebdb-test-with-records
    (ebdb-test-with-database (db1 ebdb-test-database-1)
      (ebdb-test-with-database (db2 ebdb-test-database-2)
	(let ((rec1 (make-instance 'ebdb-record-person))
	      (rec2 (make-instance 'ebdb-record-person)))
	  (ebdb-db-add-record db1 rec1)
	  (ebdb-db-add-record db2 rec1)
	  (ebdb-db-add-record db1 rec2)
	  (setf (slot-value db2 'read-only) t)
	  (ebdb-with-record-edits (r (list rec1 rec2))
	    (ebdb-record-insert-field
	     r (ebdb-parse 'ebdb-field-mail "none@such.com")))
	  ;; rec1 should have been excluded from the list of editable
	  ;; records, but no error should be raised.
	  (should-not
	   (slot-value rec1 'mail)))))))

;; Test adding, deleting and changing fields.

(ert-deftest ebdb-add-delete-record-field ()
  "Add and delete fields."
  (ebdb-test-with-records
    (let ((rec (make-instance 'ebdb-record-person))
	  (mail (ebdb-parse ebdb-default-mail-class
			    "bogus@nosuchaddress.com"))
	  (phone (ebdb-parse ebdb-default-phone-class
			     "+1 (555) 555-5555")))
      ;; Pass slot explicitly.
      (ebdb-record-insert-field rec mail 'mail)
      ;; Let the method find the slot.
      (ebdb-record-insert-field rec phone)
      (should (object-of-class-p
	       (car (ebdb-record-phone rec))
	       'ebdb-field-phone))
      (should (object-of-class-p
	       (car (ebdb-record-mail rec))
	       'ebdb-field-mail))
      (ebdb-record-delete-field rec mail)
      (ebdb-record-delete-field rec phone 'phone)
      (should (null (ebdb-record-mail rec)))
      (should (null (ebdb-record-phone rec))))))

(ert-deftest ebdb-insert-unacceptable ()
  "Make sure records reject unacceptable fields."
  (ebdb-test-with-records
    (let ((rec (make-instance 'ebdb-record-person))
	  (field (make-instance 'ebdb-field-domain :domain "gnu.org")))
      (should-error (ebdb-record-field-slot-query
		     'ebdb-record-person (cons nil 'ebdb-field-domain))
		    :type 'ebdb-unacceptable-field)
      (should-error (ebdb-record-insert-field rec field)
		    :type 'ebdb-unacceptable-field))))

(ert-deftest ebdb-change-record-field ()
  "Change record's field."
  (ebdb-test-with-records
    (let ((rec (make-instance 'ebdb-record-person))
	  (mail (ebdb-parse ebdb-default-mail-class
			    "bogus@nosuchaddress.com"))
	  (mail2 (ebdb-parse ebdb-default-mail-class
			     "no@such.address")))
      (ebdb-record-insert-field rec mail)
      (should (string= (ebdb-string (car (ebdb-record-mail rec)))
		       "bogus@nosuchaddress.com"))
      (ebdb-record-change-field rec mail mail2)
      (should (string= (ebdb-string (car (ebdb-record-mail rec)))
		       "no@such.address")))))

;; Field instance parse tests.

;; Test `ebdb-decompose-ebdb-address'

(ert-deftest ebdb-address-decompose ()
  "Test `ebdb-decompose-ebdb-address'."
  (should (equal '("Charles Lamb" "charlie@lamb.com")
		 (ebdb-decompose-ebdb-address
		  "Charles Lamb <charlie@lamb.com>")))

  (should (equal '("Charles Lamb" "charlie@lamb.com")
		 (ebdb-decompose-ebdb-address
		  "Charles Lamb mailto:charlie@lamb.com")))

  (should (equal '("Charles Lamb" "charlie@lamb.com")
		 (ebdb-decompose-ebdb-address
		  "\"Charles Lamb\" charlie@lamb.com")))

  (should (equal '("Charles Lamb" "charlie@lamb.com")
		 (ebdb-decompose-ebdb-address
		  "charlie@lamb.com (Charles Lamb)")))

  (should (equal '(nil "charlie@lamb.com")
		 (ebdb-decompose-ebdb-address
		  "\"charlie@lamb.com\" charlie@lamb.com")))

  (should (equal '(nil "charlie@lamb.com")
		 (ebdb-decompose-ebdb-address
		  "<charlie@lamb.com>")))

  (should (equal '(nil "charlie@lamb.com")
		 (ebdb-decompose-ebdb-address
		  "charlie@lamb.com <charlie@lamb.com>")))

  (should (equal '("Charles Lamb" nil)
		 (ebdb-decompose-ebdb-address
		  "Charles Lamb"))))

(ert-deftest ebdb-parse-mail ()
  "Parse various strings as mail fields."
  (should (equal
	   (slot-value
	    (ebdb-parse 'ebdb-field-mail "William Hazlitt <bill@theexaminer.com>")
	    'aka)
	   "William Hazlitt"))
  (should (equal
	   (slot-value
	    (ebdb-parse 'ebdb-field-mail "William Hazlitt <bill@theexaminer.com>")
	    'mail)
	   "bill@theexaminer.com"))
  (should-error (ebdb-parse 'ebdb-field-mail "William Hazlitt")
		:type 'ebdb-unparseable))

(ert-deftest ebdb-parse-name ()
  "Parse various strings as name fields."
  (should (equal
	   (slot-value
	    (ebdb-parse 'ebdb-field-name-complex "Eric Abrahamsen")
	    'surname)
	   "Abrahamsen"))
  (should (equal
	   (slot-value
	    (ebdb-parse 'ebdb-field-name-complex "Eric P. Abrahamsen")
	    'given-names)
	   '("Eric" "P.")))
  (should (equal
	   (slot-value
	    (ebdb-parse 'ebdb-field-name-complex "Eric Abrahamsen, III")
	    'suffix)
	   "III")))

;; Snarf testing.

(ert-deftest ebdb-snarf-mail-and-name ()
  (let ((test-texts
	 '("Eric Abrahamsen <eric@ericabrahamsen.net>"
	   "Eric Abrahamsen eric@ericabrahamsen.net"
	   "Eric Abrahamsen (eric@ericabrahamsen.net)"
	   "Eric Abrahamsen \n<eric@ericabrahamsen.net>"
	   "Eric Abrahamsen can't hold his drink\n<eric@ericabrahamsen.net> is where you can write and tell him so."))
	result)
    (dolist (text test-texts)
      (setq result (car (ebdb-snarf-collect text)))
      (pcase result
	(`[nil (,name) (,mail)]
	 (unless (string= (ebdb-string name) "Eric Abrahamsen")
	   (ert-fail (list (format "Parsing \"%s\" resulted in name %s"
				   text (ebdb-string name)))))
	 (unless (string= (ebdb-string mail) "eric@ericabrahamsen.net")
	   (ert-fail (list (format "Parsing \"%s\" resulted in mail %s"
				   text (ebdb-string mail))))))
	(_ (ert-fail (list (format "Parsing \"%s\" resulted in %s"
				   text result))))))))

;; Search testing.

(ert-deftest ebdb-message-search ()
  "Test the `ebdb-message-search' function."
  (ebdb-test-with-records
   (ebdb-test-with-database (db ebdb-test-database-1)
     (let ((rec (make-instance
		 'ebdb-record-person
		 :name (ebdb-parse 'ebdb-field-name-complex "Spongebob Squarepants")
		 :mail (list (ebdb-parse 'ebdb-field-mail "spob@thepants.com")))))
       (ebdb-db-add-record db rec)
       ;; Must init in order to get the record hashed,
       ;; `ebdb-message-search' relies on that.
       (ebdb-init-record rec)
       (should (equal (car (ebdb-message-search "Spongebob Squarepants" nil))
		      rec))
       (should (equal (car (ebdb-message-search nil "spob@thepants.com"))
		      rec))
       (should (null (ebdb-message-search "Spongebob" nil)))
       (should (null (ebdb-message-search nil "thepants.com")))
       (ebdb-delete-record rec)))))

(ert-deftest ebdb-general-search ()
  "Test some of the general search functions."
  (ebdb-test-with-records
    (ebdb-test-with-database (db ebdb-test-database-1)
      (let ((rec (make-instance
		  'ebdb-record-person
		  :name (ebdb-parse 'ebdb-field-name-complex
				    "Spongebob Squarepants")
		  :mail (list (ebdb-parse 'ebdb-field-mail
					  "spob@thepants.com"))
		  :notes (ebdb-parse 'ebdb-field-notes
				     "World's greatest cartoon."))))
	(ebdb-db-add-record db rec)
	(ebdb-init-record rec)
	;; Name is name.
	(should (equal (car
			(ebdb-search
			 (ebdb-records)
			 '((ebdb-field-name "Squarepants"))))
		       rec))
	;; Mail is mail.
	(should (equal (car
			(ebdb-search
			 (ebdb-records)
			 '((ebdb-field-mail "thepants.com"))))
		       rec))
	;; Mail is not notes.
	(should (null (car
			(ebdb-search
			 (ebdb-records)
			 '((ebdb-field-notes "thepants.com"))))))
	;; Notes are notes.
	(should (equal (car
			(ebdb-search
			 (ebdb-records)
			 '((ebdb-field-notes "cartoon"))))
		       rec))
	;; Notes inverted are not notes.
	(should (null (car
			(ebdb-search
			 (ebdb-records)
			 '((ebdb-field-notes "cartoon"))
			 t))))
	;; Not notes inverted are.
	(should (equal (car
			(ebdb-search
			 (ebdb-records)
			 '((ebdb-field-notes "carton"))
			 t))
		       rec))))))

;; Test search folding and transform functions.

(ert-deftest ebdb-search-transform-and-fold ()
  (ebdb-test-with-records
    (let ((recs
	   (list (make-instance
		  'ebdb-record-person
		  :name (ebdb-parse 'ebdb-field-name-complex "Björk Jónsdóttir")))))

      (let ((ebdb-case-fold-search nil)
	    (ebdb-char-fold-search nil)
	    (ebdb-search-transform-functions nil))
	(should-not (ebdb-search
		     recs
		     '((ebdb-field-name "Bjork"))))
	(should-not (ebdb-search
		     recs
		     '((ebdb-field-name "björk"))))
	(should (ebdb-search
		 recs
		 '((ebdb-field-name "Björk")))))

      (let ((ebdb-case-fold-search t)
	    (ebdb-char-fold-search nil)
	    (ebdb-search-transform-functions nil))
	(should-not (ebdb-search
		     recs
		     '((ebdb-field-name "Bjork"))))
	(should (ebdb-search
		 recs
		 '((ebdb-field-name "björk"))))
	(should (ebdb-search
		 recs
		 '((ebdb-field-name "Björk")))))

      (let ((ebdb-case-fold-search nil)
	    (ebdb-char-fold-search t)
	    (ebdb-search-transform-functions nil))
	(should (ebdb-search
		 recs
		 '((ebdb-field-name "Bjork"))))
	(should-not (ebdb-search
		     recs
		     '((ebdb-field-name "björk"))))
	(should (ebdb-search
		 recs
		 '((ebdb-field-name "Björk")))))

      (let ((ebdb-case-fold-search t)
	    (ebdb-char-fold-search t)
	    (ebdb-search-transform-functions nil))
	(should (ebdb-search
		 recs
		 '((ebdb-field-name "Bjork"))))
	(should (ebdb-search
		 recs
		 '((ebdb-field-name "björk"))))
	(should (ebdb-search
		 recs
		 '((ebdb-field-name "Björk"))))

	(let ((ebdb-case-fold-search nil)
	      (ebdb-char-fold-search nil)
	      (ebdb-search-transform-functions
	       (list (lambda (str)
		       (concat str " Jonsdottir")))))
	  (should-not (ebdb-search
		       recs
		       '((ebdb-field-name "Björk")))))

	(let ((ebdb-case-fold-search nil)
	      (ebdb-char-fold-search t)
	      (ebdb-search-transform-functions
	       (list (lambda (str)
		       (concat str " Jonsdottir")))))
	  (should (ebdb-search
		   recs
		   '((ebdb-field-name "Björk")))))))))

;; Vcard testing.

(ert-deftest ebdb-vcard-escape/unescape ()
  "Test the escaping and unescaping routines."
  (should (equal (ebdb-vcard-escape "Nothing.to \"escape\"!")
		 "Nothing.to \"escape\"!"))

  (should (equal (ebdb-vcard-escape "Marry, nuncle")
		 "Marry\\, nuncle"))

  (should (equal (ebdb-vcard-escape "Mine uncle; nay!")
		 "Mine uncle\\; nay!"))

  ;; Don't double-escape
  (should (equal (ebdb-vcard-escape "Marry\\, uncle")
		 "Marry\\, uncle"))

  ;; Don't double-escape, part II
  (should (equal (ebdb-vcard-escape "Marry\\n uncle!")
		 "Marry\\n uncle!"))

  (should (equal (ebdb-vcard-escape "Mine 
uncle")
		 "Mine \\nuncle"))

  (should (equal (ebdb-vcard-unescape "Marry\\, nuncle!")
		 "Marry, nuncle!"))

  (should (equal (ebdb-vcard-unescape "Marry \\nuncle")
		 "Marry 
uncle"))

  (should (equal (ebdb-vcard-unescape
		  (ebdb-vcard-escape
		   "Look, a bog; dogs."))
		 "Look, a bog; dogs.")))

(ert-deftest ebdb-vcard-fold/unfold ()
  "Test line-length folding/unfolding."
  (let ((short-lines "For sale:
Baby shoes,
Never used.")
	(long-lines
	 "Turns out seventy five bytes is a lot of bytes when you just have to keep typing and typing
and typing.")
	(multibyte-lines
	 "然后还要用中文写一行没完没了的话。
其实先要来一个短的，然后一行特别长的，那就是现在这行，
然后可以再有一个短的"))
    (should (equal (ebdb-vcard-fold-lines short-lines)
		   "For sale:
Baby shoes,
Never used."))
    (should (equal (ebdb-vcard-unfold-lines
		    (ebdb-vcard-fold-lines short-lines))
		   short-lines))
    (should
     (equal (ebdb-vcard-fold-lines long-lines)
	    "Turns out seventy five bytes is a lot of bytes when you just have to keep t
 yping and typing
and typing."))
    (should
     (equal (ebdb-vcard-unfold-lines
	     (ebdb-vcard-fold-lines long-lines))
	    long-lines))
    (should
     (equal (ebdb-vcard-fold-lines multibyte-lines)
	    "然后还要用中文写一行没完没了的话。
其实先要来一个短的，然后一行特别长的，那就是现在这
 行，
然后可以再有一个短的"))
    (should
     (equal (ebdb-vcard-unfold-lines
	     (ebdb-vcard-fold-lines multibyte-lines))
	    multibyte-lines))))

(ert-deftest ebdb-vcard-export-dont-explode ()
  "Can we export a record to Vcard without immediate disaster?"
  (ebdb-test-with-records
    (let ((rec (make-instance ebdb-default-record-class
			      :name (ebdb-field-name-complex
				     :surname "Barleycorn"
				     :given-names '("John"))
			      :uuid (ebdb-field-uuid
				     :uuid "asdfasdfadsf")
			      :mail (list (ebdb-field-mail
					   :mail "jb@barleycorn.com"))
			      :phone (list (ebdb-field-phone
					    :object-name "home"
					    :country-code 1
					    :area-code 555
					    :number "5555555"))
			      :notes (ebdb-field-notes
				      :notes "He's in the fields")))
	  (fmt-4
	   (ebdb-formatter-vcard-40
	    :combine nil
	    :collapse nil
	    :include '(ebdb-field-uuid
		       ebdb-field-name
		       ebdb-field-mail
		       ebdb-field-phone
		       ebdb-field-mail)))
	  (fmt-3
	   (ebdb-formatter-vcard-30
	    :combine nil
	    :collapse nil
	    :include '(ebdb-field-uuid
		       ebdb-field-name
		       ebdb-field-mail
		       ebdb-field-phone
		       ebdb-field-mail))))

      (should (ebdb-fmt-record fmt-4 rec))

      (should (ebdb-fmt-record fmt-3 rec)))))

(provide 'ebdb-test)
;;; ebdb-test.el ends here
