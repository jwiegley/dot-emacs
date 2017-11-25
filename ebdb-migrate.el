;;; ebdb-migrate.el --- Migration/upgrade functions for EBDB  -*- lexical-binding: t; -*-

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

;; This file provides functions for upgrading from earlier versions of
;; EBDB, or from BBDB.

;;; Code:

(require 'ebdb)
(autoload 'calendar-absolute-from-gregorian "calendar")
(autoload 'calendar-gregorian-from-absolute "calendar")
(autoload 'org-time-string-to-absolute "org")
(declare-function make-gnorb-ebdb-link "ext:gnorb-ebdb")
(declare-function org-contacts-db "ext:org-contacts")
(defvar url-handler-regexp)
;;; Migrating the EBDB

;; For org-contacts

(defvar org-contacts-email-property)
(defvar org-contacts-alias-property)
(defvar org-contacts-tel-property)
(defvar org-contacts-address-property)
(defvar org-contacts-birthday-property)
(defvar org-contacts-note-property)
(defvar org-contacts-icon-property)
(defvar org-contacts-nickname-property)

;; Unused
(defconst ebdb-migration-features
  '((3 . "* Date format for `creation-date' and `timestamp' has changed,
  from \"dd mmm yy\" (ex: 25 Sep 97) to \"yyyy-mm-dd\" (ex: 1997-09-25).")
    (4 . "* Country field added.")
    (5 . "* More flexible street address.")
    (6 . "* postcodes are stored as plain strings.")
    (7 . "* Xfields is always a list.  Organizations are stored as list.
  New field `affix'."))
  "EBDB Features that have changed in various database revisions.
Format ((VERSION . DIFFERENCES) ... ).")

;; Quiet compiler
(defvar bbdb-file)

;;; These struct functions and definitions are here only to enable
;;; multi-step upgrades from earlier versions of the database.

(defmacro ebdb-defstruct (name &rest elts)
  "Define two functions to operate on vector NAME for each symbol ELT in ELTS.
The function ebdb-NAME-ELT returns the element ELT in vector NAME.
The function ebdb-NAME-set-ELT sets ELT.
Also define a constant ebdb-NAME-length that holds the number of ELTS
in vector NAME."
  (declare (indent 1))
  (let* ((count 0)
         (sname (symbol-name name))
         (uname (upcase sname))
         (cname (concat "ebdb-" sname "-"))
         body)
    (dolist (elt elts)
      (let* ((selt (symbol-name elt))
             (setname  (intern (concat cname "set-" selt))))
        (push (list 'defsubst (intern (concat cname selt)) `(,name)
                    (format "For EBDB %s read element %i `%s'."
                            uname count selt)
                    ;; Use `elt' instead of `aref' so that these functions
                    ;; also work for the `ebdb-record-type' pseudo-code.
                    `(elt ,name ,count)) body)
        (push (list 'defsubst setname `(,name value)
                    (format "For EBDB %s set element %i `%s' to VALUE.  \
Return VALUE.
Do not call this function directly.  Call instead `ebdb-record-set-field'
which ensures the integrity of the database.  Also, this makes your code
more robust with respect to possible future changes of EBDB's innermost
internals."
                            uname count selt)
                    `(aset ,name ,count value)) body))
      (setq count (1+ count)))
    (push (list 'defconst (intern (concat cname "length")) count
                (concat "Length of EBDB `" sname "'.")) body)
    (cons 'progn body)))

;; Define structs so that the getters/setters used elsewhere in the
;; file operate normally.  These functions are used nowhere else in
;; EBDB, and the "v" prefix has been added to prevent function name
;; clashes.
(ebdb-defstruct vrecord
  firstname lastname affix aka organization phone address mail xfields cache)

(ebdb-defstruct vphone
  label area exchange suffix extension)

(ebdb-defstruct vaddress
  label streets city state postcode country)

(defun ebdb-peel-the-onion (lis)
  "Remove outer layers of parens around singleton lists.
This is done until we get a list which is either not a singleton list
or does not contain a list.  This is a utility function used in recovering
slightly munged old EBDB files."
  (while (and (consp lis)
	      (null (cdr lis))
	      (listp (car lis)))
    (setq lis (car lis)))
  lis)

(defconst ebdb-file-format 7
  "Obsolete variable, only used in migration.")

;;;###autoload
(defun ebdb-migrate (records old-format)
  "Migrate the EBDB from the version on disk to the current version
\(in `ebdb-file-format')."
  ;; Some EBDB files were corrupted by random outer layers of
  ;; parentheses surrounding the actual correct data.  We attempt to
  ;; compensate for this.
  (setq records (ebdb-peel-the-onion records))

  ;; Add new field `affix'.
  (if (< old-format 7)
      (let ((temp records) record)
        (while (setq record (car temp))
          (setcar temp (vector (elt record 0) (elt record 1) nil
                               (elt record 2) (elt record 3) (elt record 4)
                               (elt record 5) (elt record 6) (elt record 7)
                               (elt record 8)))
          (setq temp (cdr temp)))))
  (mapc (ebdb-migrate-versions-lambda old-format) records)
  records)

(defconst ebdb-migration-spec
  '((2 (ebdb-vrecord-xfields ebdb-vrecord-set-xfields
        ebdb-migrate-change-dates))
    (3 (ebdb-vrecord-address ebdb-vrecord-set-address
        ebdb-migrate-add-country-field))
    (4 (ebdb-vrecord-address ebdb-vrecord-set-address
        ebdb-migrate-streets-to-list))
    (5 (ebdb-vrecord-address ebdb-vrecord-set-address
        ebdb-migrate-postcodes-to-strings))
    (6 (ebdb-vrecord-xfields ebdb-vrecord-set-xfields
        ebdb-migrate-xfields-to-list)
       (ebdb-vrecord-organization ebdb-vrecord-set-organization
        ebdb-migrate-organization-to-list)))
  "The alist of (version . migration-spec-list).
See `ebdb-migrate-record-lambda' for details.")

(defun ebdb-migrate-record-lambda (changes)
  "Return a function which will migrate a single record.
CHANGES is a `migration-spec-list' containing entries of the form

        (GET SET FUNCTION)

where GET is the function to be used to retrieve the field to be
modified, and SET is the function to be used to set the field to be
modified.  FUNCTION will be applied to the result of GET, and its
results will be saved with SET."
  (byte-compile `(lambda (record)
                  ,@(mapcar (lambda (ch)
                              `(,(cadr ch) record
                                (,(car (cddr ch))
                                 (,(car ch) record))))
                            changes)
                  record)))

(defun ebdb-migrate-versions-lambda (v0)
  "Return the function to migrate from V0 to `ebdb-file-format'."
  (let (spec)
    (while (< v0 ebdb-file-format)
      (setq spec (append spec (cdr (assoc v0 ebdb-migration-spec)))
            v0 (1+ v0)))
    (ebdb-migrate-record-lambda spec)))

(defun ebdb-migrate-postcodes-to-strings (addresses)
  "Make all postcodes plain strings.
This uses the code that used to be in `ebdb-address-postcode'."
  ;; apply the function to all addresses in the list and return a
  ;; modified list of addresses
  (mapcar (lambda (address)
            (let ((postcode (if (stringp (ebdb-vaddress-postcode address))
                                (ebdb-vaddress-postcode address)
                              ;; if not a string, make it a string...
                              (if (consp (ebdb-vaddress-postcode address))
                                  ;; if a cons cell with two strings
                                  (if (and (stringp (car (ebdb-vaddress-postcode address)))
                                           (stringp (car (cdr (ebdb-vaddress-postcode address)))))
                                      ;; if the second string starts with 4 digits
                                      (if (string-match "^[0-9][0-9][0-9][0-9]"
                                                        (car (cdr (ebdb-vaddress-postcode address))))
                                          (concat (car (ebdb-vaddress-postcode address))
                                                  "-"
                                                  (car (cdr (ebdb-vaddress-postcode address))))
                                        ;; if ("abc" "efg")
                                        (concat (car (ebdb-vaddress-postcode address))
                                                " "
                                                (car (cdr (ebdb-vaddress-postcode address)))))
                                    ;; if ("SE" (123 45))
                                    (if (and (stringp (nth 0 (ebdb-vaddress-postcode address)))
                                             (consp (nth 1 (ebdb-vaddress-postcode address)))
                                             (integerp (nth 0 (nth 1 (ebdb-vaddress-postcode address))))
                                             (integerp (nth 1 (nth 1 (ebdb-vaddress-postcode address)))))
                                        (format "%s-%d %d"
                                                (nth 0 (ebdb-vaddress-postcode address))
                                                (nth 0 (nth 1 (ebdb-vaddress-postcode address)))
                                                (nth 1 (nth 1 (ebdb-vaddress-postcode address))))
                                      ;; if a cons cell with two numbers
                                      (if (and (integerp (car (ebdb-vaddress-postcode address)))
                                               (integerp (car (cdr (ebdb-vaddress-postcode address)))))
                                          (format "%05d-%04d" (car (ebdb-vaddress-postcode address))
                                                  (car (cdr (ebdb-vaddress-postcode address))))
                                        ;; else a cons cell with a string an a number (possible error
                                        ;; if a cons cell with a number and a string -- note the
                                        ;; order!)
                                        (format "%s-%d" (car (ebdb-vaddress-postcode address))
                                                (car (cdr (ebdb-vaddress-postcode address)))))))
                                ;; if nil or zero
                                (if (or (zerop (ebdb-vaddress-postcode address))
                                        (null (ebdb-vaddress-postcode address)))
                                    ""
                                  ;; else a number, could be 3 to 5 digits (possible error: assuming
                                  ;; no leading zeroes in postcodes)
                                  (format "%d" (ebdb-vaddress-postcode address)))))))
              (ebdb-vaddress-set-postcode address postcode))
            address)
          addresses))

(defun ebdb-migrate-change-dates (record)
  "Change date formats.
Formats are changed in timestamp and creation-date fields from
\"dd mmm yy\" to \"yyyy-mm-dd\"."
  (unless (stringp record)
    (mapc (lambda (rr)
                 (when (memq (car rr) '(creation-date timestamp))
                   (ebdb-migrate-change-dates-change-field rr)))
               record)
    record))

(defun ebdb-migrate-change-dates-change-field (field)
  "Migrate the date field (the cdr of FIELD) from \"dd mmm yy\" to
\"yyyy-mm-dd\"."
  (let ((date (cdr field))
    parsed)
    ;; Verify and extract - this is fairly hideous
    (and (equal (setq parsed (timezone-parse-date (concat date " 00:00:00")))
        ["0" "0" "0" "0" nil])
     (equal (setq parsed (timezone-parse-date date))
        ["0" "0" "0" "0" nil])
     (cond ((string-match
         "^\\([0-9]\\{4\\}\\)[-/]\\([ 0-9]?[0-9]\\)[-/]\\([ 0-9]?[0-9]\\)" date)
        (setq parsed (vector (string-to-number (match-string 1 date))
                     (string-to-number (match-string 2 date))
                     (string-to-number (match-string 3 date))))
        ;; This should be fairly loud for GNU Emacs users
        (message "EBDB is treating %s field value %s as %s %d %d"
               (car field) (cdr field)
               (upcase-initials
                (downcase (car (rassoc (aref parsed 1)
                           timezone-months-assoc))))
               (aref parsed 2) (aref parsed 0)))
           ((string-match
         "^\\([ 0-9]?[0-9]\\)[-/]\\([ 0-9]?[0-9]\\)[-/]\\([0-9]\\{4\\}\\)" date)
        (setq parsed (vector (string-to-number (match-string 3 date))
                     (string-to-number (match-string 1 date))
                     (string-to-number (match-string 2 date))))
        ;; This should be fairly loud for GNU Emacs users
        (message "EBDB is treating %s field value %s as %s %d %d"
               (car field) (cdr field)
               (upcase-initials
                (downcase (car (rassoc (aref parsed 1)
                           timezone-months-assoc))))
               (aref parsed 2) (aref parsed 0)))
           (t ["0" "0" "0" "0" nil])))

    ;; I like numbers
    (and (stringp (aref parsed 0))
     (aset parsed 0 (string-to-number (aref parsed 0))))
    (and (stringp (aref parsed 1))
     (aset parsed 1 (string-to-number (aref parsed 1))))
    (and (stringp (aref parsed 2))
     (aset parsed 2 (string-to-number (aref parsed 2))))

    ;; Sanity check
    (cond ((and (< 0 (aref parsed 0))
        (< 0 (aref parsed 1)) (>= 12 (aref parsed 1))
        (< 0 (aref parsed 2))
        (>= (timezone-last-day-of-month (aref parsed 1)
                        (aref parsed 0))
            (aref parsed 2)))
       (setcdr field (format "%04d-%02d-%02d" (aref parsed 0)
                 (aref parsed 1) (aref parsed 2)))
       field)
      (t
       (error "EBDB cannot parse %s header value %S for upgrade"
          field date)))))

(defun ebdb-migrate-add-country-field (addrl)
  "Add a country field to each address in the address list."
  (mapcar (lambda (address) (vconcat address [""])) addrl))

(defun ebdb-migrate-streets-to-list (addrl)
  "Convert the streets to a list."
  (mapcar (lambda (address)
            (vector (aref address 0) ; tag
                    (delq nil (delete "" ; nuke empties
                                      (list (aref address 1) ; street1
                                            (aref address 2) ; street2
                                            (aref address 3))));street3
                    (aref address 4) ; city
                    (aref address 5) ; state
                    (aref address 6) ; postcode
                    (aref address 7))) ; country
          addrl))

(defun ebdb-migrate-xfields-to-list (xfields)
  "Migrate XFIELDS to list."
  (if (stringp xfields)
      (list (cons 'notes xfields))
    xfields))

(defun ebdb-migrate-organization-to-list (organization)
  "Migrate ORGANIZATION to list."
  (if (stringp organization)
      (ebdb-split 'organization organization)
    organization))

;;; These defcustoms are now obsolete, but they're here so that,
;;; during the migration/upgrade process, we know which xfields to
;;; handle specially, and turn into specific field types.  In the case
;;; of `bbdb/gnus-split-public-field', this should signal to us that
;;; the record should actually be changed into a
;;; `ebdb-record-mailing-list'.  But that hasn't been implemented yet,
;;; so...

(defcustom bbdb/gnus-split-private-field 'gnus-private
  "This variable is used to determine the xfield to reference to find the
associated group when saving private mail for a mail address known to
the EBDB.  The value of the xfield should be the name of a mail group."
  :group 'ebdb-mua-gnus-splitting
  :type  'symbol)

(defcustom bbdb/gnus-split-public-field 'gnus-public
  "This variable is used to determine the xfield to reference to find the
associated group when saving non-private mail (received from a mailing
list) for a mail address known to the EBDB.  The value of the xfield
should be the name of a mail group, followed by a space, and a regular
expression to match on the envelope sender to verify that this mail came
from the list in question."
  :group 'ebdb-mua-gnus-splitting
  :type  'symbol)

(defcustom bbdb/vm-auto-folder-field 'vm-folder
  "The name of the VM-specific xfield for mail splitting."
  :group 'ebdb-mua-vm
  :type 'symbol)

(defcustom bbdb/gnus-score-field 'gnus-score
  "This variable contains the name of the EBDB field which should be
checked for a score to add to the mail addresses in the same record."
  :group 'ebdb-mua-gnus-scoring
  :type 'symbol)

(defcustom gnorb-ebdb-org-tag-field 'org-tags
  "The name (as a symbol) of the field to use for org tags."
  :group 'gnorb-ebdb
  :type 'symbol)

;;;###autoload
(defun ebdb-migrate-from-bbdb (&optional file)
  "Migrate from BBDB to EBDB.

This upgrade is extreme enough that we can't really use the
existing migration mechanisms.  They are still there, though, in
case someone's going from, say, version 2 to 4 in one jump.

Migrate from FILE, if non-nil.  Otherwise, assume that the
variable `bbdb-file' points to an existing file holding valid
contacts in a previous BBDB format.  If that variable isn't set
use \(locate-user-emacs-file \"bbdb\" \".bbdb\"\), which is how
BBDB sets the default of that option."
  (interactive)
  (require 'url-handlers)
  (require 'ebdb-org)
  (require 'ebdb-gnus)
  (with-current-buffer (find-file-noselect
			(or file
			    (and (bound-and-true-p bbdb-file)
				 bbdb-file)
			    (locate-user-emacs-file "bbdb" ".bbdb")))
    (when (and (/= (point-min) (point-max))
	       (yes-or-no-p "Upgrade from previous version of BBDB? "))
      (let ((v-records (ebdb-migrate-parse-records))
	    (target-db (ebdb-prompt-for-db nil t))
	    (total 0)
	    c-records duds)
	(message "Migrating records from BBDB...")
	(dolist (r v-records)
	  (condition-case-unless-debug err
	      (let ((orgs (ebdb-vrecord-organization r))
		    (c-rec (ebdb-migrate-vector-to-class r))
		    org)
		;; Gives it a uuid
		(ebdb-db-add-record target-db c-rec)
		(when orgs
		  (dolist (o orgs)
		    ;; Make all the orgs into real records.
		    (unless (string= o "") ; There are many of these.
		      (setq org (or (seq-find
				     (lambda (r)
				       (string= o (ebdb-record-name r)))
				     c-records)
				    (let ((time (current-time)))
				      (ebdb-db-add-record
				       target-db
				       (make-instance
					'ebdb-record-organization
					:name (make-instance 'ebdb-field-name-simple :name o)
					:timestamp
					(make-instance 'ebdb-field-timestamp :timestamp time)
					:creation-date
					(make-instance 'ebdb-field-creation-date :timestamp time))))))
		      ;; Create the connection between the org and the
		      ;; person.
		      (ebdb-record-add-org-role c-rec org)
		      (unless (member org c-records)
			(push org c-records)))))
		(push c-rec c-records)
		(message "Migrating records from BBDB... %d" (cl-incf total)))
	    (error
	     (push (list r err) duds))))
	(when duds
	  (pop-to-buffer
	   (get-buffer-create "*EBDB Migration Errors*")
	   '(nil . ((window-height . 10))))
	  (insert "The records below could not be migrated:\n\n")
	  (insert
	   (mapconcat
	    (lambda (r)
	      (format "%S, error: %S" (car r) (cadr r)))
	    duds "\n\n"))
	  (fit-window-to-buffer)
	  (goto-char (point-min)))
	(dolist (r c-records)
	  (ebdb-init-record r))
	(setf (slot-value target-db 'dirty) t)
	(message "Migrating records from BBDB... %d records migrated"
		 (length c-records))))))

(defun ebdb-migrate-vector-to-class (v)
  "Migrate a single vector-style BBDB record V to EBDB style EIEIO object."
  ;; In the vector version, vector elements were:

  ;; record: firstname lastname affix aka organization phone address mail xfields
  ;; phone: label area exchange suffix extension
  ;; address: label streets city state postcode country
  (let ((f-name (aref v 0))
	(l-name (aref v 1))
	(affix (aref v 2))
	(aka (aref v 3))
	(phone (aref v 5))
	(address (aref v 6))
	(mail (aref v 7))
	(xfields (aref v 8))
	name akas phones mails addresses fields ts c-date notes lab val)
    (setq name (make-instance ebdb-default-name-class
			      :surname l-name
			      :given-names (when f-name (split-string f-name " " nil))
			      :affix affix))
    (when aka
      (dolist (a aka)
	(push (make-instance ebdb-default-name-class
			     :surname (car (last (split-string a)))
			     :given-names (butlast (split-string a)))
	      akas)))
    (when phone
      (dolist (p phone)
	(let ((label (aref p 0))
	      area extension number)
	  (if (= 2 (length p))
	      (setq number (aref p 1))
	    (setq area (ebdb-vphone-area p)
		  number (format "%d%d"
				 (ebdb-vphone-exchange p)
				 (ebdb-vphone-suffix p))
		  extension (ebdb-vphone-extension p)))
	  (push (make-instance ebdb-default-phone-class
			       :object-name label
			       :area-code area
			       :number (replace-regexp-in-string "[- ]+"
								 "" number)
			       :extension extension)
		phones))))
    (when address
      (dolist (a address)
	(let ((label (aref a 0))
	      (streets (aref a 1))
	      (city (aref a 2))
	      (state (aref a 3))
	      (postcode (aref a 4))
	      (country (aref a 5))
	      (case-fold-search t))
	  (push (make-instance ebdb-default-address-class
			       :object-name label
			       :streets streets
			       :locality city
			       :region state
			       :postcode postcode
			       :country country)
		addresses))))
    (when mail
      (dolist (m mail)
	(let ((bits (ebdb-decompose-ebdb-address m)))
	  (when (cadr bits)
	    (push (make-instance ebdb-default-mail-class
				 :aka (car bits)
				 :mail (cadr bits))
		  mails))))
      (when mails
	(setf (slot-value (car (last mails)) 'priority) 'primary)))
    (when xfields
      (dolist (x xfields)
	(setq lab (car x)
	      val (cdr x))
	(cond
	 ((eq lab 'timestamp)
	  (setq ts (make-instance 'ebdb-field-timestamp
				  :timestamp
				  (apply #'encode-time
					 (mapcar
					  (lambda (el)
					    (if (null el)
						0
					      el))
					  (parse-time-string val))))))
	 ((eq lab 'creation-date)
	  (setq c-date (make-instance 'ebdb-field-creation-date
				      :timestamp
				      (apply #'encode-time
					     (mapcar
					      (lambda (el)
						(if (null el)
						    0
						  el))
					      (parse-time-string val))))))
	 ((eq lab 'mail-alias)
	  (push (make-instance 'ebdb-field-mail-alias
			       :alias val
			       :address (car-safe mails))
		fields))
	 ((and (stringp v)
	       (string-match-p val url-handler-regexp))
	  (push (make-instance 'ebdb-field-url
			       :url val)
		fields))
	 ((eq lab 'anniversary)
	  (let* ((bits (split-string val " "))
		 (date-bits (split-string (car bits) "-")))
	    (push (make-instance 'ebdb-field-anniversary
				 :date (list
					(string-to-number (nth 1 date-bits))
					(string-to-number (nth 2 date-bits))
					(string-to-number (car date-bits)))
				 :object-name (cadr bits))
		  fields)))
	 ((eq lab 'notes)
	  (setq notes (make-instance 'ebdb-field-notes
				     :notes val)))
	 ((eq lab 'messages)
	  (unless (stringp val)
	    (require 'ebdb-gnorb)
	    (setq val
		  (mapcar
		   (lambda (s)
		     (make-gnorb-ebdb-link
		      :subject (aref s 1)
		      :date (aref s 2)
		      :group (aref s 3)
		      :id (aref s 4)))
		   val))
	    (push (make-instance 'gnorb-ebdb-field-messages
				 :messages val)
		  fields)))
	 ((eq lab gnorb-ebdb-org-tag-field)
	  (push (make-instance 'ebdb-org-field-tags
			       :tags (if (listp val)
					 val
				       (split-string val ";" t " ")))
		fields))
	 ((eq lab bbdb/gnus-score-field)
	  (push (make-instance 'ebdb-gnus-score-field
			       :score val)
		fields))
	 ((memq lab (list 'imap bbdb/gnus-split-private-field
			  bbdb/vm-auto-folder-field))
	  (push (make-instance 'ebdb-field-mail-folder
			       :folder val)
		fields))
	 (t
	  (push (make-instance 'ebdb-field-user-simple
			       :object-name (symbol-name (car x))
			       :value val)
		fields)))))
    (make-instance ebdb-default-record-class
		   :name name
		   :aka akas
		   :phone phones
		   :address addresses
		   :mail mails
		   :timestamp ts
		   :creation-date c-date
		   :notes notes
		   :dirty t
		   :fields fields)))

(defun ebdb-migrate-parse-records ()
  "Parse an earlier (non-EIEIO) version of a BBDB database file."
  (save-excursion
    (save-restriction
      (widen)
      (goto-char (point-min))
      ;; look backwards for file-format, and convert if necessary.
      (let ((file-format
	     (if (re-search-forward
		  "^;+[ \t]*file-\\(format\\|version\\):[ \t]*\\([0-9]+\\)[ \t]*$" nil t)
		 (string-to-number (match-string 2))))
            migrate records)
        (unless file-format ; current file-format, but no file-format: line.
          (error "BBDB corrupted: no file-format line"))
        (if (> file-format ebdb-file-format)
            (error "EBDB version %s understands file format %s but not %s."
                   ebdb-version ebdb-file-format file-format)
          (setq migrate (< file-format ebdb-file-format)))
	(unless (re-search-forward "^\\[" nil t)
	  (error "Unreadabe BBDB file: no contacts found"))
	(goto-char (point-at-bol))
        ;; narrow the buffer to skip over the rubbish before the first record.
        (narrow-to-region (point) (point-max))
        (let ((modp (buffer-modified-p))
              ;; Make sure those parens get cleaned up.
              ;; This code had better stay simple!
              (inhibit-quit t)
              (buffer-undo-list t)
              buffer-read-only)
          (goto-char (point-min)) (insert "(\n")
          (goto-char (point-max)) (insert "\n)")
          (goto-char (point-min))
          (unwind-protect
              (setq records (read (current-buffer)))
            (goto-char (point-min)) (delete-char 2)
            (goto-char (point-max)) (delete-char -2)
            (set-buffer-modified-p modp)))
        (widen)

        ;; Migrate if `bbdb-file' is outdated.
        (if migrate (setq records (ebdb-migrate records file-format)))

	records))))

(defvar ebdb-migrate-org-simple-correspondences
  '((org-contacts-email-property . ebdb-default-mail-class)
    (org-contacts-tel-property . ebdb-default-phone-class)
    (org-contacts-note-property . ebdb-default-notes-class)
    ;; NICKNAME is specifically meant for erc nicks, not normal
    ;; nicknames.
;    (org-contacts-nickname-property . ebdb-field-name-simple)
    (org-contacts-alias-property . ebdb-default-name-class))
  "The simplest property-to-field correspondences.
This variable only holds correspondences for fields that require
no processing beyond calling `ebdb-parse' on the string values.")

;;;###autoload
(defun ebdb-migrate-from-org-contacts ()
  "Migrate contacts from the org-contacts format."
  (interactive)
  (require 'org-contacts)
  (unless ebdb-sources
    (error "First set `ebdb-sources' to the location of your EBDB database."))

  (let ((db (ebdb-prompt-for-db nil t))
	;; Postpone evaluation of the symbols until run time.
	(prop-fields
	 (mapcar
	  (pcase-lambda (`(,prop . ,class))
	    (cons (symbol-value prop)
		  (if (class-p class) class (symbol-value class))))
	  ebdb-migrate-org-simple-correspondences))
	(count 0)
	(dud-fields '())
	record records)

    (message "Migrating records from org-contacts... %d records" count)

    (pcase-dolist (`(,name ,_ ,fields) (org-contacts-db))
      (setq record (make-instance ebdb-default-record-class))
      (ebdb-record-change-name record name)
      (pcase-dolist (`(,field-label . ,value) fields)
	(condition-case nil
	    (let ((f (if (assoc-string field-label prop-fields)
			 (ebdb-parse (cdr (assoc-string field-label prop-fields))
				     value)
		       (pcase field-label
			 ((pred (equal org-contacts-address-property))
			  (signal 'ebdb-unparseable (list value)))
			 ((pred (equal org-contacts-birthday-property))
			  (make-instance 'ebdb-field-anniversary
					 :date  (calendar-gregorian-from-absolute
						 (org-time-string-to-absolute
						  value))
					 :object-name "birthday"))))))
	      (when f
		(ebdb-record-insert-field record f)))
	  (ebdb-unparseable
	   (push (cons field-label value)
		 (alist-get name dud-fields '() nil #'equal)))))
      (push record records)
      (message "Migrating records from org-contacts... %d records"
	       (cl-incf count)))

    (dolist (r records)
      (ebdb-db-add-record db r))

    (message "Migrating records from org-contacts... %d records"
	     (length records))

    (ebdb-display-records records)

    (when dud-fields
      (pop-to-buffer (get-buffer-create "*EBDB Migration Errors*")
		     '(display-buffer-pop-up-window . ((width . 50))))
      (goto-char (point-min))
      (pcase-dolist (`(,name . ,fields) dud-fields)
	(insert (format "* [[ebdb:uuid/%s][%s]]\n"
			(ebdb-record-uuid (car (ebdb-gethash name '(fl-name))))
			name))
	(pcase-dolist (`(,field-label . ,value) fields)
	  (insert (format "%s: %s\n" field-label value)))
	(insert "\n"))
      (goto-char (point-min))
      (org-mode)
      (message "Some field values could not be parsed"))))

(provide 'ebdb-migrate)
;;; ebdb-migrate.el ends here
