;;; ebib-db.el --- Part of Ebib, a BibTeX database manager  -*- lexical-binding: t -*-

;; Copyright (c) 2003-2014 Joost Kremers
;; All rights reserved.

;; Author: Joost Kremers <joostkremers@fastmail.fm>
;; Maintainer: Joost Kremers <joostkremers@fastmail.fm>
;; Created: 2003
;; Version: 2.3
;; Keywords: text bibtex

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;;
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in the
;;    documentation and/or other materials provided with the distribution.
;; 3. The name of the author may not be used to endorse or promote products
;;    derived from this software without specific prior written permission.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
;; IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
;; OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
;; IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
;; INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
;; NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES ; LOSS OF USE,
;; DATA, OR PROFITS ; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
;; THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:

;; This file is part of Ebib, a BibTeX database manager for Emacs. It
;; contains the database code.

;;; Code:

(require 'cl-lib)
(require 'ebib-utils)

;; each database is represented by a struct
(cl-defstruct ebib--db-struct
  (database (make-hash-table :test 'equal)) ; hashtable containing the database itself
  (strings)                                 ; alist with the @STRING definitions
  (preamble)                                ; string with the @PREAMBLE definition
  (comments)                                ; list of @COMMENTS
  (local-vars)                              ; the file's local variable block
  (dialect)                                 ; the dialect of this database
  (cur-entry)                               ; the current entry
  (marked-entries)                          ; list of marked entries
  (filter)                                  ; the active filter
  (sortinfo)                                ; custom sorting
  (filename)                                ; name of the BibTeX file that holds this database
  (modified)                                ; flag indicating whether this database has been modified
  (backup))                                 ; flag indicating whether we need to make a backup of the .bib file

(defun ebib-db-new-database ()
  "Creates a new database instance and returns it."
  (make-ebib--db-struct))

(defun ebib-db-clear-database (db)
  "Remove all information in DB.
The database object itself is retained, only the information in
it is deleted."
  (clrhash (ebib--db-struct-database db))
  (setf (ebib--db-struct-strings db) nil)
  (setf (ebib--db-struct-preamble db) nil)
  (setf (ebib--db-struct-comments db) nil)
  (setf (ebib--db-struct-local-vars db) nil)
  (setf (ebib--db-struct-dialect db) nil)
  (setf (ebib--db-struct-cur-entry db) nil)
  (setf (ebib--db-struct-marked-entries db) nil)
  (setf (ebib--db-struct-filter db) nil)
  (setf (ebib--db-struct-sortinfo db) nil)
  (setf (ebib--db-struct-filename db) nil)
  (setf (ebib--db-struct-modified db) nil)
  (setf (ebib--db-struct-backup db) nil))

(defun ebib-db-get-dialect (db)
  "Return the BibTeX dialect of DB."
  (ebib--db-struct-dialect db))

(defun ebib-db-set-dialect (dialect db)
  "Set the dialect of DB to DIALECT."
  (setf (ebib--db-struct-dialect db) dialect))

(defun ebib-db-get-comments (db)
  "Return a list of @COMMENTS for DB."
  (ebib--db-struct-comments db))

(defun ebib-db-set-comment (comment db)
  "Add COMMENT to the list of comments in DB."
  (setf (ebib--db-struct-comments db) (append (ebib--db-struct-comments db) (list comment))))

(defun ebib-db-set-local-vars (vars db)
  "Store VARS as the local variable block.
No check is performed to see if VARS is really a local variable block."
  (setf (ebib--db-struct-local-vars db) vars))

(defun ebib-db-get-local-vars (db)
  "Return the local variable block."
  (ebib--db-struct-local-vars db))

(defun ebib--db-get-current-entry-key (db)
  "Return the key of the current entry in DB."
  (ebib--db-struct-cur-entry db))

(defun ebib-db-set-current-entry-key (entry db &optional noerror)
  "Set the current entry in DB to ENTRY.
ENTRY is a key in DB. If ENTRY is not in DB, an error is raised
unless NOERROR is non-NIL. In this case, if NOERROR is 'first,
the current entry key is set to the alphabetically first key in
DB. Any other non-NIL value means do not change the current entry
if ENTRY is not in DB.

ENTRY may also be T, in which case the current entry is
unconditionally set to the alphabetically first entry in DB.

Return the new entry key if successful, NIL otherwise."
  (cond
   ((stringp entry)
    (if (ebib-db-get-entry entry db 'noerror)
        (setf (ebib--db-struct-cur-entry db) entry)
      (unless noerror
        (error "No entry key `%s' in the current database" entry))
      (if (eq noerror 'first)
          (setf (ebib--db-struct-cur-entry db) (car (ebib-db-list-keys db 'sort))))))
   ((eq entry t)
    (setf (ebib--db-struct-cur-entry db) (car (ebib-db-list-keys db 'sort))))))

(defun ebib-db-set-entry (key data db &optional if-exists)
  "Add or modify entry KEY in database DB.
DATA is an alist of (FIELD . VALUE) pairs.

IF-EXISTS defines what to do when the key already exists in DB.
If it is 'overwrite, replace the existing entry. If it is 'uniquify,
generate a unique key by appending a letter `b', `c', etc. to it.
If it is 'noerror, a duplicate key is not stored and the function
returns NIL. If it is NIL (or any other value), a duplicate key
triggers an error.

In order to delete an entry, DATA must be NIL and IF-EXISTS must be
'overwrite.

If storing/updating/deleting the entry is successful, return its key."
  (let ((exists (gethash key (ebib--db-struct-database db))))
    (when exists
      (cond
       ;;  if so required, make the entry unique:
       ((eq if-exists 'uniquify)
	(setq key (ebib-db-uniquify-key key db))
	(setq exists nil))
       ;; if the entry is an update, we simply pretend the key does not exist:
       ((eq if-exists 'overwrite)
	(setq exists nil))
       ;; otherwise signal an error, if so requested:
       ((not (eq if-exists 'noerror))
	(error "Ebib: key `%s' exists in database; cannot overwrite" key))))
    (unless exists
      (if data
	  (puthash key data (ebib--db-struct-database db))
	(remhash key (ebib--db-struct-database db)))
      key)))

(defun ebib-db-remove-entry (key db)
  "Remove entry KEY from DB."
  (ebib-db-set-entry key nil db 'overwrite))

(defun ebib-db-get-entry (key db &optional noerror)
  "Return entry KEY in database DB as an alist.
The entry is returned as an alist of (FIELD . VALUE) pairs.
Trigger an error if KEY does not exist, unless NOERROR is T."
  (let ((entry (gethash key (ebib--db-struct-database db))))
    (unless (or entry noerror)
      (error "Ebib: entry `%s' does not exist" key))
    entry))

(defun ebib-db-uniquify-key (key db)
  "Create a unique key in DB from KEY.
The key is made unique by suffixing `b' to it. If that does not
yield a unique key, `c' is suffixed instead, etc. until a unique
key is found. If suffixing `z' does not yield a unique key, `aa'
is suffixed, then `ab' etc."
  (let* ((suffix ?b)
	 (unique-key (concat key (list suffix))))
    (while (gethash unique-key (ebib--db-struct-database db))
      (setq suffix (1+ suffix))
      (setq unique-key (concat key (list suffix)))
      (when (eq suffix ?z)
	(setq key (concat key "a"))
	(setq suffix ?a)))
    unique-key))

(defun ebib-db-list-keys (db &optional sort)
  "Return a list of keys in DB.
If SORT is non-`nil', the list is sorted."
  (let (keys)
    (maphash #'(lambda (key _)
		 (push key keys))
	     (ebib--db-struct-database db))
    (if sort
        (ebib-db-sort-keys-list keys db)
      keys)))

(defun ebib-db-change-key (key new-key db &optional if-exists)
  "Change entry key KEY to NEW-KEY in DB.
ENTRY must be a key itself. IF-EXISTS determines what to do when
NEW-KEY already exists. If it is NIL, an error is triggered. If
it is 'noerror, no error is triggered and nothing is updated. If
it is 'overwrite, the existing entry under NEW-KEY is overwritten.
If it is 'uniquify, a unique key is created.

If there is no entry with KEY in DB, an error is triggered.

Returns the new key upon succes, or NIL if nothing was updated."
  (let* ((data (ebib-db-get-entry key db))
	 (actual-new-key (ebib-db-set-entry new-key data db if-exists)))
    (when actual-new-key
      (ebib-db-remove-entry key db)
      actual-new-key)))

(defun ebib-db-set-field-value (field value key db &optional if-exists nobrace)
  "Set FIELD of entry KEY in database DB to VALUE.

IF-EXISTS determines what to do if the field already exists. If
it is 'overwrite, the existing value is overwritten. If it is
'noerror, the value is not stored and the function returns NIL.
If it is NIL (or any other value), an error is raised.

IF-EXISTS can also be the symbol 'append or a string. In this
case, the new value is appended to the old value, separated by a
space or by the string. Before appending, braces/double quotes
are removed from both values.

If NOBRACE is t, the value is stored without braces. If it is
nil, braces are added if not already present. NOBRACE may also be
the symbol `as-is', in which case the value is stored as is.

A field can be removed from the entry by passing NIL as VALUE and
setting IF-EXISTS to 'overwrite.

Return non-NIL upon success, or NIL if the value could not be stored."
  (if (eq if-exists 'append)
      (setq if-exists " "))
  (let* ((entry (ebib-db-get-entry key db))
	 (elem (assoc-string field entry 'case-fold))
         (old-value (cdr elem)))
    ;; If the field has a value, decide what to do:
    (if old-value
        (cond
         ((eq if-exists 'overwrite)
          (setq old-value nil))
         ((stringp if-exists)
          (setq value (concat (ebib-db-unbrace old-value) if-exists (ebib-db-unbrace value)))
          (setq old-value nil))
         ((not (eq if-exists 'noerror))
          (error "Ebib: field `%s' exists in entry `%s'; cannot overwrite" field key)))
      ;; Otherwise add the new field. We just add the field here, the value
      ;; is added later, so that we can put braces around it if needed.
      ;; This also makes it easier to return `nil' when storing/changing
      ;; the field value wasn't successful. Note that if `elem' is
      ;; non-`nil', we mustn't add the field again. Note also: we use
      ;; `setcdr' to modify the entry in place.
      (unless elem
        (setq elem (car (setcdr (last entry) (list (cons field nil))))))) ; Make sure `elem' points to the newly added field.
    ;; If there is (still) an old value, do nothing.
    (unless old-value
      ;; Otherwise overwrite the existing entry. Note that to delete a
      ;; field, we set its value to `nil', rather than removing it
      ;; altogether from the database. In `ebib--display-fields', such
      ;; fields are ignored, so they're not saved.
      (if (and value nobrace)
          (unless (eq nobrace 'as-is)
            (setq value (ebib-db-unbrace value)))
        (setq value (ebib-db-brace value)))
      (setcdr elem value)
      t))) ; make sure we return non-`nil'.

(defun ebib-db-remove-field-value (field key db)
  "Remove FIELD from entry KEY in DB."
  (ebib-db-set-field-value field nil key db 'overwrite))

(defun ebib-db-get-field-value (field key db &optional noerror unbraced xref)
  "Return the value of FIELD in entry KEY in database DB.
If FIELD or KEY does not exist, trigger an error, unless NOERROR
is non-NIL. In this case, if NOERROR is a string, return NOERROR,
otherwise return `nil'. If UNBRACED is non-NIL, return the value
without braces.

If XREF is non-NIL, the field value may be retrieved from a
cross-referenced entry. If the result in non-NIL, the returned
text has the text property `ebib--xref', which has as value the
key of the entry from which the field value was retrieved.

Similarly, the value can be retrieved from an alias field. (See
the variable `ebib--field-aliases'). In this case, the returned
string has the text property `ebib--alias' with value T."
  (let* ((entry (ebib-db-get-entry key db noerror))
         (value (cdr (assoc-string field entry 'case-fold)))
         (xref-key)
         (alias))
    (when (and (not value) xref)      ; Check if there's a cross-reference.
      (setq xref-key (ebib-db-get-field-value "crossref" key db 'noerror 'unbraced))
      (when xref-key
        (let* ((source-type (ebib-db-get-field-value "=type=" xref-key db 'noerror))
               (xref-field (ebib--db-get-xref-field field (cdr (assoc "=type=" entry)) source-type (ebib-db-get-dialect db))))
          (when xref-field
            (setq value (ebib-db-get-field-value xref-field xref-key db 'noerror))))))
    (when (not value)                   ; Check if there is a field alias
      (setq alias (cdr (assoc-string field ebib--field-aliases 'case-fold)))
      (if alias
          (setq value (cdr (assoc-string alias entry 'case-fold)))))
    (unless (or value noerror)
      (error "Ebib: field `%s' does not exist in entry `%s'" field key))
    (when value
      (setq value (copy-sequence value))
      (when unbraced
        (setq value (ebib-db-unbrace value)))
      (when alias
        (add-text-properties 0 1 '(ebib--alias t) value))
      (when xref
        (add-text-properties 0 1 `(ebib--xref ,xref-key) value)))
    (when (and (not value)
               (stringp noerror))
      (setq value noerror))
    value))

(defun ebib--db-get-xref-field (target-field target-entry source-entry &optional dialect)
  "Return the field from which TARGET-FIELD inherits.
SOURCE-ENTRY is the entry type of the cross-referenced
entry, (the entry providing the value), TARGET-ENTRY the type of
the cross-referencing entry, (the entry containing the field that
should inherit a value). DIALECT is a BibTeX dialect and defaults
to the default value of `ebib-bibtex-dialect'. If it is `BibTeX',
the return value is simply TARGET-FIELD; otherwise the
inheritances are taken from the variable
`ebib-biblatex-inheritances'. If TARGET-FIELD cannot inherit a
value, this function returns `nil'."
  (or dialect (setq dialect ebib-bibtex-dialect))
  (if (eq dialect 'BibTeX)
      target-field
    (let* ((inheritance (cl-third (cl-find-if (lambda (e)
                                                (and (string-match-p (concat "\\b" target-entry "\\b") (cl-first e))
                                                     (string-match-p (concat "\\b" source-entry "\\b") (cl-second e))))
                                              ebib-biblatex-inheritances)))
           (source-field (or (cdr (assoc-string target-field inheritance 'case-fold))
                             (cdr (assoc-string target-field
                                                (cl-third (assoc-string "all" ebib-biblatex-inheritances 'case-fold))
                                                'case-fold)))))
      (unless (eq source-field 'none)
        (or source-field target-field)))))

(defun ebib-db-set-string (abbr value db &optional if-exists)
  "Set the @string definition ABBR in database DB to VALUE.
If ABBR does not exist, create it. VALUE is enclosed in braces if
it isn't already.

IF-EXISTS determines what to do when ABBR already exists. If it
is 'overwrite, the new string replaces the existing one. If it is
'noerror, the string is not stored and the function returns NIL.
If it is NIL (or any other value), an error is raised.

In order to remove a @STRING definition, pass NIL as VALUE and
set IF-EXISTS to 'overwrite."
  (let* ((old-string (ebib-db-get-string abbr db 'noerror))
	 (strings-list (delete (cons abbr old-string) (ebib--db-struct-strings db))))
    (when old-string
      (cond
       ((eq if-exists 'overwrite)
	(setq old-string nil))
       ((not (eq if-exists 'noerror))
	(error "Ebib: @STRING abbreviation `%s' exists in database %s" abbr (ebib-db-get-filename db 'short)))))
    (unless old-string
      (setf (ebib--db-struct-strings db)
	    (if (null value)
                strings-list
              ;; put the new string at the end of the list, to keep them in
              ;; the order in which they appear in the .bib file. this is
              ;; preferable for version control.
              (append strings-list (list (cons abbr (ebib-db-brace value)))))))))

(defun ebib-db-remove-string (abbr db)
  "Remove @STRING definition from DB."
  (ebib-db-set-string abbr nil db 'overwrite))

(defun ebib-db-get-string (abbr db &optional noerror unbraced)
  "Return the value of @STRING definition ABBR in database DB.
If ABBR does not exist, trigger an error, unless NOERROR is
non-NIL, in which case return NIL. If UNBRACED is non-NIL, return
the value without braces."
  ;; I assume abbreviations should be case-sensitive, so I use assoc
  ;; instead of assoc-string here.
  (let ((value (cdr (assoc abbr (ebib--db-struct-strings db)))))
    (unless (or value noerror)
      (error "Ebib: @STRING abbreviation `%s' does not exist" abbr))
    (if unbraced
        (ebib-db-unbrace value)
      value)))

(defun ebib-db-get-all-strings (db)
  "Return the alist containing all @STRING definitions."
  (ebib--db-struct-strings db))

(defun ebib-db-list-strings (db &optional sort)
  "Return a list of @STRING abbreviations (without expansions).
If SORT is non-nil, the list is sorted."
  (let ((list (mapcar #'car (ebib--db-struct-strings db))))
    (if sort
        (sort list 'string<)
      list)))

(defun ebib-db-set-preamble (preamble db &optional if-exists)
  "Set the preamble of DB to PREAMBLE.

IF-EXISTS determines what to do if there already is a preamble:
if its value is 'append, PREAMBLE is appended to the existing
text (with a newline and hash in between); if it is 'overwrite,
PREAMBLE replaces the existing text. If it is 'noerror, PREAMBLE
is not stored and the function returns NIL. If it is NIL (or any
other value), an error is raised.

In order to delete the preamble, PREAMBLE should be NIL and
IF-EXISTS should be 'overwrite.

Return non-NIL on success or NIL if PREAMBLE could not be stored."
  (let ((existing-preamble (ebib-db-get-preamble db)))
    (when existing-preamble
      (cond
       ((eq if-exists 'append)
	(setq preamble (concat existing-preamble "\n# " preamble))
	(setq existing-preamble nil))
       ((eq if-exists 'overwrite)
	(setq existing-preamble nil))))
    (if (not existing-preamble)
	(setf (ebib--db-struct-preamble db) preamble)
      (unless (eq if-exists 'noerror)
	(error "Ebib: Preamble is not empty; cannot overwrite")))))

(defun ebib-db-remove-preamble (db)
  "Remove the @PREAMBLE definition from DB."
  (ebib-db-set-preamble nil db 'overwrite))

(defun ebib-db-get-preamble (db)
  "Return the preamble of DB.
If DB has no preamble, return NIL."
  (ebib--db-struct-preamble db))

(defun ebib-db-set-modified (mod db)
  "Set the modification flag of DB to MOD."
  (setf (ebib--db-struct-modified db) mod))

(defun ebib-db-modified-p (db)
  "Return T if DB has been modified, NIL otherwise."
  (ebib--db-struct-modified db))

(defun ebib-db-set-filename (filename db &optional if-exists)
  "Set filename of DB to FILENAME.
IF-EXISTS determines what to do when the database already has a
filename. If it is 'overwrite, the filename is changed. If 'noerror,
the filename is not changed an NIL is returned. If IF-EXISTS is
NIL, an existing filename triggers an error."
  (let ((exists (ebib--db-struct-filename db)))
    (when exists
      (cond
       ((eq if-exists 'overwrite)
	(setq exists nil))
       ((not (eq if-exists 'noerror))
	(error "Ebib: database has a filename; cannot overwrite"))))
    (unless exists
      (setf (ebib--db-struct-filename db) filename))))

(defun ebib-db-get-filename (db &optional shortened)
  "Return the filename of DB.
If SHORTED is non-NIL, return only the filename part, otherwise
return the full path."
  (if shortened
      (file-name-nondirectory (ebib--db-struct-filename db))
    (ebib--db-struct-filename db)))

(defun ebib-db-marked-entries-p (db)
  "Return T if there are marked enries in DB."
  (ebib--db-struct-marked-entries db))

(defun ebib-db-marked-p (entry db)
  "Return T if ENTRY is marked in DB.
ENTRY is an entry key."
  (member entry (ebib--db-struct-marked-entries db)))

(defun ebib-db-mark-entry (entry db)
  "Add ENTRY to the list of marked entries in DB.
ENTRY is an entry key. ENTRY is added unconditionally, no check
is performed to see if it is already on the list.

ENTRY can also be 'all, in which case all entries are marked."
  (cond
   ((stringp entry)
    (setf (ebib--db-struct-marked-entries db) (cons entry (ebib--db-struct-marked-entries db))))
   ('all
    (setf (ebib--db-struct-marked-entries db) (ebib-db-list-keys db)))))

(defun ebib-db-unmark-entry (entry db)
  "Remove ENTRY from the list of marked entries in DB.
ENTRY is an entry key. If ENTRY is 'all, all entries are
unmarked."
  (cond
   ((stringp entry)
    (setf (ebib--db-struct-marked-entries db) (remove entry (ebib--db-struct-marked-entries db))))
   ('all
    (setf (ebib--db-struct-marked-entries db) nil))))

(defun ebib-db-toggle-mark (entry db)
  "Toggle the mark on ENTRY in DB."
  (if (ebib-db-marked-p entry db)
      (ebib-db-unmark-entry entry db)
    (ebib-db-mark-entry entry db)))

(defun ebib-db-list-marked-entries (db &optional sort)
  "Return a list of entry keys of all marked entries in DB.
If SORT is non-`nil', the list is sorted."
  (let ((entries (copy-sequence (ebib--db-struct-marked-entries db))))
    (if sort
        (ebib-db-sort-keys-list entries db)
      entries)))

(defun ebib-db-filtered-p (db)
  "Return T if a filter exists for DB."
  (ebib--db-struct-filter db))

(defun ebib-db-set-filter (filter db)
  "Set the filter of DB to FILTER.
The filter is set unconditionally, overwriting any existing filter."
  (setf (ebib--db-struct-filter db) filter))

(defun ebib-db-get-filter (db)
  "Return the filter of DB."
  (ebib--db-struct-filter db))

(defun ebib-db-set-sortinfo (sortinfo db)
  "Set the SORTINFO of DB.
The sortinfo is set unconditionally, overwriting
any existing sortinfo."
  (setf (ebib--db-struct-sortinfo db) sortinfo))

(defun ebib-db-custom-sorted-p (db)
  "Return t if DB has a custom sort."
  (ebib--db-struct-sortinfo db))

(defun ebib-db-get-sort-field (db)
  "Return the sort field of DB, or nil if there is none."
  (car (ebib--db-struct-sortinfo db)))

(defun ebib-db-get-sort-order (db)
  "Return the sort order of DB, or nil if there is none."
  (cdr (ebib--db-struct-sortinfo db)))

(defun ebib-db-sort-keys-list (keys db)
  "Sort KEYS according to the sort info of DB."
  ;; first sort the keys themselves
  (setq keys (sort keys #'string<))
  ;; and then stably sort on the sort field, if any
  (when (ebib-db-custom-sorted-p db)
    (let* ((field (ebib-db-get-sort-field db))
           ;; We use a temp list for sorting, so that the :key argument to
           ;; `cl-stable-sort' can simply be `car' rather than (a much
           ;; heavier) `ebib-db-get-field-value'. Sorting is much faster
           ;; that way.
           (list (mapcar (lambda (key)
                           (cons (ebib-db-get-field-value field key db "" 'unbraced 'xref) key))
                         keys)))
      (setq list (cl-stable-sort list #'string-lessp :key #'car))
      (setq keys (mapcar #'cdr list)))
    ;; reverse the list if necessary
    (if (eq (ebib-db-get-sort-order db) 'descend)
        (setq keys (nreverse keys))))
  ;; now return the list of keys
  keys)

(defun ebib-db-set-backup (backup db)
  "Set the backup flag of DB to BACKUP.
BACKUP must be either T (make backup at next save) or NIL (do not
make backup at next save)."
  (setf (ebib--db-struct-backup db) backup))

(defun ebib-db-backup-p (db)
  "Return backup flag of DB."
  (ebib--db-struct-backup db))

;; EBIB-DB-UNBRACED-P determines if STRING is enclosed in braces. Note that
;; we cannot do this by simply checking whether STRING begins with { and
;; ends with } (or begins and ends with "), because something like "{abc} #
;; D # {efg}" would then be incorrectly recognised as braced. So we need to
;; do the following: take out everything that is between braces or quotes,
;; and see if anything is left. If there is, the original string was
;; braced, otherwise it was not.

;; So we first check whether the string begins with { or ". if not, we
;; certainly have an unbraced string. (EBIB-DB-UNBRACED-P recognises this
;; through the default clause of the COND.) If the first character is { or
;; ", we first take out every occurrence of backslash-escaped { and } or ",
;; so that the rest of the function does not get confused over them.

;; Then, if the first character is {, EBIB--REMOVE-FROM-STRING takes out
;; every occurrence of the regex "{[^{]*?}", which translates to "the
;; smallest string that starts with { and ends with }, and does not contain
;; another {. IOW, it takes out the innermost braces and their contents.
;; Because braces may be embedded, we have to repeat this step until no
;; more balanced braces are found in the string. (Note that it would be
;; unwise to check for just the occurrence of { or }, because that would
;; throw EBIB-DB-UNBRACED-P in an infinite loop if a string contains an
;; unbalanced brace.)

;; For strings beginning with " we do the same, except that it is not
;; necessary to repeat this in a WHILE loop, for the simple reason that
;; strings surrounded with double quotes cannot be embedded; i.e.,
;; "ab"cd"ef" is not a valid (BibTeX) string, while {ab{cd}ef} is.

;; Note: because these strings are to be fed to BibTeX and ultimately
;; (La)TeX, it might seem that we don't need to worry about strings
;; containing unbalanced braces, because (La)TeX would choke on them. But
;; the user may inadvertently enter such a string, and we therefore need to
;; be able to handle it. (Alternatively, we could perform a check on
;; strings and warn the user.)

(defun ebib-db-unbraced-p (string)
  "Non-NIL if STRING is not enclosed in braces or quotes."
  (when (stringp string)
    (cond
     ((eq (string-to-char string) ?\{)
      ;; first, remove all escaped { and } from the string:
      (setq string (ebib--remove-from-string (ebib--remove-from-string string "[\\][{]")
                                             "[\\][}]"))
      ;; then remove the innermost braces with their contents and continue until
      ;; no more braces are left.
      (while (and (member ?\{ (string-to-list string)) (member ?\} (string-to-list string)))
	(setq string (ebib--remove-from-string string "{[^{]*?}")))
      ;; if STRING is not empty, the original string contains material not in braces
      (> (length string) 0))
     ((eq (string-to-char string) ?\")
      ;; remove escaped ", then remove any occurrences of balanced quotes with
      ;; their contents and check for the length of the remaining string.
      (> (length (ebib--remove-from-string (ebib--remove-from-string string "[\\][\"]")
                                           "\"[^\"]*?\""))
	 0))
     (t t))))

(defun ebib-db-unbrace (string)
  "Convert STRING to its unbraced counterpart.
If STRING is already unbraced, do nothing."
  (if (and (stringp string)
           (not (ebib-db-unbraced-p string)))
      (substring string 1 -1)
    string))

(defun ebib-db-brace (string)
  "Put braces around STRING.
If STRING is already braced, do nothing."
  (if (ebib-db-unbraced-p string)
      (concat "{" string "}")
    string))

(provide 'ebib-db)

;;; ebib-db.el ends here
