;;; ebib-keywords.el --- Part of Ebib, a BibTeX database manager  -*- lexical-binding: t -*-

;; Copyright (c) 2003-2014 Joost Kremers
;; All rights reserved.

;; Author: Joost Kremers <joostkremers@fastmail.fm>
;; Maintainer: Joost Kremers <joostkremers@fastmail.fm>
;; Created: 2014
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
;; contains the keywords code.

;;; Code:

(require 'cl-lib)
(require 'dash)
(require 'ebib-utils)
(require 'ebib-db)

(defgroup ebib-keywords nil "Keyword settings for Ebib" :group 'ebib)

(defcustom ebib-keywords-separator ", "
  "String for separating keywords in the `keyword' field.
This separator is also used to separate multiple identical
fields, since those are most likely keyword fields."
  :group 'ebib
  :type '(string :tag "Keyword separator:"))

(defcustom ebib-keywords-list nil
  "General list of keywords."
  :group 'ebib-keywords
  :type '(repeat (string :tag "Keyword")))

(defcustom ebib-keywords-file nil
  "Single or generic file name for storing keywords.
Keywords can be stored in a single keywords file, which is used
for all BibTeX files, or in per-directory keywords files located in
the same directories as the BibTeX files.  In the latter case, the
keywords file should specify just the generic name and no path."
  :group 'ebib-keywords
  :type '(choice (const :tag "Do not use keywords file" nil)
                 (file :tag "Use single keywords file")
                 (string :value "ebib-keywords.txt" :tag "Use per-directory keywords file")))

(defcustom ebib-keywords-file-save-on-exit 'ask
  "Action to take when new keywords are added during a session.
This option only makes sense if `ebib-keywords-file' is set."
  :group 'ebib-keywords
  :type '(choice (const :tag "Always save on exit" always)
                 (const :tag "Do not save on exit" nil)
                 (const :tag "Ask whether to save" ask)))

(defcustom ebib-keywords-use-only-file nil
  "Whether or not to use only keywords from the keywords file.
If both `ebib-keywords-list' and `ebib-keywords-file' are set,
should the file take precedence or should both sets of keywords
be combined?

For BibTeX files that do not have an associated keywords file,
`ebib-keyword-list' is always used, regardless of this setting."
  :group 'ebib-keywords
  :type '(choice (const :tag "Use only keywords file" t)
                 (const :tag "Use keywords file and list" nil)))

(defcustom ebib-keywords-field-keep-sorted nil
  "Keep the keywords field sorted in alphabetical order.
Also automatically remove duplicates."
  :group 'ebib-keywords
  :type '(choice (const :tag "Sort keywords field" t)
                 (const :tag "Do not sort keywords field" nil)))

;; `ebib--keywords-files-alist' lists directories with keywords
;; files plus the keywords in them. If there is a single keywords
;; file, then there is only one entry. Entries have three
;; elements: the dir (or full filename in case of a single
;; keywords file), a list of saved keywords, and a list of new
;; keywords added during the current session.
(defvar ebib--keywords-files-alist nil "Alist of keywords files.")

;; `ebib--keywords-list-per-session' is composed of the keywords
;; in `ebib--keywords-list' and whatever new keywords are added by
;; the user during the current session. These new additions are
;; discarded when ebib is closed.
(defvar ebib--keywords-list-per-session nil "List of keywords for the current session.")

(defun ebib--keywords-load-keywords (db)
  "Check if there is a keywords file for DB and make sure it is loaded."
  (unless (or (not ebib-keywords-file)
              (file-name-directory ebib-keywords-file))
    (let ((dir (expand-file-name (file-name-directory (ebib-db-get-filename db)))))
      (if dir
          (let ((keyword-list (ebib--read-file-to-list (concat dir ebib-keywords-file))))
            ;; note: even if keyword-list is empty, we store it, because the user
            ;; may subsequently add keywords.
            (add-to-list 'ebib--keywords-files-alist    ; add the dir if not in the list yet
                         (list dir keyword-list nil)   ; the extra empty list is for new keywords
                         t (lambda (x y) (equal (car x) (car y)))))))))

(defun ebib--keywords-add-keyword (keyword db)
  "Add KEYWORD to the list of keywords for DB."
  (if (not ebib-keywords-file)        ; only the general list exists
      (add-to-list 'ebib--keywords-list-per-session keyword t)
    (let ((dir (or (file-name-directory ebib-keywords-file)      ; a single keywords file
                   (file-name-directory (ebib-db-get-filename db)))))    ; per-directory keywords files
      (push keyword (cl-third (assoc dir ebib--keywords-files-alist))))))

(defun ebib--keywords-to-list (str)
  "Convert STR to a list of keywords.
STR should be a string containing keywords separated by
`ebib-keywords-separator'."
  ;; TODO I use `replace-regexp-in-string' to trim the individual strings.
  ;; In Emacs 24.4, `split-string' has an additional argument that does
  ;; this, but that's not available in 24.3. An alternative would be
  ;; `s-trim' from the `s' library.
  (--map (replace-regexp-in-string "\\`[[:space:]]*\\(.*?\\)[[:space:]]*\\'" "\\1" it t)
         (split-string str (regexp-quote ebib-keywords-separator) t)))

(defun ebib--keywords-sort (keywords)
  "Sort the KEYWORDS string, remove duplicates, and return it as a string.
Note: KEYWORDS should be unbraced."
  (mapconcat 'identity
             (sort (delete-dups (ebib--keywords-to-list keywords))
                   'string<)
             ebib-keywords-separator))

(defun ebib--keywords-remove-existing (keywords db)
  "Remove keywords from KEYWORDS that already exist in DB.
KEYWORDS is a list of keywords.  The return value is a list of
keywords that do not exist in DB."
  (let ((all-keywords (ebib--keywords-for-database db)))
    (--remove (member-ignore-case it all-keywords) keywords)))

(defun ebib--keywords-for-database (db)
  "Return the list of keywords for database DB.
When the keywords come from a file, add the keywords in
`ebib-keywords-list', unless `ebib--keywords-use-only-file' is set."
  (if (not ebib-keywords-file)        ; only the general list exists
      ebib--keywords-list-per-session
    (let* ((dir (or (file-name-directory ebib-keywords-file)     ; a single keywords file
                    (file-name-directory (ebib-db-get-filename db))))    ; per-directory keywords files
           (lst (assoc dir ebib--keywords-files-alist)))
      (append (cl-second lst) (cl-third lst)))))

(defun ebib--keywords-get-file (db)
  "Return the name of the keywords file for DB."
  (if (and ebib-keywords-file ; TODO not sure if this function'll work correctly if ebib--keywords-file is NIL.
           (file-name-directory ebib-keywords-file))
      ebib-keywords-file
    (concat (file-name-directory (ebib-db-get-filename db)) ebib-keywords-file)))

(defun ebib--keywords-save-to-file (keyword-file-descr)
  "Save all keywords in KEYWORD-FILE-DESCR to the associated file.
KEYWORD-FILE-DESCR is an element of `ebib--keywords-files-alist',
that is, it consists of a list of three elements, the first is
the directory of the keywords file, the second the existing
keywords and the third the keywords added in this session."
  (let ((file (if (file-name-directory ebib-keywords-file)
                  ebib-keywords-file
                (concat (car keyword-file-descr) ebib-keywords-file))))
    (if (file-writable-p file)
        (with-temp-buffer
          (mapc (lambda (keyword)
                  (insert (format "%s\n" keyword)))
                (append (cl-second keyword-file-descr) (cl-third keyword-file-descr)))
          (write-region (point-min) (point-max) file))
      (ebib--log 'warning "Could not write to keyword file `%s'" file))))

(defun ebib--keywords-save-new-keywords (db)
  "Check if new keywords were added to DB and save them as required."
  (let ((lst (ebib--keywords-new-p db)))
    (when (and (cl-third lst)           ; if there are new keywords
               (or (eq ebib-keywords-file-save-on-exit 'always)
                   (and (eq ebib-keywords-file-save-on-exit 'ask)
                        (y-or-n-p "New keywords have been added. Save? "))))
      (ebib--keywords-save-to-file lst)
      ;; now move the new keywords to the list of existing keywords
      (setf (cl-second lst) (append (cl-second lst) (cl-third lst)))
      (setf (cl-third lst) nil))))

(defun ebib-keywords-save-cur-db ()
  "Save new keywords for the current database."
  (interactive)
  (ebib--keywords-save-new-keywords ebib--cur-db))

(defun ebib--keywords-new-p (&optional db)
  "Check whether there are new keywords.
Returns NIL if there are no new keywords, or a list containing
all the elements in `ebib--keywords-files-alist' that contain new
keywords.

Optional argument DB specifies the database to check for."
  (if db
      (let* ((dir (or (and ebib-keywords-file
                           (file-name-directory ebib-keywords-file)) ; a single keywords file
                      (file-name-directory (ebib-db-get-filename db)))) ; per-directory keywords files
             (lst (assoc dir ebib--keywords-files-alist)))
        (if (cl-third lst)
            lst))
    (cl-remove-if-not #'cl-third ebib--keywords-files-alist)))

(defun ebib-keywords-save-all-new ()
  "Check if new keywords were added during the session and save them as required."
  (interactive)
  (let ((new (ebib--keywords-new-p)))
    (when (and new
               (or (eq ebib-keywords-file-save-on-exit 'always)
                   (called-interactively-p 'any)
                   (and (eq ebib-keywords-file-save-on-exit 'ask)
                        (y-or-n-p (format "New keywords were added. Save '%s'? "
                                          (file-name-nondirectory ebib-keywords-file)))))) ; strip path for succinctness
      (mapc (lambda (elt)
              (ebib--keywords-save-to-file elt))
            new))))

(provide 'ebib-keywords)

;;; ebib-keywords.el ends here
