;;; ebib.el --- a BibTeX database manager  -*- lexical-binding: t -*-

;; Copyright (c) 2003-2014 Joost Kremers
;; All rights reserved.

;; Author: Joost Kremers <joostkremers@fastmail.fm>
;; Maintainer: Joost Kremers <joostkremers@fastmail.fm>
;; Created: 2003
;; Version: 2.3
;; Keywords: text bibtex
;; Package-Requires: ((dash "2.5.0") (parsebib "1.0") (emacs "24.3"))

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

;; Ebib is a BibTeX database manager that runs in GNU Emacs. With Ebib, you
;; can create and manage .bib-files, all within Emacs. It supports @string
;; and @preamble definitions, multi-line field values, searching, and
;; integration with Emacs' (La)TeX mode.

;; See the Ebib manual for usage and installation instructions.

;; The latest release version of Ebib, contact information and mailing list
;; can be found at <http://joostkremers.github.io/ebib>. Development
;; sources can be found at <https://github.com/joostkremers/ebib>.

;;; Code:

(require 'cl-lib)
(require 'easymenu)
(require 'bibtex)
(require 'dash)
(require 'pp)
(require 'parsebib)
(require 'ebib-utils)
(require 'ebib-db)
(require 'ebib-filters)
(require 'ebib-keywords)

(defun ebib--display-buffer-reuse-window (buffer _)
  "Display BUFFER in an existing Ebib window.
If BUFFER is the index buffer, simply switch to the window
displaying it.  (This function should not be called if there is a
chance the index buffer is not visible.) For any other buffer,
find a window displaying an Ebib buffer other than the index
buffer, switch to that window and display BUFFER.  If no window
can be found, return NIL."
  (let (window)
    (cond
     ;; the index buffer can only be displayed in its dedicated window.
     ((eq buffer (ebib--buffer 'index))
      (setq window (get-buffer-window buffer)))
     ;; if ebib-layout isn't full, the multiline buffer should not be
     ;; displayed in an Ebib buffer.
     ((and (memq buffer ebib--multiline-buffer-list)
           (not (eq ebib-layout 'full)))
      (setq window nil))
     ;; find a buffer other than the index buffer that's being displayed
     (t (setq window (let ((b (cdr (--find (and (not (eq (car it) 'index))
                                                (get-buffer-window (cdr it)))
                                           ebib--buffer-alist))))
                       (if b (get-buffer-window b))))))
    (when window
      (select-window window)
      (with-ebib-window-nondedicated
        (switch-to-buffer buffer t))
      window)))

(defun ebib--display-buffer-largest-window (buffer _)
  "Display BUFFER in the largest non-dedicated window."
  (unless ebib-popup-entry-window
    (let ((window (get-largest-window)))
      (select-window window)
      (switch-to-buffer buffer)
      window)))

(defun ebib--pop-to-buffer (buffer)
  "Select or create a window to display BUFFER and display it.
If the index buffer isn't visible, this function does nothing.
Otherwise, if BUFFER is the index buffer, simply switch to its
window.  For any other buffer, if there is a visible Ebib buffer
other than the index buffer, switch to its window and display
BUFFER.  If there is no Ebib window, use the largest non-dedicated
window or, if `ebib-layout' is set to `index-only', pop up a new
window.  If all else fails, pop up a new frame."
  ;; if the index buffer isn't visible, do nothing.
  (unless (not (get-buffer-window (ebib--buffer 'index)))
    (pop-to-buffer buffer
                   '((ebib--display-buffer-reuse-window
                      ebib--display-buffer-largest-window
                      display-buffer-pop-up-window
                      display-buffer-pop-up-frame))
                   t)))

(defun ebib--display-entry-key (entry-key)
  "Display ENTRY-KEY in the index buffer at POINT."
  (with-current-ebib-buffer 'index
    ;; if the database has a custom sorting, add the sort field to
    ;; ebib-index-display-fields if it's not there yet
    (let* ((sortfield (when (ebib-db-custom-sorted-p ebib--cur-db)
                        (ebib-db-get-sort-field ebib--cur-db)))
           (ebib-index-display-fields (if (and sortfield
                                               (not (member-ignore-case sortfield ebib-index-display-fields)))
                                          (cons sortfield ebib-index-display-fields)
                                        ebib-index-display-fields)))
      (with-ebib-buffer-writable
        (insert (format "%-40s %s\n"
                        entry-key
                        (if ebib-index-display-fields
                            (mapconcat (lambda (field)
                                         (ebib--first-line (ebib-db-get-field-value field entry-key ebib--cur-db "" 'unbraced 'xref)))
                                       ebib-index-display-fields
                                       "  ") ; separator for mapconcat
                          "")))))))

(defun ebib--redisplay-current-field ()
  "Redisplay the contents of the current field in the entry buffer."
  (with-current-ebib-buffer 'entry
    ;; If the `crossref' field has changed, we need to redisplay the entire entry.
    (let ((field (ebib--current-field)))
      (if (cl-equalp field "crossref")
          (progn
            (ebib--fill-entry-buffer)
            (re-search-forward "^crossref")
            (ebib--set-fields-overlay))
        (with-ebib-buffer-writable
          (goto-char (overlay-start ebib--fields-overlay))
          (let ((beg (point)))
            (end-of-line)
            (delete-region beg (point)))
          (insert (propertize (format "%-17s " field) 'face 'ebib-field-face)
                  (ebib--get-field-highlighted field (ebib--cur-entry-key)))
          (ebib--set-fields-overlay))))))

(defun ebib--redisplay-current-string ()
  "Redisplay the current string definition in the strings buffer."
  (with-current-ebib-buffer 'strings
    (with-ebib-buffer-writable
      (let* ((string (ebib--current-string))
             (val (ebib-db-get-string string ebib--cur-db nil 'unbraced)))
        (goto-char (overlay-start ebib--strings-overlay))
        (let ((beg (point)))
          (end-of-line)
          (delete-region beg (point)))
        (insert (format "%-18s %s" string
                        (if (ebib--multiline-p val)
                            (concat "+" (ebib--first-line val))
                          (concat " " val))))
        (ebib--set-strings-overlay)))))

(defun ebib--get-field-highlighted (field key &optional db match-str)
  "Return the contents of FIELD in entry KEY in DB with MATCH-STR highlighted."
  ;; Note: we need to work on a copy of the value, otherwise the highlights
  ;; are made to the value as stored in the database. Hence copy-sequence.
  (or db (setq db ebib--cur-db))
  (let* ((case-fold-search t)
         (value (ebib-db-get-field-value field key db 'noerror nil 'xref))
         (raw " ")
         (multiline " ")
         (matched nil)
         (alias ""))
    ;; we have to do a couple of things now:
    ;; - remove {} or "" around the value, if they're there
    ;; - search for match-str
    ;; - properly adjust the value if it's multiline
    ;; but all this is not necessary if there was no value
    (when value
      (if (get-text-property 0 'ebib--alias value)
          (setq alias (propertize (format "  [<== %s]" (cdr (assoc-string field ebib--field-aliases 'case-fold))) 'face 'ebib-alias-face)))
      (if (stringp (get-text-property 0 'ebib--xref value))
          (setq value (propertize value 'face 'ebib-crossref-face 'fontified t)))
      (if (and (cl-equalp field "crossref")
               (not (member (ebib-db-unbrace value) ebib--cur-keys-list)))
          (setq value (propertize value 'face 'error)))
      (if (cl-equalp field "keywords")
          (let* ((unbraced (ebib-db-unbraced-p value))
                 (keywords (ebib--keywords-to-list (ebib-db-unbrace value)))
                 (new-keywords (ebib--keywords-remove-existing keywords ebib--cur-db))
                 (new-value (mapconcat (lambda (keyword)
                                         (if (member-ignore-case keyword new-keywords)
                                             (propertize keyword 'face 'ebib-nonpermanent-keyword-face)
                                           keyword))
                                       keywords
                                       ebib-keywords-separator)))
            (setq value (if unbraced
                            new-value
                          (ebib-db-brace new-value)))))
      (if (ebib-db-unbraced-p value)
          (setq raw "*")
        (setq value (ebib-db-unbrace value))) ; we have to make the value look nice
      (when match-str
        (cl-multiple-value-setq (value matched) (ebib--match-all-in-string match-str value)))
      (when (ebib--multiline-p value)
        (setq multiline (propertize "+" 'face nil)) ; sometimes the face property persists
        (setq value (ebib--first-line value)))
      (when (and matched
                 (string= multiline "+"))
        (add-text-properties 0 1 '(face highlight) multiline)))
    (concat raw multiline value alias)))

(defun ebib--display-fields (key &optional db match-str)
  "Display the fields of entry KEY in DB.
The fields are inserted in the current buffer with their values.
If MATCH-STR is provided, then when it is present in the value,
it is highlighted.  DB defaults to the current database."
  (or db
      (setq db ebib--cur-db))
  (let* ((dialect (ebib--get-dialect db))
         (entry (ebib-db-get-entry key db))
         (entry-type (cdr (assoc "=type=" entry)))
         (req-fields (ebib--list-fields entry-type 'required dialect))
         (opt-fields (ebib--list-fields entry-type 'optional dialect))
         (extra-fields (ebib--list-fields entry-type 'extra dialect))
         (undef-fields (-remove #'ebib--special-field-p (mapcar #'car (ebib--list-undefined-fields (ebib-db-get-entry key ebib--cur-db) dialect)))))
    (insert (format "%-19s %s%s\n"
                    (propertize "type" 'face 'ebib-field-face)
                    (if (assoc-string entry-type (ebib--list-entry-types (ebib--get-dialect) t) 'case-fold)
                        entry-type
                      (propertize entry-type 'face 'error))
                    (if (and (eq dialect 'biblatex)
                             (assoc-string entry-type ebib--type-aliases 'case-fold))
                        (propertize (format "  [==> %s]" (cdr (assoc-string entry-type ebib--type-aliases 'case-fold))) 'face 'ebib-alias-face)
                      "")))
    (mapc (lambda (fields)
            (when fields ; If one of the sets is empty, we don't want an extra empty line.
              (insert "\n")
              (mapcar (lambda (field)
                        (unless (and (member-ignore-case field ebib-hidden-fields)
                                     ebib--hide-hidden-fields)
                          (insert (propertize (format "%-17s " field) 'face 'ebib-field-face))
                          (insert (or (ebib--get-field-highlighted field key ebib--cur-db match-str)
                                      ""))
                          (insert "\n")))
                      fields)))
          (list req-fields opt-fields extra-fields undef-fields))))

(defun ebib--redisplay ()
  "Redisplay the index and entry buffers."
  (ebib--fill-index-buffer)
  (ebib--fill-entry-buffer))

(defun ebib--fill-index-buffer ()
  "Fill the index buffer with the list of keys in `ebib--cur-db'.
If `ebib--cur-db' is nil, the buffer is just erased and its name set
to \"none\". This function sets `ebib--cur-keys-list'."
  (with-current-ebib-buffer 'index
    ;; First set the modification flag, so that it's still correct after
    ;; with-ebib-buffer-writable.
    (when ebib--cur-db
      (set-buffer-modified-p (ebib-db-modified-p ebib--cur-db)))
    (with-ebib-buffer-writable
      (erase-buffer)
      (if (not ebib--cur-db)
          (progn (rename-buffer " none")
                 (setq ebib--cur-keys-list nil))
        (setq ebib--cur-keys-list (ebib--list-keys))
        ;; We may call this function when there are no entries in the
        ;; database. If so, we don't need to do this:
        (when (ebib--cur-entry-key)
          ;; It may be that no entry satisfies the filter.
          (if (not ebib--cur-keys-list)
              (message "No entries matching the filter")
            ;; Make sure the current entry is among the visible entries.
            (unless (member (ebib--cur-entry-key) ebib--cur-keys-list)
              (ebib-db-set-current-entry-key (car ebib--cur-keys-list) ebib--cur-db))
            (mapc (lambda (entry)
                    (ebib--display-entry-key entry)
                    (when (member entry (ebib-db-list-marked-entries ebib--cur-db))
                      (save-excursion
                        (forward-line -1)
                        (ebib--display-mark t))))
                  ebib--cur-keys-list)
            (goto-char (point-min))
            (re-search-forward (format "^%s " (regexp-quote (ebib--cur-entry-key))))
            (beginning-of-line)
            (ebib--set-index-overlay)))
        (rename-buffer (concat (format " %d:" (1+ (- (length ebib--databases)
                                                     (length (member ebib--cur-db ebib--databases)))))
                               (ebib-db-get-filename ebib--cur-db 'shortened)))))))

(defun ebib--display-mark (mark &optional beg end)
  "Highlight/unhighlight an entry.
If MARK is t, `ebib-marked-face is added, if nil, it is removed.
BEG and END indicate the region to be marked.  If omitted, the
entry at point is (un)highlighted.
NB: if BEG and END are omitted, this function changes point."
  (unless (and beg end)
    (beginning-of-line)
    (setq beg (point))
    (skip-chars-forward "^ ")
    (setq end (point)))
  (if mark
      (add-text-properties beg end '(face ebib-marked-face))
    (remove-text-properties beg end '(face ebib-marked-face))))

(defun ebib--fill-entry-buffer (&optional match-str)
  "Fill the entry buffer with the fields of the current entry.
MATCH-STR is a regexp that will be highlighted when it occurs in
the field contents."
  (with-current-ebib-buffer 'entry
    (with-ebib-buffer-writable
      (erase-buffer)
      (when ebib--cur-keys-list         ; are there entries being displayed?
        (ebib--display-fields (ebib--cur-entry-key) ebib--cur-db match-str)
        (goto-char (point-min))))))

(defun ebib--set-modified (mod &optional db)
  "Set the modified flag MOD on database DB.
MOD must be either t or nil; DB defaults to the current database.
If DB is the current database, the modified flag of the index
buffer is also (re)set.  Return value is MOD."
  (unless db
    (setq db ebib--cur-db))
  (ebib-db-set-modified mod db)
  (when (eq db ebib--cur-db)
    (with-current-ebib-buffer 'index
      (set-buffer-modified-p mod)
      mod)))

(defun ebib--modified-p ()
  "Check if any of the databases in Ebib were modified.
Returns the first modified database, or NIL if none was modified."
  (let ((db (car ebib--databases)))
    (while (and db
                (not (ebib-db-modified-p db)))
      (setq db (ebib--next-elem db ebib--databases)))
    db))

(defun ebib--create-new-database ()
  "Create a new database instance and return it."
  (let ((new-db (ebib-db-new-database)))
    (setq ebib--databases (append ebib--databases (list new-db)))
    new-db))

(defun ebib--store-entry (entry-key fields db &optional timestamp if-exists)
  "Store the entry defined by ENTRY-KEY and FIELDS into DB.
Optional argument TIMESTAMP indicates whether a timestamp is to
be added to the entry.  Note that for a timestamp to be added,
`ebib-use-timestamp' must also be set to T. IF-EXISTS is as for
`ebib-db-set-entry'.

Return ENTRY-KEY if storing the entry was succesful, nil
otherwise.  Depending on the value of IF-EXISTS, storing an entry
may also result in an error."
  (let ((result (ebib-db-set-entry entry-key fields db if-exists)))
    (when result
      (ebib--set-modified t db)
      (when (and timestamp ebib-use-timestamp)
        (ebib-db-set-field-value "timestamp" (format-time-string ebib-timestamp-format) entry-key db 'overwrite)))
    result))

(defun ebib--get-dialect (&optional db)
  "Get the dialect of DB.
DB defaults to the current database.  If DB has no dialect, return
the default dialect, as stored in `ebib-bibtex-dialect'."
  (or db (setq db ebib--cur-db))
  (or (and db (ebib-db-get-dialect db))
      ebib-bibtex-dialect))

(defun ebib--list-keys ()
  "Return a list of entry keys in the current database.
If a filter is active, only the keys of entries that match the
filter are returned.  The returned list is sorted."
  (when ebib--cur-db
    (if (ebib-db-get-filter ebib--cur-db)
        (ebib--filters-run-filter ebib--cur-db 'sort)
      (ebib-db-list-keys ebib--cur-db 'sort))))

;; This is simply to save some typing.
(defun ebib--cur-entry-key ()
  "Get the key of the current entry."
  (ebib--db-get-current-entry-key ebib--cur-db))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(defun ebib (&optional file key)
  "Ebib, a BibTeX database manager.
Optional argument FILE is a file to load.  If FILE is already
loaded, switch to it.  If KEY is given, jump to it."
  (interactive)
  ;; Save the buffer from which Ebib is called.
  (setq ebib--buffer-before (current-buffer))
  ;; And set it as the buffer to push entries to.
  (setq ebib--push-buffer (current-buffer))
  ;; See if there are local databases.
  (or ebib--local-bibtex-filenames
      (setq ebib--local-bibtex-filenames (ebib--get-local-databases)))
  ;; See if there's a key at point.
  (or key (setq key (ebib--read-string-at-point "][^\"@\\&$#%',={} \t\n\f")))
  ;; Initialize Ebib if required.
  (unless ebib--initialized
    (ebib--init))
  ;; Set up the windows.
  (ebib--setup-windows)
  ;; See if we have a file.
  (if file
      (ebib--load-bibtex-file-internal (ebib--locate-bibfile file (append ebib-bib-search-dirs (list default-directory)))))
  ;; See if we have a key; ebib--cur-keys-list must be set for this to work.
  (or ebib--cur-keys-list (setq ebib--cur-keys-list (ebib--list-keys)))
  (if key
      (ebib--find-and-set-key key (buffer-local-value 'ebib--local-bibtex-filenames ebib--buffer-before)))
  (ebib--redisplay))

;;;###autoload
(defun ebib-open-org-link (key)
  "Open Ebib and jump to KEY.
This is for use in Org-mode links."
  (ebib nil key))

(defun ebib--find-and-set-key (key files)
  "Make KEY the current entry.
FILES is a list of BibTeX files in which KEY is searched.  If
FILES is `none', only the current database is searched."
  (when ebib--databases
    (if (eq files 'none)
        (unless (member key ebib--cur-keys-list)
          (setq key nil))
      (let ((database (catch 'found
                        (mapc (lambda (file)
                                (let ((db (ebib--get-db-from-filename file)))
                                  (if (and db (member key (ebib-db-list-keys db)))
                                      (throw 'found db))))
                              files)
                        nil))) ; We must return nil if the key wasn't found anywhere.
        (if (null database)
            (setq key nil)
          (setq ebib--cur-db database))))
    (if key
        (ebib-db-set-current-entry-key key ebib--cur-db))))

(defun ebib--read-string-at-point (chars)
  "Read a string at POINT delimited by CHARS and return it.
CHARS is a string of characters that should not occur in the string."
  (save-excursion
    (skip-chars-backward (concat "^" chars))
    (let ((beg (point)))
      (ebib--looking-at-goto-end (concat "[^" chars "]*"))
      (buffer-substring-no-properties beg (point)))))

(defun ebib--init ()
  "Initialise Ebib.
This function sets all variables to their initial values, creates
the buffers, reads the rc file and loads the files in
`ebib-preload-bib-files'."
  (setq ebib--saved-window-config nil)
  (ebib--create-buffers)
  (if (and ebib-keywords-file
           (file-name-directory ebib-keywords-file)) ; returns nil if there is no directory part
      (add-to-list 'ebib--keywords-files-alist (list (file-name-directory ebib-keywords-file)
                                                     (ebib--read-file-to-list ebib-keywords-file) nil)))
  (setq ebib--keywords-list-per-session (copy-tree ebib-keywords-list))
  (ebib--filters-load-file ebib-filters-default-file)
  (setq ebib--index-overlay (ebib--make-overlay 1 1 (ebib--buffer 'index)))
  (setq ebib--fields-overlay (ebib--make-overlay 1 1 (ebib--buffer 'entry)))
  (setq ebib--strings-overlay (ebib--make-overlay 1 1 (ebib--buffer 'strings)))
  (add-hook 'kill-emacs-query-functions 'ebib--kill-emacs-query-function)
  (add-hook 'kill-buffer-query-functions 'ebib--kill-multiline-query-function)
  (load ebib-rc-file 'noerror)
  (if ebib-preload-bib-files
      (mapc (lambda (file)
              (ebib--load-bibtex-file-internal (or (locate-file file ebib-bib-search-dirs)
                                                   file)))
            ebib-preload-bib-files))
  (setq ebib--initialized t))

(defun ebib--setup-windows ()
  "Create Ebib's window configuration in the current frame."
  ;; If the index buffer is visible, just switch to it.
  (let ((index-window (get-buffer-window (ebib--buffer 'index))))
    (if index-window
        (select-window index-window)
      ;; Save the current window configuration.
      (setq ebib--saved-window-config (current-window-configuration))
      (cond
       ((eq ebib-layout 'full)
        (delete-other-windows))
       ((eq ebib-layout 'custom)
        (setq ebib--window-before (selected-window))
        (let ((width (cond
                      ((integerp ebib-width)
                       (- (window-total-width) ebib-width))
                      ((floatp ebib-width)
                       (- (window-total-width) (truncate (* (window-total-width) ebib-width)))))))
          (select-window (split-window (selected-window) width t)))))
      (let* ((index-window (selected-window))
             (entry-window (split-window index-window ebib-index-window-size
                                         ebib-window-vertical-split)))
        (switch-to-buffer (ebib--buffer 'index))
        (unless (eq ebib-layout 'index-only)
          (set-window-buffer entry-window (ebib--buffer 'entry)))
        (set-window-dedicated-p index-window t)
        (if (eq ebib-layout 'custom)
            (set-window-dedicated-p entry-window t))))))

(defun ebib--create-buffers ()
  "Create the buffers for Ebib."
  ;; First we create a buffer to hold the fields of the current entry.
  (add-to-list 'ebib--buffer-alist (cons 'entry (get-buffer-create "*Ebib-entry*")))
  (with-current-ebib-buffer 'entry
    (ebib-entry-mode)
    (buffer-disable-undo))
  ;; Then we create a buffer to hold the @STRING definitions.
  (add-to-list 'ebib--buffer-alist (cons 'strings (get-buffer-create "*Ebib-strings*")))
  (with-current-ebib-buffer 'strings
    (ebib-strings-mode)
    (buffer-disable-undo))
  ;; The log buffer.
  (add-to-list 'ebib--buffer-alist (cons 'log (get-buffer-create "*Ebib-log*")))
  (with-current-ebib-buffer 'log
    (erase-buffer)
    (insert "Ebib log messages\n\n(Press C-v or SPACE to scroll down, M-v or `b' to scroll up, `q' to quit.)\n\n")
    (ebib-log-mode)
    (buffer-disable-undo))
  ;; And lastly we create a buffer for the entry keys.
  (add-to-list 'ebib--buffer-alist (cons 'index (get-buffer-create " none")))
  (with-current-ebib-buffer 'index
    (ebib-index-mode)
    (buffer-disable-undo)
    (if ebib-index-mode-line
        (setq mode-line-format ebib-index-mode-line))))

(defun ebib-force-quit ()
  "Force quit Ebib by call `ebib-quit'."
  (interactive)
  (ebib-quit t))

(defun ebib-quit (&optional force-quit)
  "Quit Ebib.
The Ebib buffers are killed, all variables except the keymaps are
set to nil.  If optional argument FORCE-QUIT is non-nil, do not
ask for confirmation."
  (interactive)
  ;; kill any multiline buffers first. this will ask for confirmation if
  ;; any of them haven't been saved yet.
  (mapc #'kill-buffer ebib--multiline-buffer-list)
  (when (if (ebib--modified-p)
            (yes-or-no-p "There are modified databases. Quit anyway? ")
          (or force-quit (y-or-n-p "Quit Ebib? ")))
    (ebib-keywords-save-all-new)
    (ebib--filters-update-filters-file)
    (mapc (lambda (x)
            (kill-buffer (cdr x)))
          ebib--buffer-alist)
    (setq ebib--databases nil
          ebib--cur-db nil
          ebib--buffer-alist nil
          ebib--multiline-buffer-list nil
          ebib--initialized nil
          ebib--index-overlay nil
          ebib--fields-overlay nil
          ebib--strings-overlay nil
          ebib--export-filename nil
          ebib--window-before nil
          ebib--buffer-before nil
          ebib--cur-keys-list nil
          ebib--keywords-files-alist nil
          ebib--keywords-list-per-session nil
          ebib--filters-alist nil
          ebib--filters-modified nil)
    (set-window-configuration ebib--saved-window-config)
    (remove-hook 'kill-emacs-query-functions 'ebib--kill-emacs-query-function)
    (remove-hook 'kill-buffer-query-functions 'ebib--kill-multiline-query-function)
    (message "")))

(defun ebib--kill-emacs-query-function ()
  "Function to run if Emacs is killed.
Ask if the user wants to save any modified databases and added
keywords before Emacs is killed."
  (when (or (not (ebib--modified-p))
            (if (y-or-n-p "Save all unsaved Ebib databases? ")
                (progn
                  (ebib-save-all-databases)
                  t)
              (yes-or-no-p "Ebib holds modified databases. Kill anyway? ")))
    (ebib-keywords-save-all-new)
    t))

(defun ebib--kill-multiline-query-function ()
  "Function to call when killing a multiline edit buffer."
  (if (and ebib-multiline-mode
           (buffer-modified-p))
      (yes-or-no-p (format "Multiline edit buffer `%s' not saved. Quit anyway? " (buffer-name)))
    t))

;;;;;;;;;;;;;;;;
;; index-mode ;;
;;;;;;;;;;;;;;;;

;; macro to redefine key bindings.

(defmacro ebib-key (buffer key &optional command _)
  "Bind KEY in BUFFER to COMMAND.
BUFFER is a symbol designating an Ebib buffer and can be `index',
`entry', `strings'.  KEY is a standard Emacs key description as
passed to `define-key'.  If COMMAND is nil, KEY is unbound.

BUFFER can also be `multiline', in which case the second
character of the commands in the multiline edit buffer is set to
KEY.  In this case, COMMAND is meaningless."
  ;; note: the fourth argument is for backward compatibility
  (cond
   ((eq buffer 'index)
    `(define-key ebib-index-mode-map ,key (quote ,command)))
   ((eq buffer 'entry)
    `(define-key ebib-entry-mode-map ,key (quote ,command)))
   ((eq buffer 'strings)
    `(define-key ebib-strings-mode-map ,key (quote ,command)))
   ((eq buffer 'multiline)
    `(progn
       (define-key ebib-multiline-mode-map "\C-c" nil)
       (mapc (lambda (command)
               (define-key ebib-multiline-mode-map (format "\C-c%s%c" ,key (car command)) (cdr command)))
             '((?q . ebib-quit-multiline-buffer-and-save)
               (?c . ebib-cancel-multiline-buffer)
               (?s . ebib-save-from-multiline-buffer)))
       (setq ebib--multiline-key (string-to-char ,key))))))

(defvar ebib-index-mode-map
  (let ((map (make-keymap)))
    (suppress-keymap map 'no-digits)
    (define-key map [up] #'ebib-prev-entry)
    (define-key map [down] #'ebib-next-entry)
    (define-key map [right] #'ebib-next-database)
    (define-key map [left] #'ebib-prev-database)
    (define-key map [prior] #'ebib-index-scroll-down)
    (define-key map [next] #'ebib-index-scroll-up)
    (define-key map [home] #'ebib-goto-first-entry)
    (define-key map [end] #'ebib-goto-last-entry)
    (define-key map [return] #'ebib-select-and-popup-entry)
    (define-key map " " #'ebib-index-scroll-up)
    (define-key map "/" #'ebib-search)
    (define-key map "&" #'ebib-filters-logical-and)
    (define-key map "|" #'ebib-filters-logical-or)
    (define-key map "~" #'ebib-filters-logical-not)
    (define-key map ";" #'ebib-warn-prefix)
    (define-key map "?" #'ebib-info)
    (define-key map "!" #'ebib-generate-autokey)
    (define-key map "<" #'ebib-index-sort-ascending)
    (define-key map ">" #'ebib-index-sort-descending)
    (define-key map "=" #'ebib-index-default-sort)
    (define-key map "a" #'ebib-add-entry)
    (define-key map "A" #'ebib-show-annotation)
    (define-key map "b" #'ebib-index-scroll-down)
    (define-key map "c" #'ebib-index-c)
    (define-key map "C" #'ebib-follow-crossref)
    (define-key map "d" #'ebib-delete-entry) ; prefix
    (define-key map "e" #'ebib-edit-entry)
    (define-key map "E" #'ebib-edit-keyname)
    (define-key map "f" #'ebib-view-file)
    (define-key map "F" 'ebib-filters-map)
    (define-key map "g" #'ebib-goto-first-entry)
    (define-key map "G" #'ebib-goto-last-entry)
    (define-key map "h" #'ebib-index-help)
    (define-key map "H" #'ebib-toggle-hidden)
    (define-key map "i" #'ebib-browse-doi)
    (define-key map "j" #'ebib-next-entry)
    (define-key map "J" #'ebib-switch-to-database)
    (define-key map "k" #'ebib-prev-entry)
    (define-key map "K" 'ebib-keywords-map)
    (define-key map "l" #'ebib-show-log)
    (define-key map "m" #'ebib-mark-entry) ; prefix
    (define-key map "M" #'ebib-mark-all-entries)
    (define-key map "n" #'ebib-search-next)
    (define-key map [(control n)] #'ebib-next-entry)
    (define-key map [(meta n)] #'ebib-index-scroll-up)
    (define-key map "o" #'ebib-load-bibtex-file)
    (define-key map "p" #'ebib-push-bibtex-key) ; prefix
    (define-key map [(control p)] #'ebib-prev-entry)
    (define-key map [(meta p)] #'ebib-index-scroll-down)
    (define-key map "P" #'ebib-edit-preamble)
    (define-key map "q" #'ebib-quit)
    (define-key map "r" #'ebib-reload-current-database)
    (define-key map "R" #'ebib-reload-all-databases)
    (define-key map "s" #'ebib-save-current-database)
    (define-key map "S" #'ebib-edit-strings)
    (define-key map "u" #'ebib-browse-url)
    (define-key map "w" #'ebib-write-database)
    (define-key map "x" #'ebib-export-entry) ; prefix
    (define-key map "\C-xb" #'ebib-leave-ebib-windows)
    (define-key map "\C-xk" #'ebib-quit)
    (define-key map "X" #'ebib-export-preamble)
    (define-key map "y" #'ebib-keywords-add) ; prefix
    (define-key map "z" #'ebib-leave-ebib-windows)
    (define-key map "Z" #'ebib-lower)
    map)
  "Keymap for the ebib index buffer.")

(defun ebib-switch-to-database-nth (nth)
  "Switch to the NTH database.
This function is meant to be bound to the keys 1-9, whereby the
number is also the argument to the function."
  (interactive (list last-command-event))
  (ebib-switch-to-database (- nth 48)))

(mapc (lambda (key)
        (define-key ebib-index-mode-map (format "%d" key)
          'ebib-switch-to-database-nth))
      '(1 2 3 4 5 6 7 8 9))

(define-derived-mode ebib-index-mode
  fundamental-mode "Ebib-index"
  "Major mode for the Ebib index buffer."
  (setq buffer-read-only t)
  (if ebib-hide-cursor
      (setq cursor-type nil))
  (setq truncate-lines t))

(easy-menu-define ebib--index-menu ebib-index-mode-map "Ebib index menu"
  `("Ebib"
    ["Open Database..." ebib-load-bibtex-file t]
    ["Merge Database..." ebib-merge-bibtex-file (and ebib--cur-db (not (ebib-db-get-filter ebib--cur-db)))]
    ["Save Database" ebib-save-current-database (and ebib--cur-db
                                                     (ebib-db-modified-p ebib--cur-db))]
    ["Save All Databases" ebib-save-all-databases (ebib--modified-p)]
    ["Save Database As..." ebib-write-database ebib--cur-db]
    ["Close Database" ebib-close-database ebib--cur-db]
    "--"
    ,(append (list "BibTeX Dialect")
             (mapcar (lambda (d)
                       (vector (format "%s" d) `(ebib-set-dialect (quote ,d))
                               :active 'ebib--cur-db
                               :style 'radio
                               :selected `(and ebib--cur-db
                                               (eq (ebib-db-get-dialect ebib--cur-db) (quote ,d)))))
                     bibtex-dialect-list)
             (list ["Default" (ebib-set-dialect nil)
                    :active ebib--cur-db :style radio :selected (and ebib--cur-db (not (ebib-db-get-dialect ebib--cur-db)))]))
    "--"
    ["Save New Keywords For Database" ebib-keywords-save-cur-db (ebib--keywords-new-p ebib--cur-db)]
    ["Save All New Keywords" ebib-keywords-save-all-new (ebib--keywords-new-p)]
    "--"
    ("Entry"
     ["Add" ebib-add-entry (and ebib--cur-db (not (ebib-db-get-filter ebib--cur-db)))]
     ["Edit" ebib-edit-entry ebib--cur-keys-list]
     ["Delete" ebib-delete-entry (and ebib--cur-db
                                      (ebib--cur-entry-key)
                                      (not (ebib-db-get-filter ebib--cur-db)))])
    ["Edit Strings" ebib-edit-strings (and ebib--cur-db (not (ebib-db-get-filter ebib--cur-db)))]
    ["Edit Preamble" ebib-edit-preamble (and ebib--cur-db (not (ebib-db-get-filter ebib--cur-db)))]
    "--"
    ["Open URL" ebib-browse-url (and ebib--cur-db (ebib-db-get-field-value ebib-url-field (ebib--cur-entry-key) ebib--cur-db 'noerror))]
    ["Open DOI" ebib-browse-doi (and ebib--cur-db (ebib-db-get-field-value ebib-doi-field (ebib--cur-entry-key) ebib--cur-db 'noerror))]
    ["View File" ebib-view-file (and ebib--cur-db (ebib-db-get-field-value ebib-file-field (ebib--cur-entry-key) ebib--cur-db 'noerror))]
    ("Print Entries"
     ["As Bibliography" ebib-latex-entries (and ebib--cur-db (not (ebib-db-get-filter ebib--cur-db)))]
     ["As Index Cards" ebib-print-entries ebib--cur-db]
     ["Print Multiline Fields" ebib-toggle-print-multiline :enable t
      :style toggle :selected ebib-print-multiline]
     ["Print Cards on Separate Pages" ebib-toggle-print-newpage :enable t
      :style toggle :selected ebib-print-newpage])
    "--"
    ("Options"
     ["Show Hidden Fields" ebib-toggle-hidden :enable t
      :style toggle :selected (not ebib--hide-hidden-fields)]
     ["Use Timestamp" ebib-toggle-timestamp :enable t
      :style toggle :selected ebib-use-timestamp]
     ["Save Cross-Referenced Entries First" ebib-toggle-xrefs-first :enable t
      :style toggle :selected ebib-save-xrefs-first]
     ["Allow Identical Fields" ebib-toggle-identical-fields :enable t
      :style toggle :selected ebib-allow-identical-fields]
     ["Full Layout" ebib-toggle-layout :enable t
      :style toggle :selected (eq ebib-layout 'full)]
     ["Customize Ebib" ebib-customize t])
    ["View Log Buffer" ebib-show-log t]
    ["Lower Ebib" ebib-lower t]
    ["Quit" ebib-quit t]
    ["Help on Ebib" ebib-info t]))

(easy-menu-add ebib--index-menu ebib-index-mode-map)

(defun ebib-customize ()
  "Switch to Ebib's customisation group."
  (interactive)
  (ebib-lower)
  (customize-group 'ebib))

(defun ebib-load-bibtex-file (&optional file)
  "Open the BibTeX file FILE."
  (interactive)
  (unless file
    (setq file (ebib--ensure-extension (read-file-name "File to open: " "~/") (car ebib-bibtex-extensions))))
  (ebib--load-bibtex-file-internal file)
  (ebib--redisplay))

(defun ebib--load-bibtex-file-internal (file)
  "Helper function for `ebib--load-bibtex-file'.
FILE must be a fully expanded filename."
  (let ((db (ebib--get-db-from-filename file)))
    (if db                              ; FILE is already open in Ebib.
        (setq ebib--cur-db db)
      (setq ebib--cur-db (ebib--create-new-database))
      (ebib-db-set-filename file ebib--cur-db)
      (setq ebib--log-error nil)         ; we haven't found any errors
      (ebib--log 'log "%s: Opening file %s" (format-time-string "%d %b %Y, %H:%M:%S") file)
      (if (file-exists-p file)
          (progn
            ;; load the entries in the file
            (ebib--load-entries file ebib--cur-db)
            ;; If the user makes any changes, we'll want to create a back-up.
            (ebib-db-set-backup t ebib--cur-db)
            (ebib-db-set-current-entry-key t ebib--cur-db)
            (ebib--set-modified nil))
        ;; if the file does not exist, we need to issue a message.
        (ebib--log 'message "(New file)"))
      ;; add keywords for the new database
      (ebib--keywords-load-keywords ebib--cur-db)
      (if ebib--keywords-files-alist
          (ebib--log 'log "Using keywords from %s.\n" (ebib--keywords-get-file ebib--cur-db))
        (ebib--log 'log "Using general keyword list.\n")))))

(defun ebib-reload-current-database ()
  "Reload the current database from disk."
  (interactive)
  (ebib--execute-when
    ((entries)
     (when (yes-or-no-p "Reload current database from file? ")
       (ebib--reload-database ebib--cur-db)
       (ebib--set-modified nil)
       (ebib--redisplay)
       (message "Database reloaded")))
    ((default) (beep))))

(defun ebib-reload-all-databases ()
  "Reload all databases from disk."
  (interactive)
  (when (yes-or-no-p "Reload all databases from file? ")
    (mapc (lambda (db)
            (ebib--reload-database db)
            (ebib--set-modified nil db))
          ebib--databases)
    (ebib--redisplay)))

(defun ebib--reload-database (db)
  "Reload database DB from disk."
  (let ((file (ebib-db-get-filename db)))
    ;; first clear out some variables
    (ebib-db-clear-database db)
    ;; then load the file
    (ebib--log 'log "%s: Reloading file %s" (format-time-string "%d-%b-%Y: %H:%M:%S") file)
    (ebib-db-set-filename file db)
    (ebib--load-entries file db)
    (ebib-db-set-current-entry-key t db)))

(defun ebib-merge-bibtex-file ()
  "Merge a BibTeX file into the current database."
  (interactive)
  (ebib--execute-when
    ((real-db)
     (let ((file (expand-file-name (read-file-name "File to merge: "))))
       (if (not (file-readable-p file))
           (error "No such file: %s" file)
         (setq ebib--log-error nil)      ; we haven't found any errors (yet)
         (ebib--log 'log "%s: Merging file %s" (format-time-string "%d-%b-%Y: %H:%M:%S") (ebib-db-get-filename ebib--cur-db))
         (ebib--load-entries file ebib--cur-db)
         (unless (ebib--cur-entry-key)
           (ebib-db-set-current-entry-key t ebib--cur-db))
         (ebib--redisplay)
         (ebib--set-modified t))))
    ((default) (beep))))

(defun ebib--load-entries (file db)
  "Load BibTeX entries from FILE into DB.
If FILE specifies a BibTeX dialect and no dialect is set for DB,
also set DB's dialect."
  (with-temp-buffer
    (insert-file-contents file)
    (unless (ebib-db-get-dialect db)
      (ebib-db-set-dialect (parsebib-find-bibtex-dialect) db))
    (let ((result (ebib--find-bibtex-entries db nil)))
      ;; Log the results.
      (ebib--log 'message "%d entries, %d @STRINGs and %s @PREAMBLE found in file."
                 (car result)
                 (cadr result)
                 (if (nth 2 result)
                     "a"
                   "no"))
      (when ebib--log-error
        (message "%s found! Press `l' to check Ebib log buffer." (nth ebib--log-error '("Warnings" "Errors")))))))

(defun ebib--find-bibtex-entries (db timestamp)
  "Find the BibTeX entries in the current buffer.
The search is started at the beginnig of the buffer.  All entries
found are stored in DB.  Return value is a three-element list: the
first element is the number of entries found, the second the
number of @STRING definitions, and the third is T or NIL,
indicating whether a @PREAMBLE was found.

TIMESTAMP indicates whether a timestamp is to be added to each
entry.  Note that a timestamp is only added if `ebib-use-timestamp'
is set to T."
  (let ((n-entries 0)
        (n-strings 0)
        (preamble nil)
        (entry-list (ebib--list-entry-types (ebib--get-dialect db))))
    (goto-char (point-min))
    (cl-loop for entry-type = (ebib--find-next-bibtex-item)
             while entry-type do
             (cond
              ((cl-equalp entry-type "string") ; `cl-equalp' compares strings case-insensitively.
               (if (ebib--read-string db)
                   (setq n-strings (1+ n-strings))))
              ((cl-equalp entry-type "preamble")
               (when (ebib--read-preamble db)
                 (setq preamble t)))
              ((cl-equalp entry-type "comment")
               (ebib--read-comment db))
              ((stringp entry-type)
               (when (ebib--read-entry entry-type db timestamp)
                 (setq n-entries (1+ n-entries))
                 (unless (assoc-string entry-type entry-list 'case-fold)
                   (ebib--log 'warning "Line %d: Unknown entry type `%s'." (line-number-at-pos) entry-type))))))
    (list n-entries n-strings preamble)))

(defun ebib--find-next-bibtex-item ()
  "Search for the next BibTeX item in the current buffer.
A BibTeX item is an entry, or a @Preamble, @String or @Comment
definition.  If an item is found, point is placed right after it
and the entry type is returned.  If no item is found, point is
left at the end of the buffer and nil is returned.  If something
is found that appears to be an entry (essentially, an `@' at the
start of a line), but does not consist of a valid BibTeX
identifier, an error is logged and t is returned."
  (condition-case err
      (parsebib-find-next-item)
    (parsebib-entry-type-error (ebib--log 'error "Error: illegal entry type at line %d. Skipping" (line-number-at-pos (cadr err)))
                               t))) ; return t so that searching continues in ebib--find-bibtex-entries

(defun ebib--read-comment (db)
  "Read an @Comment entry and store it in DB.
If the @Comment is a local variable list, store it as such in
DB."
  (let ((comment (parsebib-read-comment)))
    (when comment
      (let ((lvars (ebib--local-vars-to-list comment)))
        (if lvars
            (ebib-db-set-local-vars lvars db)
          (ebib-db-set-comment comment db))))))

(defun ebib--read-string (db)
  "Read an @STRING definition and store it in DB.
Return value is the string if one was read, nil otherwise."
  (let* ((def (parsebib-read-string))
         (abbr (car def))
         (string (cdr def)))
    (if def
        (if (ebib-db-set-string abbr string db 'noerror)
            string
          (ebib--log 'warning (format "Line %d: @STRING definition `%s' duplicated. Skipping."
                                      (line-number-at-pos) abbr)))
      (ebib--log 'error "Error: illegal string identifier at line %d. Skipping" (line-number-at-pos)))))

(defun ebib--read-preamble (db)
  "Read a @PREAMBLE definition and store it in DB.
If there was already another @PREAMBLE definition, the new one is
added to the existing one with a hash sign `#' between them."
  (let ((preamble (parsebib-read-preamble)))
    (if preamble
        (ebib-db-set-preamble preamble db 'append))))

(defun ebib--read-entry (entry-type db &optional timestamp)
  "Read a BibTeX entry with type ENTRY-TYPE and store it in DB.
Return the entry key if an entry was found, NIL otherwise.
Optional argument TIMESTAMP indicates whether a timestamp is to
be added.  (Whether a timestamp is actually added also depends on
`ebib-use-timestamp'.)"
  (let* ((beg (point)) ; save the start of the entry in case something goes wrong.
         (entry (parsebib-read-entry entry-type))
         (entry-key (cdr (assoc-string "=key=" entry))))
    (when (string= entry-key "")
      (setq entry-key (ebib--generate-tempkey db))
      (ebib--log 'warning "Line %d: Temporary key generated for entry." (line-number-at-pos beg)))
    (unless (ebib--store-entry entry-key entry db timestamp (if ebib-uniquify-keys 'uniquify 'noerror))
      (ebib--log 'warning "Line %d: Entry `%s' duplicated. Skipping." (line-number-at-pos beg) entry-key))
    entry-key))                         ; Return the entry key.

(defun ebib-leave-ebib-windows ()
  "Leave the Ebib windows, lowering them if necessary."
  (interactive)
  (ebib-lower t))

(defun ebib-lower (&optional soft)
  "Hide the Ebib windows.
If optional argument SOFT is non-NIL, just switch to a non-Ebib
buffer if Ebib is not occupying the entire frame."
  (interactive)
  (unless (member (window-buffer) (mapcar #'cdr ebib--buffer-alist))
    (error "Ebib is not active "))
  (cond
   ((and soft (eq ebib-layout 'custom))
    (select-window ebib--window-before))
   ((and soft (eq ebib-layout 'index-only))
    (other-window 1)
    (if (member (current-buffer) (mapcar #'cdr ebib--buffer-alist))
        (switch-to-buffer nil)))
   (t (set-window-configuration ebib--saved-window-config)))
  (mapc (lambda (buffer)
          (bury-buffer buffer))
        (mapcar #'cdr ebib--buffer-alist)))

(defun ebib-prev-entry ()
  "Move to the previous BibTeX entry."
  (interactive)
  (ebib--execute-when
    ((entries)
     ;; if the current entry is the first entry,
     (let ((prev (ebib--prev-elem (ebib--cur-entry-key) ebib--cur-keys-list)))
       (if (not prev)                   ; if we're on the first entry
           (beep)                       ; just beep
         (ebib-db-set-current-entry-key prev ebib--cur-db)
         (goto-char (overlay-start ebib--index-overlay))
         (forward-line -1)
         (ebib--set-index-overlay)
         (ebib--fill-entry-buffer))))
    ((default)
     (beep))))

(defun ebib-next-entry ()
  "Move to the next BibTeX entry."
  (interactive)
  (ebib--execute-when
    ((entries)
     (let ((next (ebib--next-elem (ebib--cur-entry-key) ebib--cur-keys-list)))
       (if (not next)                   ; if we're on the last entry,
           (beep)                       ; just beep
         (ebib-db-set-current-entry-key next ebib--cur-db)
         (goto-char (overlay-start ebib--index-overlay))
         (forward-line 1)
         (ebib--set-index-overlay)
         (ebib--fill-entry-buffer))))
    ((default)
     (beep))))

(defun ebib-show-annotation ()
  "Show the contents of the `annote' field in a *Help* window."
  (interactive)
  (let ((help-window-select t)) ; make sure the help window is selected
    (with-help-window (help-buffer)
      (princ (propertize (format "Annotation for `%s' [%s]" (ebib--cur-entry-key) (ebib-db-get-filename ebib--cur-db 'shortened)) 'face '(:weight bold)))
      (princ "\n\n")
      (let ((contents (ebib-db-get-field-value "annotation" (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced)))
        (if contents
            (princ contents)
          (princ "[No annotation]"))))))

(defun ebib--add-entry-stub (&optional entry db)
  "Add ENTRY to DB in the form of a stub.
Returns the database key of the created entry.  ENTRY is an
optional alist consisting of (FIELD . VALUE) pairs.  The alist is
converted into a BibTeX entry stub and added to DB, which
defaults to the current database.  If an entry alist doesn't
contain the `=type=' field, the entry type is set to the value of
`ebib-default-entry-type'.  If it doesn't contain a `=key=' field,
a key is created of the form \"<new-entry%d>\", where %d is
replaced with a number in ascending sequence."
  (unless db
    (setq db ebib--cur-db))
  (let ((fields ())
        entry-key)
    (cl-dolist (props entry)
      ;;aggregate properties, some require special handling
      (cond
       ((string= (car props) "=key=")
        (setq entry-key (cdr props)))
       ((string= (car props) "=type=")   ; the =type= field should not be braced.
        (push props fields))
       ((cl-equalp (car props) ebib-file-field)
        (let ((short-file (ebib--file-relative-name (expand-file-name (cdr props)))))
          (push (cons ebib-file-field (ebib-db-brace short-file)) fields)))
       (t
        (push (cons (car props) (ebib-db-brace (cdr props))) fields))))
    ;;check for required
    (unless entry-key
      (setq entry-key (ebib--generate-tempkey db)))
    (unless (assoc "=type=" fields)
      (push (cons "=type=" ebib-default-entry-type) fields))
    ;; insert
    (ebib--store-entry entry-key fields db t ebib-uniquify-keys)
    entry-key))

(defun ebib-add-entry ()
  "Interactively add a new entry to the database."
  (interactive)
  (ebib--execute-when
    ((real-db)
     (let ((entry-alist (list)))
       (unless ebib-autogenerate-keys
         (push (cons '=key= (read-string "New entry key: " nil 'ebib--key-history)) entry-alist))
       (ebib-db-set-current-entry-key (ebib--add-entry-stub entry-alist ebib--cur-db) ebib--cur-db)
       (ebib--redisplay)
       (ebib--edit-entry-internal)))
    ((no-database)
     (error "No database open. Use `o' to open a database first"))
    ((default)
     (beep))))

(defun ebib-add-file-entry (&optional filepath db disable-prompt allow-duplicates)
  "Add an entry stub for an optional FILEPATH to DB.
If FILEPATH is a list, add entries for each file contained
within.  If FILEPATH is a directory, add entries for all its
contents.  And if FILEPATH is not given, prompt the user to
browse in the minibuffer, unless DISABLE-PROMPT is T.  If a
FILEPATH is already referenced by an entry in the DB, then it is
ignored by default, unless ALLOW-DUPLICATES is true, in which
case add new entry stubs for each file anyway."
  (interactive)
  (or db
      (setq db ebib--cur-db))
  (let (all-entry-files)
    (cl-labels
        ((file-exists-in-db-p (fp)
                              (if (member (locate-file fp ebib-file-search-dirs) all-entry-files)
                                  t))
         (add-file-entry (fp)
                         (cond
                          ((listp fp)
                           (cl-dolist (file fp) (add-file-entry file)))
                          ((file-directory-p fp)
                           (add-file-entry (directory-files fp t "^\\([^.]\\)"))) ;ignore hidden
                          ((file-exists-p fp)
                           (if (and (null allow-duplicates) (file-exists-in-db-p fp))
                               (message "File %s already exists in db, skipping" fp)
                             (ebib--add-entry-stub (list (cons ebib-file-field fp)) db)
                             (message "Adding file %s" fp)))
                          (t
                           (error "Invalid file %s" fp)))))
      ;;prompt for file
      (if (and (null filepath) (null disable-prompt))
          (setq filepath (read-file-name "Add file or directory: " (file-name-as-directory (car ebib-file-search-dirs)))))
      ;;collect all file paths from db entries into single list
      (unless allow-duplicates
        (cl-dolist (entry-key (ebib-db-list-keys db))
          (let ((entry-files (ebib-db-get-field-value ebib-file-field entry-key db 'noerror 'unbraced)))
            (if entry-files
                (cl-dolist (fp (split-string entry-files (regexp-quote ebib-filename-separator)))
                  (push (locate-file fp ebib-file-search-dirs) all-entry-files))))))
      (add-file-entry filepath)
      (ebib-db-set-current-entry-key t ebib--cur-db)
      (ebib--redisplay))))

(defun ebib-generate-autokey ()
  "Automatically generate a key for the current entry.
This function uses the function BIBTEX-GENERATE-AUTOKEY to
generate the key, see that function's documentation for details."
  (interactive)
  (ebib--execute-when
    ((real-db entries)
     (let ((new-key
            (with-temp-buffer
              ;; We sort the entry fields when formatting, because if both
              ;; `author' and `editor' fields are present,
              ;; `bibtex-generate-autokey' will simply use the first one it
              ;; finds. By sorting we make sure it's always the author.
              (ebib--format-entry (ebib--cur-entry-key) ebib--cur-db nil 'sort)
              (let ((x-ref (ebib-db-get-field-value "crossref" (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced)))
                (if x-ref
                    (ebib--format-entry x-ref ebib--cur-db nil 'sort)))
              (goto-char (point-min))
              (bibtex-set-dialect (ebib--get-dialect) 'local)
              (bibtex-generate-autokey))))
       (if (string= new-key "")
           (error (format "Cannot create key"))
         (ebib--update-keyname new-key))))
    ((default)
     (beep))))

(defun ebib--generate-tempkey (&optional db)
  "Generate a unique temp key in DB or the current database.
Keys are in the form: <new-entry1>, <new-entry2>, ..."
  (unless db
    (setq db ebib--cur-db))
  (let ((key-list (ebib-db-list-keys db))
        (entry-key "<new-entry1>")
        (key-count 2))
    (while (member entry-key key-list)
      (setq entry-key (format "<new-entry%d>" key-count))
      (setq key-count (1+ key-count)))
    entry-key))

(defun ebib-index-c ()
  "Helper function for the `c' key in the index buffer."
  (interactive)
  (if (ebib-db-filtered-p ebib--cur-db)
      (ebib-filters-cancel-filter)
    (ebib-close-database)))

(defun ebib-close-database ()
  "Close the current BibTeX database."
  (interactive)
  (ebib--execute-when
    ((database)
     (catch 'return
       (unless (if (ebib-db-modified-p ebib--cur-db)
                   (yes-or-no-p "Database modified. Close it anyway? ")
                 (y-or-n-p "Close database? "))
         (throw 'return nil))

       ;; kill associated multiline edit buffers. this asks for
       ;; confirmation if there are unsaved modifications.
       (mapc (lambda (buffer)
               (unless (kill-buffer buffer)
                 (throw 'return nil)))
             (--filter (string= (ebib-db-get-filename ebib--cur-db) (cl-second (buffer-local-value 'ebib--multiline-info it)))
                       ebib--multiline-buffer-list))

       ;; save keywords
       (ebib--keywords-save-new-keywords ebib--cur-db)

       ;; remove the database from `ebib--databases' and redisplay
       (let ((new-db (ebib--next-elem ebib--cur-db ebib--databases)))
         (setq ebib--databases (delq ebib--cur-db ebib--databases))
         (setq ebib--cur-db (if ebib--databases   ; do we still have another database loaded?
                                (or new-db (-last-item ebib--databases))
                              nil))
         (ebib--redisplay)
         (message "Database closed."))))))

(defun ebib-index-sort-ascending (field)
  "Sort the entries in the index according to the contents of FIELD."
  (interactive (list (completing-read "Sort field: " (ebib--list-fields-uniquely (ebib--get-dialect)) nil t nil 'ebib--field-history)))
  (unless (string= field "")
    (ebib-db-set-sortinfo (cons field 'ascend) ebib--cur-db)
    (ebib--redisplay)))

(defun ebib-index-sort-descending (field)
  "Sort the entries in the index according to the contents of FIELD."
  (interactive (list (completing-read "Sort field: " (ebib--list-fields-uniquely (ebib--get-dialect)) nil t nil 'ebib--field-history)))
  (unless (string= field "")
    (ebib-db-set-sortinfo (cons field 'descend) ebib--cur-db)
    (ebib--redisplay)))

(defun ebib-index-default-sort ()
  "Sort index buffer on citation key."
  (interactive)
  (ebib-db-set-sortinfo nil ebib--cur-db)
  (ebib--redisplay))

(defun ebib-goto-first-entry ()
  "Move to the first BibTeX entry in the database."
  (interactive)
  (ebib--execute-when
    ((entries)
     (ebib-db-set-current-entry-key (car ebib--cur-keys-list) ebib--cur-db)
     (with-current-ebib-buffer 'index
       (goto-char (point-min))
       (ebib--set-index-overlay)
       (ebib--fill-entry-buffer)))
    ((default)
     (beep))))

(defun ebib-goto-last-entry ()
  "Move to the last entry in the BibTeX database."
  (interactive)
  (ebib--execute-when
    ((entries)
     (ebib-db-set-current-entry-key (-last-item ebib--cur-keys-list) ebib--cur-db)
     (with-current-ebib-buffer 'index
       (goto-char (point-min))
       (forward-line (1- (length ebib--cur-keys-list)))
       (ebib--set-index-overlay)
       (ebib--fill-entry-buffer)))
    ((default)
     (beep))))

(defun ebib-edit-entry ()
  "Edit the current BibTeX entry."
  (interactive)
  (ebib--execute-when
    ((entries)
     (ebib--edit-entry-internal))
    ((default)
     (beep))))

(defun ebib--edit-entry-internal ()
  "Helper function for `ebib-edit-entry'."
  (ebib--pop-to-buffer (ebib--buffer 'entry))
  (ebib--set-fields-overlay))

(defun ebib-edit-keyname ()
  "Change the key of a BibTeX entry."
  (interactive)
  (ebib--execute-when
    ((real-db entries)
     (let ((cur-keyname (ebib--cur-entry-key)))
       (ebib--ifstring (new-keyname (read-string (format "Change `%s' to: " cur-keyname)
                                                 cur-keyname
                                                 'ebib--key-history))
           (ebib--update-keyname new-keyname))))
    ((default)
     (beep))))

(defun ebib--update-keyname (new-key)
  "Change the key of the current BibTeX entry to NEW-KEY.
This function updates both the database and the buffer."
  (let ((marked (ebib-db-marked-p (ebib--cur-entry-key) ebib--cur-db))
        (actual-new-key (ebib-db-change-key (ebib--cur-entry-key) new-key ebib--cur-db (if ebib-uniquify-keys 'uniquify 'noerror))))
    (when actual-new-key
      (ebib-db-set-current-entry-key actual-new-key ebib--cur-db)
      (if marked (ebib-mark-entry))
      (ebib--redisplay)
      (ebib--set-modified t))))

(defun ebib-mark-entry ()
  "Mark or unmark the current entry."
  (interactive)
  (ebib--execute-when
    ((entries)
     (with-current-ebib-buffer 'index
       (with-ebib-buffer-writable
         (ebib-db-toggle-mark (ebib--cur-entry-key) ebib--cur-db)
         (ebib--display-mark (ebib-db-marked-p (ebib--cur-entry-key) ebib--cur-db)
                             (overlay-start ebib--index-overlay)
                             (overlay-end ebib--index-overlay)))))
    ((default)
     (beep))))

(defun ebib-mark-all-entries ()
  "Mark or unark all entries.
If there are marked entries, all entries are unmarked.  Otherwise,
all entries are marked."
  (interactive)
  (ebib--execute-when
    ((marked-entries)
     (ebib-db-unmark-entry 'all ebib--cur-db)
     (ebib--fill-index-buffer)
     (message "All entries unmarked"))
    ((entries)
     (ebib-db-mark-entry 'all ebib--cur-db)
     (ebib--fill-index-buffer)
     (message "All entries marked"))
    ((default)
     (beep))))

(defun ebib-index-scroll-down ()
  "Move one page up in the database."
  (interactive)
  (ebib--execute-when
    ((entries)
     (scroll-down)
     (ebib--select-entry))
    ((default)
     (beep))))

(defun ebib-index-scroll-up ()
  "Move one page down in the database."
  (interactive)
  (ebib--execute-when
    ((entries)
     (scroll-up)
     (ebib--select-entry))
    ((default)
     (beep))))

(defun ebib--format-entry (key db timestamp &optional sort)
  "Write entry KEY in DB into the current buffer in BibTeX format.
If TIMESTAMP is non-nil and `ebib-use-timestamp' is set, a
timestamp is added to the entry, possibly overwriting an existing
timestamp.  If SORT is non-nil, the fields are sorted before
formatting the entry."
  (let ((entry (ebib-db-get-entry key db 'noerror)))
    (setq entry (if sort
                    (cl-sort (copy-sequence entry) #'string< :key #'car)
                  ;; When reading, fields are stored with `push', so if we don't
                  ;; sort, we need to reverse them to get the original order
                  ;; back. See github issues #42, #55, #62.
                  (reverse entry)))
    (when entry
      (insert (format "@%s{%s,\n" (cdr (assoc "=type=" entry)) key))
      (mapc (lambda (field)
              (unless (or (not (cdr field)) ; Deleted fields have their value set to `nil'. See `ebib-db-set-field-value'.
                          (ebib--special-field-p (car field))
                          (and (cl-equalp (car field) "timestamp") timestamp ebib-use-timestamp))
                (insert (format "\t%s = %s,\n" (car field) (cdr field)))))
            entry)
      (if (and timestamp ebib-use-timestamp)
          (insert (format "\ttimestamp = {%s}" (format-time-string ebib-timestamp-format)))
        (delete-char -2))               ; the final ",\n" must be deleted
      (insert "\n}\n\n"))))

(defun ebib--format-comments (db)
  "Write the @COMMENTS of DB into the current buffer in BibTeX format.
If DB is set to a specific dialect, write it to a @COMMENT as
well, if it is not already in a @COMMENT."
  (mapc (lambda (c)
          (insert (format "@Comment{%s}\n\n" c)))
        (ebib-db-get-comments db)))

(defun ebib--format-strings (db)
  "Write the @STRINGs of DB into the current buffer in BibTeX format."
  (mapc (lambda (str)
          (insert (format "@STRING{%s = %s}\n" (car str) (cdr str))))
        (ebib-db-get-all-strings db))
  (insert "\n"))

(defun ebib--get-sortstring (entry-key sortkey-list db)
  "Return the field value on which the entry ENTRY-KEY is to be sorted.
SORTKEY-LIST is a list of fields that are considered in order for
the sort value.  DB is the database that contains the entry
referred to by ENTRY-KEY."
  (let ((sort-string nil))
    (while (and sortkey-list
                (null (setq sort-string (ebib-db-get-field-value (car sortkey-list) entry-key db 'noerror 'unbraced))))
      (setq sortkey-list (cdr sortkey-list)))
    sort-string))

(defun ebib--format-local-vars (db)
  "Write the local variables of DB into the current buffer."
  (let ((lvars (ebib-db-get-local-vars db)))
    (when lvars
      (insert (concat "@Comment{\n"
                      ebib-local-variable-indentation "Local Variables:\n"
                      (mapconcat (lambda (e) (format "%s%s: %s\n" ebib-local-variable-indentation (car e) (cadr e))) lvars "")
                      ebib-local-variable-indentation "End:\n"
                      "}\n\n")))))

(defun ebib--format-database-as-bibtex (db)
  "Write database DB into the current buffer in BibTeX format."
  (when (ebib-db-get-preamble db)
    (insert (format "@PREAMBLE{%s}\n\n" (ebib-db-get-preamble db))))
  (ebib--format-comments db)
  (ebib--format-strings db)
  ;; We define two comparison functions for `sort'. These must simply
  ;; return non-NIL if the first element is to be sorted before the second.
  (cl-flet
      ;; The first one is simple: if X has a crossref field, it must be
      ;; sorted before Y (or at least *can* be, if Y also has a crossref
      ;; field).
      ((compare-xrefs (x _)
                      (ebib-db-get-field-value "crossref" x db 'noerror))
       ;; This one's a bit trickier. We iterate over the lists of fields in
       ;; `ebib-sort-order'. For each level, `ebib--get-sortstring' then
       ;; returns the string that can be used for sorting. If all fails,
       ;; sorting is done on the basis of the entry key.
       (entry< (x y)
               (let (sortstring-x sortstring-y)
                 (cl-loop for sort-list in ebib-sort-order do
                          (setq sortstring-x (ebib--get-sortstring x sort-list db))
                          (setq sortstring-y (ebib--get-sortstring y sort-list db))
                          while (cl-equalp sortstring-x sortstring-y))
                 (if (and sortstring-x sortstring-y)
                     (string< sortstring-x sortstring-y)
                   (string< x y)))))    ; compare entry keys
    ;; Only entries in `ebib--cur-keys-list' are saved, in case we're
    ;; writing a filtered db to a new file.
    (let ((sorted-list (copy-tree ebib--cur-keys-list)))
      (cond
       (ebib-save-xrefs-first
        (setq sorted-list (sort sorted-list #'compare-xrefs)))
       (ebib-sort-order
        (setq sorted-list (sort sorted-list #'entry<))))
      (mapc (lambda (key) (ebib--format-entry key db nil)) sorted-list))
    (ebib--format-local-vars db)))

(defun ebib--make-backup (file)
  "Create a backup of FILE.
Honour `ebib-create-backups' and BACKUP-DIRECTORY-ALIST."
  (when ebib-create-backups
    (let ((backup-file (make-backup-file-name file)))
      (if (file-writable-p backup-file)
          (copy-file file backup-file t)
        (ebib--log 'error "Could not create backup file `%s'" backup-file)))))

(defun ebib--save-database (db)
  "Save the database DB."
  (when (and (ebib-db-backup-p db)
             (file-exists-p (ebib-db-get-filename db)))
    (ebib--make-backup (ebib-db-get-filename db))
    (ebib-db-set-backup nil db))
  (with-temp-buffer
    (ebib--format-database-as-bibtex db)
    (write-region (point-min) (point-max) (ebib-db-get-filename db)))
  (ebib--set-modified nil db))

(defun ebib-write-database ()
  "Write the current database to a different file.
If the current database is filtered, only the entries that match
the filter are saved.  The original file is not deleted."
  (interactive)
  (ebib--execute-when
    ((database)
     (ebib--ifstring (new-filename (expand-file-name (read-file-name "Save to file: " "~/")))
         (when (or (not (file-exists-p new-filename))
                   (y-or-n-p (format (format "File %s already exists; overwrite? " new-filename))))
           (with-temp-buffer
             (ebib--format-database-as-bibtex ebib--cur-db)
             (write-region (point-min) (point-max) new-filename nil nil nil))
           (if (ebib-db-get-filter ebib--cur-db)
               (message "Wrote filtered entries as new database to %s" new-filename)
             ;; If this wasn't a filtered db, we rename it.
             (ebib-db-set-filename new-filename ebib--cur-db 'overwrite)
             (rename-buffer (concat (format " %d:" (1+ (- (length ebib--databases)
                                                          (length (member ebib--cur-db ebib--databases)))))
                                    (file-name-nondirectory new-filename)))
             (ebib--set-modified nil)))))
    ((default)
     (beep))))

(defun ebib-save-current-database ()
  "Save the current database."
  (interactive)
  (ebib--execute-when
    ((real-db)
     (if (not (ebib-db-modified-p ebib--cur-db))
         (message "No changes need to be saved.")
       (ebib--save-database ebib--cur-db)))
    ((filtered-db)
     ;; Saving a filtered db would result in saving only the entries that
     ;; match the filter.
     (error "Cannot save a filtered database. Use `w' to write to a file."))))

(defun ebib-save-all-databases ()
  "Save all currently open databases if they were modified."
  (interactive)
  (mapc (lambda (db)
          (when (ebib-db-modified-p db)
            (ebib--save-database db)))
        ebib--databases)
  (message "All databases saved."))

(defun ebib-print-filename ()
  "Display the filename of the current database in the minibuffer."
  (interactive)
  (message (ebib-db-get-filename ebib--cur-db)))

(defun ebib-follow-crossref ()
  "Follow the crossref field and jump to that entry.
If the current entry's crossref field is empty, search for the
first entry with the current entry's key in its crossref field."
  (interactive)
  (let ((new-cur-entry (ebib-db-get-field-value "crossref" (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced)))
    (if new-cur-entry
        ;; If there is a cross-reference, see if we can find it.
        (cond
         ((member new-cur-entry ebib--cur-keys-list)
          (ebib-db-set-current-entry-key new-cur-entry ebib--cur-db)
          (ebib--redisplay))
         ((member new-cur-entry (ebib-db-list-keys ebib--cur-db))
          (error "Crossreference `%s' not visible due to active filter" new-cur-entry))
         (t (error "Entry `%s' does not exist" new-cur-entry)))
      ;; Otherwise, we assume the user wants to search for entries
      ;; cross-referencing the current one.
      (setq ebib--search-string (ebib--cur-entry-key))
      (ebib-search-next))))

(defun ebib-toggle-hidden ()
  "Toggle viewing hidden fields."
  (interactive)
  (setq ebib--hide-hidden-fields (not ebib--hide-hidden-fields))
  (ebib--fill-entry-buffer))

(defun ebib-toggle-timestamp ()
  "Toggle using timestamp for new entries."
  (interactive)
  (setq ebib-use-timestamp (not ebib-use-timestamp)))

(defun ebib-toggle-xrefs-first ()
  "Toggle saving of crossreferenced entries first."
  (interactive)
  (setq ebib-save-xrefs-first (not ebib-save-xrefs-first)))

(defun ebib-toggle-identical-fields ()
  "Toggle `ebib-allow-identical-fields'.
If t, Ebib handles entries with identical fields by concatenating
their contents into a single field."
  (interactive)
  (setq ebib-allow-identical-fields (not ebib-allow-identical-fields)))

(defun ebib-toggle-layout ()
  "Toggle the Ebib layout."
  (interactive)
  (if (eq ebib-layout 'full)
      (setq ebib-layout 'custom)
    (setq ebib-layout 'full))
  (ebib-lower)
  (ebib))

(defun ebib-toggle-print-newpage ()
  "Toggle whether index cards are printed with a newpage after each card."
  (interactive)
  (setq ebib-print-newpage (not ebib-print-newpage)))

(defun ebib-toggle-print-multiline ()
  "Toggle whether multiline fields are printed."
  (interactive)
  (setq ebib-print-multiline (not ebib-print-multiline)))

(defun ebib-delete-entry ()
  "Delete the current entry from the database."
  (interactive)
  (cl-flet ((remove-entry (key)
                          (ebib-db-remove-entry key ebib--cur-db)
                          (ebib-db-unmark-entry key ebib--cur-db) ; This is harmless if key isn't marked.
                          (ebib-db-set-current-entry-key (or (ebib--next-elem key ebib--cur-keys-list)
                                                             (-last-item ebib--cur-keys-list))
                                                         ebib--cur-db
                                                         'first)
                          (setq ebib--cur-keys-list (delete key ebib--cur-keys-list))))
    (ebib--execute-when
      ((marked-entries)
       (when (y-or-n-p "Delete all marked entries? ")
         (mapc #'remove-entry (ebib-db-list-marked-entries ebib--cur-db))
         (message "Marked entries deleted.")
         (ebib--set-modified t)
         (ebib--redisplay)))
      ((entries)
       (when (y-or-n-p (format "Delete %s? " (ebib--cur-entry-key)))
         (remove-entry (ebib--cur-entry-key))
         (message (format "Entry `%s' deleted." (ebib--cur-entry-key)))
         (ebib--set-modified t)
         (ebib--redisplay)))
      ((default)
       (beep)))))

(defun ebib-select-and-popup-entry ()
  "Make the entry at point current and display it.
If `ebib-layout' is set to `index-only', also popup the entry
buffer and switch to it."
  (interactive)
  (ebib--execute-when
    ((entries)
     (ebib--select-entry)
     (when (eq ebib-layout 'index-only)
       ;; this makes the entry buffer visible but then switches to the
       ;; index buffer again.
       (ebib--pop-to-buffer (ebib--buffer 'entry))
       (ebib--pop-to-buffer (ebib--buffer 'index))))
    ((default)
     (beep))))

(defun ebib--select-entry ()
  "Make the entry at point current."
  (beginning-of-line)
  (let ((beg (point)))
    (let ((key (save-excursion
                 (skip-chars-forward "^ ")
                 (buffer-substring-no-properties beg (point)))))
      (ebib-db-set-current-entry-key key ebib--cur-db)
      (ebib--set-index-overlay)
      (ebib--fill-entry-buffer))))

;; the exporting functions will have to be redesigned completely. for now (1 Feb
;; 2012) we just define a new function ebib--export-entries. in the long run,
;; this should be the general exporting function, calling other functions as the
;; need arises.

(defun ebib--export-entries (entries &optional source-db filename)
  "Export ENTRIES from SOURCE-DB to FILENAME.
ENTRIES is a list of entry keys.  SOURCE-DB defaults to the
current database.  If FILENAME is not provided, the user is asked
for one."
  (unless filename
    (setq filename (read-file-name
                    "File to export entries to:" "~/" nil nil ebib--export-filename)))
  (unless source-db
    (setq source-db ebib--cur-db))
  (with-temp-buffer
    (insert "\n")
    (mapc (lambda (key)
            (ebib--format-entry key ebib--cur-db nil))
          entries)
    (append-to-file (point-min) (point-max) filename)
    (setq ebib--export-filename filename)))

(defun ebib-export-entry (prefix)
  "Copy entries to another database.
The PREFIX argument indicates which database to copy the entry
to.  If no prefix argument is present, a filename is asked to
which the entry is appended."
  (interactive "P")
  (let ((num (ebib--prefix prefix)))
    (ebib--execute-when
      ((marked-entries)
       (ebib--export-marked-entries num))
      ((entries)
       (ebib--export-single-entry num)))))

(defun ebib--export-single-entry (num)
  "Copy the current entry to another database.
NUM indicates which database to copy the entry to.  If it is nil,
a filename is asked to which the entry is appended."
  (ebib--execute-when
    ((entries)
     (if num
         (ebib--export-to-db num (format "Entry `%s' copied to database %%d." (ebib--cur-entry-key))
                             (lambda (db)
                               (let ((entry-key (ebib--cur-entry-key)))
                                 (if (member entry-key (ebib-db-list-keys db))
                                     (error "Entry key `%s' already exists in database %d" entry-key num)
                                   (ebib--store-entry entry-key (copy-tree (ebib-db-get-entry entry-key ebib--cur-db)) db t)
                                   ;; if this is the first entry in the target DB,
                                   ;; its CUR-ENTRY must be set!
                                   (when (null (ebib--db-get-current-entry-key db))
                                     (ebib-db-set-current-entry-key t db))
                                   t)))) ; we must return T, WHEN does not always do this.
       (ebib--export-to-file (format "Export `%s' to file: " (ebib--cur-entry-key))
                             (lambda ()
                               (insert "\n")
                               (ebib--format-entry (ebib--cur-entry-key) ebib--cur-db t)))))
    ((default)
     (beep))))

(defun ebib--export-marked-entries (num)
  "Copy the marked entries to another database.
NUM indicates which database to copy the entry to.  If it is nil,
a filename is asked to which the entry is appended."
  (ebib--execute-when
    ((marked-entries)
     (if num
         (ebib--export-to-db
          num "Entries copied to database %d."
          (lambda (db)
            (mapc (lambda (entry-key)
                    (if (member entry-key (ebib-db-list-keys db))
                        (error "Entry key `%s' already exists in database %d" entry-key num)
                      (ebib--store-entry entry-key (copy-tree (ebib-db-get-entry entry-key ebib--cur-db)) db t)))
                  (ebib-db-list-marked-entries ebib--cur-db))
            ;; if the target DB was empty before, its CUR-ENTRY must be set!
            (when (null (ebib--db-get-current-entry-key db))
              (ebib-db-set-current-entry-key t db))
            t))         ; we must return T, WHEN does not always do this.
       (ebib--export-to-file "Export to file: "
                             (lambda ()
                               (mapc (lambda (entry-key)
                                       (insert "\n")
                                       (ebib--format-entry entry-key ebib--cur-db t))
                                     (ebib-db-list-marked-entries ebib--cur-db))))))
    ((default)
     (beep))))

(defun ebib-search ()
  "Search the current Ebib database.
The search is conducted with STRING-MATCH and can therefore be a
regexp.  Searching starts with the current entry.  In a filtered
database, only the visible entries are searched."
  (interactive)
  (ebib--execute-when
    ((entries)
     (ebib--ifstring (search-str (read-string "Search database for: "))
         (progn
           (setq ebib--search-string search-str)
           ;; first we search the current entry
           (if (ebib--search-in-entry ebib--search-string
                                      (ebib-db-get-entry (ebib--cur-entry-key) ebib--cur-db))
               (ebib--fill-entry-buffer ebib--search-string)
             ;; if the search string wasn't found in the current entry, we continue searching.
             (ebib-search-next)))))
    ((default)
     (beep))))

(defun ebib-search-next ()
  "Search the next occurrence of `ebib--search-string'.
Searching starts at the entry following the current entry.  If a
match is found, the matching entry is shown and becomes the new
current entry.  If a filter is active, only the visible entries
are searched."
  (interactive)
  (ebib--execute-when
    ((entries)
     (if (null ebib--search-string)
         (message "No search string")
       (let ((cur-search-entry (cdr (member (ebib--cur-entry-key) ebib--cur-keys-list))))
         (while (and cur-search-entry
                     (null (ebib--search-in-entry ebib--search-string
                                                  (ebib-db-get-entry (car cur-search-entry) ebib--cur-db 'noerror))))
           (setq cur-search-entry (cdr cur-search-entry)))
         (if (null cur-search-entry)
             (message (format "`%s' not found" ebib--search-string))
           (ebib-db-set-current-entry-key (car cur-search-entry) ebib--cur-db)
           (with-current-ebib-buffer 'index
             (goto-char (point-min))
             (re-search-forward (format "^%s " (regexp-quote (ebib--cur-entry-key))))
             (beginning-of-line)
             (ebib--set-index-overlay)
             (ebib--fill-entry-buffer ebib--search-string))))))
    ((default)
     (beep))))

(defun ebib--search-in-entry (search-str entry &optional field)
  "Search for SEARCH-STR in ENTRY in the current database.
Return a list of fields in ENTRY that match the regexp
SEARCH-STR, or nil if no matches were found.  If FIELD is given,
only that field is searched.  ENTRY is an alist of (FIELD . VALUE)
pairs.

Normally, the `=type=' field, which stores the entry type, is not
searched, but it is possible to search for specific entry types by
specifying `=type=' for FIELD.  In that case, the search string
can still be a string, but only exact matches will return a
result."
  (let ((case-fold-search t)  ; we want to ensure a case-insensitive search
        (result nil))
    (if field
        (let ((value (cdr (assoc-string field entry 'case-fold))))
          (when (and value
                     (or (and (string= field "=type=") ; The =type= field requires
                              (cl-equalp search-str value)) ; an exact match.
                         (string-match-p search-str value)))
            (setq result (list field))))
      (mapc (lambda (f)
              (when (and (not (ebib--special-field-p (car f))) ; We exlude special fields here.
                         (stringp (cdr f))
                         (string-match-p search-str (cdr f)))
                (setq result (cons (car f) result))))
            entry))
    result))

(defun ebib-edit-strings ()
  "Edit the @STRING definitions in the database."
  (interactive)
  (ebib--execute-when
    ((real-db)
     (ebib--fill-strings-buffer)
     (ebib--pop-to-buffer (ebib--buffer 'strings))
     (goto-char (point-min)))
    ((default)
     (beep))))

(defun ebib-edit-preamble ()
  "Edit the @PREAMBLE definition in the database."
  (interactive)
  (ebib--execute-when
    ((real-db)
     (ebib--multiline-edit (list 'preamble (ebib-db-get-filename ebib--cur-db)) (ebib-db-get-preamble ebib--cur-db)))
    ((default)
     (beep))))

(defun ebib-export-preamble (prefix)
  "Export the @PREAMBLE definition.
If a PREFIX argument is given, it is taken as the database to
export the preamble to.  If the goal database already has a
preamble, the new preamble will be appended to it.  If no prefix
argument is given, the user is asked to enter a filename to which
the preamble is appended."
  (interactive "P")
  (ebib--execute-when
    ((real-db)
     (if (null (ebib-db-get-preamble ebib--cur-db))
         (error "No @PREAMBLE defined")
       (let ((num (ebib--prefix prefix)))
         (if num
             (ebib--export-to-db num "@PREAMBLE copied to database %d"
                                 (lambda (db)
                                   (ebib-db-set-preamble (ebib-db-get-preamble ebib--cur-db) db 'append)))
           (ebib--export-to-file "Export @PREAMBLE to file: "
                                 (lambda ()
                                   (insert (format "\n@preamble{%s}\n\n" (ebib-db-get-preamble ebib--cur-db)))))))))
    ((default)
     (beep))))

(defun ebib-print-entries ()
  "Create a LaTeX file listing the entries.
Either prints the entire database, or the marked entries."
  (interactive)
  (ebib--execute-when
    ((entries)
     (let ((entries (or (ebib-db-list-marked-entries ebib--cur-db 'sort)
                        (ebib-db-list-keys ebib--cur-db 'sort))))
       (ebib--ifstring (tempfile (if (not (string= "" ebib-print-tempfile))
                                     ebib-print-tempfile
                                   (read-file-name "Use temp file: " "~/" nil nil)))
           (progn
             (with-temp-buffer
               (when ebib-print-preamble
                 (mapc (lambda (string)
                         (insert (format "%s\n" string)))
                       ebib-print-preamble))
               (insert "\n\\begin{document}\n\n")
               (mapc (lambda (entry-key)
                       ;; first create a table
                       (insert "\\begin{tabular}{p{0.2\\textwidth}p{0.8\\textwidth}}\n")
                       ;; insert the entry type
                       (let ((entry (ebib-db-get-entry entry-key ebib--cur-db)))
                         (insert (format "\\multicolumn{2}{l}{\\texttt{%s (%s)}}\\\\\n"
                                         entry-key (cdr (assoc "=type=" entry))))
                         (insert "\\hline\n")
                         ;; Then the other fields.
                         (mapc (lambda (field)
                                 (ebib--ifstring (value (cdr (assoc-string field entry 'case-fold)))
                                     (when (or (not (ebib--multiline-p value))
                                               ebib-print-multiline)
                                       (insert (format "%s: & %s\\\\\n"
                                                       field (ebib-db-unbrace value))))))
                               ;; Note: ebib--list-fields returns a list with `=type=' as its first element.
                               (cdr (ebib--list-fields (cdr (assoc "=type=" entry)) 'all (ebib--get-dialect)))))
                       (insert "\\end{tabular}\n\n")
                       (insert (if ebib-print-newpage
                                   "\\newpage\n\n"
                                 "\\bigskip\n\n")))
                     entries)
               (insert "\\end{document}\n")
               (write-region (point-min) (point-max) tempfile))
             (ebib-lower)
             (find-file tempfile)))))
    ((default)
     (beep))))

(defun ebib-latex-entries ()
  "Create a LaTeX file that \\nocites entries from the database.
Operates either on all entries or on the marked entries."
  (interactive)
  (ebib--execute-when
    ((real-db entries)
     (ebib--ifstring (tempfile (if (not (string= "" ebib-print-tempfile))
                                   ebib-print-tempfile
                                 (read-file-name "Use temp file: " "~/" nil nil)))
         (progn
           (with-temp-buffer
             (when ebib-latex-preamble
               (mapc (lambda (string)
                       (insert (format "%s\n" string)))
                     ebib-latex-preamble))
             (insert "\n\\begin{document}\n\n")
             (if (ebib-db-marked-entries-p ebib--cur-db)
                 (mapc (lambda (entry)
                         (insert (format "\\nocite{%s}\n" entry)))
                       (ebib-db-list-marked-entries ebib--cur-db 'sort))
               (insert "\\nocite{*}\n"))
             (insert (format "\n\\bibliography{%s}\n\n" (expand-file-name (ebib-db-get-filename ebib--cur-db))))
             (insert "\\end{document}\n")
             (write-region (point-min) (point-max) tempfile))
           (ebib-lower)
           (find-file tempfile))))
    ((default)
     (beep))))

(defun ebib-switch-to-database (num)
  "Switch do database NUM."
  (interactive "NSwitch to database number: ")
  (let ((new-db (nth (1- num) ebib--databases)))
    (if new-db
        (progn
          (setq ebib--cur-db new-db)
          (ebib--redisplay))
      (error "Database %d does not exist" num))))

(defun ebib-next-database ()
  "Switch to the next database."
  (interactive)
  (ebib--execute-when
    ((database)
     (let ((new-db (ebib--next-elem ebib--cur-db ebib--databases)))
       (unless new-db
         (setq new-db (car ebib--databases)))
       (setq ebib--cur-db new-db)
       (ebib--redisplay)))))

(defun ebib-prev-database ()
  "Switch to the preceding database."
  (interactive)
  (ebib--execute-when
    ((database)
     (let ((new-db (ebib--prev-elem ebib--cur-db ebib--databases)))
       (unless new-db
         (setq new-db (-last-item ebib--databases)))
       (setq ebib--cur-db new-db)
       (ebib--redisplay)))))

(defun ebib--extract-urls (string)
  "Extract URLs from STRING.
What counts as a URL is defined by `ebib-url-regexp'.  Return the
URLs as a list of strings.  Parts of the string that are not
recognized as URLs are discarded."
  (let ((start 0)
        (result nil))
    (while (string-match ebib-url-regexp string start)
      (push (match-string 0 string) result)
      (setq start (match-end 0)))
    result))

(defun ebib-browse-url (num)
  "Browse the URL in the standard URL field.
If this field contains more than one URL, ask the user which one
to open.  Alternatively, the user can provide a numeric prefix
argument NUM."
  (interactive "P")
  (ebib--execute-when
    ((entries)
     (let ((urls (ebib-db-get-field-value ebib-url-field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced 'xref)))
       (if urls
           (ebib--call-browser urls num)
         (error "Field `%s' is empty" ebib-url-field))))
    ((default)
     (beep))))

(defun ebib-browse-doi ()
  "Open the DOI in the standard DOI field in a browser.
The stardard DOI field (see user option `ebib-doi-field') may
contain only one DOI.  The DOI is combined with the URL
\"http://dx.doi.org/\" before being sent to the browser."
  (interactive)
  (ebib--execute-when
    ((entries)
     (let ((doi (ebib-db-get-field-value ebib-doi-field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced 'xref)))
       (if doi
           (ebib--call-browser (concat "http://dx.doi.org/" doi))
         (error "No DOI found in field `%s'" ebib-doi-field))))
    ((default)
     (beep))))

(defun ebib--call-browser (string &optional n)
  "Call a browser with the URL in STRING.
STRING is a string containing one or more URLs.  If there is more
than one, N specifies which one to pass to the browser.  If N
is nil, the user is asked which URL to open."
  (let ((urls (ebib--extract-urls string)))
    (cond
     ((null (cdr urls))                 ; there's only one URL
      (setq n 1))
     ((not (integerp n)) ; the user didn't provide a numeric prefix argument
      (setq n (string-to-number (read-string (format "Select URL to open [1-%d]: " (length urls)))))))
    (if (or (< n 1)             ; if the user provide a number out of range
            (> n (length urls)))
        (setq n 1))
    (let ((url (nth (1- n) urls)))
      (when url
        (if (string-match "\\\\url{\\(.*?\\)}" url) ; see if the url is contained in \url{...}
            (setq url (match-string 1 url)))
        (if ebib-browser-command
            (progn
              (message "Executing `%s %s'" ebib-browser-command url)
              (start-process "Ebib--browser" nil ebib-browser-command url))
          (message "Opening `%s'" url)
          (browse-url url))))))

(defun ebib-view-file (num)
  "View a file in the standard file field.
The standard file field (see option `ebib-file-field') may
contain more than one filename.  In that case, a numeric prefix
argument NUM can be used to specify which file to choose."
  (interactive "P")
  (ebib--execute-when
    ((entries)
     (let ((filename (ebib-db-get-field-value ebib-file-field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced 'xref)))
       (if filename
           (ebib--call-file-viewer filename num)
         (ebib--call-file-viewer (concat (ebib--cur-entry-key) ".pdf") nil))))
    ((default)
     (beep))))

(defun ebib--call-file-viewer (filename &optional n)
  "Open FILENAME with an external viewer.
FILENAME can also be a string of filenames separated by
`ebib-filename-separator', in which case the Nth file is
opened.  If N is NIL, the user is asked to enter a number."
  (let ((files (split-string filename (regexp-quote ebib-filename-separator) t)))
    (cond
     ((null (cdr files))                ; there's only one file
      (setq n 1))
     ((not (integerp n))  ; the user did not pass a numeric prefix argument
      (setq n (string-to-number (read-string (format "Select file to open [1-%d]: " (length files)))))))
    (if (or (< n 1)    ; if the user provided a number that is out of range
            (> n (length files)))
        (setq n 1))
    (let* ((file (nth (1- n) files))
           (file-full-path
            (or (locate-file file ebib-file-search-dirs)
                (locate-file (file-name-nondirectory file) ebib-file-search-dirs)
                (expand-file-name file))))
      (if (file-exists-p file-full-path)
          (let ((ext (file-name-extension file-full-path)))
            (ebib--ifstring (viewer (cdr (assoc ext ebib-file-associations)))
                (progn
                  (message "Executing `%s %s'" viewer file-full-path)
                  (start-process (concat "ebib " ext " viewer process") nil viewer file-full-path))
              (message "Opening `%s'" file-full-path)
              (ebib-lower)
              (find-file file-full-path)))
        (error "File not found: `%s'" file)))))

(defun ebib-set-dialect (dialect)
  "Set the BibTeX dialect of the current database.
Possible values for DIALECT are those in `bibtex-dialect-list' or
NIL, in which case the dialect is unset (and the default dialect
is used)."
  (interactive (list (intern (completing-read "Dialect: " (append (mapcar #'symbol-name bibtex-dialect-list) (list "nil")) nil t))))
  (unless (or (not dialect)
              (memq dialect bibtex-dialect-list))
    (error "Not a valid BibTeX dialect: %s" dialect))
  (ebib--execute-when
    ((database)
     (ebib-db-set-dialect dialect ebib--cur-db)
     (let ((lvars (ebib-db-get-local-vars ebib--cur-db)))
       (setq lvars (if dialect
                       (ebib--local-vars-add-dialect lvars dialect 'overwrite)
                     (ebib--local-vars-delete-dialect lvars)))
       (ebib-db-set-local-vars lvars ebib--cur-db))
     (ebib--set-modified t ebib--cur-db)
     (ebib--redisplay))
    ((default)
     (beep))))

(defun ebib-show-log ()
  "Display the contents of the log buffer."
  (interactive)
  (ebib--pop-to-buffer (ebib--buffer 'log)))

(defun ebib--create-citation-command (format-string &optional key)
  "Create a citation command using FORMAT-STRING.
If FORMAT-STRING contains a %K directive, it is replaced with
KEY.  Furthermore, FORMAT-STRING may contain any number of %A
directives for additional arguments to the citation.  The user is
asked to supply a string for each of them, which may be empty.

Each %A directive may be wrapped in a %<...%> pair, containing
optional material both before and after %A.  If the user supplies
an empty string for such an argument, the optional material
surrounding it is not included in the citation command."
  (when (and (string-match "%K" format-string)
             key)
    (setq format-string (replace-match key t t format-string)))
  (let (arg-prompt)
    (cl-loop for n = 1 then (1+ n)
             until (null (string-match "%<\\(.*?\\)%A\\(.*?\\)%>\\|%A\\|%D" format-string)) do
             (setq arg-prompt
                   (if (string= (match-string 0 format-string) "%D")
                       "Description"
                     "Argument"))
             (setq format-string
                   (replace-match (ebib--ifstring (argument
                                                   (save-match-data
                                                     (read-from-minibuffer (format "%s%s%s: "
                                                                                   arg-prompt
                                                                                   (if (string= arg-prompt "Argument")
                                                                                       (format " %s" n)
                                                                                     "")
                                                                                   (if key
                                                                                       (concat " for " key)
                                                                                     "")))))
                                      (concat "\\1" argument "\\2")
                                    "")
                                  t nil format-string))
             finally return format-string)))

(defun ebib--split-citation-string (format-string)
  "Split up FORMAT-STRING.
The return value is a list of (BEFORE REPEATER SEPARATOR AFTER),
where BEFORE is the part before the repeating part of
FORMAT-STRING, REPEATER the repeating part, SEPARATOR the string
to be placed between each instance of REPEATER and AFTER the part
after the last instance of REPEATER."
  (let (before repeater separator after)
    ;; first check if the format string has a repeater and if so, separate each component
    (cond
     ((string-match "\\(.*?\\)%(\\(.*\\)%\\(.*?\\))\\(.*\\)" format-string)
      (setq before (match-string 1 format-string)
            repeater (match-string 2 format-string)
            separator (match-string 3 format-string)
            after (match-string 4 format-string)))
     ((string-match "\\(.*?\\)\\(%K\\)\\(.*\\)" format-string)
      (setq before (match-string 1 format-string)
            repeater (match-string 2 format-string)
            after (match-string 3 format-string))))
    (cl-values before repeater separator after)))

(defun ebib-push-bibtex-key ()
  "Push the current entry to a LaTeX buffer.
The user is prompted for the buffer to push the entry into."
  (interactive)
  (ebib--execute-when
    ((entries)
     (let ((buffer (read-buffer (if (ebib-db-marked-entries-p ebib--cur-db)
                                    "Push marked entries to buffer: "
                                  "Push entry to buffer: ")
                                ebib--push-buffer t)))
       (when buffer
         (setq ebib--push-buffer buffer)
         (let* ((format-list (or (cadr (assq (buffer-local-value 'major-mode (get-buffer buffer)) ebib-citation-commands))
                                 (cadr (assq 'any ebib-citation-commands))))
                (citation-command
                 ;; Read a citation command from the user:
                 (ebib--ifstring (format-string (cadr (assoc
                                                       (completing-read "Command to use: " format-list nil nil nil 'ebib--cite-command-history)
                                                       format-list)))
                     (cl-multiple-value-bind (before repeater separator after) (ebib--split-citation-string format-string)
                       (cond
                        ((ebib-db-marked-entries-p ebib--cur-db) ; if there are marked entries
                         (concat (ebib--create-citation-command before)
                                 (mapconcat (lambda (key) ; then deal with the entries one by one
                                              (ebib--create-citation-command repeater key))
                                            (ebib-db-list-marked-entries ebib--cur-db 'sort)
                                            (if separator separator (read-from-minibuffer "Separator: ")))
                                 (ebib--create-citation-command after)))
                        (t        ; otherwise just take the current entry
                         (ebib--create-citation-command (concat before repeater after) (ebib--cur-entry-key)))))
                   ;; If the user doesn't provide a command, we just insert the entry key or keys:
                   (if (ebib-db-marked-entries-p ebib--cur-db)
                       (mapconcat (lambda (key)
                                    key)
                                  (ebib-db-list-marked-entries ebib--cur-db 'sort)
                                  (read-from-minibuffer "Separator: "))
                     (ebib--cur-entry-key)))))
           (when citation-command
             (with-current-buffer buffer
               (insert citation-command))
             (message "Pushed entries to buffer %s" buffer))))))
    ((default)
     (beep))))

(defun ebib-index-help ()
  "Show the info node of Ebib's index buffer."
  (interactive)
  (setq ebib--info-flag t)
  (ebib-lower)
  (info "(ebib) The Index Buffer"))

(defun ebib-info ()
  "Show Ebib's info node."
  (interactive)
  (setq ebib--info-flag t)
  (ebib-lower)
  (info "(ebib)"))

;; TODO These keyword functions use functions from ebib.el, so we keep them here.

;; The filters keymap
(eval-and-compile
  (define-prefix-command 'ebib-keywords-map)
  (suppress-keymap 'ebib-keywords-map 'no-digits)
  (define-key ebib-keywords-map "a" #'ebib-keywords-add)
  (define-key ebib-keywords-map "s" #'ebib-keywords-save-from-entry)
  (define-key ebib-keywords-map "S" #'ebib-keywords-save-cur-db))

(defun ebib--completing-read-keywords (collection)
  "Read keywords with completion from COLLECTION.
Return the keywords entered as a list.  Any keywords not in
COLLECTION are added to the current database's keywords list.  If
no keywords are entered, the return value is nil."
  (let ((keywords (cl-loop for keyword = (completing-read (format "Add keyword (ENTER to finish) [%s]: " (mapconcat #'identity keywords " ")) collection nil nil nil 'ebib-keyword-history)
                           until (string= keyword "")
                           collecting keyword into keywords
                           finally return keywords)))
    ;; Save any new keywords the user may have added. Note that `mapc'
    ;; returns its SEQUENCE argument, which is exactly what we want here.
    (mapc (lambda (keyword) (unless (member keyword collection)
                              (ebib--keywords-add-keyword keyword ebib--cur-db)))
          keywords)))

(defun ebib-keywords-add ()
  "Add keywords to the current entry."
  (interactive)
  (cl-flet ((add-keywords (entry-key keywords)
                          (let* ((conts (ebib-db-get-field-value "keywords" entry-key ebib--cur-db 'noerror 'unbraced))
                                 (new-conts (if conts
                                                (concat conts ebib-keywords-separator keywords)
                                              keywords)))
                            (ebib-db-set-field-value "keywords"
                                                     (if ebib-keywords-field-keep-sorted
                                                         (ebib--keywords-sort new-conts)
                                                       new-conts)
                                                     entry-key ebib--cur-db 'overwrite))))
    (let* ((minibuffer-local-completion-map (make-composed-keymap '(keymap (32)) minibuffer-local-completion-map))
           (collection (ebib--keywords-for-database ebib--cur-db))
           (keywords (ebib--completing-read-keywords collection)))
      (when keywords
        (ebib--execute-when
          ((marked-entries)
           (when (y-or-n-p "Add keywords to all marked entries? ")
             (mapc (lambda (entry)
                     (add-keywords entry (mapconcat #'identity keywords ebib-keywords-separator)))
                   (ebib-db-list-marked-entries ebib--cur-db))
             (message "Keywords added to marked entries.")
             (ebib--set-modified t)))
          ((entries)
           (add-keywords (ebib--cur-entry-key) (mapconcat #'identity keywords ebib-keywords-separator))
           (ebib--set-modified t)))
        (ebib--redisplay)))))

(defun ebib-keywords-save-from-entry ()
  "Save the keywords in the current entry.
Check the keywords of the current entry and save those that have
not been saved yet."
  (interactive)
  (let* ((keywords (ebib-db-get-field-value "keywords" (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced))
         (new-keywords (ebib--keywords-remove-existing (ebib--keywords-to-list keywords) ebib--cur-db)))
    (mapc (lambda (k)
            (ebib--keywords-add-keyword k ebib--cur-db))
          new-keywords))
  (ebib--redisplay))

(defun ebib-warn-prefix ()
  "Warn that the prefix key is no longer valid."
  (interactive)
  (error "Prefix key `;' is no longer necessary. See the Ebib manual, section \"Marking Entries\"."))

;; TODO These filter functions use functions defined in ebib.el, so we keep them here.

(defun ebib-filters-logical-and (not)
  "Filter the current database.
If the current database is filtered already, perform a logical
AND on the entries.  A negative prefix argument adds a logical
NOT to the filter."
  (interactive "p")
  (ebib--execute-when
    ((entries)
     (ebib--filters-create-filter 'and not)
     (ebib--redisplay))
    ((default)
     (beep))))

(defun ebib-filters-logical-or (not)
  "Filter the current database.
If the current database is filtered already, perform a logical OR
on the entries.  A negative prefix argument adds a logical NOT to
the filter."
  (interactive "p")
  (ebib--execute-when
    ((entries)
     (ebib--filters-create-filter 'or not)
     (ebib--redisplay))
    ((default)
     (beep))))

(defun ebib-filters-logical-not ()
  "Negate the current filter."
  (interactive)
  (ebib--execute-when
    ((filtered-db)
     (ebib-db-set-filter (if (eq (car (ebib-db-get-filter ebib--cur-db)) 'not)
                             (cadr (ebib-db-get-filter ebib--cur-db))
                           `(not ,(ebib-db-get-filter ebib--cur-db)))
                         ebib--cur-db)
     (ebib--redisplay))
    ((default)
     (beep))))

(defun ebib--filters-create-filter (bool not)
  "Create a filter interactively and store it in the current database.
BOOL is the operator to be used, either `and' or `or'.  If NOT<0,
a logical `not' is applied to the selection."
  (let ((field (completing-read (format "Filter: %s<field> contains <search string>%s. Enter field: "
                                        (if (< not 0) "not " "")
                                        (if (< not 0) "" ""))
                                (append (list "any" "=type=") (-union (ebib--list-fields-uniquely (ebib--get-dialect)) ebib-extra-fields))
                                nil nil nil 'ebib--field-history)))
    (let* ((prompt (format "Filter: %s%s contains <search string>%s. Enter %s: "
                           (if (< not 0) "not " "")
                           field
                           (if (< not 0) "" "")
                           (if (string= field "=type=") "entry type" "regexp")))
           (regexp (cond
                    ((string= field "=type=")
                     (completing-read prompt (ebib--list-entry-types (ebib--get-dialect) t) nil t nil 'ebib--filters-history))
                    ((cl-equalp field "keywords")
                     (completing-read prompt (ebib--keywords-for-database ebib--cur-db)  nil nil nil 'ebib--keywords-history))
                    (t
                     (read-string prompt nil 'ebib--filters-history)))))
      (ebib--execute-when
        ((filtered-db)
         (ebib-db-set-filter `(,bool ,(ebib-db-get-filter ebib--cur-db)
                                     ,(if (>= not 0)
                                          `(contains ,field ,regexp)
                                        `(not (contains ,field ,regexp))))
                             ebib--cur-db))
        ((real-db)
         (ebib-db-set-filter (if (>= not 0)
                                 `(contains ,field ,regexp)
                               `(not (contains ,field ,regexp)))
                             ebib--cur-db))))))

(defun ebib-filters-reapply-filter ()
  "Reapply the current filter."
  (interactive)
  (ebib--execute-when
    ((filtered-db)
     (ebib--redisplay))
    ((default)
     (error "No filter is active"))))

(defun ebib-filters-reapply-last-filter ()
  "Reapply the last used filter."
  (interactive)
  (ebib-db-set-filter ebib--filters-last-filter ebib--cur-db)
  (ebib--redisplay)
  (message "Reapplied last filter"))

(defun ebib-filters-cancel-filter ()
  "Cancel the current filter."
  (interactive)
  (ebib--execute-when
    ((filtered-db)
     (setq ebib--filters-last-filter (ebib-db-get-filter ebib--cur-db))
     (ebib-db-set-filter nil ebib--cur-db)
     (ebib--redisplay)
     (message "Filter cancelled"))
    ((default)
     (beep))))

(defun ebib-filters-apply-filter ()
  "Select a filter and apply it to the current database."
  (interactive)
  (ebib--execute-when
    ((real-db)
     (let ((filter (ebib--filters-select-filter "Apply filter: ")))
       (when filter
         (ebib-db-set-filter (cadr filter) ebib--cur-db)
         (ebib--redisplay))))
    ((filtered-db)
     (error "A stored filter can only be applied to a real database"))))

;;;;;;;;;;;;;;;;
;; entry-mode ;;
;;;;;;;;;;;;;;;;

(defvar ebib-entry-mode-map
  (let ((map (make-keymap)))
    (suppress-keymap map 'no-digits)
    (define-key map [up] 'ebib-prev-field)
    (define-key map [down] 'ebib-next-field)
    (define-key map [prior] 'ebib-goto-prev-set)
    (define-key map [next] 'ebib-goto-next-set)
    (define-key map [home] 'ebib-goto-first-field)
    (define-key map [end] 'ebib-goto-last-field)
    (define-key map [return] 'ebib-edit-field)
    (define-key map " " 'ebib-goto-next-set)
    (define-key map "a" 'ebib-add-field)
    (define-key map "b" 'ebib-goto-prev-set)
    (define-key map "c" 'ebib-copy-field-contents)
    (define-key map "d" 'ebib-delete-field-contents)
    (define-key map "e" 'ebib-edit-field)
    (define-key map "f" 'ebib-view-file-in-field)
    (define-key map "g" 'ebib-goto-first-field)
    (define-key map "G" 'ebib-goto-last-field)
    (define-key map "h" 'ebib-entry-help)
    (define-key map "j" 'ebib-next-field)
    (define-key map "k" 'ebib-prev-field)
    (define-key map "m" 'ebib-edit-multiline-field)
    (define-key map [(control n)] 'ebib-next-field)
    (define-key map [(meta n)] 'ebib-goto-prev-set)
    (define-key map [(control p)] 'ebib-prev-field)
    (define-key map [(meta p)] 'ebib-goto-next-set)
    (define-key map "q" 'ebib-quit-entry-buffer)
    (define-key map "r" 'ebib-toggle-raw)
    (define-key map "s" 'ebib-insert-abbreviation)
    (define-key map "u" 'ebib-browse-url-in-field)
    (define-key map "v" 'ebib-view-field-as-help)
    (define-key map "x" 'ebib-cut-field-contents)
    (define-key map "y" 'ebib-yank-field-contents)
    (define-key map "\C-xb" 'ebib-quit-entry-buffer)
    (define-key map "\C-xk" 'ebib-quit-entry-buffer)
    map)
  "Keymap for the Ebib entry buffer.")

(define-derived-mode ebib-entry-mode
  fundamental-mode "Ebib-entry"
  "Major mode for the Ebib entry buffer."
  (setq buffer-read-only t)
  (if ebib-hide-cursor
      (setq cursor-type nil))
  (setq truncate-lines t))

(defun ebib-quit-entry-buffer ()
  "Quit editing the entry.
If the key of the current entry matches the pattern
<new-entry%d>, a new key is automatically generated using
`bibtex-generate-autokey'."
  (interactive)
  (cond
   ((and ebib-popup-entry-window
         (eq ebib-layout 'index-only))
    (delete-window))
   ((eq ebib-layout 'index-only)
    (switch-to-buffer nil t)))
  (ebib--pop-to-buffer (ebib--buffer 'index))
  (goto-char (overlay-start ebib--index-overlay))
  (delete-overlay ebib--fields-overlay)
  ;; (select-window (get-buffer-window (ebib--buffer 'index)))
  (if (string-match "<new-entry[0-9]+>" (ebib--cur-entry-key))
      (ebib-generate-autokey)))

(defun ebib--current-field ()
  "Return the current field name.
The current field is simply the field that point is on.  If point
is on an empty line, return nil.  This function leaves point at
the beginning of the current line."
  (with-current-ebib-buffer 'entry
    (beginning-of-line)
    (if (bobp)                   ; If we're at the beginning of the buffer,
        "=type="                 ; the current field is `=type='.
      (unless (eolp)             ; We're not on an empty line
        (save-excursion
          (let ((beg (point))
                (end (progn
                       (skip-chars-forward "^[:space:]" (line-end-position))
                       (point))))
            (buffer-substring-no-properties beg end)))))))

(defun ebib-prev-field ()
  "Move to the previous field."
  (interactive)
  (if (= (forward-line -1) -1)
      (beep) ; We're at the first field already
    (while (eolp) ; If we're at an empty line,
      (forward-line -1)) ; move up until we're not.
    (ebib--set-fields-overlay)))

(defun ebib-next-field (&optional pfx)
  "Move to the next field.
The prefix argument PFX is used to determine whether the command
was called interactively."
  (interactive "p")
  (forward-line)
  (when (eobp)                     ; If we ended up at the empty line below
    (if pfx                        ; the last field, beep and adjust.
        (beep))
    (forward-line -1))
  (while (eolp)                         ; If we're at an empty line,
    (forward-line))                     ; move down until we're not.
  (ebib--set-fields-overlay))

(defun ebib-goto-first-field ()
  "Move to the first field."
  (interactive)
  (goto-char (point-min))
  (ebib--set-fields-overlay))

(defun ebib-goto-last-field ()
  "Move to the last field."
  (interactive)
  (goto-char (point-max))
  (while (eolp)                 ; move up as long as we're at an empty line
    (forward-line -1))
  (ebib--set-fields-overlay))

(defun ebib-goto-next-set ()
  "Move to the next set of fields."
  (interactive)
  (beginning-of-line)
  (let ((p (point)))
    (while (not (eolp))                 ; Search for the first empty line.
      (forward-line))
    (if (= (forward-line) 0)          ; Then try and move to the next line.
        (ebib--set-fields-overlay)
      (goto-char p))))             ; Otherwise go back to where we started.

(defun ebib-goto-prev-set ()
  "Move to the previous set of fields."
  (interactive)
  (beginning-of-line)
  (if (bobp)                  ; If we're at the =type= field, we don't move
      (beep)
    (while (not (eolp))          ; Otherwise just find the first empty line
      (forward-line -1))
    (forward-line -1)                   ; and move beyond it.
    (ebib--set-fields-overlay)))

(defun ebib-add-field (field)
  "Add FIELD to the current entry."
  (interactive "sField: ")
  ;; We store the field with a `nil' value and let the user edit it later.
  (let ((type (ebib-db-get-field-value "=type=" (ebib--cur-entry-key) ebib--cur-db)))
    (if (or (member-ignore-case field (ebib--list-fields type 'all (ebib--get-dialect)))
            (not (ebib-db-set-field-value field nil (ebib--cur-entry-key) ebib--cur-db 'noerror)))
        (message "Field `%s' already exists in entry `%s'%s" field (ebib--cur-entry-key)
                 (if (member-ignore-case field ebib-hidden-fields)
                     " but is hidden"
                   ""))
      (ebib--fill-entry-buffer)
      (re-search-forward (concat "^" field))
      (ebib--set-fields-overlay)
      (ebib--set-modified t)
      (ebib-edit-field))))

(defun ebib--edit-entry-type ()
  "Edit the entry type."
  (ebib--ifstring (new-type (completing-read "type: " (ebib--list-entry-types (ebib--get-dialect)) nil t))
      (progn
        (ebib-db-set-field-value "=type=" new-type (ebib--cur-entry-key) ebib--cur-db 'overwrite 'unbraced)
        (ebib--fill-entry-buffer)
        (ebib--set-modified t))))

(defun ebib--edit-crossref ()
  "Edit the crossref field."
  (ebib--ifstring (key (completing-read "Key to insert in `crossref': " (ebib-db-list-keys ebib--cur-db) nil t nil 'ebib--key-history))
      (progn
        (ebib-db-set-field-value "crossref" key (ebib--cur-entry-key) ebib--cur-db 'overwrite)
        ;; We now redisplay the entire entry buffer, so that the crossref'ed
        ;; fields show up. This also puts the cursor back on the =type= field,
        ;; though, so we need to readjust.
        (ebib--fill-entry-buffer)
        (re-search-forward "^crossref")
        (ebib--set-fields-overlay)
        (ebib--set-modified t))))

(defun ebib--edit-keywords-field ()
  "Edit the keywords field."
  ;; We shadow the binding of `minibuffer-local-completion-map' so that we
  ;; can unbind <SPC>, since keywords may contain spaces.
  (let ((minibuffer-local-completion-map (make-composed-keymap '(keymap (32)) minibuffer-local-completion-map))
        (collection (ebib--keywords-for-database ebib--cur-db)))
    (cl-loop for keyword = (completing-read "Add a new keyword (ENTER to finish): " collection nil nil nil 'ebib--keywords-history)
             until (string= keyword "")
             do (let* ((conts (ebib-db-get-field-value "keywords" (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced))
                       (new-conts (if conts
                                      (concat conts ebib-keywords-separator keyword)
                                    keyword)))
                  (ebib-db-set-field-value "keywords"
                                           (if ebib-keywords-field-keep-sorted
                                               (ebib--keywords-sort new-conts)
                                             new-conts)
                                           (ebib--cur-entry-key)
                                           ebib--cur-db
                                           'overwrite)
                  (ebib--redisplay-current-field)
                  (unless (member keyword collection)
                    (ebib--keywords-add-keyword keyword ebib--cur-db)))
             finally return (ebib--set-modified t))))

(defun ebib--edit-file-field ()
  "Edit the `ebib-file-field'.
Filenames are added to the standard file field separated by
`ebib-filename-separator'.  The first directory in
`ebib-file-search-dirs' is used as the start directory."
  (let ((start-dir (file-name-as-directory (car ebib-file-search-dirs))))
    (cl-loop for file = (read-file-name "Add file (ENTER to finish): " start-dir nil 'confirm-after-completion)
             until (or (string= file "")
                       (string= file start-dir))
             do (let* ((short-file (ebib--file-relative-name (expand-file-name file)))
                       (conts (ebib-db-get-field-value ebib-file-field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced))
                       (new-conts (if conts
                                      (concat conts ebib-filename-separator short-file)
                                    short-file)))
                  (ebib-db-set-field-value ebib-file-field new-conts (ebib--cur-entry-key) ebib--cur-db 'overwrite)
                  (ebib--redisplay-current-field))
             finally return (ebib--set-modified t))))

(defun ebib--file-relative-name (file)
  "Return a name for FILE relative to `ebib-file-search-dirs'.
If FILE is not in (a subdirectory of) one of the directories in
`ebib-file-search-dirs', return FILE."
  ;; We first create a list of names relative to each dir in
  ;; ebib-file-search-dirs, discarding those that start with `..'
  (let* ((names (delq nil (mapcar (lambda (dir)
                                    (let ((rel-name (file-relative-name file dir)))
                                      (unless (string-prefix-p ".." rel-name)
                                        rel-name)))
                                  ebib-file-search-dirs)))
         ;; Then we take the shortest one...
         (name (car (sort names (lambda (x y)
                                  (< (length x) (length y)))))))
    ;; ...and return it, or the filename itself if it couldn't be
    ;; relativized.
    (or name file)))

(defun ebib--edit-normal-field ()
  "Edit a field that does not require special treatment."
  (let* ((cur-field (ebib--current-field))
         (init-contents (ebib-db-get-field-value cur-field (ebib--cur-entry-key) ebib--cur-db 'noerror))
         (braced? nil))
    (if (ebib--multiline-p init-contents)
        (ebib-edit-multiline-field)     ; this always returns nil
      (when init-contents
        (setq braced? (ebib-db-unbraced-p init-contents))
        (setq init-contents (ebib-db-unbrace init-contents)))
      (ebib--ifstring (new-contents (read-string (format "%s: " cur-field)
                                                 (if init-contents
                                                     (cons init-contents 0))))
          (ebib-db-set-field-value cur-field new-contents (ebib--cur-entry-key) ebib--cur-db 'overwrite braced?)
        (ebib-db-remove-field-value cur-field (ebib--cur-entry-key) ebib--cur-db))
      (ebib--redisplay-current-field)
      (ebib--set-modified t))))

(defun ebib-edit-field (&optional pfx)
  "Edit a field of a BibTeX entry.
Most fields are edited directly using the minibuffer, but a few
are handled specially: the `type' and `crossref' fields offer
completion, the `annote' field is edited as a multiline field,
the `keywords' field adds keywords one by one, also allowing
completion, and the field in `ebib-file-field' uses filename
completion and shortens filenames if they are in (a subdirectory
of) one of the directories in `ebib-file-search-dirs'.

With a prefix argument PFX, the `keywords' field and the field in
`ebib-file-field' can be edited directly.  For other fields, the
prefix argument has no meaning."
  (interactive "p")
  (let* ((field (ebib--current-field))
         ;; we save the result of editing the field, so we can move to the
         ;; next field if necessary.
         (result (cond
                  ((string= field "=type=") (ebib--edit-entry-type))
                  ((cl-equalp field "crossref") (ebib--edit-crossref))
                  ((and (cl-equalp field "keywords")
                        (= 1 pfx))
                   (ebib--edit-keywords-field))
                  ((and (cl-equalp field ebib-file-field)
                        (= 1 pfx))
                   (ebib--edit-file-field))
                  ((member-ignore-case field '("annote" "annotation"))
                   ;; a multiline edit differs from the other ones, because
                   ;; the edit isn't done when `ebib-edit-multiline-field'
                   ;; returns. this means we cannot move to the next field.
                   ;; (in fact, the entry buffer isn't even displayed at
                   ;; this point.) for this reason, we return `nil', so
                   ;; `ebib-next-field' below isn't called.
                   (ebib-edit-multiline-field)
                   nil)
                  (t (ebib--edit-normal-field)))))
    ;; move to the next field, but only if if the edit wasn't aborted and
    ;; the function was called interactively (hence pfx):
    (if (and result pfx)
        (ebib-next-field))))

(defun ebib-browse-url-in-field (num)
  "Browse a URL in the current field.
If the field contains multiple URLs (as defined by
`ebib-url-regexp'), the user is asked which one to open.
Altertanively, a numeric prefix argument NUM can be passed."
  (interactive "P")
  (let* ((field (ebib--current-field))
         (urls (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced)))
    (if urls
        (ebib--call-browser urls num)
      (error "Field `%s' is empty" field))))

(defun ebib-view-file-in-field (num)
  "View a file in the current field.
The field may contain multiple filenames, in which case the
prefix argument NUM can be used to specify which file is to be
viewed."
  (interactive "P")
  (let* ((field (ebib--current-field))
         (files (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced)))
    (if files
        (ebib--call-file-viewer files num)
      (ebib--call-file-viewer (concat (ebib--cur-entry-key) ".pdf")))))

(defun ebib-copy-field-contents ()
  "Copy the contents of the current field to the kill ring."
  (interactive)
  (let ((field (ebib--current-field)))
    (unless (or (not field)
                (string= field "=type="))
      (let ((contents (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced 'xref)))
        (when (stringp contents)
          (kill-new contents)
          (message "Field contents copied."))))))

(defun ebib-cut-field-contents ()
  "Kill the contents of the current field.  The killed text is put in the kill ring."
  (interactive)
  (let ((field (ebib--current-field)))
    (unless (or (not field)
                (string= field "=type="))
      (let ((contents (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced)))
        (when (stringp contents)
          (ebib-db-remove-field-value field (ebib--cur-entry-key) ebib--cur-db)
          (kill-new contents)
          (ebib--redisplay-current-field)
          (ebib--set-modified t)
          (message "Field contents killed."))))))

(defun ebib-yank-field-contents (arg)
  "Insert the last killed text into the current field.
If the current field already has a contents, nothing is inserted,
unless the previous command was also `ebib--yank-field-contents',
then the field contents is replaced with the previous yank.

Prefix argument ARG functions as with \\[yank] / \\[yank-pop]."
  (interactive "P")
  (let ((field (ebib--current-field)))
    (if (or (member-ignore-case field '("=type=" "crossref")) ; We cannot yank into the `=type=' or `crossref' fields.
            (unless (eq last-command 'ebib--yank-field-contents) ; Nor into a field already filled.
              (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror)))
        (progn
          (setq this-command t)
          (beep))
      (let ((new-contents (current-kill (cond
                                         ((listp arg)
                                          (if (eq last-command 'ebib--yank-field-contents) 1 0))
                                         ((eq arg '-) -2)
                                         (t (1- arg))))))
        (when new-contents
          (ebib-db-set-field-value field new-contents (ebib--cur-entry-key) ebib--cur-db 'overwrite)
          (ebib--redisplay-current-field)
          (ebib--set-modified t))))))

(defun ebib-delete-field-contents ()
  "Delete the contents of the current field.
The deleted text is not put in the kill ring."
  (interactive)
  (let ((field (ebib--current-field)))
    (if (string= field "=type=")
        (beep)
      (when (y-or-n-p "Delete field contents? ")
        (ebib-db-remove-field-value field (ebib--cur-entry-key) ebib--cur-db)
        (ebib--redisplay-current-field)
        (ebib--set-modified t)
        (message "Field contents deleted.")))))

(defun ebib-toggle-raw ()
  "Toggle the \"special\" status of the current field contents."
  (interactive)
  (let ((field (ebib--current-field)))
    (unless (member-ignore-case field '("=type=" "crossref" "keywords"))
      (let ((contents (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror)))
        (if (ebib--multiline-p contents) ; multiline fields cannot be special
            (beep)
          (unless contents              ; If there is no value,
            (ebib-edit-field) ; the user can enter one, which we must then store unbraced.
            (setq contents (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror)))
          (when contents ; We must check to make sure the user entered some value.
            (ebib-db-set-field-value field contents (ebib--cur-entry-key) ebib--cur-db 'overwrite (not (ebib-db-unbraced-p contents)))
            (ebib--redisplay-current-field)
            (ebib--set-modified t)))))))

(defun ebib-edit-multiline-field ()
  "Edit the current field in multiline-mode."
  (interactive)
  (let ((field (ebib--current-field)))
    (unless (member-ignore-case field '("=type=" "crossref"))
      (let ((text (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror)))
        (if (ebib-db-unbraced-p text) ; unbraced fields cannot be multiline
            (beep)
          (ebib--multiline-edit (list 'field (ebib-db-get-filename ebib--cur-db) (ebib--cur-entry-key) field) (ebib-db-unbrace text)))))))

(defun ebib-insert-abbreviation ()
  "Insert an abbreviation from the ones defined in the database."
  (interactive)
  (let ((field (ebib--current-field)))
    (if (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror)
        (beep)
      (let ((strings (ebib-db-list-strings ebib--cur-db)))
        (when strings
          (unwind-protect
              (progn
                (other-window 1)
                (let ((string (completing-read "Abbreviation to insert: " strings nil t)))
                  (when string
                    (ebib-db-set-field-value field string (ebib--cur-entry-key) ebib--cur-db 'overwrite 'unbraced)
                    (ebib--set-modified t))))
            (other-window 1)
            ;; we can't do this earlier, because we would be writing to the index buffer...
            (ebib--redisplay-current-field)
            (ebib-next-field)))))))

(defun ebib-view-field-as-help ()
  "Show the contents of the current field in a *Help* window."
  (interactive)
  (let ((help-window-select t)                          ; make sure the help window is selected
        (field (ebib--current-field)))
    (with-help-window (help-buffer)
      (princ (propertize (format "%s" field) 'face '(:weight bold)))
      (princ "\n\n")
      (let ((contents (ebib-db-get-field-value field (ebib--cur-entry-key) ebib--cur-db 'noerror 'unbraced)))
        (if contents
            (princ contents)
          (princ "[Empty field]"))))))

(defun ebib-entry-help ()
  "Show the info node for Ebib's entry buffer."
  (interactive)
  (setq ebib--info-flag t)
  (ebib-lower)
  (info "(ebib) The Entry Buffer"))

;;;;;;;;;;;;;;;;;;
;; strings-mode ;;
;;;;;;;;;;;;;;;;;;

(defvar ebib-strings-mode-map
  (let ((map (make-keymap)))
    (suppress-keymap map 'no-digits)
    (define-key map [up] 'ebib-prev-string)
    (define-key map [down] 'ebib-next-string)
    (define-key map [prior] 'ebib-strings-page-up)
    (define-key map [next] 'ebib-strings-page-down)
    (define-key map [home] 'ebib-goto-first-string)
    (define-key map [end] 'ebib-goto-last-string)
    (define-key map " " 'ebib-strings-page-down)
    (define-key map "a" 'ebib-add-string)
    (define-key map "b" 'ebib-strings-page-up)
    (define-key map "c" 'ebib-copy-string-contents)
    (define-key map "d" 'ebib-delete-string)
    (define-key map "e" 'ebib-edit-string)
    (define-key map "g" 'ebib-goto-first-string)
    (define-key map "G" 'ebib-goto-last-string)
    (define-key map "h" 'ebib-strings-help)
    (define-key map "j" 'ebib-next-string)
    (define-key map "k" 'ebib-prev-string)
    (define-key map [(control n)] 'ebib-next-string)
    (define-key map [(meta n)] 'ebib-strings-page-down)
    (define-key map [(control p)] 'ebib-prev-string)
    (define-key map [(meta p)] 'ebib-strings-page-up)
    (define-key map "q" 'ebib-quit-strings-buffer)
    (define-key map "x" 'ebib-export-string)
    (define-key map "X" 'ebib-export-all-strings)
    (define-key map "\C-xb" 'ebib-quit-strings-buffer)
    (define-key map "\C-xk" 'ebib-quit-strings-buffer)
    map)
  "Keymap for the ebib strings buffer.")

(define-derived-mode ebib-strings-mode
  fundamental-mode "Ebib-strings"
  "Major mode for the Ebib strings buffer."
  (setq buffer-read-only t)
  (if ebib-hide-cursor
      (setq cursor-type nil))
  (setq truncate-lines t))

(defun ebib-quit-strings-buffer ()
  "Quit editing the @STRING definitions."
  (interactive)
  (if (and (eq ebib-layout 'index-only)
           ebib-popup-entry-window)
      (delete-window)
    (with-ebib-window-nondedicated
      (switch-to-buffer nil t)))
  (ebib--pop-to-buffer (ebib--buffer 'index)))

(defun ebib--current-string ()
  "Return the currently selected string.
The current string is simply the string that point is on.  If
point is on an empty line (e.g., when there are no @string
definitions), return nil.  This function leaves point at the
beginning of the current line."
  (with-current-ebib-buffer 'strings
    (beginning-of-line)
    (unless (eolp)
      (save-excursion
        (let ((beg (point))
              (end (progn
                     (skip-chars-forward "a-zA-Z" (line-end-position))
                     (point))))
          (buffer-substring-no-properties beg end))))))

(defun ebib-prev-string ()
  "Move to the previous string."
  (interactive)
  (if (= (forward-line -1) -1)
      (beep) ; We're at the first line already.
    (ebib--set-strings-overlay)))

(defun ebib-next-string ()
  "Move to the next string."
  (interactive)
  (forward-line)
  (when (eobp) ; If we've ended up on the empty line after the last string
    (forward-line -1) ; go back and beep
    (beep))
  (ebib--set-strings-overlay))

(defun ebib-goto-first-string ()
  "Move to the first string."
  (interactive)
  (goto-char (point-min))
  (ebib--set-strings-overlay))

(defun ebib-goto-last-string ()
  "Move to the last string."
  (interactive)
  (goto-char (point-max))
  (forward-line -1)
  (ebib--set-strings-overlay))

(defun ebib-strings-page-up ()
  "Move 10 strings up."
  (interactive)
  (forward-line -10)
  (ebib--set-strings-overlay))

(defun ebib-strings-page-down ()
  "Move 10 strings down."
  (interactive)
  (forward-line 10)
  (if (eobp)
      (forward-line -1))
  (ebib--set-strings-overlay))

(defun ebib--fill-strings-buffer ()
  "Fill the strings buffer with the @STRING definitions."
  (with-current-ebib-buffer 'strings
    (with-ebib-buffer-writable
      (erase-buffer)
      (cl-dolist (elem (ebib-db-list-strings ebib--cur-db 'sort))
        (let ((str (ebib-db-get-string elem ebib--cur-db 'noerror 'unbraced)))
          (insert (format "%-18s %s\n" elem
                          (if (ebib--multiline-p str)
                              (concat "+" (ebib--first-line str))
                            (concat " " str)))))))
    (goto-char (point-min))
    (ebib--set-strings-overlay)
    (set-buffer-modified-p nil)))

(defun ebib-edit-string ()
  "Edit the value of an @STRING definition.
When the user enters an empty string, the value is not changed."
  (interactive)
  (let* ((string (ebib--current-string))
         (init-contents (ebib-db-get-string string ebib--cur-db 'noerror 'unbraced)))
    (ebib--ifstring (new-contents (read-string (format "%s: " string)
                                               (if init-contents
                                                   (cons init-contents 0)
                                                 nil)))
        (progn
          (ebib-db-set-string string new-contents ebib--cur-db 'overwrite)
          (ebib--redisplay-current-string)
          (ebib-next-string)
          (ebib--set-modified t))
      (error "@STRING definition cannot be empty"))))

(defun ebib-copy-string-contents ()
  "Copy the contents of the current string to the kill ring."
  (interactive)
  (let ((contents (ebib-db-get-string (ebib--current-string) ebib--cur-db nil 'unbraced)))
    (kill-new contents)
    (message "String value copied.")))

(defun ebib-delete-string ()
  "Delete the current @STRING definition from the database."
  (interactive)
  (let ((string (ebib--current-string)))
    (when (y-or-n-p (format "Delete @STRING definition %s? " string))
      (ebib-db-remove-string string ebib--cur-db)
      (with-ebib-buffer-writable
        (let ((beg (progn
                     (goto-char (overlay-start ebib--strings-overlay))
                     (point))))
          (forward-line 1)
          (delete-region beg (point))))
      (when (eobp)                      ; deleted the last string
        (forward-line -1))
      (ebib--set-strings-overlay)
      (ebib--set-modified t)
      (message "@STRING definition deleted."))))

(defun ebib-add-string ()
  "Create a new @STRING definition."
  (interactive)
  (ebib--ifstring (new-abbr (read-string "New @STRING abbreviation: " nil 'ebib--key-history))
      (progn
        (if (member new-abbr (ebib-db-list-strings ebib--cur-db))
            (error (format "%s already exists" new-abbr)))
        (ebib--ifstring (new-string (read-string (format "Value for %s: " new-abbr)))
            (progn
              (ebib-db-set-string new-abbr new-string ebib--cur-db)
              (ebib--sort-in-buffer (length (ebib-db-list-strings ebib--cur-db)) new-abbr)
              (with-ebib-buffer-writable
                (insert (format "%-19s %s\n" new-abbr new-string)))
              (forward-line -1)
              (ebib--set-strings-overlay)
              (ebib--set-modified t))))))

(defun ebib-export-string (prefix)
  "Export the current @STRING.
The PREFIX argument indicates which database to copy the string
to.  If no prefix argument is present, a filename is asked to
which the string is appended."
  (interactive "P")
  (let ((string (ebib--current-string))
        (num (ebib--prefix prefix)))
    (if num
        (ebib--export-to-db num (format "@STRING definition `%s' copied to database %%d" string)
                            (lambda (db)
                              (ebib-db-set-string string (ebib-db-get-string string ebib--cur-db) db)))
      (ebib--export-to-file (format "Export @STRING definition `%s' to file: " string)
                            (lambda ()
                              (insert (format "\n@string{%s = %s}\n"
                                              string
                                              (ebib-db-get-string string ebib--cur-db))))))))

(defun ebib-export-all-strings (prefix)
  "Export all @STRING definitions.
If a PREFIX argument is given, it is taken as the database to
copy the definitions to.  Without prefix argument, asks for a file
to append them to."
  (interactive "P")
  (when (ebib--current-string) ; There is always a current string, unless there are no strings.
    (let ((num (ebib--prefix prefix)))
      (if num
          (ebib--export-to-db
           num "All @STRING definitions copied to database %d"
           (lambda (db)
             (mapc (lambda (abbr)
                     (ebib-db-set-string abbr (ebib-db-get-string abbr ebib--cur-db) db 'noerror))
                   (ebib-db-list-strings ebib--cur-db))))
        (ebib--export-to-file "Export all @STRING definitions to file: "
                              (lambda ()
                                (insert (format "\n")) ; To keep things tidy.
                                (ebib--format-strings ebib--cur-db)))))))

(defun ebib-strings-help ()
  "Show the info node on Ebib's strings buffer."
  (interactive)
  (setq ebib--info-flag t)
  (ebib-lower)
  (info "(ebib) The Strings Buffer"))

;;;;;;;;;;;;;;;;;;;;
;; multiline edit ;;
;;;;;;;;;;;;;;;;;;;;

(define-minor-mode ebib-multiline-mode
  "Minor mode for Ebib's multiline edit buffer."
  :init-value nil :lighter " Ebib/M" :global nil
  :keymap '(("\C-c|q" . ebib-quit-multiline-buffer-and-save)
            ("\C-c|c" . ebib-cancel-multiline-buffer)
            ("\C-c|s" . ebib-save-from-multiline-buffer)
            ("\C-c|h" . ebib-multiline-help)))

(easy-menu-define ebib-multiline-menu ebib-multiline-mode-map "Ebib multiline menu"
  '("Ebib"
    ["Store Text and Exit" ebib-quit-multiline-buffer-and-save t]
    ["Cancel Edit" ebib-cancel-multiline-buffer t]
    ["Save Text" ebib-save-from-multiline-buffer t]
    ["Help" ebib-multiline-help t]))

(easy-menu-add ebib-multiline-menu ebib-multiline-mode-map)

(defun ebib--multiline-edit (info &optional starttext)
  "Edit a multiline text.
INFO contains information about the text being edited.  It is a
list, the first element of which indicates the type of text,
either `preamble' or `field', and the second element the
database.  If the text being edited is a field value, the third
element is the entry key and the fourth the field name of the
field being edited.

If the preamble or field value pointed to by INFO already has a
multiline edit buffer associated with it, switch to that buffer.
Otherwise, create a new buffer and add it to
`ebib--multiline-buffer-list'.

STARTTEXT is a string that contains the initial text of the
buffer."
  (ebib--pop-to-buffer (or (ebib--get-multiline-buffer info)
                           (ebib--create-multiline-buffer info starttext))))

(defun ebib--get-multiline-buffer (info)
  "Return the multiline edit buffer associated with INFO."
  (car (cl-member info ebib--multiline-buffer-list
                  :test (lambda (elem buffer)
                          (cl-equalp (buffer-local-value 'ebib--multiline-info buffer) elem)))))

(defun ebib--create-multiline-buffer (info starttext)
  "Create a new multiline edit buffer.
INFO indicates what value will be edited and is stored in the
buffer-local value of `ebib--multiline-info'.  STARTTEXT is
inserted as initial text."
  (let* ((name (if (eq (car info) 'preamble)
                   "Preamble"
                 (format "%s-->%s" (cl-third info) (cl-fourth info))))
         (buffer (generate-new-buffer name)))
    (if buffer
        (with-current-buffer buffer
          (funcall ebib-multiline-major-mode)
          (ebib-multiline-mode t)
          (setq ebib--multiline-info info)
          (when starttext
            (insert starttext))
          (set-buffer-modified-p nil)
          (goto-char (point-min))
          (push buffer ebib--multiline-buffer-list)
          buffer)
      (error "Unable to create a new multiline edit buffer"))))

(defun ebib-quit-multiline-buffer-and-save ()
  "Quit the multiline edit buffer, saving the text."
  (interactive)
  (ebib--store-multiline-text (current-buffer))
  (ebib--kill-multiline-edit-buffer (current-buffer))
  (message "Text stored."))

(defun ebib-cancel-multiline-buffer ()
  "Quit the multiline edit buffer and discard the changes.
If the buffer has been modified, ask for confirmation."
  (interactive)
  (catch 'no-cancel
    (when (buffer-modified-p)
      (unless (y-or-n-p "Text has been modified. Abandon changes? ")
        (throw 'no-cancel nil)))
    (ebib--kill-multiline-edit-buffer (current-buffer))
    (message "Text not stored.")))

(defun ebib--kill-multiline-edit-buffer (buffer)
  "Kill multiline edit buffer BUFFER.
Also return focus to the index or entry buffer."
  (with-current-buffer buffer
    (setq ebib--multiline-buffer-list (delq buffer ebib--multiline-buffer-list))
    (let ((info (buffer-local-value 'ebib--multiline-info buffer)))
      ;; put the buffer out of sight
      (if (and (eq ebib-layout 'index-only)
               ebib-popup-entry-window)
          (delete-window)
        (switch-to-buffer nil t))
      ;; return to the index or entry window
      (cond
       ((eq (car info) 'preamble)
        (ebib--pop-to-buffer (ebib--buffer 'index)))
       ((eq (car info) 'field)
        ;; make sure we display the correct entry & field
        (setq ebib--cur-db (ebib--get-db-from-filename (cl-second info)))
        (ebib-db-set-current-entry-key (cl-third info) ebib--cur-db 'first)
        (ebib--redisplay)
        (ebib--pop-to-buffer (ebib--buffer 'entry))
        (re-search-forward (concat "^" (regexp-quote (cl-fourth info))) nil t)
        (ebib--set-fields-overlay))))
    ;; finally, kill the buffer. this calls the functions in
    ;; `kill-buffer-query-functions', so we must mark the buffer unmodified
    ;; in case the user wants to abandon any changes.
    (set-buffer-modified-p nil))
  (kill-buffer buffer))

(defun ebib-save-from-multiline-buffer ()
  "Save the database from within the multiline edit buffer.
The text being edited is stored before saving the database."
  (interactive)
  (ebib--store-multiline-text (current-buffer))
  (ebib--save-database ebib--cur-db)
  (set-buffer-modified-p nil))

(defun ebib--store-multiline-text (buffer)
  "Store the text being edited in multiline edit buffer BUFFER."
  (with-current-buffer buffer
    (let ((text (buffer-substring-no-properties (point-min) (point-max)))
          (type (cl-first ebib--multiline-info))
          (db (ebib--get-db-from-filename (cl-second ebib--multiline-info))))
      (cond
       ((eq type 'preamble)
        (if (string= text "")
            (ebib-db-remove-preamble db)
          (ebib-db-set-preamble text db 'overwrite)))
       ((eq type 'field)
        (let ((key (cl-third ebib--multiline-info))
              (field (cl-fourth ebib--multiline-info)))
          (if (string= text "")
              (ebib-db-remove-field-value field key db)
            (ebib-db-set-field-value field text key db 'overwrite)))))
      (set-buffer-modified-p nil)))
  (ebib--set-modified t))

(defun ebib-multiline-help ()
  "Show the info node on Ebib's multiline edit buffer."
  (interactive)
  (setq ebib--info-flag t)
  (ebib-lower)
  (info "(ebib) The Multiline Edit Buffer"))

;;;;;;;;;;;;;;;;;;;
;; ebib-log-mode ;;
;;;;;;;;;;;;;;;;;;;

(defvar ebib-log-mode-map
  (let ((map (make-keymap)))
    (suppress-keymap map 'no-digits)
    (define-key map " " 'scroll-up)
    (define-key map "b" 'scroll-down)
    (define-key map "q" 'ebib-quit-log-buffer)
    map)
  "Keymap for the ebib log buffer.")

(define-derived-mode ebib-log-mode
  fundamental-mode "Ebib-log"
  "Major mode for the Ebib log buffer."
  (local-set-key "\C-xb" 'ebib-quit-log-buffer)
  (local-set-key "\C-xk" 'ebib-quit-log-buffer))

(defun ebib-quit-log-buffer ()
  "Exit the log buffer."
  (interactive)
  (if (and (eq ebib-layout 'index-only)
           ebib-popup-entry-window)
      (delete-window)
    (with-ebib-window-nondedicated
      (switch-to-buffer nil t)))
  (ebib--pop-to-buffer (ebib--buffer 'index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; functions for non-Ebib buffers ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ebib-import ()
  "Search for BibTeX entries in the current buffer.
The entries are added to the current database (i.e., the database
that was active when Ebib was lowered.  Works on the whole buffer,
or on the region if it is active."
  (interactive)
  (if (not ebib--cur-db)
      (error "No database loaded")
    (save-excursion
      (save-restriction
        (if (use-region-p)
            (narrow-to-region (region-beginning)
                              (region-end)))
        (let ((buffer (current-buffer)))
          (with-temp-buffer
            (insert-buffer-substring buffer)
            (let ((result (ebib--find-bibtex-entries ebib--cur-db t)))
              (unless (ebib--cur-entry-key)
                (ebib-db-set-current-entry-key t ebib--cur-db))
              (ebib--redisplay)
              (ebib--set-modified t)
              (message (format "%d entries, %d @STRINGs and %s @PREAMBLE found in buffer."
                               (car result)
                               (cadr result)
                               (if (nth 2 result) "a" "no"))))))))))

(defun ebib--get-db-from-filename (search-filename)
  "Return the database struct associated with SEARCH-FILENAME."
  (when search-filename
    (if (file-name-absolute-p search-filename)
        (setq search-filename (expand-file-name search-filename))) ; expand ~, . and ..
    (catch 'found
      (mapc (lambda (db)
              ;; If `search-filename' is an absolute file name, we want to compare to the
              ;; absolute file name of the database, otherwise we should use only
              ;; the non-directory component.
              (let ((db-filename (ebib-db-get-filename db (not (file-name-absolute-p search-filename)))))
                (if (file-name-absolute-p db-filename)
                    (setq db-filename (expand-file-name db-filename)))
                (if (string= search-filename db-filename)
                    (throw 'found db))))
            ebib--databases)
      nil)))

(defun ebib--get-local-databases ()
  "Return a list of .bib files associated with the current LaTeX file.
Each element in the list is a string holding the name of the .bib
file.  This function simply searches the current LaTeX file or its
master file for a `\\bibliography' or `\\addbibresource' command
and returns the file(s) given in its argument.  If no such command
is found, return the symbol `none'."
  ;; This only makes sense in LaTeX buffers
  (if (not (eq major-mode 'latex-mode))
      'none
    (let ((texfile-buffer (current-buffer))
          texfile)
      ;; if AucTeX's TeX-master is used and set to a string, we must
      ;; search that file for a \bibliography command, as it's more
      ;; likely to be in there than in the file we're in.
      (and (boundp 'TeX-master)
           (stringp TeX-master)
           (setq texfile (ebib--ensure-extension TeX-master ".tex")))
      (with-temp-buffer
        (if (and texfile (file-readable-p texfile))
            (insert-file-contents texfile)
          (insert-buffer-substring texfile-buffer))
        (save-excursion
          (save-match-data
            (let (files)
              (goto-char (point-min))
              ;; First search for a \bibliography command:
              (if (re-search-forward "\\\\\\(?:no\\)*bibliography{\\(.*?\\)}" nil t)
                  (setq files (mapcar (lambda (file)
                                        (ebib--ensure-extension file ".bib"))
                                      (split-string (buffer-substring-no-properties (match-beginning 1) (match-end 1)) ",[ ]*")))
                ;; If we didn't find a \bibliography command, search for \addbibresource commands:
                (while (re-search-forward "\\\\addbibresource\\(\\[.*?\\]\\)?{\\(.*?\\)}" nil t)
                  (let ((option (match-string 1))
                        (file (match-string-no-properties 2)))
                    ;; If this isn't a remote resource, add it to the list.
                    (unless (and option (string-match "location=remote" option))
                      (push file files)))))
              (or files 'none))))))))

(defun ebib--create-collection-from-db ()
  "Create a collection of BibTeX keys.
The source of the collection is either curent database or, if the
current buffer is a LaTeX file containing a \\bibliography
command, the BibTeX files in that command (if they are open in
Ebib)."
  (or ebib--local-bibtex-filenames
      (setq ebib--local-bibtex-filenames (ebib--get-local-databases)))
  (let (collection)
    (if (eq ebib--local-bibtex-filenames 'none)
        (if (null ebib--cur-keys-list)
            (error "No entries found in current database")
          (setq collection ebib--cur-keys-list))
      (mapc (lambda (file)
              (let ((db (ebib--get-db-from-filename file)))
                (cond
                 ((null db)
                  (message "Database %s not loaded" file))
                 ((null (ebib--db-get-current-entry-key db))
                  (message "No entries in database %s" file))
                 (t (setq collection (append (ebib-db-list-keys db)
                                             collection))))))
            ebib--local-bibtex-filenames))
    collection))

(defun ebib-insert-bibtex-key ()
  "Insert a BibTeX key at POINT.
The user is prompted for a BibTeX key and has to choose one from
the database(s) associated with the current LaTeX file, or from
the current database if there is no \\bibliography command.  Tab
completion works."
  (interactive)
  (ebib--execute-when
    ((database)
     (let ((collection (ebib--create-collection-from-db)))
       (when collection
         (let* ((key (completing-read "Key to insert: " collection nil t nil 'ebib--key-history))
                (format-list (or (cadr (assq (buffer-local-value 'major-mode (current-buffer)) ebib-citation-commands))
                                 (cadr (assq 'any ebib-citation-commands))))
                (citation-command
                 (ebib--ifstring (format-string (cadr (assoc
                                                       (completing-read "Command to use: " format-list nil nil nil 'ebib--cite-command-history)
                                                       format-list)))
                     (cl-multiple-value-bind (before repeater _ after) (ebib--split-citation-string format-string)
                       (concat (ebib--create-citation-command before)
                               (ebib--create-citation-command repeater key)
                               (ebib--create-citation-command after)))
                   key))) ; if the user didn't provide a command, we insert just the entry key
           (when citation-command
             (insert (format "%s" citation-command)))))))
    ((default)
     (error "No database loaded"))))

(defun ebib-create-bib-from-bbl ()
  "Create a .bib file for the current LaTeX document.
The LaTeX document must have a .bbl file associated with it.  All
bibitems are extracted from this file and a new .bib file is
created containing only these entries."
  (interactive)
  (ebib--execute-when
    ((database)
     (or ebib--local-bibtex-filenames
         (setq ebib--local-bibtex-filenames (ebib--get-local-databases)))
     (let* ((filename-sans-extension (file-name-sans-extension (buffer-file-name)))
            (bbl-file (concat filename-sans-extension ".bbl"))
            (bib-file (concat filename-sans-extension (car ebib-bibtex-extensions))))
       (unless (file-exists-p bbl-file)
         (error "No .bbl file exists. Run BibTeX first"))
       (when (or (not (file-exists-p bib-file))
                 (y-or-n-p (format "%s already exists. Overwrite? " (file-name-nondirectory bib-file))))
         (when (file-exists-p bib-file)
           (delete-file bib-file t))
         (let ((databases
                (delq nil (mapcar (lambda (file)
                                    (ebib--get-db-from-filename file))
                                  ebib--local-bibtex-filenames))))
           (with-temp-buffer
             (insert-file-contents bbl-file)
             (ebib--export-entries (ebib-read-entries-from-bbl) databases bib-file))))))
    ((default)
     (beep))))

(defun ebib-read-entries-from-bbl ()
  "Read BibTeX entries from the .bbl file of the current buffer."
  (interactive)
  (goto-char (point-min))
  (let (entries)
    (while (re-search-forward "\\\\\\(?:bibitem\\[\\(?:.\\|\n[^\n]\\)*]\\|entry\\){\\(.*?\\)}" nil t)
      (push (match-string 1) entries))
    entries))

(provide 'ebib)

;;; ebib.el ends here
