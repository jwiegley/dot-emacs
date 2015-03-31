;;; file-properties.el --- non-intrusive file local variables

;; Copyright (C) 2002 Thomas Link

;; Author: Thomas Link AKA samul AT web DOT de
;; Time-stamp: <2003-03-27>
;; Keywords:

(defconst file-properties-version "1.3")
(defconst file-properties-homepage
  "http://members.a1.net/t.link/CompEmacsProperties.html")
 
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

;;; Commentary:

;; ;---(:excerpt-beg file-properties :name desc)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsFileproperties")---
;; 
;; Store file local variables without changing the file's contents. Add the
;; variable's symbol to `file-properties-list', and the variable will be
;; automatically saved and restored. Candidates would be:
;; 
;; - `buffer-undo-list' (got the idea from Ivar Rummelhoff's
;; continuous-undo.el)
;; - `register-alist'
;; 
;; In addition, overlays can be stored too (see `file-properties-overlays').
;; 
;; By default, the file-properties of file =/there/here/this.txt= will be
;; stored in =/there/here/.props/this.txt= (see `file-properties-subdir').
;; This variable can be tweaked, so that properties for files in
;; unwriteable directories are stored in =~/.props/filename=. This means
;; you can store file local variables for files for which you don't have
;; writing permisson.
;; 
;; Installation: Put (require 'file-properties) (file-properties-install)
;; into your startup/user init file.
;; 
;; 
;; *** Commands
;; 
;; `file-properties-add', `file-properties-remove' :: Add and remove a
;; variable to or from the file's property list.
;; 
;; `file-properties-overlay-add', `file-properties-overlay-remove' :: Add
;; and remove overlays containing a specific symbol.
;; 
;; `file-properties-add-special', `file-properties-remove-special' :: Add
;; or remove a mode setting function or a hook function.
;; 
;; `file-properties-write' :: Write the property file.
;; 
;; `file-properties-install', `file-properties-deinstall' :: Add and remove
;; file-properties.el specific hooks.
;; 
;; 
;; *** Variables
;; 
;; `file-properties-list' :: A list of file-properties that should be
;; stored in the property file.
;; 
;; `file-properties-overlays' :: A list of symbols or plists identifying
;; overlays that should be stored.
;; 
;; `file-properties-overlay-ignored-properties' :: Ignore these properties
;; when dumping overlays.
;; 
;; `file-properties-categories' :: Definition of "special" properties.
;; 
;; `file-properties-file' :: A buffer local variable defining the properties
;; file -- relative to the current buffer's/file's location. Use this to
;; force the use of a non-standard properties file.
;; 
;; ;---(:excerpt-end file-properties :name desc)---

;;; Known problems:

;; ;---(:excerpt-beg file-properties :name problems)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsFileproperties")---
;; 
;; - File-Properties sometimes loses information -- e.g. when reading the
;; properties file failes or when a file was moved or renamed. Don't move
;; your files! If you have to, make backups of the auxillary files before
;; opening one of the files -- just do be sure.
;; 
;; ;---(:excerpt-end file-properties :name problems)---

;;; Change log:

;; ;---(:excerpt-beg file-properties :name versionhist)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsFileproperties")---
;; 
;; 1.3 :: Renamed "properties" to "file-properties"; directory properties;
;; `file-properties-dirty-flag'; catch errors, when `file-properties-read'
;; fails; `file-properties-get-file-desc',
;; `file-properties-verify-file-desc'; `file-properties-do-nothing'.
;; 
;; 1.2 :: Save some modes and hooks too -- see `file-properties-add-special'.
;; 
;; 1.1 :: Save and restore some overlays; better control over where to save
;; properties files (see `file-properties-location')
;; 
;; 1.0 :: Initial release
;; 
;; ;---(:excerpt-end file-properties :name versionhist)---

;;; To do:

;;; Code:

(require 'tellib)
(tellib-version-check-with-name "tellib" "0.2.1")


(defgroup file-properties nil
  "Make backups with a time stamp"
  :prefix "file-properties-"
  :group 'tools)

(defcustom file-properties-verbosity 2
  "*File properties' verbosity level."
  :type 'integer
  :group 'file-properties)

(defcustom file-properties-subdir ".props"
  "*Subdirectory where to put property files
\(relative to the current file's directory)."
  :type 'string
  :group 'file-properties)

(defcustom file-properties-dirprops ".props"
  "*The file name of the directory's file-properties file.
This file has to be edited by hand."
  :type 'string
  :group 'file-properties)

(defcustom file-properties-uniquedir ".props-id"
  "*Subdirectory where to put property files for buffers with unique IDs
\(relative to the current file's directory)."
  :type 'string
  :group 'file-properties)

(defcustom file-properties-location
  '(
    ;;("^.+://" file-properties-get-urls-properties-file)
    ((lambda (file) (not (file-writable-p (file-name-directory file))))
     file-properties-get-nonwriteable-properties-file)
    (:with-id
     file-properties-get-unique-properties-file)
    (:default "%{CD}%/.props%/"))
  "*An alist of regexps and locations of property files.
An alist or form: \((MATCH DIR) ...)

MATCH ... either :default, :with-id or a regexp or a predicate testing
the filename

DIR ... either a directory or a function returning the file-properties
filename

Replacement strings:
%{CD} ... the file's current directory
%{INITDIR} ... the init file's directory
%/ ... the default path separator
%% ... %
"
  :type '(repeat
	  (list :value ("" "")
		(choice (regexp :tag "RegExp" :value "")
			(function :tag "Predicate" :value nil)
			(const :tag "Default" :value :default)
			(const :tag "Unique ID" :value :with-id))
		(choice (string :tag "Directory" :value "")
			(function :tag "Function" :value nil))))
  :group 'file-properties)

(defcustom file-properties-warn-if-not-readable t
  "*Non-nil means, warn user if the file-properties file is non readable
and if `file-properties-flag' is non-nil."
  :type 'boolean
  :group 'file-properties)

(defcustom file-properties-overlay-ignored-properties
  '(begin-glyph end-glyph local-map keymap)
  "*Ignore these file-properties when dumping overlays."
  :type '(repeat
	  (symbol :tag "Symbol" :value nil))
  :group 'file-properties)

(defcustom file-properties-categories
  `(("Mode"
     (:key    :modes)
     (:setter funcall)
     (:reader (lambda ()
		(read-function "Function: "))))
    ("Variables"
     (:key    :vars)
     (:setter (lambda (x)
		;;(message "DEBUG %S" x)
		(apply #'set x)))
     (:reader (lambda ()
		(let ((var (intern
			    (completing-read "Variable: "
					     obarray nil nil nil 'variable-history))))
		  (when var
		    (list var (read-expression "Value: "
					       (when (boundp var) (eval var)))))))))
    ("Hooks"
     (:key    :hooks)
     (:setter (lambda (compound-def &optional append)
		(let ((hook     (nth 0 compound-def))
		      (function (nth 1 compound-def)))
		  (make-local-variable hook)
		  (add-hook hook function append))))
     (:reader (lambda ()
		(let ((hook (intern-soft
			     (completing-read
			      "Hook: "
			      obarray
			      (lambda (x)
				(and (boundp x)
				     (string-match "-hooks?$" (symbol-name x))))
			      t nil 'variable-history)))
		      (function (read-expression "Function: ")))
		  (when (and hook function)
		    (list hook function))))))
    )
  "*A list of categories know to `file-properties-add-special'.
Looks like: '(NAME-AS-STRING
		\(:key    SYMBOL)
		\(:setter FUNCTION)
		\(:reader FUNCTION))

The :setter function takes one argument -- the argument returned by reader.
The :reader function takes no arguments.
:key is a symbol -- the (currently ignored) key for storing extra data
in the properties list.
"
  :type '(repeat (list :value nil
		       (choice (const :tag "Mode" :value "Mode")
			       (const :tag "Hooks" :value "Hooks")
			       (string :tag "String" :value nil))
		       (list :value (:key nil)
			     (const :format "" :value :key)
			     (symbol :tag "Key (Symbol)" :value nil))
		       (list :value (:setter nil)
			     (const :format "" :value :setter)
			     (function :tag "Setting function" :value nil))
		       (list :value (:reader nil)
			     (const :format "" :value :reader)
			     (function :tag "Reading function" :value nil))
		       ))
  :group 'file-properties)

(defcustom file-properties-list nil
  "*A list of file-properties that should be stored in the property file.
There are three types of list elements:

SYMBOL ... add '(SYMBOL \(eval SYMBOL)) to the property file.

\(SYMBOL . ALIST) ... where ALIST has the following keys:

:predicate PREDICATE ... add '\(SYMBOL \(eval SYMBOL)) only if
\(PREDICATE \(eval SYMBOL) is non-nil. Defaults to `identity'.

:filter FILTER ... filter SYMBOLS value, i.e. add `\(SYMBOL ,\(FILTER
\(eval SYMBOL))). Defaults to `identity'.
"
  :type '(repeat
	  (choice
	   (symbol :tag "Variable" :value nil)
	   (cons :tag "List format" :value (nil)
		 (symbol :tag "Variable" :value nil)
		 (repeat
		  (choice
		   (list :tag "Predicate" :value (:predicate nil)
			 (const :format "" :value :predicate)
			 (function :value identity))
		   (list :tag "Filter function" :value (:filter nil)
			 (const :format "" :value :filter)
			 (function :value identity)))))))
)
(make-variable-buffer-local 'file-properties-list)

(defvar file-properties-dirty-flag nil
  "Non-nil if something happened that could require saving file properties.")
(make-variable-buffer-local 'file-properties-dirty-flag)

(defvar file-properties-write-out-hook nil
  "A list of predicates.
If one yields non-nil, the file-properties file will be written.")
(make-variable-buffer-local 'file-properties-write-out-hook)

(defvar file-properties-overlays nil
  "A list of symbols or plists identifying overlay that should be stored.
If it is a plist, the following fields are known:
:name ... Equal to symbol
:ignore ... A list of ignored properties
")
(make-variable-buffer-local 'file-properties-overlays)

(defvar file-properties-etc nil
  "An plist of other things to add.
Categories are defined by `file-properties-categories'.")
(make-variable-buffer-local 'file-properties-etc)

(defvar file-properties-tmp-buffer nil)
(make-variable-buffer-local 'file-properties-tmp-buffer)

(defvar file-properties-flag nil
  "Non-nil means, warn user if the file's file-properties file can't be loaded.")
(make-variable-buffer-local 'file-properties-flag)

(defvar file-properties-file nil
  "A buffer local variable defining the file-properties file
-- relative to the current buffer's/file's location.")
(make-variable-buffer-local 'file-properties-file)

(defvar file-properties-id nil
  "A buffer's (hopefully) unique id.")
(make-variable-buffer-local 'file-properties-id)

(defvar file-properties-do-nothing nil
  "If non-nil, file properties won't be read or written.")



(defun file-properties-get-urls-properties-file (file)
  "Get the file-properties filename based on an url
protocol://there/here/etc"
  (if (string-match "^\\(.+\\)://\\(.+\\)$" file)
      (concat (file-name-as-directory user-init-directory)
	      (file-name-as-directory file-properties-subdir)
	      (file-name-as-directory (match-string 1 file))
	      (tellib-replace-args (match-string 2 file)
				   `(("" ,(string directory-sep-char)))
				   ?/))
    (tellib-error 'error "file-properties: Not an URL" file)))
;;test: (file-properties-get-urls-properties-file "http://localhost/wherever")

(defun file-properties-get-nonwriteable-properties-file (file)
  "Get the file-properties filename for an non-writeable file"
  (tellib-remove-redundant-dir-separators
   (concat (file-name-as-directory user-init-directory)
	   (file-name-as-directory file-properties-subdir)
	   (if (and (not (char= ?: directory-sep-char))
		    (string-match "^\\(.+\\):\\(.+\\)$" file))
	       (concat (match-string 1 file)
		       (match-string 2 file))
	     file))))
;;test: (file-properties-get-nonwriteable-properties-file "c:\\there\\here")
;;test: (file-properties-get-nonwriteable-properties-file "/there/here")

(defun file-properties-define-unique-id ()
  "Define & insert a unique ID in the current buffer.
The ID is made up from the `system-name', the user name, the current
time, and the current buffer's file name -- this is md5 encoded."
  (interactive)
  (if file-properties-id
      (tellib-error 'error "file properties: Buffer has already an ID.")
    (let* ((m  (system-name))
	   (u  (getenv "USER"))
	   (d  (current-time))
	   (f  (buffer-file-name))
	   (id (md5 (format "%S %S %S %S" m u d f))))
      (tellib-update-local-variable-def 'file-properties-id id
					:dont-replace t :set-var t)
      id)))
;;test: (file-properties-define-unique-id)

(defun file-properties-get-unique-properties-file (file)
  "Get the file-properties filename for files with a unique id."
  (if file-properties-id
      (tellib-remove-redundant-dir-separators
       (concat (file-name-as-directory user-init-directory)
	       (file-name-as-directory file-properties-uniquedir)
	       file-properties-id))
    (tellib-error 'error "file properties: No unique buffer id.")))
;;test: (let ((file-properties-id "Bla"))
;; (file-properties-get-unique-properties-file "/there/here"))

(defun file-properties-get-file-name (file &optional makedir-flag)
  "Return the name of the property file for FILE (which can be a directory).

If MAKEDIR-FLAG is non-nil, this function is used if query mode and the
parent directory will be created if necessary.
"
  (if file-properties-file
      (concat (file-name-directory file) file-properties-file)
    (let* ((dd (file-name-directory file))
	   (ps (string directory-sep-char))
	   (rv (concat dd (file-name-as-directory file-properties-subdir)))
	   (fn (let ((fn (file-name-nondirectory file)))
		 (if (string= fn "")
		     file-properties-dirprops
		   fn)))
	   (file
	    (tellib-remove-redundant-dir-separators
	     (catch 'exit
	       (mapc
		#'(lambda (this)
		    (let ((rx (nth 0 this))
			  (rs (nth 1 this)))
		      (when (if (functionp rx)
				(funcall rx file)
			      (case rx
				((:default) t)
				((:with-id)
				 (and file-properties-id
				      (equal file (buffer-file-name))))
				(t
				 (string-match rx file))))
			(throw 'exit
			       (cond
				((functionp rs)
				 (funcall rs file))
				((stringp rs)
				 (concat (file-name-as-directory
					  (tellib-replace-args 
					   rs
					   `(("{CD}" ,dd)
					     ("{INITDIR}" ,user-init-directory)
					     ("/"    ,ps))))
					 fn))
				(t
				 (tellib-error 'error 
					       "file-properties: Bad type" rs))
				)))))
		file-properties-location)
	       rv)))
	   (dir (file-name-directory file)))
      (when (and makedir-flag
		 (not (file-readable-p dir)))
	;;(message "DEBUG: %s %s" dir file)
	(make-directory dir t))
      file)))
;;test: (file-properties-get-file-name (buffer-file-name))
;;test: (file-properties-get-file-name "~/src/")
;;test: (file-properties-get-file-name "/etc/hosts")
;;test: (file-properties-get-file-name "http://localhost/wherever")
;;test: (let ((file-properties-file "x")) (file-properties-get-file-name (buffer-file-name)))

(defun file-properties-get-properties-list ()
  "Return a list of \(VARIABLE VALUE) list for the current buffer
as defined by `file-properties-list'."
  (flet ((log (this)
	   (tellib-message 0 'file-properties
			   "General confusion: unbound variable: %s" 
			   this)
	   nil))
    (let ((rv (loop for this in file-properties-list append
		(cond
		 ((listp this)
		  (let* ((sym (car this))
			 (val (if (boundp sym)
				  (eval sym)
				(log this)))
			 (props (cdr this))
			 (pred (tellib-alist-get props :predicate #'identity t))
			 (flt  (tellib-alist-get props :filter #'identity t)))
		    (when (funcall pred val)
		      ;;`((,sym ,(eval val))))))
		      `((,sym ,(funcall flt val))))))
		 (t
		  (if (boundp this)
		      `((,this ,(eval this)))
		    (log this)))))))
	  (when rv
	    (cons `(file-properties-list ,file-properties-list)
		  rv)))))
;;test: (file-properties-get-properties-list)
;;test: (setq test '(1 2 3 4 5))
;;test: (let ((file-properties-list
;;       '((test (:filter (lambda (x)
;;			  (tellib-filter-list x #'(lambda (y) (> y 3)))))))))
;;  (file-properties-get-properties-list))

(defun file-properties-get-overlay-list ()
  "Return a list of dumped overlays for the current buffer
as defined by `file-properties-overlays'."
  (tellib-overlay-collect (mapcar (lambda (x) 
				    (if (listp x)
					(plist-get x :name)
				      x))
				  file-properties-overlays)
			  nil
			  nil
			  (append file-properties-overlay-ignored-properties
				  (tellib-mappend (lambda (x)
						    (if (listp x)
							(plist-get x :ignore)
						      nil))
						  file-properties-overlays))))

(defun file-properties-save-properties-file-p (&optional properties overlays etc)
  "Return non-nil, if the file-properties file for current buffer should be saved."
  ;(message "DEBUG: %s %s %s %s" file-properties-dirty-flag properties overlays etc)
  (not (not (or file-properties-dirty-flag
		(or properties
		    (file-properties-get-properties-list))
		(or etc
		    file-properties-etc)
		(or overlays
		    (file-properties-get-overlay-list))))))
;;test: (file-properties-save-properties-file-p)

(defun file-properties-get-file-desc (&optional filename)
  "Return something describing the current file (or FILENAME)."
  (let* ((file  (abbreviate-file-name (or filename
					  buffer-file-name)
				      t))
	 (attr  (file-attributes file))
	 (size  (nth 7 attr))
	 (md5   (md5 (buffer-string))))
    (list file md5 size)))
;;test: (file-properties-get-file-desc "~/.bashrc")
;;test: (file-properties-get-file-desc "~/.bash_profile")
;;test: (file-properties-get-file-desc "/cygdrive/c/tml/.bash_profile")

(defun file-properties-verify-file-desc (desc &optional filename)
  "Return something describing the current file (or FILENAME).
This currently is not very useful."
  (let* ((file (or filename
		   buffer-file-name))
	 (curr (file-properties-get-file-desc file))
	 ;;(dbg  (message "DEBUG: desc: %S <-> curr: %S" desc curr))
	 (cmpr (tellib-zip desc curr)))
    (catch 'exit
      (loop for x from 0 to (1- (length curr)) do
	(let* ((c (nth x cmpr))
	       (a (nth 0 c))
	       (b (nth 1 c)))
	  (cond
	   ((and (= x 0)
		 (not (string= (expand-file-name a) (expand-file-name b))))
	    (tellib-message 2 'file-properties "File has moved: %s -> %s"  a b))
	   ((not (equal a b))
	    (tellib-message 1 'file-properties "File has changed: %s <> %s" a b)
	    (throw 'exit nil))
	   )))
      t)))

(defun file-properties-write-file (file string)
  "Write a file-properties file."
  (with-temp-buffer
    (setq file-properties-tmp-buffer t)
    (let (;;(backup-inhibited t)
	  (auto-mode-alist nil)
	  (version-control 'never)
	  (comment-start ";")
	  (comment-end   ""))
      ;;(message "DEBUG: %S" string)
      (insert string)
      ;;(tellib-update-local-variable-def 'backup-inhibited t)
      (tellib-update-local-variable-def 'version-control 'never)
      (write-file file)))
  (setq file-properties-dirty-flag nil))
  
;;;###autoload
(defun file-properties-write (&optional file)
  "Write the property file.
See the documentation of `file-properties-list'."
  (interactive)
  (unless (or file-properties-do-nothing
	      file-properties-tmp-buffer)
    (when file-properties-dirty-flag
      (let ((file
	     (or file
		 (buffer-file-name)
		 (if (y-or-n-p
		      "Save buffer to a file in order to use file-properties? ")
		     (save-buffer)
		   (message
		    "file-properties: Can't determine the buffer's file name.")
		   nil))))
	(when file
	  (when file-properties-overlays
	    (add-to-list 'file-properties-list 'file-properties-overlays))
	  (let ((ols      (file-properties-get-overlay-list))
		(etc      file-properties-etc)
		(filedesc (file-properties-get-file-desc))
		(proplst  (file-properties-get-properties-list))
		(propfile (file-properties-get-file-name file t)))
	    ;;(message "DEBUG: %S" proplst)
	    (when (file-properties-save-properties-file-p proplst ols etc)
	      (file-properties-write-file
	       propfile 
	       (format "(:version 3\n :filedesc %S\n :vars %S\n :overlays %S\n :etc %S)"
		       filedesc proplst ols etc)))))))))
;;test: (progn (setq al '(1 2 3)) (setq bl nil) (setq file-properties-list '(bl al)))
;;test: (progn 	(setq al '(1 2 3)) (setq bl nil)
;;		(setq file-properties-list '((bl identity) al)))
;;test: (file-properties-write)

(defun file-properties-read-file (file)
  "Read a file-properties FILE."
  (car (read-from-string (tellib-read-file file "()"))))

(defun file-properties-read (&optional file)
  "Read the property file."
  (unless file-properties-do-nothing
    (let ((file      (or file
			 buffer-file-name)))
      (when (not (string-match (format "%s%s%s"
				       directory-sep-char
				       file-properties-subdir
				       directory-sep-char)
			       file))
	(let ((dirpfile (file-properties-get-file-name
			 (concat (file-name-directory file)
				 file-properties-dirprops)))
	      (propfile (file-properties-get-file-name file)))
	  (cond
	   ((file-readable-p propfile)
	    (let* ((flst    (file-properties-read-file propfile))
		   (dlst    (file-properties-read-file dirpfile))
		   (version (if (tellib-valid-plist-p flst)
				(plist-get flst :version 1)
			      1))
		   (pre3    (< version 3))
		   (lst     (if pre3
				flst
			      (tellib-plist-mapkeys
			       (lambda (key f d) `(,key ,(append d f)))
			       '(:vars :etc :overlays :filedesc)
			       flst
			       dlst)))
		   (desc-ok (let ((desc (case version
					  ((3)
					   (plist-get lst :filedesc))
					  (t
					   nil))))
			      (if desc
				  (file-properties-verify-file-desc desc file)
				t)))
		   (vars    (case version
			      ((2 3)
			       (plist-get lst :vars))
			      (t
			       flst)))
		   (etc     (case version
			      ((2 3)
			       (setq file-properties-etc (plist-get flst :etc))
			       (plist-get lst :etc))
			      (t
			       nil)))
		   (ols     (case version
			      ((2 3)
			       (plist-get lst :overlays))
			      (t
			       nil))))
	      ;;(message "DEBUG: %S" lst)(sleep-for 3)
	      ;;restore variables
	      (setq file-properties-dirty-flag
		    (or (unless desc-ok
			  (tellib-message 1 'file-properties
					  "Properties file is out of sync!")
			  t)
			file-properties-dirty-flag 
			vars etc ols))
	      (mapc #'(lambda (this)
			(let ((var (car this))
			      (val (cadr this)))
			  (when pre3
			    (add-to-list 'file-properties-list var))
			  (make-local-variable var)
			  (set var val)))
		    vars)
	      ;;restore etc
	      (mapc #'(lambda (this)
			(let* ((cat (car this))
			       (setter (tellib-alist-get
					(assoc cat file-properties-categories)
					:setter nil t)))
			  (dolist (val (cadr this))
			    (condition-case nil
				(funcall setter val)
			      (error
			       (tellib-message 1 'file-properties
					       "Restore failed: %S"
					       val))))))
		    etc)
	      ;;restore overlays
	      (tellib-overlay-restore ols)
	      ))
	   ((and file-properties-warn-if-not-readable
		 file-properties-flag)
	    (let ((msg "file-properties: Properties file can't be loaded"))
	      (unless (y-or-n-p (format "%s. Continue? " msg))
		(tellib-error 'error msg file))))))))))
;;test: (progn (setq al t) (setq bl t))
;;test: (progn (setq file-properties-list nil) (file-properties-read))

;;;###autoload
(defun file-properties-minor-mode (&optional check-if-needed dirty-flag)
  "Prepare the current buffer for use with file-properties.el."
  (let ((flag (if check-if-needed
		  (file-properties-save-properties-file-p)
		t)))
    (setq file-properties-dirty-flag t)
    (tellib-update-local-variable-def 'file-properties-flag flag
				      :val-flag t
				      :if-different t
				      :set-var t
				      :no-error-if-read-only t)))
;;test: (file-properties-minor-mode)
;;test: (file-properties-minor-mode t)

;;;###autoload
(defun file-properties-add (&optional variable predicate)
  "Add VARIABLE to the file's property list.
PREDICATE defaults to (not (null VARIABLE))."
  (interactive)
  (let ((var (or variable
		 (intern-soft (read-from-minibuffer "Variable: ")))))
    (if (boundp var)
	(progn
	  (if predicate
	      (add-to-list 'file-properties-list (list var :predicate predicate))
	    (add-to-list 'file-properties-list var))
	  (file-properties-minor-mode nil t))
      (tellib-error 'error "Property: symbol not bound" var))))
;;test: (file-properties-add)
;;test: (let (x file-properties-list) (file-properties-add 'x #'null))

;;;###autoload
(defun file-properties-remove (&optional var)
  "Remove a variable from the file's property list."
  (interactive)
  (let ((var (or var
		 (intern-soft
		  (completing-read "Variable: "
				   (mapcar (lambda (x)
					     (list (symbol-name x)))
					   file-properties-list))))))
    (setq file-properties-list
	  (tellib-filter-list file-properties-list
			      #'(lambda (x)
				  (not (equal (if (listp x)
						  (car x)
						x)
					      var)))))
    (file-properties-minor-mode t t)))
;;test: (file-properties-remove)

;;;###autoload
(defun file-properties-overlay-add (&optional symbol)
  "Add SYMBOL to `file-properties-overlays'."
  (interactive)
  (let ((sym (or symbol
		 (intern (read-from-minibuffer "Variable: ")))))
    (when sym
      (add-to-list 'file-properties-overlays sym)
      (file-properties-minor-mode nil t))))
;;test: (file-properties-overlay-add)
;;test: (let (x file-properties-overlays) (file-properties-overlay-add 'x))

;;;###autoload
(defun file-properties-overlay-remove (&optional symbol)
  "Remove SYMBOL from `file-properties-overlays'."
  (interactive)
  (let ((sym (or symbol
		 (intern (completing-read "Symbol: "
					  (mapcar (lambda (x)
						    (list (symbol-name x)))
						  file-properties-overlays))))))
    (tellib-del-from-list 'file-properties-overlays sym)
    (file-properties-minor-mode t t)))
;;test: (file-properties-overlay-remove)

;;;###autoload
(defun* file-properties-add-special (&key category
				     value
				     dont-set
				     (use-as-etc nil use-as-etc-flag))
  "Add something being defined in `file-properties-categories'
to `file-properties-etc'. CATEGORY and the corresponding VALUEs are
defined in `file-properties-categories'."
  (interactive)
  (let* ((cat (or category
		  (completing-read "Category: " file-properties-categories nil t)))
	 (val (or value
		  (funcall (tellib-alist-get (assoc cat file-properties-categories)
					     :reader nil t))))
	 (etc (if use-as-etc-flag use-as-etc file-properties-etc))
	 (rv  (tellib-alist-set etc cat (cons val (tellib-alist-get etc cat)))))
    (if dont-set
	rv
      (setq file-properties-etc rv))))

;;;###autoload
(defun* file-properties-remove-special (&key category
					value 
					dont-set
					(use-as-etc nil use-as-etc-flag))
  "Remove something being defined in `file-properties-categories'
from `file-properties-etc'. CATEGORY and the corresponding VALUEs are
defined in `file-properties-categories'."
  (interactive)
  (let* ((cat (or category
		  (completing-read "Category: " file-properties-categories nil t)))
	 (val (or value
		  (funcall (tellib-alist-get (assoc cat file-properties-categories)
					     :reader nil t))))
	 (etc (if use-as-etc-flag use-as-etc file-properties-etc))
	 (rv  (tellib-alist-set etc cat (remove val (tellib-alist-get etc cat)))))
    (if dont-set
	rv
      (setq file-properties-etc rv))))

;;;###autoload
(defun file-properties-add-dirprop (&optional category value directory)
  "Attach a file property to the directory's properties."
  (interactive)
  (let* ((dirpfile (file-properties-get-file-name
		    (concat (or directory
				(file-name-directory buffer-file-name))
			    file-properties-dirprops)))
	 (etc (file-properties-add-special
	       :dont-set t
	       :use-as-etc (plist-get (file-properties-read-file dirpfile) :etc))))
    ;;(message "DEBUG: %S %S" etc (plist-get (file-properties-read-file dirpfile) :etc))
    (file-properties-write-file dirpfile (format "(:etc %S)" etc))))

;;;###autoload
(defun file-properties-remove-dirprop (&optional category value directory)
  "Remove a file property from the directory's properties."
  (interactive)
  (let* ((dirpfile (file-properties-get-file-name
		    (concat (or directory
				(file-name-directory buffer-file-name))
			    file-properties-dirprops)))
	 (etc (file-properties-remove-special
	       :dont-set t
	       :use-as-etc (plist-get (file-properties-read-file dirpfile) :etc))))
    (file-properties-write-file dirpfile (format "(:etc %S)" etc))))

;;;###autoload
(defun file-properties-list ()
  "List current buffer's file properties."
  (interactive)
  (let ((ols file-properties-overlays)
	(vrs (file-properties-get-properties-list))
	(etc file-properties-etc))
    (pop-to-buffer (format "*File properties: %s*" buffer-file-name))
    (delete-region (point-min) (point-max))
    (insert "Overlays:\n")
    (mapc #'(lambda (this)
	      (insert (format "%S" this))
	      (newline))
	  ols)
    (insert "\nVariables:\n")
    (mapc #'(lambda (this)
	      (insert (format "%S" this))
	      (newline))
	  vrs)
    (insert "\nEtc:\n")
    (mapc #'(lambda (this)
	      (insert (format "%S" this))
	      (newline))
	   etc)
    (newline)))

(defun file-properties-install ()
  "Install file-properties specific hooks."
  (interactive)
  (tellib-installer 'tellib 'file-properties)
  (add-hook 'find-file-hooks #'file-properties-read)
  ;;(add-hook 'write-file-hooks #'file-properties-write)
  (add-hook 'kill-buffer-hook #'file-properties-write)
  ;;(setq kill-buffer-hook nil)
  (when (boundp 'filesets-ingroup-collect-hook)
    (add-hook 'filesets-ingroup-collect-hook #'file-properties-read)))

(defun file-properties-uninstall ()
  "Deinstall file-properties specific hooks."
  (interactive)
  (tellib-uninstaller 'tellib 'file-properties)
  (remove-hook 'find-file-hooks #'file-properties-read)
  ;;(remove-hook 'write-file-hooks #'file-properties-write)
  (remove-hook 'kill-buffer-hook #'file-properties-write)
  ;;(setq kill-buffer-hook nil)
  (when (boundp 'filesets-ingroup-collect-hook)
    (remove-hook 'filesets-ingroup-collect-hook #'file-properties-read)))

;(file-properties-install)
;(file-properties-uninstall)

;;test: (setq file-properties-list nil)
;;test: (setq file-properties-overlays nil)
;;test: (setq al '(1 2 3))
;;test: (file-properties-add 'al)
;;test: (file-properties-remove 'al)
;;test: (file-properties-overlay-add 'al)
;;test: (file-properties-overlay-remove 'al)
;;test: (file-properties-save-properties-file-p)
;;test: (file-properties-get-properties-list)
;;test: (file-properties-get-overlay-list)

(provide 'file-properties)

;;; file-properties.el ends here

;;; Local Variables:
;;; file-properties-flag: t
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
