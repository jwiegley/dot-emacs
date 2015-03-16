;;; TELLIB.EL --- Thomas' ELisp LIBrary

;; Copyright (C) 2002 Free Software Foundation, Inc.

;; Author: Thomas Link aka samul at web dot de
;; Time-stamp: <2003-04-06>
;; Keywords: Elisp Library

(defvar tellib-version "0.2.1")
(defvar tellib-homepage "http://members.a1.net/t.link/CompEmacsTellib.html")

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

;; Tested with: 21.4 (patch 10) "Military Intelligence" XEmacs Lucid

;;; Commentary:

;; Installation: Put (require 'tellib) (tellib-install) into your
;; startup/user init file.

;; Some possibly useful functions.

;; ;---(:excerpt-beg *FUNCTION* :name tellib-selfdoc)---
;; ;---(:excerpt-source #'(tellib-selfdocumentation "^tellib-"))---
;; 
;; (tellib-add-related-buffer BUFFER &optional PARENT-BUFFER)
;; Add BUFFER to `tellib-related-buffers'.
;; 
;; (tellib-alist-get ALIST KEY &optional DEFAULT CAR-FLAG)
;; Get KEY's value in the association list ALIST.
;; 
;; (tellib-alist-p ALIST)
;; Return non-nil if ALIST appears to be a proper association list.
;; 
;; (tellib-alist-set ALIST KEY &rest VALUES)
;; Replace KEY's value with VALUES in ALIST or append (KEY . VALUES) to
;; ALIST.
;; 
;; (tellib-alist-setcdr ALIST KEY LIST)
;; Replace KEY's cdr with LIST in ALIST or append (KEY . LIST) to ALIST.
;; 
;; (tellib-andmap TELLIB-PRED &rest TELLIB-LISTS)
;; Return non-nil if TELLIB-PRED is true for all elements of TELLIB-LISTS.
;; 
;; (tellib-andmap-1 TELLIB-PRED TELLIB-DEFAULT &rest TELLIB-LISTS)
;; Return non-nil if TELLIB-PRED is true for all elements of TELLIB-LISTS.
;; 
;; (tellib-call-with-event-pos TELLIB-FN TELLIB-EVENT &rest TELLIB-ARGS)
;; Set current buffer and call FN with the position where EVENT occured.
;; 
;; (tellib-close-related-buffers)
;; Close related buffers.
;; 
;; (tellib-define-provide-hook FEATURE &rest HOOKS)
;; Add FEATURE's post-provide HOOKS to `tellib-post-provide-hooks'.
;; 
;; (tellib-del-from-list LIST-VAR ELEMENT)
;; Delete ELEMENT from LIST-VAR.
;; 
;; (tellib-desc-env &optional VERTSPACE)
;; Return a string describing the environment -- a little bit.
;; 
;; (tellib-directory-files DIR &optional WHAT FILE-PATTERN DIR-PATTERN
;;                        FULL-NAME-FLAG)
;; List files or dirs in DIR.
;; 
;; (tellib-document SYMBOL &optional PRE SEP POST SKIP-IF-UNDOC
;;                 SKIP-IF-UNIMPORTANT PREDICATE REFORMAT-FLAG)
;; Return a short documentation for SYMBOL.
;; 
;; (tellib-edit-in-buffer TEXT &optional MESSAGE MODE-FN KEYMAP-VAR
;;                       ON-EXIT-FN)
;; Edit TEXT in a temporary buffer -- use `tellib-edit-in-buffer*' if
;; possible.
;; 
;; (tellib-edit-in-buffer* TITLE TEXT ON-EXIT-FUNCTION &rest KEY-ARGS)
;; Edit TEXT in a buffer called TITLE.
;; 
;; (tellib-error DATUM &rest ARGS)
;; Signal a non-continuable error.
;; 
;; (tellib-file-name-break-up FILENAME &optional DROP-NULL-ELEMENTS)
;; Return a list of FILENAME parts.
;; 
;; (tellib-file-name-last-bit FILENAME)
;; Returns the last bit of FILENAME -- either directory or file.
;; 
;; (tellib-filter-list TELLIB-LIST TELLIB-COND-FN)
;; Remove all elements not conforming to TELLIB-COND-FN from list
;; TELLIB-LIST.
;; 
;; (tellib-info NAME)
;; Display NAME's version information.
;; 
;; (tellib-install)
;; Install tellib's hooks etc.
;; 
;; tellib-installation-requests
;; An plist of libraries and who demanded their installation.
;; 
;; (tellib-installer PACKAGE-NAME REQUESTING-LIBRARY &optional
;;                  TOP-INSTALL-FLAG)
;; Call LIBRARY-install and add REQUESTING-LIBRARY to
;; `tellib-installation-requests'.
;; 
;; (tellib-lax-plist-get LAX-PLIST PROPERTY &optional DEFAULT)
;; Extract a value from a lax property list.
;; 
;; (tellib-lax-plist-put LAX-PLIST PROPERTY VALUE)
;; Change value in LAX-PLIST of PROPERTY to VALUE.
;; 
;; (tellib-make-proper-filename STRING &optional REGEXP)
;; Replace suspicious characters in STRING with an underscore.
;; 
;; (tellib-mapcart TELLIB-FN TELLIB-LIST)
;; Similar to `mapcar' but drops nil values.
;; 
;; (tellib-mappend TELLIB-FN TELLIB-LIST)
;; Map TELLIB-FN (returning lists) on TELLIB-LIST and append results.
;; 
;; (tellib-member TELLIB-ITEM TELLIB-LIST &rest TELLIB-KEYS)
;; A clone of `member*'. At the moment only the :test key is supported.
;; 
;; (tellib-message LEVEL &rest ARGS)
;; Show a message only if LEVEL is sufficiently low -- i.e. important.
;; 
;; (tellib-not-yet-implemented FEATURE)
;; Throw an error explaining that FEATURE is not yet implemented.
;; 
;; (tellib-ormap TELLIB-PRED TELLIB-LIST)
;; Return SUBLIST of TELLIB-LIST, for which (TELLIB-PRED (car SUBLIST)) is
;; true.
;; 
;; (tellib-overlay-change-size DX &optional SYMBOLS OVERLAY)
;; Make an overlay DX characters larger/smaller.
;; 
;; (tellib-overlay-collect SYMBOLS &optional BUFFER OVERLAYS IGNORE)
;; Return a list of dumped overlays with one of SYMBOLS being non-nil.
;; 
;; (tellib-overlay-collect* SYMBOLS &optional BUFFER OVERLAYS
;;                         USE-THESE-OVERLAY-FLAG PREDICATE)
;; Return a list of overlays with one of SYMBOLS being non-nil.
;; 
;; (tellib-overlay-dump OVERLAY &optional IGNORE)
;; Return a list representing OVERLAY.
;; 
;; (tellib-overlay-move DX DY &optional SYMBOLS OVERLAY)
;; Move an overlay to DX/DY from the current position.
;; 
;; (tellib-overlay-restore DUMPED-OVERLAYS &optional BUFFER)
;; Restore all overlays in DUMPED-OVERLAYS
;; 
;; (tellib-plist-mapkeys FUNCTION KEYS &rest PLISTS)
;; Map FUNCTION on the KEYS in PLISTS and append the values to a list.
;; 
;; (tellib-plist-merge PLIST1 PLIST2)
;; Insert PLIST 1 into PLIST2.
;; 
;; tellib-post-provide-hooks
;; A plist of hooks to be run after providing a certain feature.
;; 
;; (tellib-quote TXT)
;; Return TXT in quotes.
;; 
;; (tellib-re-search REGEXP &optional CASE-SENSITIVE BACKWARD-FLAG)
;; Search for REGEXP while taking care of `case-fold-search'.
;; 
;; (tellib-read-file FILENAME &optional DEFAULT)
;; Read FILENAME and return its contents as string.
;; 
;; tellib-related-buffers
;; A list of related editing buffers.
;; 
;; (tellib-remove-redundant-dir-separators FILENAME)
;; Remove multiples '/' (or whatever) in filename.
;; 
;; (tellib-replace-args STRING ARGS-ALIST &optional ESCAPE-CHAR)
;; Replace args-alist in string.
;; 
;; (tellib-require PACKAGE REQUIRED-STRING)
;; Require a package and check if the version is okay.
;; 
;; tellib-running-xemacs
;; Non-nil means we are running XEmacs.
;; 
;; (tellib-scan-variables TRUNC &optional BEG END BUFFER)
;; Scan variables TRUNC-[BEG-END] and combine their values to a list.
;; 
;; (tellib-selfdocumentation REGEXP &optional PREDICATE
;;                          SKIP-IF-UNIMPORTANT)
;; List documentations for symbols matching REGEXP -- see
;; `tellib-document'.
;; 
;; (tellib-set-file-variable &rest DONT-REPLACE-FLAG)
;; Set a file local variable.
;; 
;; (tellib-simplify-string STRING &optional REGEXP)
;; Replace suspicious characters in STRING with an underscore.
;; 
;; (tellib-some TELLIB-PRED TELLIB-LIST)
;; Return the value of TELLIB-PRED, if non-nil for an item in TELLIB-LIST.
;; 
;; (tellib-split-string-by-char STRING SEPCHAR)
;; Split STRING into a list of substrings originally separated by SEPCHAR.
;; 
;; (tellib-string-count STRING REGEXP)
;; Count occurances of REGEXP in STRING.
;; 
;; (tellib-string-fill STRING &optional LEFT-COL RIGHT-COL PREFIX)
;; Fill STRING using `fill-region'. FILL-STRING defaults to "\n".
;; 
;; (tellib-string-trim STRING &optional DONT-TRIM-LEFT DONT-TRIM-RIGHT
;;                    REMOVE-TEXT-PROPERTIES-FLAG)
;; Lose leading and trailing whitespace.
;; 
;; (tellib-sublist TELLIB-LIST TELLIB-BEG &optional TELLIB-END)
;; Get the sublist of TELLIB-LIST from TELLIB-BEG to TELLIB-END - 1.
;; 
;; (tellib-test NAME RESULT &rest BODY)
;; Evaluate BODY at compile time and check if it returns RESULT.
;; 
;; (tellib-test-error NAME ERROR-LIST &rest BODY)
;; Evaluate BODY at compile time and check if it throws an error as
;; expected.
;; 
;; tellib-test-flag
;; Non-nil means, perform compile-time testing.
;; 
;; (tellib-testing MODE-STRING FEATURE-NAME MESSAGEP &rest BODY)
;; Disable features in non-testing mode.
;; 
;; (tellib-uninstall)
;; Deinstall tellib's hooks etc.
;; 
;; (tellib-uninstaller PACKAGE-NAME REQUESTING-LIBRARY &optional
;;                    TOP-UNINSTALL-FLAG)
;; Call LIBRARY-uninstall
;; 
;; (tellib-update-local-variable-def &optional VAR VAL &rest --REST--72872)
;; 
;; (tellib-valid-plist-p PLIST)
;; Given a plist, return non-nil if its format is correct.
;; 
;; tellib-verbosity
;; An integer defining the level of verbosity. 0 means no messages
;; 
;; (tellib-version-check NAME VERSION-STRING REQUIRED-STRING)
;; Throw an error if VERSION-STRING doesn't fit REQUIRED-STRING.
;; 
;; (tellib-version-check-p VERSION-STRING REQUIRED-STRING)
;; Return non-nil if VERSION-STRING satisfies REQUIRED-STRING.
;; 
;; (tellib-version-check-with-name PACKAGE-NAME REQUIRED-STRING)
;; Throw an error if PACKAGE-NAME-version doesn't fit REQUIRED-STRING.
;; 
;; (tellib-with-key-arguments ARGS DEFINITION &rest BODY)
;; Set ARGS according to DEFINITION and evaluate BODY.
;; 
;; (tellib-with-message-buffer MESSAGE &rest BODY)
;; Display a buffer with MESSAGE and evaluate BODY.
;; 
;; (tellib-with-result RESULT &rest BODY)
;; Eval RESULT and BODY, and return RESULT's value.
;; 
;; (tellib-zip &rest TELLIB-LISTS)
;; Zip lists. Turns '((A1 ...) (A2 ...) ...) into '((A1 A2 ...) ...).
;; 
;; (tellib-zip-1 DEFAULT &rest TELLIB-LISTS)
;; Zip lists. Like `tellib-zip' but accepts lists of unequal length
;; 
;; ;---(:excerpt-end *FUNCTION* :name tellib-selfdoc)---

;;; Change log:

;;; To do:

;;; Thanks to:

;; Christian Ohler (Christian DOT Ohler AT Informatik DOT Uni-Oldenburg DOT DE)
;;	help with `tellib-re-search'

;;; Code:

(eval-and-compile
  (unless (boundp 'tellib-running-xemacs)
    (defvar tellib-running-xemacs (string-match "XEmacs\\|Lucid" emacs-version)
      "Non-nil means we are running XEmacs."))
  (when tellib-running-xemacs
    (require 'overlay)))



; ------------------------------------------- * Control

(defmacro tellib-with-result (result &rest body)
  "Eval RESULT and BODY, and return RESULT's value."
  (let ((tellib-rv (gensym "tellib-rv")))
    `(let ((,tellib-rv ,result))
       ,@body
       ,tellib-rv)))
;;test: (tellib-with-result 1 2 3)
;;test: (tellib-with-result (- 1 1) 2 3)
;;test: (tellib-with-result (- 1 1))



; ------------------------------------------- * Debugging, Error, Testing

(defmacro tellib-testing (mode-string feature-name messagep &rest body)
  "Disable features in non-testing mode."
  (cond
   ((equal mode-string "testing")
    `(progn ,@body))
   (messagep
    (message "Tellib: feature `%s' is disabled." feature-name)
    nil)
   (t
    nil)))

(defun tellib-desc-env (&optional vertspace)
  "Return a string describing the environment -- a little bit."
  (let ((vs (make-string (or vertspace 0) ?\n)))
    (format "%sTested with: %s\n%s"
	    vs
	    emacs-version
	    vs)))

(eval-and-compile
  (if tellib-running-xemacs
      (defalias 'tellib-error 'error)
    ;; a version by RMS
    (defmacro tellib-error (class &rest args)
      "`error' wrapper."
      `(error (mapconcat 'identity ,args " "))))

  (defvar tellib-test-flag nil
    "Non-nil means, perform compile-time testing.")

  (defmacro tellib-test (name result &rest body)
    "Evaluate BODY at compile time and check if it returns RESULT.
\(Throw an error if this is not the case.)

Sample usage:
	\(tellib-test \"test-add-1\" 2 \(+ 1 1))
"
    (let ((val (make-symbol "val")))
      `(eval-when-compile
	 (when ,tellib-test-flag
	   (let ((,val (progn ,@body)))
	     (if (equal ,result ,val)
		 (message "TEST: %s succeeded" ,name)
	       (tellib-error 'error (format "TEST: %s failed: expected %S, got %S"
					    ,name ,result ,val))))))))
  
  (defmacro tellib-test-error (name error-list &rest body)
    "Evaluate BODY at compile time and check if it throws an error as expected.
ERROR-LIST ... a list of acceptable errors.
\(Throw an error if this is not the case.)

Sample usage:
	\(tellib-test-error \"test-add\" '\(some-error error) \(+ 1 \"a\"))
"
    `(eval-when-compile
       (when (fboundp 'condition-case)
	 (if (catch 'exit
	       (condition-case nil
		   (progn ,@body)
		 ,@(mapcar (lambda (err)
			     `(,err (throw 'exit t)))
			   error-list)
		 (t nil)))
	     (message "tellib: Test %s succeeded" ,name)
	   (tellib-error
	    'error
	    (format "tellib: Test %s didn't throw an acceptable error %S"
		    ,name ,error-list))))))
  )
;;test: (setq tellib-test-flag t)
;;test: (tellib-test "test-add-1" 2 (+ 1 1))
;;test: (tellib-test "test-add-2" 3 (+ 1 1))
;;test: (tellib-test-error "test-add-3" '(error) (+ 1 "a"))
;;test: (tellib-test-error "test-add-4" nil (+ 1 "a"))
;;test: (tellib-test-error "test-add-5" '(some-error) (+ 1 "a"))
;;test: (tellib-test-error "test-add-6" '(some-error error) (+ 1 "a"))
;;test: (tellib-test-error "tellib-test-error" '(error)
;;		   (tellib-test-error "test-add-5" '(some-error) (+ 1 "a")))

(defun tellib-not-yet-implemented (feature)
  "Throw an error explaining that FEATURE is not yet implemented."
  (tellib-error 'error "Not yet implemented" feature))



; ------------------------------------------- * Message & Log

(defvar tellib-verbosity 1
  "An integer defining the level of verbosity. 0 means no messages
at all.")

(defun tellib-message (level &rest args)
  "Show a message only if LEVEL is sufficiently low -- i.e. important.
This function can be called in two ways:

\(tellib-message LEVEL &rest ARGS): LEVEL will be tested against
`tellib-verbosity'. ARGS will be passed to `message'.

\(tellib-message LEVEL CLASS FORMAT-STRING &rest ARGS): LEVEL will be
tested against CLASS-verbosity \(or `tellib-verbosity' if
CLASS-verbosity isn't defined). FORMAT-STRING will be prepended with
\"CLASS: \".

A level of 0 means: log always.
"
  (let* ((class     (when (symbolp (car args))
		      (car args)))
	 (class$    (symbol-name (or class 'tellib)))
	 (args      (if class
			(append (list (concat (upcase-initials class$)
					      ": " (cadr args)))
				(cddr args))
		      args))
	 (name      (intern-soft (concat class$ "-verbosity")))
	 (verbosity (if name
			(eval name)
		      tellib-verbosity)))
    (when (<= level (abs verbosity))
      (apply 'message args)))
  nil)
;;test: (tellib-message 1 "test")
;;test: (tellib-message 2 "test")
;;test: (tellib-message 1 'tellib "test %s" 1)
;;test: (tellib-message 2 'tellib "test")

(eval-when-compile
  (defvar tellib-logged-messages nil
    "A list of logged message classes.")

  (defmacro tellib-define-logged-messages (class &rest types)
    "Define CLASS-logged-messages comprising TYPES."
    ;;(message "DEBUG: %s" (intern (format "%s-logged-messages"  (eval class))))
    `(eval-when-compile
       (defconst ,(intern (format "%s-logged-messages"  (eval class)))
	 (quote ,(mapcar #'eval types))
	 "A list of logged message classes.
Created by `tellib-define-logged-messages'.")))
  
  (defmacro tellib-log (class type level message &rest args)
    "Display MESSAGE with ARGS if TYPE is a member of CLASS-logged-messages.

LEVEL has to be less or equal CLASS-verbosity (see `tellib-message'). 
The decision if a message should be logged or not is made during
compilation, i.e. defining log messages throughout your code doesn't
\(shouldn't) hurt efficiency if you set CLASS-logged-messages to nil."
    (let* ((tellib-logged (eval (intern-soft (format "%s-logged-messages"
						     (eval class))))))
      (when (member (eval type) tellib-logged)
	`(tellib-message ,level ,class
			 ,(format "LOG %s: %s" (eval type) message)
			 ,@args))))

  (defmacro tellib-log! (class type message &rest args)
    "Like `tellib-log' with level 0."
    (let* ((tellib-logged (eval (intern-soft (format "%s-logged-messages"
						     (eval class))))))
      (when (member (eval type) tellib-logged)
	`(tellib-message 0 ,class
			 ,(format "LOG %s: %s" (eval type) message)
			 ,@args))))
  (defmacro tellib-log-one (class type message arg)
    "Log ARG and return ARG."
    (tellib-log! class type message args)
    arg)
  )
;;test: (setq tellib-logged-messages '(test))
;;test: (tellib-define-logged-messages 'tellib 'test)
;;test: (tellib-define-logged-messages 'unknown 'test)
;;test: (tellib-log 'tellib 'test 1 "Test")
;;test: (tellib-log 'tellib 'notest 1 "Test")
;;test: (tellib-log! 'tellib 'test "Test")

(defun tellib-info (name)
  "Display NAME's version information."
  (interactive "sLibrary Name: ")
  (let ((v  (eval (intern-soft (concat name "-version"))))
	(hp (eval (intern-soft (concat name "-homepage")))))
    (when (and v hp
	       (y-or-n-p (format "%s v%s: visit homepage? " name v)))
      (browse-url hp))))

(defmacro tellib-with-message-buffer (message &rest body)
  "Display a buffer with MESSAGE and evaluate BODY."
  `(with-temp-buffer
    (pop-to-buffer (current-buffer))
    (delete-other-windows)
    (insert ,message)
    ,@body))
;;test: (tellib-with-message-buffer "Test" (y-or-n-p "ok? "))



; ------------------------------------------- * Documenation

(defun tellib-document (symbol &optional 
			       pre sep post
			       skip-if-undoc skip-if-unimportant
			       predicate
			       reformat-flag)
  "Return a short documentation for SYMBOL.
PRE, SEP, POST ... Formatting options.
SKIP-IF-UNDOC ... Return null string, if the symbol is not documented.
PREDICATE ... Return the documentation only if (PREDICATE SYMBOL) is non-nil.
"
  (when (and (if predicate
		 (funcall predicate symbol)
	       (or (fboundp symbol)
		   (boundp symbol)))
	     (if skip-if-unimportant
		 (not (get symbol 'tellib-unimportant))
	       t))
    (let ((doc (if (fboundp symbol)
		   (documentation symbol)
		 (documentation-property symbol 'variable-documentation))))
      (when (or doc
		(not skip-if-undoc))
	(let* ((sym-def (format "%s" (if (fboundp symbol)
					 (function-arglist symbol)
				       symbol)))
	       (sym-doc (car (split-string-by-char
			      (or doc "not documented")
			      ?\n)))
	       (fmt-def  (if reformat-flag
			     (lambda (x)
			       (tellib-string-fill
				x nil nil
				(make-string (1+ (length (format "%s" symbol))) ? )))
			   #'identity))
	       (fmt-doc  (if reformat-flag
			     (lambda (x)
			       (let ()
				 (tellib-string-fill x)))
			   #'identity)))
	(concat (or pre "")
		(funcall fmt-def sym-def)
		(or sep " :: ")
		(funcall fmt-doc sym-doc)
		(or post "")))))))

(defun tellib-selfdocumentation (regexp &optional predicate skip-if-unimportant)
  "List documentations for symbols matching REGEXP -- see `tellib-document'."
  (concat "\n"
	  (mapconcat (lambda (x)
		       (tellib-document x "" "" "\n" t t predicate t))
		     (apropos-internal regexp) "")))



; ------------------------------------------- * Events

(eval-and-compile
  (if tellib-running-xemacs
      (defun tellib-call-with-event-pos (tellib-fn tellib-event
						   &rest tellib-args)
	"Set current buffer and call FN with the position where EVENT occured.
This will result in \(FN POS . ARGS)."
	(set-buffer (window-buffer (event-window tellib-event)))
	(apply tellib-fn (event-point tellib-event) tellib-args))
    (defun tellib-call-with-event-pos (tellib-fn tellib-event
						 &rest tellib-args)
      "Set current buffer and call FN with the position where EVENT occured.
This will result in \(FN POS . ARGS)."
      (set-buffer (posn-window (event-start tellib-event)))
      (apply tellib-fn (posn-point (event-start tellib-event)) tellib-args))))



; ------------------------------------------- * Files

(defun tellib-directory-files (dir &optional
				   what file-pattern dir-pattern full-name-flag)
  "List files or dirs in DIR.
WHAT ... :dirs or :files.
"
  (cond
   ((file-exists-p dir)
    (let ((files           nil)
	  (dirs            nil)
	  (coll-files-flag (not (equal what ':dirs)))
	  (coll-dirs-flag  (not (equal what ':files)))
	  (get-name (lambda (filename)
		      (if full-name-flag
			  (concat (file-name-as-directory dir) filename)
			filename)))
	  (sort-fn (lambda (a b)
		     (string< (upcase a) (upcase b)))))
      (mapc (lambda (this)
		(cond 
		 ((string-match "^\\.+/$" this)
		  nil)
		 ((and coll-dirs-flag (string-match "[:/\\]$" this))
		  (when (or (not dir-pattern)
			    (string-match dir-pattern this))
		    (setq dirs (append dirs (list (funcall get-name this))))))
		 (coll-files-flag
		  (when (or (not file-pattern)
			    (string-match file-pattern this))
		    (setq files (append files (list (funcall get-name this))))))))
	    (file-name-all-completions "" dir))
      (append (when dirs  (sort (copy-sequence dirs)  sort-fn))
	      (when files (sort (copy-sequence files) sort-fn)))))
   (t
    (tellib-error 'error "Tellib: " dir " does not exist"))))
;;test: (tellib-directory-files "~/" :all "^[^.]" "^[^.]")
;;test: (tellib-directory-files "~/" :all)

(defun tellib-simplify-string (string &optional regexp)
  "Replace suspicious characters in STRING with an underscore."
  (replace-in-string string (or regexp "\\W") "_"))
(defalias 'tellib-make-proper-filename 'tellib-simplify-string)
;;test: (tellib-make-proper-filename "a+b*c/")
;;test: (tellib-make-proper-filename "a+.b* c/" "[. ]")

(defun tellib-remove-redundant-dir-separators (filename)
  "Remove multiples '/' (or whatever) in filename."
  (let ((ps (string directory-sep-char)))
    (replace-in-string filename (concat (regexp-quote ps) "+") ps t)))
;;test: (tellib-remove-redundant-dir-separators "/x///x////x//x///x")
;;test: (let ((directory-sep-char ?\\)) (tellib-remove-redundant-dir-separators "c:\\x\\\\x\\\\\\x"))

(defun tellib-file-name-last-bit (filename)
  "Returns the last bit of FILENAME -- either directory or file."
  (if (file-directory-p filename)
      (file-name-as-directory
       (file-name-nondirectory
	(directory-file-name filename)))
    (file-name-nondirectory filename)))

(defun tellib-file-name-break-up (filename &optional drop-null-elements)
  "Return a list of FILENAME parts.
\"\" at position 0 means: absolute path.
\"\" at the last position means: it's a directory.
If DROP-NULL-ELEMENTS is non-nil, empty strings will be dropped."
  (let ((rv (tellib-split-string-by-char filename directory-sep-char)))
    (if drop-null-elements
	(loop for x in rv
	  when (not (string= x ""))
	  collect x)
      rv)))
;;test: (tellib-file-name-break-up "/d1/d2/filename")
;;test: (tellib-file-name-break-up "/d1/d2/d3/")
;;test: (tellib-file-name-break-up "/d1/d2/d3/" t)

(defun tellib-read-file (filename &optional default)
  "Read FILENAME and return its contents as string.
If FILENAME is not readable, nil or DEFAULT will be returned."
  (if (file-readable-p filename)
      (with-temp-buffer
	(insert-file-contents-literally filename)
	(buffer-string))
    default))




; ------------------------------------------- * Input

(defvar tellib-related-buffers nil
  "A list of related editing buffers.")
(make-variable-buffer-local 'tellib-related-buffers)

(defun tellib-add-related-buffer (buffer &optional parent-buffer)
  "Add BUFFER to `tellib-related-buffers'."
  (save-excursion
    (when parent-buffer
      (set-buffer parent-buffer)
      (add-to-list 'tellib-related-buffers buffer))))

(defun tellib-close-related-buffers ()
  "Close related buffers."
  (mapc #'(lambda (this)
	    (kill-buffer this))
	tellib-related-buffers))

(defmacro tellib-edit-in-buffer (text &optional
				      message mode-fn keymap-var on-exit-fn)
  "Edit TEXT in a temporary buffer -- use `tellib-edit-in-buffer*' if possible."
  `(with-temp-buffer
     (pop-to-buffer (current-buffer))
     (delete-other-windows)
     (insert ,text)
     (when ,mode-fn
       (funcall ,mode-fn))
     (goto-char (point-min))
     (let ((exit-temp-buffer (lambda (&optional buffer)
			       (interactive)
			       (when ,on-exit-fn
				 (funcall ,on-exit-fn))
			       (exit-recursive-edit)
			       ;;(throw 'exit nil)
			       ))
	   (map (or ,keymap-var (make-sparse-keymap))))
       (define-key map [(control c) (control c)] exit-temp-buffer)
       (define-key map [(control x) k] exit-temp-buffer)
       (unless ,keymap-var (use-local-map map))
       (message "Exit with C-c C-c. %s" (or ,message ""))
       (flet ((kill-buffer (buffer)
		(funcall exit-temp-buffer)))
	 (recursive-edit)))
     (buffer-string)))
;;test: (tellib-edit-in-buffer "Test")

(defun* tellib-edit-in-buffer*
  (title text on-exit-function
	 &key
	 ((:message message) "")
	 ((:mode mode-fn))
	 ((:keymap keymap-var))
	 ((:show-other-windows show-other-windows))
	 ((:dont-replace-text dont-replace-text))
	 ((:write-buffer write-buffer-function) #'insert))
  "Edit TEXT in a buffer called TITLE.
Eval ON-EXIT-FUNCTION when killing the buffer or pressing C-c C-c.
KEY-ARGS can be one of these:
:message STRING ... A message to be display when showing the buffer.
:mode MODE-SETTING-FUNCTION ... A function that sets up the proper mode.
:keymap KEYMAP-VARIABLE ... The keymap that should be used.
:show-other-windows BOOLEAN ... Don't delete other windows.
:dont-replace-text BOOLEAN ... Don't replace the text if the buffer with
TITLE already exists.
:write-buffer FUNCTION ... A function called to insert TEXT in the
buffer. (Defaults to `insert'.)
"
  (let ((buf (current-buffer))
	(map  (or keymap-var (make-sparse-keymap)))
	(reedit-flag (get-buffer title))
	(pop-up-windows show-other-windows))
    (pop-to-buffer title)
    (tellib-add-related-buffer (current-buffer) buf)
    (make-local-variable 'kill-buffer-hook)
    (setq kill-buffer-hook nil)
    (add-hook 'kill-buffer-hook on-exit-function)
    (unless (and reedit-flag dont-replace-text)
      (delete-region (point-min) (point-max))
      (funcall write-buffer-function text))
    (goto-char (point-min))
    (when mode-fn
      (funcall mode-fn))
    (define-key map [(control c) (control c)] (lambda () (interactive)
						(kill-buffer nil)))
    (use-local-map map)
    (message "Exit with C-c C-c. %s" message)))
;;test: (setq x "")
;;test: (tellib-edit-in-buffer* "*tmp*" "Test" (lambda () (setq x (buffer-string))))
;;test: (tellib-edit-in-buffer* "*tmp*" "Test" (lambda () (setq x (buffer-string)))
;;			      :dont-replace-text t)
;;test: (tellib-edit-in-buffer* "*tmp*" "Test" #'buffer-string :show-other-windows t)
;;test: (let ((x! (lambda () (setq x (buffer-string)))))
;;  (tellib-edit-in-buffer* "*tmp*" "Test" x!))



; ------------------------------------------- * Lists 

(defmacro tellib-del-from-list (list-var element)
  "Delete ELEMENT from LIST-VAR."
  `(set ,list-var (delete ,element (eval ,list-var))))
;;test: (setq x '(1 2 3 4 1 2 4))
;;test: (tellib-del-from-list 'x 1)

(defmacro tellib-filter-list (tellib-list tellib-cond-fn)
  "Remove all elements not conforming to TELLIB-COND-FN from list TELLIB-LIST.
COND-FN takes one argument: the current element."
  (let ((rv  (gensym "tellib-rv"))
	(elt (gensym "tellib-elt")))
    `(let ((,rv (list)))
       (mapc (lambda (,elt)
	       (when (funcall ,tellib-cond-fn ,elt)
		 (setq ,rv (nconc ,rv (list ,elt)))))
	     ,tellib-list)
       ,rv)))
;;test: (tellib-filter-list '(1 2 3) (lambda (x) (> x 2)))

(defun tellib-sublist (tellib-list tellib-beg &optional tellib-end)
  "Get the sublist of TELLIB-LIST from TELLIB-BEG to TELLIB-END - 1."
  (let ((rv  nil)
	(i   tellib-beg)
	(top (or tellib-end
		 (length tellib-list))))
    (while (< i top)
      (setq rv (append rv (list (nth i tellib-list))))
      (setq i (+ i 1)))
    rv))

(defun tellib-zip (&rest tellib-lists)
  "Zip lists. Turns '\((A1 ...) (A2 ...) ...) into '\((A1 A2 ...) ...)."
  (let ((max nil))
    (mapc #'(lambda (this)
	      (if (and max
		       (/= (length this) max))
		  (tellib-error 'error 
				"tellib-zip: Lists have to be of same length.")
		(setq max (length this))))
	  tellib-lists)
    (let ((rv nil))
      (do ((pos 0 (setq pos (+ pos 1))))
	  ((>= pos max) rv)
	(setq rv (append rv (list (mapcar (lambda (x) (nth pos x))
					  tellib-lists))))))))
;;test: (tellib-zip '(1 2 3))
;;test: (tellib-zip '(1 2 3) '(a b c))
;;test: (tellib-zip '(1 2 3) '(a b c) '(A B C))
;;test: (tellib-zip '(1 2 3) '(a b c) '(A B C D))

(defun tellib-zip-1 (default &rest tellib-lists)
  "Zip lists. Like `tellib-zip' but accepts lists of unequal length
-- i.e. missing elements will be replaces with DEFAULT."
  (let ((max 0))
    (mapc #'(lambda (this)
	      (let ((lt (length this)))
		(when (> lt max)
		  (setq max lt))))
	  tellib-lists)
    (let ((rv nil))
      (do ((pos 0 (setq pos (+ pos 1))))
	  ((>= pos max) rv)
	(setq rv (append rv (list (mapcar (lambda (x)
					    (if (>= pos (length x))
						default
					      (nth pos x)))
					  tellib-lists))))))))
;;test: (tellib-zip-1 'nope '(1 2 3))
;;test: (tellib-zip-1 'nope '(1 2 3) '(a b))
;;test: (tellib-zip-1 'nope '(1 2 3) '(a b) '(A))
;;test: (tellib-zip-1 'nope '(1 2 3) nil '(A B C D))

(defmacro tellib-andmap (tellib-pred &rest tellib-lists)
  "Return non-nil if TELLIB-PRED is true for all elements of TELLIB-LISTS."
  (let ((tellib-this (gensym "tellib-this")))
    `(catch 'failure
       (mapc (lambda (,tellib-this)
	       (unless (apply ,tellib-pred ,tellib-this)
		 (throw 'failure nil)))
	     (tellib-zip ,@tellib-lists))
       t)))
;;test: (tellib-andmap 'equal '(1 2) '(1 2))
;;test: (tellib-andmap 'equal '(1 2) '(1 3))

(defmacro tellib-andmap-1 (tellib-pred tellib-default &rest tellib-lists)
  "Return non-nil if TELLIB-PRED is true for all elements of TELLIB-LISTS.
Missing elements in TELLIB-LILST will be replaced with TELLIB-DEFAULT."
  (let ((tellib-this (gensym "tellib-this")))
    `(catch 'failure
       (mapc (lambda (,tellib-this)
	       (unless (apply ,tellib-pred ,tellib-this)
		 (throw 'failure nil)))
	     (tellib-zip-1 ,tellib-default ,@tellib-lists))
       t)))
;;test: (tellib-andmap-1 'equal nil '(1 2) '(1 2))
;;test: (tellib-andmap-1 'equal nil '(1 2) '(1 3))
;;test: (tellib-andmap-1 'equal t '(1) '(1 t))

(defmacro tellib-ormap (tellib-pred tellib-list)
  "Return SUBLIST of TELLIB-LIST, for which \(TELLIB-PRED (car SUBLIST)) is true."
  (let ((list (gensym "tellib-list"))
	(rv   (gensym "tellib-rv")))
    `(let ((,list ,tellib-list)
	   (,rv   nil))
       (while (and (not (null ,list))
		   (null ,rv))
	 (if (funcall ,tellib-pred (car ,list))
	     (setq ,rv ,list)
	   (setq ,list (cdr ,list))))
       ,rv)))
;;test: (tellib-ormap (lambda (x) (> x 2)) '(1 2 3))
;;test: (tellib-ormap (lambda (x) (> x 2)) nil)

(defmacro tellib-some (tellib-pred tellib-list)
  "Return the value of TELLIB-PRED, if non-nil for an item in TELLIB-LIST."
  (let ((tellib-this (gensym "tellib-this"))
	(tellib-rv   (gensym "tellib-rv")))
    `(catch 'exit
       (mapc (lambda (,tellib-this)
	       (let ((,tellib-rv (funcall ,tellib-pred ,tellib-this)))
		 (when ,tellib-rv
		   (throw 'exit ,tellib-rv))))
	     ,tellib-list)
       nil)))
;(defalias 'tellib-some 'some)
;;test:(let ((tellib-pred 1))
;  (tellib-some (lambda (x) (equal x tellib-pred)) '(0 1 2)))

(defmacro tellib-member (tellib-item tellib-list &rest tellib-keys)
  "A clone of `member*'. At the moment only the :test key is supported."
  (let ((tellib-test (plist-get tellib-keys ':test (function equal)))
	(tellib-this (gensym "tellib-this")))
    `(tellib-ormap (lambda (,tellib-this)
		     (funcall ,tellib-test ,tellib-item ,tellib-this)) 
		   ,tellib-list)))
;(let (((tellib-member 1 '(0 1 2 3) :test (lambda (x y) (= x y)))
;(defalias 'tellib-member 'member*)

(defmacro tellib-mapcart (tellib-fn tellib-list)
  "Similar to `mapcar' but drops nil values.
Apply TELLIB-FN to each element of TELLIB-LIST. If the result is
non-nil, add it to the list of return values."
  (let ((tellib-rv   (gensym "tellib-rv"))
	(tellib-this (gensym "tellib-this"))
	(tellib-tmp  (gensym "tellib-tmp")))
    `(let (,tellib-rv)
       (mapc (lambda (,tellib-this)
	       (let ((,tellib-tmp (funcall ,tellib-fn ,tellib-this)))
		 (when ,tellib-tmp
		   (setq ,tellib-rv (append ,tellib-rv (list ,tellib-tmp))))))
	     ,tellib-list)
       ,tellib-rv)))
;;test: (tellib-mapcart #'identity '(1 nil 2))

(defmacro tellib-mappend (tellib-fn tellib-list)
  "Map TELLIB-FN (returning lists) on TELLIB-LIST and append results."
  (let ((tellib-rv (gensym "tellib-rv"))
	(tellib-this (gensym "tellib-this")))
    `(let (,tellib-rv)
       (mapc (lambda (,tellib-this)
	       (setq ,tellib-rv
		     (append ,tellib-rv (funcall ,tellib-fn ,tellib-this))))
	     ,tellib-list)
       ,tellib-rv)))
;;test: (tellib-mappend #'identity '((1 2) nil (3 4)))


; ------------------------------------------- * Property Lists

(eval-and-compile
  (if (fboundp 'valid-plist-p)
      (defalias 'tellib-valid-plist-p 'valid-plist-p)
    (defun tellib-valid-plist-p (tellib-plist)
      "XEmacs' valid-plist-p mimicry."
      (= (mod (length tellib-plist) 2) 0))))

(defun tellib-plist-merge (plist1 plist2)
  "Insert PLIST 1 into PLIST2."
  (let ((rv plist2))
    (loop for i to (1- (length plist1)) by 2 do
      (let ((key (nth i plist1))
	    (val (nth (1+ i) plist1)))
	(setq rv (plist-put rv key val))))
    rv))
;;test: (tellib-plist-merge '(1 "a" 2 "b") '(1 "" 2 "" 3 ""))

(defun tellib-plist-mapkeys (function keys &rest plists)
  "Map FUNCTION on the KEYS in PLISTS and append the values to a list.
The function is called with KEY, VAL1 ... VALN as arguments."
  (loop for key in keys append
    (apply function key
	   (mapcar (lambda (plist) (plist-get plist key)) plists))))
;;test: (tellib-plist-mapkeys (lambda (k x y) `(,k (,x ,y))) '(b) '(a 1 b 2) '(a a b b))



; ------------------------------------------- * Lax Property Lists

(eval-and-compile
  (if (fboundp 'lax-plist-get)
      (defalias 'tellib-lax-plist-get 'lax-plist-get)
    (defun tellib-lax-plist-get (lax-plist property &optional default)
      "Emacs support for XEmacs' lax-plists."
      (if (tellib-valid-plist-p lax-plist)
	  (let ((this (member property lax-plist)))
	    (if this
		(if (= (mod (length this) 2) 0)
		    (cadr this)
		  (tellib-lax-plist-get (cdr this) property default))
	      default))
	(tellib-error 'malformed-property-list
		      'tellib-lax-plist-get lax-plist))))
  
  (if (fboundp 'lax-plist-put)
      (defalias 'tellib-lax-plist-put 'lax-plist-put)
    (defun tellib-lax-plist-put (lax-plist property value)
      "Emacs support for XEmacs' lax-plists."
      (if (tellib-valid-plist-p lax-plist)
	  (let ((this (member property lax-plist)))
	    (if this
		(progn
		  (if (= (mod (length this) 2) 0)
		      (setcdr this (cons value (cddr this)))
		    (setcdr this (tellib-lax-plist-put (cdr this)
						       property value)))
		  lax-plist)
	      (append (list property value) lax-plist)))
	(tellib-error 'malformed-property-list
		      'tellib-lax-plist-put lax-plist)))))



; ------------------------------------------- * Association Lists

(defun tellib-alist-get (alist key &optional default car-flag)
  "Get KEY's value in the association list ALIST.
Return DEFAULT if not found.  Return \(car value) if CAR-FLAG is non-nil."
  (let* ((elt (assoc key alist)))
    (cond
     (elt
      (if car-flag
	  (cadr elt)
	(cdr elt)))
     (default default)
     (t nil))))

(defun tellib-alist-set (alist key &rest values)
  "Replace KEY's value with VALUES in ALIST or append (KEY . VALUES) to ALIST."
  (let ((this (assoc key alist)))
    (if this
	(progn
	  (setcdr this values)
	  alist)
      (append alist (list (cons key values))))))
;;test: (tellib-alist-set '(("a" 1) ("b" 2)) "a" 3)
;;test: (tellib-alist-set '(("a" 1) ("b" 2)) "a" 3 4 5)
;;test: (tellib-alist-set '(("a" 1) ("b" 2)) "x" 3)
;;test: (tellib-alist-set nil "x" 3)

(defun tellib-alist-setcdr (alist key list)
  "Replace KEY's cdr with LIST in ALIST or append (KEY . LIST) to ALIST."
  (if (listp list)
      (let ((this (assoc key alist)))
	(if this
	    (progn
	      (setcdr this list)
	      alist)
	  (append alist `((,key . ,list)))))
    (tellib-error 'error "tellib-alist-setcdr: not a list" list)))
;;test: (tellib-alist-setcdr '(("a" 1) ("b" 2)) "a" 3) -> incorrect
;;test: (tellib-alist-setcdr '(("a" 1) ("b" 2)) "a" '(3 4 5))
;;test: (tellib-alist-setcdr '(("a" 1) ("b" 2)) "x" 3) -> incorrect
;;test: (tellib-alist-setcdr nil "x" 3) -> incorrect
;;test: (tellib-alist-setcdr nil "x" '(3))

(defun tellib-alist-p (alist)
  "Return non-nil if ALIST appears to be a proper association list."
  (tellib-andmap #'listp alist))
;;test: (tellib-alist-p nil)
;;test: (tellib-alist-p '(nil))
;;test: (tellib-alist-p '(1 nil))
;;test: (tellib-alist-p '((a 1) (b 2)))
;;test: (tellib-alist-p '((a 1) b 2))



; ------------------------------------------- * Overlays, extents

(defun tellib-overlay-dump (overlay &optional ignore)
  "Return a list representing OVERLAY."
  (list :start (overlay-start overlay)
	:end   (overlay-end overlay)
	:props (let ((prps (overlay-properties overlay)))
		 (mapc #'(lambda (this)
			   (setq prps (plist-remprop prps this)))
		        ignore)
		 prps)))

(defun tellib-overlay-collect* (symbols &optional 
					buffer
					overlays
					use-these-overlay-flag
					predicate)
  "Return a list of overlays with one of SYMBOLS being non-nil.
Collect from OVERLAYS if provided.
Use PREDICATE \(default is \(overlay-get OVERLAY SYMBOL)) if provided."
  (save-excursion
    (when buffer
      (set-buffer buffer))
    (let ((pred (or predicate
		    (lambda (overlay symbol)
		      (overlay-get overlay symbol))))
	  (ols (if (or use-these-overlay-flag overlays)
		   overlays
		 (let ((all-ol  (overlay-lists)))
		   (append (car all-ol) (cdr all-ol))))))
      (tellib-filter-list ols
			  (lambda (this)
			    (tellib-ormap (lambda (sym)
					    (funcall pred this sym))
					  symbols))))))
;;test: (tellib-overlay-collect* '(excerpt-reference))

(defun tellib-overlay-collect (symbols &optional buffer overlays ignore)
  "Return a list of dumped overlays with one of SYMBOLS being non-nil.
Collect from OVERLAYS if provided.
IGNORE these properties if provided."
  (mapcar (lambda (x) (tellib-overlay-dump x ignore))
	  (tellib-overlay-collect* symbols buffer overlays)))
;;test: (tellib-overlay-collect '(excerpt-reference))


(defface tellib-unknown-face
  '((t (:background "lightred")))
  "Face for marking coded text.")

(defun tellib-overlay-restore (dumped-overlays &optional buffer)
  "Restore all overlays in DUMPED-OVERLAYS
-- as returned by `tellib-overlay-collect'.

If the property 'tellib-restore-function exists, its value is called as
function with the overlay as parameter. A restore function must already
be defined/loaded or marked as autoload.

You should take care that all data needed for restoring an overlay is
already defined. This function takes care of unknown faces and tries to
continue if setting other properties fails -- although this can lead to
incorrect settings.
"
  (when dumped-overlays
    (save-excursion
      (let ((buf (or buffer (current-buffer))))
	(mapc
	 #'(lambda (this)
	     (let* ((ol    (make-overlay (plist-get this :start)
					 (plist-get this :end)
					 buf))
		    (props (plist-get this :props))
		    (count 0)
		    (max   (length props)))
	       (while (< count max)
		 (let ((prop (nth count props))
		       (val  (nth (+ count 1) props)))
		   (condition-case nil
		       (when (cond
			      ((equal prop 'face)
			       (unless (find-face val)
				 (make-face val)
				 (set-face-background val "red")
				 (tellib-message
				  1 'tellib
				  "Unknown face '%s' is marked with red background" 
				  val))
			       t)
			      (t
			       t))
			 (overlay-put ol prop val))
		     (error (tellib-message 1 'tellib
					    "Restoring overlay property failed %s %s"
					    prop val)
			    nil))
		   (setq count (+ count 2))))
	       (let ((rf (overlay-get ol 'tellib-restore-function)))
		 (when rf
		   (if (fboundp rf)
		       (condition-case nil
			   (funcall rf ol)
			 (error (tellib-message 1 'tellib
						"Restore overlay function failed: %s"
						rf)))
		     (tellib-message 1 'tellib "Unknown restore function `%s'" rf))))
	       ))
	 dumped-overlays)))))

(defun tellib-overlay-change-size (dx &optional symbols overlay)
  "Make an overlay DX characters larger/smaller.
The overlay used is either OVERLAY or the top one with one of SYMBOLS
being non-nil. Either SYMBOLS of OVERLAY has to be provided. 
If overlays start is greater or equal its end, the
overlay will be deleted."
  (let* ((ol  (or overlay
		  (car (tellib-overlay-collect* symbols nil
						(overlays-at (point)) t))))
	 (beg (overlay-start ol))
	 (end (+ (overlay-end ol) dx)))
    (if (>= beg end)
	(delete-overlay ol)
      (move-overlay ol beg end))))

(defun tellib-overlay-move (dx dy &optional symbols overlay)
  "Move an overlay to DX/DY from the current position.
The overlay used is either OVERLAY or the top one with one of SYMBOLS
being non-nil. Either SYMBOLS of OVERLAY has to be provided.
Returns the new starting position of overlay."
  (let* ((ol   (or overlay
		   (car (tellib-overlay-collect* symbols nil
						 (overlays-at (point)) t))))
	 (beg0 (overlay-start ol))
	 (rx   (- (point) beg0))
	 (beg  (+ (if dy
		      (+ (point-at-bol dy) (- beg0 (point-at-bol)))
		    beg0)
		  dx))
	 (end (- (overlay-end ol) (- beg0 beg))))
    (move-overlay ol beg end)
    (goto-char (+ beg rx))))



; ------------------------------------------- * RegExp, search & find

(defun tellib-re-search (regexp &optional
				case-sensitive
				backward-flag)
  "Search for REGEXP while taking care of `case-fold-search'.

CASE-SENSITIVE can be t, nil, or 'default \(don't change the value of
`case-fold-search').
If BACKWARD-FLAG is non-nil, the search will proceed in reverse direction.
"
  (let ((case-fold-search (if (eq case-sensitive 'default)
			      case-fold-search
			    (not case-sensitive))))
    (if backward-flag
	(re-search-backward regexp nil t)
      (re-search-forward regexp nil t))))



; ------------------------------------------- * Work on current buffer

(defun* tellib-update-local-variable-def (&optional var val &key
						    val-flag
						    dont-replace
						    if-different
						    set-var
						    add
						    ignore-read-only
						    no-error-if-read-only)
  "Set local VAR's definition to VAL.
OPTIONAL-ARGS may include the following keys plus boolean value:
:val-flag              ... val was set
:dont-replace          ... Don't replace an existing definition
:if-different          ... Replace the definition only if VAR has changed
:set-var               ... Also set VAR to VAL
:add                   ... Always add a new definition
:ignore-read-only      ... Temporarily set the `buffer-read-only' to nil
:no-error-if-read-only ... Show a message if read-only, but *don't* throw an error

Example: \(tellib-update-local-variable-def 'x 1 :if-different t)
"
  (interactive)
  (let* ((var (or var
		  (intern
		   (completing-read "Variable: " obarray
				    nil nil nil 'variable-history))))
	 (val (or val
		  val-flag
		  (read-expression "Expression: "
				   (when (boundp var) (format "%S" (eval var)))))))
    (cond
     ((and buffer-read-only
	   (not ignore-read-only))
      (let ((msg (format "Buffer is read only; can't set %s to %S" 
			 var val)))
	(if no-error-if-read-only
	    (tellib-message 1 'properties msg)
	  (tellib-error 'error (concat "tellib: " msg)))))
     ((or (not if-different)
	  (not (boundp var))
	  (not (equal (eval var) val)))
      (let ((buffer-read-only nil))
	(save-excursion
	  (goto-char (point-max))
	  (let* ((begrex (concat "^" comment-start 
				 "[" comment-start " ]+Local Variables:"))
		 (begloc "Local Variables:")
		 (endloc "End:")
		 (lvs    (let ((here (tellib-re-search begrex t t)))
			   (when here
			     (goto-char here)
			     (tellib-re-search begloc t))))
		 (pre    (if lvs
			     (progn
			       (goto-char (match-beginning 0))
			       (buffer-substring (point-at-bol) (point)))
			   (concat comment-start comment-start comment-start " ")))
		 (post   (if lvs
			     (progn
			       (goto-char (match-end 0))
			       (buffer-substring (point) (point-at-eol)))
			   (concat " " comment-end comment-end comment-end))))
	    (let* ((lvss (concat pre begloc post))
		   (lves (concat pre endloc post))
		   (lve  (when lvs
			   (goto-char lvs)
			   (tellib-re-search (regexp-quote lves) t))))
	      (if lve
		  (progn
		    (goto-char lvs)
		    (end-of-line))
		(let (p)
		  (goto-char (point-max))
		  (newline)
		  (insert lvss)
		  (setq p (point))
		  (newline)
		  (insert lves)
		  (newline)
		  (goto-char p)))
	      (let* ((sfss (concat "^"
				   (regexp-quote pre)
				   (format "%s:\\W*\\(.*\\)"
					   (regexp-quote (if (stringp var)
							     var
							   (symbol-name var))))
				   (regexp-quote post)
				   "$"))
		     (sfsn (concat pre
				   (format "%s: %S" var val)
				   post))
		     (sfs  (when (and (not add) lve)
			     (tellib-re-search sfss t))))
		(if sfs
		    (unless dont-replace
		      (replace-match sfsn t t))
		  (newline)
		  (insert sfsn))))))
	(when set-var
	  (set var val)))))))
;;test: (tellib-update-local-variable-def 'var "valy")
;;test: (tellib-update-local-variable-def 'var "valx" :add t)
;;test: (tellib-update-local-variable-def 'auto-recompile 1)
;;test: (tellib-update-local-variable-def 'auto-recompile 2)
;;test: (tellib-update-local-variable-def 'auto-recompile 2 :dont-replace t)
;;test: (tellib-update-local-variable-def 'auto-recompile 3 :ignore-read-only t)
;;test: (tellib-update-local-variable-def 'auto-recompile 3 :no-error-if-read-only t)

(defun tellib-set-file-variable (&rest dont-replace-flag)
  "Set a file local variable."
  (interactive "P")
  (let* ((var (read-from-minibuffer "Variable: " nil nil #'intern))
	 (val (read-from-minibuffer "Value: "
				    (format "%S" (when (boundp var) (eval var)))
				    nil
				    (lambda (x) (car (read-from-string x)))))
	 (optional-args (when dont-replace-flag
			    '(:dont-replace t))))
    (apply #'tellib-update-local-variable-def var val optional-args)))



; ------------------------------------------- * String, Text etc.

(defun tellib-quote (txt)
  "Return TXT in quotes."
  (concat "\"" txt "\""))

(defun tellib-string-count (string regexp)
  "Count occurances of REGEXP in STRING."
  (let ((pos   0)
	(count 0))
    (while (string-match regexp string pos)
      (setq count (+ count 1))
      (setq pos   (match-end 0)))
    count))
;;test: (tellib-string-count "abcabc" "x")
;;test: (tellib-string-count "abcabc" "a")
;;test: (tellib-string-count "abcabc" "[abc]+")

(eval-and-compile
  (if tellib-running-xemacs
      (defalias 'tellib-split-string-by-char 'split-string-by-char)
    (defmacro tellib-split-string-by-char (string sepchar)
      "Split STRING into a list of substrings originally separated by SEPCHAR."
      `(split-string ,string (regexp-quote (char-to-string ,sepchar))))))

(defun tellib-replace-args (string args-alist &optional escape-char)
  "Replace args-alist in string. 

ARGS-ALIST is an association list with the form '\(\(SHORTCUT
REPLACEMENT) ...). A shortcut may be any string except \"§\".

The default for ESCAPE-CHAR is '%'."
  (let* ((esc (or escape-char ?\%))
	 (rv  (replace-in-string string (string esc esc) (string esc ?\§))))
    (mapc #'(lambda (this)
	      (let ((sc (nth 0 this))
		    (rs (nth 1 this)))
		(setq rv (replace-in-string rv (format "%c%s" esc sc) rs t))))
	  args-alist)
    (replace-in-string rv
		       (string esc ?\§)
		       (string esc)
		       t)))
;;test: (tellib-replace-args "test %x" '(("x" "0^0")))
;;test: (tellib-replace-args "test %x" '(("x" "0\\10")))

(defun tellib-string-fill (string &optional left-col right-col prefix)
  "Fill STRING using `fill-region'. FILL-STRING defaults to \"\\n\"."
  (with-temp-buffer
    (insert string)
    (let ((fill-column (or right-col fill-column))
	  (left-margin (or left-col  left-margin))
	  (fill-prefix (or prefix fill-prefix)))
      (fill-region (point-min) (point-max)))
    (buffer-string)))


(defun tellib-string-trim (string &optional dont-trim-left dont-trim-right 
				  remove-text-properties-flag)
  "Lose leading and trailing whitespace.
Based on `bbdb-string-trim'."
  (if (and (not dont-trim-left)
	   (string-match "^\\W+" string))
      (setq string (substring string (match-end 0))))
  (if (and (not dont-trim-right)
	   (string-match "\\W$" string))
      (setq string (substring string 0 (match-beginning 0))))
  (when remove-text-properties-flag
    ;; This is not ideologically blasphemous.  It is a bad function to
    ;; use on regions of a buffer, but since this is our string, we can
    ;; do whatever we want with it. --Colin [in `bbdb-string-trim']
    (set-text-properties 0 (length string) nil string))
  string)



; ------------------------------------------- * Variables

(defun tellib-scan-variables (trunc &optional beg end buffer)
  "Scan variables TRUNC-[BEG-END] and combine their values to a list.
BEG (default=1) and END (default=infinit) are numbers."
  (let ((count  (or beg 1))
	(end    (or end nil))
	(rv     nil)
	(varlist (buffer-local-variables buffer))
	(trunc$ (if (stringp trunc)
		    trunc
		  (symbol-name trunc))))
    (catch 'exit
      (while (or (null end)
		 (<= count end))
	(let ((this (intern-soft (format "%s-%s" trunc$ count))))
	  (if this
	      (setq count (+ count 1)
		    rv    (append rv (list (cdr (assoc this varlist)))))
	    (throw 'exit nil)))))
    rv))
;;test: tellib-scan-test-1, tellib-scan-test-2
;;test: (tellib-scan-variables 'tellib-scan-test)     -> ("a" "b")
;;test: (tellib-scan-variables 'tellib-scan-test 1 1) -> ("a")
;;test: (tellib-scan-variables 'tellib-scan-test 3 3) -> nil



; ------------------------------------------- * Version check & update

(defun tellib-version-check-p (version-string required-string)
  "Return non-nil if VERSION-STRING satisfies REQUIRED-STRING.
A version string has the form \"MAJOR\", \"MAJOR.MINOR\", or
\"MAJOR.MINOR.MICRO\" etc.

A version number can be negativ or include a \"pre\" tag.

Examples:
	\(tellib-version-check-p \"1.2.-99\"  \"1.2.0\") -> nil
	\(tellib-version-check-p \"1.2.pre1\" \"1.2.0\") -> nil
	\(tellib-version-check-p \"1.2.pre2\" \"1.2.pre1\") -> t
"
  (let* ((mapfn (lambda (x)
		  (if (and (> (length x) 3)
			   (equal (substring x 0 3) "pre"))
		      (- (/ 1 (string-to-int (substring x 3))))
		    (string-to-int x))))
	 (vl    (mapcar mapfn
			(tellib-split-string-by-char version-string ?\.)))
	 (rl    (mapcar mapfn
			(tellib-split-string-by-char required-string ?\.))))
    (catch 'exit
      (tellib-andmap-1 (lambda (x y)
			 (cond
			  ((or (not y) (> x y))
			   (throw 'exit t))
			  ((or (not x) (< x y))
			   (throw 'exit nil))
			  (t
			   t)))
		       nil vl rl))))
;;test: (tellib-version-check-p "1" "1") -> t
;;test: (tellib-version-check-p "1" "2") -> nil
;;test: (tellib-version-check-p "2" "1") -> t
;;test: (tellib-version-check-p "1.1" "2.0") -> nil
;;test: (tellib-version-check-p "2.0" "1.1") -> t
;;test: (tellib-version-check-p "1.1" "2") -> nil
;;test: (tellib-version-check-p "2" "1.1") -> t
;;test: (tellib-version-check-p "1.3" "1.2") -> t
;;test: (tellib-version-check-p "1.2.-99" "1.2.0") -> nil
;;test: (tellib-version-check-p "1.2.pre1" "1.2.0") -> nil
;;test: (tellib-version-check-p "1.2.pre1" "1.2.pre2") -> nil
;;test: (tellib-version-check-p "1.2.pre2" "1.2.pre1") -> t

(defmacro tellib-version-check (name version-string required-string)
  "Throw an error if VERSION-STRING doesn't fit REQUIRED-STRING."
  `(eval-when-compile
     (unless (tellib-version-check-p ,version-string ,required-string)
       (tellib-error
	'error
	(format "excerpt: %s is v%s, but at least v%s is required"
		,name ,version-string ,required-string)))))

(defmacro tellib-version-check-with-name (package-name required-string)
  "Throw an error if PACKAGE-NAME-version doesn't fit REQUIRED-STRING.
PACKAGE-NAME is a string."
  `(tellib-version-check ,package-name
			 (eval (intern-soft (concat ,package-name "-version")))
			 ,required-string))

(defmacro tellib-require (package required-string)
  "Require a package and check if the version is okay."
  `(progn
     (require ,package)
     (eval-and-compile
       (tellib-version-check-with-name (symbol-name ,package) ,required-string))))



; ------------------------------------------- * Features

(defvar tellib-post-provide-hooks nil
  "A plist of hooks to be run after providing a certain feature.")

(defun tellib-define-provide-hook (feature &rest hooks)
  "Add FEATURE's post-provide HOOKS to `tellib-post-provide-hooks'."
  (let ((o (assoc feature tellib-post-provide-hooks)))
    (loop for x in (nreverse hooks) do
      (unless (member x o)
	(setq o (cons x o))))
    (setq tellib-post-provide-hooks (plist-put tellib-post-provide-hooks feature o))))

(defadvice provide (after tellib-run-post-provide-hooks)
  "Run hooks defined by `tellib-define-provide-hook'."
  (let ((hooks (plist-get tellib-post-provide-hooks feature)))
    (loop for hook in hooks do
      (funcall hook))
    (setq tellib-post-provide-hooks
	  (plist-put tellib-post-provide-hooks feature nil))))



; ------------------------------------------- * Setup

(defvar tellib-installation-requests nil
  "An plist of libraries and who demanded their installation.")

(defun tellib-installer (package-name requesting-library
				      &optional top-install-flag)
  "Call LIBRARY-install and add REQUESTING-LIBRARY to `tellib-installation-requests'.
PACKAGE-NAME ... a symbol or a list of symbol.
TOP-INSTALL-FLAG ... If non-nil, the requesting library will be markes,
so that it doesn't get uninstalled automatically.
"
  (when top-install-flag
    (tellib-installer requesting-library '*main*))
  (if (listp package-name)
      (mapc #'(lambda (this)
		(tellib-installer this requesting-library))
	    package-name)
    (let ((inst (intern-soft (concat (symbol-name package-name) "-install"))))
      (if (fboundp inst)
	  (let ((ir (plist-get tellib-installation-requests package-name)))
	    (setq tellib-installation-requests
		  (plist-put tellib-installation-requests
			     package-name
			     (cons requesting-library ir)))
	    (unless ir
	      (funcall inst)))
	(tellib-error 'error "tellib: No installer for" package-name)))))

(defun tellib-uninstaller (package-name requesting-library
					&optional top-uninstall-flag)
  "Call LIBRARY-uninstall
and remove REQUESTING-LIBRARY from `tellib-installation-requests'.
PACKAGE-NAME ... a symbol or a list of symbol.
TOP-UNINSTALL-FLAG ... If non-nil, remove *main* reference to REQUESTING-LIBRARY.
"
  (when top-uninstall-flag
    (tellib-uninstaller requesting-library '*main*))
  (if (listp package-name)
      (mapc #'(lambda (this)
		(tellib-uninstaller this requesting-library))
	    package-name)
    (let ((uninst (intern-soft (concat (symbol-name package-name) "-uninstall"))))
      (if (fboundp uninst)
	  (let ((ir (delete requesting-library
			    (plist-get tellib-installation-requests
				       package-name))))
	    (if ir
		(setq tellib-installation-requests
		      (plist-put tellib-installation-requests package-name ir))
	      (funcall uninst)))
	(tellib-error 'error "tellib: No uninstaller for" package-name)))))
;;(defun tellib-test-install () (message "install"))
;;(defun tellib-test-uninstall () (message "uninstall"))
;;test: (tellib-installer 'tellib-test 'unknown)
;;test: (tellib-installer 'tellib-test 'tellib)
;;test: (tellib-uninstaller 'tellib-test 'unknown)
;;test: (tellib-uninstaller 'tellib-test 'tellib)

(defun tellib-install ()
  "Install tellib's hooks etc."
  (ad-activate-regexp "^tellib-")
  (add-hook 'kill-buffer-hook #'tellib-close-related-buffers))

(defun tellib-uninstall ()
  "Deinstall tellib's hooks etc."
  (ad-disable-regexp "^tellib-")
  (remove-hook 'kill-buffer-hook #'tellib-close-related-buffers))

;;(tellib-install)
;;(tellib-uninstall)


(provide 'tellib)

;;; TELLIB.EL ends here

;;; Local Variables: ***
;;; file-properties-flag: t ***
;;; auto-recompile: 3 ***
;;; time-stamp-format:"%y-%02m-%02d" ***
;;; tellib-scan-test-1:"a" ***
;;; tellib-scan-test-2:"b" ***
;;; End: ***
