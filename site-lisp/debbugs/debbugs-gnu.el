;;; debbugs-gnu.el --- interface for the GNU bug tracker  -*- lexical-binding:t -*-

;; Copyright (C) 2011-2017 Free Software Foundation, Inc.

;; Author: Lars Magne Ingebrigtsen <larsi@gnus.org>
;;         Michael Albinus <michael.albinus@gmx.de>
;; Keywords: comm, hypermedia, maint
;; Package: debbugs

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This package provides an interface to bug reports which are located
;; on the GNU bug tracker debbugs.gnu.org.  Its main purpose is to
;; show and manipulate bug reports from Emacs, but it could be used
;; also for other GNU projects which use the same bug tracker.

;; If you have `debbugs-gnu.el' in your load-path, you could enable
;; the bug tracker commands by the following lines in your ~/.emacs
;;
;;   (autoload 'debbugs-gnu "debbugs-gnu" "" 'interactive)
;;   (autoload 'debbugs-gnu-search "debbugs-gnu" "" 'interactive)
;;   (autoload 'debbugs-gnu-usertags "debbugs-gnu" "" 'interactive)
;;   (autoload 'debbugs-gnu-patches "debbugs-gnu" "" 'interactive)
;;   (autoload 'debbugs-gnu-bugs "debbugs-gnu" "" 'interactive)

;; The bug tracker is called interactively by
;;
;;   M-x debbugs-gnu

;; It asks for the severities, for which bugs shall be shown. This can
;; be either just one severity, or a list of severities, separated by
;; comma.  Valid severities are "serious", "important", "normal",
;; "minor" or "wishlist".  Severities "critical" and "grave" are not
;; used, although configured on the GNU bug tracker.  If no severity
;; is given, all bugs are selected.

;; There is also the pseudo severity "tagged".  When it is used, the
;; function will ask for user tags (a comma separated list), and shows
;; just the bugs which are tagged with them.  In general, user tags
;; shall be strings denoting to subprojects of the package, like
;; "cedet" or "tramp" of the package "emacs".  If no user tag is
;; given, locally tagged bugs are shown.

;; If a prefix is given to the command, more search parameters are
;; asked for, like packages (also a comma separated list, "emacs" is
;; the default), whether archived bugs shall be shown, and whether
;; closed bugs shall be suppressed from being retrieved.

;; Another command is
;;
;;   M-x debbugs-gnu-search

;; It behaves like `debbugs-gnu', but asks at the beginning for a
;; search phrase to be used for full text search.  Additionally, it
;; asks for key-value pairs to filter bugs.  Keys are as described in
;; `debbugs-get-status', the corresponding value must be a regular
;; expression to match for.  The other parameters are as described in
;; `debbugs-gnu'.  Usually, there is just one value except for the
;; attribute "date", which needs two arguments specifying a period in
;; which the bug has been submitted or modified.

;; The bug reports are downloaded from the bug tracker.  In order to
;; not generate too much load of the server, up to 500 bugs will be
;; downloaded at once.  If there are more hits, several downloads will
;; be performed, until all bugs are retrieved.

;; These default values could be changed also by customer options
;; `debbugs-gnu-default-severities', `debbugs-gnu-default-packages'
;; and `debbugs-gnu-default-suppress-bugs'.

;; The commands create a page of bug lists.  Every bug is shown in one
;; line, including the bug number, the status (combining merged bug
;; numbers, keywords and severities), the name of the submitter, and
;; the title of the bug.  On every bug line you could apply the
;; following actions by the following keystrokes:

;;   RET: Show corresponding messages in Gnus/Rmail
;;   "C": Send a control message
;;   "t": Mark the bug locally as tagged
;;   "b": Show bugs this bug is blocked by
;;   "B": Show bugs this bug is blocking
;;   "d": Show bug attributes

;; Furthermore, you could apply the global actions

;;   "g": Rescan bugs
;;   "q": Quit the buffer
;;   "s": Toggle bug sorting for age or for state
;;   "x": Toggle suppressing of bugs
;;   "/": Display only bugs matching a string
;;   "R": Display only bugs blocking the current release
;;   "w": Display all the currently selected bug reports

;; When you visit the related bug messages in Gnus or Rmail, you could
;; also send control messages by keystroke "C".

;; In the header line of every bug list page, you can toggle sorting
;; per column by selecting a column with the mouse.  The sorting
;; happens as expected for the respective column; sorting in the Title
;; column is depending on whether you are the owner of a bug.

;; Another approach for listing bugs is calling the command
;;
;;   M-x debbugs-gnu-usertags

;; This command shows you all existing user tags for the packages
;; defined in `debbugs-gnu-default-packages'.  A prefix for the
;; command allows you to use other package names, or an arbitrary
;; string for a user who has tagged bugs.  The command returns the
;; list of existing user tags for the given user(s) or package
;; name(s), respectively.  Applying RET on a user tag, all bugs tagged
;; with this user tag are shown.

;; Unfortunately, it is not possible with the SOAP interface to show
;; all users who have tagged bugs.  This list can be retrieved via
;; <https://debbugs.gnu.org/cgi/pkgindex.cgi?indexon=users>.

;; A special command to show bugs containing patches is
;;
;;   M-x debbugs-gnu-patches

;; This command shows all unarchived bugs of the packages declared in
;; `debbugs-gnu-default-packages', and tagged with "patch".  This is
;; useful for bug triages.

;; Finally, if you simply want to list some bugs with known bug
;; numbers, call the command
;;
;;   M-x debbugs-gnu-bugs

;; The bug numbers to be shown shall be entered as comma separated
;; list.  A bug number can also be a range of bugs like "123-456" or
;; "-10".  In the former case, all bugs from 123 until 456 are
;; presented, and in the latter case the last 10 bugs are shown,
;; counting from the highest bug number in the repository.

;;; Code:

(require 'debbugs)
(require 'tabulated-list)
(require 'add-log)
(eval-when-compile (require 'subr-x))
(eval-when-compile (require 'cl-lib))

(autoload 'article-decode-charset "gnus-art")
(autoload 'diff-goto-source "diff-mode")
(autoload 'diff-hunk-file-names "diff-mode")
(autoload 'gnus-article-mime-handles "gnus-art")
(autoload 'gnus-fetch-field "gnus-util")
(autoload 'gnus-read-ephemeral-emacs-bug-group "gnus-group")
(autoload 'gnus-summary-article-header "gnus-sum")
(autoload 'gnus-summary-select-article "gnus-sum")
(autoload 'gnus-summary-show-article "gnus-sum")
(autoload 'log-edit-insert-changelog "log-edit")
(autoload 'mail-header-subject "nnheader")
(autoload 'message-goto-body "message")
(autoload 'message-make-from "message")
(autoload 'rmail-get-new-mail "rmail")
(autoload 'rmail-show-message "rmail")
(autoload 'rmail-summary "rmailsum")
(autoload 'vc-dir-hide-up-to-date "vc-dir")
(autoload 'vc-dir-mark "vc-dir")

(defvar compilation-in-progress)
(defvar diff-file-header-re)
(defvar gnus-article-buffer)
(defvar gnus-posting-styles)
(defvar gnus-save-duplicate-list)
(defvar gnus-suppress-duplicates)
(defvar rmail-current-message)
(defvar rmail-mode-map)
(defvar rmail-summary-mode-map)
(defvar rmail-total-messages)

;; Buffer-local variables.
(defvar debbugs-gnu-local-query)
(defvar debbugs-gnu-local-filter)
(defvar debbugs-gnu-local-suppress)
(defvar debbugs-gnu-sort-state)
(defvar debbugs-gnu-limit)

(defgroup debbugs-gnu ()
  "UI for the debbugs.gnu.org bug tracker."
  :group 'debbugs
  :version "24.1")

(defcustom debbugs-gnu-default-severities '("serious" "important" "normal")
  "The list severities bugs are searched for.
\"tagged\" is not a severity but marks locally tagged bugs."
  ;; <https://debbugs.gnu.org/Developer.html#severities>
  ;; /ssh:debbugs:/etc/debbugs/config @gSeverityList
  ;; We don't use "critical" and "grave".
  :group 'debbugs-gnu
  :type '(set (const "serious")
	      (const "important")
	      (const "normal")
	      (const "minor")
	      (const "wishlist")
	      (const "tagged"))
  :version "24.1")

(defcustom debbugs-gnu-send-mail-function nil
  "A function to send control messages from debbugs.
If nil, the value of `send-mail-function' is used instead."
  :type '(radio (const :tag "Use `send-mail-function'" nil)
		(function-item message-send-mail-with-sendmail)
		(function-item message-smtpmail-send-it)
		(function-item mailclient-send-it)
		(function-item smtpmail-send-it)
		(function-item feedmail-send-it)
		(function-item :tag "Use Mailclient package"
			       message-send-mail-with-mailclient)
 		(function :tag "Other function"))
  :version "25.1")

(defcustom debbugs-gnu-suppress-closed t
  "If non-nil, don't show closed bugs."
  :group 'debbugs-gnu
  :type 'boolean
  :version "25.1")

(defconst debbugs-gnu-all-severities
  (mapcar 'cadr (cdr (get 'debbugs-gnu-default-severities 'custom-type)))
  "List of all possible severities.")

(defcustom debbugs-gnu-default-packages '("emacs")
  "The list of packages to be searched for."
  ;; <https://debbugs.gnu.org/Packages.html>
  ;; <https://debbugs.gnu.org/cgi/pkgindex.cgi>
  :group 'debbugs-gnu
  :type `(set (const "adns")
	      (const "auctex")
	      (const "automake")
	      (const "cc-mode")
	      (const "coreutils")
	      (const "cppi")
	      (const "debbugs.gnu.org")
	      (const "diffutils")
	      (const "emacs")
	      (const "emacs-xwidgets")
	      (const "fm")
	      (const "gnus")
	      (const "grep")
	      (const "guile")
	      (const "guix")
	      (const "guix-patches")
	      (const "gzip")
	      (const "hyperbole")
	      (const "idutils")
	      (const "libtool")
	      (const "mh-e")
	      (const "oo-browser")
	      (const "org-mode")
	      (const "parted")
	      (const "sed")
	      (const ,(propertize
		      "test"
		      'face 'debbugs-gnu-done
		      'help-echo "This is a pseudo-package for test."))
	      (const "vc-dwim")
	      (const "woodchuck"))
  :version "25.2")

(defconst debbugs-gnu-all-packages
  (mapcar 'cadr (cdr (get 'debbugs-gnu-default-packages 'custom-type)))
  "List of all possible package names.")

(defcustom debbugs-gnu-default-suppress-bugs
  '((pending . "done"))
  "A list of specs for bugs to be suppressed.
An element of this list is a cons cell \(KEY . REGEXP\), with key
being returned by `debbugs-get-status', and REGEXP a regular
expression matching the corresponding value, a string.  Showing
suppressed bugs is toggled by `debbugs-gnu-toggle-suppress'."
  :group 'debbugs-gnu
  :type '(alist :key-type symbol :value-type regexp)
  :version "24.1")

(defcustom debbugs-gnu-mail-backend 'gnus
  "The email backend to use for reading bug report email exchange.
If this is `gnus', the default, use Gnus.
If this is `rmail', use Rmail instead."
  :group 'debbugs-gnu
  :type '(radio (function-item :tag "Use Gnus" gnus)
		(function-item :tag "Use Rmail" rmail))
  :version "25.1")

(defface debbugs-gnu-archived '((t (:inverse-video t)))
  "Face for archived bug reports.")

(defface debbugs-gnu-new '((t (:foreground "red")))
  "Face for new reports that nobody has answered.")

(defface debbugs-gnu-handled '((t (:foreground "ForestGreen")))
  "Face for reports that have been modified recently.")

(defface debbugs-gnu-pending '((t (:foreground "MidnightBlue")))
  "Face for reports that are pending.")

(defface debbugs-gnu-stale '((t (:foreground "orange")))
  "Face for reports that have not been touched for two weeks.")

(defface debbugs-gnu-done '((t (:foreground "DarkGrey")))
  "Face for closed bug reports.")

(defface debbugs-gnu-tagged '((t (:foreground "red")))
  "Face for reports that have been tagged locally.")

(defvar debbugs-gnu-local-tags nil
  "List of bug numbers tagged locally, and kept persistent.")

(defvar debbugs-gnu-persistency-file
  (expand-file-name (locate-user-emacs-file "debbugs"))
  "File name of a persistency store for debbugs variables")

(defun debbugs-gnu-dump-persistency-file ()
  "Function to store debbugs variables persistently."
  (with-temp-file debbugs-gnu-persistency-file
    (insert
     ";; -*- emacs-lisp -*-\n"
     ";; Debbugs tags connection history.  Don't change this file.\n\n"
     (format "(setq debbugs-gnu-local-tags '%S)"
	     (sort (copy-sequence debbugs-gnu-local-tags) '>)))))

(defvar debbugs-gnu-current-query nil
  "The query object of the current search.
It will be applied server-side, when calling `debbugs-get-bugs'.
It has the same format as `debbugs-gnu-default-suppress-bugs'.")

(defvar debbugs-gnu-current-filter nil
  "The filter object for the current search.
It will be applied client-side, when parsing the results of
`debbugs-get-status'.  It has a similar format as
`debbugs-gnu-default-suppress-bugs'.  In case of keys representing
a date, value is the cons cell \(BEFORE . AFTER\).")

(defvar debbugs-gnu-current-suppress nil
  "Whether bugs shall be suppressed.
The specification which bugs shall be suppressed is taken from
  `debbugs-gnu-default-suppress-bugs'.")

(defcustom debbugs-gnu-emacs-current-release "25.2"
  "The current Emacs relase developped for."
  :group 'debbugs-gnu
  :type '(choice (const "24.5")
		 (const "25.1")
		 (const "25.2")
		 (const "26.1"))
  :version "25.2")

(defconst debbugs-gnu-emacs-blocking-reports
  '(("24.5" . 19758)
    ("25.1" . 19759)
    ("25.2" . 21966)
    ("26.1" . 24655))
  "The IDs of the Emacs report used to track blocking bug reports.
It is a list of cons cells, each one containing the Emacs
version (a string) and the bug report number (a number).")

(defun debbugs-gnu-calendar-read (prompt acceptable &optional initial-contents)
  "Return a string read from the minibuffer.
Derived from `calendar-read'."
  (let ((value (read-string prompt initial-contents)))
    (while (not (funcall acceptable value))
      (setq value (read-string prompt initial-contents)))
    value))

(defconst debbugs-gnu-phrase-prompt
  (propertize
   "Enter search phrase: "
   'help-echo "\
The search phrase contains words to be searched for, combined by
operators like AND, ANDNOT and OR.  If there is no operator
between the words, AND is used by default.  The phrase can also
be empty, in this case only the following attributes are used for
search."))

;;;###autoload
(defun debbugs-gnu-search ()
  "Search for Emacs bugs interactively.
Search arguments are requested interactively.  The \"search
phrase\" is used for full text search in the bugs database.
Further key-value pairs are requested until an empty key is
returned.  If a key cannot be queried by a SOAP request, it is
marked as \"client-side filter\"."
  (interactive)

  (unwind-protect
      (let ((date-format "\\([[:digit:]]\\{4\\}\\)-\\([[:digit:]]\\{1,2\\}\\)-\\([[:digit:]]\\{1,2\\}\\)")
	    key val1 val2 phrase severities packages archivedp)

	;; Check for the phrase.
	(setq phrase (read-string debbugs-gnu-phrase-prompt))
	(if (zerop (length phrase))
	    (setq phrase nil)
	  (add-to-list 'debbugs-gnu-current-query (cons 'phrase phrase)))
	;; We suppress closed bugs if there is no phrase.
	(setq debbugs-gnu-current-suppress
	      (if (not debbugs-gnu-suppress-closed)
		  nil
		(null phrase)))

	;; The other queries.
	(catch :finished
	  (while t
	    (setq key (completing-read
		       "Enter attribute: "
		       (if phrase
			   (append
			    '("severity" "package" "tags"
			      "author" "date" "subject")
			     ;; Client-side filters.
			    (mapcar
			     (lambda (key)
			       (propertize
				key 'face 'debbugs-gnu-done
				'help-echo "Client-side filter"))
			     '("status")))
			 (append
			  '("severity" "package" "archive" "src" "status" "tag"
			    "owner" "submitter" "maint" "correspondent")
			  ;; Client-side filters.
			  (mapcar
			   (lambda (key)
			     (propertize
			      key 'face 'debbugs-gnu-done
			      'help-echo "Client-side filter"))
			   '("date" "log_modified" "last_modified"
			     "found_date" "fixed_date" "unarchived"
			     "subject" "done" "forwarded" "msgid" "summary"))))
		       nil t))
	    (cond
	     ;; Server-side queries.
	     ((equal key "severity")
	      (setq
	       severities
	       (completing-read-multiple
		"Enter severities: " debbugs-gnu-all-severities nil t
		(mapconcat 'identity debbugs-gnu-default-severities ","))))

	     ((equal key "package")
	      (setq
	       packages
	       (completing-read-multiple
		"Enter packages: " debbugs-gnu-all-packages nil t
		(mapconcat 'identity debbugs-gnu-default-packages ","))))

	     ((equal key "archive")
	      ;; We simplify, by assuming just archived bugs are requested.
	      (setq archivedp t))

	     ((member key '("src" "tag" "tags"))
	      (setq val1 (read-string (format "Enter %s: " key)))
	      (when (not (zerop (length val1)))
		(add-to-list
		 'debbugs-gnu-current-query (cons (intern key) val1))))

	     ((member
	       key '("author" "owner" "submitter" "maint" "correspondent"))
	      (setq val1 (read-string "Enter email address: "))
	      (when (not (zerop (length val1)))
		(add-to-list
		 'debbugs-gnu-current-query
		 (cons (intern (if (equal key "author") "@author" key)) val1))))

	     ;; Client-side filters.
	     ((equal key "status")
	      (setq
	       val1
	       (completing-read
		(format "Enter status%s: "
			(if (null phrase) "" " (client-side filter)"))
		'("open" "forwarded" "done") nil t))
	      (when (not (zerop (length val1)))
		 (if (null phrase)
		     (add-to-list
		      'debbugs-gnu-current-query (cons (intern key) val1))
		   (add-to-list
		    'debbugs-gnu-current-filter (cons 'pending val1)))))

	     ((member key '("date" "log_modified" "last_modified"
			    "found_date" "fixed_date" "unarchived"))
	      (setq val1
		    (debbugs-gnu-calendar-read
		     (format "Enter %s before YYYY-MM-DD%s: "
			     key (if phrase "" " (client-side filter)"))
		     (lambda (x)
		       (string-match (concat "^\\(" date-format "\\|\\)$") x))))
	      (if (string-match date-format val1)
		  (setq val1 (floor
			      (float-time
			       (encode-time
				0 0 0
				(string-to-number (match-string 3 val1))
				(string-to-number (match-string 2 val1))
				(string-to-number (match-string 1 val1))))))
		(setq val1 nil))
	      (setq val2
		    (debbugs-gnu-calendar-read
		     (format "Enter %s after YYYY-MM-DD%s: "
			     key (if phrase "" " (client-side filter)"))
		     (lambda (x)
		       (string-match (concat "^\\(" date-format "\\|\\)$") x))))
	      (if (string-match date-format val2)
		  (setq val2 (floor
			      (float-time
			       (encode-time
				0 0 0
				(string-to-number (match-string 3 val2))
				(string-to-number (match-string 2 val2))
				(string-to-number (match-string 1 val2))))))
		(setq val2 nil))
	      (when (or val1 val2)
		(add-to-list
		 (if phrase
		     'debbugs-gnu-current-query 'debbugs-gnu-current-filter)
		 (cons (intern
			(if (and phrase (equal key "date")) "@cdate" key))
		       (cons val1 val2)))))

	     ;; "subject", "done", "forwarded", "msgid", "summary".
	     ((not (zerop (length key)))
	      (setq val1
		    (funcall
		     (if phrase 'read-string 'read-regexp)
		     (format "Enter %s%s: "
			     key (if phrase "" " (client-side filter)"))))
	      (when (not (zerop (length val1)))
		(add-to-list
		 (if phrase
		     'debbugs-gnu-current-query 'debbugs-gnu-current-filter)
		 (cons (intern key) val1))))

	     ;; The End.
	     (t (throw :finished nil)))))

	;; Do the search.
	(debbugs-gnu severities packages archivedp))))

;;;###autoload
(defun debbugs-gnu-patches ()
  "List the bug reports that have been marked as containing a patch."
  (interactive)
  (setq debbugs-gnu-current-suppress t)
  (debbugs-gnu nil debbugs-gnu-default-packages nil nil "patch"))

;;;###autoload
(defun debbugs-gnu (severities &optional packages archivedp suppress tags)
  "List all outstanding bugs."
  (interactive
   (let (severities archivedp)
     (list
      (setq severities
	    (completing-read-multiple
	     "Severities: " debbugs-gnu-all-severities nil t
	     (mapconcat 'identity debbugs-gnu-default-severities ",")))
      ;; The next parameters are asked only when there is a prefix.
      (if current-prefix-arg
	  (completing-read-multiple
	   "Packages: " debbugs-gnu-all-packages nil t
	   (mapconcat 'identity debbugs-gnu-default-packages ","))
	debbugs-gnu-default-packages)
      (when current-prefix-arg
	(setq archivedp (y-or-n-p "Show archived bugs?")))
      (when (and current-prefix-arg (not archivedp))
	(y-or-n-p "Suppress unwanted bugs?"))
      ;; This one must be asked for severity "tagged".
      (when (member "tagged" severities)
	(split-string (read-string "User tag(s): ") "," t)))))

  (unwind-protect
      (progn
	;; Initialize variables.
	(when (and (file-exists-p debbugs-gnu-persistency-file)
		   (not debbugs-gnu-local-tags))
	  (with-temp-buffer
	    (insert-file-contents debbugs-gnu-persistency-file)
	    (eval (read (current-buffer)))))
	;; Per default, we suppress retrieved unwanted bugs.
	(when (and (called-interactively-p 'any)
		   debbugs-gnu-suppress-closed)
	  (setq debbugs-gnu-current-suppress t))

	;; Add queries.
	(dolist (severity (if (consp severities) severities (list severities)))
	  (when (not (zerop (length severity)))
	    (when (string-equal severity "tagged")
	      (setq debbugs-gnu-current-suppress nil))
	    (add-to-list 'debbugs-gnu-current-query (cons 'severity severity))))
	(dolist (package (if (consp packages) packages (list packages)))
	  (when (not (zerop (length package)))
	    (add-to-list 'debbugs-gnu-current-query (cons 'package package))))
	(when archivedp
	  (setq debbugs-gnu-current-suppress nil)
	  (add-to-list 'debbugs-gnu-current-query '(archive . "1")))
	(when suppress
	  (setq debbugs-gnu-current-suppress t)
	  (add-to-list 'debbugs-gnu-current-query '(status . "open"))
	  (add-to-list 'debbugs-gnu-current-query '(status . "forwarded")))
	(dolist (tag (if (consp tags) tags (list tags)))
	  (when (not (zerop (length tag)))
	    (add-to-list 'debbugs-gnu-current-query (cons 'tag tag))))

	;; Show result.
	(debbugs-gnu-show-reports))

    ;; Reset query, filter and suppress.
    (setq debbugs-gnu-current-query nil
	  debbugs-gnu-current-filter nil
	  debbugs-gnu-current-suppress nil)))

(defun debbugs-gnu-get-bugs (query)
  "Retrieve bug numbers from debbugs.gnu.org according search criteria."
  (let* ((debbugs-port "gnu.org")
	 (bugs (assoc 'bugs query))
	 (tags (and (member '(severity . "tagged") query) (assoc 'tag query)))
	 (local-tags (and (member '(severity . "tagged") query) (not tags)))
	 (phrase (assoc 'phrase query))
	 args)
    ;; Compile query arguments.
    (unless (or query tags)
      (dolist (elt debbugs-gnu-default-packages)
	(setq args (append args (list :package elt)))))
    (dolist (elt query)
      (unless (equal elt '(severity . "tagged"))
	(setq args
	      (append
	       args
	       (if phrase
		   (cond
		    ((eq (car elt) 'phrase)
		     (list (list :phrase (cdr elt))))
		    ((memq (car elt) '(date @cdate))
		     (list (list (intern (concat ":" (symbol-name (car elt))))
				 (cddr elt) (cadr elt)
				 :operator "NUMBT")))
		    (t
		     (list (list (intern (concat ":" (symbol-name (car elt))))
				 (cdr elt) :operator "ISTRINC"))))
		 (list (intern (concat ":" (symbol-name (car elt))))
		       (cdr elt)))))))

    (cond
     ;; If the query is just a list of bug numbers, we return them.
     (bugs (cdr bugs))
     ;; If the query contains the pseudo-severity "tagged", we return
     ;; just the local tagged bugs.
     (local-tags (copy-sequence debbugs-gnu-local-tags))
     ;; A full text query.
     (phrase
      (mapcar
       (lambda (x) (cdr (assoc "id" x)))
       (apply 'debbugs-search-est args)))
     ;; User tags.
     (tags
      (setq args (mapcar (lambda (x) (if (eq x :package) :user x)) args))
      (apply 'debbugs-get-usertag args))
     ;; Otherwise, we retrieve the bugs from the server.
     (t (apply 'debbugs-get-bugs args)))))

(defun debbugs-gnu-show-reports (&optional offline)
  "Show bug reports.
If OFFLINE is non-nil, the query is not sent to the server.  Bugs
are taken from the cache instead."
  (let* ((inhibit-read-only t)
	 string
	 (buffer-name
	  (cond
	   ((setq string (cdr (assq 'phrase debbugs-gnu-current-query)))
	    (format "*%S Bugs*" string))
	   ((setq string (cdr (assq 'package debbugs-gnu-current-query)))
	    (format "*%s Bugs*" (capitalize string)))
	   (t "*Bugs*"))))
    ;; The tabulated mode sets several local variables.  We must get
    ;; rid of them.
    (when (get-buffer buffer-name)
      (kill-buffer buffer-name))
    (switch-to-buffer (get-buffer-create buffer-name))
    (debbugs-gnu-mode)

    ;; Print bug reports.
    (dolist (status
	     (let ((debbugs-cache-expiry (if offline nil debbugs-cache-expiry))
		   ids)
	       (apply 'debbugs-get-status
		      (if offline
			  (progn
			    (maphash (lambda (key _elem)
				       (push key ids))
				     debbugs-cache-data)
			    (sort ids '<))
			(debbugs-gnu-get-bugs debbugs-gnu-local-query)))))
      (let* ((id (cdr (assq 'id status)))
	     (words
	      (mapconcat
	       'identity
	       (cons (cdr (assq 'severity status))
		     (cdr (assq 'keywords status)))
	       ","))
	     (address (if (cdr (assq 'originator status))
			  (mail-header-parse-address
			   (decode-coding-string (cdr (assq 'originator status))
						 'utf-8))))
	     (owner (if (cdr (assq 'owner status))
			(car (mail-header-parse-address
			      (decode-coding-string (cdr (assq 'owner status))
						    'utf-8)))))
	     (subject (if (cdr (assq 'subject status))
			  (decode-coding-string (cdr (assq 'subject status))
						'utf-8)))
	     merged)
	(unless (equal (cdr (assq 'pending status)) "pending")
	  (setq words (concat words "," (cdr (assq 'pending status)))))
	(let ((packages (cdr (assq 'package status))))
	  (dolist (elt packages)
	    (when (member elt debbugs-gnu-default-packages)
	      (setq packages (delete elt packages))))
	  (when packages
	    (setq words (concat words "," (mapconcat 'identity packages ",")))))
	(when (setq merged (cdr (assq 'mergedwith status)))
	  (setq words (format "%s,%s"
			      (if (numberp merged)
				  merged
				(mapconcat 'number-to-string merged ","))
			      words)))
	(when (or (not merged)
		  (not (let ((found nil))
			 (dolist (id (if (listp merged)
					 merged
				       (list merged)))
			   (dolist (entry tabulated-list-entries)
			     (when (equal id (cdr (assq 'id (car entry))))
			       (setq found t))))
			 found)))
	  (add-to-list
	   'tabulated-list-entries
	   (list
	    status
	    (vector
	     (propertize
	      (format "%5d" id)
	      'face
	      ;; Mark tagged bugs.
	      (if (memq id debbugs-gnu-local-tags)
		  'debbugs-gnu-tagged
		'default))
	     (propertize
	      ;; Mark status and age.
	      (or words "")
	      'face
	      (cond
	       ((cdr (assq 'archived status))
		'debbugs-gnu-archived)
	       ((equal (cdr (assq 'pending status)) "done")
		'debbugs-gnu-done)
	       ((member "pending" (cdr (assq 'keywords status)))
		'debbugs-gnu-pending)
	       ;; For some new bugs `date' and `log_modified' may
	       ;; differ in 1 second.
	       ((< (abs (- (cdr (assq 'date status))
			   (cdr (assq 'log_modified status))))
		   3)
		'debbugs-gnu-new)
	       ((< (- (float-time)
		      (cdr (assq 'log_modified status)))
		   (* 60 60 24 7 2))
		'debbugs-gnu-handled)
	       (t
		'debbugs-gnu-stale)))
	     (propertize
	      ;; Prefer the name over the address.
	      (or (cdr address)
		  (car address)
		  "")
	      'face
	      ;; Mark own submitted bugs.
	      (if (and (stringp (car address))
		       (string-equal (car address) user-mail-address))
		  'debbugs-gnu-tagged
		'default))
	     (propertize
	      (or subject "")
	      'face
	      ;; Mark owned bugs.
	      (if (and (stringp owner)
		       (string-equal owner user-mail-address))
		  'debbugs-gnu-tagged
		'default))))
	   'append))))

    (tabulated-list-init-header)
    (tabulated-list-print)

    (set-buffer-modified-p nil)
    (goto-char (point-min))))

(defun debbugs-gnu-print-entry (list-id cols)
  "Insert a debbugs entry at point.
Used instead of `tabulated-list-print-entry'."
  (let ((beg (point))
	(pos 0)
	(case-fold-search t)
	(id               (aref cols 0))
	(id-length        (nth 1 (aref tabulated-list-format 0)))
	(state            (aref cols 1))
	(state-length     (nth 1 (aref tabulated-list-format 1)))
	(submitter        (aref cols 2))
	(submitter-length (nth 1 (aref tabulated-list-format 2)))
	(title            (aref cols 3))
	;; (title-length     (nth 1 (aref tabulated-list-format 3)))
        )
    (when (and
	   ;; We may have a narrowing in effect.
	   (or (not debbugs-gnu-limit)
	       (memq (cdr (assq 'id list-id)) debbugs-gnu-limit))
	   ;; Filter suppressed bugs.
	   (or (not debbugs-gnu-local-suppress)
	       (not (catch :suppress
		      (dolist (check debbugs-gnu-default-suppress-bugs)
			(when
			    (string-match
			     (cdr check)
			     (or (cdr (assq (car check) list-id)) ""))
			  (throw :suppress t))))))
	   ;; Filter search list.
	   (not (catch :suppress
		  (dolist (check debbugs-gnu-local-filter)
		    (let ((val (cdr (assq (car check) list-id))))
		      (if (stringp (cdr check))
			  ;; Regular expression.
			  (when (not (string-match (cdr check) (or val "")))
			    (throw :suppress t))
			;; Time value.
			(when (or (and (numberp (cadr check))
				       (< (cadr check) val))
				  (and (numberp (cddr check))
				       (> (cddr check) val)))
			  (throw :suppress t))))))))

      ;; Insert id.
      (indent-to (- id-length (length id)))
      (insert id)
      ;; Insert state.
      (indent-to (setq pos (+ pos id-length 1)) 1)
      (insert (if (> (length state) state-length)
		  (propertize (substring state 0 state-length)
			      'help-echo state)
		state))
      ;; Insert submitter.
      (indent-to (setq pos (+ pos state-length 1)) 1)
      (insert "[" (if (> (length submitter) (- submitter-length 2))
		      (propertize (substring submitter 0 (- submitter-length 2))
				  'help-echo submitter)
		    submitter))
      (indent-to (+ pos (1- submitter-length)))
      (insert "]")
      ;; Insert title.
      (indent-to (setq pos (+ pos submitter-length 1)) 1)
      (insert (propertize title 'help-echo title))
      ;; Add properties.
      (add-text-properties
       beg (point)
       `(tabulated-list-id ,list-id mouse-face highlight))
      (insert ?\n))))

(defun debbugs-gnu-menu-map-emacs-enabled ()
  "Whether \"Show Release Blocking Bugs\" is enabled in the menu."
  (or ;; No package discriminator has been used.
      (not (assq 'package debbugs-gnu-local-query))
      ;; Package "emacs" has been selected.
      (member '(package . "emacs") debbugs-gnu-local-query)))

(defun debbugs-gnu-manual ()
  "Display the Debbugs manual in Info mode."
  (interactive)
  (info "debbugs-ug"))

(defconst debbugs-gnu-bug-triage-file
  (expand-file-name "../admin/notes/bug-triage" data-directory)
  "The \"bug-triage\" file.")

(defun debbugs-gnu-menu-map-bug-triage-enabled ()
  "Whether \"Describe Bug Triage Procedure\" is enabled in the menu."
  (and (debbugs-gnu-menu-map-emacs-enabled)
       (stringp debbugs-gnu-bug-triage-file)
       (file-readable-p debbugs-gnu-bug-triage-file)))

(defun debbugs-gnu-view-bug-triage ()
  "Show \"bug-triage\" file."
  (interactive)
  (view-file debbugs-gnu-bug-triage-file))

(defvar debbugs-gnu-mode-map
  (let ((map (make-sparse-keymap))
	(menu-map (make-sparse-keymap)))
    (set-keymap-parent map tabulated-list-mode-map)
    (define-key map "\r" 'debbugs-gnu-select-report)
    (define-key map [mouse-2] 'debbugs-gnu-select-report)
    (define-key map "g" 'debbugs-gnu-rescan)
    (define-key map "R" 'debbugs-gnu-show-all-blocking-reports)
    (define-key map "C" 'debbugs-gnu-send-control-message)

    (define-key map "s" 'debbugs-gnu-toggle-sort)
    (define-key map "t" 'debbugs-gnu-toggle-tag)
    (define-key map "x" 'debbugs-gnu-toggle-suppress)
    (define-key map "/" 'debbugs-gnu-narrow-to-status)
    (define-key map "w" 'debbugs-gnu-widen)

    (define-key map "b" 'debbugs-gnu-show-blocked-by-reports)
    (define-key map "B" 'debbugs-gnu-show-blocking-reports)
    (define-key map "d" 'debbugs-gnu-display-status)

    (define-key map [menu-bar debbugs] (cons "Debbugs" menu-map))
    (define-key menu-map [debbugs-gnu-select-report]
      '(menu-item "Show Reports" debbugs-gnu-select-report
		  :help "Show all reports belonging to this bug"))
    (define-key-after menu-map [debbugs-gnu-rescan]
      '(menu-item "Refresh Bugs" debbugs-gnu-rescan
		  :help "Refresh bug list")
      'debbugs-gnu-select-report)
    (define-key-after menu-map [debbugs-gnu-show-all-blocking-reports]
      '(menu-item "Show Release Blocking Bugs"
		  debbugs-gnu-show-all-blocking-reports
		  :enable (debbugs-gnu-menu-map-emacs-enabled)
		  :help "Show all bugs blocking next Emacs release")
      'debbugs-gnu-rescan)
    (define-key-after menu-map [debbugs-gnu-send-control-message]
      '(menu-item "Send Control Message"
		  debbugs-gnu-send-control-message
		  :help "Send control message to debbugs.gnu.org")
      'debbugs-gnu-show-all-blocking-reports)

    (define-key-after menu-map [debbugs-gnu-separator1]
      '(menu-item "--") 'debbugs-gnu-send-control-message)
    (define-key-after menu-map [debbugs-gnu-search]
      '(menu-item "Search Bugs" debbugs-gnu-search
		  :help "Search bugs on debbugs.gnu.org")
      'debbugs-gnu-separator1)
    (define-key-after menu-map [debbugs-gnu]
      '(menu-item "Retrieve Bugs" debbugs-gnu
		  :help "Retrieve bugs from debbugs.gnu.org")
      'debbugs-gnu-search)
    (define-key-after menu-map [debbugs-gnu-bugs]
      '(menu-item "Retrieve Bugs by Number" debbugs-gnu-bugs
		  :help "Retrieve selected bugs from debbugs.gnu.org")
      'debbugs-gnu)

    (define-key-after menu-map [debbugs-gnu-separator2]
      '(menu-item "--") 'debbugs-gnu-bugs)
    (define-key-after menu-map [debbugs-gnu-manual]
      '(menu-item "Debbugs Manual" debbugs-gnu-manual
		  :help "Show Debbugs Manual")
      'debbugs-gnu-separator2)
    (define-key-after menu-map [debbugs-gnu-view-bug-triage]
      '(menu-item "Describe Bug Triage Procedure"
		  debbugs-gnu-view-bug-triage
		  :enable (debbugs-gnu-menu-map-bug-triage-enabled)
		  :help "Show procedure of triaging bugs")
      'debbugs-gnu-manual)
    map))

(defun debbugs-gnu-rescan ()
  "Rescan the current set of bug reports."
  (interactive)
  (let ((id (debbugs-gnu-current-id))
	(debbugs-gnu-current-query debbugs-gnu-local-query)
	(debbugs-gnu-current-filter debbugs-gnu-local-filter)
	(debbugs-gnu-current-suppress debbugs-gnu-local-suppress)
	(debbugs-cache-expiry (if current-prefix-arg t debbugs-cache-expiry)))
    (debbugs-gnu-show-reports)
    (when id
      (debbugs-gnu-goto id))))

(define-derived-mode debbugs-gnu-mode tabulated-list-mode "Debbugs"
  "Major mode for listing bug reports.

All normal editing commands are switched off.
\\<debbugs-gnu-mode-map>

The following commands are available:

\\{debbugs-gnu-mode-map}"
  (set (make-local-variable 'debbugs-gnu-sort-state) 'number)
  (set (make-local-variable 'debbugs-gnu-limit) nil)
  (set (make-local-variable 'debbugs-gnu-local-query)
       debbugs-gnu-current-query)
  (set (make-local-variable 'debbugs-gnu-local-filter)
       debbugs-gnu-current-filter)
  (set (make-local-variable 'debbugs-gnu-local-suppress)
       debbugs-gnu-current-suppress)
  (setq tabulated-list-format [("Id"         5 debbugs-gnu-sort-id)
			       ("State"     20 debbugs-gnu-sort-state)
			       ("Submitter" 25 debbugs-gnu-sort-submitter)
			       ("Title"     10 debbugs-gnu-sort-title)])
  (setq tabulated-list-sort-key (cons "Id" nil))
  (setq tabulated-list-printer 'debbugs-gnu-print-entry)
  (buffer-disable-undo)
  (setq truncate-lines t)
  (setq buffer-read-only t))

(defun debbugs-gnu-sort-id (s1 s2)
  (> (cdr (assq 'id (car s1)))
     (cdr (assq 'id (car s2)))))

(defconst debbugs-gnu-state-preference
  '((debbugs-gnu-new . 1)
    (debbugs-gnu-stale . 2)
    (debbugs-gnu-handled . 3)
    (debbugs-gnu-pending . 4)
    (debbugs-gnu-done . 5)))

(defun debbugs-gnu-get-state-preference (face-string)
  (or (cdr (assq (get-text-property 0 'face face-string)
		 debbugs-gnu-state-preference))
      10))

(defconst debbugs-gnu-severity-preference
  '(("serious" . 1)
    ("important" . 2)
    ("normal" . 3)
    ("minor" . 4)
    ("wishlist" . 5)))

(defun debbugs-gnu-get-severity-preference (state)
  (or (cdr (assoc (cdr (assq 'severity state))
		  debbugs-gnu-severity-preference))
      10))

(defun debbugs-gnu-sort-state (s1 s2)
  (let ((id1 (cdr (assq 'id (car s1))))
	(age1 (debbugs-gnu-get-state-preference (aref (nth 1 s1) 1)))
	(id2 (cdr (assq 'id (car s2))))
	(age2 (debbugs-gnu-get-state-preference (aref (nth 1 s2) 1))))
    (cond
     ;; Tagged bugs go to the beginning.
     ((and (memq id1 debbugs-gnu-local-tags)
	   (not (memq id2 debbugs-gnu-local-tags)))
      t)
     ((and (not (memq id1 debbugs-gnu-local-tags))
	   (memq id2 debbugs-gnu-local-tags))
      nil)
     ;; Then, we check the age of the bugs.
     ((< age1 age2)
      t)
     ((> age1 age2)
      nil)
     ;; If they have the same age, we check for severity.
     ((< (debbugs-gnu-get-severity-preference (car s1))
	 (debbugs-gnu-get-severity-preference (car s2)))
      t)
     (t nil))))

(defun debbugs-gnu-sort-submitter (s1 s2)
  (let ((address1
	 (mail-header-parse-address
	  (decode-coding-string
	   (or (cdr (assq 'originator (car s1))) "") 'utf-8)))
	(address2
	 (mail-header-parse-address
	  (decode-coding-string
	   (or (cdr (assq 'originator (car s2))) "") 'utf-8))))
    (cond
     ;; Bugs I'm the originator of go to the beginning.
     ((and (string-equal user-mail-address (car address1))
	   (not (string-equal (car address1) (car address2))))
      t)
     ((and (string-equal user-mail-address (car address2))
	   (not (string-equal (car address1) (car address2))))
      nil)
     ;; Then, we check the originator.  Prefer the name over the address.
     (t (if (functionp 'string-collate-lessp)
	    (funcall 'string-collate-lessp
		     (or (cdr address1) (car address1) "")
		     (or (cdr address2) (car address2) "")
		     nil t)
	  (string-lessp
	   (downcase (or (cdr address1) (car address1) ""))
	   (downcase (or (cdr address2) (car address2) ""))))))))

(defun debbugs-gnu-sort-title (s1 s2)
  (let ((owner1
	 (car (mail-header-parse-address
	       (decode-coding-string
		(or (cdr (assq 'owner (car s1))) "") 'utf-8))))
	(subject1
	 (decode-coding-string (or (cdr (assq 'subject (car s1))) "") 'utf-8))
	(owner2
	 (car (mail-header-parse-address
	       (decode-coding-string
		(or (cdr (assq 'owner (car s2))) "") 'utf-8))))
	(subject2
	 (decode-coding-string (or (cdr (assq 'subject (car s2))) "") 'utf-8)))
    (cond
     ;; Bugs I'm the owner of go to the beginning.
     ((and (string-equal user-mail-address owner1)
	   (not (string-equal owner1 owner2)))
      t)
     ((and (string-equal user-mail-address owner2)
	   (not (string-equal owner1 owner2)))
      nil)
     ;; Then, we check the title.
     (t (if (functionp 'string-collate-lessp)
	     (funcall 'string-collate-lessp subject1 subject2 nil t)
	   (string-lessp (downcase subject1) (downcase subject2)))))))

(defun debbugs-gnu-toggle-sort ()
  "Toggle sorting by age and by state."
  (interactive)
  (if (eq debbugs-gnu-sort-state 'number)
      (progn
	(setq debbugs-gnu-sort-state 'state)
	(setq tabulated-list-sort-key (cons "Id" nil)))
    (setq debbugs-gnu-sort-state 'number)
    (setq tabulated-list-sort-key (cons "State" nil)))
  (tabulated-list-init-header)
  (tabulated-list-print))

(defun debbugs-gnu-widen ()
  "Display all the currently selected bug reports."
  (interactive)
  (let ((id (debbugs-gnu-current-id t))
	(inhibit-read-only t))
    (setq debbugs-gnu-limit nil)
    (tabulated-list-init-header)
    (tabulated-list-print)
    (when id
      (debbugs-gnu-goto id))))

(defun debbugs-gnu-show-blocked-by-reports ()
  "Display all bug reports this report is blocked by."
  (interactive)
  (let ((id (debbugs-gnu-current-id))
	(status (debbugs-gnu-current-status)))
    (if (null (cdr (assq 'blockedby status)))
	(message "Bug %d is not blocked by any other bug" id)
      (apply 'debbugs-gnu-bugs (cdr (assq 'blockedby status))))))

(defun debbugs-gnu-show-blocking-reports ()
  "Display all bug reports this report is blocking."
  (interactive)
  (let ((id (debbugs-gnu-current-id))
	(status (debbugs-gnu-current-status)))
    (if (null (cdr (assq 'blocks status)))
	(message "Bug %d is not blocking any other bug" id)
      (apply 'debbugs-gnu-bugs (cdr (assq 'blocks status))))))

(defun debbugs-gnu-show-all-blocking-reports (&optional release)
  "Narrow the display to just the reports that are blocking an Emacs release."
  (interactive
   (list
    (if current-prefix-arg
	(completing-read
	 "Emacs release: "
	 (mapcar 'identity debbugs-gnu-emacs-blocking-reports)
	 nil t debbugs-gnu-emacs-current-release)
      debbugs-gnu-emacs-current-release)))

  (let ((blockers
	 (cdr
	  (assq
	   'blockedby
	   (car
	    (debbugs-get-status
	     (cdr (assoc release debbugs-gnu-emacs-blocking-reports)))))))
	(id (debbugs-gnu-current-id t))
	(inhibit-read-only t)
	status)
    (setq debbugs-gnu-limit nil)
    (goto-char (point-min))
    (while (not (eobp))
      (setq status (debbugs-gnu-current-status))
      (if (not (memq (cdr (assq 'id status)) blockers))
	  (delete-region (point) (progn (forward-line 1) (point)))
	(push (cdr (assq 'id status)) debbugs-gnu-limit)
	(forward-line 1)))
    (when id
      (debbugs-gnu-goto id))))

(defun debbugs-gnu-narrow-to-status (string &optional status-only)
  "Only display the bugs matching STRING.
If STATUS-ONLY (the prefix), ignore matches in the From and
Subject fields."
  (interactive "sNarrow to: \nP")
  (let ((id (debbugs-gnu-current-id t))
	(inhibit-read-only t)
	status)
    (setq debbugs-gnu-limit nil)
    (if (equal string "")
	(debbugs-gnu-toggle-suppress)
      (goto-char (point-min))
      (while (not (eobp))
	(setq status (debbugs-gnu-current-status))
	(if (and (not (member string (assq 'keywords status)))
		 (not (equal string (cdr (assq 'severity status))))
		 (or status-only
		     (not (string-match
			   string (cdr (assq 'originator status)))))
		 (or status-only
		     (not (string-match string (cdr (assq 'subject status))))))
	    (delete-region (point) (progn (forward-line 1) (point)))
	  (push (cdr (assq 'id status)) debbugs-gnu-limit)
	  (forward-line 1)))
      (when id
	(debbugs-gnu-goto id)))))

(defun debbugs-gnu-goto (id)
  "Go to the line displaying bug ID."
  (goto-char (point-min))
  (while (and (not (eobp))
	      (not (equal (debbugs-gnu-current-id t) id)))
    (forward-line 1)))

(defun debbugs-gnu-toggle-tag ()
  "Toggle the local tag of the report in the current line.
If a report is tagged locally, it is presumed to be of little
interest to you."
  (interactive)
  (save-excursion
    (beginning-of-line)
    (let ((inhibit-read-only t)
	  (id (debbugs-gnu-current-id)))
      (if (memq id debbugs-gnu-local-tags)
	  (progn
	    (setq debbugs-gnu-local-tags (delq id debbugs-gnu-local-tags))
	    (put-text-property (point) (+ (point) 5) 'face 'default))
	(add-to-list 'debbugs-gnu-local-tags id)
	(put-text-property
	 (+ (point) (- 5 (length (number-to-string id)))) (+ (point) 5)
	 'face 'debbugs-gnu-tagged))
      (debbugs-gnu--update-tag-face id)))
  (debbugs-gnu-dump-persistency-file))

(defun debbugs-gnu--update-tag-face (id)
  (dolist (entry tabulated-list-entries)
    (when (equal (cdr (assq 'id (car entry))) id)
      (aset (cadr entry) 0
	    (propertize
	     (format "%5d" id)
	     'face
	     ;; Mark tagged bugs.
	     (if (memq id debbugs-gnu-local-tags)
		 'debbugs-gnu-tagged
	       'default))))))

(defun debbugs-gnu-toggle-suppress ()
  "Suppress bugs marked in `debbugs-gnu-suppress-bugs'."
  (interactive)
  (setq debbugs-gnu-local-suppress (not debbugs-gnu-local-suppress))
  (tabulated-list-init-header)
  (tabulated-list-print))

(defvar debbugs-gnu-bug-number nil)
(defvar debbugs-gnu-subject nil)

(defun debbugs-gnu-current-id (&optional noerror)
  (or (cdr (assq 'id (debbugs-gnu-current-status)))
      (and (not noerror)
	   (error "No bug on the current line"))))

(defun debbugs-gnu-current-status ()
  (get-text-property (line-beginning-position) 'tabulated-list-id))

(defun debbugs-gnu-display-status (query filter status)
  "Display the query, filter and status of the report on the current line."
  (interactive (list debbugs-gnu-local-query
		     debbugs-gnu-local-filter
		     (debbugs-gnu-current-status)))
  (switch-to-buffer "*Bug Status*")
  (let ((inhibit-read-only t))
    (erase-buffer)
    (when query
      (insert ";; Query\n")
      (pp query (current-buffer))
      (insert "\n"))
    (when filter
      (insert ";; Filter\n")
      (pp filter (current-buffer))
      (insert "\n"))
    (when status
      (insert ";; Status\n")
      (pp status (current-buffer)))
    (goto-char (point-min)))
  (set-buffer-modified-p nil)
  (special-mode))

(defun debbugs-read-emacs-bug-with-rmail (id status merged)
  "Read email exchange for debbugs bug ID.
STATUS is the bug's status list.
MERGED is the list of bugs merged with this one."
  (let* ((mbox-dir (make-temp-file "debbugs" t))
	 (mbox-fname (format "%s/bug_%d.mbox" mbox-dir id)))
    (debbugs-get-mbox id 'mboxmaint mbox-fname)
    (rmail mbox-fname)
    ;; Download messages of all the merged bug reports and append them
    ;; to the mailbox of the requested bug.
    (when merged
      (dolist (bugno merged)
	(let ((fn (make-temp-file "url")))
	  (debbugs-get-mbox bugno 'mboxmaint fn)
	  (rmail-get-new-mail fn)
	  (delete-file fn)
	  ;; Remove the 'unseen' attribute from all the messages we've
	  ;; just read, so that all of them appear in the summary with
	  ;; the same face.
	  (while (< rmail-current-message rmail-total-messages)
	    (rmail-show-message (1+ rmail-current-message))))))
    (set (make-local-variable 'debbugs-gnu-bug-number) id)
    (set (make-local-variable 'debbugs-gnu-subject)
	 (format "Re: bug#%d: %s" id (cdr (assq 'subject status))))
    (rmail-summary)
    (define-key rmail-summary-mode-map "C" 'debbugs-gnu-send-control-message)
    (set-window-text-height nil 10)
    (other-window 1)
    (define-key rmail-mode-map "C" 'debbugs-gnu-send-control-message)
    (rmail-show-message 1)))

(defun debbugs-read-emacs-bug-with-gnus (id status merged)
  "Read email exchange for debbugs bug ID.
STATUS is the bug's status list.
MERGED is the list of bugs merged with this one."
  (require 'gnus-dup)
  (setq gnus-suppress-duplicates t
	gnus-save-duplicate-list t)
  ;; Use Gnus.
  (gnus-read-ephemeral-emacs-bug-group
   (cons id (if (listp merged) merged (list merged)))
   (cons (current-buffer)
	 (current-window-configuration)))
  (with-current-buffer (window-buffer (selected-window))
    (set (make-local-variable 'debbugs-gnu-bug-number) id)
    (set (make-local-variable 'debbugs-gnu-subject)
	 (format "Re: bug#%d: %s" id (cdr (assq 'subject status))))
    (debbugs-gnu-summary-mode 1)))

(defun debbugs-gnu-select-report ()
  "Select the report on the current line."
  (interactive)
  (when (mouse-event-p last-input-event) (mouse-set-point last-input-event))
  ;; We open the report messages.
  (let* ((status (debbugs-gnu-current-status))
	 (id (cdr (assq 'id status)))
	 (merged (cdr (assq 'mergedwith status))))
    (setq merged (if (listp merged) merged (list merged)))
    (cond
     ((not id)
      (message "No bug report on the current line"))
     ((eq debbugs-gnu-mail-backend 'rmail)
      (debbugs-read-emacs-bug-with-rmail id status merged))
     ((eq debbugs-gnu-mail-backend 'gnus)
      (debbugs-read-emacs-bug-with-gnus id status merged))
     (t (error "No valid mail backend specified")))))

(defvar debbugs-gnu-summary-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "C" 'debbugs-gnu-send-control-message)
    (define-key map [(meta m)] 'debbugs-gnu-apply-patch)
    map))

(define-minor-mode debbugs-gnu-summary-mode
  "Minor mode for providing a debbugs interface in Gnus summary buffers.

\\{debbugs-gnu-summary-mode-map}"
  :lighter " Debbugs" :keymap debbugs-gnu-summary-mode-map
  (set (make-local-variable 'gnus-posting-styles)
       `((".*"
	  (eval
	   (when (buffer-live-p gnus-article-copy)
	     (with-current-buffer gnus-article-copy
	       (set (make-local-variable 'message-prune-recipient-rules)
		    '((".*@debbugs.*" "emacs-pretest-bug")
		      (".*@debbugs.*" "bug-gnu-emacs")
		      ("[0-9]+@debbugs.*" "submit@debbugs.gnu.org")
		      ("[0-9]+@debbugs.*" "quiet@debbugs.gnu.org")))
	       (set (make-local-variable 'message-alter-recipients-function)
		    (lambda (address)
		      (if (string-match "\\([0-9]+\\)@donarmstrong"
					(car address))
			  (let ((new (format "%s@debbugs.gnu.org"
					     (match-string 1 (car address)))))
			    (cons new new))
			address)))
	       ;; `gnus-posting-styles' is eval'ed after
	       ;; `message-simplify-subject'.  So we cannot use m-s-s.
	       (setq subject ,debbugs-gnu-subject))))))))

(defun debbugs-gnu-guess-current-id ()
  "Guess the ID based on \"#23\"."
  (save-excursion
    (beginning-of-line)
    (and
     (or (re-search-forward "#\\([0-9]+\\)" (line-end-position) t)
	 (progn
	   (goto-char (point-min))
	   (re-search-forward "#\\([0-9]+\\)" nil t)))
     (string-to-number (match-string 1)))))

(defun debbugs-gnu-proper-bug-number (id)
  "Check that ID is a number string and in the range of existing bugs."
  (and (string-match "^[1-9][0-9]*$" id)
       (<= (string-to-number id) (car (debbugs-newest-bugs 1)))))

(defvar debbugs-gnu-completion-table
  (completion-table-dynamic
   (lambda (string)
     (let* ((split (split-string string "-"))
	    (from (and (cdr split) (car split)))
	    (to (or (car (cdr split)) (car split))))
       (cond
	((> (length split) 2) nil)
	((and (or (zerop (length from)) (debbugs-gnu-proper-bug-number from))
	      (string-equal to ""))
	 (mapcar
	  (lambda (x) (concat string x))
	  (cons (unless from "-") '("1" "2" "3" "4" "5" "6" "7" "8" "9"))))
	((and (or (zerop (length from)) (debbugs-gnu-proper-bug-number from))
	      (debbugs-gnu-proper-bug-number to))
	 (mapcar
	  (lambda (x)
	    (and (debbugs-gnu-proper-bug-number (concat to x))
		 (concat string x)))
	  '("" "0" "1" "2" "3" "4" "5" "6" "7" "8" "9")))))))
  "Dynamic completion table for reading bug numbers.")

(defun debbugs-gnu-expand-bug-number-list (bug-number-list)
  "Expand BUG-NUMBER-LIST to a list of single bug numbers.
BUG-NUMBER-LIST is a list of bug numbers or bug number ranges, as
returned by `debbugs-gnu-bugs'."
  (let (result)
    (dolist (elt bug-number-list result)
      (let* ((split (split-string elt "-"))
	     (from (and (cdr split) (car split)))
	     (to (or (car (cdr split)) (car split))))
	(setq
	 result
	 (cond
	  ((or (> (length split) 2)
	       (zerop (length to)))
	   (user-error "Wrong bug number or range %s" elt))
	  ((null from)
	   (cons to result))
	  ((string-equal from "")
	   (append
	    (mapcar
	     'number-to-string
	     (debbugs-newest-bugs (string-to-number to)))
	    result))
	  (t (append
	      (mapcar
	       'number-to-string
	       (number-sequence (string-to-number from) (string-to-number to)))
	      result))))))))

(defun debbugs-gnu-send-control-message (message &optional reverse)
  "Send a control message for the current bug report.
You can set the severity or add a tag, or close the report.  If
you use the special \"done\" MESSAGE, the report will be marked as
fixed, and then closed.

If given a prefix, and given a tag to set, the tag will be
removed instead."
  (interactive
   (list (completing-read
	  "Control message: "
	  '("serious" "important" "normal" "minor" "wishlist"
	    "done" "donenotabug" "donewontfix" "doneunreproducible"
	    "unarchive" "unmerge" "reopen" "close"
	    "merge" "forcemerge"
	    "block" "unblock"
	    "owner" "noowner"
	    "invalid"
	    "reassign"
	    "retitle"
	    "patch" "wontfix" "moreinfo" "unreproducible" "fixed" "notabug"
	    "pending" "help" "security" "confirmed" "easy"
	    "usertag")
	  nil t)
	 current-prefix-arg))
  (let* ((id (or (debbugs-gnu-current-id t)
		 debbugs-gnu-bug-number	; Set on group entry.
		 (debbugs-gnu-guess-current-id)))
	 (status (debbugs-gnu-current-status))
	 (version
	  (when (and
		 (member message '("close" "done"))
		 (member "emacs" (cdr (assq 'package status))))
	    (read-string
	     "Version: "
	     (cond
	      ;; Emacs development versions.
	      ((if (boundp 'emacs-build-number)
		   (string-match
		    "^\\([0-9]+\\)\\.\\([0-9]+\\)\\.\\([0-9]+\\)" emacs-version)
		 (string-match
		  "^\\([0-9]+\\)\\.\\([0-9]+\\)\\.\\([0-9]+\\)\\." emacs-version))
	       (format "%s.%d"
		       (match-string 1 emacs-version)
		       (1+ (string-to-number (match-string 2 emacs-version)))))
	      ;; Emacs release versions.
	      ((if (boundp 'emacs-build-number)
		   (string-match
		    "^\\([0-9]+\\)\\.\\([0-9]+\\)$" emacs-version)
		 (string-match
		  "^\\([0-9]+\\)\\.\\([0-9]+\\)\\.\\([0-9]+\\)$" emacs-version))
	       (format "%s.%s"
		       (match-string 1 emacs-version)
		       (match-string 2 emacs-version)))
	      (t emacs-version))))))
    (with-temp-buffer
      (insert "To: control@debbugs.gnu.org\n"
	      "From: " (message-make-from) "\n"
	      (format "Subject: control message for bug #%d\n" id)
	      mail-header-separator
	      "\n"
	      (cond
	       ((member message '("unarchive" "unmerge" "reopen" "noowner"))
		(format "%s %d\n" message id))
	       ((member message '("merge" "forcemerge"))
		(format
		 "%s %d %s\n" message id
		 (mapconcat
		  'identity
		  (debbugs-gnu-expand-bug-number-list
		   (completing-read-multiple
		    (format "%s with bug(s) #: " (capitalize message))
		    debbugs-gnu-completion-table))
		  " ")))
	       ((member message '("block" "unblock"))
		(format
		 "%s %d by %s\n" message id
		 (mapconcat
		  'identity
		  (debbugs-gnu-expand-bug-number-list
		   (completing-read-multiple
		    (format "%s with bug(s) #: " (capitalize message))
		    (if (equal message "unblock")
			(mapcar 'number-to-string
				(cdr (assq 'blockedby status)))
		      debbugs-gnu-completion-table)
		    nil (and (equal message "unblock") status)))
		  " ")))
	       ((equal message "owner")
		(format "owner %d !\n" id))
	       ((equal message "retitle")
		(format "retitle %d %s\n" id (read-string "New title: ")))
	       ((equal message "reassign")
		(format "reassign %d %s\n" id (read-string "Package(s): ")))
	       ((equal message "close")
		(format "close %d %s\n" id (or version "")))
	       ((equal message "done")
		(format "tags %d fixed\nclose %d %s\n" id id (or version "")))
	       ((member message '("donenotabug" "donewontfix"
				  "doneunreproducible"))
		(format "tags %d %s\nclose %d\n" id (substring message 4) id))
	       ((member message '("serious" "important" "normal"
				  "minor" "wishlist"))
		(format "severity %d %s\n" id message))
	       ((equal message "invalid")
		(format "tags %d notabug\ntags %d wontfix\nclose %d\n"
			id id id))
	       ((equal message "usertag")
		(format "user %s\nusertag %d %s\n"
			(completing-read
			 "Package name or email address: "
			 (append
			  debbugs-gnu-all-packages (list user-mail-address))
			 nil nil (car debbugs-gnu-default-packages))
			id (read-string "User tag: ")))
	       (t
		(format "tags %d%s %s\n"
			id (if reverse " -" "")
			message))))
      (funcall (or debbugs-gnu-send-mail-function send-mail-function))
      (remhash id debbugs-cache-data)
      (message-goto-body)
      (message "Control message sent:\n%s"
	       (buffer-substring-no-properties (point) (1- (point-max)))))))

(defvar debbugs-gnu-usertags-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map tabulated-list-mode-map)
    (define-key map "\r" 'debbugs-gnu-select-usertag)
    (define-key map [mouse-2] 'debbugs-gnu-select-usertag)
    map))

(define-derived-mode debbugs-gnu-usertags-mode tabulated-list-mode "Usertags"
  "Major mode for listing user tags.

All normal editing commands are switched off.
\\<debbugs-gnu-usertags-mode-map>

The following commands are available:

\\{debbugs-gnu-usertags-mode-map}"
  (buffer-disable-undo)
  (setq truncate-lines t)
  (setq buffer-read-only t))

;;;###autoload
(defun debbugs-gnu-usertags (&rest users)
  "List all user tags for USERS, which is \(\"emacs\"\) by default."
  (interactive
   (if current-prefix-arg
       (completing-read-multiple
	"Package name(s) or email address: "
	(append debbugs-gnu-all-packages (list user-mail-address)) nil nil
	(mapconcat 'identity debbugs-gnu-default-packages ","))
     debbugs-gnu-default-packages))

  (unwind-protect
      (let ((inhibit-read-only t)
	    (debbugs-port "gnu.org")
	    (buffer-name "*Emacs User Tags*")
	    (user-tab-length
	     (1+ (apply 'max (length "User") (mapcar 'length users)))))

	;; Initialize variables.
	(when (and (file-exists-p debbugs-gnu-persistency-file)
		   (not debbugs-gnu-local-tags))
	  (with-temp-buffer
	    (insert-file-contents debbugs-gnu-persistency-file)
	    (eval (read (current-buffer)))))

	;; Create buffer.
	(when (get-buffer buffer-name)
	  (kill-buffer buffer-name))
	(switch-to-buffer (get-buffer-create buffer-name))
	(debbugs-gnu-usertags-mode)
	(setq tabulated-list-format `[("User" ,user-tab-length t)
				      ("Tag"  10 t)])
	(setq tabulated-list-sort-key (cons "User" nil))
	;(setq tabulated-list-printer 'debbugs-gnu-print-entry)

	;; Retrieve user tags.
	(dolist (user users)
	  (dolist (tag (sort (debbugs-get-usertag :user user) 'string<))
	    (add-to-list
	     'tabulated-list-entries
	     ;; `tabulated-list-id' is the parameter list for `debbugs-gnu'.
	     `((("tagged") (,user) nil nil (,tag))
	       ,(vector (propertize user 'mouse-face 'highlight)
			(propertize tag  'mouse-face 'highlight)))
	     'append)))

	;; Add local tags.
	(when debbugs-gnu-local-tags
	  (add-to-list
	     'tabulated-list-entries
	     `((("tagged"))
	       ,(vector
		 "" (propertize "(local tags)" 'mouse-face 'highlight)))))

	;; Show them.
	(tabulated-list-init-header)
	(tabulated-list-print)

	(set-buffer-modified-p nil)
	(goto-char (point-min)))))

(defun debbugs-gnu-select-usertag ()
  "Select the user tag on the current line."
  (interactive)
  (when (mouse-event-p last-input-event) (mouse-set-point last-input-event))
  ;; We open the bug reports.
  (let ((args (get-text-property (line-beginning-position) 'tabulated-list-id)))
    (when args (apply 'debbugs-gnu args))))

(defcustom debbugs-gnu-default-bug-number-list
  (propertize "-10" 'help-echo "The 10 most recent bugs.")
  "The default value used in interactive call of `debbugs-gnu-bugs'.
It must be a string, containing a comma separated list of bugs or bug ranges.
A negative value, -N, means the newest N bugs."
  :group 'debbugs-gnu
  :type 'string
  :version "25.2")

;;;###autoload
(defun debbugs-gnu-bugs (&rest bugs)
  "List all BUGS, a list of bug numbers.
In interactive calls, prompt for a comma separated list of bugs
or bug ranges, with default to `debbugs-gnu-default-bug-number-list'."
  (interactive
   (mapcar
    'string-to-number
    (debbugs-gnu-expand-bug-number-list
     (or
      (completing-read-multiple
       (format "Bug numbers (default %s): " debbugs-gnu-default-bug-number-list)
       debbugs-gnu-completion-table)
      (split-string debbugs-gnu-default-bug-number-list "," t)))))
  (dolist (elt bugs)
    (unless (natnump elt) (signal 'wrong-type-argument (list 'natnump elt))))
  (add-to-list 'debbugs-gnu-current-query (cons 'bugs bugs))
  ;; We do not suppress bugs requested explicitely.
  (setq debbugs-gnu-current-suppress nil)
  (debbugs-gnu nil))

(defcustom debbugs-gnu-trunk-directory "~/src/emacs/trunk/"
  "The directory where the main source tree lives."
  :group 'debbugs-gnu
  :type 'directory
  :version "25.2")

(defcustom debbugs-gnu-branch-directory "~/src/emacs/emacs-25/"
  "The directory where the previous source tree lives."
  :group 'debbugs-gnu
  :type 'directory
  :version "25.2")

(defvar debbugs-gnu-current-directory nil
  "The current source tree directory.")

(defun debbugs-gnu-init-current-directory (&optional branch)
"Initialize `debbugs-gnu-current-directory'."
  (setq debbugs-gnu-current-directory
	(or debbugs-gnu-current-directory
	    (if branch
		debbugs-gnu-branch-directory
	      debbugs-gnu-trunk-directory)))
  (unless (file-directory-p debbugs-gnu-current-directory)
    (setq debbugs-gnu-current-directory
	  (read-file-name
	   "Emacs repository location: "
	   debbugs-gnu-current-directory nil t nil 'file-directory-p))))

(defun debbugs-gnu-apply-patch (&optional branch)
  "Apply the patch from the current message.
If given a prefix, patch in the branch directory instead."
  (interactive "P")
  (add-hook 'emacs-lisp-mode-hook 'debbugs-gnu-lisp-mode)
  (add-hook 'diff-mode-hook 'debbugs-gnu-diff-mode)
  (add-hook 'change-log-mode-hook 'debbugs-gnu-change-mode)
  (debbugs-gnu-init-current-directory branch)
  (let ((rej (expand-file-name "debbugs-gnu.rej" temporary-file-directory))
	(output-buffer (get-buffer-create "*debbugs patch*"))
	(patch-buffers nil))
    (when (file-exists-p rej)
      (delete-file rej))
    (with-current-buffer output-buffer
      (erase-buffer))
    (gnus-summary-select-article nil t)
    ;; The patches are either in MIME attachements or the main article
    ;; buffer.  Determine which.
    (with-current-buffer gnus-article-buffer
      (dolist (handle (mapcar 'cdr (gnus-article-mime-handles)))
	(when
	    (string-match "diff\\|patch\\|plain" (mm-handle-media-type handle))
	  (push (cons (mm-handle-encoding handle)
		      (mm-handle-buffer handle))
		patch-buffers))))
    (unless patch-buffers
      (gnus-summary-show-article 'raw)
      (article-decode-charset)
      (push (cons nil gnus-article-buffer) patch-buffers))
    (dolist (elem patch-buffers)
      (with-current-buffer (generate-new-buffer "*debbugs input patch*")
	(insert-buffer-substring (cdr elem))
	(cond ((eq (car elem) 'base64)
	       (base64-decode-region (point-min) (point-max)))
	      ((eq (car elem) 'quoted-printable)
	       (quoted-printable-decode-region (point-min) (point-max))))
	(debbugs-gnu-fix-patch debbugs-gnu-current-directory)
	(call-process-region (point-min) (point-max)
			     "patch" nil output-buffer nil
			     "-r" rej "--no-backup-if-mismatch"
			     "-l" "-f"
			     "-d" (expand-file-name
				   debbugs-gnu-current-directory)
			     "-p1")))
    (set-buffer output-buffer)
    (when (file-exists-p rej)
      (goto-char (point-max))
      (insert-file-contents-literally rej))
    (goto-char (point-max))
    (save-some-buffers t)
    (require 'compile)
    (mapc 'kill-process compilation-in-progress)
    (compile
     (format
      "cd %s; make -k" (expand-file-name "lisp" debbugs-gnu-current-directory)))
    (vc-dir debbugs-gnu-current-directory)
    (vc-dir-hide-up-to-date)
    (goto-char (point-min))
    (sit-for 1)
    (vc-diff)
    ;; All these commands are asynchronous, so just wait a bit.  This
    ;; should be done properly a different way.
    (sit-for 2)
    ;; We've now done everything, so arrange the windows we need to see.
    (delete-other-windows)
    (switch-to-buffer output-buffer)
    (split-window)
    (split-window)
    (other-window 1)
    (switch-to-buffer "*compilation*")
    (goto-char (point-max))
    (other-window 1)
    (switch-to-buffer "*vc-diff*")
    (goto-char (point-min))))

(defun debbugs-gnu-fix-patch (dir)
  (require 'diff-mode)
  (setq dir (directory-file-name (expand-file-name dir)))
  (goto-char (point-min))
  (while (re-search-forward diff-file-header-re nil t)
    (goto-char (match-beginning 0))
    (let ((target-name (car (diff-hunk-file-names))))
      (when (and target-name
		 (or (not (string-match "/" target-name))
		     (and (string-match "^[ab]/" target-name)
			  (not (file-exists-p
				(expand-file-name (substring target-name 2)
						  dir))))
		     (file-exists-p (expand-file-name target-name dir))))
	;; We have a simple patch that refers to a file somewhere in the
	;; tree.  Find it.
	(when-let ((files (directory-files-recursively
			   dir
			   (concat "^" (regexp-quote
					(file-name-nondirectory target-name))
				       "$"))))
	  (when (re-search-forward (concat "^[+]+ "
					   (regexp-quote target-name)
					   "\\([ \t\n]\\)")
				   nil t)
	    (replace-match (concat "+++ a"
				   (substring (car files) (length dir))
				   (match-string 1))
			   nil t)))))
    (forward-line 2)))

(defun debbugs-gnu-find-contributor (string)
  "Search through ChangeLogs to find contributors."
  (interactive "sContributor match: ")
  (debbugs-gnu-init-current-directory)
  (let ((found 0)
	(match (concat "^[0-9].*" string)))
    (dolist (file (directory-files-recursively
		   debbugs-gnu-current-directory "ChangeLog\\(.[0-9]+\\)?$"))
      (with-temp-buffer
	(when (file-exists-p file)
	  (insert-file-contents file))
	(goto-char (point-min))
	(while (and (re-search-forward match nil t)
		    (not (looking-at ".*tiny change")))
	  (cl-incf found))))
    (message "%s is a contributor %d times" string found)
    found))

(defvar debbugs-gnu-patch-subject nil)

(defun debbugs-gnu-insert-changelog ()
  "Add a ChangeLog from a recently applied patch from a third party."
  (interactive)
  (let (from subject patch-subject changelog
	     patch-from)
    (with-current-buffer gnus-article-buffer
      (widen)
      (goto-char (point-min))
      (setq from (gnus-fetch-field "from")
	    subject (gnus-fetch-field "subject"))
      ;; If it's a patch formatted the right way, extract that data.
      (dolist (handle (mapcar 'cdr (gnus-article-mime-handles)))
	(when (string-match "diff\\|patch\\|plain"
			    (mm-handle-media-type handle))
	  (with-temp-buffer
	    (insert-buffer-substring (mm-handle-buffer handle))
	    (cond ((eq (mm-handle-encoding handle) 'base64)
		   (base64-decode-region (point-min) (point-max)))
		  ((eq (mm-handle-encoding handle) 'quoted-printable)
		   (quoted-printable-decode-region (point-min) (point-max))))
	    (setq patch-subject
		  (or (gnus-fetch-field "subject") patch-subject))
	    (setq patch-from
		  (or (gnus-fetch-field "from") patch-from))
	    (goto-char (point-min))
	    (when (re-search-forward "^[*] " nil t)
	      (let ((start (match-beginning 0)))
		(while (and (not (eobp))
			    (not (looking-at "---")))
		  (forward-line 1))
		(setq changelog (buffer-substring
				 start (line-end-position 0)))))))))
    (setq from (mail-extract-address-components (or patch-from from)))
    (let ((add-log-full-name (car from))
	  (add-log-mailing-address (cadr from)))
      (add-change-log-entry-other-window)
      (when patch-subject
	(setq-local debbugs-gnu-patch-subject patch-subject))
      (when changelog
	(delete-region (line-beginning-position) (point-max))
	(save-restriction
	  (narrow-to-region (point) (point))
	  (insert changelog)
	  (indent-region (point-min) (point-max))))
      (let ((point (point)))
	(when (string-match "\\(bug#[0-9]+\\)" subject)
	  (insert " (" (match-string 1 subject) ")."))
	(when (zerop (debbugs-gnu-find-contributor
		      (let ((bits (split-string (car from))))
			(cond
			 ((>= (length bits) 2)
			  (format "%s.*%s" (car bits) (car (last bits))))
			 ((= (length bits) 1)
			  (car bits))
			 ;; Fall back on the email address.
			 (t
			  (cadr from))))))
	  (goto-char (point-max))
	  (end-of-line)
	  (when changelog
	    (insert "\n\n"))
	  (insert "  Copyright-paperwork-exempt: yes"))
	(goto-char point)))))

(defvar debbugs-gnu-lisp-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(meta m)] 'debbugs-gnu-insert-changelog)
    map))

(define-minor-mode debbugs-gnu-lisp-mode
  "Minor mode for providing a debbugs interface in Lisp buffers.
\\{debbugs-gnu-lisp-mode-map}"
  :lighter " Debbugs" :keymap debbugs-gnu-lisp-mode-map)

(defvar debbugs-gnu-diff-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(meta m)] 'debbugs-gnu-diff-select)
    map))

(define-minor-mode debbugs-gnu-diff-mode
  "Minor mode for providing a debbugs interface in diff buffers.
\\{debbugs-gnu-diff-mode-map}"
  :lighter " Debbugs" :keymap debbugs-gnu-diff-mode-map)

(defun debbugs-gnu-diff-select ()
  "Select the diff under point."
  (interactive)
  (delete-other-windows)
  (diff-goto-source))

(defvar debbugs-gnu-change-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(meta m)] 'debbugs-gnu-change-checkin)
    map))

(define-minor-mode debbugs-gnu-change-mode
  "Minor mode for providing a debbugs interface in ChangeLog buffers.
\\{debbugs-gnu-change-mode-map}"
  :lighter " Debbugs" :keymap debbugs-gnu-change-mode-map)

(defun debbugs-gnu-change-checkin ()
  "Prepare checking in the current changes."
  (interactive)
  (debbugs-gnu-init-current-directory)
  (save-some-buffers t)
  (when (get-buffer "*vc-dir*")
    (kill-buffer (get-buffer "*vc-dir*")))
  (let ((patch-subject debbugs-gnu-patch-subject))
    (vc-dir debbugs-gnu-current-directory)
    (goto-char (point-min))
    (while (not (search-forward "edited" nil t))
      (sit-for 0.01))
    (beginning-of-line)
    (while (search-forward "edited" nil t)
      (vc-dir-mark)
      (beginning-of-line))
    (vc-diff nil)
    (vc-next-action nil)
    (delete-region (point-min) (point-max))
    (log-edit-insert-changelog t)
    (delete-other-windows)
    (split-window)
    (other-window 1)
    (switch-to-buffer "*vc-diff*")
    (other-window 1)
    (when patch-subject
      (insert "Summary: "
	      (replace-regexp-in-string "^ *\\[PATCH\\] *" "" patch-subject)
	      "\n"))))

(defun debbugs-gnu-save-cache ()
  "Save the bugs cache to a file."
  (interactive)
  (unless debbugs-cache-data
    (error "No data to cache"))
  (unless (file-exists-p "~/.emacs.d/debbugs-cache")
    (make-directory "~/.emacs.d/debbugs-cache" t))
  (let ((coding-system-for-write 'utf-8))
    (with-temp-file "~/.emacs.d/debbugs-cache/list"
      (prin1 debbugs-cache-data (current-buffer)))))

(provide 'debbugs-gnu)

;;; TODO:

;; * Extend SOAP interface to get all bugs modified in a given timeframe.

;; * Extend SOAP interface to get existing package names on the
;;  server, in order not to hardcode them.

;; * Add debbugs commands to commit messages.
;;   It'd be nice if the language would be something along the lines of
;;
;;   bug#45 done
;;   bug#45 tags 25.1 fixed
;;
;;   That is, that you could drop arbitrary debbugs commands into
;;   commit messages.

;; * The bug tracker should be aware of repositories, branches,
;;   commits, contributors, and ticket links or mentions in commit
;;   messages.
;;
;;   For me personally, if I can *see* the specific code that fixes a
;;   ticket inside the ticket as a commit, and click my way to the
;;   wider commit and then diff from before that commit against
;;   today's state of that code, I've built a mental map of the code
;;   that would otherwise take me a lot of work. That's one common
;;   workflow. Another is to view several commits that fix a single
;;   ticket in one place. So it's not revolutionary, just simpler and
;;   more straightforward for the user.
;;
;;   Being able to close a bug just by mentioning it in a certain way
;;   in the commit message and pushing that commit is also handy. You
;;   don't have to switch to the bug discussion and duplicate that
;;   info there manually.

;; * Contributors should be able to tag and notify each other.
;;
;;   You mean to (re)assign bugs to particular persons and things like that?

;;   Yes, plus ping someone or a team specifically: "hey, maybe the
;;   @gnus team should look at this" in a comment.

;; * Markdown should be well supported.

;; * Inline code comments should be easy, and linked to a commit (so
;;   an updated commit can resolve the comment). This is just the
;;   essential stuff.

;;   Rebase or amend+force push would update a branch destructively,
;;   which in a pull request context should show you that a comment
;;   was for a commit that's no longer in the branch. Furthermore some
;;   trackers allow you to mark a comment as resolved (e.g. Github
;;   recently added reactions, which can be used as ad-hoc markup).
;;
;;   Even if you don't rebase, but just push a new commit to the
;;   branch upon review, IIRC both Github and Gitlab can see that the
;;   changes that started a particular discussion are no longer there
;;   (and collapse the comment sub-thread a no longer relevant, while
;;   allowing the user to expand it again if they so wish).
;;
;;   I think I'm starting to see what you mean.  You're talking about
;;   a tight integration where a pull-request is also itself an issue,
;;   so the comments can be directly on the patch itself.  As opposed
;;   to having issues and pull-request be two separate things that can
;;   refer to each other via an indirection.
;;
;;   So this is particularly useful/meaningful when reviewing a
;;   proposed patch from another developer, rather than when
;;   interacting with an end-user trying to track down some bugs
;;   here's experiencing (which is the kind of use-case I've had in
;;   mind when working on BugIt).
;;
;;   But indeed, the two use-cases would best be served by the same
;;   tool since after the bug is tracked a patch might show up to fix
;;   it, after which a review process will come up.
;;
;;   And on the more basic level, compared to flat discussions in
;;   mailing lists, having separate subthread for each part of the
;;   patch the reviewer commented on, is great. You can have
;;   discussion sub-threads in the mailing list too, but people never
;;   split their emails in pieces that small.
;;
;; * The next link in the chain are CI/CD hooks. You can set up a
;;   Github repo, for instance, to build every pull request before the
;;   reviewer ever looks, which saves a lot of time with compiled
;;   languages. It will run tests and so on, but most important is
;;   that it keeps the context inside the pull request, you don't have
;;   to go elsewhere.

;;; debbugs-gnu.el ends here
