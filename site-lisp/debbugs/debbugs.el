;;; debbugs.el --- SOAP library to access debbugs servers

;; Copyright (C) 2011 Free Software Foundation, Inc.

;; Author: Michael Albinus <michael.albinus@gmx.de>
;; Keywords: comm, hypermedia
;; Package: debbugs
;; Version: 0.3

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This package provides some basic functions to access a debbugs SOAP
;; server (see <http://wiki.debian.org/DebbugsSoapInterface>).

;; The SOAP functions "get_usertag" and "get_versions" are not
;; implemented (yet).

;;; Code:

;(setq soap-debug t message-log-max t)
(require 'soap-client)
(eval-when-compile (require 'cl))

(defgroup debbugs nil
  "Debbugs library"
  :group 'hypermedia)

(defcustom debbugs-servers
  '(("gnu.org"
     :wsdl "http://debbugs.gnu.org/cgi/soap.cgi?WSDL"
     :bugreport-url "http://debbugs.gnu.org/cgi/bugreport.cgi")
    ("debian.org"
     :wsdl "http://bugs.debian.org/cgi-bin/soap.cgi?WSDL"
     :bugreport-url "http://bugs.debian.org/cgi-bin/bugreport.cgi"))
  "*List of Debbugs server specifiers.
Each entry is a list that contains a string identifying the port
name and the server parameters in keyword-value form. Allowed
keywords are:

`:wsdl' -- Location of WSDL. The value is a string with URL that
should return the WSDL specification of Debbugs/SOAP service.

`:bugreport-url' -- URL of the server script that returns mboxes
with bug logs.

The list initially contains two predefined and configured Debbugs
servers: \"gnu.org\" and \"debian.org\"."
  :group 'debbugs
  :link '(custom-manual "(debbugs)Debbugs server specifiers")
  :type '(choice
	  (const nil)
	  (repeat
	   (cons :tag "Server"
		 (string :tag "Port name")
		 (checklist :tag "Options" :greedy t
			    (group :inline t
				   (const :format "" :value :wsdl)
				   (string :tag "WSDL"))
			    (group :inline t
				   (const :format "" :value :bugreport-url)
				   (string :tag "Bugreport URL")))))))

(defcustom debbugs-port "gnu.org"
  "The port instance to be applied from `debbugs-wsdl'.
This corresponds to the Debbugs server to be accessed, either
\"gnu.org\", or \"debian.org\", or user defined port name."
  ;; Maybe we should create an own group?
  :group 'debbugs
  :type '(choice :tag "Debbugs server" (const "gnu.org") (const "debian.org")
		 (string :tag "user defined port name")))

;; It would be nice if we could retrieve it from the debbugs server.
;; Not supported yet.
(defconst debbugs-wsdl
  (soap-load-wsdl
   (expand-file-name
    "Debbugs.wsdl"
    (if load-in-progress
	(file-name-directory load-file-name)
      default-directory)))
  "The WSDL object to be used describing the SOAP interface.")

(defun debbugs-get-bugs (&rest query)
  "Return a list of bug numbers which match QUERY.

QUERY is a sequence of keyword-value pairs where the values are
strings, i.e. :KEYWORD \"VALUE\" [:KEYWORD \"VALUE\"]*

The keyword-value pair is a subquery.  The keywords are allowed to
have multiple occurrence within the query at any place.  The
subqueries with the same keyword form the logical subquery, which
returns the union of bugs of every subquery it contains.

The result of the QUERY is an intersection of results of all
subqueries.

Valid keywords are:

  :package -- The value is the name of the package a bug belongs
  to, like \"emacs\", \"coreutils\", \"gnus\", or \"tramp\".

  :src -- This is used to retrieve bugs that belong to source
  with given name.

  :severity -- This is the severity of the bug.  The exact set of
  allowed values depends on the Debbugs port.  Examples are
  \"normal\", \"minor\", \"wishlist\" etc.

  :tag -- An arbitrary string the bug is annotated with.
  Usually, this is used to mark the status of the bug, like
  \"fixed\", \"moreinfo\", \"notabug\", \"patch\",
  \"unreproducible\" or \"wontfix\".  The exact set of tags
  depends on the Debbugs port.

  :owner -- This is used to identify bugs by the owner's email
  address.  The special email address \"me\" is used as pattern,
  replaced with `user-mail-address'.

  :submitter -- With this keyword it is possible to filter bugs
  by the submitter's email address.  The special email address
  \"me\" is used as pattern, replaced with `user-mail-address'.

  :maint -- This is used to find bugs of the packages which are
  maintained by the person with the given email address.  The
  special email address \"me\" is used as pattern, replaced with
  `user-mail-address'.

  :correspondent -- This allows to find bug reports where the
  person with the given email address has participated.  The
  special email address \"me\" is used as pattern, replaced with
  `user-mail-address'.

  :affects -- With this keyword it is possible to find bugs which
  affect the package with the given name.  The bugs are chosen by
  the value of field `affects' in bug's status.  The returned bugs
  do not necessary belong to this package.

  :status -- Status of bug.  Valid values are \"done\",
  \"forwarded\" and \"open\".

  :archive -- A keyword to filter for bugs which are already
  archived, or not.  Valid values are \"0\" (not archived),
  \"1\" (archived) or \"both\".  If this keyword is not given in
  the query, `:archive \"0\"' is assumed by default.

Example.  Get all opened and forwarded release critical bugs for
the packages which are maintained by \"me\" and which have a
patch:

  \(debbugs-get-bugs :maint \"me\" :tag \"patch\"
                     :severity \"critical\"
                     :status \"open\"
                     :severity \"grave\"
                     :status \"forwarded\"
                     :severity \"serious\")"

  (let (vec kw key val)
    ;; Check query.
    (while (and (consp query) (<= 2 (length query)))
      (setq kw (pop query)
	    val (pop query))
      (unless (and (keywordp kw) (stringp val))
	(error "Wrong query: %s %s" kw val))
      (setq key (substring (symbol-name kw) 1))
      (case kw
	((:package :severity :tag :src :affects)
	 ;; Value shall be one word.
	 (if (string-match "\\`\\S-+\\'" val)
	     (setq vec (vconcat vec (list key val)))
	   (error "Wrong %s: %s" key val)))
	((:owner :submitter :maint :correspondent)
	 ;; Value is an email address.
	 (if (string-match "\\`\\S-+\\'" val)
	     (progn
	       (when (string-equal "me" val)
		 (setq val user-mail-address))
	       (when (string-match "<\\(.+\\)>" val)
		 (setq val (match-string 1 val)))
	       (setq vec (vconcat vec (list key val))))
	   (error "Wrong %s: %s" key val)))
	(:status
	 ;; Possible values: "done", "forwarded" and "open"
	 (if (string-match "\\`\\(done\\|forwarded\\|open\\)\\'" val)
	     (setq vec (vconcat vec (list key val)))
	   (error "Wrong %s: %s" key val)))
	(:archive
	 ;; Value is `0' or `1' or `both'.
	 (if (string-match "\\`\\(0\\|1\\|both\\)\\'" val)
	     (setq vec (vconcat vec (list key val)))
	   (error "Wrong %s: %s" key val)))
	(t (error "Unknown key: %s" kw))))

    (unless (null query)
      (error "Unknown key: %s" (car query)))
    (sort (car (soap-invoke debbugs-wsdl debbugs-port "get_bugs" vec)) '<)))

(defun debbugs-newest-bugs (amount)
  "Return the list of bug numbers, according to AMOUNT (a number) latest bugs."
  (sort (car (soap-invoke debbugs-wsdl debbugs-port "newest_bugs" amount)) '<))

(defun debbugs-get-status (&rest bug-numbers)
  "Return a list of status entries for the bugs identified by BUG-NUMBERS.

Every returned entry is an association list with the following attributes:

  `bug_num': The bug number.

  `package': A list of package names the bug belongs to.

  `severity': The severity of the bug report. This can be
  \"important\", \"grave\", \"normal\", \"minor\" or \"wishlist\".

  `tags': The status of the bug report, a list of strings.  This
  can be \"fixed\", \"notabug\", \"wontfix\", \"unreproducible\",
  \"moreinfo\" or \"patch\".

  `pending': The string \"pending\", \"forwarded\" or \"done\".

  `subject': Subject/Title of the bugreport.

  `originator': Submitter of the bugreport.

  `mergedwith': A list of bug numbers this bug was merged with.

  `source': Source package name of the bug report.

  `date': Date of bug creation.

  `log_modified', `last_modified': Date of last update.

  `found_date', `fixed_date': Date of bug report / bug fix
  \(empty for now).

  `done': The email address of the worker who has closed the bug (if done).

  `archived': `t' if the bug is archived, `nil' otherwise.

  `unarchived': The date the bug has been unarchived, if ever.

  `found_versions', `fixed_versions': List of version strings.

  `forwarded': A URL or an email address.

  `blocks': A list of bug numbers this bug blocks.

  `blockedby': A list of bug numbers this bug is blocked by.

  `msgid': The message id of the initial bug report.

  `owner': Who is responsible for fixing.

  `location': Always the string \"db-h\" or \"archive\".

  `affects': A list of package names.

  `summary': Arbitrary text.

Example:

  \(debbugs-get-status 10)

  => ;; Attributes with empty values are not show
     \(\(\(bug_num . 10)
       \(source . \"unknown\")
       \(date . 1203606305.0)
       \(msgid . \"<87zltuz7eh.fsf@freemail.hu>\")
       \(severity . \"wishlist\")
       \(owner . \"Magnus Henoch <mange@freemail.hu>\")
       \(log_modified . 1261079402.0)
       \(location . \"db-h\")
       \(subject . \"url-gw should support HTTP CONNECT proxies\")
       \(originator . \"Magnus Henoch <mange@freemail.hu>\")
       \(last_modified . 1271200046.0)
       \(pending . \"pending\")
       \(package \"emacs\")))"
  (when bug-numbers
    (let ((object
	   (car
	    (soap-invoke
	     debbugs-wsdl debbugs-port "get_status"
	     (apply 'vector bug-numbers)))))
      (mapcar
       (lambda (x)
	 (let (y)
	   ;; "archived" is the number 1 or 0.
	   (setq y (assoc 'archived (cdr (assoc 'value x))))
	   (setcdr y (= (cdr y) 1))
	   ;; "found_versions" and "fixed_versions" are lists,
	   ;; containing strings or numbers.
	   (dolist (attribute '(found_versions fixed_versions))
	     (setq y (assoc attribute (cdr (assoc 'value x))))
	     (setcdr y (mapcar
			(lambda (z) (if (numberp z) (number-to-string z) z))
			(cdr y))))
	   ;; "mergedwith" is a string, containing blank separated bug numbers.
	   (setq y (assoc 'mergedwith (cdr (assoc 'value x))))
	   (when (stringp (cdr y))
	     (setcdr y (mapcar 'string-to-number (split-string (cdr y) " " t))))
	   ;; "package" is a string, containing comma separated
	   ;; package names.  "keywords" and "tags" are strings,
	   ;; containing blank separated package names.
	   (dolist (attribute '(package keywords tags))
	     (setq y (assoc attribute (cdr (assoc 'value x))))
	     (when (stringp (cdr y))
	       (setcdr y (split-string (cdr y) ",\\| " t))))
	   (cdr (assoc 'value x))))
       object))))

(defun debbugs-get-bug-log (bug-number)
  "Return a list of messages related to BUG-NUMBER.

Every message is an association list with the following attributes:

  `msg_num': The number of the message inside the bug log.  The
  numbers are ascending, newer messages have a higher number.

  `header': The message header lines, as arrived at the bug tracker.

  `body': The message body.

  `attachments' A list of possible attachments, or `nil'.  Not
  implemented yet server side."
  (car (soap-invoke debbugs-wsdl debbugs-port "get_bug_log" bug-number)))

(defun debbugs-search-est (&rest query)
  "Return the result of a full text search according to QUERY.

QUERY is a sequence of lists of keyword-value pairs where the
values are strings or numbers, i.e. :KEYWORD \"VALUE\" [:KEYWORD
VALUE]*

Every sublist of the QUERY forms a hyperestraier condition.  A
detailed description of hyperestraier conditions can be found at
URL `http://fallabs.com/hyperestraier/uguide-en.html#searchcond'.

The following conditions are possible:

\[:phrase SEARCH-PHRASE :skip NUMBER :max NUMBER\]

  The string SEARCH-PHRASE forms the search on the database.  It
  contains words to be searched for, combined by operators like
  AND, ANDNOT and OR.  If there is no operator between the words,
  AND is used by default.  The phrase keyword and value can also
  be omitted, this is useful in combination with other conditions.

  :skip and :max are optional.  They specify, how many hits are
  skipped, and how many maximal hits are returned.  This can be
  used for paged results.  Per default, :skip is 0 and :max is 10.

  There must be exactly one such condition.

\[ATTRIBUTE VALUE+ :operation OPERATION :order ORDER\]

  ATTRIBUTE is one of the following keywords:

  :status --  Status of bug.  Valid values are \"done\",
  \"forwarded\" and \"open\".

  :subject, :@title -- The subject of a message or the title of
  the bug, a string.

  :date, :@cdate -- The submission or modification dates of a
  message, a number.

  :submitter, :@author -- The email address of the submitter of a
  bug or the author of a message belonging to this bug, a string.
  The special email address \"me\" is used as pattern, replaced
  with `user-mail-address'.

  :package -- The value is the name of the package a bug belongs
  to, like \"emacs\", \"coreutils\", \"gnus\", or \"tramp\".

  :tags -- An arbitrary string the bug is annotated with.

  :severity -- This is the severity of the bug.  The exact set of
  allowed values depends on the Debbugs port.  Examples are
  \"normal\", \"minor\", \"wishlist\" etc.

  :operator defines the comparison operator to be applied to
  ATTRIBUTE.  For string attributes this could be \"STREQ\" \(is
  equal to the string), \"STRNE\" \(is not equal to the string),
  \"STRINC\" \(includes the string), \"STRBW\" \(begins with the
  string), \"STREW\" \(ends with the string), \"STRAND\"
  \(includes all tokens in the string), \"STROR\" \(includes at
  least one token in the string), \"STROREQ\" \(is equal to at
  least one token in the string) or \"STRRX\" \(matches regular
  expressions of the string).  For operators with tokens, several
  values for ATTRIBUTE shall be used.

  Numbers can be compared by the operators \"NUMEQ\" \(is equal
  to the number), \"NUMNE\" \(is not equal to the number),
  \"NUMGT\" \(is greater than the number), \"NUMGE\" \(is greater
  than or equal to the number), \"NUMLT\" \(is less than the
  number), \"NUMLE\" \(is less than or equal to the number) or
  \"NUMBT\" \(is between the two numbers).  In the last case,
  there must be two values for ATTRIBUTE.

  If an operator is leaded by \"!\", the meaning is inverted.  If
  a string operator is leaded by \"I\", the case of the value is
  ignored.

  The optional :order can be specified only in one condition.  It
  means, that ATTRIBUTE is used for sorting the results.  The
  following order operators exist: \"STRA\" \(ascending by
  string), \"STRD\" \(descending by string), \"NUMA\" \(ascending
  by number) or \"NUMD\" \(descending by number).

  A special case is an :order, where there is no corresponding
  attribute value and no operator.  In this case, ATTRIBUTE is
  not used for the search.

The result of the QUERY is a list of association lists with the
same attributes as in the conditions.  Additional attributes are

  `id': The bug number.

  `msg_num': The number of the message inside the bug log.

  `snippet': The surrounding text found by the search.  For the
  syntax of the snippet, consult the hyperestraier user guide.

Examples:

  \(debbugs-search-est
    '\(:phrase \"armstrong AND debbugs\" :skip 10 :max 2)
    '\(:severity \"normal\" :operator \"STRINC\")
    '\(:date :order \"NUMA\"))

  => \(\(\(msg_num . 21)
       \(date . 1229208302)
       \(@author . \"Glenn Morris <rgm@gnu.org>\")
       \(@title . \"Re: bug#1567: Mailing an archived bug\")
       \(id . 1567)
       \(severity . \"normal\")
       \(@cdate . \"Wed, 17 Dec 2008 14:34:50 -0500\")
       \(snippet . \"...\")
       \(subject . \"Mailing an archived bug\")
       \(package . \"debbugs.gnu.org\"))
      ...)

  ;; Show all messages from me between 2011-08-01 and 2011-08-31.
  \(debbugs-search-est
    '\(:max 20)
    '\(:@author \"me\" :operator \"ISTRINC\")
    `\(:date
      ,\(floor \(float-time \(encode-time 0 0 0  1 8 2011)))
      ,\(floor \(float-time \(encode-time 0 0 0 31 8 2011)))
      :operator \"NUMBT\"))"

  (let (args result)
    ;; Compile search arguments.
    (dolist (elt query)
      (let (vec kw key val
	    phrase-cond attr-cond)

	;; Phrase is mandatory, even if empty.
	(when (and (or  (member :skip elt) (member :max elt))
		   (not (member :phrase elt)))
	  (setq vec (vector "phrase" "")))

	;; Parse condition.
	(while (consp elt)
	  (setq kw (pop elt))
	  (unless (keywordp kw)
	    (error "Wrong keyword: %s" kw))
	  (setq key (substring (symbol-name kw) 1))
	  (case kw
	    ;; Phrase condition.
	    (:phrase
	     ;; It shouldn't happen in an attribute condition.
	     (if attr-cond
		 (error "Wrong keyword: %s" kw))
	     (setq phrase-cond t val (pop elt))
	     ;; Value is a string.
	     (if (stringp val)
		 (setq vec (vconcat vec (list key val)))
	       (error "Wrong %s: %s" key val)))

	    ((:skip :max)
	     ;; It shouldn't happen in an attribute condition.
	     (if attr-cond
		 (error "Wrong keyword: %s" kw))
	     (setq phrase-cond t val (pop elt))
	     ;; Value is a number.
	     (if (numberp val)
		 (setq vec (vconcat vec (list key (number-to-string val))))
	       (error "Wrong %s: %s" key val)))

	    ;; Attribute condition.
	    ((:submitter :@author)
	     ;; It shouldn't happen in a phrase condition.
	     (if phrase-cond
		 (error "Wrong keyword: %s" kw))
	     (if (not (stringp (car elt)))
		 (setq vec (vconcat vec (list key "")))
	       ;; Value is an email address.
	       (while (and (stringp (car elt))
			   (string-match "\\`\\S-+\\'" (car elt)))
		 (when (string-equal "me" (car elt))
		   (setcar elt user-mail-address))
		 (when (string-match "<\\(.+\\)>" (car elt))
		   (setcar elt (match-string 1 (car elt))))
		 (add-to-list 'val (pop elt) 'append))
	       (setq vec
		     (vconcat vec (list key (mapconcat 'identity val " "))))))

	    (:status
	     ;; It shouldn't happen in a phrase condition.
	     (if phrase-cond
		 (error "Wrong keyword: %s" kw))
	     (setq attr-cond t)
	     (if (not (stringp (car elt)))
		 (setq vec (vconcat vec (list key "")))
	       ;; Possible values: "done", "forwarded" and "open"
	       (while  (and (stringp (car elt))
			    (string-match
			     "\\`\\(done\\|forwarded\\|open\\)\\'" (car elt)))
		 (add-to-list 'val (pop elt) 'append))
	       (setq vec
		     (vconcat vec (list key (mapconcat 'identity val " "))))))

	    ((:subject :package :tags :severity :@title)
	     ;; It shouldn't happen in a phrase condition.
	     (if phrase-cond
		 (error "Wrong keyword: %s" kw))
	     (setq attr-cond t)
	     (if (not (stringp (car elt)))
		 (setq vec (vconcat vec (list key "")))
	       ;; Just a string.
	       (while (stringp (car elt))
		 (add-to-list 'val (pop elt) 'append))
	       (setq vec
		     (vconcat vec (list key (mapconcat 'identity val " "))))))

	    ((:date :@cdate)
	     ;; It shouldn't happen in a phrase condition.
	     (if phrase-cond
		 (error "Wrong keyword: %s" kw))
	     (setq attr-cond t)
	     (if (not (numberp (car elt)))
		 (setq vec (vconcat vec (list key "")))
	       ;; Just a number.
	       (while (numberp (car elt))
		 (add-to-list 'val (pop elt) 'append))
	       (setq vec
		     (vconcat
		      vec (list key (mapconcat 'number-to-string val " "))))))

	    ((:operator :order)
	     ;; It shouldn't happen in a phrase condition.
	     (if phrase-cond
		 (error "Wrong keyword: %s" kw))
	     (setq attr-cond t val (pop elt))
	     ;; Value is a number.
	     (if (stringp val)
		 (setq vec (vconcat vec (list key val)))
	       (error "Wrong %s: %s" key val)))

	    (t (error "Unknown key: %s" kw))))

	(setq args (vconcat args (list vec)))))

    (setq result
	  (car (soap-invoke debbugs-wsdl debbugs-port "search_est" args)))
    ;; The result contains lists (key value).  We transform it into
    ;; cons cells (key . value).
    (dolist (elt1 result result)
      (dolist (elt2 elt1)
	(setcdr elt2 (cadr elt2))))))

(defun debbugs-get-attribute (bug-or-message attribute)
  "Return the value of key ATTRIBUTE.

BUG-OR-MESSAGE must be list element returned by either
`debbugs-get-status' or `debbugs-get-bug-log'.

Example: Return the originator of last submitted bug.

\(debbugs-get-attribute
  \(car \(apply 'debbugs-get-status \(debbugs-newest-bugs 1))) 'originator)"
  (cdr (assoc attribute bug-or-message)))

(defun debbugs-get-message-numbers (messages)
  "Return the message numbers of MESSAGES.
MESSAGES must be the result of a `debbugs-get-bug-log' call."
  (mapcar (lambda (x) (debbugs-get-attribute x 'msg_num)) messages))

(defun debbugs-get-message (messages message-number)
  "Return the message MESSAGE-NUMBER of MESSAGES.
MESSAGES must be the result of a `debbugs-get-bug-log' call.

The returned message is a list of strings.  The first element are
the header lines of the message, the second element is the body
of the message.  Further elements of the list, if any, are
attachments of the message.

If there is no message with MESSAGE-NUMBER, the function returns `nil'.

Example: Return the first message of last submitted bug.

\(let \(\(messages \(apply 'debbugs-get-bug-log \(debbugs-newest-bugs 1))))
  \(debbugs-get-message messages
		       \(car \(debbugs-get-message-numbers messages))))"
  (while (and messages
	      (/= (debbugs-get-attribute (car messages) 'msg_num)
		  message-number))
    (setq messages (cdr messages)))
  (when messages
    (append (list (debbugs-get-attribute (car messages) 'header)
		  (debbugs-get-attribute (car messages) 'body))
	    (debbugs-get-attribute (car messages) 'attachments))))

(defun debbugs-get-mbox (bug-number mbox-type &optional filename)
  "Download mbox with messages of bug BUG-NUMBER from Debbugs server.
BUG-NUMBER is a number of bug.  It must be of integer type.

MBOX-TYPE specifies a type of mbox and can be one of the
following symbols:

   `mboxfolder': Download mbox folder.

   `mboxmaint': Download maintainer's mbox.

   `mboxstat', `mboxstatus': Download status mbox.  The use of
   either symbol depends on actual Debbugs server configuration.
   For gnu.org, use the former; for debian.org - the latter.

FILENAME, if non-`nil', is the name of file to store mbox.  If
FILENAME is `nil', the downloaded mbox is inserted into the
current buffer."
  (let (url (mt "") bn)
    (unless (setq url (plist-get
		       (cdr (assoc debbugs-port debbugs-servers))
		       :bugreport-url))
      (error "URL of bugreport script for port %s is not specified"
	     debbugs-port))
    (setq bn (format "bug=%s;" (number-to-string bug-number)))
    (unless (eq mbox-type 'mboxfolder)
      (if (memq mbox-type '(mboxmaint mboxstat mboxstatus))
	  (setq mt (concat (symbol-name mbox-type) "=yes;"))
	(error "Unknown mbox type: %s" mbox-type)))
    (setq url (concat url (format "?%s%smbox=yes" bn mt)))
    (if filename
	(url-copy-file url filename t)
      (url-insert-file-contents url))))

(provide 'debbugs)

;;; TODO:

;; * SOAP interface extensions (wishlist).
;;   - Server-side sorting.
;;   - Regexp and/or wildcards search.
;;   - Fulltext search.
;;   - Returning message attachments.

;;; debbugs.el ends here
