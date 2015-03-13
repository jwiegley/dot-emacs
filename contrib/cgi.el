;;; cgi.el -- using Emacs for CGI scripting
;;;
;;; Author: Eric Marsden  <emarsden@laas.fr>
;;;         Michael Olson <mwolson@gnu.org> (slight modifications)
;;; Keywords: CGI web scripting slow
;;; Version: 0.3
;;; Time-stamp: <2001-08-24 emarsden>
;;; Copyright: (C) 2000  Eric Marsden
;;; Parts copyright (C) 2006 Free Software Foundation, Inc.
;;
;;     This program is free software; you can redistribute it and/or
;;     modify it under the terms of the GNU General Public License as
;;     published by the Free Software Foundation; either version 3 of
;;     the License, or (at your option) any later version.
;;
;;     This program is distributed in the hope that it will be useful,
;;     but WITHOUT ANY WARRANTY; without even the implied warranty of
;;     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;;     GNU General Public License for more details.
;;
;;     You should have received a copy of the GNU General Public
;;     License along with this program; if not, write to the Free
;;     Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;;     MA 02111-1307, USA.
;;
;;
;;; Commentary:
;;
;; People who like this sort of thing will find this the sort of
;; thing they like.                           -- Abraham Lincoln
;;
;;
;; Overview ==========================================================
;;
;; A simple library for the Common Gateway Interface for Emacs,
;; allowing you to service requests for non static web pages in elisp.
;; Provides routines for decoding arguments to GET- and POST-type CGI
;; requests.
;;
;; Usage: place a shell script such as the following in your web
;; server's CGI directory (typically called something like
;; /var/www/cgi-bin/):
;;
;; ,-------------------------------------------------------------------
;; | #!/bin/sh
;; |
;; | emacs -batch -l cgi.el -f cgi-calendar
;; `-------------------------------------------------------------------
;;
;; (`cgi-calendar' is a sample elisp CGI script provided at the end of
;; this file).
;;
;; Alternatively, if you're running version 2.x of the linux kernel
;; you could make .elc files directly executable via the binfmt_misc
;; mechanism and run them straight from the cgi-bin directory.
;;
;; Efficiency would be improved by having Emacs bind to the http
;; service port and spawn a thread per connection. Extending Emacs to
;; support server sockets and multithreading is left as an exercise
;; for the reader.
;;
;; References:
;;   * rfc1738 "Uniform Resource Locators"
;;   * rfc1630 "Universal Resource Identifiers in WWW"
;;
;; Thanks to Christoph Conrad <christoph.conrad@gmx.de> for pointing
;; out a bug in the URI-decoding.

;;; Code:

(eval-when-compile
  (require 'cl)
  (require 'calendar))

(defconst cgi-url-unreserved-chars '(
    ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m
    ?n ?o ?p ?q ?r ?s ?t ?u ?v ?w ?x ?y ?z
    ?A ?B ?C ?D ?E ?F ?G ?H ?I ?J ?K ?L ?M
    ?N ?O ?P ?Q ?R ?S ?T ?U ?V ?W ?X ?Y ?Z
    ?0 ?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9
    ?\$ ?\- ?\_ ?\. ?\! ?\~ ?\* ?\' ?\( ?\) ?\,))

(defun cgi-int-char (i)
  (if (fboundp 'int-char) (int-char i) i))

(defun cgi-hex-char-p (ch)
  (declare (character ch))
  (let ((hexchars '(?0 ?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9
		    ?A ?B ?C ?D ?E ?F)))
    (member (upcase ch) hexchars)))

;; decode %xx to the corresponding character and + to ' '
(defun cgi-decode-string (str)
  (do ((i 0)
       (len (length str))
       (decoded '()))
      ((>= i len) (concat (nreverse decoded)))
    (let ((ch (aref str i)))
      (cond ((eq ?+ ch)
	     (push ?\  decoded)
	     (incf i))
	    ((and (eq ?% ch)
		  (< (+ i 2) len)
		  (cgi-hex-char-p (aref str (+ i 1)))
		  (cgi-hex-char-p (aref str (+ i 2))))
	     (let ((hex (string-to-number (substring str (+ i 1) (+ i 3)) 16)))
	       (push (cgi-int-char hex) decoded)
	       (incf i 3)))
	    (t (push ch decoded)
	       (incf i))))))

(defun cgi-position (item seq &optional start end)
  (or start (setq start 0))
  (or end (setq end (length seq)))
  (while (and (< start end)
	      (not (equal item (aref seq start))))
    (setq start (1+ start)))
  (and (< start end) start))

;; Parse "foo=x&bar=y+re" into (("foo" . "x") ("bar" . "y re"))
;; Substrings are plus-decoded and then URI-decoded.
(defun cgi-decode (q)
  (when q
    (flet ((split-= (str)
	    (let ((pos (or (cgi-position ?= str) 0)))
	      (cons (cgi-decode-string (substring str 0 pos))
		    (cgi-decode-string (substring str (+ pos 1)))))))
      (mapcar #'split-= (split-string q "&")))))

(defun cgi-lose (fmt &rest args)
  (let ((why (apply #'format fmt args)))
    (message "Script error: %s" why)    ; to error_log
    (princ "Content-type: text/html\n\n") ; to browser
    (princ "<html><head><title>Script error</title></head>\r\n")
    (princ "<body><h1>Script error</h1>\r\n<p>\r\n")
    (princ why)
    (princ "\r\n</body></html>\r\n")
    (kill-emacs 0)))

(defmacro cgi-evaluate (&rest forms)
  `(condition-case why
       (princ (with-output-to-string ,@forms))
     (error (cgi-lose "Emacs Lisp error: %s" why))))

(defun cgi-arguments ()
  (let ((method (getenv "REQUEST_METHOD"))
	req buf)
    (cond ((null method)
	   (cgi-lose "No request method specified"))
	  ((string= "GET" method)
	   (unless (getenv "QUERY_STRING")
	     (cgi-lose "No query string for GET request"))
	   (cgi-decode (getenv "QUERY_STRING")))
	  ((string= "POST" method)
	   (setq req (getenv "CONTENT_LENGTH"))
	   (unless req
	     (cgi-lose "No content-length for POST request"))
	   (setq buf (get-buffer-create " *cgi*"))
	   (set-buffer buf)
	   (erase-buffer)
	   (loop for i from 1 to (string-to-number req)
		 do (insert (read-event)))
	   (cgi-decode (buffer-string)))
	  (t
	   (cgi-lose "Can't handle request method %s" method)))))

;; ====================================================================
;; a sample application: calendar via the web. If invoked without
;; arguments, presents a calendar for the three months around the
;; current date. You can request a calendar for a specific period by
;; specifying the year and the month in the query string:
;;
;;   ~$ lynx -dump 'http://localhost/cgi-bin/cal?year=1975&month=6'
;;
;; When run in batch mode, text normally displayed in the echo area
;; (via `princ' for example) goes to stdout, and thus to the browser.
;; Text output using `message' goes to stderr, and thus normally to
;; your web server's error_log.
;; ====================================================================

(eval-and-compile
  (if (fboundp 'calendar-extract-month)
      (defalias 'cgi-calendar-extract-month 'calendar-extract-month)
    (defalias 'cgi-calendar-extract-month 'extract-calendar-month))

  (if (fboundp 'calendar-extract-year)
      (defalias 'cgi-calendar-extract-year 'calendar-extract-year)
    (defalias 'cgi-calendar-extract-year 'extract-calendar-year))

  (if (fboundp 'calendar-generate)
      (defalias 'cgi-calendar-generate 'calendar-generate)
    (defalias 'cgi-calendar-generate 'generate-calendar)))

(defun cgi-calendar-string ()
  (require 'calendar)
  (let* ((args (cgi-arguments))
	 (now (calendar-current-date))
	 (mnth (cdr (assoc "month" args)))
	 (month (if mnth (string-to-number mnth)
		  (cgi-calendar-extract-month now)))
	 (yr (cdr (assoc "year" args)))
	 (year (if yr (string-to-number yr)
		 (cgi-calendar-extract-year now))))
    (with-temp-buffer
      (cgi-calendar-generate month year)
      (buffer-string))))

(defun cgi-calendar ()
  (cgi-evaluate
   (princ "Content-type: text/html\n\n")
   (princ "<html><head><title>Emacs calendar</title></head>\r\n")
   (princ "<body> <h1>Emacs calendar</h1>\r\n")
   (princ "<pre>\r\n")
   (princ (cgi-calendar-string))
   (princ "\r\n</pre></body></html>\r\n")))

(provide 'cgi)

;; cgi.el ends here
