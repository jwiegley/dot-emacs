;;; mediawiki.el --- mediawiki frontend

;; Copyright (C) 2008, 2009, 2010, 2011, 2015 Mark A. Hershberger

;; Original Authors: Jerry <unidevel@yahoo.com.cn>,
;;      Chong Yidong <cyd at stupidchicken com> for wikipedia.el,
;;      Uwe Brauer <oub at mat.ucm.es> for wikimedia.el
;; Author: Mark A. Hershberger <mah@everybody.org>
;; Created: Sep 17 2004
;; Keywords: mediawiki wikipedia network wiki
;; URL: https://github.com/hexmode/mediawiki-el
;; Last Modified: <2017-08-13 01:53:37 mah>

(defconst mediawiki-version "2.2.9"
  "Current version of mediawiki.el.")

;; This file is NOT (yet) part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This version of mediawiki.el represents a merging of
;; wikipedia-mode.el (maintained by Uwe Brauer <oub at mat.ucm.es>)
;; from https://www.emacswiki.org/emacs/wikipedia-mode.el for its
;; font-lock code, menu, draft mode, replying and convenience
;; functions to produce mediawiki.el 2.0.

;;; Installation

;; If you use ELPA, you can install via the M-x package-list-packages
;; interface. This is preferrable as you will have access to updates
;; automatically.

;; Otherwise, just make sure this file is in your load-path (usually
;; ~/.emacs.d is included) and put (require 'mediawiki.el) in your
;; ~/.emacs or ~/.emacs.d/init.el file.

;;; Howto:
;;  M-x customize-group RET mediawiki RET
;;  *dink* *dink*
;;  M-x mediawiki-site RET Wikipedia RET
;;
;; Open a wiki file:    M-x mediawiki-open
;; Save a wiki buffer:  C-x C-s
;; Save a wiki buffer with a different name:  C-x C-w

;;; TODO

;;  * Optionally use org-mode formatting for editing and translate
;;    that to mw
;;  * Move url-* methods to url-http
;;  * Use the MW API to support searching, etc.
;;  * Clean up and thoroughly test imported wikimedia.el code
;;  * Improve language support.  Currently there is a toggle for
;;    English or German.  This should probably just be replaced with
;;    customizable words given MediaWiki's wide language support.

;;; Changes

;; 2.2.7:
;;  * Add the ability to accept the domain
;;  * Fix false failures when site isn't found.

;; 2.2.6:
;;  * Moved to github
;;  * Code cleanup, flycheck

;; Since 2.2.4.2
;;  * Move to github
;;  * Added Readme.mediawiki to with information about security.

;; Since 2.2.4.1:
;;  * Add the forgotten customizable mediawiki-debug.

;; Since 2.2.4:
;;  * Made it clearer where debugging information is found when
;;    mediawiki-debug is non-nil by adding messages to the message
;;    buffer when debug buffers are killed.

;;; History

;; From the News section of wikipedia.el comes this bit, kept here for
;; reference later.
;;     (4) "Draft", "send" and "reply" (for discussion pages)
;;         abilities `based' on ideas of John Wigleys remember.el: see
;;         the functions wikipedia-draft-*
;;         RATIONALE: This comes handy in 2 situations
;;            1. You are editing articles which various authors (this I
;;               think is the usual case), you then want not to submit
;;               your edit immediately but want to copy it somewhere and
;;               to continue later. You can use the following functions
;;               for doing that:
;;               wikipedia-draft-buffer \C-c\C-b
;;               wikipedia-draft-region \C-c\C-r
;;               then the buffer/region will be appended to the
;;               wikipedia-draft-data-file (default is
;;               "~/Wiki/discussions/draft.wiki", which you can visit via
;;               wikipedia-draft-view-draft) and it will be
;;               surrounded by the ^L marks in order to set a page.
;;               moreover on top on that a section header == will be
;;               inserted, which consists of the Word Draft, a subject
;;               you are asked for and a date stamp.
;;
;;               Another possibility consists in using the function
;;               wikipedia-draft, bound to \C-c \C-m then a new buffer
;;               will opened already in wikipedia mode. You edit and then
;;               either can send the content of the buffer to the
;;               wikipedia-draft-data-file in the same manner as
;;               described above using the function
;;               wikipedia-draft-buffer (bound to \C-c\C-k)
;;
;;               BACK: In order to copy/send the content of temporary
;;               buffer or of a page in the wikipedia-draft-data-file
;;               back in to your wikipedia file, use the function
;;               wikipedia-send-draft-to-mozex bound to "\C-c\C-c". You
;;               will be asked to which buffer to copy your text!
;;
;;
;;            2. You want to reply  in a discussion page to a specific
;;               contribution, you can use either the function
;;
;;               \\[wikipedia-reply-at-point-simple] bound to [(meta shift r)]
;;               which inserts a newline, a hline, and the signature of
;;               the author. Or can use
;;               \\[wikipedia-draft-reply] bound  [(meta r)]
;;               which does the same as wikipedia-reply-at-point-simple
;;               but in a temporary draft buffer.
;;
;;               BACK: In order to copy/send the content of that buffer
;;               back in to your wikipedia file, use the function
;;               \\[wikipedia-send-draft-to-mozex] bound to "\C-c\C-c". You
;;               will be asked to which buffer to copy your text! If
;;               you want a copy to be send to your draft file, use
;;               the variable  wikipedia-draft-send-archive
;;

;;; Code:

(require 'url-http)
(require 'mml)
(require 'mm-url)
(require 'ring)
(require 'subr-x)
(eval-when-compile
  (require 'cl)
  (require 'mml)
;; Below copied from url-http to avoid compilation warnings
  (defvar url-http-extra-headers)
  (defvar url-http-target-url)
  (defvar url-http-proxy)
  (defvar url-http-connection-opened)
  ;; This should only be used in xemacs, anyway
  (setq byte-compile-not-obsolete-funcs (list 'assoc-ignore-case)))

;; As of 2010-06-22, these functions are in Emacs
(unless (fboundp 'url-bit-for-url)
  (defun url-bit-for-url (method lookfor url)
    (when (fboundp 'auth-source-user-or-password)
      (let* ((urlobj (url-generic-parse-url url))
             (bit (funcall method urlobj))
             (methods (list 'url-recreate-url
                            'url-host)))
        (if (and (not bit) (> (length methods) 0))
            (auth-source-user-or-password
             lookfor (funcall (pop methods) urlobj) (url-type urlobj))
          bit)))))

(unless (fboundp 'url-user-for-url)
  (defun url-user-for-url (url)
    "Attempt to use .authinfo to find a user for this URL."
    (url-bit-for-url 'url-user "login" url)))

(unless (fboundp 'url-password-for-url)
  (defun url-password-for-url (url)
    "Attempt to use .authinfo to find a password for this URL."
    (url-bit-for-url 'url-password "password" url)))

(when (fboundp 'url-http-create-request)
  (if (string= "GET / HTTP/1.0\r\nMIME-Version: 1.0\r\nConnection: close\r\nHost: example.com\r\nAccept: */*\r\nUser-Agent: URL/Emacs\r\nContent-length: 4\r\n\r\ntest"
	       (let ((url-http-target-url (url-generic-parse-url "http://example.com/"))
		     (url-http-data "test") (url-http-version "1.0")
		     url-http-method url-http-attempt-keepalives url-extensions-header
		     url-http-extra-headers url-http-proxy url-mime-charset-string)
		 (url-http-create-request)))
      (defun url-http-create-request (&optional ref-url)
	"Create an HTTP request for `url-http-target-url', referred to by REF-URL."
	(declare (special proxy-info
			  url-http-method url-http-data
			  url-http-extra-headers))
	(let* ((extra-headers)
	       (request nil)
	       (no-cache (cdr-safe (assoc "Pragma" url-http-extra-headers)))
	       (using-proxy url-http-proxy)
	       (proxy-auth (if (or (cdr-safe (assoc "Proxy-Authorization"
						    url-http-extra-headers))
				   (not using-proxy))
			       nil
			     (let ((url-basic-auth-storage
				    'url-http-proxy-basic-auth-storage))
			       (url-get-authentication url-http-target-url nil 'any nil))))
	       (real-fname (concat (url-filename url-http-target-url)
				   (with-no-warnings
                                    (url-recreate-url-attributes url-http-target-url))))
	       (host (url-host url-http-target-url))
	       (auth (if (cdr-safe (assoc "Authorization" url-http-extra-headers))
			 nil
		       (url-get-authentication (or
						(and (boundp 'proxy-info)
						     proxy-info)
						url-http-target-url) nil 'any nil))))
	  (if (equal "" real-fname)
	      (setq real-fname "/"))
	  (setq no-cache (and no-cache (string-match "no-cache" no-cache)))
	  (if auth
	      (setq auth (concat "Authorization: " auth "\r\n")))
	  (if proxy-auth
	      (setq proxy-auth (concat "Proxy-Authorization: " proxy-auth "\r\n")))

	  ;; Protection against stupid values in the referer
	  (if (and ref-url (stringp ref-url) (or (string= ref-url "file:nil")
						 (string= ref-url "")))
	      (setq ref-url nil))

	  ;; We do not want to expose the referer if the user is paranoid.
	  (if (or (memq url-privacy-level '(low high paranoid))
		  (and (listp url-privacy-level)
		       (memq 'lastloc url-privacy-level)))
	      (setq ref-url nil))

	  ;; url-http-extra-headers contains an assoc-list of
	  ;; header/value pairs that we need to put into the request.
	  (setq extra-headers (mapconcat
			       (lambda (x)
				 (concat (car x) ": " (cdr x)))
			       url-http-extra-headers "\r\n"))
	  (if (not (equal extra-headers ""))
	      (setq extra-headers (concat extra-headers "\r\n")))

	  ;; This was done with a call to `format'.  Concatting parts has
	  ;; the advantage of keeping the parts of each header together and
	  ;; allows us to elide null lines directly, at the cost of making
	  ;; the layout less clear.
	  (setq request
		;; We used to concat directly, but if one of the strings happens
		;; to being multibyte (even if it only contains pure ASCII) then
		;; every string gets converted with `string-MAKE-multibyte' which
		;; turns the 127-255 codes into things like latin-1 accented chars
		;; (it would work right if it used `string-TO-multibyte' instead).
		;; So to avoid the problem we force every string to be unibyte.
		(mapconcat
		 ;; FIXME: Instead of `string-AS-unibyte' we'd want
		 ;; `string-to-unibyte', so as to properly signal an error if one
		 ;; of the strings contains a multibyte char.
		 'string-as-unibyte
		 (delq nil
		       (list
			;; The request
			(or url-http-method "GET") " "
			(if using-proxy (url-recreate-url url-http-target-url) real-fname)
			" HTTP/" url-http-version "\r\n"
			;; Version of MIME we speak
			"MIME-Version: 1.0\r\n"
			;; (maybe) Try to keep the connection open
			"Connection: " (if (or using-proxy
					       (not url-http-attempt-keepalives))
					   "close" "keep-alive") "\r\n"
					   ;; HTTP extensions we support
			(if url-extensions-header
			    (format
			     "Extension: %s\r\n" url-extensions-header))
			;; Who we want to talk to
			(if (/= (url-port url-http-target-url)
				(url-scheme-get-property
				 (url-type url-http-target-url) 'default-port))
			    (format
			     "Host: %s:%d\r\n" host (url-port url-http-target-url))
			  (format "Host: %s\r\n" host))
			;; Who its from
			(if url-personal-mail-address
			    (concat
			     "From: " url-personal-mail-address "\r\n"))
			;; Encodings we understand
			(if url-mime-encoding-string
			    (concat
			     "Accept-encoding: " url-mime-encoding-string "\r\n"))
			(if url-mime-charset-string
			    (concat
			     "Accept-charset: " url-mime-charset-string "\r\n"))
			;; Languages we understand
			(if url-mime-language-string
			    (concat
			     "Accept-language: " url-mime-language-string "\r\n"))
			;; Types we understand
			"Accept: " (or url-mime-accept-string "*/*") "\r\n"
			;; User agent
			(url-http-user-agent-string)
			;; Proxy Authorization
			proxy-auth
			;; Authorization
			auth
			;; Cookies
			(url-cookie-generate-header-lines host real-fname
							  (equal "https" (url-type url-http-target-url)))
			;; If-modified-since
			(if (and (not no-cache)
				 (member url-http-method '("GET" nil)))
			    (let ((tm (url-is-cached url-http-target-url)))
			      (if tm
				  (concat "If-modified-since: "
					  (url-get-normalized-date tm) "\r\n"))))
			;; Whence we came
			(if ref-url (concat
				     "Referer: " ref-url "\r\n"))
			extra-headers
			;; Length of data
			(if url-http-data
			    (concat
			     "Content-length: " (number-to-string
						 (length url-http-data))
			     "\r\n"))
			;; End request
			"\r\n"
			;; Any data
			url-http-data "\r\n"))
		 ""))
	  (url-http-debug "Request is: \n%s" request)
	  request))))

;; There are some versions of emacs that don't have
;; mm-url-encode-multipart-form-data.
;; See https://lists.gnu.org/archive/html/emacs-diffs/2014-11/msg00167.html
(unless (fboundp 'mm-url-encode-multipart-form-data)
  (defun mm-url-encode-multipart-form-data (pairs &optional boundary)
    "Return PAIRS encoded in multipart/form-data."
    ;; RFC1867

    ;; Get a good boundary
    (unless boundary
      (setq boundary (mml-compute-boundary '())))

    (concat

     ;; Start with the boundary
     "--" boundary "\r\n"

     ;; Create name value pairs
     (mapconcat
      'identity
      ;; Delete any returned items that are empty
      (delq nil
            (mapcar (lambda (data)

                      (cond
                       ((consp (car data))
                        (let ((fieldname (cadar data))
                              (filename  (caadar data))
                              (mimetype  (car (caadar data)))
                              (content   (caar (caadar data))))

                          (concat
                           ;; Encode the name
                           "Content-Disposition: form-data; name=\"" fieldname "\"\r\n"
                           "Content-Type: " mimetype "\r\n"
                           "Content-Transfer-Encoding: binary\r\n\r\n"
                           content
                           "\r\n")))

                       ((stringp (car data))
                                ;; For each pair

                        (concat
                         ;; Encode the name
                         "Content-Disposition: form-data; name=\""
                         (car data) "\"\r\n"
                         "Content-Type: text/plain; charset=utf-8\r\n"
                         "Content-Transfer-Encoding: binary\r\n\r\n"

                         (cond ((stringp (cdr data))
                                (cdr data))
                               ((integerp (cdr data))
                                (int-to-string (cdr data))))

                         "\r\n"))
                       (t (error "I don't handle this"))))
                    pairs))
      ;; use the boundary as a separator
      (concat "--" boundary "\r\n"))

     ;; put a boundary at the end.
     "--" boundary "--\r\n")))

;; Not defined in my Xemacs
(unless (fboundp 'assoc-string)
  (defun assoc-string (key list &optional case-fold)
    (if case-fold
        (assoc-ignore-case key list)
      (assoc key list))))

(defun url-compat-retrieve (url post-process buffer callback cbargs)
  "Function to compatibly retrieve a URL.
Some provision is made for different versions of Emacs version.
POST-PROCESS is the function to call for post-processing.
BUFFER is the buffer to store the result in.  CALLBACK will be
called in BUFFER with CBARGS, if given."
  (let ((url-user-agent (concat (string-trim (if (functionp url-user-agent)
                                                 (funcall url-user-agent)
                                               url-user-agent))
                                " mediawiki.el " mediawiki-version "\r\n")))
    (cond ((boundp 'url-be-asynchronous) ; Sniff w3 lib capability
           (if callback
               (setq url-be-asynchronous t)
             (setq url-be-asynchronous nil))
           (url-retrieve url t)
           (when (not url-be-asynchronous)
             (let ((result (funcall post-process buffer)))
               result)))
          (t (if callback
                 (url-retrieve url post-process
                               (list buffer callback cbargs))
               (with-current-buffer (url-retrieve-synchronously url)
                 (funcall post-process buffer)))))))

(defvar url-http-get-post-process 'url-http-response-post-process)
(defun url-http-get (url &optional headers buffer callback cbargs)
  "Convenience method to use method 'GET' to retrieve URL.
HEADERS is the optional headers to send.  BUFFER is where the
result will be stored.  CALLBACK will be called in BUFFER with
CBARGS, if given."
  (let* ((url-request-extra-headers (if headers headers
                                      (if url-request-extra-headers
                                          url-request-extra-headers
                                        (cons nil nil))))
         (url-request-method "GET"))

    (when (url-basic-auth url)
      (add-to-list 'url-request-extra-headers
                   (cons "Authorization" (url-basic-auth url))))
    (url-compat-retrieve url url-http-get-post-process
			 buffer callback cbargs)))

(defvar url-http-post-post-process 'url-http-response-post-process)
(defun url-http-post (url parameters &optional multipart headers buffer
                          callback cbargs)
  "Convenience method to use method 'POST' to retrieve URL.
PARAMETERS are the parameters to put the the body.  If MULTIPART
is t, then multipart/form-data will be used.  Otherwise,
applicaton/x-www-form-urlencoded is used.  HEADERS is the
optional headers to send.  BUFFER is where the result will be
stored.  CALLBACK will be called in BUFFER with CBARGS, if
given."

  (let* ((url-request-extra-headers
          (if headers headers
            (when url-request-extra-headers url-request-extra-headers)))
         (boundary (int-to-string (random)))
         (cs 'utf-8)
         (content-type
          (if multipart
              (concat "multipart/form-data, boundary=" boundary)
            (format "application/x-www-form-urlencoded; charset=%s" cs)))
         (url-request-method "POST")
         (url-request-coding-system cs)
         (url-request-data
          (if multipart
              (mm-url-encode-multipart-form-data
               parameters boundary)
            (mm-url-encode-www-form-urlencoded (delq nil parameters)))))
    (mapc
     (lambda (pair)
       (let ((key (car pair))
             (val (cdr pair)))
         (if (assoc key url-request-extra-headers)
             (setcdr (assoc key url-request-extra-headers) val)
           (add-to-list 'url-request-extra-headers
                        (cons key val)))))
     (list
      (cons "Connection" "close")
      (cons "Content-Type" content-type)))

     (url-compat-retrieve url url-http-post-post-process
			 buffer callback cbargs)))

(defun url-http-response-post-process (status &optional buffer
                                              callback cbargs)
  "Default post-processor for an HTTP POST request response.
STATUS is the HTTP status code.  BUFFER, CALLBACK, and CBARGS are
passed as well from the original POST request."
  (declare (special url-http-end-of-headers))
  (let ((kill-this-buffer (current-buffer)))
    (when (and (integerp status) (not (< status 300)))
      (mediawiki-debug kill-this-buffer "url-http-response-post-process:1")
      (error "Oops! Invalid status: %d" status))

    (when (or (not (boundp 'url-http-end-of-headers))
              (not url-http-end-of-headers))
      (mediawiki-debug kill-this-buffer "url-http-response-post-process:2")
      (error "Oops! Don't see end of headers!"))

    ;; FIXME: need to limit redirects
    (if (and (listp status)
             (eq (car status) :redirect))
        (progn
          (message (concat "Redirecting to " (cadr status)))
          (url-http-get (cadr status) nil buffer callback cbargs))

      (goto-char url-http-end-of-headers)
      (forward-line)

      (let ((str (decode-coding-string
                  (buffer-substring-no-properties (point) (point-max))
                  'utf-8)))
        (mediawiki-debug (current-buffer) "url-http-response-post-process:3")
        (when buffer
          (set-buffer buffer)
          (insert str)
          (goto-char (point-min))
          (set-buffer-modified-p nil))
        (when callback
          (apply callback (list str cbargs)))
        (when (not (or callback buffer))
          str)))))

(defgroup mediawiki nil
  "A mode for editting pages on MediaWiki sites."
  :tag "MediaWiki"
  :group 'applications)

(defcustom mediawiki-site-default "Wikipedia"
  "The default mediawiki site to point to.
Set here for the default and use `mediawiki-site' to set it
per-session later."
  :type 'string
  :tag "MediaWiki Site Default"
  :group 'mediawiki)

(defcustom mediawiki-debug nil
  "Turn on debugging (non-nil)."
  :type 'boolean
  :tag "MediaWiki Debugging"
  :group 'mediawiki)

(defcustom mediawiki-site-alist '(("Wikipedia"
                                   "https://en.wikipedia.org/w/"
                                   "username"
                                   "password"
                                   nil
				   "Main Page"))
  "A list of MediaWiki websites."
  :tag "MediaWiki sites"
  :group 'mediawiki
  :type '(alist :tag "Site Name"
                :key-type (string :tag "Site Name")
                :value-type (list :tag "Parameters"
                                  (string :tag "URL")
                                  (string :tag "Username")
                                  (string :tag "Password")
                                  (choice :tag "Provide LDAP Domain?"
                                          (string)
                                          (other :tag "No" nil))
                                  (string :tag "First Page"
                                          :description "First page to open when `mediawiki-site' is called for this site"))))

(defcustom mediawiki-pop-buffer-hook '()
  "List of functions to execute after popping to a buffer.
Can be used to to open the whole buffer."
  :options '(delete-other-windows)
  :type 'hook
  :group 'mediawiki)

(defvar mediawiki-page-history '()
  "Assoc list of visited pages on this MW site.")

(defvar mediawiki-enumerate-with-terminate-paragraph nil
"*Before insert enumerate/itemize do \\[mediawiki-terminate-paragraph].")

(defvar mediawiki-english-or-german t
  "*Variable in order to set the english (t) or german (nil) environment.")

(defcustom mediawiki-user-simplify-signature t
  "Simplify other user's signatures."
  :type 'boolean
  :group 'mediawiki)

(defgroup mediawiki-draft nil
  "A mode to mediawiki-draft information."
  :group 'mediawiki)

;;; User Variables:

(defcustom mediawiki-debug nil
  "Keep buffers around for debugging purposes."
  :type 'boolean
  :group 'mediawiki)

(defcustom mediawiki-draft-mode-hook nil
  "*Functions run upon entering mediawiki-draft-mode."
  :type 'hook
  :group 'mediawiki-draft)

(defcustom mediawiki-draft-register ?R
  "The register in which the window configuration is stored."
  :type 'character
  :group 'mediawiki-draft)

(defcustom mediawiki-draft-filter-functions nil
  "*Functions run to filter mediawiki-draft data.
All functions are run in the mediawiki-draft buffer."
  :type 'hook
  :group 'mediawiki-draft)

(defcustom mediawiki-draft-handler-functions '(mediawiki-draft-append-to-file)
  "*Functions run to process mediawiki-draft data.
Each function is called with the current buffer narrowed to what the
user wants mediawiki-drafted.
If any function returns non-nil, the data is assumed to have been
recorded somewhere by that function."
  :type 'hook
  :group 'mediawiki-draft)

(defcustom mediawiki-draft-data-file "~/Wiki/discussions/draft.wiki"
  "*The file in which to store the wikipedia drafts."
  :type 'file
  :group 'mediawiki-draft)

(defcustom mediawiki-draft-reply-register ?M
  "The register in which the window configuration is stored."
  :type 'character
  :group 'mediawiki-draft)

(defcustom mediawiki-draft-page ?S		;Version:1.37
  "The register in which the a page of the wiki draft file is stored."
  :type 'character
  :group 'mediawiki-draft)


(defcustom mediawiki-draft-leader-text "== "
  "*The text used to begin each mediawiki-draft item."
  :type 'string
  :group 'mediawiki-draft)

(defvar mediawiki-reply-with-hline nil
"*Whether to use a hline as a header seperator in the reply.")

(defvar mediawiki-reply-with-quote nil
  "*Whether to use a quotation tempalate or not.")

(defvar mediawiki-imenu-generic-expression
  (list '(nil "^==+ *\\(.*[^\n=]\\)==+" 1))
  "Imenu expression for `mediawiki-mode'.  See `imenu-generic-expression'.")

(defvar mediawiki-login-success "pt-logout"
  "String to look for in HTML response.
This will be used to verify a successful login.")

(defvar mediawiki-permission-denied
  "[^;]The action you have requested is limited"
  "String that indicates permission has been denied.
Note that it should not match the mediawiki.el file itself since
it is sometimes put on MediaWiki sites.")

(defvar mediawiki-view-source
  "ca-viewsource"
  "String that indicates you cannot edit this page.")

(defvar mediawiki-site nil
  "The current mediawiki site from `mediawiki-site-alist'.
If not set, defaults to `mediawiki-site-default'.")

(defvar mediawiki-site-info nil
  "Holds the site information fetched in this session.")

(defvar mediawiki-argument-pattern "?title=%s&action=%s"
  "Format of the string to append to URLs.
Two string arguments are expected: first is a title and then an
action.")

(defvar mediawiki-URI-pattern
  "https?://\\([^/:]+\\)\\(:\\([0-9]+\\)\\)?/"
  "Pattern match for a URI.
Expected to match something like this:
	https://mediawiki.sf.net/index.php
Passwords in the URL are not supported yet")

(defvar mediawiki-page-uri nil
  "The URI of the page corresponding to the current buffer.
This is used to determine the base URI of the wiki engine as well
as group and page name.")

(defvar mediawiki-page-title nil
  "The title of the page corresponding to the current buffer.")

(defvar mediawiki-edittoken nil
  "The edit token for this page.")
(defvar mediawiki-starttimestamp nil
  "The starttimestamp for this page.")
(defvar mediawiki-basetimestamp nil
  "The base timestamp for this page.")

(defvar mediawiki-page-ring nil
  "Ring that holds names of buffers we navigate through.")

(defvar mediawiki-page-ring-index 0)

(defvar font-mediawiki-sedate-face 'font-mediawiki-sedate-face
  "Face to use for mediawiki  minor keywords.")
(defvar font-mediawiki-italic-face 'font-mediawiki-italic-face
  "Face to use for mediawiki italics.")
(defvar font-mediawiki-bold-face 'font-mediawiki-bold-face
  "Face to use for mediawiki bolds.")
(defvar font-mediawiki-math-face 'font-mediawiki-math-face
  "Face to use for mediawiki math environments.")
(defvar font-mediawiki-string-face 'font-mediawiki-string-face
  "Face to use for strings.")
(defvar font-mediawiki-verbatim-face 'font-mediawiki-verbatim-face
  "Face to use for text in verbatim macros or environments.")

(defface font-mediawiki-bold-face
  (let ((font (cond ((assq :inherit custom-face-attributes) '(:inherit bold))
		    ((assq :weight custom-face-attributes) '(:weight bold))
		    (t '(:bold t)))))
    `((((class grayscale) (background light))
       (:foreground "DimGray" ,@font))
      (((class grayscale) (background dark))
       (:foreground "LightGray" ,@font))
      (((class color) (background light))
       (:foreground "DarkOliveGreen" ,@font))
      (((class color) (background dark))
       (:foreground "OliveDrab" ,@font))
      (t (,@font))))
  "Face used to highlight text to be typeset in bold."
  :group 'font-mediawiki-highlighting-faces)

(defface font-mediawiki-italic-face
  (let ((font (cond ((assq :inherit custom-face-attributes) '(:inherit italic))
		    ((assq :slant custom-face-attributes) '(:slant italic))
		    (t '(:italic t)))))
    `((((class grayscale) (background light))
       (:foreground "DimGray" ,@font))
      (((class grayscale) (background dark))
       (:foreground "LightGray" ,@font))
      (((class color) (background light))
       (:foreground "DarkOliveGreen" ,@font))
      (((class color) (background dark))
       (:foreground "OliveDrab" ,@font))
      (t (,@font))))
  "Face used to highlight text to be typeset in italic."
  :group 'font-mediawiki-highlighting-faces)

(defface font-mediawiki-math-face
  (let ((font (cond ((assq :inherit custom-face-attributes)
		     '(:inherit underline))
		    (t '(:underline t)))))
    `((((class grayscale) (background light))
       (:foreground "DimGray" ,@font))
      (((class grayscale) (background dark))
       (:foreground "LightGray" ,@font))
      (((class color) (background light))
       (:foreground "SaddleBrown"))
      (((class color) (background dark))
       (:foreground "burlywood"))
      (t (,@font))))
  "Face used to highlight math."
  :group 'font-mediawiki-highlighting-faces)

(defface font-mediawiki-sedate-face
  '((((class grayscale) (background light)) (:foreground "DimGray"))
    (((class grayscale) (background dark))  (:foreground "LightGray"))
    (((class color) (background light)) (:foreground "DimGray"))
    (((class color) (background dark))  (:foreground "LightGray"))
   ;;;(t (:underline t))
    )
  "Face used to highlight sedate stuff."
  :group 'font-mediawiki-highlighting-faces)

(defface font-mediawiki-string-face
  (let ((font (cond ((assq :inherit custom-face-attributes) '(:inherit italic))
		    ((assq :slant custom-face-attributes) '(:slant italic))
		    (t '(:italic t)))))
    `((((type tty) (class color))
       (:foreground "green"))
      (((class grayscale) (background light))
       (:foreground "DimGray" ,@font))
      (((class grayscale) (background dark))
       (:foreground "LightGray" ,@font))
      (((class color) (background light))
       (:foreground "RosyBrown"))
      (((class color) (background dark))
       (:foreground "LightSalmon"))
      (t (,@font))))
  "Face used to highlight strings."
  :group 'font-mediawiki-highlighting-faces)

(defface font-mediawiki-warning-face
  (let ((font (cond ((assq :inherit custom-face-attributes) '(:inherit bold))
		    ((assq :weight custom-face-attributes) '(:weight bold))
		    (t '(:bold t)))))
    `((((class grayscale)(background light))
       (:foreground "DimGray" ,@font))
      (((class grayscale)(background dark))
       (:foreground "LightGray" ,@font))
      (((class color)(background light))
       (:foreground "red" ,@font))
      (((class color)(background dark))
       (:foreground "red" ,@font))
      (t (,@font))))
  "Face for important keywords."
  :group 'font-mediawiki-highlighting-faces)

(defface font-mediawiki-verbatim-face
  (let ((font (if (and (assq :inherit custom-face-attributes)
		       (if (fboundp 'find-face)
			   (find-face 'fixed-pitch)
			 (facep 'fixed-pitch)))
		  '(:inherit fixed-pitch)
		'(:family "courier"))))
    `((((class grayscale) (background light))
       (:foreground "DimGray" ,@font))
      (((class grayscale) (background dark))
       (:foreground "LightGray" ,@font))
      (((class color) (background light))
       (:foreground "SaddleBrown" ,@font))
      (((class color) (background dark))
       (:foreground "burlywood" ,@font))
      (t (,@font))))
  "Face used to highlight TeX verbatim environments."
  :group 'font-mediawiki-highlighting-faces)

(defvar mediawiki-simple-tags
  '("b" "big" "blockquote" "br" "caption" "code" "center" "cite" "del"
    "dfn" "dl" "em" "i" "ins" "kbd" "math" "nowiki" "ol" "pre" "samp"
    "small" "strike" "strong" "sub" "sup" "tt" "u" "ul" "var")
  "Tags that do not accept arguments.")

(defvar mediawiki-complex-tags
  '("a" "div" "font" "table" "td" "th" "tr")
  "Tags that accept arguments.")

(defvar mediawiki-url-protocols
  '("ftp" "gopher" "http" "https" "mailto" "news")
  "Valid protocols for URLs in Wikipedia articles.")

(defvar mediawiki-draft-buffer "*MW-Draft*"
  "The name of the wikipedia-draft (temporary) data entry buffer.")

(defvar mediawiki-edit-form-vars nil)

(defvar mediawiki-font-lock-keywords
  (list

   ;; Apostrophe-style text markup
   (cons "''''\\([^']\\|[^']'\\)*?\\(''''\\|\n\n\\)"
         'font-lock-builtin-face)
   (cons "'''\\([^']\\|[^']'\\)*?\\('''\\|\n\n\\)"
                                        ;'font-lock-builtin-face)
         'font-mediawiki-bold-face)
   (cons "''\\([^']\\|[^']'\\)*?\\(''\\|\n\n\\)"
         'font-mediawiki-italic-face)

   ;; Headers and dividers
   (list "^\\(==+\\)\\(.*\\)\\(\\1\\)"
         '(1 font-lock-builtin-face)
                                        ;'(2 mediawiki-header-face)
         '(2 font-mediawiki-sedate-face)
         '(3 font-lock-builtin-face))
   (cons "^-----*" 'font-lock-builtin-face)

   ;; Bare URLs and ISBNs
   (cons (concat "\\(^\\| \\)" (regexp-opt mediawiki-url-protocols t)
                 "://[-A-Za-z0-9._\/~%+&#?!=()@]+")
         'font-lock-variable-name-face)
   (cons "\\(^\\| \\)ISBN [-0-9A-Z]+" 'font-lock-variable-name-face)

   ;; Colon indentation, lists, definitions, and tables
   (cons "^\\(:+\\|[*#]+\\||[}-]?\\|{|\\)" 'font-lock-builtin-face)
   (list "^\\(;\\)\\([^:\n]*\\)\\(:?\\)"
         '(1 font-lock-builtin-face)
         '(2 font-lock-keyword-face)
         '(3 font-lock-builtin-face))

   ;; Tags and comments
   (list (concat "\\(</?\\)"
                 (regexp-opt mediawiki-simple-tags t) "\\(>\\)")
         '(1 font-lock-builtin-face t t)
         '(2 font-lock-function-name-face t t)
         '(3 font-lock-builtin-face t t))
   (list (concat "\\(</?\\)"
                 (regexp-opt mediawiki-complex-tags t)
                 "\\(\\(?: \\(?:[^\"'/><]\\|\"[^\"]*\"\\|'[^']*'\\)*\\)?\\)\\(>\\)")
         '(1 font-lock-builtin-face t t)
         '(2 font-lock-function-name-face t t)
         '(3 font-lock-keyword-face t t)
         '(4 font-lock-builtin-face t t))
   (cons (concat "<!-- \\([^->]\\|>\\|-\\([^-]\\|-[^>]\\)\\)*-->")
         '(0 font-lock-comment-face t t))

   ;; External Links
   (list (concat "\\(\\[\\)\\(\\(?:"
                 (regexp-opt mediawiki-url-protocols)
                 "\\)://[-A-Za-z0-9._\/~%-+&#?!=()@]+\\)\\(\\(?: [^]\n]*\\)?\\)\\(\\]\\)")
         '(1 font-lock-builtin-face t t)
         '(2 font-lock-variable-name-face t t)
         '(3 font-lock-keyword-face t t)
         '(4 font-lock-builtin-face t t))

   ;; Wiki links
   '("\\(\\[\\[\\)\\([^]\n|]*\\)\\(|?\\)\\([^]\n]*\\)\\(\\]\\]\\)"
     (1 font-lock-builtin-face t t)
     (2 font-lock-variable-name-face t t)
     (3 font-lock-builtin-face t t)
     (4 font-lock-keyword-face t t)
     (5 font-lock-builtin-face t t))

   ;; Semantic relations
   '("\\(\\[\\[\\)\\([^]\n|]*\\)\\(::\\)\\([^]\n|]*\\)\\(|?\\)\\([^]\n]*\\)\\(\\]\\]\\)"
     (1 font-lock-builtin-face t t)
     (2 font-lock-variable-name-face t t)
     (3 font-lock-builtin-face t t)
     (4 font-lock-constant-face t t)
     (5 font-lock-builtin-face t t)
     (6 font-lock-keyword-face t t)
     (7 font-lock-builtin-face t t))

   ;; Wiki variables
   '("\\({{\\)\\(.+?\\)\\(}}\\)"
     (1 font-lock-builtin-face t t)
     (2 font-lock-variable-name-face t t)
     (3 font-lock-builtin-face t t))

   ;; Semantic variables
   '("\\({{{\\)\\(.+?\\)\\(}}}\\)"
     (1 font-lock-builtin-face t t)
     (2 font-lock-variable-name-face t t)
     (3 font-lock-builtin-face t t))

   ;; Character entity references
   (cons "&#?[a-zA-Z0-9]+;" '(0 font-lock-type-face t t))

   ;; Preformatted text
   (cons "^ .*$" '(0 font-lock-constant-face t t))

   ;; Math environment (uniform highlight only, no TeX markup)
   (list "<math>\\(\\(\n?.\\)*\\)</math>"
         '(1 font-lock-keyword-face t t))))

(defvar mediawiki-draft-send-archive t
  "*Archive the reply.")

(defvar mediawiki-draft-mode-map ())

(defvar mediawiki-debug-buffer " *MediaWiki Debug*")

(defun mediawiki-debug (buffer function)
  "The debug handler.
When debugging is turned on, log the name of the BUFFER with the
FUNCTION that called the debugging function, so it can be
examined.  If debugging is off, just kill the buffer.  This
allows you to see what is being sent to and from the server."
  (if (not mediawiki-debug)
      (kill-buffer buffer)
    (with-current-buffer (get-buffer-create mediawiki-debug-buffer)
      (goto-char (point-max))
      (insert "\n")
      (insert-buffer-substring buffer))))

(defun mediawiki-translate-pagename (name)
  "Given NAME, return the typical name that MediaWiki would use.
Right now, this only means replacing \"_\" with \" \"."
  (if (not name)
      "Main Page"
    (mapconcat 'identity (split-string name "_" t) " ")))

(defun mediawiki-make-api-url (&optional sitename)
  "Translate SITENAME (or MEDIAWIKI-SITE if not given) to a URL."
  (format (let* ((my-parsed (url-generic-parse-url
                             (mediawiki-site-url (or sitename mediawiki-site))))
                 (my-path (url-filename my-parsed)))
	 (when (or (string= my-path "") (not (string= (substring my-path -1) "/")))
	   (setq my-path (concat my-path "/")))
	 (setf (url-filename my-parsed) (concat my-path "api.php"))
	 (url-recreate-url my-parsed))))

(defun mediawiki-raise (result type notif)
  "Show a TYPE of information from the RESULT to the user using NOTIF"
  (when (assq type (cddr result))
    (mapc (lambda (err)
            (let ((label (or (cdr (assq 'code err))
                             (car err)))
                  (info (or (cdr (assq 'info err))
                            (cddr err))))
              (funcall notif label info)))

          ;; Poor man's attempt at backward compatible xml form handling
          (if (listp (cdr (assq type (cddr result))))
              (cdr (assq type (cddr result)))
            (cddr (assq type (cddr result)))))))

(defun mediawiki-api-call (sitename action &optional args)
  "Wrapper for making an API call to SITENAME.
ACTION is the API action.  ARGS is a list of arguments."
  (let* ((raw (url-http-post (mediawiki-make-api-url sitename)
                             (append args (list (cons "format" "xml")
                                                (cons "action" action)))))
         (result (assoc 'api
                            (with-temp-buffer
                              (insert raw)
                              (xml-parse-region (point-min) (point-max))))))
    (unless result
      (error "There was an error parsing the result of the API call"))

    (mediawiki-raise result 'warnings
                     (lambda (label info)
                       (message "Warning (%s) %s" label info)))
    (mediawiki-raise result 'info
                     (lambda (label info)
                       (message  "(%s) %s" label info)))
    (mediawiki-raise result 'error
                     (lambda (label info)
                       (error "(%s) %s" label info)))

    (if (cddr result)
        (let ((action-res (assq (intern action) (cddr result))))
          (unless action-res
            (error "Didn't see action name in the result list"))

          action-res)
      t)))

(defun mediawiki-make-url (title action &optional sitename)
  "Return a url when given a TITLE, ACTION and, optionally, SITENAME."
  (format (concat (mediawiki-site-url (or sitename mediawiki-site))
                  (if action
                      mediawiki-argument-pattern
                    "?title=%s"))
	  (mm-url-form-encode-xwfu
           (mediawiki-translate-pagename title))
	  action))

(defun mediawiki-open (name)
  "Open a wiki page specified by NAME from the mediawiki engine."
  (interactive
   (let ((hist (cdr (assoc-string mediawiki-site mediawiki-page-history))))
     (list (read-string "Wiki Page: " nil 'hist))))
  (when (or (not (stringp name))
            (string-equal "" name))
    (error "Need to specify a name"))
  (mediawiki-edit mediawiki-site name))

(defun mediawiki-reload ()
  "Reload the page from the server."
  (interactive)
  (let ((title mediawiki-page-title))
    (if title
	(mediawiki-open title)
      (error "Error: %s is not a mediawiki document" (buffer-name)))))

(defun mediawiki-add-page-history (sitename title)
  "Update SITENAME's page history with TITLE."
  (let ((hist (cdr (assoc-string sitename mediawiki-page-history))))
    (unless hist
      (add-to-list 'mediawiki-page-history (cons sitename "")))
    (setcdr (assoc-string sitename mediawiki-page-history) (append (list title) hist))))

(defun mediawiki-edit (sitename title)
  "Edit wiki page on SITENAME named TITLE."
  (when (not (ring-p mediawiki-page-ring))
    (setq mediawiki-page-ring (make-ring 30)))

  (let ((pagetitle (mediawiki-translate-pagename title)))

    (mediawiki-add-page-history sitename title)
    (with-current-buffer (get-buffer-create
                          (concat sitename ": " pagetitle))
      (unless (mediawiki-logged-in-p sitename)
        (mediawiki-do-login sitename)
        (setq mediawiki-site sitename))
      (ring-insert mediawiki-page-ring (current-buffer))
      (delete-region (point-min) (point-max))
      (mediawiki-mode)
      (set-buffer-file-coding-system 'utf-8)
      (insert (or (mediawiki-get sitename pagetitle) ""))

      (set-buffer-modified-p nil)
      (setq buffer-undo-list t)
      (buffer-enable-undo)
      (mediawiki-pop-to-buffer (current-buffer))
      (setq mediawiki-page-title pagetitle)
      (goto-char (point-min))
      (current-buffer))))

(defun mediawiki-get-edit-form-vars (buffer)
  "Extract the form variables from a page.
Messages are displayed if permission is denied in some way.
This should only be called from a BUFFER in mediawiki-mode as the
variables it sets there will be local to that buffer."

  (let* ((str (with-current-buffer buffer (buffer-string)))
         (args (mediawiki-get-form-vars str "id" "editform")))
    (if args
	(with-current-buffer buffer
	  (setq mediawiki-edit-form-vars args))
      (cond
       ((string-match mediawiki-permission-denied str)
	(message "Permission Denied"))
       ((string-match mediawiki-view-source str)
        ;; FIXME set read-only flag
	(message "Editing of this page is disabled, here is the source"))))))

(defun mediawiki-get-form-vars (str attribute value)
  "Look in STR for form element with ATTRIBUTE set to VALUE."
  ;; Find the form
  (when (string-match
         (concat "<form [^>]*" attribute "=[\"']" value "['\"][^>]*>")
         str)

    (let* ((start-form (match-end 0))
           (end-form (when (string-match "</form>" str start-form)
                       (match-beginning 0)))
           (form (substring str start-form end-form))
           (start (string-match
                   "<input \\([^>]*name=[\"']\\([^\"']+\\)['\"][^>]*\\)>"
                   form))
           (vars '(nil)))

      ;; Continue until we can't find any more input elements
      (while start

        ;; First, capture the place where we'll start next.  Have
        ;; to do this here since match-end doesn't seem to let you
        ;; specify the string you were matching against, unlike
        ;; match-string
        (setq start (match-end 0))

        ;; Capture the string that defines this element
        (let ((el (match-string 1 form))
              ;; get the element name
              (el-name (match-string 2 form)))

          ;; figure out if this is a submit button and skip it if it is.
          (when (not (string-match "type=[\"']submit['\"]" el))
            (add-to-list 'vars
                         (if (string-match "value=[\"']\\([^\"']*\\)['\"]" el)
                             (cons el-name (match-string 1 el))
                           (cons el-name nil)))))

        (setq start
              (string-match
               "<input \\([^>]*name=[\"']\\([^\"']+\\)['\"][^>]*\\)>"
               form start)))
      vars)))

(defun mediawiki-logged-in-p (&optional sitename)
  "Return t if we have cookies for the SITENAME."
  (let ((urlobj (url-generic-parse-url
                 (mediawiki-site-url (or sitename mediawiki-site)))))
    (url-cookie-retrieve
     (url-host urlobj)
     (url-filename urlobj)
     (equal "https" (url-type urlobj)))))

(defun mediawiki-pop-to-buffer (buffer)
  "Pop to BUFFER and then execute a hook."
  (pop-to-buffer buffer)
  (run-hooks 'mediawiki-pop-buffer-hook))

(defun mediawiki-api-param (value)
  "Convert VALUE into a usable form for the MediaWiki API.
* Concat a list into a bar-separated string,
* Turn an integer into a string, or
* Just return the string"
  (cond
   ((integerp value) (int-to-string value))
   ((stringp value) value)
   ((listp value) (mapconcat 'identity value "|"))
   (t (error "Don't know what to do with %s" value))))

(defun mediawiki-api-query-revisions (sitename title props &optional limit)
  "Get a list of revisions and properties for a given page.
SITENAME is the site to use.  TITLE is a string containing one
title or a list of titles.  PROPS are the revision properites to
fetch.  LIMIT is the upper bound on the number of results to give."
  (cddr (mediawiki-api-call sitename "query"
                      (list (cons "prop" (mediawiki-api-param (list "info" "revisions")))
                            (cons "intoken" (mediawiki-api-param "edit"))
                            (cons "titles" (mediawiki-api-param title))
                            (when limit
                              (cons "rvlimit" (mediawiki-api-param limit)))
                            (cons "rvprop" (mediawiki-api-param props))))))

(defun mediawiki-page-get-title (page)
  "Given a PAGE from a pagelist structure, extract the title."
  (cdr (assq 'title (cadr page))))

(defun mediawiki-page-get-revision (page revision &optional bit)
  "Given a PAGE, extract a REVISION from the pagelist structure.
If BIT is 'content, then return the content only.  Otherwise,
return only the items that BIT matches.  If BIT isn't given,
return the whole revision structure."
  (let ((rev (cdr (nth revision (cddr (assq 'revisions (cddr page)))))))
    (cond
     ((eq bit 'content)
      (cadr rev))
     ((assoc bit (car rev))
      (cdr (assoc bit (car rev))))
     (t rev))))

(defun mediawiki-pagelist-find-page (pagelist title)
  "Given PAGELIST, extract the informaton for TITLE."
  (let ((pl (cddr (assq 'pages pagelist)))
        page current)
    (while (and (not page)
                (setq current (pop pl)))
      ;; This fails when underbars are here instead of spaces,
      ;; so we make sure that it has the mediawiki pagename
      (when (string= (mediawiki-page-get-title current)
                     (mediawiki-translate-pagename title))
        (setq page current)))
    page))

(defun mediawiki-api-query-title (sitename title)
  "Query SITENAME for TITLE."
  (let* ((pagelist (mediawiki-api-query-revisions
                    sitename title
                    (list "ids" "timestamp" "flags" "comment" "user" "content"))))
    (mediawiki-pagelist-find-page pagelist title)))

(defun mediawiki-get (sitename title)
  "Query SITENAME for the content of TITLE."
  (let ((page (mediawiki-api-query-title sitename title)))
    (mediawiki-save-metadata sitename page)
    (mediawiki-page-get-revision page 0 'content)))

(defun mediawiki-page-get-metadata (page item)
  "Using PAGE, extract ITEM."
  (cdr (assoc item (cadr page))))

(defun mediawiki-save-metadata (sitename page)
  "Set per-buffer variables for all the SITENAME data for PAGE."
  (setq mediawiki-site sitename)
  (setq mediawiki-page-title
        (mediawiki-page-get-metadata page 'title))
  (setq mediawiki-edittoken
        (mediawiki-page-get-metadata page 'edittoken))
  (setq mediawiki-basetimestamp
        (mediawiki-page-get-revision page 0 'timestamp))
  (setq mediawiki-starttimestamp
        (mediawiki-page-get-metadata page 'starttimestamp)))

(defun mediawiki-save (&optional summary)
  "Save the current buffer as a page on the current site.
Prompt for a SUMMARY if one isn't given."
  (interactive "sSummary: ")
  (when (not (eq major-mode 'mediawiki-mode))
    (error "Not a mediawiki-mode buffer"))
  (if mediawiki-page-title
      (mediawiki-save-page
       mediawiki-site
       mediawiki-page-title
       summary
       (buffer-substring-no-properties (point-min) (point-max)))
    (error "Error: %s is not a mediawiki document" (buffer-name))))

(defun mediawiki-prompt-for-page ()
  "Prompt for a page name and return the answer."
  (let* ((prompt (concat "Page"
                         (when mediawiki-page-title
                           (format " (default %s)" mediawiki-page-title))
                         ": "))
         (answer (completing-read prompt '())))
    (if (string= "" answer)
        mediawiki-page-title
      answer)))

(defun mediawiki-prompt-for-summary ()
  "Prompt for a summary and return the answer."
  (completing-read  "Summary: " '()))

(defun mediawiki-save-on (&optional sitename name summary)
  "On SITENAME, save a page with NAME and SUMMARY."
  (interactive)
  (when (not sitename)
    (setq sitename (mediawiki-prompt-for-site)))
  (when (not name)
    (setq name (mediawiki-translate-pagename (mediawiki-prompt-for-page))))
  (when (not summary)
    (setq summary (mediawiki-prompt-for-summary)))

  (setq mediawiki-site (mediawiki-do-login sitename))
  (mediawiki-get mediawiki-site name)
  (mediawiki-save-as name summary))

(defun mediawiki-save-as (&optional name summary)
  "Save a page on the current site wite NAME and SUMMARY."
  (interactive "sSave As: \nsSummary: ")
  (if name
      (mediawiki-save-page
       mediawiki-site
       name
       summary
       (buffer-substring-no-properties (point-min) (point-max)))
    (error "Error: %s is not a mediawiki document" (buffer-name))))

(defun mediawiki-save-and-bury (&optional summary)
  "Prompt for a SUMMARY, save the page, then bury the buffer."
  (interactive "sSummary: ")
  (mediawiki-save summary)
  (bury-buffer))

(defun mediawiki-site-extract (sitename index)
  "Using 'mediawiki-site-alist' and SITENAME, find the nth item using INDEX."
  (let* ((site (assoc sitename mediawiki-site-alist))
         (bit (nth index site)))
    (cond
     ((eq nil sitename)
      (error "Sitename isn't set"))
     ((eq nil site)
      (error "Couldn't find a site named: %s" sitename))
     ((stringp bit)
      bit)
     (nil))))

(defun mediawiki-site-url (sitename)
  "Get the url for a given SITENAME."
  (mediawiki-site-extract sitename 1))

(defmacro mediawiki-site-user-pass (sitename index method)
  "Fetch the user or pass if provided, or use authinfo if not."
  `(let* ((arg (mediawiki-site-extract ,sitename ,index))
          (auth (funcall ,method (mediawiki-site-url ,sitename))))
     (if (and arg (> (string-width arg) 0))
         arg
       auth)))

(defun mediawiki-site-username (sitename)
  "Get the username for a given SITENAME."
  (mediawiki-site-user-pass sitename 2 'url-user-for-url))

(defun mediawiki-site-password (sitename)
  "Get the password for a given SITENAME."
  (mediawiki-site-user-pass sitename 3 'url-password-for-url))

(defun mediawiki-site-domain (sitename)
  "Get the LDAP domain for a given SITENAME."
  (mediawiki-site-extract sitename 4))

(defun mediawiki-site-first-page (sitename)
  "Get the first page for a given SITENAME."
  (mediawiki-site-extract sitename 5))

(defun mediawiki-site-get-token (sitename type)
  "Get token(s) for SITENAME of TYPE type."
  (cdr
   (caadar
    (cddr (mediawiki-api-call sitename "query"
                              (list (cons "meta" "tokens")
                                    (cons "type" type)))))))

(defun mediawiki-do-login (&optional sitename username password domain)
  "Log into SITENAME using USERNAME, PASSWORD and DOMAIN.
Store cookies for future authentication."
  (interactive)
  (when (not sitename)
    (setq sitename (mediawiki-prompt-for-site)))

  (setq mediawiki-site nil)             ; This wil be set once we are
                                        ; logged in

  ;; Possibly save info once we have it, eh?
  (lexical-let* ((user (or (mediawiki-site-username sitename)
                           username
                           (read-string "Username: ")))
                 (pass (or (mediawiki-site-password sitename)
                           password
                           (read-passwd "Password: ")))
                 (dom-loaded (mediawiki-site-domain sitename))
                 (dom (when dom-loaded
                        (if (string= "" dom-loaded)
                            (read-string "LDAP Domain: ")
                          dom-loaded)))
                 (sitename sitename)
                 (token (mediawiki-site-get-token sitename "login"))
                 (args (list (cons "lgname" user)
                             (cons "lgpassword" pass)
                             (when token
                               (cons "lgtoken" token))
                             (when dom
                               (cons "lgdomain" dom))))
                 (result (cadr (mediawiki-api-call sitename "login" args))))
    (when (string= (cdr (assq 'result result)) "NeedToken")
      (setq result
            (cadr (mediawiki-api-call sitename "login"
                   (append
                    args (list (cons "lgtoken"
                                     (cdr (assq 'token result)))))))))
    (when (string= "Success" (cdr (assoc 'result result)))
      sitename)))

(defun mediawiki-do-logout (&optional sitename)
  "Log out of SITENAME."
  (interactive)
  (when (not sitename)
    (setq sitename (mediawiki-prompt-for-site)))

  (mediawiki-api-call sitename "logout" nil)
  (setq mediawiki-site nil))

(defun mediawiki-save-page (sitename title summary content &optional trynum)
  "On SITENAME, save the current page using TITLE, SUMMARY, and CONTENT."
  ;; FIXME error checking, conflicts!
  (when (and trynum (< trynum 0))
    (error "Too many tries."))
  (let ((trynum (or trynum 3)))
    (condition-case err
        (mediawiki-api-call sitename "edit"
                            (list (cons "title"
                                        (mediawiki-translate-pagename title))
                                  (cons "text" content)
                                  (cons "summary" summary)
                                  (cons "token" mediawiki-edittoken)
                                  (cons "basetimestamp"
                                        (or mediawiki-basetimestamp ""))
                                  (cons "starttimestamp"
                                        (or mediawiki-starttimestamp ""))))
      (error (progn (message (concat trynum "Retry because of error: " err))
                    (mediawiki-retry-save-page
                     sitename title summary content trynum)))))
  (set-buffer-modified-p nil))

(defun mediawiki-retry-save-page (sitename title summary content trynum)
  "Refresh the edit token and then try to save the current page using TITLE,
SUMMARY, and CONTENT on SITENAME."
  (let ((try (if trynum
                 (- trynum 1)
               3)))
    (mediawiki-do-login sitename)
    (setq mediawiki-edittoken (mediawiki-site-get-token sitename "csrf"))
    (mediawiki-save-page sitename title summary content try)))

(defun mediawiki-browse (&optional buffer)
  "Open the BUFFER in a browser.
If BUFFER is not given, the current buffer is used."
  (interactive)
  (if mediawiki-page-title
      (browse-url (mediawiki-make-url mediawiki-page-title "view"))
    (with-current-buffer buffer
      (browse-url (mediawiki-make-url mediawiki-page-title "view")))))

(defun mediawiki-prompt-for-site ()
  "Prompt the user for a site."
  (let* ((prompt (concat "Sitename"
                         (when mediawiki-site
                           (format " (default %s)" mediawiki-site))
                         ": "))
         (answer (completing-read prompt mediawiki-site-alist nil t)))
    (if (string= "" answer)
        mediawiki-site
      answer)))

;;;###autoload
(defun mediawiki-site (&optional site)
  "Set up mediawiki.el for a SITE.
Without an argument, use `mediawiki-site-default'.
Interactively, prompt for a SITE."
  (interactive)
  (when (not site)
    (setq site (mediawiki-prompt-for-site)))
  (when (or (eq nil mediawiki-site)
            (not (string-equal site mediawiki-site)))
    (setq mediawiki-site (mediawiki-do-login site)))
  (mediawiki-edit site (mediawiki-site-first-page site)))

(defun mediawiki-open-page-at-point ()
  "Open a new buffer with the page at point."
  (interactive)
  (mediawiki-open (mediawiki-page-at-point)))

(defun mediawiki-page-at-point ()
  "Return the page name under point.
Typically, this means anything enclosed in [[PAGE]]."
  (let ((pos (point))
        (eol (point-at-eol))
        (bol (point-at-bol)))
    (save-excursion
      (let* ((start  (when (search-backward "[[" bol t)
                       (+ (point) 2)))
             (end    (when (search-forward "]]" eol t)
                       (- (point) 2)))
             (middle (progn
                       (goto-char start)
                       (when (search-forward  "|" end t)
                         (1- (point)))))
             (pagename (when (and
                              (not (eq nil start))
                              (not (eq nil end))
                              (<= pos end)
                              (>= pos start))
                         (buffer-substring-no-properties
                          start (or middle end)))))
        (if (string= "/"
                     (substring pagename 0 1))
            (concat mediawiki-page-title pagename)
          pagename)))))

(defun mediawiki-next-header ()
  "Move point to the end of the next section header."
  (interactive)
  (let ((oldpoint (point)))
    (end-of-line)
    (if (re-search-forward "\\(^==+\\).*\\1" (point-max) t)
        (beginning-of-line)
      (goto-char oldpoint)
      (message "No section headers after point."))))

(defun mediawiki-prev-header ()
  "Move point to the start of the previous section header."
  (interactive)
  (unless (re-search-backward "\\(^==+\\).*\\1" (point-min) t)
    (message "No section headers before point.")))

(defun mediawiki-terminate-paragraph ()	;Version:1.58
  "End a paragraph by any means necessary.
In a list, start a new list item; in a paragraph, start a new paragraph;
if the current paragraph is colon indented, the new
paragraph will be indented in the same way."
  (interactive)
  (let (indent-chars)
    (save-excursion
      (beginning-of-line)
      (while (cond ((looking-at "^$") nil)
                   ((looking-at "^\\(\\(?: \\|:+\\|[#*]+\\) *\\)")
                    (setq indent-chars (match-string 1)) nil)
                   ((eq (point) (point-min)) nil)
                   ((progn (forward-line -1) t)))
        t))
    (newline) (if (not indent-chars) (newline)
		(insert indent-chars))))

(defun mediawiki-terminate-paragraph-and-indent ()
  "In a list, start a new list item.
In a paragraph, start a new paragraph but *,# will be ignored; if
the current paragraph is colon indented, the new paragraph will
be indented in the same way."
  (interactive)
  (let (indent-chars)
    (save-excursion
      (beginning-of-line)
      (while (cond ((looking-at "^$") nil)
                   ((looking-at "^\\(\\(?: \\|:+\\) *\\)")
                    (setq indent-chars (match-string 1)) nil)
                   ((eq (point) (point-min)) nil)
                   ((progn (forward-line -1) t)))
        t))
    (newline)
    (if (not indent-chars) (newline)
      (insert indent-chars))))


(defun mediawiki-link-fill-nobreak-p ()
  "When filling, don't break the line for preformatted (fixed-width)
text or inside a Wiki link.  See `fill-nobreak-predicate'."
  (save-excursion
    (let ((pos (point)))
      (or (eq (char-after (line-beginning-position)) ? )
          (if (re-search-backward "\\[\\[" (line-beginning-position) t)
              ;; Break if the link is really really long.
              ;; You often get this with captioned images.
              (null (or (> (- pos (point)) fill-column)
                        (re-search-forward "\\]\\]" pos t))))))))

(defun mediawiki-fill-article ()
  "Fill the entire article."
  (interactive)
  (save-excursion
    (fill-region (point-min) (point-max))))

(defun mediawiki-unfill-article ()
  "Undo filling, deleting stand-alone newlines.
Stand-alone newlines are those that do not end paragraphs, list
entries, etc."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward ".\\(\n\\)\\([^# *;:|!\n]\\|----\\)" nil t)
      (replace-match " " nil nil nil 1)))
  (message "Stand-alone newlines deleted"))

(defun mediawiki-draft-reply ()
  "Open a temporary buffer to edit a draft.
After finishing the editing: either use 'mediawiki-draft-buffer'
to send the data into the 'mediawiki-draft-data-file'.  Check the
variable mediawiki-draft-send-archive."
  (interactive)
  (mediawiki-reply-at-point-simple)
  (beginning-of-line 1)
  (kill-line nil)
  (save-excursion
	(window-configuration-to-register mediawiki-draft-register)
	(let ((buf (get-buffer-create mediawiki-draft-buffer)))
	  (switch-to-buffer-other-window buf)
	  (mediawiki-mode)
	  (if mediawiki-reply-with-quote
              (progn
		(insert "{{Quotation|")
		(yank)
		(insert "'''Re: ")
		(insert-register mediawiki-draft-reply-register 1)
		(insert "''' |~~~~}}")
		(backward-char 7))
            (when mediawiki-reply-with-hline
              (insert "----")
              (newline 1))
            (yank)
            (end-of-line 1))
	  (message " C-c C-k sends to draft, C-c C-c sends to org buffer."))))

(defun mediawiki-reply-at-point-simple ()
  "Very simple function to reply to posts in the discussion forum.
You have to set the point around the signature, then the
functions inserts the following
:'''Re: [[User:foo]]'''."
  (interactive)
  (beginning-of-line 1)
  (if mediawiki-english-or-german
      (progn
        (search-forward "(UTC)")
        (search-backward "[[User:"))
    (search-forward "(CET)")
    (search-backward "[[Benutzer:"))
  (if mediawiki-user-simplify-signature
      (mark-word 2)
    (mark-word 3))
  (copy-to-register mediawiki-draft-reply-register (region-beginning) (region-end) nil)
  (end-of-line 1)
  (mediawiki-terminate-paragraph-and-indent)
  (insert ":'''Re: ")
  (insert-register mediawiki-draft-reply-register 1)
  (if mediawiki-user-simplify-signature
      (insert "|]]''' ")
    (insert "]]''' ")))

(defmacro mediawiki-goto-relative-page (direction)
  "Go to the next page in DIRECTION."
  `(let ((buff (ring-ref mediawiki-page-ring
                        (setq mediawiki-page-ring-index
                              (,direction mediawiki-page-ring-index 1)))))
     (while (not (buffer-live-p buff))
       (setq buff
             (ring-ref mediawiki-page-ring
                       (setq mediawiki-page-ring-index
                             (,direction mediawiki-page-ring-index 1)))))
     (mediawiki-pop-to-buffer buff)))

(defun mediawiki-goto-previous-page ()
  "Pop up the previous page being editted."
  (interactive)
  (mediawiki-goto-relative-page -))

(defun mediawiki-goto-next-page ()
  "Pop up the previous page being editted."
  (interactive)
  (mediawiki-goto-relative-page +))

(defun mediawiki-goto-relative-link (&optional backward)
  "Move point to a link.
If BACKWARD is t, will search backwards."
  (let* ((search (if backward 're-search-backward
                   're-search-forward))
         (limitfunc (if backward 'point-min
                      'point-max))
         (point (funcall search "\\[\\[.+\\]\\]" (funcall limitfunc) t)))
    (when point
      (let ((point (match-beginning 0)))
        (goto-char (+ point 2))))))

(defun mediawiki-goto-next-link ()
  "Go to the next link in the page."
  (interactive)
  (mediawiki-goto-relative-link))

(defun mediawiki-goto-prev-link ()
  "Go to the previous link in the page."
  (interactive)
  (mediawiki-goto-relative-link t))

(defvar mediawiki-enumerate-with-terminate-paragraph nil
"*Before insert enumerate/itemize do \\[mediawiki-terminate-paragraph].")

(defun mediawiki-insert-enumerate ()
  "Primitive function for inserting enumerated items.
Check the variable mediawiki-enumerate-with-terminate-paragraph.
Note however that the function \\[mediawiki-terminate-paragraph]
does not work very well will longlines-mode."
  (interactive)
  (if mediawiki-enumerate-with-terminate-paragraph
      (progn
        (mediawiki-terminate-paragraph)
        (insert "#"))
    (newline nil)
    (insert ":#")))

(defun mediawiki-insert-itemize ()
  "Primitive function for inserting no enumerated items.
Check the variable mediawiki-enumerate-with-terminate-paragraph.
Note however that the function \\[mediawiki-terminate-paragraph]
does not work very well will longlines-mode."
  (interactive)
  (if mediawiki-enumerate-with-terminate-paragraph
      (progn
        (mediawiki-terminate-paragraph)
        (insert "*"))
    (newline nil)
    (insert ":*")))

(defun mediawiki-insert (pre post)
  "Wrap the current region with PRE and POST."
  (if (or (and (boundp 'zmacs-region-active-p) zmacs-region-active-p)
          (and (boundp 'transient-mark-mode) transient-mark-mode mark-active))
      (let ((beg (region-beginning))
            (end (region-end)))
        (save-excursion
          (goto-char beg)
          (insert pre)
          (goto-char (+ end (string-width pre)))
          (insert post)))
    (insert (concat pre " " post))
    (backward-char (+ 1 (string-width post)))))

(defun mediawiki-insert-strong-emphasis ()
  "Mark with strong emphasis italics.
Uses four apostrophes (e.g. ''''FOO'''').  When mark is active,
surrounds region."
  (interactive)
  (mediawiki-insert "''''" "''''"))

(defun mediawiki-insert-bold ()
  "Mark bold.
Uses three apostrophes (e.g. '''FOO''').  When mark is active,
surrounds region."
  (interactive)
  (mediawiki-insert "'''" "'''"))


(defun mediawiki-insert-italics ()
  "Mark italics.
Uses TWO apostrophes (e.g. ''FOO'').  When mark is active,
surrounds region."
  (interactive)
  (mediawiki-insert "''" "''"))

(defun mediawiki-insert-quotation-with-signature ()
  "Mark the current region as a quotation with your signature."
  (interactive)
  (mediawiki-insert "{{Quotation|}}" "{{~~~~}}"))

(defun mediawiki-insert-quotation ()
  "Mark the current selection as a quote.
Use the form {{Quotation}}{{}}.  When mark is active,
surrounds region."
  (interactive)
  (mediawiki-insert "{{Quotation|}}{{" "}}"))

(defun mediawiki-insert-bible-verse-template ()
  "Insert a template for the quotation of Bible verses."
  (interactive)
  (insert "({{niv|")
  (let ((name    (read-string "Name: ")))
    (insert (concat name "|"))
    (let ((verse (read-string "Verse: ")))
      (insert (concat verse "|" name " " verse "}})")))))

(defun mediawiki-insert-user ()
  "Interactively insert a user name."
  (interactive)
  (if mediawiki-english-or-german
      (let ((user (read-string "Name of user: " )))
        (insert (concat "[[User:" user "|" user "]]")))
    (let ((user (read-string "Name des Benutzers: " )))
      (insert (concat "[[Benutzer:" user "|" user "]]")))))

(defun mediawiki-insert-reply-prefix ()
  "Quotation box of the form {{Quotation}}{{}}."
  (interactive)
  (beginning-of-line 1)
  (search-forward "[[")
  (backward-char 2)
  (mark-sexp 1)
  (copy-to-register mediawiki-draft-reply-register (region-beginning) (region-end) nil)
  (end-of-line 1)
  (mediawiki-terminate-paragraph)
  (beginning-of-line 1)
  (kill-line nil)
  (insert "----")
  (newline 1)
  (yank)
  (insert ":'''Re: ")
  (insert-register mediawiki-draft-reply-register 1)
  (insert "''' ")
  (end-of-line 1))

(defun mediawiki-insert-header ()
  "Insert subheader via == (e.g. == FOO ==)."
  (interactive)
  (mediawiki-insert "==" "=="))

(defun mediawiki-insert-link ()
  "Insert link (e.g. [[FOO]])."
  (interactive)
  (mediawiki-insert "[[" "]]"))

(defun mediawiki-insert-link-www ()
  "Insert link (e.g. [://FOO])."
  (interactive)
  (mediawiki-insert "[://" "]"))

(defun mediawiki-insert-image ()
  "Insert image link (e.g. [[Image:FOO]]).
Checks the variable mediawiki-english-or-german."
  (interactive)
  (mediawiki-insert (if mediawiki-english-or-german
                        "[[Image:"
                      "[[Bild:") "]]"))

(defun mediawiki-insert-audio ()
  "Insert audio link (e.g. [[Media:FOO]])
Checks The variable mediawiki-english-or-german."
  (interactive)
  (mediawiki-insert (if mediawiki-english-or-german
                        "[[Media:"
                      "[[Bild:") "]]"))

(defun mediawiki-insert-signature ()
  "Insert signature (e.g. \"~~~~:\")."
  (interactive)
  (insert "~~~~: "))

(defun mediawiki-insert-hline ()
  "Insert hline (e.g. \"----\")."
  (interactive)
  (insert "\n----\n"))

(defun mediawiki-unfill-paragraph-or-region ()
  "Unfill region.
This function does NOT explicitly search for \"soft newlines\"
as does mediawiki-unfill-region."
  (interactive)
  (set (make-local-variable 'paragraph-start) "[ \t\n\f]")
  (set (make-local-variable 'paragraph-start)
       "\\*\\| \\|#\\|;\\|:\\||\\|!\\|$")
  (set-fill-prefix)
  (beginning-of-line 1)

  (if use-hard-newlines
      (progn
        (set (make-local-variable 'use-hard-newlines) nil)
        (set (make-local-variable 'sentence-end-double-space) t))
    (set (make-local-variable 'sentence-end-double-space) nil)
    (set (make-local-variable 'use-hard-newlines) t))
  (let ((fill-column (point-max)))
    (if (fboundp 'fill-paragraph-or-region)
        (fill-paragraph-or-region nil)
      (fill-paragraph nil))))

(defun mediawiki-start-paragraph ()
  "Start a Paragraph."
  (interactive)
  (set (make-local-variable 'paragraph-start)
       "\\*\\| \\|#\\|;\\|:\\||\\|!\\|$"))

(defun mediawiki-hardlines ()
  "Set 'use-hard-newlines' to NIL."
  (interactive)
  (setq use-hard-newlines nil))

(defun mediawiki-next-long-line ()
  "Move forward to the next long line.
Lines are considered long if their length is greater
than `fill-column'.

TODO: When function reaches end of buffer, 'save-excursion' to
starting point.  Generalise to make `previous-long-line'."
  (interactive)
  ;; global-variable: fill-column
  (if (= (forward-line) 0)
	  (let ((line-length
			 (save-excursion
			   (end-of-line)
			   (current-column))))
		(if (<= line-length fill-column)
			(mediawiki-next-long-line)
		  (message "Long line found")))
	;; Stop, end of buffer reached.
 	(error "Long line not found")))

(defun mediawiki-unfill-paragraph-simple ()
  "A very simple function for unfilling a paragraph."
  (interactive)
  (let ((fill-column (point-max)))
    (fill-paragraph nil)))

(defun mediawiki-outline-magic-keys ()
  "Set up outline magic keys.
See https://www.emacswiki.org/emacs/OutlineMagic"
  (interactive)
  (unless  (featurep 'xemacs)
    (local-set-key [(shift iso-lefttab)] 'outline-cycle)
    (local-set-key [iso-left-tab] 'outline-cycle))
  (local-set-key [(meta left)]  'outline-promote)
  (local-set-key [(meta right)] 'outline-demote)
  (local-set-key [(shift return)] 'newline-and-indent)
  (local-set-key [(control left)]  'mediawiki-simple-outline-promote)
  (local-set-key [(control right)] 'mediawiki-simple-outline-demote)
  (local-set-key [(control up)] 'outline-move-subtree-up)
  (local-set-key [(control down)] 'outline-move-subtree-down))
(add-hook 'mediawiki-mode-hook (lambda () (outline-minor-mode nil)))
(add-hook 'outline-minor-mode-hook 'mediawiki-outline-magic-keys)

(defun mediawiki-enhance-indent ()
  "Indent a region using MediaWiki markup (e.g \":\")."
  (interactive)
  (string-rectangle (region-beginning) (region-end) ":"))

(defun mediawiki-yank-prefix ()
  "Remove indent markup from region.
FIXME!!!"
  (interactive)
  (string-rectangle (region-beginning) (region-end) " "))

(defun mediawiki-simple-outline-promote ()
  "Simple-minded promotion of current line.
This function simply deletes one \"=\" from the beginning and end
of the line.  It does not promote the whole tree!"
  (interactive)
  (save-excursion
    (beginning-of-line 1)
    (search-forward "=")
    (delete-char 1 nil)
    (end-of-line 1)
    (search-backward "=")
    (delete-char 1 nil)))

(defun mediawiki-simple-outline-demote ()
  "Simple-minded demotion of the current line.
This function simple adds \"=\" to the beginning and end of the
line.  It does not promote the whole tree!"
  (interactive)
  (save-excursion
    (beginning-of-line 1)
    (search-forward "=")
    (insert "=")
    (end-of-line 1)
    (search-backward "=")
    (insert "=")))

(defun mediawiki-rename-buffer ()
  "Make sure that the option UNIQUE is used."
  (interactive)
  (rename-buffer (read-string "Name of new buffer (unique): " ) 1))

(defsubst mediawiki-draft-time-to-seconds (time)
  "Convert TIME to a floating point number."
  (+ (* (car time) 65536.0)
     (cadr time)
     (/ (or (car (cdr (cdr time))) 0) 1000000.0)))

(defsubst mediawiki-draft-mail-date (&optional rfc822-p)
  "Return a simple date.
If RFC822-P is passed, use RFC822 format."
  (if rfc822-p
      (format-time-string "%a, %e %b %Y %T %z" (current-time))
    (format-time-string "%c" (current-time))))

(defun mediawiki-draft-buffer-desc ()
  "Using the first line of the current buffer, create a short description."
  (buffer-substring (point-min)
		    (save-excursion
		      (goto-char (point-min))
		      (end-of-line)
		      (if (> (- (point) (point-min)) 60)
			  (goto-char (+ (point-min) 60)))
		      (point))))

(defun mediawiki-draft-append-to-file ()
  "Append a draft to the drafts file."
  (let ((text (buffer-string)))
    (with-temp-buffer
      (insert (concat "\n\n"  mediawiki-draft-leader-text "Draft: "
                      (read-string "Enter Subject: ") " "
                      (current-time-string) " "
                      mediawiki-draft-leader-text
                      "\n\n\f\n\n" text "\n\f\n"))
      (if (not (bolp))
          (insert "\n\n"))
      (if (find-buffer-visiting mediawiki-draft-data-file)
          (let ((mediawiki-draft-text (buffer-string)))
            (set-buffer (get-file-buffer mediawiki-draft-data-file))
            (save-excursion
              (goto-char (point-max))
              (insert (concat "\n" mediawiki-draft-text "\n"))
              (save-buffer)))
        (append-to-file (point-min) (point-max) mediawiki-draft-data-file)))))

;;;###autoload
(defun mediawiki-draft ()
  "Open a temporary buffer in mediawiki-mode.
This is for editing a draft.  After finishing the editing either
use \\[mediawiki-draft-buffer] to send the data into the
mediawiki-draft-data-file, or send the buffer using
\\[mediawiki-save] and insert it later into a mediawiki article."
  (interactive)
  (window-configuration-to-register mediawiki-draft-register)
  (let ((buf (get-buffer-create mediawiki-draft-buffer)))
    (switch-to-buffer-other-window buf)
    (mediawiki-mode)
    (message " C-c C-k sends to draft file, C-c C-c sends to org buffer.")))

(defun mediawiki-draft-page ()
  "Set the current buffer as a draft buffer."
  (interactive)
  (mark-page)
  (copy-region-as-kill (region-beginning) (region-end))
  (mediawiki-draft)
  (yank nil))

(defun mediawiki-draft-region (&optional begin end)
  "Mediawiki-draft the data from BEGIN to END.
If called from within the mediawiki-draft buffer, BEGIN and END are ignored,
and the entire buffer will be mediawiki-drafted.  If called from any other
buffer, that region, plus any context information specific to that
region, will be mediawiki-drafted."
  (interactive)
  (let ((b (or begin (min (point) (or (mark) (point-min)))))
	(e (or end (max (point) (or (mark) (point-max))))))
    (save-restriction
      (narrow-to-region b e)
      (run-hook-with-args-until-success 'mediawiki-draft-handler-functions)
    (when (equal mediawiki-draft-buffer (buffer-name))
      (mediawiki-debug (current-buffer) "mediawiki-draft-region")
      (jump-to-register mediawiki-draft-register)))))

(defun mediawiki-draft-buffer ()
  "Mediawiki-draft-buffer sends the contents of the current (temporary)
buffer to the mediawiki-draft-buffer, see the variable
mediawiki-draft-data-file."
  (interactive)
  (mediawiki-draft-region  (point-min) (point-max)))

(defun mediawiki-draft-clipboard ()
  "Mediawiki-Draft the contents of the current clipboard.
Most useful for mediawiki-drafting things from Netscape or other X Windows
application."
  (interactive)
  (with-temp-buffer
    (insert (if (fboundp 'gui-get-selection) ; Since 25.1
                (gui-get-selection)
              (x-get-clipboard)))
    (run-hook-with-args-until-success 'mediawiki-draft-handler-functions)))

(defun mediawiki-draft-view-draft ()
  "Simple shortcut to visit the drafts file."
  (interactive)
  (find-file mediawiki-draft-data-file))

(defun mediawiki-mark-section ()
  "Set mark at end of current logical section, and point at top."
  (interactive)
  (re-search-forward (concat  "== "  "[a-z,A-z \t]*" " =="))
  (re-search-backward "^")
  (set-mark (point))
  (re-search-backward (concat "== "  "[a-z,A-z \t]*" " "))
  (when (fboundp 'zmacs-activate-region)
    (zmacs-activate-region)))

(defun mediawiki-mark-signature ()
  "Set mark at end of current logical section, and point at top."
  (interactive)
  (re-search-forward "]]") ;;[[ ]]
  (re-search-backward "^")
  (set-mark (point))
  (re-search-backward "[[")
  (when (fboundp 'zmacs-activate-region)
    (zmacs-activate-region)))

(defun mediawiki-draft-copy-page-to-register ()
  "Copy a page via the mediawiki-draft-register."
  (interactive)
  (save-excursion
    (narrow-to-page nil)
    (copy-to-register mediawiki-draft-page (point-min) (point-max) nil)
    (message "draft page copied to wikipedia register mediawiki-draft-page.")
    (widen)))

(defun mediawiki-draft-yank-page-to-register ()
  "Insert a page via the mediawiki-draft-register."
  (interactive)
  (insert-register mediawiki-draft-page nil))

(defun mediawiki-draft-send (target-buffer)
  "Copy the current page in the drafts file to TARGET-BUFFER.
If 'mediawiki-draft-send-archive' is t, then additionally the
text will be archived in the draft.wiki file."
  (interactive "bTarget buffer: ")
  (mediawiki-draft-copy-page-to-register)
  (switch-to-buffer target-buffer)
  (end-of-line 1)
  (newline 1)
  (mediawiki-draft-yank-page-to-register)
  (message "The page has been sent (copied) to the mozex file!")
  (switch-to-buffer "*MW-Draft*")
  (when mediawiki-draft-send-archive
    (let ((text (buffer-string)))
      (with-temp-buffer
	(insert (concat "\n\n" mediawiki-draft-leader-text)
		(insert-register mediawiki-draft-reply-register 1)
		(insert (concat " " (current-time-string) " "
				mediawiki-draft-leader-text  "\n\n\f\n\n"
				text "\n\f\n"))
		(if (not (bolp))
		    (insert "\n\n"))
		(if (find-buffer-visiting mediawiki-draft-data-file)
		    (let ((mediawiki-draft-text (buffer-string)))
		      (set-buffer (get-file-buffer mediawiki-draft-data-file))
		      (save-excursion
			(goto-char (point-max))
			(insert (concat "\n" mediawiki-draft-text "\n"))
			(save-buffer)))
		  (append-to-file (point-min) (point-max)
				  mediawiki-draft-data-file)))))
    (when (equal mediawiki-draft-buffer (buffer-name))
      (mediawiki-debug (current-buffer) "mediawiki-draft-send"))
    (switch-to-buffer target-buffer)))

(define-derived-mode mediawiki-draft-mode text-mode "MW-Draft"
  "Major mode for output from \\[mediawiki-draft].
\\<mediawiki-draft-mode-map> This buffer is used to collect data that
you want mediawiki-draft.  Just hit \\[mediawiki-draft-region] when
you're done entering, and it will go ahead and file the data for
latter retrieval, and possible indexing.
\\{mediawiki-draft-mode-map}"
  (kill-all-local-variables)
  (indented-text-mode)
  (define-key mediawiki-draft-mode-map "\C-c\C-k" 'mediawiki-draft-buffer)
  (define-key mediawiki-draft-mode-map "\C-c\C-d" 'mediawiki-draft-buffer))

(define-derived-mode mediawiki-mode text-mode "MW"
  "Major mode for editing articles written in the markup language
used by Mediawiki.

Wikipedia articles are usually unfilled: newline characters are not
used for breaking paragraphs into lines. Unfortunately, Emacs does not
handle word wrapping yet. As a workaround, mediawiki-mode turns on
longlines-mode automatically. In case something goes wrong, the
following commands may come in handy:

\\[mediawiki-fill-article] fills the buffer.
\\[mediawiki-unfill-article] unfills the buffer.

Be warned that function can be dead  slow, better use mediawiki-unfill-paragraph-or-region.
\\[mediawiki-unfill-paragraph-or-region] unfills the paragraph
\\[mediawiki-unfill-paragraph-simple] doehe same but simpler.

The following commands put in markup structures.
\\[mediawiki-insert-strong-emphasis] inserts italics
\\[mediawiki-insert-bold] inserts bold text
\\[mediawiki-insert-italics] italics
\\[mediawiki-insert-header] header
\\[mediawiki-insert-link] inserts a link

The following commands are also defined:
\\[mediawiki-insert-user] inserts user name
\\[mediawiki-insert-signature] inserts ~~~~
\\[mediawiki-insert-enumerate] inserts enumerate type structures
\\[mediawiki-insert-itemize] inserts itemize type structures
\\[mediawiki-insert-hline] inserts a hline

The draft functionality
\\[mediawiki-draft]
\\[mediawiki-draft-region]
\\[mediawiki-draft-view-draft]
\\[mediawiki-draft-page]
\\[mediawiki-draft-buffer]

Replying and sending functionality
\\[mediawiki-reply-at-point-simple]
\\[mediawiki-draft-reply]

The register functionality
\\[mediawiki-copy-page-to-register]
\\[defun mediawiki-insert-page-to-register]

Some simple editing commands.
\\[mediawiki-enhance-indent]
\\[mediawiki-yank-prefix]
\\[mediawiki-unfill-paragraph-or-region]

\\[mediawiki-terminate-paragraph]     starts a new list item or paragraph in a context-aware manner.
\\[mediawiki-next-header]     moves to the next (sub)section header.
\\[mediawiki-prev-header]     moves to the previous (sub)section header."

  (make-local-variable 'change-major-mode-hook)
  (make-local-variable 'mediawiki-edittoken)
  (make-local-variable 'mediawiki-starttimestamp)
  (make-local-variable 'mediawiki-basetimestamp)
  (make-local-variable 'mediawiki-site)
  (make-local-variable 'mediawiki-edit-form-vars)
  (make-local-variable 'mediawiki-page-title)
  (set (make-local-variable 'adaptive-fill-regexp) "[ ]*")
  (set (make-local-variable 'comment-start-skip) "\\(?:<!\\)?-- *")
  (set (make-local-variable 'comment-end-skip) " *--\\([ \n]*>\\)?")
  (set (make-local-variable 'comment-start) "<!-- ")
  (set (make-local-variable 'comment-end) " -->")
  (set (make-local-variable 'paragraph-start)
       "\\*\\| \\|#\\|;\\|:\\||\\|!\\|$")
  (set (make-local-variable 'sentence-end-double-space) nil)
  (set (make-local-variable 'font-lock-multiline) t)
  (set (make-local-variable 'font-lock-defaults)
       '(mediawiki-font-lock-keywords t nil nil nil))
  (set (make-local-variable 'fill-nobreak-predicate)
       'mediawiki-link-fill-nobreak-p)
  (set (make-local-variable 'auto-fill-inhibit-regexp) "^[ *#:|;]")

  ;; Support for outline-minor-mode. No key conflicts, so we'll use
  ;; the normal outline-mode prefix.
  (set (make-local-variable 'outline-regexp) "==+")
  (when (boundp 'outline-minor-mode-prefix)
    (set (make-local-variable 'outline-minor-mode-prefix) "\C-c\C-o"))
; (set (make-local-variable 'outline-regexp) "=+")
; (set (make-local-variable 'outline-regexp) ":")

  ;; Turn on the Imenu automatically.
  (when menu-bar-mode
    (set (make-local-variable 'imenu-generic-expression)
         mediawiki-imenu-generic-expression)
    (imenu-add-to-menubar "Contents"))

  (let ((map (make-sparse-keymap "mediawiki")))
    (define-key mediawiki-mode-map [menu-bar mediawiki]
      (cons "MediaWiki" map))
    (define-key map [unfill-article]
      '("Unfill article" . mediawiki-unfill-article))
    (define-key map [fill-article]
      '("Fill article" . mediawiki-fill-article))
    (define-key map [separator-fill] '("--"))
    (define-key map [next-header]
      '("Next header" . mediawiki-next-header))
    (define-key map [prev-header]
      '("Previous header" . mediawiki-prev-header))
    (define-key map [separator-header] '("--"))
    (define-key map [outline]
      '("Toggle Outline Mode..." . outline-minor-mode))

    (modify-syntax-entry ?< "(>" mediawiki-mode-syntax-table)
    (modify-syntax-entry ?> ")<" mediawiki-mode-syntax-table)

    (define-key mediawiki-mode-map "\M-n" 'mediawiki-next-header)
    (define-key mediawiki-mode-map "\C-c\C-n" 'mediawiki-next-long-line)
    (define-key mediawiki-mode-map "\M-p" 'mediawiki-prev-header)
    (define-key mediawiki-mode-map [(meta down)] 'mediawiki-next-header)
    (define-key mediawiki-mode-map [(meta up)]   'mediawiki-prev-header)
    (define-key mediawiki-mode-map "\C-j" 'mediawiki-terminate-paragraph)

    (define-key mediawiki-mode-map "\C-c\C-q" 'mediawiki-unfill-article)
    (define-key mediawiki-mode-map "\C-c\M-q" 'mediawiki-fill-article)
    (define-key mediawiki-mode-map "\C-c\M-u" 'mediawiki-unfill-paragraph-or-region)
    (define-key mediawiki-mode-map "\C-c\C-u" 'mediawiki-unfill-paragraph-simple)
    (define-key mediawiki-mode-map "\C-c\C-f\C-s" 'mediawiki-insert-strong-emphasis)
    (define-key mediawiki-mode-map "\C-c\C-f\C-b" 'mediawiki-insert-bold)
    (define-key mediawiki-mode-map "\C-c\C-f\C-i" 'mediawiki-insert-italics)
    (define-key mediawiki-mode-map "\C-c\C-f\C-e" 'mediawiki-insert-header)
    (define-key mediawiki-mode-map "\C-c\C-f\C-l" 'mediawiki-insert-link)
    (define-key mediawiki-mode-map "\C-c\C-f\C-u" 'mediawiki-insert-user)
    (define-key mediawiki-mode-map "\C-c\C-f\C-q" 'mediawiki-insert-quotation)
    (define-key mediawiki-mode-map "\C-c\C-f\C-v" 'mediawiki-insert-bible-verse-template)
    (define-key mediawiki-mode-map "\C-c\C-w" 'mediawiki-insert-signature)
    (define-key mediawiki-mode-map "\C-c\C-l" 'mediawiki-insert-hline)
    (define-key mediawiki-mode-map [(meta f7)] 'mediawiki-draft)
    (define-key mediawiki-mode-map [(meta f8)] 'mediawiki-reply-at-point-simple)
    (define-key mediawiki-mode-map [(meta f9)] 'mediawiki-draft-view-draft)
    (define-key mediawiki-mode-map "\C-c\C-r" 'mediawiki-reply-at-point-simple)
    (define-key mediawiki-mode-map "\C-cr" 'mediawiki-draft-region)
    (define-key mediawiki-mode-map [(meta r)] 'mediawiki-draft-reply)
    (define-key mediawiki-mode-map "\C-c\C-m" 'mediawiki-draft)
    (define-key mediawiki-mode-map "\C-c\C-b" 'mediawiki-draft-region)
    (define-key mediawiki-mode-map "\C-c\C-d" 'mediawiki-draft-buffer)
    (define-key mediawiki-mode-map "\C-c\C-k" 'mediawiki-draft-buffer)
    (define-key mediawiki-mode-map "\C-c\C-p" 'mediawiki-draft-copy-page-to-register)
    (define-key mediawiki-mode-map "\C-c\C-c" 'mediawiki-draft-send)
    (define-key mediawiki-mode-map "\C-c\C-s" 'mediawiki-draft-yank-page-to-register)

    (define-key mediawiki-mode-map [(control meta prior)] 'mediawiki-enhance-indent)
    (define-key mediawiki-mode-map [(control meta next)] 'mediawiki-yank-prefix)
    (define-key mediawiki-mode-map [(meta return)] 'mediawiki-insert-enumerate)
    (define-key mediawiki-mode-map [(meta control return)] 'mediawiki-insert-enumerate-nonewline)
    ;; private setting
    (define-key mediawiki-mode-map [(shift return)] 'newline-and-indent)
    (define-key mediawiki-mode-map "\C-\\" 'mediawiki-insert-itemize)
    (define-key mediawiki-mode-map [(control return)] 'mediawiki-insert-itemize)
    (define-key mediawiki-mode-map "\C-ca" 'auto-capitalize-mode)
;    (define-key mediawiki-mode-map "\C-ci" 'set-input-method)
;    (define-key mediawiki-mode-map "\C-ct" 'toggle-input-method)

    (define-key mediawiki-mode-map [(backtab)] 'mediawiki-goto-prev-link)
    (define-key mediawiki-mode-map [(tab)]     'mediawiki-goto-next-link)
    (define-key mediawiki-mode-map "\M-g"      'mediawiki-reload)
    (define-key mediawiki-mode-map "\C-x\C-s"  'mediawiki-save)
    (define-key mediawiki-mode-map "\C-c\C-c"  'mediawiki-save-and-bury)
    (define-key mediawiki-mode-map "\C-x\C-w"  'mediawiki-save-as)
    (define-key mediawiki-mode-map "\C-c\C-o"  'mediawiki-open)
    (define-key mediawiki-mode-map "\M-p"
      'mediawiki-goto-previous-page)
    (define-key mediawiki-mode-map "\M-n"      'mediawiki-goto-next-page)
    (define-key mediawiki-mode-map [(control return)]
      'mediawiki-open-page-at-point)))

;; (defvar mw-pagelist-mode-map
;;   (let ((map (make-sparse-keymap)))
;;     (suppress-keymap map)
;;     (define-key map [(return)] 'mw-pl-goto-page-at-point)
;;     (define-key map "n"        'mw-pl-page-down)
;;     (define-key map "C-v"      'mw-pl-page-down)
;;     (define-key map [(next)]  'mw-pl-page-down)
;;     (define-key map "p"        'mw-pl-page-up)
;;     (define-key map "M-v"      'mw-pl-page-up)
;;     (define-key map [(prior)]  'mw-pl-page-up)))

;; (define-derived-mode mw-pagelist-mode special-mode "MW-PageList")

(provide 'mediawiki)

;; Local Variables:
;; time-stamp-pattern: "20/^;; Last Modified: <%%>$"
;; End:

;;; mediawiki.el ends here
