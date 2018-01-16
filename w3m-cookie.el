;;; w3m-cookie.el --- Functions for cookie processing

;; Copyright (C) 2002, 2003, 2005, 2006, 2008, 2009, 2010, 2017
;; TSUCHIYA Masatoshi <tsuchiya@namazu.org>

;; Authors: Teranishi Yuuichi  <teranisi@gohome.org>
;; Keywords: w3m, WWW, hypermedia

;; This file is a part of emacs-w3m.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This file contains the functions for cookies.  For more detail
;; about emacs-w3m, see:
;;
;;    http://emacs-w3m.namazu.org/

;; Reference for version 0 cookie:
;;	http://www.netscape.com/newsref/std/cookie_spec.html
;; Reference for version 1 cookie:
;;	http://www.ietf.org/rfc/rfc2965.txt
;;

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'w3m-util)
(require 'w3m)

(defvar w3m-cookies nil
  "A list of cookie elements.
Currently only browser local cookies are stored.")

;; Use `url-domsuf-cookie-allowed-p', if available (Emacs >= 24.3),
;; to check if a domain is unique to allow having cookies set.
(eval-and-compile (ignore-errors (require 'url-domsuf)))
(declare-function url-domsuf-cookie-allowed-p "url-domsuf")

(defconst w3m-cookie-two-dot-domains-regexp
  (concat "\\.\\(?:"
	  (mapconcat 'identity (list "com" "edu" "net" "org" "gov" "mil" "int")
		     "\\|")
	  "\\)$")
  "A regular expression of top-level domains that only require two dots
in the domain name in order to set a cookie.
This constant will never be used if url-domsuf.el(c) is available.")

(defcustom w3m-cookie-accept-domains nil
  "A list of trusted domain name string."
  :group 'w3m
  :type '(repeat (string :format "Domain name: %v\n")))

(defcustom w3m-cookie-reject-domains nil
  "A list of untrusted domain name string."
  :group 'w3m
  :type '(repeat (string :format "Domain name: %v\n")))

(defcustom w3m-cookie-accept-bad-cookies nil
  "If nil, don't accept bad cookies.
If t, accept bad cookies.
If ask, ask user whether accept bad cookies or not."
  :group 'w3m
  :type '(radio
	  (const :tag "Don't accept bad cookies" nil)
	  (const :tag "Ask accepting bad cookies" ask)
	  (const :tag "Always accept bad cookies" t)))

(defcustom w3m-cookie-save-cookies t
  "*Non-nil means save cookies when emacs-w3m cookie system shutdown."
  :group 'w3m
  :type 'boolean)

(defcustom w3m-cookie-file
  (expand-file-name ".cookie" w3m-profile-directory)
  "File in which cookies are kept."
  :group 'w3m
  :type 'file)

;;; Cookie accessor.
(defmacro w3m-cookie-url (cookie)
  "Return the url of COOKIE."
  `(aref ,cookie 0))
(defmacro w3m-cookie-domain (cookie)
  "Return the domain of COOKIE."
  `(aref ,cookie 1))
(defmacro w3m-cookie-secure (cookie)
  "Return whether COOKIE is secure."
  `(aref ,cookie 2))
(defmacro w3m-cookie-name (cookie)
  "Return the name of COOKIE."
  `(aref ,cookie 3))
(defmacro w3m-cookie-value (cookie)
  "Return the value of COOKIE."
  `(aref ,cookie 4))
(defmacro w3m-cookie-path (cookie)
  "Return the relative file path of COOKIE."
  `(aref ,cookie 5))
(defmacro w3m-cookie-version (cookie)
  "Return a version information of COOKIE."
  `(aref ,cookie 6))
(defmacro w3m-cookie-expires (cookie)
  "Return when COOKIE will expire."
  `(aref ,cookie 7))
(defmacro w3m-cookie-ignore (cookie)
  "Return t if COOKIE is marked to be ignored by emacs-w3m."
  `(aref ,cookie 8))

(defun w3m-cookie-create (&rest args)
  (let ((cookie (make-vector 9 nil)))
    (setf (w3m-cookie-url cookie)     (plist-get args :url))
    (setf (w3m-cookie-domain cookie)  (plist-get args :domain))
    (setf (w3m-cookie-secure cookie)  (plist-get args :secure))
    (setf (w3m-cookie-name cookie)    (plist-get args :name))
    (setf (w3m-cookie-value cookie)   (plist-get args :value))
    (setf (w3m-cookie-path cookie)    (plist-get args :path))
    (setf (w3m-cookie-version cookie) (or (plist-get args :version) 0))
    (setf (w3m-cookie-expires cookie) (plist-get args :expires))
    (setf (w3m-cookie-ignore cookie)  (plist-get args :ignore))
    cookie))

(defun w3m-cookie-store (cookie)
  "Store COOKIE."
  (let (ignored)
    (catch 'found
      (dolist (c w3m-cookies)
	(when (and (string= (w3m-cookie-domain c)
			    (w3m-cookie-domain cookie))
		   (string= (w3m-cookie-path c)
			    (w3m-cookie-path cookie))
		   (string= (w3m-cookie-name c)
			    (w3m-cookie-name cookie)))
	  (if (w3m-cookie-ignore c)
	      (setq ignored t)
	    (setq w3m-cookies (delq c w3m-cookies)))
	  (throw 'found t))))
    (unless ignored
      (push cookie w3m-cookies))))

(defun w3m-cookie-remove (domain path name)
  "Remove COOKIE if stored."
  (dolist (c w3m-cookies)
    (when (and (string= (w3m-cookie-domain c)
			domain)
	       (string= (w3m-cookie-path c)
			path)
	       (string= (w3m-cookie-name c)
			name))
      (setq w3m-cookies (delq c w3m-cookies)))))

(defun w3m-cookie-retrieve (host path &optional secure)
  "Retrieve cookies for DOMAIN and PATH."
  (let ((case-fold-search t)
	expires	cookies)
    (dolist (c w3m-cookies)
      (if (and (w3m-cookie-expires c)
	       (w3m-time-newer-p (current-time)
				 (w3m-time-parse-string
				  (w3m-cookie-expires c))))
	  (push c expires)
	(when (and (not (w3m-cookie-ignore c))
		   (or
		    ;; A special case that domain name is ".hostname".
		    (string= (concat "." host) (w3m-cookie-domain c))
		    (string-match (concat
				   (regexp-quote (w3m-cookie-domain c)) "$")
				  host))
		   (string-match (concat
				  "^" (regexp-quote (w3m-cookie-path c)))
				 path))
	  (if (w3m-cookie-secure c)
	      (if secure
		  (push c cookies))
	    (push c cookies)))))
    ;; Delete expired cookies.
    (dolist (expire expires)
      (setq w3m-cookies (delq expire w3m-cookies)))
    cookies))

;; HTTP URL parser.
(defun w3m-parse-http-url (url)
  "Parse an absolute HTTP URL."
  (let (secure split)
    (w3m-string-match-url-components url)
    (when (and (match-beginning 4)
	       (or (equal (match-string 2 url) "http")
		   (setq secure (equal (match-string 2 url) "https"))))
      (setq split (save-match-data
		    (split-string (match-string 4 url) ":")))
      (vector secure
	      (nth 0 split)
	      (string-to-number (or (nth 1 split) "80"))
	      (if (eq (length (match-string 5 url)) 0)
		  "/"
		(match-string 5 url))))))

(defsubst w3m-http-url-secure (http-url)
  "Secure flag of the HTTP-URL."
  (aref http-url 0))

(defsubst w3m-http-url-host (http-url)
  "Host name of the HTTP-URL."
  (aref http-url 1))

(defsubst w3m-http-url-port (http-url)
  "Port number of the HTTP-URL."
  (aref http-url 2))

(defsubst w3m-http-url-path (http-url)
  "Path of the HTTP-URL."
  (aref http-url 3))

;;; Cookie parser.
(defvar w3m-cookie-parse-args-syntax-table
  (copy-syntax-table emacs-lisp-mode-syntax-table)
  "A syntax table for parsing sgml attributes.")

(modify-syntax-entry ?' "\"" w3m-cookie-parse-args-syntax-table)
(modify-syntax-entry ?` "\"" w3m-cookie-parse-args-syntax-table)
(modify-syntax-entry ?{ "(" w3m-cookie-parse-args-syntax-table)
(modify-syntax-entry ?} ")" w3m-cookie-parse-args-syntax-table)

(defun w3m-cookie-parse-args (str &optional nodowncase)
  (let (name value results name-pos val-pos)
    (with-current-buffer (get-buffer-create " *w3m-cookie-parse-temp*")
      (erase-buffer)
      (set-syntax-table w3m-cookie-parse-args-syntax-table)
      (insert str)
      (goto-char (point-min))
      (while (not (eobp))
	(skip-chars-forward "; \n\t")
	(setq name-pos (point))
	(skip-chars-forward "^ \n\t=;")
	(unless nodowncase
	  (downcase-region name-pos (point)))
	(setq name (buffer-substring name-pos (point)))
	(skip-chars-forward " \t\n")
	(if (/= (or (char-after (point)) 0)  ?=) ; There is no value
	    (setq value nil)
	  (skip-chars-forward " \t\n=")
	  (setq val-pos (point)
		value
		(cond
		 ((or (= (or (char-after val-pos) 0) ?\")
		      (= (or (char-after val-pos) 0) ?'))
		  (buffer-substring (1+ val-pos)
				    (condition-case ()
					(prog2
					    (forward-sexp 1)
					    (1- (point))
					  (skip-chars-forward "\""))
				      (error
				       (skip-chars-forward "^ \t\n")
				       (point)))))
		 (t
		  (buffer-substring val-pos
				    (progn
				      (skip-chars-forward "^;")
				      (skip-chars-backward " \t")
				      (point)))))))
	(push (cons name value) results)
	(skip-chars-forward "; \n\t"))
      (nreverse results))))

(defun w3m-cookie-trusted-host-p (host)
  "Returns non-nil when the HOST is specified as trusted by user."
  (let ((accept w3m-cookie-accept-domains)
	(reject w3m-cookie-reject-domains)
	(trusted t)
	regexp tlen rlen)
    (while accept
      (cond
       ((string= (car accept) ".")
	(setq regexp ".*"))
       ((string= (car accept) ".local")
	(setq regexp "^[^\\.]+$"))
       ((eq (string-to-char (car accept)) ?.)
	(setq regexp (concat (regexp-quote (car accept)) "$")))
       (t (setq regexp (concat "^" (regexp-quote (car accept)) "$"))))
      (when (string-match regexp host)
	(setq tlen (length (car accept))
	      accept nil))
      (pop accept))
    (while reject
      (cond
       ((string= (car reject) ".")
	(setq regexp ".*"))
       ((string= (car reject) ".local")
	(setq regexp "^[^\\.]+$"))
       ((eq (string-to-char (car reject)) ?.)
	(setq regexp (concat (regexp-quote (car reject)) "$")))
       (t (setq regexp (concat "^" (regexp-quote (car reject)) "$"))))
      (when (string-match regexp host)
	(setq rlen (length (car reject))
	      reject nil))
      (pop reject))
    (if tlen
	(if rlen
	    (if (<= tlen rlen)
		(setq trusted nil)))
      (if rlen
	  (setq trusted nil)))
    trusted))

;;; Version 0 cookie.
(defun w3m-cookie-1-acceptable-p (host domain)
  (cond
   ((string= host domain)		; Apparently netscape lets you do this
    t)
   ;; A special case that domain name is ".hostname".
   ((string= (concat "." host) domain)
    t)
   ((fboundp 'url-domsuf-cookie-allowed-p)
    (url-domsuf-cookie-allowed-p (if (eq (aref domain 0) ?.)
				     (substring domain 1)
				   domain)))
   ((let ((case-fold-search t) (numdots 0) last)
      (while (setq last (string-match "\\." domain last))
	(setq numdots (1+ numdots)
	      last (1+ last)))
      (>= numdots			; We have enough dots in domain name
	  (if (string-match w3m-cookie-two-dot-domains-regexp domain) 2 3)))
    ;; Need to check and make sure the host is actually _in_ the
    ;; domain it wants to set a cookie for though.
    (string-match (concat (regexp-quote domain) "$") host))
   (t
    nil)))

(defun w3m-cookie-1-set (url &rest args)
  ;; Set-Cookie:, version 0 cookie.
  (let ((http-url (w3m-parse-http-url url))
	(case-fold-search t)
	secure domain expires max-age path cookie)
    (when http-url
      (setq secure (and (w3m-assoc-ignore-case "secure" args) t)
	    domain (or (cdr-safe (w3m-assoc-ignore-case "domain" args))
		       (w3m-http-url-host http-url))
	    expires (cdr-safe (w3m-assoc-ignore-case "expires" args))
	    max-age (cdr-safe (w3m-assoc-ignore-case "max-age" args))
	    path (or (cdr-safe (w3m-assoc-ignore-case "path" args))
		     (file-name-directory
		      (w3m-http-url-path http-url)))
	    cookie (car args))
      ;; Convert Max-Age to Expires
      (and max-age
	   (setq max-age
		 (ignore-errors
		   (format-time-string "%a %b %d %H:%M:%S %Y GMT"
				       (time-add nil (read max-age))
				       t)))
	   (setq expires max-age))
      (cond
       ((not (w3m-cookie-trusted-host-p (w3m-http-url-host http-url)))
	;; The site was explicity marked as untrusted by the user
	nil)
       ((or (w3m-cookie-1-acceptable-p (w3m-http-url-host http-url) domain)
	    (eq w3m-cookie-accept-bad-cookies t)
	    (and (eq w3m-cookie-accept-bad-cookies 'ask)
		 (y-or-n-p (format "Accept bad cookie from %s for %s? "
				   (w3m-http-url-host http-url) domain))))
	;; Cookie is accepted by the user, and passes our security checks

	;; If a CGI script wishes to delete a cookie, it can do so by
	;; returning a cookie with the same name, and an expires time
	;; which is in the past.
	(when (and expires
		   (w3m-time-newer-p (current-time)
				     (w3m-time-parse-string expires)))
	  (w3m-cookie-remove domain path (car cookie)))
	(w3m-cookie-store
	 (w3m-cookie-create :url url
			    :domain domain
			    :name (car cookie)
			    :value (cdr cookie)
			    :path path
			    :expires expires
			    :secure secure)))
       (t
	(message "%s tried to set a cookie for domain %s - rejected."
		 (w3m-http-url-host http-url) domain))))))

;;; Version 1 cookie.
(defun w3m-cookie-2-acceptable-p (http-url domain)
  ;;   A user agent rejects (SHALL NOT store its information) if the Version
  ;;   attribute is missing.  Moreover, a user agent rejects (SHALL NOT
  ;;   store its information) if any of the following is true of the
  ;;   attributes explicitly present in the Set-Cookie2 response header:

  ;;      *  The value for the Path attribute is not a prefix of the
  ;;         request-URI.

  ;;      *  The value for the Domain attribute contains no embedded dots,
  ;;         and the value is not .local.

  ;;      *  The effective host name that derives from the request-host does
  ;;         not domain-match the Domain attribute.

  ;;      *  The request-host is a HDN (not IP address) and has the form HD,
  ;;         where D is the value of the Domain attribute, and H is a string
  ;;         that contains one or more dots.

  ;;      *  The Port attribute has a "port-list", and the request-port was
  ;;         not in the list.
  )

(defun w3m-cookie-2-set (url &rest args)
  ;; Set-Cookie2:, version 1 cookie.
  ;; Not implemented yet.
  )


;;; Save & Load
(defvar w3m-cookie-init nil)

(defun w3m-cookie-clear ()
  "Clear cookie list."
  (interactive)
  (setq w3m-cookies nil)
  (dolist (buffer (w3m-list-buffers t))
    (with-current-buffer buffer
      (when (equal w3m-current-url "about://cookie/")
	(let ((w3m-message-silent t))
	  (w3m-reload-this-page nil t))))))

(defun w3m-cookie-save (&optional domain)
  "Save cookies.
When DOMAIN is non-nil, only save cookies whose domains match it."
  (interactive)
  (let (cookies)
    (dolist (cookie w3m-cookies)
      (when (and (or (not domain)
		     (string= (w3m-cookie-domain cookie) domain))
		 (w3m-cookie-expires cookie)
		 (w3m-time-newer-p (w3m-time-parse-string
				    (w3m-cookie-expires cookie))
				   (current-time)))
	(push cookie cookies)))
    (w3m-save-list w3m-cookie-file cookies)))

(defun w3m-cookie-save-current-site-cookies ()
  "Save cookies for the current site."
  (interactive)
  (when (and w3m-current-url
	     (not (w3m-url-local-p w3m-current-url)))
    (w3m-string-match-url-components w3m-current-url)
    (w3m-cookie-save (match-string 4 w3m-current-url))))

(defun w3m-cookie-load ()
  "Load cookies."
  (when (null w3m-cookies)
    (setq w3m-cookies
	  (w3m-load-list w3m-cookie-file))))

(defun w3m-cookie-setup ()
  "Setup cookies. Returns immediataly if already initialized."
  (interactive)
  (unless w3m-cookie-init
    (w3m-cookie-load)
    (setq w3m-cookie-init t)))

;;;###autoload
(defun w3m-cookie-shutdown (&optional interactive-p)
  "Save cookies, and reset cookies' data."
  (interactive (list t))
  ;; Don't error out no matter what happens
  ;; since `kill-emacs-hook' runs this function.
  (condition-case err
      (progn
	(when w3m-cookie-save-cookies
	  (w3m-cookie-save))
	(setq w3m-cookie-init nil)
	(w3m-cookie-clear)
	(if (get-buffer " *w3m-cookie-parse-temp*")
	    (kill-buffer (get-buffer " *w3m-cookie-parse-temp*"))))
    (error
     (if interactive-p
	 (signal (car err) (cdr err))
       (message "Error while running w3m-cookie-shutdown: %s"
		(error-message-string err))))))

(add-hook 'kill-emacs-hook 'w3m-cookie-shutdown)

;;;###autoload
(defun w3m-cookie-set (url beg end)
  "Register cookies which correspond to URL.
BEG and END should be an HTTP response header region on current buffer."
  (w3m-cookie-setup)
  (when (and url beg end)
    (save-excursion
      (let ((case-fold-search t)
	    (version 0)
	    data)
	(goto-char beg)
	(while (re-search-forward
		"^\\(?:Set-Cookie\\(2\\)?:\\) *\\(.*\\(?:\n[ \t].*\\)*\\)\n"
		end t)
	  (setq data (match-string 2))
	  (if (match-beginning 1)
	      (setq version 1))
	  (apply
	   (case version
	     (0 'w3m-cookie-1-set)
	     (1 'w3m-cookie-2-set))
	   url (w3m-cookie-parse-args data 'nodowncase)))))))

;;;###autoload
(defun w3m-cookie-get (url)
  "Get a cookie field string which corresponds to the URL."
  (w3m-cookie-setup)
  (let* ((http-url (w3m-parse-http-url url))
	 (cookies (and http-url
		       (w3m-cookie-retrieve (w3m-http-url-host http-url)
					    (w3m-http-url-path http-url)
					    (w3m-http-url-secure http-url))))
	 value)
    ;; When sending cookies to a server, all cookies with a more specific path
    ;; mapping should be sent before cookies with less specific path mappings.
    (setq cookies (sort cookies
			(lambda (x y)
			  (< (length (w3m-cookie-path x))
			     (length (w3m-cookie-path y))))))
    (when cookies
      (mapconcat (lambda (cookie)
		   (if (setq value (w3m-cookie-value cookie))
		       (concat (w3m-cookie-name cookie) "=" value)
		     (w3m-cookie-name cookie)))
		 cookies
		 "; "))))

;;;###autoload
(defun w3m-cookie (&optional no-cache)
  "Display cookies and enable you to manage them."
  (interactive "P")
  (unless w3m-use-cookies
    (when (y-or-n-p "Use of cookies is currently disable.  Enable? ")
      (setq w3m-use-cookies t)))
  (when w3m-use-cookies
    (w3m-goto-url-new-session "about://cookie/" no-cache)))

;;;###autoload
(defun w3m-about-cookie (url &optional no-decode no-cache post-data &rest args)
  "Make the html contents to display and to enable you to manage cookies.
To delete all cookies associated with amazon.com for example, do it in
the following two steps:

1. Mark them `unused' (type `C-c C-c' or press any OK button).

Limit to [amazon.com          ] <= [ ]regexp  [OK]
( )Noop  ( )Use all  (*)Unuse all  ( )Delete unused all  [OK]

2. Delete cookies that are marked `unused'.

Limit to [amazon.com          ] <= [ ]regexp  [OK]
( )Noop  ( )Use all  ( )Unuse all  (*)Delete unused all  [OK]

You can mark cookies on the one-by-one basis of course.  The `Limit-to'
string is case insensitive and allows a regular expression."
  (w3m-cookie-setup)
  (let ((case-fold-search t)
	(pos 0)
	;; The car is a string used to limit cookies to the ones matching,
	;; and the cdr is a boolean flag that specifies whether the string
	;; is a regexp or not.
	(match '(nil . nil))
	delete dels cookies regexp)
    (when post-data
      (dolist (pair (split-string post-data "&"))
	(setq pair (split-string pair "="))
	(w3m-static-if (fboundp 'pcase)
	    (pcase (car pair)
	      ("delete" (setq delete (cadr pair)))
	      ("re-search" (setcdr match t))
	      ("search" (setcar match (replace-regexp-in-string
				       "[\n\r].*" ""
				       (w3m-url-decode-string (cadr pair)))))
	      (_ (when (equal (cadr pair) "0")
		   (push (string-to-number (car pair)) dels))))
	  (cond ((equal "delete" (car pair)) (setq delete (cadr pair)))
		((equal "re-search" (car pair)) (setcdr match t))
		((equal "search" (car pair))
		 (setcar match (replace-regexp-in-string
				"[\n\r].*" ""
				(w3m-url-decode-string (cadr pair)))))
		(t (when (equal (cadr pair) "0")
		     (push (string-to-number (car pair)) dels)))))))
    (if (zerop (length (car match)))
	(setq match nil
	      cookies w3m-cookies)
      (setq regexp (car match))
      (unless (cdr match)
	(setq regexp (regexp-quote regexp)))
      (dolist (cookie w3m-cookies)
	(when (string-match regexp (w3m-cookie-url cookie))
	  (push cookie cookies)))
      (setq cookies (nreverse cookies)))
    (w3m-static-if (fboundp 'pcase)
	(pcase delete
	  ("0" (dolist (del dels)
		 (setf (w3m-cookie-ignore (nth del cookies)) t)))
	  ("1" (dolist (cookie cookies)
		 (setf (w3m-cookie-ignore cookie) nil)))
	  ("2" (dolist (cookie cookies)
		 (setf (w3m-cookie-ignore cookie) t)))
	  ("3" (progn
		 (dolist (del dels)
		   (setf (w3m-cookie-ignore (nth del cookies)) t))
		 (dolist (cookie cookies)
		   (when (w3m-cookie-ignore cookie)
		     (setq cookies (delq cookie cookies)
			   w3m-cookies (delq cookie w3m-cookies)))))))
      (cond ((equal "0" delete)
	     (dolist (del dels)
	       (setf (w3m-cookie-ignore (nth del cookies)) t)))
	    ((equal "1" delete)
	     (dolist (cookie cookies)
	       (setf (w3m-cookie-ignore cookie) nil)))
	    ((equal "2" delete)
	     (dolist (cookie cookies)
	       (setf (w3m-cookie-ignore cookie) t)))
	    ((equal "3" delete)
	     (dolist (del dels)
	       (setf (w3m-cookie-ignore (nth del cookies)) t))
	     (dolist (cookie cookies)
	       (when (w3m-cookie-ignore cookie)
		 (setq cookies (delq cookie cookies)
		       w3m-cookies (delq cookie w3m-cookies)))))))
    (insert
     (concat ;; Allow nil values in operand.
      "<html><head><title>Cookies</title></head>
<body><center><b>Cookies</b></center>
<form method=\"post\" action=\"about://cookie/\">
<p><table><tr><td>Limit to <input type=\"text\" name=\"search\" value=\""
      (car match)
      "\">&nbsp;&lt;=&nbsp;<input type=checkbox name=\"re-search\""
      (when (cdr match) " checked")
      ">regexp&nbsp;<input type=submit value=\"OK\"></td></tr>
<tr><td><input type=radio name=\"delete\" value=0 checked>Noop&nbsp;
<input type=radio name=\"delete\" value=1>Use all&nbsp;
<input type=radio name=\"delete\" value=2>Unuse all&nbsp;
<input type=radio name=\"delete\" value=3>Delete unused all&nbsp;
<input type=submit value=\"OK\"></td></tr></table></p>
<ol>"))
    (dolist (cookie cookies)
      (insert
       (concat ;; Allow nil values in operand.
	"<p><li><h1><a href=\""
	(w3m-cookie-url cookie)
	"\">"
	(w3m-cookie-url cookie)
	"</a></h1>"
	"<table cellpadding=0>"
	"<tr><td width=\"80\"><b>Cookie:</b></td><td><nobr>"
	(w3m-cookie-name cookie) "=" (or (w3m-cookie-value cookie) "(no value)")
	"</nobr></td></tr>"
	(when (w3m-cookie-expires cookie)
	  (concat "<tr><td width=\"80\"><b>Expires:</b></td><td>"
		  (w3m-cookie-expires cookie)
		  "</td></tr>"))
	"<tr><td width=\"80\"><b>Version:</b></td><td>"
	(number-to-string (w3m-cookie-version cookie))
	"</td></tr>"
	(when (w3m-cookie-domain cookie)
	  (concat "<tr><td width=\"80\"><b>Domain:</b></td><td>"
		  (w3m-cookie-domain cookie)
		  "</td></tr>"))
	(when (w3m-cookie-path cookie)
	  (concat "<tr><td width=\"80\"><b>Path:</b></td><td>"
		  (w3m-cookie-path cookie)
		  "</td></tr>"))
	"<tr><td width=\"80\"><b>Secure:</b></td><td>"
	(if (w3m-cookie-secure cookie) "Yes" "No")
	"</td></tr><tr><td width=\"80\"><b>Use:</b></td><td>"
	(format "<input type=radio name=\"%d\" value=1%s>Yes"
		pos (if (w3m-cookie-ignore cookie) "" " checked"))
	"&nbsp;&nbsp;"
	(format "<input type=radio name=\"%d\" value=0%s>No"
		pos (if (w3m-cookie-ignore cookie) " checked" ""))
	"&nbsp;&nbsp;"
	"<input type=submit value=\"OK\"></td></tr></table>"))
      (setq pos (1+ pos)))
    (insert "</ol></form></body></html>")
    "text/html"))

(provide 'w3m-cookie)

;;; w3m-cookie.el ends here
