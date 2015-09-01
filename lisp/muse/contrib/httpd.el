;;; httpd.el -- a web server in Emacs Lisp
;;;
;;; Author: Eric Marsden <emarsden@laas.fr>
;;;         John Wiegley <johnw@gnu.org>
;;;         Michael Olson <mwolson@gnu.org> (slight modifications)
;;; Version: 1.1
;;; Keywords: games
;;; Copyright (C) 2001, 2003 Eric Marsden
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
;; The latest version of this package should be available from
;;
;;     <URL:http://purl.org/net/emarsden/home/downloads/>

;;; Commentary:
;;
;; httpd.el is an HTTP server embedded in the Emacs. It can handle GET
;; and HEAD requests; adding support for POST should not be too
;; difficult.  By default, httpd.el will listen on server side Emacs
;; sockets for HTTP requests.
;;
;; I have only tested this code with Emacs; it may need modifications
;; to work with XEmacs.
;;
;; This version has been modified to work with GNU Emacs 21 and 22.
;;
;;; Acknowledgements:
;;
;; httpd.el was inspired by pshttpd, an HTTP server written in
;; Postscript by Anders Karlsson <URL:http://www.pugo.org:8080/>.
;;
;; Thanks to John Wiegley and Cyprian Adam Laskowski.

;;; Code

(defvar httpd-document-root "/var/www")

(defvar httpd-path-handlers '()
  "Alist of (path-regexp . handler) forms.
If a GET request is made for an URL whose path component matches
a PATH-REGEXP, the corresponding handler is called to generate
content.")

(defvar httpd-mime-types-alist
  '(("html" . "text/html; charset=iso-8859-1")
    ("txt"  . "text/plain; charset=iso-8859-1")
    ("jpg"  . "image/jpeg")
    ("jpeg" . "image/jpeg")
    ("gif"  . "image/gif")
    ("png"  . "image/png")
    ("tif"  . "image/tiff")
    ("tiff" . "image/tiff")
    ("css"  . "text/css")
    ("gz"   . "application/octet-stream")
    ("ps"   . "application/postscript")
    ("pdf"  . "application/pdf")
    ("eps"  . "application/postscript")
    ("tar"  . "application/x-tar")
    ("rpm"  . "application/x-rpm")
    ("zip"  . "application/zip")
    ("mp3"  . "audio/mpeg")
    ("mp2"  . "audio/mpeg")
    ("mid"  . "audio/midi")
    ("midi" . "audio/midi")
    ("wav"  . "audio/x-wav")
    ("au"   . "audio/basic")
    ("ram"  . "audio/pn-realaudio")
    ("ra"   . "audio/x-realaudio")
    ("mpg"  . "video/mpeg")
    ("mpeg" . "video/mpeg")
    ("qt"   . "video/quicktime")
    ("mov"  . "video/quicktime")
    ("avi"  . "video/x-msvideo")))

(defun httpd-mime-type (filename)
  (or (cdr (assoc (file-name-extension filename) httpd-mime-types-alist))
      "text/plain"))

(put 'httpd-exception 'error-conditions '(httpd-exception error))

(defun defhttpd-exception (name code msg)
  (put name 'error-conditions (list name 'httpd-exception 'error))
  (put name 'httpd-code code)
  (put name 'httpd-msg msg))

(defhttpd-exception 'httpd-moved/perm       301 "Moved permanently")
(defhttpd-exception 'httpd-moved/temp       302 "Moved temporarily")
(defhttpd-exception 'httpd-bad-request      400 "Bad request")
(defhttpd-exception 'httpd-forbidden        403 "Forbidden")
(defhttpd-exception 'httpd-file-not-found   404 "Not found")
(defhttpd-exception 'httpd-method-forbidden 405 "Method not allowed")
(defhttpd-exception 'httpd-unimplemented    500 "Internal server error")
(defhttpd-exception 'httpd-unimplemented    501 "Not implemented")
(defhttpd-exception 'httpd-unimplemented    503 "Service unavailable")

(defvar httpd-endl "\r\n")

(defvar httpd-process nil)
(defvar httpd-bytes-sent nil)		; only used with `httpd-process'
(defvar httpd-log-accesses t)

(defun httpd-add-handler (path-regexp handler)
  (push (cons path-regexp handler) httpd-path-handlers))

(defun httpd-try-internal-handler (path &optional cont)
  (catch 'result
    (dolist (elem httpd-path-handlers)
      (let ((regexp (car elem))
	    (handler (cdr elem)))
	(if (string-match regexp path)
	    (throw 'result (funcall handler path cont)))))))

(defun httpd-date-stamp ()
  (format-time-string "[%d/%b/%Y %H:%M:%S %z]"))

(defun httpd-log (&rest strings)
  (if httpd-log-accesses
      (save-excursion
	(goto-char (point-max))
	(with-current-buffer (get-buffer-create "*httpd access_log*")
	  (mapc 'insert strings)))))

(defun httpd-send-data (&rest strings)
  (dolist (s strings)
    (send-string httpd-process s)
    (if httpd-bytes-sent
	(setq httpd-bytes-sent (+ httpd-bytes-sent (length s))))))

(defun httpd-send (code msg &rest strings)
  (httpd-log (number-to-string code) " ")
  (apply 'httpd-send-data
	 "HTTP/1.0 " (number-to-string code) " " msg httpd-endl
	 strings))

(defun httpd-send-eof ()
  (httpd-log (number-to-string httpd-bytes-sent) "\n")
  (process-send-eof httpd-process))

(defun httpd-send-file (filename)
  (with-temp-buffer
    (insert-file-contents filename)
    (httpd-send-data (buffer-string))))

(defun httpd-lose (code msg)
  (httpd-send code msg
	      "Content-Type: text/html" httpd-endl
	      "Connection: close" httpd-endl
	      httpd-endl
	      "<html><head><title>Error</title></head>" httpd-endl
	      "<body><h1>" msg "</h1>" httpd-endl
	      "<p>" msg httpd-endl
	      "</body></html>" httpd-endl)
  (httpd-send-eof))

(defun httpd-handle-redirect (req where)
  "Redirect the client to new location WHERE."
  (httpd-send 301 "Moved permanently"
	      "Location: " where httpd-endl
	      "URI: " where httpd-endl
	      "Connection: close" httpd-endl
	      httpd-endl)
  (httpd-send-eof))

(defun httpd-handle-GET+HEAD (path &optional want-data req)
  (if (zerop (length path))
      (setq path "index.html"))

  ;; could use `expand-file-name' here instead of `concat', but we
  ;; don't want tilde expansion, etc.
  (let ((filename (concat httpd-document-root "/" path))
	modified-since)
    (cond ((httpd-try-internal-handler path) t)
	  ((file-directory-p filename)
	   (httpd-handle-redirect path (concat "http://" (system-name) "/"
					       path "/")))
	  ((file-readable-p filename)
	   (let ((attrs (file-attributes filename)))
	     (if (and (string-match "^If-Modified-Since:\\s-+\\(.+\\)" req)
		      (setq modified-since
			    (apply 'encode-time
				   (parse-time-string (match-string 1 req))))
		      (time-less-p (nth 5 attrs) modified-since))
		   (httpd-send 304 "Not modified"
			       "Server: Emacs/httpd.el" httpd-endl
			       "Connection: close" httpd-endl
			       httpd-endl)
	       (httpd-send 200 "OK"
			   "Server: Emacs/httpd.el" httpd-endl
			   "Connection: close" httpd-endl
			   "MIME-Version: 1.0" httpd-endl
			   "Content-Type: "
			   (httpd-mime-type filename) httpd-endl
			   "Content-Length: "
			   (number-to-string (nth 7 attrs)) httpd-endl
			   httpd-endl)
	       (if want-data
		   (httpd-send-file filename)))
	     (httpd-send-eof)))

	  (t (signal 'httpd-file-not-found path)))))

(defun httpd-handle-request (req &optional cont)
  (httpd-log (car (process-contact httpd-process)) " - - "
	     (httpd-date-stamp) " \"")
  (if (not (string-match ".+" req))
      (progn
	(httpd-log "\"")
	(error "HTTP request was empty"))
    (let ((request (match-string 0 req)))
      (httpd-log request "\" ")
      (cond
       ((string-match "\\.\\." request)
	;; reject requests containing ".." in the path. Should really
	;; URI-decode first.
	(signal 'httpd-forbidden request))

       ((string-match "\\`\\(GET\\|HEAD\\|POST\\)\\s-/\\(\\S-*\\)" request)
	(let ((kind (match-string 1 request))
	      (arg  (match-string 2 request)))
	  (if (string= kind "POST")
	      (unless (httpd-try-internal-handler arg cont)
		(signal 'httpd-unimplemented arg))
	    (httpd-handle-GET+HEAD arg (string= kind "GET") req))))

       (t (signal 'httpd-bad-request request))))))

(defun httpd-serve (proc string)
  (let ((httpd-process proc)
	(httpd-bytes-sent 0))
    (condition-case why
	(httpd-handle-request string)
      (httpd-exception
       (httpd-lose (get (car why) 'httpd-code)
		   (get (car why) 'httpd-msg)))
      ;; Comment out these two lines if you want to catch errors
      ;; inside Emacs itself.
      (error
       (httpd-lose 500 (format "Emacs Lisp error: %s" why)))
      )))

(defun httpd-start (&optional port)
  (interactive (list (read-string "Serve Web requests on port: " "8080")))
  (if (null port)
      (setq port 8080)
    (if (stringp port)
	(setq port (string-to-number port))))
  (if httpd-process
      (delete-process httpd-process))
  (setq httpd-process
	(if (fboundp 'make-network-process)
	    (make-network-process :name "httpd"
				  :buffer (generate-new-buffer "httpd")
				  :host 'local :service port
				  :server t :noquery t
				  :filter 'httpd-serve)
	  (and (fboundp 'open-network-stream-server)
	       (open-network-stream-server "httpd"
					   (generate-new-buffer "httpd")
					   port nil 'httpd-serve))))
  (if (and (processp httpd-process)
	   (eq (process-status httpd-process) 'listen))
      (message "httpd.el is listening on port %d" port)))

(defun httpd-stop ()
  (interactive)
  (when httpd-process
    (message "httpd.el server on port %d has stopped"
	     (cadr (process-contact httpd-process)))
    (delete-process httpd-process)
    (setq httpd-process nil)))

(provide 'httpd)

;; httpd.el ends here
