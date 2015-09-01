;;; elnode.el --- a simple emacs async HTTP server -*- lexical-binding: t -*-

;; Copyright (C) 2010, 2011, 2012  Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Maintainer: Nic Ferrier <nferrier@ferrier.me.uk>
;; Created: 5th October 2010
;; Keywords: lisp, http, hypermedia

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This is an elisp version of the popular node.js asynchronous
;; webserver toolkit.
;;
;; You can define HTTP request handlers and start an HTTP server
;; attached to the handler.  Many HTTP servers can be started, each
;; must have it's own TCP port.  Handlers can defer processing with a
;; signal (which allows comet style resource management)
;;
;; See elnode-start for how to start an HTTP server.

;;; Source code
;;
;; elnode's code can be found here:
;;   http://github.com/nicferrier/elnode

;;; Style note
;;
;; This codes uses the Emacs style of:
;;
;;    elnode--private-function
;;
;; for private functions.


;;; Code:

(require 'mm-encode)
(require 'mailcap)
(require 'url-util)
(require 'json)
(eval-when-compile (require 'cl))

(defconst ELNODE-FORM-DATA-TYPE "application/x-www-form-urlencoded"
  "The type of HTTP Form POSTs.")

(defgroup elnode nil
  "An extensible asynchronous web server for Emacs."
  :group 'applications)

(defvar elnode-server-socket nil
  "Where we store the server sockets.

This is an alist of proc->server-process:

  (port . process)")


;; Error log handling

(defun elnode-trunc (data)
  "Truncate and clean DATA."
  (replace-regexp-in-string
   "[\r\n]" "."
   (substring data 0 (if (> 20 (length data)) (length data) 20))))

(defun elnode-trim (str)
  "Trim off whitespace."
  (string-match "[ \t\n\r]*$" str)
  (setq str (replace-match "" nil nil str))
  (string-match "^[ \t\n\r]*" str)
  (replace-match "" nil nil str))

(defcustom elnode-log-files-directory "~/.elnodelogs"
  "The directory to store any Elnode log files.

Elnode can use files for storing logs and will write them to this
directory.  If the directory does not exist it is created.  If
this field is left blank no log saving is done."
  :group 'elnode
  :type '(directory))

(defvar elnode-log-buffer-position-written 0
  "The position in the log buffer written.

This is used by `elnode-log-buffer-log' to track what has been written
so far.")

(defvar elnode-log-buffer-max-size 1000
  "Maximum number of lines of log.")

(defvar elnode-log-buffer-datetime-format "%Y%m%d%H%M%S"
  "The date time format used by `elnode-log-buffer-log'.")

(defun elnode-log-buffer-log (text buffer-or-name &optional filename)
  "Log TEXT to the BUFFER-OR-NAME saving the buffer in FILENAME.

BUFFER-OR-NAME is either a buffer or a string naming a buffer.
FILENAME is a filename to save the buffer into.  If the FILENAME
is not specified then we try to use the filename of the
BUFFER-OR-NAME.

If nether a buffer filename nor FILENAME is specified then an
error is generated.

The TEXT is logged with the current date and time formatted with
`elnode-log-buffer-datetime-format'."
  (let ((name (or filename (buffer-file-name (current-buffer)))))
    (if (not name)
        (error "Filename is required, or use a buffer with a filename"))
    (with-current-buffer (get-buffer-create buffer-or-name)
      (unless (assq
               'elnode-log-buffer-position-written
               (buffer-local-variables))
        (make-local-variable 'elnode-log-buffer-position-written)
        (setq elnode-log-buffer-position-written (make-marker))
        (set-marker elnode-log-buffer-position-written (point-min)))
      (save-excursion
        (goto-char (point-max))
        (insert
         (format
          "%s: %s\n"
          (format-time-string elnode-log-buffer-datetime-format)
          text))
        (if (not (file-exists-p (file-name-directory name)))
            (make-directory (file-name-directory name) t))
        (append-to-file elnode-log-buffer-position-written (point-max) name)
        (set-marker elnode-log-buffer-position-written (point-max))
        ;; Truncate the file if it's grown too large
        (goto-char (point-max))
        (forward-line (- elnode-log-buffer-max-size))
        (beginning-of-line)
        (delete-region (point-min) (point))))))

(defcustom elnode-error-log-to-messages t
  "Wether to send elnode logging through the messaging system."
  :group 'elnode
  :type '(boolean))

(defvar elnode-server-error-log "*elnode-server-error*"
  "The buffer where error log messages are sent.")

(defvar elnode--do-error-logging t
  "Allows tests to turn off error logging.")

(defun elnode--get-error-log-buffer ()
  "Returns the buffer for the error-log."
  (get-buffer-create elnode-server-error-log))

(defun elnode-error (msg &rest args)
  "Log MSG with ARGS as an error.

This function is available for handlers to call.  It is also used
by elnode iteslf.

There is only one error log, in the future there may be more."
  (when elnode--do-error-logging
    (let ((filename (elnode--log-filename "elnode-error"))
          (fmtmsg (apply 'format `(,msg ,@args))))
      (elnode-log-buffer-log
       fmtmsg
       (elnode--get-error-log-buffer)
       filename)
      (when elnode-error-log-to-messages
        (message "elnode-error: %s" fmtmsg)))))

(defun elnode--log-filename (logname)
  "Turn LOGNAME into a filename.

`elnode-log-files-directory' is used as the container for log files.

This function mainly exists to make testing easier."
  (expand-file-name
   (format "%s/%s"
           elnode-log-files-directory
           logname)))

(defun elnode-log-access (logname httpcon)
  "Log the HTTP access in buffer LOGNAME.

This function is available for handlers to call.  It is also used
by elnode iteslf."
  (let ((elnode-log-buffer-datetime-format "%Y-%m-%d-%H:%M:%S")
        (buffer-name (format "*%s-elnode-access*" logname))
        (filename (elnode--log-filename logname)))
    (elnode-log-buffer-log
     (format "%s % 6d %s %s\n"
             (process-get httpcon :elnode-httpresponse-status)
             (or (process-get httpcon :elnode-bytes-written) 0)
             (elnode-http-method httpcon)
             (elnode-http-pathinfo httpcon))
     buffer-name
     filename)))


;; Defer stuff

(progn
  ;; Sets up the elnode defer signal
  (put 'elnode-defer 'error-conditions '(elnode-defer)))

(defvar elnode--deferred '()
  "List of deferred pairs: (socket . handler).")

(defun elnode-defer-now (handler)
  "The function you call to defer processing of the current socket.

Pass in the current HANDLER.

FIXME: We could capture the current handler somehow? I think the
point is that whatever signals elnode-defer should be getting
control back when the deferred is re-processed."
  (signal 'elnode-defer handler))

(defmacro elnode-defer-or-do (guard &rest body)
  "Test GUARD and defer if it succeeds and BODY if it doesn't.

`httpcon' is captured in this macro which means the macro can
only be expanded where there is an inscope `httpcon'."
  (declare (indent defun))
  (let ((bv (make-symbol "bv")))
    `(let ((,bv (lambda (httpcon) ,@body)))
       (if ,guard
           (elnode-defer-now ,bv)
         (progn
           (funcall ,bv httpcon))))))

(defun elnode--deferred-add (httpcon handler)
  "Add the specified HTTPCON/HANDLER pair to the deferred list."
  (elnode-error "deferred-add: adding a defer for %s" httpcon)
  (push (cons httpcon handler) elnode--deferred))

(defun elnode--deferred-processor ()
  "Process the deferred queue."
  (let ((new-deferred (list)))
    (loop for pair in elnode--deferred
          do
          (let ((httpcon (car pair))
                (handler (cdr pair)))
            (elnode-error "elnode-deferred handling %s %s" httpcon handler)
            (condition-case signal-value
                (funcall handler httpcon)
              ('elnode-defer
               (push
                (cons httpcon (cdr signal-value))
                new-deferred))
              (error
               (elnode-error
                "elnode-deferred found an error processing %s" httpcon)))))
    ;; Set the correct queue
    (setq elnode--deferred new-deferred)))


(defvar elnode--defer-timer nil
  "The timer used by the elnode defer processing.

This is initialized by `elnode--init-deferring'.")

(defun elnode--init-deferring ()
  "Initialize elnode defer processing.

Necessary for running comet apps."
  (setq elnode--defer-timer
        (run-with-idle-timer 0.1 't 'elnode--deferred-processor)))

(defun elnode-deferred-queue (arg)
  "Message the length of the deferred queue."
  (interactive "P")
  (if (not arg)
      (message
       "elnode deferred queue: %d %s"
       (length elnode--deferred)
       elnode--defer-timer)
    (setq elnode--deferred (list))
    (message "elnode deferred queue reset!")))

(defun elnode-deferred-queue-stop ()
  "Stop any running deferred queue processor."
  (interactive)
  (when elnode--defer-timer
    (cancel-timer elnode--defer-timer)
    (setq elnode--defer-timer nil)))

;;; Basic response mangling

(defcustom elnode-default-response-table
  '((201 . "Created")
    (400 . "Bad request")
    (404 . "Not found")
    (500 . "Server error")
    (t . "Ok"))
  "The status code -> default message mappings.

When Elnode sends a default response these are the text used.

Alter this if you want to change the messages that Elnode sends
with the following functions:

 'elnode-send-400'
 'elnode-send-404'
 'elnode-send-500'

The function `elnode-send-status' also uses these."
  :group 'elnode
  :type '(alist :key-type integer
                :value-type string))

(defun elnode--format-response (status &optional msg)
  "Format the STATUS and optionally MESSAGE as an HTML return."
  (format "<h1>%s</h1>%s\r\n"
          (cdr (or (assoc status elnode-default-response-table)
                   (assoc t elnode-default-response-table)))
          (if msg (format "<p>%s</p>" msg) "")))


;; Main control functions

(defun elnode--sentinel (process status)
  "Sentinel function for the main server and for the client sockets."
  (elnode-error
   "elnode--sentinel %s for process  %s"
   (elnode-trunc status)
   (process-name process))
  (cond
   ;; Server status
   ((and
     (assoc (process-contact process :service) elnode-server-socket)
     (equal status "deleted\n"))
    (kill-buffer (process-buffer process))
    (elnode-error "Elnode server stopped"))

   ;; Client socket status
   ((equal status "connection broken by remote peer\n")
    (if (process-buffer process)
        (progn
          (kill-buffer (process-buffer process))
          (elnode-error "Elnode connection dropped %s" process))))

   ((equal status "open\n") ;; this says "open from ..."
    (elnode-error "Elnode opened new connection"))

   ;; Default
   (t
    (elnode-error "Elnode status: %s %s" process (elnode-trim status)))))

(defun elnode--process-send-string (proc data)
  "Elnode adapter for `process-send-string'.

Sends DATA to the HTTP connection PROC (which is an HTTP
connection) using `elnode-http-send-string'.

This is used by `elnode-worker-elisp' to implement a protocol for
sending data through an elnode connection transparently."
  (elnode-http-send-string proc data))

(defun elnode--process-send-eof (proc)
  "Elnode adapter for `process-send-eof'.

Sends EOF to the HTTP connection PROC (which is an HTTP
connection) in a way that chunked encoding is endeed properly.

This is used by `elnode-worker-elisp' to implement a protocol for
sending data through an elnode connection transparently."
  (elnode-error "elnode--process-send-eof on %s" proc)
  (elnode-http-send-string proc "")
  (process-send-string proc "\r\n")
  (elnode--http-end proc))

(defun elnode--http-parse (httpcon)
  "Parse the HTTP header for the process.

If the request is not fully complete (if the header has not
arrived yet or we don't have all the content-length yet for
example) this can throw `elnode-parse-http'.  The thing being
waited for is indicated.

Important side effects of this function are to add certain
process properties to the HTTP connection.  These are the result
of succesful parsing."
  (with-current-buffer (process-buffer httpcon)
    (save-excursion
      (goto-char (point-min))
      (let ((hdrend (re-search-forward "\r\n\r\n" nil 't)))
        (when (not hdrend)
          (throw 'elnode-parse-http 'header))
        ;; FIXME: we don't handle continuation lines of anything like
        ;; that
        (let* ((lines
                (split-string
                 (buffer-substring (point-min) hdrend)
                 "\r\n"
                 't))
               (status (car lines)) ;; the first line is the status line
               (header (cdr lines)) ;; the rest of the lines are the header
               (header-alist-strings
                (mapcar
                 (lambda (hdrline)
                   (if (string-match "\\([A-Za-z0-9_-]+\\): \\(.*\\)" hdrline)
                       (cons
                        (match-string 1 hdrline)
                        (match-string 2 hdrline))))
                 header))
               (header-alist-syms
                (mapcar
                 (lambda (hdr)
                   (cons (intern (downcase (car hdr)))
                         (cdr hdr)))
                 header-alist-strings))
               (content-len (assq 'content-length header-alist-syms)))
          ;; Check the content if we have it.
          (when content-len
            (let* ((available-content (- (point-max) hdrend)))
              (when (> (string-to-number (cdr content-len))
                       available-content)
                (throw 'elnode-parse-http 'content))))
          (process-put httpcon :elnode-header-end hdrend)
          (process-put httpcon :elnode-http-status status)
          (process-put httpcon :elnode-http-header-syms header-alist-syms)
          (process-put httpcon :elnode-http-header header-alist-strings)))))
  ;; Return a symbol to indicate done-ness
  'done)

(defun elnode--http-make-hdr (method resource &rest headers)
  "Convenience function to make an HTTP header.

METHOD is the method to use.  RESOURCE is the path to use.
HEADERS should be pairs of strings indicating the header values:

 (elnode--http-make-hdr 'get \"/\" '(host . \"localhost\"))

Where symbols are encountered they are turned into strings.
Inside headers they are capitalized.

A header pair with the key `body' can be used to make a content body:

 (elnode--http-make-hdr 'get \"/\" '(body . \"some text\"))
 =>
 GET / HTTP/1.1

 some text

No other transformations are done on the body, no content type
added or content length computed."
  (let (body)
    (format "%s %s HTTP/1.1\r\n%s\r\n%s"
            (upcase (if (symbolp method) (symbol-name method) method))
            resource
            (mapconcat
             (lambda (header)
               (let ((name (if (symbolp (car header))
                               (symbol-name (car header))
                             (car header))))
                 (if (not (equal name "body"))
                     (format "%s: %s\r\n"
                             (capitalize name)
                             (cdr header))
                   (setq body (cdr header))
                   "")))
             headers
             "")
            ;; If we have a body then add that as well
            (or body ""))))


(defun elnode--get-server-prop (process key)
  "Get the value of the KEY from the server attached to PROCESS.

Server properties are bound with `elnode-start' which sets up
`elnode--log-fn' to ensure that all sockets created have a link
back to the server."
  (let* ((server (process-get process :server))
         (value (process-get server key)))
    value))

(defun elnode--make-send-string ()
  "Make a function to send a string to an HTTP connection."
  (lambda (httpcon str)
    "Send STR to the HTTPCON.
Does any necessary encoding."
    (elnode--process-send-string httpcon str)))

(defun elnode--make-send-eof ()
  "Make a function to send EOF to an HTTP connection."
  (lambda (con)
    "Send EOF to the HTTPCON.
Does any necessary encoding."
    (elnode--process-send-eof con)))

(defun elnode--filter (process data)
  "Filtering DATA sent from the client PROCESS..

This does the work of finding and calling the user HTTP
connection handler for the request on PROCESS.

A buffer for the HTTP connection is created, uniquified by the
port number of the connection."
  (let ((buf
         (or
          (process-buffer process)
          ;; Set the process buffer (because the server doesn't
          ;; automatically allocate them)
          ;;
          ;; The name of the buffer has the client port in it
          ;; the space in the name ensures that emacs does not list it
          ;;
          ;; We also use this moment to setup functions required by
          ;; elnode-worker-lisp
          (let* ((port (cadr (process-contact process)))
                 (send-string-func (elnode--make-send-string))
                 (send-eof-func (elnode--make-send-eof)))
            (process-put
             process :send-string-function
             send-string-func)
            ;; ... and this one does closing the connection properly
            ;; with elnode's chunked encoding.
            (process-put
             process :send-eof-function
             send-eof-func)
            ;; Now do the buffer creation
            (set-process-buffer
             process
             (get-buffer-create (format " *elnode-request-%s*" port)))
            (process-buffer process)))))
    (with-current-buffer buf
      (insert data)
      ;; Try and parse...
      (case (catch 'elnode-parse-http
              (elnode--http-parse process))
        ;; If this fails with one of these specific codes it's
        ;; ok... we'll finish it when the data arrives
        ('(header content)
         (elnode-error "elnode--filter: partial header data received"))
        ;; We were successful so we can call the user handler.
        ('done
         (save-excursion
           (goto-char (process-get process :elnode-header-end))
           (let ((handler
                  (elnode--get-server-prop process :elnode-http-handler)))
             ;; This is where we call the user handler
             ;; TODO: this needs error protection so we can return an error?
             (condition-case signal-value
                 (progn
                   (elnode-error "filter: calling handler on %s" process)
                   (funcall handler process)
                   (elnode-error "filter: handler returned on %s" process))
               ('elnode-defer
                (elnode-error "filter: defer caught on %s" process)
                (case (elnode--get-server-prop process :elnode-defer-mode)
                  ((:managed 'managed)
                   (elnode--deferred-add process
                                         (cdr signal-value)))
                  ((:immediate 'immediate)
                   (elnode-error "filter: immediate defer on %s" process)
                   (funcall (cdr signal-value) process))))
               ('t
                ;; FIXME: we need some sort of check to see if the
                ;; header has been written
                (elnode-error "elnode--filter: default handling")
                (process-send-string
                 process
                 (elnode--format-response 500)))))))))))

(defmacro with-elnode-mock-server (handler &rest body)
  "Execute BODY with a fake server which is bound to HANDLER.

This is useful for doing end to end client testing:

 (ert-deftest elnode-some-page ()
  (with-elnode-mock-server 'elnode-hostpath-default-handler
    (elnode-test-call \"/something/test\")))

The test call with be passed to the
`elnode-hostpath-default-handler' via the normal HTTP parsing
routines."
  (declare
   (indent defun)
   (debug t))
  `(flet ((elnode--get-server-prop (proc key)
            (cond
              ((eq key :elnode-http-handler)
               ,handler))))
     ,@body))

(defun* elnode-test-call (path
                          &key
                          (method "GET")
                          (parameters '())
                          (headers '()))
  "Fake a call to elnode with the PATH.

In addition you can specify some extra HTTP stuff:

 :method  one of GET, POST, DELETE, etc...
 :parameters POST parameters, will be turned into a POST body
 :headers any specific headers you require, you may override
   test-call headers.

For example:

 (elnode-test-call \"/wiki/test\")

or:

 (elnode-test-call \"/wiki/test\"
                   :method \"POST\"
                   :parameters '((\"a\" . 10)))

For header and parameter names, strings MUST be used currently."
  (let ((fakir-mock-process-require-specified-buffer t))
    (fakir-mock-process ()
      (let ((hdrtext
             (apply
              'elnode--http-make-hdr
              `(,method
                ,path
                ,@headers
                (body ""))))
            (http-connection t))
        ;; Capture the real eof-func and then override it to do fake ending.
        (let ((eof-func (elnode--make-send-eof))
              (main-send-string (symbol-function 'elnode-http-send-string))
              (send-string-func (elnode--make-send-string))
              (the-end 0)
              (res-buffer (get-buffer-create "*elnode-test-call*"))
              result-data)
          (flet
              ((test-send-string (httpcon str)
                 (with-current-buffer res-buffer
                   (goto-char (point-max))
                   (insert str)))
               (elnode-http-send-string (httpcon str)
                 (test-send-string httpcon str)
                 (funcall main-send-string httpcon str))
               (elnode--make-send-string ()
                 (lambda (httpcon str)
                   (test-send-string httpcon str)
                   (send-string-func httpcon str)))
               (elnode--make-send-eof ()
                 (lambda (httpcon)
                   ;; Flet everything in elnode--http-end
                   (flet ((process-send-eof (proc)
                            ;; Signal the end
                            (setq the-end 't))
                          (delete-process (proc)
                            ;; Do nothing - we want the test proc
                            )
                          (kill-buffer (buffer)
                            ;; Again, do nothing, we want this buffer
                            (with-current-buffer buffer
                              (setq
                               result-data
                               (buffer-substring (point-min) (point-max))))
                            ;; Return true, don't really kill the buffer
                            t))
                     ;; Now call the captured eof-func
                     (funcall eof-func httpcon)))))
            ;; FIXME - we should unwind protect this?
            (elnode--filter http-connection hdrtext)
            ;; Now we sleep till the-end is true
            (while (not the-end)
              (sleep-for 0 10))
            (when the-end
              (list
               :result-data
               result-data
               :result-string
               (let ((data (with-current-buffer res-buffer
                             (buffer-substring (point-min) (point-max)))))
                 (kill-buffer res-buffer)
                 data)
               :buffer
               (process-buffer http-connection)
               ;; These properties are set by elnode-http-start
               :status
               (process-get
                http-connection
                :elnode-httpresponse-status)
               :header
               (process-get
                http-connection
                :elnode-httpresponse-header)))))))))

(defun elnode-test-handler (httpcon)
  "A simple handler for testing `elnode-test-call'.

The text spat out is tested, so is the status."
  (elnode-http-start httpcon 200 '("Content-Type" . "text/html"))
  (elnode-http-return
   httpcon
   "<html><body><h1>Hello World</h1></body></html>"))

(defun elnode--log-fn (server con msg)
  "Log function for elnode.

Serves only to connect the server process to the client processes"
  (process-put con :server server))

(defvar elnode-handler-history '()
  "The history of handlers bound to servers.")

(defvar elnode-port-history '()
  "The history of ports that servers are started on.")

(defvar elnode-host-history '()
  "The history of hosts that servers are started on.")

;;;###autoload
(defun* elnode-start (request-handler
                      &key
                      port
                      (host "localhost")
                      (defer-mode :managed))
  "Start a server using REQUEST-HANDLER.

REQUEST-HANDLER will handle requests on PORT on HOST (which is
'localhost' by default).

REQUEST-HANDLER is a function which is called with the request.
The function is called with one argument, which is the
http-connection.

You can use functions such as `elnode-http-start' and
`elnode-http-send-body' to send the http response.

Example:

  (defun nic-server (httpcon)
    (elnode-http-start httpcon 200 '((\"Content-Type: text/html\")))
    (elnode-http-return httpcon \"<html><b>BIG!</b></html>\")
  )
  (elnode-start 'nic-server)

Now visit http://127.0.0.1:8000

If PORT is non-nil, then run server on PORT, otherwise default to
8000.

If HOST is non-nil, then run the server on the specified local IP
address, otherwise use localhost.  A few names are predefined:

  \"localhost\" is 127.0.0.1
  \"*\" is 0.0.0.0

Additionally, you may specifiy an IP address, e.g \"1.2.3.4\"

Note that although HOST may be specified, elnode does not
disambiguate on running servers by HOST.  So you cannot start two
elnode servers on the same port on different hosts."
  (interactive
   (let ((handler (completing-read "Handler function: "
                                   obarray 'fboundp t nil nil))
         (port (read-number "Port: " 8000))
         (host (read-string "Host: " "localhost" 'elnode-host-history)))
     (list (intern handler) :port port :host host)))
  (let ((port (or port 8000))
        (host (or host "localhost")))
    (unless (assoc port elnode-server-socket)
      ;; Add a new server socket to the list
      (setq elnode-server-socket
            (cons
             (cons port
                   (let ((buf (get-buffer-create "*elnode-webserver*")))
                     (make-network-process
                      :name "*elnode-webserver-proc*"
                      :buffer buf
                      :server t
                      :nowait 't
                      :host (cond
                             ((equal host "localhost") 'local)
                             ((equal host "*") nil)
                             (t host))
                      :service port
                      :coding '(raw-text-unix . raw-text-unix)
                      :family 'ipv4
                      :filter 'elnode--filter
                      :sentinel 'elnode--sentinel
                      :log 'elnode--log-fn
                      :plist (list
                              :elnode-http-handler request-handler
                              :elnode-defer-mode defer-mode))))
             elnode-server-socket)))))

;; TODO: make this take an argument for the
(defun elnode-stop (port)
  "Stop the elnode server attached to PORT."
  (interactive "nPort: ")
  (let ((server (assoc port elnode-server-socket)))
    (if server
        (progn
          (delete-process (cdr server))
          (setq elnode-server-socket
                ;; remove-if
                (let ((test (lambda (elem)
                              (= (car elem) port)))
                      (l elnode-server-socket)
                      result)
                  (while (car l)
                    (let ((p (pop l))
                          (r (cdr l)))
                      (if (not (funcall test p))
                          (setq result (cons p result)))))
                  result))))))

(defun elnode-list-buffers ()
  "List the current buffers being managed by Elnode."
  (interactive)
  (with-current-buffer (get-buffer-create "*elnode-buffers*")
    (erase-buffer)
    (mapc
     (lambda (b)
       (save-excursion
         (if (string-match " \\*elnode-.*" (buffer-name b))
             (insert (format "%s\n" b)))
       ))
     (sort (buffer-list)
           (lambda (a b)
             (string-lessp (buffer-name b) (buffer-name a))))))
  (display-buffer (get-buffer "*elnode-buffers*")))

(defun elnode-time-encode (time-str)
  "Basic TIME-STR to time encoding."
  (apply 'encode-time (parse-time-string time-str)))


;; HTTP API methods

(defun elnode--http-hdr (httpcon)
  "Return the header cons for the HTTPCON.

The status-line and the header alist."
  (cons
   (process-get httpcon :elnode-http-status)
   (process-get httpcon :elnode-http-header)))

(defun elnode-http-header (httpcon name &optional convert)
  "Get the header specified by NAME from the HTTPCON.

HEADER may be a string or a symbol.  If NAME is a symbol it is
case insensitve.

If optional CONVERT is specified it may specify a conversion,
currently supported conversions are:

 :time - to convert a time value properly"
  (let* ((key (if (symbolp name)
                  (intern (downcase (symbol-name name)))
                name))
         (hdr (process-get
               httpcon
               (if (symbolp key)
                   :elnode-http-header-syms
                 :elnode-http-header)))
         (val (cdr (assoc key hdr))))
    (case convert
      (:time
       (when val
         (elnode-time-encode val)))
      (t
       val))))


(defun elnode-http-cookie (httpcon name)
  "Return the cookie value for HTTPCON specified by NAME."
  (let ((cookie-list (or
                      (process-get httpcon :elnode-http-coookie-list)
                      ;; Split out the cookies
                      (let* ((cookie-hdr (elnode-http-header httpcon "Cookie"))
                             (parts (split-string cookie-hdr ";")))
                        (let ((lst
                               (mapcar
                                (lambda (s)
                                  (url-parse-args
                                   (if (string-match "[ \t]*\\(.*\\)[ \t]*$" s)
                                       (replace-match "\\1" nil nil s)
                                     s)))
                                parts)))
                          (process-put httpcon :elnode-http-cookie-list lst)
                          lst)))))
    (loop for cookie in cookie-list
          do (if (assoc-string name cookie)
                 (return cookie)))))


(defun elnode--http-parse-status (httpcon &optional property)
  "Parse the status line of HTTPCON.

If PROPERTY is non-nil, then return that property."
  (let ((http-line (process-get httpcon :elnode-http-status)))
    (string-match
     "\\(GET\\|POST\\|HEAD\\) \\(.*\\) HTTP/\\(1.[01]\\)"
     http-line)
    (process-put httpcon :elnode-http-method (match-string 1 http-line))
    (process-put httpcon :elnode-http-resource (match-string 2 http-line))
    (process-put httpcon :elnode-http-version (match-string 3 http-line))
    (if property
        (process-get httpcon property))))

(defun elnode--http-parse-resource (httpcon &optional property)
  "Convert the specified resource to a path and a query."
  (save-match-data
    (let ((resource
           (or
            (process-get httpcon :elnode-http-resource)
            (elnode--http-parse-status httpcon :elnode-http-resource))))
      (or
       ;; root pattern
       (string-match "^\\(/\\)\\(\\?.*\\)*$" resource)
       ;; /somepath or /somepath/somepath
       (string-match "^\\(/[^?]+\\)\\(\\?.*\\)*$" resource))
      (let ((path (url-unhex-string (match-string 1 resource))))
        (process-put httpcon :elnode-http-pathinfo path))
      (if (match-string 2 resource)
          (let ((query (match-string 2 resource)))
            (string-match "\\?\\(.+\\)" query)
            (if (match-string 1 query)
                (process-put
                 httpcon
                 :elnode-http-query
                 (match-string 1 query)))))))
  (if property
      (process-get httpcon property)))

(defun elnode-http-pathinfo (httpcon)
  "Get the PATHINFO of the request."
  (or
   (process-get httpcon :elnode-http-pathinfo)
   (elnode--http-parse-resource httpcon :elnode-http-pathinfo)))

(defun elnode-http-query (httpcon)
  "Get the QUERY of the request."
  (or
   (process-get httpcon :elnode-http-query)
   (elnode--http-parse-resource httpcon :elnode-http-query)))

(defun elnode--http-param-part-decode (param-thing)
  "Decode an HTTP URL parameter part.

For example in:

 http://nic.ferrier.me.uk/blog/elnode/?p=10&a+c=20&d=x+y&z=this%20is%09me+and%20this

The following are param parts and the decoding that this function
will do:

 \"p\" ->  \"p\"

 \"10\" -> \"10\"

 \"a+c\" -> \"a c\" - an example of + encoding

 \"d\" -> \"d\"

 \"x+y\" -> \"x y\" - another example of + encoding, in a parameter name

 \"z\" -> \"z\"

 \"this%20is%09me+and%20this\" -> \"this is\tme and this\" -
 percent encoding and plus encoding"
  (url-unhex-string (replace-regexp-in-string "\\+" " " param-thing) 't)
  )

(defun elnode--http-query-to-alist (query)
  "Crap parser for HTTP QUERY data.

Returns an association list."
  (let ((alist (mapcar
                (lambda (nv)
                  (if (string-match "\\([^=]+\\)\\(=\\(.*\\)\\)*" nv)
                      (cons
                       (elnode--http-param-part-decode (match-string 1 nv))
                       (if (match-string 2 nv)
                           (elnode--http-param-part-decode (match-string 3 nv))
                         nil))))
                (split-string query "&"))
               ))
    alist))

(defun elnode--alist-merge (a b &optional operator)
  "Merge two association lists non-destructively.

A is considered the priority (it's elements go in first)."
  (if (not operator)
      (setq operator 'assq))
  (let* ((res '()))
    (let ((lst (append a b)))
      (while lst
        (let ((item (car-safe lst)))
          (setq lst (cdr-safe lst))
          (let* ((key (car item))
                 (aval (funcall operator key a))
                 (bval (funcall operator key b)))
            (if (not (funcall operator key res))
                (setq res (cons
                           (if (and aval bval)
                               ;; the item is in both lists
                               (cons (car item)
                                     (list (cdr aval) (cdr bval)))
                             item)
                           res))))))
        res)))

(defun elnode--http-post-to-alist (httpcon)
  "Parse the POST body."
  ;; FIXME: this is ONLY a content length header parser it should also
  ;; cope with transfer encodings.
  (let ((postdata
         (with-current-buffer (process-buffer httpcon)
           (buffer-substring
            ;; we might have to add 2 to this because of trailing \r\n
            (process-get httpcon :elnode-header-end)
            (point-max)))))
    (elnode--http-query-to-alist postdata)))

(defun elnode-http-params (httpcon)
  "Get an alist of the parameters in the request.

If the method is a GET then the parameters are from the url. If
the method is a POST then the parameters may come from either the
url or the POST body or both:

 POST /path?a=b&x=y
 a=c

would result in:

 '(('a' 'b' 'c')('x' . 'y'))"
  (or
   (process-get httpcon :elnode-http-params)
   (let ((query (elnode-http-query httpcon)))
     (let ((alist (if query
                      (elnode--http-query-to-alist query)
                    '())))
       ;; If we're a POST we have to merge the params
       (if (equal "POST" (elnode-http-method httpcon))
           (progn
             (setq alist (elnode--alist-merge
                          alist
                          (elnode--http-post-to-alist httpcon)
                          'assoc))
             (process-put httpcon :elnode-http-params alist)
             alist)
         ;; Else just return the query params
         (process-put httpcon :elnode-http-params alist)
         alist)))))

(defun elnode-http-param (httpcon name)
  "Get the named parameter from the request."
  (let* ((params (elnode-http-params httpcon))
         (param-pair (assoc name params)))
    ;; Should we signal when we don't have a param?
    (when param-pair
      (cdr param-pair))))


(defun elnode-http-method (httpcon)
  "Get the PATHINFO of the request."
  (or
   (process-get httpcon :elnode-http-method)
   (elnode--http-parse-status httpcon :elnode-http-method)))

(defun elnode-http-version (httpcon)
  "Get the PATHINFO of the request."
  (or
   (process-get httpcon :elnode-http-version)
   (elnode--http-parse-status httpcon :elnode-http-version)))

(defun elnode-http-send-string (httpcon str)
  "Send the string to the HTTP connection.

This is really only a placeholder function for doing transfer-encoding."
  ;; We should check that we are actually doing chunked encoding...
  ;; ... but for now we just presume we're doing it.
  (elnode-error "elnode-http-send-string %s [[%s]]" httpcon (elnode-trunc str))
  (let ((len (string-bytes str)))
    (process-put httpcon :elnode-bytes-written
                 (+ len (or (process-get httpcon :elnode-bytes-written) 0)))
    ;; FIXME Errors can happen here, because the socket goes away.. it
    ;; would be nice to trap them and report and then re-raise them.
    (process-send-string httpcon (format "%x\r\n%s\r\n" len (or str "")))))

(defvar elnode-http-codes-alist
  (loop for p in '((200 . "Ok")
                   (302 . "Redirect")
                   (400 . "Bad Request")
                   (401 . "Authenticate")
                   (404 . "Not Found")
                   (500 . "Server Error"))
        collect
        p
        collect
        (cons (number-to-string (car p))
              (cdr p)))
  "HTTP codes with string keys and integer keys.")

(defun elnode--http-result-header (hdr-alist)
  "Turn the HDR-ALIST into a result header string.

The HDR-ALIST is an alist of symbol or string keys which are
header names, against values which should be strings."
  (loop
   for p in (append (list (cons 'transfer-encoding "chunked")) hdr-alist)
   concat
   (format
    "%s: %s\r\n"
    (let ((hname (car p)))
      (capitalize
       (cond
        ((symbolp hname)
         (symbol-name hname))
        ((stringp hname)
         hname)
        (t
         (error "unsupported header type")))))
    (cdr p))))

(defun elnode-http-start (httpcon status &rest header)
  "Start the http response on the specified http connection.

HTTPCON is the HTTP connection being handled.
STATUS is the HTTP status, eg: 200 or 404
HEADER is a sequence of (header-name . value) pairs.

For example:

 (elnode-http-start httpcon \"200\" '(\"Content-type\" . \"text/html\"))

The status and the header are also stored on the process as meta
data.  This is done mainly for testing infrastructure."
  (if (process-get httpcon :elnode-http-started)
      (elnode-error "Http already started on %s" httpcon)
    ;; Send the header
    (elnode-error "starting HTTP response on %s" httpcon)
    (let ((header-alist (cons '("Transfer-encoding" . "chunked") header)))
      ;; Store the meta data about the response.
      (process-put httpcon :elnode-httpresponse-status status)
      (process-put httpcon :elnode-httpresponse-header header)
      (process-send-string
       httpcon
       (format
        "HTTP/1.1 %s %s\r\n%s\r\n"
        status
        ;; The status text
        (aget elnode-http-codes-alist status)
        ;; The header
        (or
         (elnode--http-result-header header)
         "\r\n")))
      (process-put httpcon :elnode-http-started 't))))

(defun elnode--http-end (httpcon)
  "We need a special end function to do the emacs clear up.

This makes access log file calls if the socket has a property
`:elnode-access-log-name'.  The property is taken to be the name
of a buffer."
  (elnode-error "elnode--http-end ending socket %s" httpcon)
  (let ((access-log-name (process-get httpcon :elnode-access-log-name)))
    (when access-log-name
      (elnode-log-access access-log-name httpcon)))
  (process-send-eof httpcon)
  (delete-process httpcon)
  (kill-buffer (process-buffer httpcon)))

(defun elnode-http-return (httpcon &optional data)
  "End the response on HTTPCON optionally sending DATA first.

HTTPCON is the http connection which must have had the headers
sent with `elnode-http-start'

DATA must be a string, it's just passed to `elnode-http-send'."
  (if (not (process-get httpcon :elnode-http-started))
      (elnode-error "Http not started")
    (progn
      (if data
          (elnode-http-send-string httpcon data))
      ;; Need to close the chunked encoding here
      (elnode-http-send-string httpcon "")
      (process-send-string httpcon "\r\n")
      (let ((eof-func (process-get httpcon :send-eof-function)))
        (when (functionp eof-func)
          (funcall eof-func httpcon))))))

(defun elnode-send-json (httpcon data &optional content-type)
  "Send a 200 OK to the HTTPCON along with DATA as JSON.

If CONTENT-TYPE is specified then it is used as the HTTP Content
Type of the response."
  (let ((json-to-send (json-encode data)))
    (elnode-http-start
     httpcon 200
     `("Content-type" . ,(or content-type "application/json")))
    (elnode-http-return httpcon json-to-send)))

(defun elnode-send-status (httpcon status &optional msg)
  "A generic handler to send STATUS to HTTPCON.

Sends an HTTP response with STATUS to the HTTPCON.  An HTML body
is sent by looking up the STATUS in the `elnode-default-response'
table.

Optionally include MSG."
  (elnode-http-start httpcon status '("Content-type" . "text/html"))
  (elnode-http-return httpcon
                      (elnode--format-response status msg)))

(defun elnode-send-404 (httpcon &optional msg)
  "Sends a Not Found error to the HTTPCON.

Optionally include MSG."
  (elnode-send-status httpcon 404 msg))

(defun elnode-send-400 (httpcon &optional msg)
  "Sends a Bad Request error to the HTTPCON.

Optionally include MSG."
  (elnode-send-status httpcon 404 msg))

(defun elnode-send-500 (httpcon &optional msg)
  "Sends a Server Error to the HTTPCON.

Optionally include MSG."
  (elnode-send-status httpcon 500 msg))


(defun elnode-send-redirect (httpcon location &optional type)
  "Sends a redirect to LOCATION.

If TYPE is non-nil, use it as a status code.  Defaults to 302 -
permanent redirect."
  (let ((status-code (or type 302)))
    (elnode-http-start httpcon status-code `("Location" . ,location))
    (elnode-http-return
     httpcon
     (format "<h1>redirecting you to %s</h1>\r\n" location))))

(defun elnode-normalize-path (httpcon handler)
  "A decorator for HANDLER that normalizes paths to have a trailing slash.

This checks the HTTPCON path for a trailing slash and sends a 302
to the slash trailed url if there is none.

Otherwise it calls HANDLER."
  (let ((ends-in-slash-or-extension-regex ".*\\(/\\|.*\\.[^/]*\\)$")
        (path (elnode-http-pathinfo httpcon)))
    (if (not (save-match-data
               (string-match ends-in-slash-or-extension-regex
                             path)))
        (elnode-send-redirect
         httpcon
         (format "%s/" path))
      (funcall handler httpcon))))

(defun elnode--mapper-find-mapping (match-path mapping-table)
  "Return the mapping that matches MATCH-PATH in MAPPING-TABLE."
  (loop for mapping in mapping-table
        if (string-match (car mapping) match-path)
        return mapping))

(defun elnode--mapper-find (httpcon path mapping-table)
  "Try and find the PATH inside the MAPPING-TABLE.

This function exposes it's `match-data' on the 'path' variable so
that you can access that in your handler with something like:

 (match-string 1 (elnode-http-pathinfo httpcon))

Returns the handler function that mapped, or `nil'.

This function also establishes the `:elnode-http-mapping'
property, adding it to the HTTPCON so it can be accessed from
inside your handler with `elnode-http-mapping'."
  ;; First find the mapping in the mapping table
  (let* ((match-path (save-match-data
                       ;; remove leading slash
                       (if (string-match "^/\\(.*\\)" path)
                           (match-string 1 path)
                         path)))
         (m (elnode--mapper-find-mapping match-path mapping-table)))
    ;; Now work out if we found one and what it was mapped to
    (when (and m
               (or (functionp (cdr m))
                   (functionp (and (symbolp (cdr m))
                                   (symbol-value (cdr m))))))
      ;; Make the match parts accessible
      (process-put
       httpcon
       :elnode-http-mapping
       (when (string-match (car m) match-path)
         (loop for i from 0 to (- (/ (length (match-data match-path)) 2) 1)
               collect (match-string i match-path))))
      ;; Check if it's a function or a variable pointing to a
      ;; function
      (cond
       ((functionp (cdr m))
        (cdr m))
       ((functionp (symbol-value (cdr m)))
        (symbol-value (cdr m)))))))

(defun elnode-http-mapping (httpcon &optional part)
  "Return the match on the HTTPCON that resulted in the current handler.

With PART it returns a specific part of the match , by default
PART is 0.

This results only from a call via `elnode-dispatcher'.

It returns the string which matched your url-mapping, with the
match-data attached. So given the mapping:

 (\"static/\\(.*\\)\" . my-handler)

and the request:

 /static/somedir/somefile.jpg

The following is true inside the handler:

 (equals \"/somedir/somefile.jpg\"
         (match-string 1 (elnode-http-mapping httpcon)))

The function `elnode-test-path' uses this facility to work out a
target path."
  (elt
   (process-get httpcon :elnode-http-mapping)
   (if part part 0)))



(defun elnode-get-targetfile (httpcon docroot)
  "Get the targetted file from the HTTPCON.

Attempts to resolve the matched path of the HTTPCON against the
DOCROOT.

The resulting file is NOT checked for existance or safety."
  (let* ((pathinfo (elnode-http-pathinfo httpcon))
         (path (elnode-http-mapping httpcon 1))
         (targetfile
          (format
           "%s%s"
           (expand-file-name docroot)
           (format (or (and path
                            (save-match-data
                              (string-match "^/" path))
                            "%s")
                       "/%s")
                   (if (or (not path) (equal path "/"))
                       ""
                     path)))))
    targetfile))

(defvar elnode--do-access-logging-on-dispatch t
  "Needed to suppress logging in testing.")

(defun* elnode--dispatch-proc (httpcon
                              path
                              url-mapping-table
                              &key
                              (function-404 'elnode-send-404)
                              (log-name "elnode"))
  "Dispatch to the matched handler for the PATH on the HTTPCON.

The handler for PATH is matched in the URL-MAPPING-TABLE via
`elnode--mapper-find'.

If no handler is found then a 404 is attempted via FUNCTION-404,
it it's found to be a function, or as a last resort
`elnode-send-404'."
  (let ((handler-func
         (elnode--mapper-find
          httpcon path
          url-mapping-table)))
    (when elnode--do-access-logging-on-dispatch
      (process-put httpcon :elnode-access-log-name log-name))
    (cond
     ;; If we have a handler, use it.
     ((functionp handler-func)
      (funcall handler-func httpcon))
     (t
      (funcall function-404 httpcon)))))

(defun elnode-dispatcher (httpcon url-mapping-table &optional function-404)
  "Dispatch the HTTPCON to the correct function based on the URL-MAPPING-TABLE.

URL-MAPPING-TABLE is an alist of:

 (url-regex . function-to-dispatch)

To map the root url you should use:

  \"^$\"

To ensure paths end in /, `elnode-dispatcher' uses
`elnode-normalize-path'.  To map another url you should use:

  \"^path/$\" or \"^path/sub-path/$\"

An example server setup:

  (defun my-server (httpcon)
    (elnode-dispatcher
     httpcon
     '((\"^$\" . root-view)
       (\"^1/$\" . view-1))))

If FUNCTION-404 is non-nil then it is called when no regexp is
matched."
  (elnode-normalize-path
   httpcon
   (lambda (httpcon)
     ;; Get pathinfo again because we may have redirected.
     (let ((pathinfo (elnode-http-pathinfo httpcon)))
       (elnode--dispatch-proc
        httpcon
        pathinfo
        url-mapping-table
        :function-404 function-404)))))

(defun* elnode-hostpath-dispatcher (httpcon
                                   hostpath-mapping-table
                                   &key
                                   (function-404 'elnode-send-404)
                                   (log-name "elnode"))
  "Dispatch HTTPCON to a handler based on the HOSTPATH-MAPPING-TABLE.

HOSTPATH-MAPPING-TABLE has a regex of the host and the path slash
separated, thus:

 (\"^localhost/pastebin.*\" . pastebin-handler)

FUNCTION-404 should be a 404 handling function, by default it's
`elnode-send-404'.

LOG-NAME is an optional log-name."
  (let ((hostpath
         (format "%s%s"
                 (let ((host
                        (or
                         (elnode-http-header httpcon "Host")
                         "")))
                   (save-match-data
                     (string-match "\\([^:]+\\)\\(:[0-9]+.*\\)" host)
                     (match-string 1 host)))
                 (elnode-http-pathinfo httpcon))))
    (elnode--dispatch-proc
     httpcon
     hostpath
     hostpath-mapping-table
     :function-404 function-404
     :log-name log-name)))

;;;###autoload
(defcustom elnode-hostpath-default-table
  '(("[^/]+/wiki/\\(.*\\)" . elnode-wikiserver)
    ("[^/]+/\\(.*\\)" . elnode-webserver))
  "Defines mappings for `elnode-hostpath-default-handler'.

This is the default mapping table for Elnode, out of the box. If
you customize this then elnode will serve these hostpath mappings
by just loading Elnode.

By default the table maps everything to
`elnode-webserver'. Unless you're happy with the default you
should probably get rid of the everything path because it will
interfere with any other mappings you add."
  :group 'elnode
  :type '(alist :key-type string
                :value-type symbol))

(defun elnode-hostpath-default-handler (httpcon)
  "A default hostpath handler.

This uses the `elnode-hostpath-default-table' for the match
table.  It calls `elnode-hostpath-dispatcher' with
`elnode-hostpath-default-table'."
  (elnode-hostpath-dispatcher httpcon elnode-hostpath-default-table))


;; Elnode child process functions

(defcustom elnode-log-worker-elisp nil
  "If true then worker Elisp (Elisp run in a child-Emacs process) is logged.

The buffer '* elnode-worker-elisp *' is used for the log."
  :group 'elnode
  :type '(boolean))

(defcustom elnode-log-worker-responses nil
  "If true then worker Elisp logs responses in a buffer.

The buffer '* elnode-worker-response *' is used for the log."
  :group 'elnode
  :type '(boolean))

(defun elnode--worker-filter-helper (process
                                     data
                                     child-lisp
                                     out-stream)
  "A helper function for `elnode-worker-elisp'.

Sends DATA being sent from PROCESS to OUT-STREAM.

CHILD-LISP is sent in response to Emacs' query for the Lisp on stdin."
  (if elnode-log-worker-responses
      (with-current-buffer
          (get-buffer-create "* elnode-worker-response *")
        (goto-char (point-max))
        (insert data)))

  ;; Spit out a bit of the data (truncated)
  (elnode-error
   "elnode--worker-filter-helper data %s... %s"
   (elnode-trunc data)
   out-stream)

  ;; We get this as a signal to read a lisp expression
  (if (equal data "Lisp expression: ")
      (process-send-string process child-lisp)
    (cond
     ((bufferp out-stream)
      (with-current-buffer out-stream
        (insert data)))
     ((functionp out-stream)
      (funcall out-stream process data))
     ((processp out-stream)
      (if (not (equal "closed" (process-status process)))
          (funcall
           ;; Does the output-stream have a specific function?
           (or (process-get out-stream :send-string-function)
               'process-send-string)
           ;; The data to sent to the output-stream process
           out-stream data))))))

(defun elnode--worker-lisp-helper (child-lisp)
  "Called with CHILD-LISP it returns a version of CHILD-LISP.

By default this function does nothing except return it's argument.

The function exists so that other functions CAN flet it and thus
override the Lisp being passed to the child Emacs."
  child-lisp)

(defmacro elnode-worker-elisp (output-stream bindings &rest body)
  "Evaluate the BODY in a child Emacs connected to OUTPUT-STREAM.

The BINDINGS are let-form variable assignments which are
serialized for the child Emacs.  Unless a variable from the
parent is explicitly stated here it will NOT be accessible in the
child Emacs.

The child Emacs has a `load-path' exactly as the `load-path' of
the parent Emacs at execution.

The created child Emacs process is returned.  It's possible to
kill the child Emacs process or do other things to it directly.
This could be very dangerous however, you should know what you
are doing before attempting it.

The OUTPUT-STREAM could be a buffer, a function or another
process.

If the OUTPUT-STREAM is another process it may have a process
property `:send-string-function' evaluating to a function to send
data to that process.  The function should take the same
arguments as the standard Emacs Lisp `process-send-string'.

Furthermore, if the OUTPUT-STREAM is another process, when the
child Emacs finishes an EOF is sent to that process.  If the
OUTPUT-STREAM process has a process property `:send-eof-function'
then that is used to send the EOF.  The function should take the
same arguments as the standard Emacs Lisp `process-send-eof'.

An example:

 (elnode-worker-elisp http-connection
                      ((path (path-function)))
   (require 'creole)
   (creole-wiki path))

Presuming http-connection is a process (in the manner of Elnode,
for example) this will cause a child Emacs to be created, within
which `path' (which is serialized from the value of the parent
Emacs' `path-function') will be loaded and converted from
WikiCreole to HTML and then sent to the standard output stream.
The child's standard output stream is connected directly to the
`http-connection'.  In this case, presumably the
`http-connection' would have functions attached to the properties
`:send-string-function' and `:send-eof-function' to do HTTP
chunk encoding and to end the HTTP connection correctly."
  (declare
   (indent 2)
   (debug
    (sexp
     (&rest
      &or symbolp (gate symbolp &optional form))
     &rest form)))
  (let ((loadpathvar (make-symbol "load-path-form"))
        (bindingsvar (make-symbol "bindings"))
        (childlispvar (make-symbol "child-lisp"))
        (childlispfile (make-symbol "child-lisp-file"))
        (filtervar (make-symbol "filter-function"))
        (cmdvar (make-symbol "command"))
        (procvar (make-symbol "process"))
        (namevar (make-symbol "process-name"))
        (bufvar (make-symbol "buffer"))
        (outvar (make-symbol "output-stream")))
    `(let* ((,outvar ,output-stream)
            (,childlispvar  ; the lisp to run
             (concat
              ;; There is a very strange thing with sending lisp to
              ;; (read) over a piped stream... (read) can't cope with
              ;; multiple lines; so we encode newline here.
              (replace-regexp-in-string
               "\n"
               "\\\\n"
               (format "(progn (setq load-path (quote %S)) (let %S %S))"
                       load-path
                       (list
                        ,@(loop
                           for f in bindings collect
                           (list 'list
                                 `(quote ,(car f))
                                 `(format "%s" ,(cadr f)))))
                       '(progn ,@(elnode--worker-lisp-helper body))))
              "\n"))
            (,childlispfile
             (let ((,childlispfile (make-temp-file "elnode")))
               (with-temp-file ,childlispfile
                 (insert ,childlispvar))
               ,childlispfile))
            (,cmdvar
             (concat "emacs -q -batch "
                     "--script " ,childlispfile
                     ));;" 2> /dev/null"))
            (,namevar (concat
                       (number-to-string (random))
                       (number-to-string (float-time))))
            ;; We have to make a buffer unless the output-stream is a buffer
            (,bufvar (cond
                      ((bufferp ,outvar) ,outvar)
                      (t
                       (get-buffer-create (format "* %s *" ,namevar)))))
            (,procvar (start-process-shell-command ,namevar ,bufvar ,cmdvar)))
       ;; Log the lisp
       (if elnode-log-worker-elisp
           (with-current-buffer (get-buffer-create "* elnode-worker-elisp *")
             (insert ,childlispvar)))
       ;; Setup a filter funcion on the child lisp to map output back
       ;; to whatever the output is
       (set-process-filter
        ,procvar
        (lambda (process data)
          (elnode--worker-filter-helper
           process
           data
           ,childlispvar
           ,outvar)))
       ;; Now setup the sentinel
       (set-process-sentinel
        ,procvar
        (lambda (process status)
          ;; Choose or fake a send-eof func
          (elnode-error "elnode-worker-elisp sentinel for %s" ,namevar)
          (let ((send-eof-function
                 (or (and (processp ,outvar)
                          (or (process-get ,outvar :send-eof-function)
                              'process-send-eof))
                     (lambda (con)
                       (elnode-error
                        "elnode-worker-elisp fake eof func %s"
                        ,namevar)))))
            (cond
             ;; Normal end
             ((equal status "finished\n")
              (elnode-error
               "elnode-worker-elisp %s completed %s"
               ,namevar
               ,outvar)
              (funcall send-eof-function ,outvar))
             ;; Error end
             ((string-match "exited abnormally with code \\([0-9]+\\)\n" status)
              (elnode-error
               "elnode-worker-elisp %s completed with an error: %s"
               ,namevar
               status)
              (funcall send-eof-function ,outvar)
              (delete-process process)
              (unless (bufferp ,outvar)
                (kill-buffer (process-buffer process))))
             ;; Any other signal status is ignored
             (t)))))
       ,procvar)))

(defun elnode-worker-last-code ()
  "Put the last worker code in a file for later use.

When testing it's good to be able to capture the last lisp made
by `elnode-worker-elisp' for manipulating manually."
  (interactive)
  (with-current-buffer "* elnode-worker-elisp *"
    (goto-line -1)
    (let ((last-line
           (buffer-substring (line-beginning-position)
                             (line-end-position))))
      (with-temp-file "/tmp/elnode-worker-elisp-code.el"
        (insert last-line)))))

(defun elnode-wait-for-exit (process)
  "Wait for PROCESS status to go to 'exit."
  (while (not (eq (process-status process) 'exit))
    (sleep-for 1)))


;; TODO: handle errors better than messaging
(defun elnode--child-process-sentinel (process status)
  "A sentinel for Elnode child PROCESS.

Elnode child processes are just Emacs asynchronous processes that
send their output to an Elnode HTTP connection.

The main job of this sentinel is to monitor when the STATUS of
PROCESS indicates the end of the PROCESS and to do
`elnode-http-end' on the associated HTTP connection when that
happens."
  (cond
   ((equal status "finished\n")
    (let ((httpcon (process-get process :elnode-httpcon)))
      (elnode-error
       "Elnode-child-process-sentinel Status @ finished: %s -> %s on %s"
       (process-status httpcon)
       (process-status process)
       httpcon)
      (if (not (eq 'closed (process-status httpcon)))
          (progn
            (elnode-http-send-string httpcon  "")
            (process-send-string httpcon "\r\n")
            (elnode--http-end httpcon)))))
   ((string-match "exited abnormally with code \\([0-9]+\\)\n" status)
    (let ((httpcon (process-get process :elnode-httpcon)))
      (elnode-error "Elnode-child-process-sentinel: %s on %s" status httpcon)
      (if (not (eq 'closed (process-status httpcon)))
          (progn
            (elnode-http-send-string httpcon "")
            (process-send-string httpcon "\r\n")
            (elnode--http-end httpcon)))
      (delete-process process)
      (kill-buffer (process-buffer process))))
   (t
    (elnode-error "Elnode-chlild-process-sentinel: %s on %s" status process))))

(defun elnode--child-process-filter (process data)
  "A generic filter function for elnode child processes.

elnode child processes are just emacs asynchronous processes that
send their output to an elnode http connection.

This filter function does the job of taking the output from the
async process and finding the associated elnode http connection
and sending the data there."
  (let ((httpcon (process-get process :elnode-httpcon)))
    (elnode-error
     "Elnode-child-process-filter http state: %s data length: %s on %s"
     (process-status httpcon)
     (length data)
     httpcon)
    (if (not (eq 'closed (process-status httpcon)))
        (elnode-http-send-string httpcon data))))

(defun elnode-child-process (httpcon program &rest args)
  "Run the specified PROGRAM asynchronously sending output to HTTPCON.

PROGRAM is the path to the program to run, to be resolved by
`start-process' in the usual way.

ARGS is a list of arguments to pass to the program.

It is NOT POSSIBLE to run more than one process at a time
directed at the same http connection."
  (let* ((args `(,(format "%s-%s" (process-name httpcon) program)
                 ,(format " %s-%s" (process-name httpcon) program)
                 ,program
                 ,@args
                ))
         (p (let ((process-connection-type nil))
              (apply 'start-process args))))
    (set-process-coding-system p 'raw-text-unix)
    ;; Bind the http connection to the process
    (process-put p :elnode-httpcon httpcon)
    ;; Bind the process to the http connection
    ;;
    ;; WARNING: this means you can only have 1 child process at a time
    (process-put httpcon :elnode-child-process p)
    ;; Setup the filter and the sentinel to do the right thing with
    ;; incomming data and signals
    (set-process-filter p 'elnode--child-process-filter)
    (set-process-sentinel p 'elnode--child-process-sentinel)
    (elnode-error "Elnode-child-process init %s" httpcon)))

;; Authentication handlers

(defun elnode-auth (httpcon)
  )

(defcustom elnode-send-file-program "/bin/cat"
  "The program to use for sending files.

Altering this is not recomended but it may be a good hook for
certain types of debugging."
  :group 'elnode
  :type '(string))

(defun elnode--buffer-template (file-buf replacements)
  "Template render a buffer and return a copy.

FILE-BUF is the source buffer to use, template sections marked up like:

 <!##E \\(.*?\\) E##!>

will be replaced with a value looked up in REPLACEMENTS.

REPLACEMENTS is either a hashtable or an association list.

For example:

 <title><!##E my-title E##!></title>
 <p>By <!##E my-name E##!>.</p>

with the REPLACEMENTS being:

  my-title => All things Elnode!
  my-name => Nic Ferrier

would result in the string:

  <title>All things Elnode!</title>
  <p>By Nic Ferrier</p>

being returned."
  (with-current-buffer file-buf
    (replace-regexp-in-string
     "<!##E \\(.*?\\) E##!>"
     (lambda (matched)
       (cond
        ((hash-table-p replacements)
         (gethash (match-string 1 matched) replacements ""))
        (t
         ;; Presume it's an alist
         (or
          (aget replacements (match-string 1 matched) t) ""))))
     (buffer-substring (point-min)(point-max)))))

(defvar elnode-webserver-visit-file nil
  "Whether the webserver reads files by visiting buffers or not.

When set to `t' files to be sent with the `elnode-send-file' are
read into Emacs using `find-file'.")

(defun* elnode-send-file (httpcon targetfile
                                  &key
                                  preamble
                                  mime-types
                                  replacements)
  "Send the TARGETFILE to the HTTPCON.

If the TARGETFILE is relative then resolve it via the current
`load-file-name' or `buffer-file-name' or `default-directory'.

WARNING: this resolution order is likely to change because,
especially when developing `default-directory' can be quite
random (change buffer, change `default-directory').

Optionally you may specify extra keyword arguments:

:PREAMBLE a string of data to send before the file.

:PREAMBLE is most useful for prefixing syntax to some other file,
for example you could prefix an XML file with XSL transformation
statements so a compliant user-agent will transform the XML.

:MIME-TYPES is an optional alist of MIME type mappings to help
resolve the type of a file.

If :REPLACEMENTS is specified it should be a hash-table or an
association list used to supply values for templating.  When
templating is specified the targetfile is not sent directly but
opened in Emacs as a buffer and transformed through the
templating system before being sent.  See
`elnode--buffer-template' for details of templating."
  (let ((filename
         (if (not (file-name-absolute-p targetfile))
             (file-relative-name
              targetfile
              (let ((dir (or load-file-name buffer-file-name)))
                (if dir
                    (directory-file-name dir)
                  default-directory)))
           targetfile)))
    (if (not (file-exists-p filename))
        ;; FIXME: This needs improving so we can handle the 404
        ;; This function should raise an exception?
        (elnode-send-404 httpcon)
      (let ((mimetype
             (or (when (listp mime-types)
                   (car (rassoc
                         (file-name-extension targetfile)
                         mime-types)))
                 (mm-default-file-encoding targetfile)
                  "application/octet-stream")))
        (elnode-http-start httpcon 200 `("Content-type" . ,mimetype))
        (when preamble (elnode-http-send-string httpcon preamble))
        (if (or elnode-webserver-visit-file replacements)
            (let ((file-buf (find-file-noselect filename)))
              (elnode-http-return
               httpcon
               (elnode--buffer-template file-buf replacements)))
          (elnode-child-process
           httpcon
           elnode-send-file-program
           targetfile))))))

(defmacro elnode-method (&rest method-mappings)
  "Map the HTTP method.

Write code like this:

 (elnode-method
  (GET
   (code)
   (more code))
  (POST
   (different code)
   (evenmorecode)))"
  (declare
   (debug (&rest (sexp &rest form)))
   (indent defun))
  (let ((var (make-symbol "v")))
    `(let ((,var (intern "GET"))) ;; (elnode-http-method httpcon))))
       (cond
        ,@(loop
           for d in method-mappings
           collect `((eq ,var (quote ,(car d)))
                     ,@(cdr d)))))))


;; Make simple handlers automatically

(defun elnode-make-redirecter (location &optional type)
  "Make a handler that will redirect to LOCATION.

Optionally, use the specified TYPE as the status code, eg:

 (elnode-make-redirect \"http://somehost.com/\" 301)"
  (lambda (httpcon)
    (elnode-send-redirect httpcon location type)))

(defun* elnode-make-send-file  (filename &key preamble mime-types )
  "Make a handler that will serve a single FILENAME.

If the FILENAME is relative then it is resolved against the
package's `load-file-name'.

Optionally mime-types and other additional keyword arguments may be
specified and are passed through, see `elnode-send-file' for
details."
  (lambda (httpcon)
    (elnode-send-file
     httpcon
     filename
     :mime-tpes mime-types
     :preamble preamble)))


;; Docroot protection

(defun elnode--under-docroot-p (target-file doc-root)
  (let ((docroot (expand-file-name doc-root)))
    (and
     (string-match
      (format "^%s\\($\\|/\\)" docroot)
      target-file)
     (file-exists-p target-file))))


(defun elnode-not-found (httpcon target-file)
  "`elnode-docroot-for' calls this when the doc was not found.

You can override this in tests to have interesting effects.  By
default it just calls `elnode-send-404'."
  (elnode-send-404 httpcon))

(defun elnode-cached-p (httpcon target-file)
  "Is the specified TARGET-FILE older than the HTTPCON?"
  (let ((modified-since
         (elnode-http-header httpcon 'if-modified-since :time)))
    (and
     modified-since
     (time-less-p
      (elt (file-attributes target-file) 5)
      modified-since))))


(defun elnode-cached (httpcon)
  "`elnode-docroot-for' calls this when the resources was cached.

By default it just calls `elnode-send-status' with 304."
  (elnode-send-status httpcon 304))

(defmacro elnode-docroot-for (doc-root with target-file-var
                                       on httpcon
                                       do &rest handling)
  "Docroot protection for Elnode handlers.

Test the path requested in HTTPCON is safely under the DOC-ROOT
specified, bind the TARGET-FILE-VAR to the resulting expanded
file name and execute the HANDLING code.

For example:

  (elnode-docroot-for
        \"~/work\"
        with file-var
        on httpcon
        do
        (elnode-send-file httpcon file-var))

checks any resource requested in HTTPCON is a file under the
doc-root \"~/work\" and if it is, binds the resulting file name
to FILE-VAR and calls the code following DO (which sends the file
to the HTTPCON).

When a file is not found (or not safe to return) `elnode-not-found' is called.

When a file is cached on the client (when a client sends a
conditional GET for the file that shows the client has an up to
date copy) then `elnode-cached' is called."
  (declare
   (debug (sexp "with" sexp "on" sexp "do" &rest form))
   (indent defun))
  (let ((dr (make-symbol "docroot"))
        (con (make-symbol "httpcon")))
    (assert (eq with 'with))
    (assert (eq on 'on))
    (assert (eq do 'do))
    `(let ((,dr ,doc-root)
           (,con ,httpcon))
       (let ((,target-file-var (elnode-get-targetfile ,con ,dr)))
         (if (not (elnode--under-docroot-p ,target-file-var ,dr))
             (elnode-not-found ,con ,target-file-var)
           (if (elnode-cached-p ,con ,target-file-var)
               (elnode-cached ,con)
             ,@handling))))))


;; Webserver stuff

(defcustom elnode-webserver-docroot "~/public_html"
  "The document root of the webserver.

Webserver functions are free to use this or not.  The
`elnode-webserver' function does use it."
  :group 'elnode
  :type 'file)

(defcustom elnode-webserver-extra-mimetypes '(("text/plain" . "creole")
                                               ("text/plain" . "el"))
  "this is just a way of hacking the mime type discovery so we
can add more file mappings more easily than editing
/etc/mime.types"
  :group 'elnode
  :type '(alist :key-type string
                :value-type string))

(defcustom elnode-webserver-index '("index.html" "index.htm")
  "A list of possible index filenames.

Anyone of the values of this list may be picked as the index page
for a directory."
  :group 'elnode
  :type '(repeat string))

(defun elnode-url-encode-path (path)
  "Return a url encoded version of PATH.

This is like `url-hexify-string' but it handles the parts of the
PATH properly.  It also hexifies single quote."
  (replace-regexp-in-string
   "'" "%27"
   (mapconcat
    'identity
    (loop
       for part in (split-string path "/")
       collect
         (concat
          (url-hexify-string part)))
    "/")))

(defcustom elnode-webserver-index-page-template "<html>
 <head>
  <title>%s</title>
 </head>
 <body>
  <h1>%s</h1>
  <div>%s</div>
 </body>
</html>
"
  "The page template used to render an index page.

The order of the variables is:

- the title of the document
- the title of the document
- the HTML formatted list of files."
  :group 'elnode
  :type '(string))

(defcustom elnode-webserver-index-file-template "<a href='%s'>%s</a><br/>\r\n"
  "The template for each file in the webserver index.

This is used to display each file in an automated directory index."
  :group 'elnode
  :type '(string))

(defun elnode--webserver-index (docroot targetfile pathinfo)
  "Constructs index documents.

The index is made for the DOCROOT and TARGETFILE. The web path is
PATHINFO."
  ;; TODO make this usable by people generally
  (let ((dirlist (directory-files-and-attributes targetfile)))
    ;; TODO make some templating here so people can change this
    (format
     elnode-webserver-index-page-template
     pathinfo
     pathinfo
     (loop for dir-entry in dirlist
           concat
           (let ((entry
                  (format
                   "%s/%s"
                   (if (equal pathinfo "/")  "" pathinfo)
                   (car dir-entry))))
             (format
              elnode-webserver-index-file-template
              (elnode-url-encode-path entry)
              (car dir-entry)))))))

;;;###autoload
(defun elnode--webserver-handler-proc (httpcon docroot mime-types)
  "Actual webserver implementation.

Do webserving to HTTPCON from the DOCROOT using the MIME-TYPES
for meta information.

This is not a real handler (because it takes more than the
HTTPCON) but it is called directly by the real webserver
handlers."
  (elnode-docroot-for docroot
    with targetfile
    on httpcon
    do
    (let ((pathinfo (elnode-http-pathinfo httpcon)))
      (if (file-directory-p targetfile)
          ;; Use an existing index file or send a directory index
          (let* ((indexfile
                  (loop for i in elnode-webserver-index
                        if (member i (directory-files targetfile))
                        return i)))
            (if indexfile
                (elnode-send-file httpcon (concat targetfile "/" indexfile))
              (let ((index (elnode--webserver-index
                            docroot
                            targetfile
                            pathinfo)))
                (elnode-http-start httpcon 200 '("Content-type" . "text/html"))
                (elnode-http-return httpcon index))))
        ;; Send a file.
        (elnode-send-file httpcon targetfile)))))

(defun elnode-webserver-handler-maker (&optional docroot extra-mime-types)
  "Make a webserver handler possibly with the DOCROOT and EXTRA-MIME-TYPES.

Returns a proc which is the handler. The handler serves files out
of the docroot and marks them with the content types that Emacs
knows about. You can add extra content types for the webserver
just by supplying an alist of mime-types and extensions for
EXTRA-MIME-TYPES.

The webserver handler also creates file indexes.

The webserver uses `elnode-test-path' to make sure that the
request does not go above the DOCROOT."
  ;;; REQUIRES LEXICAL SCOPE
  (let ((my-docroot (or docroot elnode-webserver-docroot))
        (my-mime-types (or extra-mime-types
                           elnode-webserver-extra-mimetypes)))
    ;; Return the proc
    (lambda (httpcon)
      (elnode--webserver-handler-proc httpcon my-docroot my-mime-types))))

;;;###autoload
(defun elnode-webserver (httpcon)
  "A simple webserver that serves documents out of `elnode-webserver-docroot'.

This is just an example of an elnode webserver, but it may be all
that is needed most of the time.

See `elnode-webserver-handler-maker' for more possibilities for
making webserver functions.

HTTPCON is the HTTP connection to the user agent."
  (elnode--webserver-handler-proc
   httpcon
   elnode-webserver-docroot
   elnode-webserver-extra-mimetypes))


;; Wiki stuff

(require 'creole nil 't)
(require 'vc)

(defgroup elnode-wikiserver nil
  "A Wiki server written with Elnode."
  :group 'elnode)

(defcustom elnode-wikiserver-wikiroot "~/wiki"
  "The default root for the Elnode wiki files."
  :type '(directory)
  :group 'elnode-wikiserver)

(defcustom elnode-wikiserver-body-header
  "<div id='top'></div>"
  "HTML BODY preamable of a rendered Wiki page."
  :type '(string)
  :group 'elnode-wikiserver)

(defcustom elnode-wikiserver-body-footer
  "<div id='footer'>
<form action='{{page}}' method='POST'>
<fieldset>
<legend>Edit this page</legend>
<textarea  cols='80' rows='20' name='wikitext'>
{{text}}
</textarea><br/>
<input type='text' name='comment' value=''/>
<input type='submit' name='save' value='save'/>
<input type='submit' name='preview' value='preview'/>
</fieldset>
</form>
</div>"
  "HTML BODY footter for a rendered Wiki page."
  :type '(string)
  :group 'elnode-wikiserver)

(defun elnode--wiki-call (out-buf page-text page)
  "Call a wiki page sending output OUT-BUF.

The page is faked with PAGE-TEXT."
  (flet
      ((elnode--worker-lisp-helper (child-lisp)
         `((progn
             (require 'creole)
             (require 'cl)
             (flet ((creole--get-file (filename)
                      (let ((buf (get-buffer-create "wikibuf")))
                        (with-current-buffer buf
                          (insert ,page-text))
                        buf)))
               ,@child-lisp)))))
    (elnode-wait-for-exit
     (elnode-worker-elisp
         out-buf
         ((target page)
          (page-info page)
          (header elnode-wikiserver-body-header)
          (footer elnode-wikiserver-body-footer))
       (require 'creole)
       (creole-wiki
        target
        :destination t
        :variables `((page . ,page-info))
        :body-header header
        :body-footer footer)))))


(defun elnode-wiki-send (httpcon wikipage &optional pageinfo)
  "A very low level Wiki handler.

Sends the WIKIPAGE to the HTTPCON.

If PAGEINFO is specified it's the HTTP path to the Wiki page."
  (elnode-http-start httpcon 200 `("Content-type" . "text/html"))
  (let ((page (or pageinfo (elnode-http-pathinfo httpcon))))
    (elnode-worker-elisp
        httpcon
        ((target wikipage)
         (page-info page)
         (header elnode-wikiserver-body-header)
         (footer elnode-wikiserver-body-footer))
      (require 'creole)
      (creole-wiki
       target
       :destination t
       :variables `((page . ,page-info))
       :body-header header
       :body-footer footer))))

(defun elnode-wiki-handler (httpcon wikiroot)
  "A low level handler for Wiki operations.

Send the Wiki page requested, which must be a file existing under
the WIKIROOT, back to the HTTPCON."
  (elnode-method
    (GET
     (elnode-docroot-for wikiroot
       with target-path
       on httpcon
       do
       (if (equal target-path (concat wikiroot "/"))
           (elnode-wiki-send httpcon (concat wikiroot "/index.creole"))
         (elnode-wiki-send httpcon target-path))))
    (POST
     (let* ((path (elnode-http-pathinfo httpcon))
            (comment (elnode-http-param httpcon "comment"))
            (text (replace-regexp-in-string
                   "\r" "" ; browsers send text in DOS line ending format
                   (elnode-http-param httpcon "wikitext")))
            (page (if path
                      (save-match-data
                        (string-match "/wiki/\\(.*\\)$" path)
                        (match-string 1 path)))))
       (if (not (elnode-http-param httpcon "preview"))
           ;; A save request in which case save the new text and then
           ;; send the wiki text.
           (let* ((file-name (concat wikiroot "/" page))
                  (buffer (find-file-noselect file-name)))
             (with-current-buffer buffer
               (erase-buffer)
               (insert text)
               (save-buffer)
               (let ((git-buf
                      (get-buffer-create
                       (generate-new-buffer-name
                        "* elnode wiki commit buf *"))))
                 (shell-command
                  (format "git commit -m '%s' %s" comment file-name)
                  git-buf)
                 (kill-buffer git-buf))
               (elnode-wiki-send httpcon file-name)))
         ;; Might be a preview request in which case send back the WIKI
         ;; text that's been sent.
         (with-temp-file "/tmp/preview"
           (insert text))
         (elnode-wiki-send httpcon "/tmp/preview" path))))))

(defun elnode-wikiserver-test ()
  "Test whether we should serve Wiki or not."
  (featurep 'creole))

;;;###autoload
(defun elnode-wikiserver (httpcon)
  "Serve Wiki pages from `elnode-wikiserver-wikiroot'.

HTTPCON is the request.

The Wiki server is only available if the `creole' package is
provided. Otherwise it will just error."
  (if (elnode-wikiserver-test)
      (elnode-wiki-handler httpcon elnode-wikiserver-wikiroot)
    (elnode-send-500 httpcon "The Emacs feature 'creole is required.")))


;;; Main customization stuff

;;;###autoload
(defcustom elnode-init-port 8000
  "The port that `elnode-init' starts the default server on."
  :group 'elnode)

(defcustom elnode-init-host "localhost"
  "The host that `elnode-init' starts the default server listening on."
  :group 'elnode)

;;;###autoload
(defun elnode-init ()
  "Bootstraps the elnode environment when the Lisp is loaded.

It's useful to have elnode start automatically... on Lisp
load.  If the variable `elnode-init-port' is set then this
function will launch a server on it.

The server is started with `elnode-hostpath-default-handler' as
the handler and listening on `elnode-init-host'"
  (interactive)
  (if elnode-init-port
      (condition-case nil
          (elnode-start
           'elnode-hostpath-default-handler
           :port elnode-init-port
           :host elnode-init-host)
        (error
         (elnode-error
          "elnode-init: can't start - port %d has something attached already"
          elnode-init-port))))
  ;;(if (not elnode--defer-timer)
  ;;    (elnode--init-deferring))
  )

;;;###autoload
(defcustom elnode-do-init 't
  "Should elnode start a server on load?

The server that is started is controlled by more elnode
customizations.

`elnode-hostpath-default-table' defines the mappings from
hostpath regexs to handler functions. By default elnode ships
with this customization setup to serve the document root defined
in `elnode-webserver-docroot', which by default is ~/public_html."
  :group 'elnode
  :type '(boolean)
  )

;;;###autoload
(defvar elnode--inited nil
  "Records when elnode is initialized.
This is autoloading mechanics, see the eval-after-load for doing init.")

;; Auto start elnode if we're ever loaded
;;;###autoload
(eval-after-load 'elnode
  (if (and elnode-do-init (not elnode--inited))
      (progn
        (elnode-init)
        (setq elnode--inited nil))))

(provide 'elnode)

;;; elnode.el ends here
