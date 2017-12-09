;;; IMPORTANT!!!

;; The following file is meant for testing, not usage! It has been
;; heavily modified, so the original author should not be blaimed (or
;; even bothered) by any bug that happens to be in this version.

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


;;; Commentary:
;;
;; This is an elisp version of the popular node.js asynchronous
;; webserver toolkit.
;;
;; You can define HTTP request handlers and start an HTTP server
;; attached to the handler.  Many HTTP servers can be started, each
;; must have its own TCP port.  Handlers can defer processing with a
;; signal (which allows comet style resource management)
;;
;; See elnode-start for how to start an HTTP server.

;;; Code:

(require 'fakir)
(require 'mm-encode)
(require 'mailcap)
(require 'mail-parse) ; for mail-header-parse-content-type
(require 'url-util)
(require 'kv)
(require 's)
(require 'dash)
(require 'rx)
(require 'web)
(require 'json)
(require 'db)
(require 'dired) ; needed for the setup
(require 'tabulated-list)
(require 'noflet)

(eval-when-compile (require 'cl))

(require 'names)
(defconst ELNODE-FORM-DATA-TYPE "application/x-www-form-urlencoded"
  "The type of HTTP Form POSTs.")

(defconst http-referrer 'referer
  "Helper to bypass idiot spelling of the word `referrer'.")


;; Customization stuff

(defgroup elnode nil
  "An extensible asynchronous web server for Emacs."
  :group 'applications)



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
   (indent 1)
   (debug t))
  `(let ((elnode--cookie-store (make-hash-table :test 'equal)))
     (noflet ((elnode/get-server-prop (proc key)
                                      (cond
                                       ((eq key :elnode-http-handler)
                                        ,handler))))
       ,@body)))

(defmacro with-elnode-mock-httpcon (symbol elnode-plist &rest body)
  "Mock an HTTP connection for SYMBOL and evaluate BODY.

ELNODE-PLIST is either `nil' or a list of elnode properties, such
as `:elnode-method'."
  (declare
   (debug (sexp sexp &rest form))
   (indent 2))
  `(fakir-mock-process ,symbol ()
                       (set-process-plist ,symbol (list (make-hash-table :test 'eq)))
                       (elnode/con-put ,symbol ,@elnode-plist)
                       (progn ,@body)))

(defmacro with-stdout-to-elnode (httpcon &rest body)
  "Execute BODY so that any output gets sent to HTTPCON."
  (declare
   (debug (sexp &rest form))
   (indent defun))
  (let ((hv (make-symbol "httpconvar"))
        (val (make-symbol "value")))
    `(with-temp-buffer
       (let ((,hv ,httpcon)
             (standard-output (current-buffer)))
         (let ((,val (progn ,@body)))
           (elnode-http-return ,hv (buffer-string)))))))

(defmacro if-elnode-auth (httpcon scheme authd &rest anonymous)
  "Check the HTTPCON for SCHEME auth and eval AUTHD.

If the auth fails then evaluate ANONYMOUS instead.

When evaling AUTHD the `:auth-username' property of the process is set
to the user who authenticated."
  (declare
   (debug (sexp sexp form body))
   (indent 2))
  (let ((httpconv (make-symbol "httpconv")))
    `(let ((,httpconv ,httpcon)
           (scheme-list
            (gethash ,scheme
                     elnode--defined-authentication-schemes)))
       (if (eq :cookie (plist-get scheme-list :test))
           (condition-case token
               (let* ((cookie (plist-get scheme-list :cookie-name))
                      (username
                       (elnode-auth-cookie-check ,httpconv :cookie-name cookie)))
                 (elnode/con-put ,httpconv :auth-username username)
                 ;; Do whatever the code was now.
                 ,authd)
             ;; On auth failure do the ELSE
             (elnode-auth-token (progn ,@anonymous)))
         ;; Not a cookie test - not sure what to do...
         (error 'elnode-not-a-cookie)))))

(defmacro with-elnode-auth (httpcon scheme &rest body)
  "Protect code with authentication using HTTPCON and SCHEME.

This macro protects code in a handler with a check for an
authenticated request (the check is configurable).  If the check
fails then an appropriate action is taken; for example, sending a
login page.

SCHEME is the authentication scheme to use as defined by
`elnode-auth-define-scheme'."
  (declare (debug (sexp sexp body))
           (indent 2))
  (let ((httpconv (make-symbol "httpconv")))
    `(let ((,httpconv ,httpcon))
       (if-elnode-auth ,httpconv ,scheme
                       (progn ,@body)
                       (let ((to
                              (cond
                               (;; We have a wrapper... other lists other
                                ;; than wrappers are probably possible; we
                                ;; should qualify the test here to be
                                ;; wrapper specific
                                (listp (plist-get scheme-list :redirect))
                                (format
                                 "%s?redirect=%s"
                                 (elt (plist-get scheme-list :redirect) 3)
                                 (elnode-http-pathinfo ,httpconv)))
                               ;; A plain string can be used directly
                               ((stringp (plist-get scheme-list :redirect))
                                (plist-get scheme-list :redirect))
                               (t
                                (error
                                 ":redirect MUST be  a list or a string")))))
                         (elnode-send-redirect ,httpconv to))))))

(defun elnode/con-lookup (con attr)
  "Dynamic lookup."
  (gethash attr (car (process-plist con))))

(defmacro elnode/con-put (con attr value &rest other)
  "Put ATTR with VALUE into an array on CON's plist.

If OTHER is specified it is other pairs of attribute and value."
  (declare (indent 1)
           (debug (sexp sexp form &rest sexp)))
  (let ((valv (make-symbol "val"))
        (conv (make-symbol "con")))
    `(let* ((,valv ,value)
            (,conv ,con)
            (convec
             (or (car (process-plist ,conv))
                 (car (set-process-plist
                       ,conv (list (make-hash-table :test 'eq)))))))
       (puthash ,attr ,valv convec)
       ,@(when other
           (loop for (name val) on other by 'cddr
                 collect `(puthash ,name ,val convec))))))

(defmacro elnode/con-get (con attr)
  "Alternative implementation of `process-get'."
  (let ((conv (make-symbol "con")))
    `(let* ((,conv ,con)
            (convec
             (or (car (process-plist ,conv))
                 (car (set-process-plist
                       ,conv (list (make-hash-table :test 'eq)))))))
       (gethash ,attr convec))))

(defun elnode/get-server-prop (process key)
  "Get the value of the KEY from the server attached to PROCESS.

Server properties are bound with `elnode-start' which sets up
`elnode--log-fn' to ensure that all sockets created have a link
back to the server."
  (let* ((server (elnode/con-get process :server)))
    (elnode/con-lookup server key)))

(defun elnode/proc-log (server-proc client-proc msg)
  (set-process-plist client-proc (list (make-hash-table :test 'eq)))
  (elnode/con-put client-proc :server server-proc))

(defmacro elnode/case (expr &rest clauses)
  "A better `case' implementation."
  (declare (indent 1)(debug (form &rest (sexp body))))
  (let* ((backwards (reverse clauses))
         (last-clause (car backwards))
         (other-clauses (cdr backwards))
         (else-clause (when (eq t (car last-clause)) last-clause)))
    `(catch :escapesym
       (let ((value (progn ,expr)))
         ,@(let (collected)
             (dolist (c (if else-clause other-clauses clauses) collected)
               (setq collected
                     (cons `(when (eq ,(car c) value)
                              (throw :escapesym (progn ,@(cdr c))))
                           collected))))
         ,(if else-clause `(throw :escapesym ,@(cdr else-clause)))))))

(defun elnode/get-or-make-con-buffer (httpcon)
  (or
   (process-buffer httpcon)
   (let* ((port (cadr (process-contact httpcon)))
          (buf (get-buffer-create (format " *elnode-request-%s*" port))))
     (set-process-buffer httpcon buf)
     (process-buffer httpcon))))

(defun elnode/make-service (host port service-mappings request-handler defer-mode)
  "Make an actual server TCP or Unix PORT.

If PORT is a number then a TCP port is made on the specified HOST
on the PORT.

If PORT is a string a Unix socket is made in \"/tmp/\" and HOST
is ignored."
  (let* ((name (format "*elnode-webserver-%s:%s*" host port))
         (an-buf (get-buffer-create name))
         (unix-sock-file-name (unless (numberp port) (concat "/tmp/" port)))
         (proc-args
          (list
           :name name
           :buffer an-buf
           :server (if (numberp port) 300 't)
           :nowait 't
           :host (cond
                  ((not (numberp port)) nil)
                  ((equal host "localhost") 'local)
                  ((equal host "*") nil)
                  (t host))
           :coding '(raw-text-unix . raw-text-unix)
           :family (if (numberp port) 'ipv4 'local)
           :service (if (numberp port) port unix-sock-file-name)
           :filter 'elnode--filter
           ;;:sentinel 'elnode--sentinel
           :log 'elnode/proc-log))
         (proc (apply 'make-network-process proc-args)))
    (elnode/con-put proc
      :elnode-service-map service-mappings
      :elnode-http-handler request-handler
      :elnode-defer-mode defer-mode)
    proc))

(define-namespace elnode-

(defvar server-socket nil
  "Where we store the server sockets.

This is an alist of proc->server-process:

  (port . process)")


(defcustom init-port 8000
  "The port that `elnode-init' starts the default server on."
  :group 'elnode)

(defcustom init-host "localhost"
  "The default host for the default webserver.

Also used as the default host for `elnode-make-webserver'.

See `elnode-init' for more details."
  :group 'elnode)


;;;###autoload
(defconst config-directory
  (expand-file-name (concat user-emacs-directory "elnode/"))
  "The config directory for elnode to store peripheral files.

This is used as a base for other constant directory or file
names (the elnode auth database is a file in this directory, the
elnode webserver has a docroot directory in this directory).

It is based on the `user-emacs-directory' which always seems to
be set, even when emacs is started with -Q.")

;; Error log handling

(defun join (&rest parts)
  "Path join the parts together.

EmacsLisp should really provide this by default."
  (let* (savedpart
         (path
          (loop for p in parts
                concat
                (when (> (length p) 0)
                  (setq savedpart p)
                  (file-name-as-directory p)))))
    (if (equal (elt savedpart (- (length savedpart) 1)) ?\/)
        path
      (substring path 0 (- (length path) 1)))))

(defun -dir-setup (dir default default-file-name
                       &optional target-file-name
                       &rest other-files)
  "Install a DIR and DEFAULT-FILE-NAME if it's not setup already.

This is a packaging helper.  It helps an ELPA package install
files from it's package base into the user's Emacs.  If the DIR
is specified under `user-emacs-directory'.

DIR is the directory to install, DEFAULT is the default for that
directory, unless DIR equals DEFAULT nothing is done.

DEFAULT-FILE-NAME is the name of the file that will be installed
in DIR.  It is the expected name of the source file inside the
package.  Unless TARGET-FILE-NAME is specified it is also the
name the installed file will be given.  If the TARGET-FILE-NAME
is specified then that is the the name the file is installed as.

If OTHER-FILES is present it is treated as a list of other
filenames to copy to the DIR."
  (when  (and
          (equal
           dir
           default)
          (not (file-exists-p dir)))
    ;; Do install
    (let ((source-default-file
           (concat
            (file-name-directory
             (or (buffer-file-name)
                 (symbol-file 'elnode--dir-setup))) ; this not very portable
            ;; This should probably tie in with the makefile somehow
            default-file-name)))
      (when (and source-default-file
                 (file-exists-p source-default-file))
        (let ((to (concat
                   dir
                   (or target-file-name default-file-name))))
          (make-directory dir t)
          (message "copying %s elnode wiki default page to %s" dir to)
          (dired-copy-file source-default-file to nil)
          (when other-files
            (noflet ((resolve-filename (file)
                                       (if (file-name-absolute-p file)
                                           file
                                         (concat
                                          (file-name-directory
                                           source-default-file)
                                          file))))
                    (loop for file in other-files
                          ;; does the file exist?
                          if (and file (file-exists-p (resolve-filename file)))
                          do
                          (dired-copy-file
                           ;; from...
                           (resolve-filename file)
                           ;; to...nd
                           (concat dir (file-name-nondirectory file))
                           nil)))))))))

(defun -protected-load (feature dir)
  "Try and require FEATURE, if it fails try and load."
  (condition-case err
      (require feature)
    (file-error (progn
                  (load
                   (concat dir (symbol-name feature) ".el"))
                  (require feature)))))

;;;###autoload
(defmacro app (dir-var &rest features)
  "A macro that sets up the boring boilerplate for Elnode apps.

This sets up lexical binding, captures the module's parent
directory in DIR-VAR, requires `cl' and any other features you
list.  Use it like this:

 (elnode-app my-app-dir esxml mongo-elnode)

Once used you can access the variable `my-app-dir' as the dirname
of your module (which is useful for serving files and such)."
  (declare (indent 1))
  (let ((dir-var-v (make-symbol "dv")))
    `(let ((,dir-var-v (file-name-directory
                        (or (buffer-file-name)
                            load-file-name
                            default-directory))))
       (setq lexical-binding t)
       (defconst ,dir-var ,dir-var-v)
       (require 'cl)
       (require 'elnode)
       ,@(loop for f in features
               collect
               `(elnode--protected-load
                 (quote ,f) ,dir-var-v)))))

(defcustom log-files-directory nil
  "The directory to store any Elnode log files.

If this is not-nil (in which case logs are not saved at all) it
must be the name of a directory Elnode can use for storing logs.
If a directory is specified but it does not exist it is created."
  :group 'elnode
  :type '(choice (const :tag "Off" nil)
                 directory))

(defvar log-buffer-position-written 0
  "The position in the log buffer written.

This is used by `elnode-log-buffer-log' to track what has been written
so far.")

(defvar log-buffer-max-size 1000
  "Maximum number of lines of log.")

(defvar log-buffer-datetime-format "%Y-%m-%dT%H:%M:%S"
  "The date time format used by `elnode-log-buffer-log'.")

(defun log-buffer-log (text buffer-or-name &optional filename)
  "Log TEXT to the BUFFER-OR-NAME saving the buffer in FILENAME.

BUFFER-OR-NAME is either a buffer or a string naming a buffer.
FILENAME is a filename to save the buffer into.  If the FILENAME
is not specified then we try to use the filename of the
BUFFER-OR-NAME.

If neither a buffer filename nor FILENAME is specified then an
error is generated.

The TEXT is logged with the current date and time formatted with
`elnode-log-buffer-datetime-format'."
  (let ((name (or filename (buffer-file-name (get-buffer buffer-or-name)))))
    (with-current-buffer (get-buffer-create buffer-or-name)
      (let ((buffer-read-only nil))
        (unless (assq
                 'elnode-log-buffer-position-written
                 (buffer-local-variables))
          (make-local-variable 'elnode-log-buffer-position-written)
          (setq log-buffer-position-written (make-marker))
          (set-marker log-buffer-position-written (point-min)))
        ;; To test this stuff we could rip these functions out into
        ;; separate pieces?
        (save-excursion
          (goto-char (point-max))
          (insert
           (format
            "%s: %s\n"
            (format-time-string log-buffer-datetime-format)
            text))
          ;; Save the file if we have a filename
          (when name
            (if (not (file-exists-p (file-name-directory name)))
                (make-directory (file-name-directory name) t))
            ;; could be switched to write-region - probably better
            (append-to-file log-buffer-position-written (point-max) name)
            (set-marker log-buffer-position-written (point-max)))
          ;; Truncate the file if it's grown too large
          (goto-char (point-max))
          (forward-line (- log-buffer-max-size))
          (beginning-of-line)
          (delete-region (point-min) (point)))))))

(defcustom error-log-to-messages t
  "Whether to send elnode logging through the messaging system."
  :group 'elnode
  :type '(boolean))

(defvar server-error-log "*elnode-server-error*"
  "The buffer where error log messages are sent.")

(defvar -do-error-logging t
  "Allows tests to turn off error logging.")

(defvar -http-send-string-debug nil
  "Whether to do error logging in `elnode-http-send-string'.

That is very high logging, probably a bad idea for anyone but an
elnode developer.")

(defun -get-error-log-buffer ()
  "Returns the buffer for the error-log."
  (get-buffer-create server-error-log))

(defmacro error (msg &rest args)
  "Log MSG with ARGS as an error.

This function is available for handlers to call.  It is also used
by elnode iteslf.

There is only one error log, in the future there may be more."
  `(when elnode--do-error-logging
     (let ((filename (elnode--log-filename "elnode-error"))
           (fmtmsg (format ,msg ,@args)))
       (elnode-log-buffer-log
        fmtmsg
        (elnode--get-error-log-buffer)
        filename)
       (when elnode-error-log-to-messages
         (message "elnode: %s" fmtmsg)))))

(defconst msg-levels (list :debug :info :status :warning)
  "Levels of message `elnode-msg' uses.")

(defmacro -posq (element lst)
  "Return the index in the LST of ELEMENT."
  (let ((elv (make-symbol "el")))
    `(let ((,elv ,element))
       (catch :escape
         (let ((i 0))
           (dolist (e ,lst)
             (when (eq e ,elv)
               (throw :escape i))
             (setq i (+ i 1)))
           nil)))))

(defmacro msg (level msg &rest args)
  "Log MSG to the error console with a particular LEVEL.

LEVEL is compared to `elnode--do-error-logging'."
  (declare (indent 2))
  `(when (or (eq t elnode--do-error-logging)
             (>= (elnode--posq ,level elnode-msg-levels)
                 (elnode--posq
                  (or elnode--do-error-logging (car elnode-msg-levels))
                  elnode-msg-levels)))
     (elnode-error ,msg ,@args)))

(defun -log-filename (logname)
  "Turn LOGNAME into a filename.

`elnode-log-files-directory' is used as the container for log files.

This function mainly exists to make testing easier."
  (when log-files-directory
    (expand-file-name
     (format "%s/%s"
             log-files-directory
             logname))))

(defvar log-access-format-path-width 20
  "How to truncate the path in the access log.")

(defun log-access-format-func (httpcon)
  "Standard access log format function."
  (format
   (concat
    "%s % 8d %s % "
    (number-to-string log-access-format-path-width)
    "s %s")
   (elnode/con-get httpcon :elnode-httpresponse-status)
   (or (elnode/con-get httpcon :elnode-bytes-written) 0)
   (http-method httpcon)
   (http-pathinfo httpcon)
   (format-time-string ""
                       (time-subtract (current-time)
                                      (elnode/con-get httpcon :elnode-http-started)))))

(defcustom log-access-default-formatter-function
  'elnode-log-access-format-func
  "The default access log formatter function.

This is used when there is no specific logger function for a
log-name."
  :group 'elnode
  :type 'function)

(defcustom log-access-alist nil
  "An association list of access log format functions for log names.

An access log format function receives the http connection and
should return a log line to be entered in the log buffer.

These override the default log formatter."
  :group 'elnode
  :type '(alist
          :key-type string
          :value-type function))

(defun log-access (logname httpcon)
  "Log the HTTP access in buffer LOGNAME.

This function is available for handlers to call.  It is also used
by elnode iteslf."
  (let* ((elnode-log-buffer-datetime-format "%Y-%m-%d-%H:%M:%S")
         (buffer-name (format "*%s-elnode-access*" logname))
         (filename (-log-filename logname))
         (formatter
          (or
           (kva logname log-access-alist)
           log-access-default-formatter-function))
         (formatted
          (when formatter
            (funcall formatter httpcon))))
    (log-buffer-log formatted buffer-name filename)))


;; Defer stuff

(progn
  ;; Sets up the elnode defer signal
  (put 'elnode-defer
       'error-conditions
       '(error elnode elnode-defer))
  (put 'elnode-defer
       'error-message
       "Elnode handler processing defered"))

(defvar -deferred '()
  "List of deferred pairs: (socket . handler).")

(defun defer-now (handler)
  "The function you call to defer processing of the current socket.

Pass in the current HANDLER.

FIXME: We could capture the current handler somehow? I think the
point is that whatever signals elnode-defer should be getting
control back when the deferred is re-processed."
  (signal 'elnode-defer handler))

(defmacro defer-until (guard &rest body)
  "Test GUARD and defer if it fails and BODY if it doesn't.

`httpcon' is captured in this macro which means the macro can
only be expanded where there is an inscope `httpcon'.

Inside the macro the symbol `elnode-defer-guard-it' is bound to
the value of the GUARD."
  (declare (indent 1))
  (let ((bv (make-symbol "bv"))
        (gv (make-symbol "gv"))
        (fv (make-symbol "fv")))
    `(let* ((,gv (lambda () ,guard))
            (elnode-defer-guard-it (funcall ,gv))
            (,bv (lambda (httpcon) ,@body))
            (,fv ; a y-combinator!
             (lambda (httpcon proc)
               (setq elnode-defer-guard-it (funcall ,gv))
               (if elnode-defer-guard-it
                   (funcall ,bv httpcon)
                 ;; the test failed we should defer again
                 (elnode-defer-now
                  (lambda (http-con)
                    (funcall proc http-con proc)))))))
       (if elnode-defer-guard-it
           (funcall ,bv httpcon)
         ;; The test failed, we should defer.
         (elnode-defer-now
          (lambda (httpcon) ; apply the y-combinator
            (funcall ,fv httpcon ,fv)))))))

(defun -deferred-add (httpcon handler)
  "Add the specified HTTPCON/HANDLER pair to the deferred list."
  (msg :info "deferred-add: adding a defer %s for %s" handler httpcon)
  (push (cons httpcon handler) -deferred))

(defun -deferred-process-open (httpcon handler)
  "Process the HANDLER with the known open HTTPCON."
  ;; (elnode-error "defer - just before calling the handler %s" handler)
  (funcall handler httpcon))


;; Log levels
(defconst log-debug 0)
(defconst log-info 1)
(defconst log-warning 2)
(defconst log-critical 3)

(defvar defer-processor-log-level log-critical
  "Log level of the defer processor.")

(defun -deferred-log (level msg &rest args)
  "Special log for deferreds"
  (when (>= level defer-processor-log-level)
    (msg :info (format "elnode-deferred-processor %s %s" msg args))))

(defvar defer-failure-hook nil
  "Hook called when a deferred socket fails.

The hook function is called with the http connection and the
failure state which either the symbol `closed' or the symbol
`failed'.")

(defconst -debug-with-backtraces nil
  "Feature switch to include backtrace debugging support.")

(defun -deferred-processor ()
  "Process the deferred queue."
  (let ((run (random 5000)) ; use this to disambiguate runs in the logs
        (new-deferred (list)))
    (-deferred-log log-info "start")
    (loop for pair in -deferred
          do
          (let ((httpcon (car pair))
                (handler (cdr pair)))
            (elnode/case (process-status httpcon)
                         ('open
                          (-deferred-log log-info
                                         "open %s %s" httpcon handler)
                          (condition-case signal-value
                              (-deferred-process-open httpcon handler)
                            ('elnode-defer
                             (push
                              (cons httpcon (cdr signal-value))
                              new-deferred))
                            (error
                             (-deferred-log
                              log-critical
                              "error %s - %s %S" httpcon signal-value
                              (if -debug-with-backtraces
                                  debugger-previous-backtrace
                                "")))))
                         ('closed
                          (-deferred-log log-info
                                         "closed %s %s" httpcon handler)
                          ;; Call any hook function for defer closes
                          (loop for hook-func in elnode-defer-failure-hook
                                do
                                (funcall hook-func httpcon 'closed)))
                         ('failed
                          (-deferred-log
                           log-info "failed %s %s" httpcon handler)
                          ;; Call any hook function for defer failures
                          (loop for hook-func in defer-failure-hook
                                do
                                (funcall hook-func httpcon 'failed)))
                         ;; Not sure how to do connect... same as open?
                         ;; ... or just put it back?
                         ('connect
                          (push
                           (cons httpcon handler)
                           new-deferred)))))
    (-deferred-log log-info "complete")
    ;; Set the correct queue
    (setq -deferred new-deferred)))

(defun deferred-queue-process ()
  (interactive)
  (-deferred-processor))

(defvar defer-on nil
  "Whether to do deferring or not.")

(defvar -defer-timer nil
  "The timer used by the elnode defer processing.

This is initialized by `elnode--init-deferring'.")

(defun -init-deferring ()
  "Initialize elnode defer processing.

Necessary for running comet apps."
  (setq -defer-timer
        (run-at-time "2 sec" 2 'elnode--deferred-processor)))

(defun deferred-queue-start ()
  "Start the deferred queue, unless it's running."
  (interactive)
  (unless defer-on
    (setq defer-on t))
  (unless -defer-timer
    (-init-deferring)))

(defun deferred-queue-stop ()
  "Stop any running deferred queue processor."
  (interactive)
  (when -defer-timer
    (cancel-timer -defer-timer)
    (setq -defer-timer nil)))

;;; Basic response mangling

(defcustom default-response-table
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

(defconst -default-response-groups
  '((1 . "Informing you of something.")
    (2 . "Ok.")
    (3 . "")
    (4 . "Bad.")
    (5 . "Error."))
  "Response codes for error code / 100.

These are designed to be used when a specific code is not
available.")

(defun -format-response (status &optional msg)
  "Format the STATUS and optionally MESSAGE as an HTML return."
  (format "<h1>%s</h1>%s\r\n"
          (cdr (or (assoc status default-response-table)
                   (assoc (/ status 100) -default-response-groups)
                   (assoc t default-response-table)))
          (if msg (format "<p>%s</p>" msg) "")))


;; Main control functions

(defun -http-parse-header (buffer start &optional non-header)
  "Parse a header from the BUFFER at point START.

The initial header may be parsed with this or if NON-HEADER is
sent then another header, such as a multipart header, may be read.

If the complete header has not been read then we throw to
`elnode-parse-http' with either `header' or `non-header'.

We return a list of the leader, which is the first line of the
header (which is not the header) followed by an alist of
headers."
  (with-current-buffer buffer
    (let ((hdrend (re-search-forward "\r\n\r\n" nil 't)))
      (when (not hdrend)
        (throw 'elnode-parse-http (or (and non-header 'non-header) 'header)))
      (let* ((lines
              (split-string
               (buffer-substring start hdrend)
               "\r\n"
               't))
             (status (car lines)) ;; the first line is the status line
             (header (cdr lines)) ;; the rest of the lines are the header
             (header-alist-strings
              (mapcar
               (lambda (hdrline)
                 (when (string-match
                        "\\([A-Za-z0-9_-]+\\):[ ]*\\(.*\\)"
                        hdrline)
                   (cons
                    (downcase (match-string 1 hdrline))
                    (match-string 2 hdrline))))
               header)))
        (list status header-alist-strings)))))


(defun -http-parse (process)
  "Parse the HTTP header for the PROCESS.

If the request is not fully complete (if the header has not
arrived yet or we don't have all the content-length yet for
example) this can throw `elnode-parse-http'.  The thing being
waited for is indicated.

Important side effects of this function are to add certain
process properties to the HTTP connection.  These are the result
of successful parsing."
  ;; FIXME - we don't need to do this - we should check for
  ;; header-parsed and avoid it we we can
  (with-current-buffer (process-buffer process)
    (save-excursion
      (goto-char (point-min))
      (destructuring-bind (leader alist-strings)
          (elnode--http-parse-header (current-buffer) (point-min))
        (let* ((hdrend (point))
               (alist-syms
                (kvalist-keys->symbols alist-strings :first-fn 'downcase))
               (content-len (assq 'content-length alist-syms)))
          ;; Check the content if we have it.
          (when content-len
            (let* ((available-content (- (point-max) hdrend)))
              (when (> (string-to-number (cdr content-len))
                       available-content)
                (throw 'elnode-parse-http 'content))))
          (elnode/con-put process
                          :elnode-header-end hdrend
                          :elnode-http-status leader
                          :elnode-http-header-syms alist-syms
                          :elnode-http-header alist-strings)))))
  ;; Return a symbol to indicate done-ness
  'done)

(defun -http-make-hdr (method resource &rest headers)
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
    (noflet ((header-name (hdr)
                          (if (symbolp (car hdr))
                              (symbol-name (car hdr))
                            (car hdr))))
            (format
             "%s %s HTTP/1.1\r\n%s\r\n%s"
             (upcase (if (symbolp method) (symbol-name method) method))
             resource
             (loop for header in headers
                   if (equal (header-name header) "body")
                   do (setq body (cdr header))
                   else
                   concat (format
                           "%s: %s\r\n"
                           (capitalize (header-name header))
                           (cdr header)))
             ;; If we have a body then add that as well
             (or body "")))))

(defsubst -call (handler con)
  (funcall handler con))

(defun -filter (process data)
  "Filtering DATA sent from the client PROCESS..

This does the work of finding and calling the user HTTP
connection handler for the request on PROCESS.

A buffer for the HTTP connection is created, uniquified by the
port number of the connection."
  (with-current-buffer (elnode/get-or-make-con-buffer process)
    (insert data)
    (elnode/case (catch 'elnode-parse-http (-http-parse process))
                 ('header (msg :info "filter: partial header data received"))
                 ('content (msg :info "filter: partial header data received"))
                 ('done
                  (save-excursion
                    (goto-char (elnode/con-get process :elnode-header-end))
                    (let ((handler (elnode/get-server-prop process :elnode-http-handler)))
                      (unwind-protect
                          (condition-case signal-value 
                              (funcall handler process)
                            ('elnode-defer ; see elnode-defer-now
                             (msg :info "filter: defer caught on %s" process)
                             ;; Check the timer, this is probably spurious but useful "for now"
                             (unless defer-on
                               (msg :info "filter: no defer timer for %s" process))
                             (elnode/case (elnode/get-server-prop process :elnode-defer-mode)
                                          (:managed
                                           (elnode/con-put process :elnode-deferred t)
                                           ;; the cdr of the sig value is the func
                                           (-deferred-add process (cdr signal-value)))
                                          (:immediate
                                           (msg :info "filter: immediate defer on %s" process)
                                           (funcall (cdr signal-value) process))))
                            ('t
                             (unless (elnode/con-get process :elnode-http-started)
                               (msg :info "filter: default handling %S" signal-value)
                               (process-send-string process (-format-response 500)))))
                        (if (and (not (elnode/con-get process :elnode-http-started))
                                 (not (elnode/con-get process :elnode-deferred)))
                            (process-send-string process (-format-response 500))
                          (when (elnode/con-get process :elnode-finished)
                            (unwind-protect
                                (progn
                                  (delete-process process)
                                  (kill-buffer (process-buffer process)))
                              (unless (eq 'closed (process-status process))
                                (msg :warning "elnode--filter failed at the end"))))))))))))

(defun -ip-addr->string (ip-addr)
  "Turn a vector IP-ADDR into a string form.

The vector form is produced by `process-contact' and includes the
port number."
  (destructuring-bind (a b c d port)
      (mapcar 'identity ip-addr)
    (format "%s.%s.%s.%s:%s" a b c d port)))

(defun get-remote-ipaddr (httpcon)
  "Return the remote IP address from the HTTPCON.

Returned as a dotted ip address followed by a colon separated
port number.  For example: \"127.0.0.1:8080\"."
  (let* ((remote (plist-get
                  (process-contact httpcon t)
                  :remote)))
    (-ip-addr->string remote)))

(defun server-info (httpcon)
  "Returns a string adress of the server host and port for HTTPCON.

For example: \"127.0.0.1:8000\" - localhost on port 8000."
  (-ip-addr->string
   (plist-get
    (process-contact (elnode/con-get httpcon :server) t)
    :local)))


;;; Testing stuff

(defvar -cookie-store nil
  "Cookie store for test servers.

This is a special defvar for dynamic overriding by
`with-elnode-mock-server'.")

(defun -alist-to-query (alist)
  "Turn an alist into a formdata/query string."
  (noflet ((web--key-value-encode (key value)
                                  "Encode a KEY and VALUE for url encoding."
                                  (cond
                                   ((or
                                     (numberp value)
                                     (stringp value))
                                    (format
                                     "%s=%s"
                                     (url-hexify-string (format "%s" key))
                                     (url-hexify-string (format "%s" value))))
                                   (t
                                    (format "%s" (url-hexify-string (format "%s" key))))))
           (web--to-query-string (object)
                                 "Convert OBJECT (a hash-table or alist) to an HTTP query string."
                                 ;; Stolen from web
                                 (mapconcat
                                  (lambda (pair)
                                    (web--key-value-encode (car pair) (cdr pair)))
                                  (cond
                                   ((hash-table-p object)
                                    (let (result)
                                      (maphash
                                       (lambda (key value)
                                         (setq result (append (list (cons key value)) result)))
                                       object)
                                      (reverse result)))
                                   ((listp object)
                                    object))
                                  "&")))
          (web--to-query-string alist)))

(defun -make-test-call (path method parameters headers)
  "Construct the HTTP request for a test call.

This should probably be merged with the stuff in the `web'
module."
  (let* ((query
          (if (and parameters (equal method "GET"))
              (format
               "?%s"
               (-alist-to-query parameters))
            ""))
         (http-path
          (if (equal query "")
              path
            (format "%s%s" path query)))
         (http-body
          (if (equal method "GET")
              nil
            (let ((param-data (-alist-to-query parameters)))
              (setq headers
                    (append
                     (list
                      (cons "Content-Type"
                            "application/x-www-form-urlencoded")
                      (cons "Content-Length"
                            (format "%d" (length param-data))))
                     headers))
              param-data))))
    (apply
     'elnode--http-make-hdr
     `(,method
       ,http-path
       ,@headers
       (body . ,http-body)))))

(defun -response-header-to-cookie-store (response)
  "Add Set-Cookie headers from RESPONSE to the cookie store."
  (let ((cookie-set (assoc "Set-Cookie" response)))
    (when cookie-set
      (let* ((cookie-value (car (split-string (cdr cookie-set) ";"))))
        (apply
         'puthash
         (append
          (split-string cookie-value "=")
          (list -cookie-store))))))
  -cookie-store)

(defun -cookie-store-to-header-value ()
  "Turn the current cookie store into a header.

The cookies in the header are sorted alphabetically - makes
testing easier."
  (let ((cookie-value
         (mapconcat
          (lambda (cookie)
            (format "%s=%s" (car cookie)
                    (url-hexify-string (cdr cookie))))
          (kvalist-sort
           (kvhash->alist -cookie-store)
           'string-lessp)
          "; ")))
    (unless (equal "" cookie-value)
      cookie-value)))

(defun* test-call (path
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

For header and parameter names, strings MUST be used currently.

During the test the variable `elnode-webserver-visit-file' is set
to `t' to ensure that Elnode does not pass fake HTTP connections
to external processes."
  (let ((fakir-mock-process-require-specified-buffer t))
    (fakir-mock-process :httpcon ()
                        (let ((req (-make-test-call
                                    path method parameters
                                    (append
                                     headers
                                     (let ((cookies (-cookie-store-to-header-value)))
                                       (when cookies
                                         (list (cons "Cookie" cookies)))))))
                              (http-con :httpcon)
                              (the-end nil)
                              (elnode-webserver-visit-file t))
                          (noflet ((process-send-eof (proc) (setq the-end 't))
                                   (process-status (proc) (if the-end 'closed 'open))
                                   (elnode/get-server-prop (proc prop)
                                                           (elnode/case prop
                                                                        (:elnode-defer-mode nil)
                                                                        (t (funcall this-fn proc prop))))
                                   ;; Do nothing - we want the test proc
                                   (delete-process (proc))
                                   ;; Again, do nothing, we want this buffer
                                   (kill-buffer (buffer) t))
                                  ;; FIXME - we should unwind protect this?
                                  (-filter http-con req)
                                  ;; Now we sleep till the-end is true
                                  (while (not the-end) (sit-for 0.1))
                                  (when the-end
                                    (-response-header-to-cookie-store
                                     (elnode/con-get http-con :elnode-httpresponse-header))
                                    ;; Could we add to the cookie store here?
                                    (list
                                     :result-string
                                     (with-current-buffer (fakir-get-output-buffer)
                                       (buffer-substring-no-properties (point-min) (point-max)))
                                     :buffer (process-buffer http-con)
                                     ;; These properties are set by elnode-http-start
                                     :status (elnode/con-get http-con :elnode-httpresponse-status)
                                     :header (elnode/con-get http-con :elnode-httpresponse-header))))))))


(defvar handler-history '()
  "The history of handlers bound to servers.")

(defvar port-history '()
  "The history of ports that servers are started on.")

(defvar host-history '()
  "The history of hosts that servers are started on.")

(defun ports ()
  "List of all ports currently in use by elnode."
  (mapcar 'car server-socket))

;;;###autoload
(defun* start (request-handler
               &key
               port
               (host "localhost")
               (defer-mode :managed)
               service-mappings)
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
    (elnode-http-start httpcon 200 '(\"Content-Type\" . \"text/html\"))
    (elnode-http-return httpcon \"<html><b>BIG!</b></html>\"))
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
elnode servers on the same port on different hosts.

DEFER-MODE may be used to control how deferred handlers are
managed for this server.

SERVICE-MAPPINGS is an alist of service resource symbols mapped
to integer port numbers.  This can be supplied to elnode-start to
allow it to map service resources defined by handlers to
different TCP ports and therefore different Emacs instances.

The list of SERVICE-MAPPINGS is also used to start ancilliary
port servers.  Ancilliary port servers should be automatically
stopped when the main server is stopped."
  (interactive
   (let ((handler (completing-read "Handler function: "
                                   obarray 'fboundp t nil nil))
         (port (read-number "Port: " 8000))
         (host (read-string "Host: " "localhost" 'elnode-host-history)))
     (list (intern handler) :port port :host host)))
  (let ((port (or port 8000))
        (host (or host "localhost")))
    (unless (assoc port server-socket)
      ;; Add a new server socket to the list
      (setq server-socket
            (cons
             (cons port
                   (let ((buf (get-buffer-create "*elnode-webserver*"))
                         (ancilliarys
                          (loop for (resource . port) in service-mappings
                                collect
                                (elnode/make-service
                                 host port service-mappings
                                 request-handler defer-mode)))
                         (main (elnode/make-service
                                host port service-mappings
                                request-handler defer-mode)))
                     ;; Add the link between the main and the ancilliarys
                     (elnode/con-put main :elnode-ancilliarys ancilliarys)
                     main))
             server-socket)))))

;; TODO: make this take an argument for the
(defun stop (port)
  "Stop the elnode server attached to PORT."
  (interactive
   (let ((prt
          (string-to-number
           (completing-read
            "Port: "
            (mapcar (lambda (n) (format "%s" n))
                    (ports))))))
     (list prt)))
  (let* ((server
          (or (assoc port server-socket)
              (assoc (format "%d" port) server-socket)))
         (port-to-kill (car-safe server)))
    (when server
      (message "deleting server process")
      (loop for ancilliary
            in (elnode/con-get (cdr server) :elnode-ancilliarys)
            do (delete-process ancilliary))
      ;; Now the main one
      (delete-process (cdr server))
      (setq server-socket
            ;; remove-if
            (let ((test (lambda (elem)
                          (equal (car elem) port-to-kill)))
                  (l server-socket)
                  result)
              (while (car l)
                (let ((p (pop l))
                      (r (cdr l)))
                  (if (not (funcall test p))
                      (setq result (cons p result)))))
              result)))))

(defun find-free-service ()
  "Return a free (unused) TCP port.

The port is chosen randomly from the ephemeral ports. "
  (let (myserver
        (port 50000)) ; this should be ephemeral base
    (while
        (not
         (processp
          (condition-case sig
              (setq myserver
                    (make-network-process
                     :name "*test-proc*"
                     :server t
                     :nowait 't
                     :host 'local
                     :service port
                     :family 'ipv4))
            (file-error
             (if (equal
                  "Cannot bind server socket address already in use"
                  (mapconcat 'identity (cdr sig) " "))
                 (setq port (+ 50000 (random 5000)))))))))
    (delete-process myserver)
    port))

(defun list-buffers ()
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

(defun time-encode (time-str)
  "Basic TIME-STR to time encoding."
  (apply 'encode-time (parse-time-string time-str)))


;; HTTP API methods

(defun -http-hdr (httpcon)
  "Return the header cons for the HTTPCON.

The status-line and the header alist."
  (cons
   (elnode/con-get httpcon :elnode-http-status)
   (elnode/con-get httpcon :elnode-http-header)))

(defun http-headers (httpcon)
  "Return the alist of headers from HTTPCON."
  (elnode/con-get httpcon :elnode-http-header))

(defun http-header (httpcon name &optional convert)
  "Get the header specified by NAME from the HTTPCON.

HEADER may be a string or a symbol.  If NAME is a symbol it is
case insensitve.

If optional CONVERT is specified it may specify a conversion,
currently supported conversions are:

 :time - to convert a time value properly"
  (let* ((key (if (symbolp name)
                  (intern (downcase (symbol-name name)))
                name))
         (hdr (if (symbolp key)
                  (elnode/con-get httpcon :elnode-http-header-syms)
                (elnode/con-get httpcon :elnode-http-header)))
         (val (cdr (assoc (if (stringp key) (downcase key) key) hdr))))
    (elnode/case convert
                 (:time
                  (when val
                    (time-encode val)))
                 (t
                  val))))

(defun* http-host (httpcon &key split just-host)
  "Return the HTTP `host' name header.

With SPLIT return a list of the hostname and any port part (the
port part might be empty if not specifically specified).  With
JUST-HOST return just the host-name part, dropping any port entirely."
  (let ((host (http-header httpcon "Host")))
    (cond
     (split
      (string-match "\\([^:]+\\)\\(:\\([0-9]+\\)\\)*" host)
      (list (match-string-no-properties 1 host)
            (match-string-no-properties 3 host)))
     (just-host
      (string-match "\\([^:]+\\)\\(:\\([0-9]+\\)\\)*" host)
      (match-string-no-properties 1 host))
     (t
      host))))

(defun http-cookies (httpcon)
  "Return the list of cookies attached to this HTTPCON.

The list of cookies is an alist."
  (or
   (elnode/con-get httpcon :elnode-http-cookie-list)
   (let* ((cookie-hdr (http-header httpcon 'Cookie))
          (lst (when cookie-hdr
                 (kvalist-sort
                  (mapcar
                   (lambda (pair)
                     (cons
                      (url-unhex-string (car pair))
                      (url-unhex-string (cdr pair))))
                   (url-parse-args cookie-hdr))
                  'string-lessp))))
     (elnode/con-put httpcon :elnode-http-cookie-list lst)
     lst)))

(defun http-cookie (httpcon name &optional cookie-key)
  "Return the cookie value for HTTPCON specified by NAME.

The cookie is a cons:

  name . value

If COOKIE-KEY is `t' then only the value is returned, else the
cons is returned."
  (let* ((cookie-list (http-cookies httpcon))
         (cookie (assoc-string name cookie-list)))
    (if cookie-key
        (cdr cookie)
      cookie)))

(defconst -http-status-line-rx
  (rx (and (group-n 1 (or "GET" "HEAD" "POST" "DELETE" "PUT"))
           " "
           (group-n 2 (1+ (any "A-Za-z0-9+&=?./:;-"))) ; FIXME - get this from the spec?
           " "
           "HTTP/"
           (group-n 3 (and "1." (1+ (any "0-9"))))))
  "The regex used to match the status line.")

(defun -http-parse-status (httpcon &optional property)
  "Parse the status line of HTTPCON.

If PROPERTY is non-nil, then return that property."
  (let* ((http-line (elnode/con-get httpcon :elnode-http-status)))
    (save-match-data
      (when (and http-line
                 (string-match -http-status-line-rx http-line))
        (elnode/con-put httpcon
                        :elnode-http-method (match-string 1 http-line)
                        :elnode-http-resource (match-string 2 http-line)
                        :elnode-http-version (match-string 3 http-line)
                        :elnode-http-parsed-time (current-time))
        (when property
          (elnode/con-lookup httpcon property))))))

(defun -http-parse-resource (httpcon &optional property)
  "Convert the specified resource to a path and a query."
  (let ((resource
         (or
          (elnode/con-get httpcon :elnode-http-resource)
          (-http-parse-status
           httpcon :elnode-http-resource))))
    (save-match-data
      (if (or
           ;; root pattern with 
           (string-match "^\\(/\\)\\(\\?.*\\)*$" resource)
           ;; /somepath or /somepath/somepath
           (string-match "^\\(/[^?]+\\)\\(\\?.*\\)*$" resource))
          (let ((path (url-unhex-string (match-string 1 resource))))
            (elnode/con-put httpcon :elnode-http-pathinfo path)
            (when (match-string 2 resource)
              (let ((query (match-string 2 resource)))
                (string-match "\\?\\(.+\\)" query)
                (if (match-string 1 query)
                    (elnode/con-put
                     httpcon
                     :elnode-http-query
                     (match-string 1 query))))))
        ;; Else it might be a more exotic path
        (elnode/con-put httpcon :elnode-http-pathinfo resource))))
  (when property
    (elnode/con-lookup httpcon property)))

(defun http-pathinfo (httpcon)
  "Get the PATHINFO of the request.

The PATHINFO is the CGI term for the part of the path that is not
the hostname or the query; the part that relates to the path."
  (or
   (elnode/con-get httpcon :elnode-http-pathinfo)
   (-http-parse-resource httpcon :elnode-http-pathinfo)))

(defun http-query (httpcon)
  "Get the QUERY of the request."
  (or
   (elnode/con-get httpcon :elnode-http-query)
   (-http-parse-resource httpcon :elnode-http-query)))

(defun -http-param-part-decode (param-thing)
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

(defun -http-query-to-alist (query)
  "Crap parser for HTTP QUERY data.

Returns an association list."
  (--map
   (if (string-match "\\([^=]+\\)\\(=\\(.*\\)\\)*" it)
       (cons
        (-http-param-part-decode (match-string 1 it))
        (if (match-string 2 it)
            (-http-param-part-decode (match-string 3 it))
          nil)))
   (split-string query "&")))

(defun -alist-merge (a b &optional operator)
  "Merge two association lists non-destructively.

A is considered the priority (its elements go in first)."
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

(defun -http-mp-find-boundary (boundary)
  "Find the boundary string from point."
  (let ((boundary-rx
         (rx-to-string `(seq "\r\n--" ,boundary))))
    (save-match-data
      (when (re-search-forward boundary-rx nil t)
        (let ((mpt (match-beginning 0)))
          ;; Return status indicator and the start match point
          (list
           (if (save-excursion
                 (goto-char (line-beginning-position))
                 (looking-at (rx-to-string `(seq bol "--" ,boundary "--"))))
               :done :continue)
           (progn (goto-char mpt) mpt)))))))

(defun -http-mp-decode (buffer header-end-pt boundary)
  "Decode a multipart/form-data upload with BOUNDARY in BUFFER."
  (with-current-buffer buffer
    (goto-char (- header-end-pt 2)) ; moves back over the \r\n
    (loop while (eq (car next-boundary) :continue)
          with next-boundary = (elnode--http-mp-find-boundary boundary)
          collect
          (destructuring-bind (leader alist)
              (elnode--http-parse-header (current-buffer) (point) t)
            (let* ((cde
                    (mail-header-parse-content-disposition
                     (kva "content-disposition" alist)))
                   (name (kva 'name (cdr cde)))
                   (filename (kva 'filename (cdr cde)))
                   (pt (point)))
              ;; Find the next end point
              (setq next-boundary
                    (elnode--http-mp-find-boundary boundary))
              (let* ((lbp (line-beginning-position))
                     (content (buffer-substring pt (cadr next-boundary)))
                     (content-data
                      (if (equal
                           "base64"
                           (downcase (or (kva "content-transfer-encoding" alist) "")))
                          (base64-decode-string content)
                        content))
                     (content-object
                      (cond
                       ((not filename) content-data)
                       (t (propertize content-data :elnode-filename filename)))))
                (cons name content-object)))))))

(defun -http-post-mp-decode (httpcon parsed-content-type)
  "Decode the HTTP POST multipart thing on HTTPCON."
  (let ((boundary (kva 'boundary (cdr parsed-content-type)))
        (buf (process-buffer httpcon))
        (hdr-end-pt (elnode/con-get httpcon :elnode-header-end)))
    (-http-mp-decode buf hdr-end-pt boundary)))

(defun -http-post-body (httpcon)
  "Get the HTTP POST body."
  (with-current-buffer (process-buffer httpcon)
    ;; (buffer-substring (point-min) (point-max)) ;debug
    (buffer-substring
     ;; we might have to add 2 to this because of trailing \r\n
     (elnode/con-get httpcon :elnode-header-end)
     (point-max))))

(defun -http-post-to-alist (httpcon)
  "Parse the POST body."
  ;; FIXME: this is ONLY a content length header parser -- it should
  ;; also cope with transfer encodings.
  (let* ((content-type (http-header httpcon 'content-type))
         (parsed-type
          (when content-type
            (mail-header-parse-content-type content-type))))
    (if (equal "multipart/form-data" (car parsed-type))
        (-http-post-mp-decode httpcon parsed-type)
      ;; Else it's a non-multipart request
      (-http-query-to-alist (-http-post-body httpcon)))))

(defun http-params (httpcon &rest names)
  "Get an alist of the parameters in the request.

If the method is a GET then the parameters are from the url.  If
the method is a POST then the parameters may come from either the
url or the POST body or both:

 POST /path?a=b&x=y
 a=c

would result in:

 '((\"a\" \"b\" \"c\")(\"x\" . \"y\"))

If NAMES are specified it is a filter list of symbols or strings
which will be returned.

File upload with Multipart/form-data is supported by Elnode.
Uploaded files are present in the params the same as any other
param except for the fact that uploaded file params have a text
property :elnode-filename on them:

  (get-text-property 0 :elnode-filename
    (elnode-http-param httpcon \"myfile\")) => '/somefile.txt'

The value comes from the \"Content-Disposition\" header in the
multipart upload."
  (loop for pair in
        (or
         (elnode/con-get httpcon :elnode-http-params)
         (let ((query (http-query httpcon)))
           (let ((alist (if query
                            (-http-query-to-alist query)
                          '())))
             (if (equal "POST" (http-method httpcon))
                 ;; If we're a POST we have to merge the params
                 (progn
                   (setq alist
                         (-alist-merge
                          alist
                          (-http-post-to-alist httpcon)
                          'assoc))
                   (elnode/con-put httpcon :elnode-http-params alist)
                   alist)
               ;; Else just return the query params
               (elnode/con-put httpcon :elnode-http-params alist)
               alist))))
        if (or (not names)
               (memq (intern (car pair)) names)
               (member (car pair) names))
        collect pair))

(defun http-param (httpcon name &optional default)
  "Get the parameter named NAME from the request.

If the parameter came from a file upload it has a text property
indicating the filename:

  (get-text-property 0 :elnode-filename
    (elnode-http-param httpcon \"myfile\")) => '/somefile.txt'

If the parameter is not present and DEFAULT is present then
return DEFAULT instead of `nil'."
  (let* ((params (http-params httpcon))
         (param-pair
          (assoc
           (if (symbolp name) (symbol-name name) name)
           params)))
    ;; Should we signal when we don't have a param?
    (if param-pair
        (cdr param-pair)
      default)))

(defun http-method (httpcon)
  "Get the HTTP request method (GET, PUT, etc...) as a string."
  (or
   (elnode/con-get httpcon :elnode-http-method)
   (-http-parse-status httpcon :elnode-http-method)))

(defun http-version (httpcon)
  "Get the PATHINFO of the request."
  (or
   (elnode/con-get httpcon :elnode-http-version)
   (-http-parse-status httpcon :elnode-http-version)))

(defun http-send-string (httpcon str)
  "Send STR to HTTPCON, doing chunked encoding."
  (msg :debug
       "elnode-http-send-string %s [[%s]]" httpcon (s-truncate 10 str))
  (let ((len (string-bytes str)))
    (elnode/con-put httpcon :elnode-bytes-written
                    (+ len (or (elnode/con-get httpcon :elnode-bytes-written) 0)))
    ;; FIXME Errors can happen here, because the socket goes away.. it
    ;; would be nice to trap them and report and then re-raise them.
    (if (eq (process-status httpcon) 'open)
        (condition-case err
            (process-send-string
             httpcon
             (format "%x\r\n%s\r\n" (length str) (or str "")))
          (error
           (msg :warning
                "elnode-http-send-string failed to send [%s] on %s (%s)"
                (length str) httpcon (process-status httpcon))))
      (msg :warning
           "elnode-http-send-string can't print [%s] because %s is %s"
           (length str) httpcon (process-status httpcon)))))

(defconst http-codes-alist
  (loop for p in '((200 . "Ok")
                   (201 . "Created")
                   (302 . "Redirect")
                   (400 . "Bad Request")
                   (401 . "Authenticate")
                   (404 . "Not Found")
                   (500 . "Server Error"))
        ;; add an alist entry with an integer key
        collect p
        ;; add an alist entry with a string key
        collect
        (cons (number-to-string (car p))
              (cdr p)))
  "HTTP codes with string keys and integer keys.")

(defun* http-cookie-make (name data &key expiry path)
  "Make a set-cookie header pair from NAME and DATA.

DATA should be a string to be used as the value of the cookie.

Other key values are standard cookie attributes.

Use this with `elnode-http-start' to make cookie headers:

 (elnode-http-start
    httpcon 200
    '(content-type . \"text/html\")
    (elnode-http-cookie-make \"pi\" 3.14579)
    (elnode-http-cookie-make \"e\" 1.59
       :expiry \"Mon, Feb 27 2012 22:10:21 GMT;\")

This will send two Set-Cookie headers setting the cookies 'pi'
and 'e'.

The return value is a cons pair."
  (cons
   "Set-Cookie"
   (format "%s=%s;%s"
           name
           data
           (if (not (or expiry
                        path))
               ""
             (loop for p in `((expires . ,expiry)
                              (path . ,path))
                   if (cdr p)
                   concat
                   (format
                    " %s=%s;"
                    (capitalize (symbol-name (car p)))
                    (cdr p)))))))

(defun http-header-set (httpcon header &optional value)
  "Sets the HEADER for later processing.

HEADER may be a pair of `name' and `value' or it may just be a
String, or a Symbol in which case the VALUE must be specified.

If HEADER is a pair and VALUE is also specified then VALUE is
ignored.

When the HTTP response is started any set headers will be merged
with any requested headers and sent.

If the response has been started it is an error to try to set a
header.  This function will log the error and return `nil'.

See `elnode-http-start'."
  (if (elnode/con-get httpcon :elnode-http-started)
      (msg :warning "can't set header, HTTP already started on %s" httpcon)
    (let ((headers (elnode/con-get httpcon :elnode-headers-to-set)))
      (elnode/con-put
       httpcon
       :elnode-headers-to-set
       (append headers
               (list (if (consp header)
                         header
                       (cons header value))))))))

(defun* http-cookie-set (httpcon name data &key expiry path)
  "Make a cookie and set it on the HTTPCON.

See `elnode-http-cookie-make' for details about cookie making."
  (let ((cookie-cons (http-cookie-make
                      name data :expiry expiry :path path)))
    (http-header-set httpcon (car cookie-cons) (cdr cookie-cons))))

(defun -http-result-header (hdr-alist)
  "Turn the HDR-ALIST into a result header string.

The HDR-ALIST is an alist of symbol or string keys which are
header names, against values which should be strings."
  (let ((hdr-pairs
         (append
          (list (cons 'transfer-encoding "chunked"))
          hdr-alist)))
    (loop for p in hdr-pairs
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
           (cdr p)))))

(defun http-start (httpcon status &rest header)
  "Start the http response on the specified http connection.

HTTPCON is the HTTP connection being handled.

STATUS is the HTTP status, eg: 200 or 404; integers or strings
are acceptable types.

HEADER is a sequence of (`header-name' . `value') pairs.

For example:

 (elnode-http-start httpcon \"200\" '(\"Content-type\" . \"text/html\"))

The status and the header are also stored on the process as meta
data.  This is done mainly for testing infrastructure."
  (if (elnode/con-get httpcon :elnode-http-started)
      (msg :warning "elnode-http-start: HTTP already started on %s" httpcon)
    ;; Send the header
    (msg :debug "elnode-http-start: starting HTTP response on %s" httpcon)
    (let ((header-alist
           (append (elnode/con-get httpcon :elnode-headers-to-set) header))
          (status-code (if (stringp status)
                           (string-to-number status)
                         status)))
      ;; Store the meta data about the response.
      (elnode/con-put httpcon
                      :elnode-httpresponse-status status-code
                      :elnode-httpresponse-header header-alist)
      (process-send-string
       httpcon
       (format
        "HTTP/1.1 %d %s\r\n%s\r\n"
        status-code
        ;; The status text
        (kva status-code http-codes-alist)
        ;; The header
        (or
         (-http-result-header header-alist)
         "\r\n")))
      (elnode/con-put httpcon :elnode-http-started (current-time)))))

(defun -http-end (httpcon)
  "Marks the HTTPCON ended and does end of request things.

This makes access log file calls if the socket has a property
`:elnode-access-log-name'.  The property is taken to be the name
of a buffer."
  (msg :info "elnode--http-end ending socket %s" httpcon)
  (let ((access-log-name (elnode/con-get httpcon :elnode-access-log-name)))
    (when access-log-name
      (condition-case err
          (log-access access-log-name httpcon)
        (error
         (when nil
           (msg :warning
                "elnode--http-end: an error occurred processing the access log"))))))
  (when (eq 'open (process-status httpcon)) (process-send-eof httpcon))
  ;; Signal to elnode--filter that we're done
  (elnode/con-put httpcon :elnode-finished t))

(defun http-return (httpcon &optional data)
  "End the response on HTTPCON optionally sending DATA first.

HTTPCON is the http connection which must have had the headers
sent with `elnode-http-start'

DATA must be a string, it's just passed to `elnode-http-send'."
  (if (not (elnode/con-get httpcon :elnode-http-started))
      (msg :warning "elnode-http-return: HTTP not started")
    (progn
      (when data
        (http-send-string httpcon data))
      ;; Need to close the chunked encoding here
      (http-send-string httpcon "")
      (-http-end httpcon))))

(defun send-html (httpcon html)
  "Simple send for HTML.

Use this for simple sending of a full HTML response:

 (defun my-handler (httpcon)
   (elnode-send-html httpcon \"<html><h1>Hello!</h1></html>\"))

The data is sent with content type: text/html."
  (http-start httpcon 200 '("Content-Type" . "text/html"))
  (http-return httpcon html))

(defun json-fix (data)
  "Fix JSON "
  (let ((json-to-send
         (noflet
          ((json-alist-p (list)
                         "Proper check for ALIST."
                         (while (consp list)
                           (setq list
                                 (if (and
                                      (consp (car list))
                                      (not (consp (caar list)))
                                      (not (vectorp (caar list))))
                                     (cdr list)
                                   'not-alist)))
                         (null list)))
          (json-encode data)))) json-to-send))

(defun send-report (httpcon)
  "Send back an HTML report on the request.

This is often useful for debugging."
  (noflet ((alist->html (alist)
                        (mapconcat
                         (lambda (hdr-pair)
                           (format
                            "%s %s"
                            (car hdr-pair)
                            (let ((v (cdr hdr-pair)))
                              (if (and v (not (equal v "")))
                                  (format "%S" v) ""))))
                         alist
                         "\n")))
          (let* ((method (http-method httpcon))
                 (paramters (alist->html
                             (or (http-params httpcon)
                                 '(("None". "")))))
                 (headers (alist->html (http-headers httpcon)))
                 (page (s-lex-format "<html>
<style>
body { font-family: sans-serif;}
td {
vertical-align: top;
}
</style>
<body>
<table>
<tr><td>method:</td><td>${method}</td></tr>
<tr><td>parameters:</td><td><pre>${paramters}</pre></td><tr>
<tr><td>headers:</td><td><pre>${headers}</pre></td><tr>
</table>
</body>
</html>")))
            (send-html httpcon page))))


(defun* send-json (httpcon data &key content-type jsonp)
  "Convert DATA to JSON and send to the HTTPCON with a 200 \"Ok\".

DATA is some lisp object.

If CONTENT-TYPE is specified then it is used as the HTTP Content
Type of the response.

If JSONP is specified the content is sent as a JSON-P response.
If the variable specifies a name for the JSON-P callback function
that that is used.  Alternately, if the JSONP parameter does not
specify a name, the parameter `callback' is looked up on the
HTTPCON and the value of that used.  If neither the JSONP
parameter, not the HTTP parameter `callback' is present that the
name \"callback\" is used."
  (let ((json-to-send (json-fix data)))
    (http-start
     httpcon 200
     `("Content-type" . ,(or content-type "application/json")))
    (http-return
     httpcon
     (if jsonp
         (format
          "%s(%s);"
          (or (when (stringp jsonp)
                jsonp)
              (http-param httpcon "callback")
              "callback")
          json-to-send)
       json-to-send))))

(defun send-status (httpcon status &optional msg)
  "A generic handler to send STATUS to HTTPCON.

Sends an HTTP response with STATUS to the HTTPCON.  An HTML body
is sent by looking up the STATUS in the `elnode-default-response'
table.

Optionally include MSG."
  (http-start httpcon status '("Content-type" . "text/html"))
  (http-return httpcon
               (-format-response status msg)))

(defun send-404 (httpcon &optional msg)
  "Sends a Not Found error to the HTTPCON.

Optionally include MSG."
  (send-status httpcon 404 msg))

(defun send-400 (httpcon &optional msg)
  "Sends a Bad Request error to the HTTPCON.

Optionally include MSG."
  (send-status httpcon 400 msg))

(defun send-500 (httpcon &optional msg)
  "Sends a Server Error to the HTTPCON.

Optionally include MSG."
  (send-status httpcon 500 msg))

(defun send-redirect (httpcon location &optional type)
  "Sends a redirect to LOCATION.

If TYPE is non-nil, use it as a status code.  Defaults to 302 -
permanent redirect."
  (let ((status-code (or type 302)))
    (http-start httpcon status-code `("Location" . ,location))
    (http-return
     httpcon
     (format "<h1>redirecting you to %s</h1>\r\n" location))))

(defun normalize-path (httpcon handler)
  "A decorator for HANDLER that normalizes paths to have a trailing slash.

This checks the HTTPCON path for a trailing slash and sends a 302
to the slash trailed url if there is none.

Otherwise it calls HANDLER."
  (let ((ends-in-slash-or-extension-regex ".*\\(/\\|.*\\.[^/]*\\)$")
        (path (http-pathinfo httpcon)))
    (if (not (save-match-data
               (string-match ends-in-slash-or-extension-regex
                             path)))
        (send-redirect
         httpcon
         (format "%s/" path))
      (funcall handler httpcon))))

(defun -mapper-find-match-func (match-path match-pair)
  "Funtion to test MATCH-PATH against MATCH-PAIR."
  (let ((m (string-match (car match-pair) match-path)))
    (and m
         (numberp m)
         (>= m 0)
         match-pair)))

(defun -mapper-find-mapping (match-path mapping-table)
  "Return the mapping that matches MATCH-PATH in MAPPING-TABLE."
  (loop for mapping in mapping-table
        if (-mapper-find-match-func match-path mapping)
        return mapping))

(defun -mapper-find (httpcon path mapping-table)
  "Try and find the PATH inside the MAPPING-TABLE.

This function exposes its `match-data' on the 'path' variable so
that you can access that in your handler with something like:

 (match-string 1 (elnode-http-pathinfo httpcon))

Returns the handler function that mapped, or `nil'.

This function also establishes the `:elnode-http-mapping'
property, adding it to the HTTPCON so it can be accessed from
inside your handler with `elnode-http-mapping'."
  ;; First find the mapping in the mapping table
  (let* ((pair (-mapper-find-mapping path mapping-table))
         (func-item (and pair
                         (let* ((v (cdr pair)))
                           (or (and (atom v) v)
                               (if (functionp (car v))
                                   (car v)
                                 (when (functionp v) v)))))))
    ;; Now work out if we found one and what it was mapped to
    (when (or (functionp func-item)
              (functionp (and (symbolp func-item)
                              (symbol-value func-item))))
      ;; Make the match parts accessible
      (elnode/con-put
       httpcon
       :elnode-http-mapping
       (when (string-match (car pair) path)
         (loop for i from 0 to (- (/ (length (match-data path)) 2) 1)
               collect (match-string i path))))
      ;; Return the function
      func-item)))

(defun -http-mapping-implementation (httpcon &optional part)
  "The actual implementation of `elnode-http-mapping.'

This is here so that you flet `elnode-http-mapping' and still get
at the real functionality."
  (if (eq part t)
      (length (elnode/con-get httpcon :elnode-http-mapping))
    ;; Else it's a specific part
    (elt
     (elnode/con-get httpcon :elnode-http-mapping)
     (if part part 0))))

(defun http-mapping (httpcon &optional part)
  "Return the match on the HTTPCON that resulted in the current handler.

With PART it returns a specific part of the match, by default
PART is 0.  If PART is specified as `t' then the count of parts
is returned.

This results only from a call via `elnode-dispatcher'.

It returns the string which matched your url-mapping, with the
match-data attached. So given the mapping:

 (\"/static/\\(.*\\)\" . my-handler)

and the request:

 /static/somedir/somefile.jpg

The following is true inside the handler:

 (equal \"/somedir/somefile.jpg\"
        (match-string 1 (elnode-http-mapping httpcon)))

The function `elnode-test-path' uses this facility to work out a
target path."
  (-http-mapping-implementation httpcon part))

(defsubst -strip-leading-slash (str)
  "Strip any leading slash from STR.

If there is no leading slash then just return STR."
  (if (and (stringp str) (eq (elt str 0) ?/))
      (substring str 1)
    str))

(defun get-targetfile (httpcon docroot)
  "Get the targeted file from the HTTPCON.

Attempts to resolve the matched path of the HTTPCON against the
DOCROOT.  If that doesn't work then it attempts to use just the
pathinfo of the request.

The resulting file is NOT checked for existence or safety."
  (let* ((pathinfo (http-pathinfo httpcon))
         (path (http-mapping httpcon 1))
         (targetfile
          (join
           (expand-file-name docroot)
           (-strip-leading-slash
            (or path pathinfo)))))
    targetfile))


;; We need to declare this before the dispatcher stuff, which uses it.
(defvar -defined-authentication-schemes
  (make-hash-table :test 'equal)
  "The hash of defined authentication schemes.")

(defvar -do-access-logging-on-dispatch t
  "Needed to suppress logging in testing.")

(defun -auth-entry->dispatch-table (auth-scheme &optional hostpath)
  "Make a dispatch table from the AUTH-SCHEME.

If HOSTPATH is specified then the resulting match spec is of the
`hostpath' type for use with `elnode-hostpath-dispatcher'."
  (let* ((auth-scheme (gethash
                       auth-scheme
                       -defined-authentication-schemes))
         (redirect (plist-get auth-scheme :redirect))
         (login-handler (plist-get auth-scheme :login-handler)))
    (when redirect
      (list
       (cons
        (concat (if hostpath "^.*/" "^") redirect "$")
        login-handler)))))

(defun* -dispatch-proc (httpcon
                        path
                        url-mapping-table
                        &key
                        (function-404 'elnode-send-404)
                        (log-name "elnode")
                        extra-table)
  "Dispatch to the matched handler for the PATH on the HTTPCON.
The handler for PATH is matched in the URL-MAPPING-TABLE via
`elnode--mapper-find'.

If no handler is found then a 404 is attempted via FUNCTION-404,
if it's found to be a function, or as a last resort
`elnode-send-404'.

The function also supports the searching of the map provided by
an EXTRA-TABLE.  This is useful for authentication and other
wrappers.  If it is specified it is searched first."
  (let ((handler-func
         (or
          ;; Either a match from extra-table ...
          (and extra-table
               (-mapper-find
                httpcon path extra-table))
          ;; ... or from the standard url-mapping-table
          (-mapper-find
           httpcon path url-mapping-table))))
    (when -do-access-logging-on-dispatch
      (elnode/con-put httpcon :elnode-access-log-name log-name))
    (cond
     ;; If we have a handler, use it.
     ((functionp handler-func)
      (funcall handler-func httpcon))
     (t
      (funcall function-404 httpcon)))))

(defun* dispatcher (httpcon
                    url-mapping-table
                    &key
                    (function-404 'elnode-send-404)
                    auth-scheme)
  "Dispatch HTTPCON to the function mapped in URL-MAPPING-TABLE.

URL-MAPPING-TABLE is an alist of:

 (url-regex . function-to-dispatch)

To map the root url you should use:

  \"^/$\"

To ensure paths end in /, `elnode-dispatcher' uses
`elnode-normalize-path'.  To map another url you should use:

  \"^/path/$\" or \"^/path/sub-path/$\"

An example server setup:

  (defun my-server (httpcon)
    (elnode-dispatcher
     httpcon
     '((\"^/$\" . root-view)
       (\"^/1/$\" . view-1))))

If FUNCTION-404 is specified it is called when no regexp is
matched, otherwise `elnode-send-404' is used.

AUTH-SCHEME is an optional authentication scheme, defined with
`elnode-defauth', which specifies a redirect mapping for
authentications."
  (normalize-path
   httpcon
   (lambda (httpcon)
     ;; Get pathinfo again because we may have redirected.
     (let ((pathinfo (http-pathinfo httpcon))
           (extra-table
            (-auth-entry->dispatch-table auth-scheme)))
       (-dispatch-proc
        httpcon
        pathinfo
        url-mapping-table
        :function-404 function-404
        :extra-table extra-table)))))

(defun -hostpath (host path)
  "Turn the host and path into a hostpath."
  (format
   "%s/%s"
   (let ((host-name (or host "")))
     ;; Separate the hostname from any port in the host header
     (save-match-data
       (if (string-match "\\([^:]+\\)\\(:[0-9]+.*\\)*" host-name)
           (match-string 1 host-name)
         "")))
   path))

(defun* hostpath-dispatcher (httpcon
                             hostpath-mapping-table
                             &key
                             (function-404 'elnode-send-404)
                             (log-name "elnode")
                             auth-scheme)
  "Dispatch HTTPCON to a handler based on the HOSTPATH-MAPPING-TABLE.

HOSTPATH-MAPPING-TABLE has regexs of the host and the path double
slash separated, thus:

 (\"^localhost//pastebin.*\" . pastebin-handler)

FUNCTION-404 should be a 404 handling function, by default it's
`elnode-send-404'.

LOG-NAME is an optional log-name.

AUTH-SCHEME is an optional authentication scheme, defined with
`elnode-defauth', which specifies a redirect mapping for
authentications."
  (let ((hostpath (-hostpath
                   (http-header httpcon "Host")
                   (http-pathinfo httpcon)))
        (extra-table
         ;; Make sure it's a hostpath type
         (-auth-entry->dispatch-table auth-scheme t)))
    (-dispatch-proc
     httpcon
     hostpath
     hostpath-mapping-table
     :function-404 function-404
     :log-name log-name
     :extra-table extra-table)))

;;;###autoload
(defcustom hostpath-default-table
  '(("[^/]+//wiki/\\(.*\\)" . elnode-wikiserver)
    ("[^/]+//\\(.*\\)" . elnode-webserver))
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

(defun hostpath-default-handler (httpcon)
  "A default hostpath handler.

This uses the `elnode-hostpath-default-table' for the match
table.  It calls `elnode-hostpath-dispatcher' with
`elnode-hostpath-default-table'."
  (hostpath-dispatcher httpcon hostpath-default-table))


;; Async handling stuff

;; Elnode child process functions

(defcustom log-worker-elisp nil
  "If true then worker Elisp (Elisp run in a child-Emacs process) is logged.

The buffer '* elnode-worker-elisp *' is used for the log."
  :group 'elnode
  :type '(boolean))

(defcustom log-worker-responses nil
  "If true then worker Elisp logs responses in a buffer.

The buffer '* elnode-worker-response *' is used for the log."
  :group 'elnode
  :type '(boolean))


(defun wait-for-exit (process)
  "Wait for PROCESS status to go to 'exit."
  (while (not (eq (process-status process) 'exit))
    (sleep-for 1)))


;; TODO: handle errors better than messaging
(defun -child-process-sentinel (process status)
  "A sentinel for Elnode child PROCESS.

Elnode child processes are just Emacs asynchronous processes that
send their output to an Elnode HTTP connection.

The main job of this sentinel is to monitor when the STATUS of
PROCESS indicates the end of the PROCESS and to do
`elnode-http-end' on the associated HTTP connection when that
happens."
  (cond
   ((equal status "finished\n")
    (let ((httpcon (elnode/con-get process :elnode-httpcon)))
      (msg
       :info
       "elnode-child-process-sentinel Status @ finished: %s -> %s on %s"
       (process-status httpcon)
       (process-status process)
       httpcon)
      (if (not (eq 'closed (process-status httpcon)))
          (progn
            (http-send-string httpcon  "")
            (process-send-string httpcon "\r\n")
            (-http-end httpcon)))))
   ((string-match "exited abnormally with code \\([0-9]+\\)\n" status)
    (let ((httpcon (elnode/con-get process :elnode-httpcon)))
      (msg
       :info "elnode-child-process-sentinel: %s on %s"
       status httpcon)
      (if (not (eq 'closed (process-status httpcon)))
          (progn
            ;; Spit out the error at the end of the content
            (when (elnode/con-get httpcon :elnode-child-process-command)
              (http-send-string
               httpcon
               (format
                "%s %s"
                (elnode/con-get httpcon :elnode-child-process-command)
                status)))
            ;; Now close the content
            (http-send-string httpcon "")
            (process-send-string httpcon "\r\n")
            (-http-end httpcon)))
      (delete-process process)
      (kill-buffer (process-buffer process))))
   (t
    (msg
     :info "elnode-child-process-sentinel: %s on %s"
     status process))))

(defun -child-process-filter (process data)
  "A generic filter function for elnode child processes.

Elnode child processes are just Emacs asynchronous processes that
send their output to an Elnode HTTP connection.

This filter function does the job of taking the output from the
async process and finding the associated Elnode HTTP connection
and sending the data there."
  (let ((httpcon (elnode/con-get process :elnode-httpcon)))
    (msg
     :info "elnode-child-process-filter http state: %s data length: %s on %s"
     (process-status httpcon)
     (length data)
     httpcon)
    (unless (eq 'closed (process-status httpcon))
      (http-send-string httpcon data))))

(defun child-process (httpcon program &rest args)
  "Run the specified PROGRAM asynchronously sending output to HTTPCON.

PROGRAM is the path to the program to run, to be resolved by
`start-process' in the usual way.

ARGS is a list of arguments to pass to the program.

It is NOT POSSIBLE to run more than one process at a time
directed at the same http connection."
  (let* ((proc-args
          (append
           (list
            (format "%s-%s" (process-name httpcon) program)
            (format " %s-%s" (process-name httpcon) program)
            program) args))
         (p (let ((process-connection-type nil)
                  (default-directory (file-name-directory program)))
              (apply 'start-process proc-args))))
    ;; Store the program and args for later
    (elnode/con-put
     httpcon :elnode-child-process-command
     (format "%s %s" program (s-join " " args)))
    (set-process-coding-system p 'raw-text-unix)
    ;; Bind the http connection to the process
    (elnode/con-put p :elnode-httpcon httpcon)
    ;; Bind the process to the http connection
    ;;
    ;; WARNING: this means you can only have 1 child process at a time
    (elnode/con-put httpcon :elnode-child-process p)
    ;; Setup the filter and the sentinel to do the right thing with
    ;; incomming data and signals
    (set-process-filter p 'elnode--child-process-filter)
    (set-process-sentinel p 'elnode--child-process-sentinel)
    (msg :info "elnode-child-process init %s" httpcon)))


;; File management

(defcustom send-file-program "/bin/cat"
  "The program to use for sending files.

Altering this is not recomended but it may be a good hook for
certain types of debugging."
  :group 'elnode
  :type '(string))

(defvar replacements-pattern "<!##E \\(.*?\\) E##!>"
  "The regex used for replacing things.

The default regex is rather baroque.  This is because it needs to
be quite unique and there are a lot of different sorts of things
like this to be unique from.")

(defun -buffer-template (file-buf replacements)
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
     replacements-pattern
     (lambda (matched)
       (let ((match-var (match-string-no-properties 1 matched)))
         (cond
          ((hash-table-p replacements)
           (gethash match-var replacements ""))
          (t
           ;; Presume it's an alist
           (or
            (assoc-default match-var replacements nil t)
            "")))))
     (buffer-substring-no-properties (point-min)(point-max)))))

(defcustom webserver-visit-file (eq system-type 'windows-nt)
  "Whether the webserver reads files by visiting buffers or not.

When set to `t' files to be sent with the `elnode-send-file' are
read into Emacs using `find-file'."
  :group 'elnode
  :type 'boolean)

(defvar replacements-httpcon nil
  "This is bound by `elnode-send-file' when doing replacements.

It should not be used otherwise.")

(defvar replacements-targetfile nil
  "This is bound by `elnode-send-file' when doing replacements.

It should not be used otherwise.")

(defun -rfc1123-date (time)
  "Return TIME in RFC1123 format, suitable for HTTP dates."
  (let* ((day-names '("Sun" "Mon" "Tue" "Wed" "Thu" "Fri" "Sat"))
         (month-names '("Jan" "Feb" "Mar" "Apr" "May" "Jun"
                        "Jul" "Aug" "Sep" "Oct" "Nov" "Dec"))
         (decoded-time (decode-time time))
         (day (nth (nth 6 decoded-time) day-names))
         (month (nth (- (nth 4 decoded-time) 1) month-names)))
    (format "%s, %s %s %s"
            day
            (format-time-string "%d" time t)
            month
            (format-time-string "%Y %H:%M:%S GMT" time t))))

(defsubst -file-modified-time (file)
  "Get modification time for FILE."
  (nth 5 (file-attributes file)))

(defvar send-file-assoc nil
  "A-list of file patterns vs functions to serve files.

When a file is sent with `elnode-send-file' we try and match the
targetfile against the regex patterns in the `car' of this alist
and then use the function in the `cdr' to send the file instead
of sending it directly.")

(defun* send-file (httpcon targetfile
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
`elnode--buffer-template' for details of templating.

REPLACEMENTS can optionally be a function in which case the
return value is expected to be the hash-table or alist for the
variables.  The function should have no arguments but two
variables are bound during the function's execution
`elnode-replacements-httpcon' is the `httpcon' and
`elnode-replacements-targetfile' is the targetfile to be
delivered.

See `elnode-send-file-assoc' for more possible transformations."
  (let ((filename
         (if (not (file-name-absolute-p targetfile))
             (let ((dir (or load-file-name buffer-file-name)))
               (file-relative-name
                targetfile
                (if dir (directory-file-name dir) default-directory)))
           targetfile)))
    (if (not (file-exists-p filename))
        ;; FIXME: This needs improving so we can handle the 404
        ;; This function should raise an exception?
        (send-404 httpcon)
      ;; Else ...
      (let (send-func)
        (if (setq send-func
                  (and send-file-assoc
                       (loop for (pattern . func) in send-file-assoc
                             if (string-match-p pattern targetfile)
                             return func)))
            (funcall send-func httpcon targetfile)
          ;; Else we don't have a send func so just send it
          (let ((mimetype
                 (or (when (listp mime-types)
                       (car (rassoc
                             (file-name-extension targetfile)
                             mime-types)))
                     (mm-default-file-encoding targetfile)
                     "application/octet-stream")))
            (http-start
             httpcon 200
             `("Content-type" . ,mimetype)
             `("Last-Modified" . ,(elnode--rfc1123-date
                                   (elnode--file-modified-time targetfile))))
            (when preamble (http-send-string httpcon preamble))
            (if (or webserver-visit-file replacements)
                (http-return
                 httpcon
                 (if replacements
                     (-buffer-template
                      (find-file-noselect filename)
                      ;; Replacements handling
                      (if (functionp replacements)
                          (let ((replacements-httpcon httpcon)
                                (replacements-targetfile targetfile))
                            (funcall replacements))
                        replacements))
                   (with-temp-buffer 
                     (insert-file-contents-literally filename)
                     (buffer-string))))
              (child-process
               httpcon
               send-file-program
               (expand-file-name targetfile)))))))))

(defmacro method (httpcon &rest method-mappings)
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
   (debug (sexp &rest (sexp &rest form)))
   (indent 1))
  (let* ((var (make-symbol "v"))
         (conv (make-symbol "con")))
    `(let* ((,conv ,httpcon)
            (,var (intern (elnode-http-method ,conv))))
       (cond
        ,@(loop
           for d in method-mappings
           unless (eq (car d) t)
           collect `((eq ,var (quote ,(car d)))
                     ,@(cdr d)))
        ;; If we don't map then send an error
        ;;
        ;; probably should be 405
        (t
         ,@(or (cdr (assoc t method-mappings))
               `((elnode-send-500 ,conv))))))))


;; Make simple handlers automatically

(defun make-redirecter (location &optional type)
  "Make a handler that will redirect to LOCATION.

Optionally, use the specified TYPE as the status code, eg:

 (elnode-make-redirect \"http://somehost.com/\" 301)"
  (lambda (httpcon)
    (send-redirect httpcon location type)))

(defun* make-send-file  (filename
                         &key
                         preamble
                         mime-types
                         replacements
                         replacements-pattern)
  "Make a handler that will serve a single FILENAME.

If the FILENAME is relative then it is resolved against the
package's `load-file-name'.

Optionally MIME-TYPES and other additional keyword arguments may be
specified and are passed through, see `elnode-send-file' for
details.

The REPLACEMENTS parameter can be a function that returns a
hash-table or alist, this is very useful for this function
because it allows dynamic variables to be defined.  Again, see
`elnode-send-file' for full documentation of this feature.

The REPLACEMENTS-PATTERN can be used to set the regex used to
match replacements.  See `elnode-replacements-pattern'."
  (lambda (httpcon)
    (let ((replacements-pattern
           (or replacements-pattern
               replacements-pattern)))
      (send-file
       httpcon
       filename
       :mime-types mime-types
       :preamble preamble
       :replacements replacements))))


;; Docroot protection

(defun -under-docroot-p (target-file doc-root &optional ignore-missing)
  "Is the TARGET-FILE under the DOC-ROOT?
Optional argument IGNORE-MISSING will inhibit checks for missing files."
  (let ((docroot (directory-file-name (expand-file-name doc-root))))
    (and
     (string-match
      (format "^%s\\($\\|/\\)" docroot)
      target-file)
     (or ignore-missing (file-exists-p target-file)))))


(defun not-found (httpcon target-file)
  "`elnode-docroot-for' calls this when the doc was not found.

You can override this in tests to have interesting effects.  By
default it just calls `elnode-send-404'."
  (send-404 httpcon))

(defun modified-since (httpcon modified-time)
  "Implement the HTTP If-Modified-Since test.

MODIFIED-TIME is the time the resource was modified, for example
a file modification time."
  (let* ((modified-since
          (http-header
           httpcon 'if-modified-since :time)))
    (and
     modified-since
     (time-less-p modified-time modified-since))))

(defun cached-p (httpcon target-file)
  "Is the specified TARGET-FILE older than the HTTPCON?

This uses `elnode-modified-since'."
  (modified-since
   httpcon (-file-modified-time target-file)))

(defun cached (httpcon)
  "`elnode-docroot-for' calls this when the resources was cached.

By default it just calls `elnode-send-status' with 304."
  (send-status httpcon 304))

(defvar docroot-for-no-404 nil
  "When set to true `elnode-docroot-for' doesn't check for missing files.")

(defvar docroot-for-no-cache nil
  "When set to true `elnode-docroot-for' doesn't check for cached files.")

(defmacro docroot-for (doc-root with target-file-var
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
    (assert (or (eq with 'with) (eq with :with)))
    (assert (or (eq on 'on)     (eq on :on)))
    (assert (or (eq do 'do)     (eq do :do)))
    `(let ((,dr ,doc-root)
           (,con ,httpcon))
       (let ((,target-file-var (elnode-get-targetfile ,con ,dr)))
         (if (not (elnode--under-docroot-p
                   ,target-file-var ,dr elnode-docroot-for-no-404))
             (elnode-not-found ,con ,target-file-var)
           (if (and (not elnode-docroot-for-no-cache)
                    (elnode-cached-p ,con ,target-file-var))
               (elnode-cached ,con)
             ,@handling))))))


;; Webserver stuff

(defconst webserver-docroot-default
  (expand-file-name (concat config-directory "public_html/"))
  "The default location of the website.

This is used to detect whether elnode needs to create this
directory or not.")

(defcustom webserver-docroot
  webserver-docroot-default
  "The document root of the webserver.

Webserver functions are free to use this or not.  The
`elnode-webserver' function does use it."
  :group 'elnode
  :type 'file)

(defcustom webserver-extra-mimetypes
  '(("text/plain" . "creole")
    ("text/plain" . "el"))
  "Extra mime types to identify special file types.

This is just a way of hacking the mime type discovery so we can
add more file mappings more easily than editing `/etc/mime.types'."
  :group 'elnode
  :type '(alist :key-type string
                :value-type string))

(defcustom webserver-index '("index.html" "index.htm")
  "A list of possible index filenames.

Anyone of the values of this list may be picked as the index page
for a directory."
  :group 'elnode
  :type '(repeat string))

(defun -webserver-setup ()
  "Setup the Elnode webserver by making a default public_html dir.

The server has a single `test.html' file, this is so we can show
off the standard webserver indexing in elnode's webserver."
  (-dir-setup webserver-docroot
              webserver-docroot-default
              "default-webserver-test.html"
              "test.html"
              "default-webserver-image.png"))

(defun url-encode-path (path)
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

(defcustom webserver-index-page-template "<html>
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

(defcustom webserver-index-file-template "<a href='%s'>%s</a><br/>\r\n"
  "The template for each file in the webserver index.

This is used to display each file in an automated directory index.

It is expected the template has 2 %s variables in it, the first
is the url to link to and the second is the content of the link."
  :group 'elnode
  :type '(string))

(defun -webserver-index (docroot targetfile pathinfo &optional match)
  "Constructs index documents.

The index is made for the DOCROOT and TARGETFILE. The web path is
PATHINFO.

Optional MATCH is passed directly through to
`directory-files-and-attributes'."
  ;; TODO make this usable by people generally
  (let ((dirlist (directory-files-and-attributes targetfile nil match)))
    ;; TODO make some templating here so people can change this
    (format
     webserver-index-page-template
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
              webserver-index-file-template
              (url-encode-path entry)
              (car dir-entry)))))))

;;;###autoload
(defun -webserver-handler-proc (httpcon docroot mime-types)
  "Actual webserver implementation.

Do webserving to HTTPCON from the DOCROOT using the MIME-TYPES
for meta information.

This is not a real handler (because it takes more than the
HTTPCON) but it is called directly by the real webserver
handlers."
  (docroot-for docroot
               with targetfile
               on httpcon
               do
               (let ((pathinfo (http-pathinfo httpcon)))
                 (if (file-directory-p targetfile)
                     ;; Use an existing index file or send a directory index
                     (let* ((indexfile
                             (loop for i in webserver-index
                                   if (member i (directory-files targetfile))
                                   return i)))
                       (if indexfile
                           (send-file httpcon (concat targetfile "/" indexfile))
                         (let ((index (-webserver-index
                                       docroot
                                       targetfile
                                       pathinfo)))
                           (http-start httpcon 200 '("Content-type" . "text/html"))
                           (http-return httpcon index))))
                   ;; Send a file.
                   (send-file
                    httpcon
                    targetfile
                    :mime-types mime-types)))))

(defun webserver-handler-maker (&optional docroot extra-mime-types)
  "Make a webserver handler possibly with the DOCROOT and EXTRA-MIME-TYPES.

Returns a proc which is the handler. The handler serves files out
of the docroot and marks them with the content types that Emacs
knows about. You can add extra content types for the webserver
just by supplying an alist of mime-types and extensions for
EXTRA-MIME-TYPES.

The webserver handler also creates file indexes.

The webserver uses `elnode-test-path' to make sure that the
request does not go above the DOCROOT."
  (let ((my-docroot (or docroot webserver-docroot))
        (my-mime-types (or extra-mime-types
                           webserver-extra-mimetypes)))
    `(lambda (httpcon)
       ,(format "Webserver serving files on %s" my-docroot)
       (elnode--webserver-handler-proc
        httpcon ,my-docroot (quote ,my-mime-types)))))


(defvar -make-webserver-store nil
  "Alist of webservers made by `elnode-make-webserver'.

Stored as `docroot' . `webserver'.")

;;;###autoload
(defun make-webserver (docroot port &optional host)
  "Make a webserver interactively, for DOCROOT on PORT.

An easy way for a user to make a webserver for a particular
directory."
  (interactive
   (let ((docroot (read-directory-name "Docroot: " nil nil t))
         (port (read-from-minibuffer "Port: "))
         (host (if current-prefix-arg
                   (read-from-minibuffer "Host: ")
                 init-host)))
     (list docroot port host)))
  (let ((webserver-proc (webserver-handler-maker docroot)))
    (add-to-list
     'elnode--make-webserver-store
     (cons docroot webserver-proc))
    (start
     webserver-proc
     :port (string-to-number (format "%s" port))
     :host host)))

;;;###autoload
(defun webserver (httpcon)
  "A simple webserver that serves documents out of `elnode-webserver-docroot'.

This is just an example of an elnode webserver, but it may be all
that is needed most of the time.

See `elnode-webserver-handler-maker' for more possibilities for
making webserver functions.

HTTPCON is the HTTP connection to the user agent."
  (-webserver-setup)
  (let (use-webserver-handler-maker)
    (if use-webserver-handler-maker
        (-webserver-handler-proc
         httpcon
         webserver-docroot
         webserver-extra-mimetypes)
      ;; Otherwise DO use the handler maker...
      (let ((webserver (webserver-handler-maker
                        webserver-docroot
                        webserver-extra-mimetypes)))
        (funcall webserver httpcon)))))

;; Default elnode auth databases

(defconst auth-db-spec-default
  `(db-hash
    :filename
    ,(expand-file-name (concat elnode-config-directory "elnode-auth")))
  "The default elnode-auth-db specification.")

(defcustom auth-db-spec
  auth-db-spec-default
  "The `db' specification of where the auth db is."
  :group 'elnode
  :type '(list symbol symbol string))

(defvar auth-db
  (db-make auth-db-spec)
  "Authentication database.

This is the data structure storing hashed passwords against
username keys.

It is an elnode database which can be one of several
implementations.")

(defvar secret-key "secret"
  "Secret key used to hash secrets like passwords.")

(defun auth-make-hash (username password)
  "Hash the `elnode-secret-key' and the USERNAME and PASSWORD.

This is not an ideal hashing function because `elnode-secret-key'
is not very customizable.  We need to find a way of making a
secret key per elnode app and communicating that to this kind of function.

It is possible to use a different hashing function when you
define an elnode-auth scheme and that's probably the best way to
do it right now."
  (sha1 (format "%s:%s:%s"
                secret-key
                username
                password)))

(defvar -auth-user-add-databases-history nil
  "The history of symbols used for auth databases.")

(defvar -auth-user-add-username-history nil
  "The history of usernames used for auth databases.")

(defun auth-user-add (username password &optional auth-db)
  "Command to add a user to the internal authentication database.

With prefix-arg also request the authentication database variable
name.  The authentication database must exist.  By default the
main `elnode-auth-db' is used."
  (interactive
   (list (read-from-minibuffer
          "username: " nil nil nil
          'elnode--auth-user-add-username-history)
         (read-passwd "password: ")
         (when current-prefix-arg
           (intern
            (completing-read
             "auth database variable (elnode-auth-user-db): "
             obarray
             nil t nil
             'elnode--auth-user-add-databases-history
             'elnode-auth-db)))))
  (unless auth-db
    (setq auth-db 'elnode-auth-db))
  (db-put
   username
   `(("token" . ,(elnode-auth-make-hash username password))
     ("username" . ,username))
   (symbol-value auth-db))
  (message "username is %s" username))

(defun* auth-user-p (username
                     password
                     &key
                     auth-test
                     (make-hash 'elnode-auth-make-hash))
  "Does the AUTH-TEST pass?

The password is stored in the db hashed keyed by the USERNAME,
this looks up and tests the hash.

MAKE-HASH is `elnode-auth-make-hash' by default.  It takes a
username and password and returns a token.  Implementing a
different function can implement different hashing algorithms.

AUTH-TEST is passed a username and must return a token.
AUTH-TEST can be used to change the hashed token lookup to find
the token in a particular database."
  (let ((token (funcall (or make-hash 'elnode-auth-make-hash)
                        username password)))
    (equal token (funcall auth-test username))))


(defvar loggedin-db (make-hash-table :test 'equal)
  "Stores logins - authentication sessions.

See `elnode-auth-login' for how this is updated.")


(progn
  ;; Sets up the elnode auth errors
  (put 'elnode-auth-credentials
       'error-conditions
       '(error elnode elnode-auth elnode-auth-credentials))
  (put 'elnode-auth-credentials
       'error-message
       "Elnode authentication failed")

  ;; For failing cookies
  (put 'elnode-auth-token
       'error-conditions
       '(error elnode elnode-auth elnode-auth-token))
  (put 'elnode-auth-token
       'error-message
       "Elnode authentication failed"))

(defun* auth-login (username
                    password
                    &key
                    auth-test
                    make-hash
                    (loggedin-db elnode-loggedin-db))
  "Log a user in.

Check the USERNAME and PASSWORD with `elnode-auth-user-p' and
then update `elnode-loggedin-db' with the username and the login
record.

When the authentication test fails `elnode-auth-credentials'
signal is raised.

The optional AUTH-TEST which is the test to check the username
and password with.  It is passed to `elnode-auth-user-p'.

The optional MAKE-HASH is a hash generation function passed to
`elnode-auth-user-p'.

LOGGEDIN-DB is the logged-in state database to use.  By default,
this is `elnode-loggedin-db'."
  (if (auth-user-p username password
                   :auth-test auth-test :make-hash make-hash)
      (let* ((rndstr (format "%d" (random)))
             (str (format "%s:%s:%s" username rndstr secret-key))
             (hash (sha1 str))
             (user-record
              (list
               :user username
               :token rndstr
               :hash hash)))
        (puthash username user-record loggedin-db)
        hash)
    ;; Else it was bad so throw an error.
    (signal 'elnode-auth-credentials (list username password))))

(defun* auth-check-p (username
                      token
                      &key
                      (loggedin-db elnode-loggedin-db))
  "Check login status of the USERNAME against the hashed TOKEN.

Optionally use the LOGGEDIN-DB supplied.  By default this is
`elnode-loggedin-db'.

Returns USERNAME if true and `nil' if not it fails."
  (let ((record (gethash username loggedin-db)))
    (when (equal token (plist-get record :hash))
      username)))

(defun auth-cookie-decode (cookie-value)
  "Decode an encoded elnode auth COOKIE-VALUE.

Returns a cons of `username' and `token'"
  (when (string-match "\\(.*\\)::\\(.*\\)" cookie-value)
    (cons (match-string 1 cookie-value)
          (match-string 2 cookie-value))))

(defun* auth-get-cookie-value (httpcon &key (cookie-name "elnode-auth"))
  "Return the decoded value for COOKIE-NAME.

By default it's \"elnode-auth\" but you should use whatever
cookie-name you're using for your app."
  (let* ((cookie-value (http-cookie httpcon cookie-name t))
         (decoded-cons (auth-cookie-decode (or cookie-value ""))))
    decoded-cons))

(defun* auth-cookie-check-p (httpcon &key
                                     (cookie-name "elnode-auth")
                                     (loggedin-db elnode-loggedin-db))
  "Check that the user is loggedin according to the cookie.

The name of the cookie can be supplied with :COOKIE-NAME - by
default is is \"elnode-auth\".

LOGGEDIN-DB can be a loggedin state database which is a
hash-table.  By default it is `elnode-loggedin-db'.

Returns the username that authenticated or `nil' if it did not or
signal's an `elnode-auth-token' error with the COOKIE-NAME if
that cookie was not found."
  (let ((cookie-cons (auth-get-cookie-value
                      httpcon :cookie-name cookie-name)))
    (if (not cookie-cons)
        (signal 'elnode-auth-token cookie-name)
      ;; Else check the username and token
      (let ((username (car cookie-cons))
            (token (cdr cookie-cons)))
        (auth-check-p username token :loggedin-db loggedin-db)))))

(defun* auth-cookie-check (httpcon &key
                                   (cookie-name "elnode-auth")
                                   (loggedin-db elnode-loggedin-db))
  "Check the COOKIE-NAME has a loggedin cookie in LOGGEDIN-DB.

Signals `elnode-auth-token' on cookie or authentication failure.

See `elnode-auth-cookie-check-p' for more details."
  (or (auth-cookie-check-p
       httpcon
       :cookie-name cookie-name
       :loggedin-db loggedin-db)
      ;; Not sure this is the correct token...
      (signal 'elnode-auth-token :not-logged-in)))

(defvar auth-httpcon nil
  "Dynamic scope variable for HTTP con while we auth.")

(defun* auth-http-login (httpcon
                         username password logged-in
                         &key
                         (cookie-name "elnode-auth")
                         auth-test
                         make-hash
                         (loggedin-db elnode-loggedin-db))
  "Log the USERNAME in on the HTTPCON if PASSWORD is correct.

If authentication succeeds set the relevant cookie and redirect
the user to LOGGED-IN.

Actually uses `elnode-auth-login' to do the assertion.
`elnode-auth-credentials' is signaled by that if the assertion fails.

AUTH-DB is a database, by default `elnode-auth-db', it's passed
to `elnode-auth-login'.

AUTH-TEST and MAKE-HASH are both optional and passed down to
`elnode-auth-user-p' if they exist."
  (let* ((elnode-auth-httpcon httpcon)
         (hash
          (auth-login
           username password
           :auth-test auth-test
           :make-hash make-hash
           :loggedin-db loggedin-db)))
    (http-header-set
     httpcon
     (http-cookie-make
      cookie-name
      (format "%s::%s" username hash)
      :path "/"))
    (send-redirect httpcon (or logged-in "/"))))

(defcustom auth-login-page "<html>
<body>
<form method='POST' action='<!##E target E##!>'>
<input type='hidden' name='redirect' value='<!##E redirect E##!>'/>
username: <input type='text' name='username'/><br/>
password: <input type='password' name='password'/><br/>
<input type='submit' name='login'/>
</form>
</body>
</html>"
  "A standard login page, used by `elnode-auth-login-sender'."
  :group 'elnode
  :type '(string))

(defun auth-login-sender (httpcon target redirect)
  "Send the login page for auth to HTTPCON.

The login page will send its authentication request to TARGET.

The authentication will include username, password AND REDIRECT,
which is the URL to redirect to when login is successful.

This function sends the contents of the custom variable
`elnode-auth-login-page' after templating it."
  (http-start httpcon 200 `("Content-type" . "text/html"))
  ;; It would be nice to support preambles... not sure how.
  ;;  (when preamble (elnode-http-send-string httpcon preamble))
  (http-return
   httpcon
   (with-temp-buffer
     (insert auth-login-page)
     (-buffer-template
      (current-buffer)
      `(("target" . ,target)
        ("redirect" . ,redirect))))))

(defun* auth--login-handler (httpcon
                             sender target
                             &key
                             auth-test ; assert not nil?
                             make-hash
                             (cookie-name "elnode-auth")
                             (loggedin-db elnode-loggedin-db))
  "An authentication handler implementation.

This is the handler that is mapped to the login path, by default
\"/login/\".

SENDER is the function which will send the login page to the
user, it takes an HTTPCON and the TARGET from the call to this
and a redirect path.  The redirect path is taken from the HTTP
parameter \"redirect\".  The SENDER function must send a
'username' and 'password' HTTP parameters to this handler.  The
SENDER function may also send a \"redirect\" parameter which will
be used to HTTP redirect the user-agent on successful
authentication.

TARGET is the path that will be used as the login handler
path (the path to call this handler).

AUTH-TEST checks the hashed details of the user's password and is
passed to `elnode-auth-user-p'.

MAKE-HASH is optional and passed down to `elnode-auth-user-p' if
present."
  (elnode-method httpcon
                 (GET
                  (funcall sender httpcon target
                           (or (http-param httpcon "redirect") "/")))
                 (POST
                  (let ((username (http-param httpcon "username"))
                        (password (http-param httpcon "password"))
                        (logged-in (http-param httpcon "redirect")))
                    (condition-case err
                        (auth-http-login
                         httpcon
                         username password logged-in
                         :auth-test auth-test
                         :make-hash make-hash
                         :cookie-name cookie-name)
                      (elnode-auth-credentials
                       (send-redirect
                        httpcon
                        (if (not logged-in)
                            target
                          (format "%s?redirect=%s" target logged-in))))
                      (t (msg
                          :warning "elnode-auth--login-handler: unexpected error: %S"
                          err)))))))

(defun auth-default-test-v001 (username database)
  "The first test function used for Elnode auth.

This uses just the keyed value of the username as the token.  We
no longer store databases like that by default."
  (db-get username database))

(defun auth-default-test (username database)
  "The default test function used for Elnode auth.

Is uses a stored alist against USERNAME, the alist should contain
the key \"token\" with a user's token.  Whatever else the alist
contains is irrelevant."
  (let ((user (db-get username database)))
    (when user
      (kva "token" user))))

(defun* auth--make-login-handler (&key
                                  (sender 'elnode-auth-login-sender)
                                  (target "/login/")
                                  auth-test
                                  make-hash
                                  ;; only used if the auth-test is not present
                                  (auth-db elnode-auth-db) 
                                  (cookie-name "elnode-auth")
                                  (loggedin-db elnode-loggedin-db))
  "Make an `elnode-auth--login-handler', binding parameters."
  (lambda (httpcon)
    (auth--login-handler
     httpcon
     sender target
     ;; Make a test function if we don't have one
     :auth-test (if (functionp auth-test)
                    auth-test
                  (lambda (username)
                    (auth-default-test username auth-db)))
     :make-hash (when (functionp make-hash) make-hash)
     :cookie-name cookie-name
     :loggedin-db loggedin-db)))

(defun* defauth (scheme-name
                 &key
                 (test :cookie)
                 auth-test
                 make-hash
                 (auth-db 'elnode-auth-db)
                 (cookie-name "elnode-auth")
                 (failure-type :redirect)
                 (redirect "/login/")
                 (sender 'elnode-auth-login-sender))
  "Define an Elnode authentication scheme.

An authentication scheme consists of the following attributes:

TEST what sort of test is used to test the authentication, by
default this is `:cookie'.  No other authentication tests are
possible right now but in the future there might be many (there
might also be a general `:function' test that allows calling of a
function to implement the test).

COOKIE-NAME is used when the TEST is `:cookie'.  It is the name
of the cookie to use for authentication.  By default this is
`elnode-auth'.  It must be specified as a string.

AUTH-TEST is a function to implement checking authentiation of
users.  It is passed a username and must respond with a token
that can be checked against the value returned by the hashing
function (see MAKE-HASH and `elnode-auth-make-hash' which is the
default hashing function).  AUTH-TEST can be nil in which case a
default based on AUTH-DB will be used.

MAKE-HASH is a function to implement the construction of a hash
token for authentication.  It takes a username and password and
must produce the same value as AUTH-TEST.

AUTH-DB is the `db' used for authentication information.
It is used as the authority of information on users.  By default
this is `elnode-auth-db'.

FAILURE-TYPE is what to do if authentication fails.  Currently
only `:redirect' is supported.  To redirect on failure means to
send a 302 with a location to visit a login page.  :FAILURE-TYPE
is `:redirect' by default.

REDIRECT is where to redirect to if FAILURE-TYPE is `:redirect'.
By default this is \"/login/\".  If SENDER is not nil then a
dispatcher told about this auth scheme will dispatch a path
naming REDIRECT to SENDER.

SENDER is an Elnode handler taking additional parameters of
`target' and `redirect'.  By default this is the function
`elnode-auth-login-sender'.  Specify a different function if you
want to totally change the login page."
  (let* ((login-handler (auth--make-login-handler
                         :sender sender
                         :target redirect
                         :auth-test auth-test
                         :make-hash make-hash
                         :auth-db auth-db
                         :cookie-name cookie-name))
         (auth-scheme (list
                       :test test
                       :cookie-name cookie-name
                       :failure-type failure-type
                       :redirect redirect
                       :login-handler login-handler)))
    (puthash scheme-name
             auth-scheme
             -defined-authentication-schemes)))

(defmacro auth-dispatcher (httpcon auth-scheme &rest body)
  "Dispatch HTTPCON to AUTH-SCHEME's handler if it matches.

Otherwise do BODY."
  (declare
   (debug (sexp sexp &rest form))
   (indent 2))
  (let ((httpcon-v (make-symbol "httpcon-v"))
        (auth-scheme-v (make-symbol "auth-scheme-v"))
        (redirect-v (make-symbol "redirect-v"))
        (handler-v (make-symbol "handler-v")))
    `(let* ((,httpcon-v ,httpcon)
            (,auth-scheme-v
             (gethash
              ,auth-scheme
              elnode--defined-authentication-schemes))
            (,redirect-v (plist-get ,auth-scheme-v :redirect))
            (,handler-v (plist-get ,auth-scheme-v :login-handler)))
       (if (elnode--mapper-find-match-func
            (elnode-http-pathinfo ,httpcon-v)
            (cons ,redirect-v ,handler-v))
           ;; If the current path matches call the auth handler
           (funcall ,handler-v ,httpcon-v)
         ;; Else do whatever the body was
         ,@body))))

(defun auth-username (httpcon)
  "Return the username currently associated to the HTTPCON."
  (elnode/con-get httpcon :auth-username))

(defun test-login (auth target username password)
  "Send a test login to Elnode."
  ;; FIXME - use AUTH as a reference to an elnode-authentication
  ;; declaration and pull things like /login/ from it
  (test-call
   (format "/login/?redirect=%s" target)
   :method "POST"
   :parameters (list (cons "username" username)
                     (cons "password" password))))

;;;###autoload
(defun init ()
  "Bootstraps the elnode environment when the Lisp is loaded.

It's useful to have elnode start automatically... on Lisp
load.  If the variable `elnode-init-port' is set then this
function will launch a server on it.

The server is started with `elnode-hostpath-default-handler' as
the handler and listening on `elnode-init-host'"
  (interactive)
  (when init-port
    (condition-case nil
        (progn
          (start
           'elnode-hostpath-default-handler
           :port init-port)
          (setq -inited t))
      (error "Elnode could not initialize."))))

;;;###autoload
(defcustom do-init nil
  "Should elnode start a server on load?

The server that is started is controlled by more elnode
customizations.

`elnode-hostpath-default-table' defines the mappings from
hostpath regexs to handler functions. By default elnode ships
with this customization setup to serve the document root defined
in `elnode-webserver-docroot', which by default is ~/public_html."
  :group 'elnode
  :type '(boolean))

(defvar -inited nil
  "Records when elnode is initialized.

This is autoloading mechanics, see the eval-after-load for doing
init.")
)

;; Make sure we add elnode/case to the keywords
(font-lock-add-keywords
 'emacs-lisp-mode
 '(("\\<elnode/case\\>" . 'font-lock-keyword-face)))


;; Auto start elnode if we're ever loaded
;;;###autoload
(eval-after-load 'elnode
  '(progn
     (when (and (boundp 'elnode-do-init) 
                elnode-do-init)
       (condition-case err
           (progn
             (elnode-init)
             (when (and elnode-defer-on 
                        (not elnode--defer-timer))
               (elnode--init-deferring)))
         (error "Elnode could not be started.")))))


(provide 'elnode)

;;; elnode.el ends here
