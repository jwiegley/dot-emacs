;;; web-server.el --- Emacs Web Server

;; Copyright (C) 2013-2014 Free Software Foundation, Inc.

;; Author: Eric Schulte <schulte.eric@gmail.com>
;; Maintainer: Eric Schulte <schulte.eric@gmail.com>
;; Version: 0.1.1
;; Package-Requires: ((emacs "24.3"))
;; Keywords: http, server, network
;; URL: https://github.com/eschulte/emacs-web-server

;; This software is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; A web server in Emacs running handlers written in Emacs Lisp.
;;
;; Full support for GET and POST requests including URL-encoded
;; parameters and multipart/form data.  Supports web sockets.
;;
;; See the examples/ directory for examples demonstrating the usage of
;; the Emacs Web Server.  The following launches a simple "hello
;; world" server.
;;
;;     (ws-start
;;      '(((lambda (_) t) .                         ; match every request
;;         (lambda (request)                        ; reply with "hello world"
;;           (with-slots (process) request
;;             (ws-response-header process 200 '("Content-type" . "text/plain"))
;;             (process-send-string process "hello world")))))
;;      9000)

;;; Code:
(require 'web-server-status-codes)
(require 'mail-parse)             ; to parse multipart data in headers
(require 'mm-encode)              ; to look-up mime types for files
(require 'url-util)               ; to decode url-encoded params
(require 'eieio)
(eval-when-compile (require 'cl))
(require 'cl-lib)

(defclass ws-server ()
  ((handlers :initarg :handlers :accessor handlers :initform nil)
   (process  :initarg :process  :accessor process  :initform nil)
   (port     :initarg :port     :accessor port     :initform nil)
   (requests :initarg :requests :accessor requests :initform nil)))

(defclass ws-request ()
  ((process  :initarg :process  :accessor process  :initform nil)
   (pending  :initarg :pending  :accessor pending  :initform "")
   (context  :initarg :context  :accessor context  :initform nil)
   (boundary :initarg :boundary :accessor boundary :initform nil)
   (index    :initarg :index    :accessor index    :initform 0)
   (active   :initarg :active   :accessor active   :initform nil)
   (headers  :initarg :headers  :accessor headers  :initform (list nil))))

(defvar ws-servers nil
  "List holding all web servers.")

(defvar ws-log-time-format "%Y.%m.%d.%H.%M.%S.%N"
  "Logging time format passed to `format-time-string'.")

(defvar ws-guid "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
  "This GUID is defined in RFC6455.")

;;;###autoload
(defun ws-start (handlers port &optional log-buffer &rest network-args)
  "Start a server using HANDLERS and return the server object.

HANDLERS may be a single function (which is then called on every
request) or a list of conses of the form (MATCHER . FUNCTION),
where the FUNCTION associated with the first successful MATCHER
is called.  Handler functions are called with two arguments, the
process and the request object.

A MATCHER may be either a function (in which case it is called on
the request object) or a cons cell of the form (KEYWORD . STRING)
in which case STRING is matched against the value of the header
specified by KEYWORD.

Any supplied NETWORK-ARGS are assumed to be keyword arguments for
`make-network-process' to which they are passed directly.

For example, the following starts a simple hello-world server on
port 8080.

  (ws-start
   (lambda (request)
     (with-slots (process headers) request
       (process-send-string process
        \"HTTP/1.1 200 OK\\r\\nContent-Type: text/plain\\r\\n\\r\\nhello world\")))
   8080)

Equivalently, the following starts an identical server using a
function MATCH and the `ws-response-header' convenience
function.

  (ws-start
   '(((lambda (_) t) .
      (lambda (proc request)
        (ws-response-header proc 200 '(\"Content-type\" . \"text/plain\"))
        (process-send-string proc \"hello world\")
        t)))
   8080)

"
  (let ((server (make-instance 'ws-server :handlers handlers :port port))
        (log (when log-buffer (get-buffer-create log-buffer))))
    (setf (process server)
          (apply
           #'make-network-process
           :name "ws-server"
           :service (port server)
           :filter 'ws-filter
           :server t
           :nowait t
           :family 'ipv4
           :coding 'no-conversion
           :plist (append (list :server server)
                          (when log (list :log-buffer log)))
           :log (when log
                  (lambda (proc request message)
                    (let ((c (process-contact request))
                          (buf (plist-get (process-plist proc) :log-buffer)))
                      (with-current-buffer buf
                        (goto-char (point-max))
                        (insert (format "%s\t%s\t%s\t%s"
                                        (format-time-string ws-log-time-format)
                                        (first c) (second c) message))))))
           network-args))
    (push server ws-servers)
    server))

(defun ws-stop (server)
  "Stop SERVER."
  (setq ws-servers (remove server ws-servers))
  (mapc #'delete-process (append (mapcar #'process (requests server))
                                 (list (process server)))))

(defun ws-stop-all ()
  "Stop all servers in `ws-servers'."
  (interactive)
  (mapc #'ws-stop ws-servers))

(defvar ws-http-common-methods '(GET HEAD POST PUT DELETE TRACE)
  "HTTP methods from http://www.w3.org/Protocols/rfc2616/rfc2616-sec9.html.")

(defvar ws-http-method-rx
  (format "^\\(%s\\) \\([^[:space:]]+\\) \\([^[:space:]]+\\)$"
          (mapconcat #'symbol-name ws-http-common-methods "\\|")))

(defun ws-parse-query-string (string)
  "Thin wrapper around `url-parse-query-string'."
  (mapcar (lambda (pair) (cons (first pair) (second pair)))
          (url-parse-query-string string nil 'allow-newlines)))

(defun ws-parse (proc string)
  "Parse HTTP headers in STRING reporting errors to PROC."
  (cl-flet ((to-keyword (s) (intern (concat ":" (upcase s)))))
    (cond
     ;; Method
     ((string-match ws-http-method-rx string)
      (let ((method (to-keyword (match-string 1 string)))
            (url (match-string 2 string)))
        (if (string-match "?" url)
            (cons (cons method (substring url 0 (match-beginning 0)))
                  (ws-parse-query-string
                   (url-unhex-string (substring url (match-end 0)))))
          (list (cons method url)))))
     ;; Authorization
     ((string-match "^AUTHORIZATION: \\([^[:space:]]+\\) \\(.*\\)$" string)
      (let ((protocol (to-keyword (match-string 1 string)))
            (credentials (match-string 2 string)))
        (list (cons :AUTHORIZATION
                    (cons protocol
                          (case protocol
                            (:BASIC
                             (let ((cred (base64-decode-string credentials)))
                               (if (string-match ":" cred)
                                   (cons (substring cred 0 (match-beginning 0))
                                         (substring cred (match-end 0)))
                                 (ws-error proc "bad credentials: %S" cred))))
                            (t (ws-error proc "un-support protocol: %s"
                                         protocol))))))))
     ;; All other headers
     ((string-match "^\\([^[:space:]]+\\): \\(.*\\)$" string)
      (list (cons (to-keyword (match-string 1 string))
                  (match-string 2 string))))
     (:otherwise (ws-error proc "bad header: %S" string) nil))))

(defun ws-trim (string)
  (while (and (> (length string) 0)
              (or (and (string-match "[\r\n]" (substring string -1))
                       (setq string (substring string 0 -1)))
                  (and (string-match "[\r\n]" (substring string 0 1))
                       (setq string (substring string 1))))))
  string)

(defun ws-parse-multipart/form (proc string)
  ;; ignore empty and non-content blocks
  (when (string-match "Content-Disposition:[[:space:]]*\\(.*\\)\r\n" string)
    (let ((dp (cdr (mail-header-parse-content-disposition
                    (match-string 1 string))))
          (last-index (match-end 0))
          index)
      ;; every line up until the double \r\n is a header
      (while (and (setq index (string-match "\r\n" string last-index))
                  (not (= index last-index)))
        (setcdr (last dp) (ws-parse proc (substring string last-index index)))
        (setq last-index (+ 2 index)))
      ;; after double \r\n is all content
      (cons (cdr (assoc 'name dp))
            (cons (cons 'content (substring string (+ 2 last-index)))
                  dp)))))

(defun ws-filter (proc string)
  (with-slots (handlers requests) (plist-get (process-plist proc) :server)
    (unless (cl-find-if (lambda (c) (equal proc (process c))) requests)
      (push (make-instance 'ws-request :process proc) requests))
    (let ((request (cl-find-if (lambda (c) (equal proc (process c))) requests)))
      (with-slots (pending) request (setq pending (concat pending string)))
      (unless (active request) ; don't re-start if request is being parsed
        (setf (active request) t)
        (when (not (eq (catch 'close-connection
                         (if (ws-parse-request request)
                             (ws-call-handler request handlers)
                           :keep-alive))
                       :keep-alive))
          ;; Properly shut down processes requiring an ending (e.g., chunked)
          (let ((ender (plist-get (process-plist proc) :ender)))
            (when ender (process-send-string proc ender)))
          (setq requests (cl-remove-if (lambda (r) (eql proc (process r))) requests))
          (delete-process proc))))))

(defun ws-parse-request (request)
  "Parse request STRING from REQUEST with process PROC.
Return non-nil only when parsing is complete."
  (catch 'finished-parsing-headers
    (with-slots (process pending context boundary headers index) request
      (let ((delimiter (concat "\r\n" (if boundary (concat "--" boundary) "")))
            ;; Track progress through string, always work with the
            ;; section of string between INDEX and NEXT-INDEX.
            next-index)
        ;; parse headers and append to request
        (while (setq next-index (string-match delimiter pending index))
          (let ((tmp (+ next-index (length delimiter))))
            (if (= index next-index) ; double \r\n ends current run of headers
                (case context
                  ;; Parse URL data.
                  ;; http://www.w3.org/TR/html4/interact/forms.html#h-17.13.4
                  (application/x-www-form-urlencoded
                   (mapc (lambda (pair) (setcdr (last headers) (list pair)))
                         (ws-parse-query-string
                          (replace-regexp-in-string
                           "\\+" " "
                           (ws-trim (substring pending index)))))
                   (throw 'finished-parsing-headers t))
                  ;; Set custom delimiter for multipart form data.
                  (multipart/form-data
                   (setq delimiter (concat "\r\n--" boundary)))
                  ;; No special context so we're done.
                  (t (throw 'finished-parsing-headers t)))
              (if (eql context 'multipart/form-data)
                  (progn
                    (setcdr (last headers)
                            (list (ws-parse-multipart/form process
                                    (substring pending index next-index))))
                    ;; Boundary suffixed by "--" indicates end of the headers.
                    (when (and (> (length pending) (+ tmp 2))
                               (string= (substring pending tmp (+ tmp 2)) "--"))
                      (throw 'finished-parsing-headers t)))
                ;; Standard header parsing.
                (let ((header (ws-parse process (substring pending
                                                           index next-index))))
                  ;; Content-Type indicates that the next double \r\n
                  ;; will be followed by a special type of content which
                  ;; will require special parsing.  Thus we will note
                  ;; the type in the CONTEXT variable for parsing
                  ;; dispatch above.
                  (if (and (caar header) (eql (caar header) :CONTENT-TYPE))
                      (cl-destructuring-bind (type &rest data)
                          (mail-header-parse-content-type (cdar header))
                        (setq boundary (cdr (assoc 'boundary data)))
                        (setq context (intern (downcase type))))
                    ;; All other headers are collected directly.
                    (setcdr (last headers) header)))))
            (setq index tmp)))))
    (setf (active request) nil)
    nil))

(defun ws-call-handler (request handlers)
  (catch 'matched-handler
    (when (functionp handlers)
      (throw 'matched-handler
             (condition-case e (funcall handlers request)
               (error (ws-error (process request) "Caught Error: %S" e)))))
    (mapc (lambda (handler)
            (let ((match (car handler))
                  (function (cdr handler)))
              (when (or (and (consp match)
                             (assoc (car match) (headers request))
                             (string-match (cdr match)
                                           (cdr (assoc (car match)
                                                       (headers request)))))
                        (and (functionp match) (funcall match request)))
                (throw 'matched-handler
                       (condition-case e (funcall function request)
                         (error (ws-error (process request)
                                          "Caught Error: %S" e)))))))
          handlers)
    (ws-error (process request) "no handler matched request: %S"
              (headers request))))

(defun ws-error (proc msg &rest args)
  (let ((buf (plist-get (process-plist proc) :log-buffer))
        (c (process-contact proc)))
    (when buf
      (with-current-buffer buf
        (goto-char (point-max))
        (insert (format "%s\t%s\t%s\tWS-ERROR: %s"
                        (format-time-string ws-log-time-format)
                        (first c) (second c)
                        (apply #'format msg args)))))
    (apply #'ws-send-500 proc msg args)))


;;; Web Socket
;; Implement to conform to http://tools.ietf.org/html/rfc6455.

;; The `ws-message' object is used to hold state across multiple calls
;; of the process filter on the websocket network process.  The fields
;; play the following roles.
;; process ------ holds the process itself, used for communication
;; pending ------ holds text received from the client but not yet parsed
;; active ------- indicates that parsing is active to avoid re-entry
;;                of the `ws-web-socket-parse-messages' function
;; new ---------- indicates that new text was received during parsing
;;                and causes `ws-web-socket-parse-messages' to be
;;                called again after it terminates
;; data --------- holds the data of parsed messages
;; handler ------ holds the user-supplied function used called on the
;;                data of parsed messages
(defclass ws-message ()                 ; web socket message object
  ((process  :initarg :process  :accessor process  :initform "")
   (pending  :initarg :pending  :accessor pending  :initform "")
   (active   :initarg :active   :accessor active   :initform nil)
   (new      :initarg :new      :accessor new      :initform nil)
   (data     :initarg :data     :accessor data     :initform "")
   (handler  :initarg :handler  :accessor handler  :initform "")))

(defun ws-web-socket-connect (request handler)
  "Establish a web socket connection with request.
If the connection is successful this function will throw
`:keep-alive' to `close-connection' skipping any remaining code
in the request handler.  If no web-socket connection is
established (e.g., because REQUEST is not attempting to establish
a connection) then no actions are taken and nil is returned.

Second argument HANDLER should be a function of one argument
which will be called on all complete messages as they are
received and parsed from the network."
  (with-slots (process headers) request
    (when (assoc :SEC-WEBSOCKET-KEY headers)
      ;; Accept the connection
      (ws-response-header process 101
        (cons "Upgrade" "websocket")
        (cons "Connection" "upgrade")
        (cons "Sec-WebSocket-Accept"
              (ws-web-socket-handshake
               (cdr (assoc :SEC-WEBSOCKET-KEY headers)))))
      ;; Setup the process filter
      (set-process-coding-system process 'binary)
      (set-process-plist
       process (list :message (make-instance 'ws-message
                                :handler handler :process process)))
      (set-process-filter process 'ws-web-socket-filter)
      process)))

(defun ws-web-socket-filter (process string)
  (let ((message (plist-get (process-plist process) :message)))
    (if (active message) ; don't re-start if message is being parsed
        (setf (new message) string)
      (setf (pending message) (concat (pending message) string))
      (setf (active message) t)
      (ws-web-socket-parse-messages message))
    (setf (active message) nil)))

(defun ws-web-socket-mask (masking-key data)
  (let ((masking-data (apply #'concat (make-list (+ 1 (/ (length data) 4))
                                                 masking-key))))
    (apply #'string (cl-mapcar #'logxor masking-data data))))

;; Binary framing protocol
;; from http://tools.ietf.org/html/rfc6455#section-5.2
;;
;;  0                   1                   2                   3
;;  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
;; +-+-+-+-+-------+-+-------------+-------------------------------+
;; |F|R|R|R| opcode|M| Payload len |    Extended payload length    |
;; |I|S|S|S|  (4)  |A|     (7)     |             (16/64)           |
;; |N|V|V|V|       |S|             |   (if payload len==126/127)   |
;; | |1|2|3|       |K|             |                               |
;; +-+-+-+-+-------+-+-------------+ - - - - - - - - - - - - - - - +
;; |     Extended payload length continued, if payload len == 127  |
;; + - - - - - - - - - - - - - - - +-------------------------------+
;; |                               |Masking-key, if MASK set to 1  |
;; +-------------------------------+-------------------------------+
;; | Masking-key (continued)       |          Payload Data         |
;; +-------------------------------- - - - - - - - - - - - - - - - +
;; :                     Payload Data continued ...                :
;; + - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - +
;; |                     Payload Data continued ...                |
;; +---------------------------------------------------------------+
;;
(defun ws-web-socket-parse-messages (message)
  "Web socket filter to pass whole frames to the client.
See RFC6455."
  (with-slots (process active pending data handler new) message
    (let ((index 0))
      (cl-labels ((int-to-bits (int size)
                    (let ((result (make-bool-vector size nil)))
                      (mapc (lambda (place)
                              (let ((val (expt 2 place)))
                                (when (>= int val)
                                  (setq int (- int val))
                                  (aset result place t))))
                            (reverse (number-sequence 0 (- size 1))))
                      (reverse (append result nil))))
                  (bits-to-int (bits)
                    (let ((place 0))
                      (apply #'+
                       (mapcar (lambda (bit)
                                 (prog1 (if bit (expt 2 place) 0) (incf place)))
                               (reverse bits)))))
                  (bits (length)
                    (apply #'append
                           (mapcar (lambda (int) (int-to-bits int 8))
                                   (cl-subseq
                                    pending index (incf index length))))))
        (let (fin rsvs opcode mask pl mask-key)
          ;; Parse fin bit, rsvs bits and opcode
          (let ((byte (bits 1)))
            (setq fin (car byte)
                  rsvs (cl-subseq byte 1 4)
                  opcode
                  (let ((it (bits-to-int (cl-subseq byte 4))))
                    (case it
                      (0 :CONTINUATION)
                      (1 :TEXT)
                      (2 :BINARY)
                      ((3 4 5 6 7) :NON-CONTROL)
                      (8 :CLOSE)
                      (9 :PING)
                      (10 :PONG)
                      ((11 12 13 14 15) :CONTROL)
                      ;; If an unknown opcode is received, the receiving
                      ;; endpoint MUST _Fail the WebSocket Connection_.
                      (t (ws-error process
                                   "Web Socket Fail: bad opcode %d" it))))))
          (unless (cl-every #'null rsvs)
            ;; MUST be 0 unless an extension is negotiated that defines
            ;; meanings for non-zero values.
            (ws-error process "Web Socket Fail: non-zero RSV 1 2 or 3"))
          ;; Parse mask and payload length
          (let ((byte (bits 1)))
            (setq mask (car byte)
                  pl (bits-to-int (cl-subseq byte 1))))
          (unless (eq mask t)
            ;; All frames sent from client to server have this bit set to 1.
            (ws-error process "Web Socket Fail: client must mask data"))
          (cond
           ((= pl 126) (setq pl (bits-to-int (bits 2))))
           ((= pl 127) (setq pl (bits-to-int (bits 8)))))
          ;; unmask data
          (when mask (setq mask-key (cl-subseq pending index (incf index 4))))
          (setq data (concat data
                             (ws-web-socket-mask
                              mask-key (cl-subseq pending index (+ index pl)))))
          (if fin
              ;; wipe the message state and call the handler
              (let ((it data))
                (setq data "" active nil pending "" new nil)
                ;; close on a close frame, otherwise call the handler
                (if (not (eql opcode :CLOSE))
                    (funcall handler process it)
                  (process-send-string process
                    (unibyte-string (logior (lsh 1 7) 8) 0))))
            ;; add any remaining un-parsed network data to pending
            (when (< (+ index pl) (length pending))
              (setq pending (substring pending (+ index pl)))))))
      ;; possibly re-parse any pending input
      (when (new message) (ws-web-socket-parse-messages message)))))

(defun ws-web-socket-frame (string &optional opcode)
  "Frame STRING for web socket communication."
  (let* ((fin 1) ;; set to 0 if not final frame
         (len (length string))
         (opcode (ecase (or opcode :TEXT) (:TEXT 1) (:BINARY 2))))
    ;; Does not do any masking which is only required of client communication
    (concat
     (cond
      ((< len 126) (unibyte-string (logior (lsh fin 7) opcode) len))
      ((< len 65536) (unibyte-string (logior (lsh fin 7) opcode) 126
                                     ;; extended 16-bit length
                                     (logand (lsh len -8) 255)
                                     (logand      len     255)))
      (t (unibyte-string (logior (lsh fin 7) opcode) 127
                         ;; more extended 64-bit length
                         (logand (lsh len -56) 255)
                         (logand (lsh len -48) 255)
                         (logand (lsh len -40) 255)
                         (logand (lsh len -32) 255)
                         (logand (lsh len -24) 255)
                         (logand (lsh len -16) 255)
                         (logand (lsh len -8)  255)
                         (logand      len      255))))
     string)))


;;; Content and Transfer encoding support
(defvar ws-compress-cmd "compress"
  "Command used for the \"compress\" Content or Transfer coding.")

(defvar ws-deflate-cmd "zlib-flate -compress"
  "Command used for the \"deflate\" Content or Transfer coding.")

(defvar ws-gzip-cmd "gzip"
  "Command used for the \"gzip\" Content or Transfer coding.")

(defmacro ws-encoding-cmd-to-fn (cmd)
  "Return a function which applies CMD to strings."
  `(lambda (s)
     (with-temp-buffer
       (insert s)
       (shell-command-on-region (point-min) (point-max) ,cmd nil 'replace)
       (buffer-string))))

(defun ws-chunk (string)
  "Convert STRING to a valid chunk for HTTP chunked Transfer-encoding."
  (format "%x\r\n%s\r\n" (string-bytes string) string))


;;; Convenience functions to write responses
(defun ws-response-header (proc code &rest headers)
  "Send the headers for an HTTP response to PROC.
CODE should be an HTTP status code, see `ws-status-codes' for a
list of known codes.

When \"Content-Encoding\" or \"Transfer-Encoding\" headers are
supplied any subsequent data written to PROC using `ws-send' will
be encoded appropriately including sending the appropriate data
upon the end of transmission for chunked transfer encoding.

For example with the header `(\"Content-Encoding\" . \"gzip\")',
any data subsequently written to PROC using `ws-send' will be
compressed using the command specified in `ws-gzip-cmd'."
  ;; update process to reflect any Content or Transfer encodings
  (let ((content  (cdr (assoc "Content-Encoding" headers)))
        (transfer (cdr (assoc "Transfer-Encoding" headers))))
    (when content
      (set-process-plist proc
        (append
         (list :content-encoding
               (ecase (intern content)
                 ((compress x-compress) (ws-encoding-cmd-to-fn ws-compress-cmd))
                 ((deflate x-deflate)   (ws-encoding-cmd-to-fn ws-deflate-cmd))
                 ((gzip x-gzip)         (ws-encoding-cmd-to-fn ws-gzip-cmd))
                 (identity #'identity)
                 ((exi pack200-zip)
                  (ws-error proc "`%s' Content-encoding not supported."
                            content))))
         (process-plist proc))))
    (when transfer
      (set-process-plist proc
        (append
         (when (string= transfer "chunked") (list :ender "0\r\n\r\n"))
         (list :transfer-encoding
               (ecase (intern transfer)
                 (chunked  #'ws-chunk)
                 ((compress x-compress) (ws-encoding-cmd-to-fn ws-compress-cmd))
                 ((deflate x-deflate)   (ws-encoding-cmd-to-fn ws-deflate-cmd))
                 ((gzip x-gzip)         (ws-encoding-cmd-to-fn ws-gzip-cmd))))
         (process-plist proc)))))
  (let ((headers
         (cons
          (format "HTTP/1.1 %d %s" code (cdr (assoc code ws-status-codes)))
          (mapcar (lambda (h) (format "%s: %s" (car h) (cdr h))) headers))))
    (setcdr (last headers) (list "" ""))
    (process-send-string proc (mapconcat #'identity headers "\r\n"))))

(defun ws-send (proc string)
  "Send STRING to process PROC.
If any Content or Transfer encodings are in use, apply them to
STRING before sending."
  (let
      ((cc (or (plist-get (process-plist proc) :content-encoding) #'identity))
       (tc (or (plist-get (process-plist proc) :transfer-encoding) #'identity)))
    (process-send-string proc (funcall tc (funcall cc string)))))

(defun ws-send-500 (proc &rest msg-and-args)
  "Send 500 \"Internal Server Error\" to PROC with an optional message."
  (ws-response-header proc 500
    '("Content-type" . "text/plain"))
  (process-send-string proc (if msg-and-args
                                (apply #'format msg-and-args)
                              "500 Internal Server Error"))
  (throw 'close-connection nil))

(defun ws-send-404 (proc &rest msg-and-args)
  "Send 404 \"Not Found\" to PROC with an optional message."
  (ws-response-header proc 404
    '("Content-type" . "text/plain"))
  (process-send-string proc (if msg-and-args
                                (apply #'format msg-and-args)
                              "404 Not Found"))
  (throw 'close-connection nil))

(defun ws-send-file (proc path &optional mime-type)
  "Send PATH to PROC.
Optionally explicitly set MIME-TYPE, otherwise it is guessed by
`mm-default-file-encoding'."
  (let ((mime (or mime-type
                  (mm-default-file-encoding path)
                  "application/octet-stream")))
    (process-send-string proc
      (with-temp-buffer
        (insert-file-contents-literally path)
        (ws-response-header proc 200
          (cons "Content-type" mime)
          (cons "Content-length" (- (point-max) (point-min))))
        (buffer-string)))))

(defun ws-send-directory-list (proc directory &optional match)
  "Send a listing of files in DIRECTORY to PROC.
Optional argument MATCH is passed to `directory-files' and may be
used to limit the files sent."
  (ws-response-header proc 200 (cons "Content-type" "text/html"))
  (process-send-string proc
    (concat "<ul>"
            (mapconcat (lambda (f)
                         (let* ((full (expand-file-name f directory))
                                (end (if (file-directory-p full) "/" ""))
                                (url (url-encode-url (concat f end))))
                           (format "<li><a href=%s>%s</li>" url f)))
                       (directory-files directory nil match)
                       "\n")
            "</ul>")))

(defun ws-in-directory-p (parent path)
  "Check if PATH is under the PARENT directory.
If so return PATH, if not return nil.  Note: the PARENT directory
must be full expanded as with `expand-file-name' and should not
contain e.g., \"~\" for a user home directory."
  (if (zerop (length path))
      parent
    (let ((expanded (expand-file-name path parent)))
      (and (>= (length expanded) (length parent))
           (string= parent (substring expanded 0 (length parent)))
           expanded))))

(defun ws-with-authentication (handler credentials
                                       &optional realm unauth invalid)
  "Return a version of HANDLER protected by CREDENTIALS.
HANDLER should be a function as passed to `ws-start', and
CREDENTIALS should be an alist of elements of the form (USERNAME
. PASSWORD).

Optional argument REALM sets the realm in the authentication
challenge.  Optional arguments UNAUTH and INVALID should be
functions which are called on the request when no authentication
information, or invalid authentication information are provided
respectively."
  (lexical-let ((handler handler)
                (credentials credentials)
                (realm realm)
                (unauth unauth)
                (invalid invalid))
    (lambda (request)
      (with-slots (process headers) request
        (let ((auth (cddr (assoc :AUTHORIZATION headers))))
          (cond
           ;; no authentication information provided
           ((not auth)
            (if unauth
                (funcall unauth request)
              (ws-response-header process 401
                (cons "WWW-Authenticate"
                      (format "Basic realm=%S" (or realm "restricted")))
                '("Content-type" . "text/plain"))
              (process-send-string process "authentication required")))
           ;; valid authentication information
           ((string= (cdr auth) (cdr (assoc (car auth) credentials)))
            (funcall handler request))
           ;; invalid authentication information
           (t
            (if invalid
                (funcall invalid request)
              (ws-response-header process 403 '("Content-type" . "text/plain"))
              (process-send-string process "invalid credentials")))))))))

(defun ws-web-socket-handshake (key)
  "Perform the handshake defined in RFC6455."
  (base64-encode-string (sha1 (concat (ws-trim key) ws-guid) nil nil 'binary)))

(provide 'web-server)
;;; web-server.el ends here
