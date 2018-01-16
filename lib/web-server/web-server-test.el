;;; web-server-test.el --- Test the Emacs Web Server

;; Copyright (C) 2013-2014  Free Software Foundation, Inc.

;; Author: Eric Schulte <schulte.eric@gmail.com>

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

;;; Code:
(require 'web-server)
(require 'cl-lib)
(eval-when-compile (require 'cl))
(require 'ert)

(defvar ws-test-port 8999)

(defun ws-test-curl-to-string (url &optional get-params post-params curl-flags)
  "Curl URL with optional parameters."
  (async-shell-command
   (format "curl -s -m 4 %s %s %s localhost:%s/%s"
           (or curl-flags "")
           (if get-params
               (mapconcat (lambda (p) (format "-d \"%s=%s\"" (car p) (cdr p)))
                          get-params " ")
             "")
           (if post-params
               (mapconcat (lambda (p) (format "-F \"%s=%s\"" (car p) (cdr p)))
                          post-params " ")
             "")
           ws-test-port url))
  (unwind-protect
      (with-current-buffer "*Async Shell Command*"
        (while (get-buffer-process (current-buffer)) (sit-for 0.1))
        (goto-char (point-min))
        (buffer-string))
    (kill-buffer "*Async Shell Command*")))

(defmacro ws-test-with (handler &rest body)
  (declare (indent 1))
  (let ((srv (cl-gensym)))
    `(let* ((,srv (ws-start ,handler ws-test-port)))
       (unwind-protect (progn ,@body) (ws-stop ,srv)))))
(def-edebug-spec ws-test-with (form body))

(ert-deftest ws/keyword-style-handler ()
  "Ensure that a simple keyword-style handler matches correctly."
  (ws-test-with (mapcar (lambda (letter)
                           `((:GET . ,letter) .
                             (lambda (request)
                               (ws-response-header (process request) 200
                                 '("Content-type" . "text/plain"))
                               (process-send-string (process request)
                                 (concat "returned:" ,letter)))))
                         '("a" "b"))
    (should (string= "returned:a" (ws-test-curl-to-string "a")))
    (should (string= "returned:b" (ws-test-curl-to-string "b")))))

(ert-deftest ws/function-style-handler ()
  "Test that a simple hello-world server responds."
  (ws-test-with
      '(((lambda (_) t) .
         (lambda (request)
           (ws-response-header (process request) 200
             '("Content-type" . "text/plain"))
           (process-send-string (process request) "hello world"))))
    (should (string= (ws-test-curl-to-string "") "hello world"))))

(ert-deftest ws/removed-from-ws-servers-after-stop ()
  (let ((start-length (length ws-servers)))
    (let ((server (ws-start nil ws-test-port)))
      (should (= (length ws-servers) (+ 1 start-length)))
      (ws-stop server)
      (should (= (length ws-servers) start-length)))))

(ert-deftest ws/parse-many-headers ()
  "Test that a number of headers parse successfully."
  (let ((server (ws-start nil ws-test-port))
        (request (make-instance 'ws-request)))
    (unwind-protect
        (progn
          (setf (pending request)
                "GET / HTTP/1.1
Host: localhost:7777
User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:26.0) Gecko/20100101 Firefox/26.0
Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
Accept-Language: en-US,en;q=0.5
Accept-Encoding: gzip, deflate
DNT: 1
Cookie: __utma=111872281.1462392269.1345929539.1345929539.1345929539.1
Connection: keep-alive

")
          (ws-parse-request request)
          (let ((headers (cdr (headers request))))
            (should (string= (cdr (assoc :ACCEPT-ENCODING headers))
                             "gzip, deflate"))
            (should (string= (cdr (assoc :GET headers)) "/"))
            (should (string= (cdr (assoc :CONNECTION headers)) "keep-alive"))))
      (ws-stop server))))

(ert-deftest ws/parse-post-data ()
  (let ((server (ws-start nil ws-test-port))
        (request (make-instance 'ws-request)))
    (unwind-protect
        (progn
          (setf (pending request)
                "POST / HTTP/1.1
User-Agent: curl/7.33.0
Host: localhost:8080
Accept: */*
Content-Length: 273
Expect: 100-continue
Content-Type: multipart/form-data; boundary=----------------f1270d0deb77af03

------------------f1270d0deb77af03
Content-Disposition: form-data; name=\"date\"

Wed Dec 18 00:55:39 MST 2013

------------------f1270d0deb77af03
Content-Disposition: form-data; name=\"name\"

\"schulte\"
------------------f1270d0deb77af03--
")
          (ws-parse-request request)
          (let ((headers (cdr (headers request))))
            (should (string= (cdr (assoc 'content (cdr (assoc "name" headers))))
                             "\"schulte\""))
            (should (string= (cdr (assoc 'content (cdr (assoc "date" headers))))
                             "Wed Dec 18 00:55:39 MST 2013\n"))))
      (ws-stop server))))

(ert-deftest ws/parse-another-post-data ()
  "This one from an AJAX request."
  (let ((server (ws-start nil ws-test-port))
        (request (make-instance 'ws-request)))
    (unwind-protect
        (progn
          (setf (pending request)
                "POST /complex.org HTTP/1.1
Host: localhost:4444
User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:26.0) Gecko/20100101 Firefox/26.0
Accept: */*
Accept-Language: en-US,en;q=0.5
Accept-Encoding: gzip, deflate
DNT: 1
Content-Type: application/x-www-form-urlencoded; charset=UTF-8
X-Requested-With: XMLHttpRequest
Referer: http://localhost:4444/complex.org
Content-Length: 78
Cookie: __utma=111872281.1462392269.1345929539.1345929539.1345929539.1
Connection: keep-alive
Pragma: no-cache
Cache-Control: no-cache

org=-+one%0A-+two%0A-+three%0A-+four%0A%0A&beg=646&end=667&path=%2Fcomplex.org")
          (ws-parse-request request)
          (let ((headers (cdr (headers request))))
            (should (string= (cdr (assoc "path" headers)) "/complex.org"))
            (should (string= (cdr (assoc "beg" headers)) "646"))
            (should (string= (cdr (assoc "end" headers)) "667"))
            (should (string= (cdr (assoc "org" headers))
                             "- one
- two
- three
- four

"))))
      (ws-stop server))))

(ert-deftest ws/simple-post ()
  "Test a simple POST server."
  (ws-test-with
      '(((:POST . ".*") .
         (lambda (request)
           (with-slots (process headers) request
             (let ((message (cdr (assoc "message" headers))))
               (ws-response-header process 200
                 '("Content-type" . "text/plain"))
               (process-send-string process
                 (format "you said %S\n" (cdr (assoc 'content message)))))))))
    (should (string= (ws-test-curl-to-string "" nil '(("message" . "foo")))
                     "you said \"foo\"\n"))))

(ert-deftest ws/in-directory-p ()
  (mapc (lambda (pair)
          (let ((should-or-not (car pair))
                (dir (cdr pair)))
            (message "dir: %S" dir)
            (should
             (funcall (if should-or-not #'identity #'not)
                      (ws-in-directory-p temporary-file-directory dir)))))
        `((nil . "foo/bar/../../../")
          (t   . ,(concat
                   "foo/bar/../../../"
                   (file-name-nondirectory
                    (directory-file-name temporary-file-directory))
                   "/baz"))
          (t   . "./")
          (nil . "/~/pics")
          (nil . "~/pics")
          (nil . "/pics")
          (nil . "../pics")
          (t   . "pics")
          (nil . ".."))))

(ert-deftest ws/parse-basic-authorization ()
  "Test that a number of headers parse successfully."
  (let* ((server (ws-start nil ws-test-port))
         (request (make-instance 'ws-request))
         (username "foo") (password "bar"))
    (unwind-protect
        (progn
          (setf (pending request)
                (format "GET / HTTP/1.1
Authorization: Basic %s
Connection: keep-alive

" (base64-encode-string (concat username ":" password))))
          (ws-parse-request request)
          (with-slots (headers) request
            (cl-tree-equal (cdr (assoc :AUTHORIZATION headers))
                           (cons :BASIC (cons username password)))))
      (ws-stop server))))

(ert-deftest ws/parse-large-file-upload ()
  "Test that `ws-parse-request' can handle at large file upload.
At least when it comes in a single chunk."
  (let* ((long-string (mapconcat #'int-to-string (number-sequence 0 20000) " "))
         (server (ws-start nil ws-test-port))
         (request (make-instance 'ws-request)))
    (unwind-protect
        (progn
          (setf (pending request)
                (format "POST / HTTP/1.1
User-Agent: curl/7.34.0
Host: localhost:9008
Accept: */*
Content-Length: 9086
Expect: 100-continue
Content-Type: multipart/form-data; boundary=----------------e458fb665704290b

------------------e458fb665704290b
Content-Disposition: form-data; name=\"file\"; filename=\"-\"
Content-Type: application/octet-stream

%s
------------------e458fb665704290b--

" long-string))
          (ws-parse-request request)
          (should
           (string= long-string
                    (cdr (assoc 'content
                                (cdr (assoc "file" (headers request))))))))
      (ws-stop server))))

(ert-deftest ws/web-socket-handshake-rfc-example ()
  "Ensure that `ws-web-socket-handshake' conforms to the example in RFC6455."
  (should (string= (ws-web-socket-handshake "dGhlIHNhbXBsZSBub25jZQ==")
                   "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=")))

(ert-deftest ws/web-socket-frame ()
  "Test WebSocket frame encoding for the different varint payload lengths:
   0-125, 126-64k, 64k-2^64."
  (should (string= (ws-web-socket-frame "short") "\201short"))
  (should (string= (substring (ws-web-socket-frame (make-string 126 ?a))
                              0 5) "\201~ ~a"))
  (should (string= (substring (ws-web-socket-frame (make-string 65536 ?a))
                              0 11) "\201       a")))

(ert-deftest ws/simple-chunked ()
  "Test a simple server using chunked transfer encoding."
  (ws-test-with
      (lambda (request)
        (with-slots (process) request
          (ws-response-header process 200
            '("Content-type" . "text/plain")
            '("Transfer-Encoding" . "chunked"))
          (ws-send process "I am chunked")))
    (should (string= (ws-test-curl-to-string "") "I am chunked"))))

(ert-deftest ws/simple-gzip ()
  "Test a simple server using gzip content/transfer encoding."
  (cl-macrolet ((gzipper (header)
                         `(ws-test-with
                              (lambda (request)
                                (with-slots (process) request
                                  (ws-response-header process 200
                                    '("Content-type" . "text/plain")
                                    '(,header . "gzip"))
                                  (ws-send process "I am zipped")))
                            (should (string= (ws-test-curl-to-string
                                              "" nil nil "--compressed")
                                             "I am zipped")))))
    (gzipper "Content-Encoding")
    (gzipper "Transfer-Encoding")))

(provide 'web-server-test)
