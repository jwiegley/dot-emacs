;;; simple-httpd-test.el --- simple-httpd unit tests

;;; Commentary:

;; Run standalone with this,
;;   emacs -batch -L . -l simple-httpd-test.el -f ert-run-tests-batch

;;; Code:

(require 'ert)
(require 'cl-lib)
(require 'simple-httpd)

(defmacro httpd--flet (funcs &rest body)
  "Like `cl-flet' but with dynamic function scope."
  (declare (indent 1))
  (let* ((names (mapcar #'car funcs))
         (lambdas (mapcar #'cdr funcs))
         (gensyms (cl-loop for name in names
                           collect (make-symbol (symbol-name name)))))
    `(let ,(cl-loop for name in names
                    for gensym in gensyms
                    collect `(,gensym (symbol-function ',name)))
       (unwind-protect
           (progn
             ,@(cl-loop for name in names
                        for lambda in lambdas
                        for body = `(lambda ,@lambda)
                        collect `(setf (symbol-function ',name) ,body))
             ,@body)
         ,@(cl-loop for name in names
                    for gensym in gensyms
                    collect `(setf (symbol-function ',name) ,gensym))))))

(ert-deftest httpd-clean-path-test ()
  "Ensure that paths are sanitized properly."
  (should (equal (httpd-clean-path "/") "./"))
  (should (equal (httpd-clean-path "../") "./"))
  (should (equal (httpd-clean-path "/../../foo/../..") "./foo"))
  (should (equal (httpd-clean-path "/tmp/../root/foo") "./tmp/root/foo"))
  (should (equal (httpd-clean-path "~") "./~"))
  (should (equal (httpd-clean-path "/~/.gnupg") "./~/.gnupg")))

(ert-deftest httpd-mime-test ()
  "Test MIME type fetching."
  (should (equal (httpd-get-mime "txt") "text/plain"))
  (should (equal (httpd-get-mime "unknown") "application/octet-stream"))
  (should (equal (httpd-get-mime nil) "application/octet-stream")))

(ert-deftest httpd-parse-test ()
  "Test HTTP header parsing."
  (with-temp-buffer
    (set-buffer-multibyte nil)
    (insert "GET /f%20b HTTP/1.1\r\n"
            "Host: localhost:8080\r\n"
            "DNT: 1, 2\r\n\r\n")
    (let ((p (httpd-parse)))
      (should (equal (cl-cadar p) "/f%20b"))
      (should (equal (cadr (assoc "Host" p)) "localhost:8080"))
      (should (equal (cadr (assoc "Dnt" p)) "1, 2")))))

(ert-deftest httpd-parse-uri-test ()
  "Test URI parsing."
  (let* ((url "/foo/bar%20baz.html?q=test%26case&v=10#page10")
         (p (httpd-parse-uri url))
         (args (cadr p))
         (fragment (cl-caddr p)))
    (should (equal (car p) "/foo/bar baz.html"))
    (should (equal (cadr (assoc "v" args)) "10"))
    (should (equal (cadr (assoc "q" args)) "test&case"))
    (should (equal fragment "page10"))))

(ert-deftest httpd-send-header-test ()
  "Test server header output."
  (with-temp-buffer
    (set-buffer-multibyte nil)
    (let ((buffer (current-buffer)))
      (httpd--flet ((process-send-region (_proc _start _end)
                      (let ((send-buffer (current-buffer)))
                        (with-current-buffer buffer
                          (insert-buffer-substring send-buffer)))))
        (httpd-send-header nil "text/html" 404 :Foo "bar")))
    (let ((out (httpd-parse)))
      (should (equal (cl-cadar out) "404"))
      (should (equal (cadr (assoc "Content-Type" out)) "text/html"))
      (should (equal (cadr (assoc "Foo" out)) "bar")))))

(ert-deftest httpd-status-test ()
  "Test HTTP status message for mocked request states."
  (httpd--flet ((file-exists-p (file) t)
                (file-readable-p (file) nil))
    (should (eq (httpd-status "/some/file") 403)))
  (httpd--flet ((file-exists-p (file) nil))
    (should (eq (httpd-status "/some/file") 404)))
  (httpd--flet ((file-exists-p (file) t)
                (file-readable-p (file) t)
                (file-directory-p (file) nil))
    (should (eq (httpd-status "/some/file") 200)))
  (httpd--flet ((file-exists-p (file) t)
                (file-readable-p (file) t)
                (file-directory-p (file) t))
    (let ((httpd-listings nil))
      (should (eq (httpd-status "/some/file") 403)))
    (let ((httpd-listings t))
      (should (eq (httpd-status "/some/file") 200)))))

(ert-deftest httpd-get-servlet-test ()
  "Test servlet dispatch."
  (httpd--flet ((httpd/foo/bar () t))
    (let ((httpd-servlets t))
      (should (eq (httpd-get-servlet "/foo/bar")     'httpd/foo/bar))
      (should (eq (httpd-get-servlet "/foo/bar/baz") 'httpd/foo/bar))
      (should (eq (httpd-get-servlet "/undefined")   'httpd/)))))

(ert-deftest httpd-unhex-test ()
  "Test URL decoding."
  (should (equal (httpd-unhex "I+%2Bam%2B+foo.") "I +am+ foo."))
  (should (equal (httpd-unhex "foo%0D%0Abar") "foo\nbar"))
  (should (equal (httpd-unhex "na%C3%AFve") "naïve"))
  (should (eq (httpd-unhex nil) nil)))

(ert-deftest httpd-parse-args-test ()
  "Test argument parsing."
  (should (equal (httpd-parse-args "na=foo&v=1") '(("na" "foo") ("v" "1"))))
  (should (equal (httpd-parse-args "") ())))

(ert-deftest httpd-parse-endpoint ()
  "Test endpoint parsing for defservlet*."
  (should (equal (httpd-parse-endpoint 'example/foos/:n/:d)
                 '(example/foos ((n . 2) (d . 3))))))

;;; simple-httpd-test.el ends here
