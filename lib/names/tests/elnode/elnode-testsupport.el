;;; test support functions for elnode   -*- lexical-binding: t -*-

(require 'noflet)
(require 'ert)

(defmacro elnode-sink (httpcon &rest body)
  "Sink the HTTP response from BODY.

Output to `elnode-http-start', `elnode-http-send-string' and
`elnode-http-return' is collected and stored internallly.

When `elnode-http-return' is called the form ends with a string
result of whatever was sent as the response.  The string is
propertized with the header sent to `elnode-http-start'."
  (declare (indent 1)(debug (sexp &rest form)))
  `(let (res reshdr)
     (catch :elnode-sink-ret
       (noflet ((elnode-http-start (httpcon status &rest header)
                  (setq reshdr 
                        (kvalist->plist header)))
                (elnode-http-header-set (httpcon header &optional value)
                  (setq reshdr
                        (plist-put (intern (concat ":" reshdr))
                                   header value)))
                (elnode-http-send-string (httpcon data)
                  (setq res (apply 'propertize
                                   (concat res data) reshdr)))
                (elnode-http-return (httpcon &optional data)
                  (when data
                    (setq res (apply 'propertize
                                     (concat res data) reshdr)))
                  (throw :elnode-sink-ret :end)))
         ,@body))
     res))

(defmacro elnode-fake-params (httpcon params-list &rest body)
  "Fake the PARAM-BINDINGS and evaluate BODY.

PARAM-BINDINGS is an ALIST with string cars for parameter names
and string cdrs for values.  A cdr of a list can be used to
provide a string value with a property list, for example:

  '((\"param1\" . \"value\" )
    (\"param2\" \"value\" :elnode-filename \"somefile.txt\"))

Note the first parameter is an improper list.

PARAM-BINDINGS should be quoted."
  (declare (indent 2)
           (debug (sexp sexp &rest form)))
  (let ((httpconv (make-symbol "httpconv"))
        (paramsv (make-symbol "paramsv")))
    `(let ((,httpconv ,httpcon)
           (,paramsv ,params-list))
       (noflet ((elnode-http-param (httpc param-name)
                  (if (eq httpc ,httpcon)
                      (let ((v (kva param-name ,paramsv)))
                        (cond
                          ((listp v)
                           (apply 'propertize (car v) (cdr v)))
                          (t v)))
                      (funcall this-fn httpcon param-name))))
         ,@body))))


;; Extensions to ert

(defmacro should-equal (a b)
  "Simple shortcut for `(should (equal a b))'."
  `(should
    (equal ,a ,b)))

(defmacro should-match (regex a)
  "Simple shortcut for a `string-match' with `should'."
  `(should
   (string-match
    ,regex
    ,a)))

(defmacro* should-elnode-response (call
                                   &key
                                   status-code
                                   header-name
                                   header-value
                                   header-list
                                   header-list-match
                                   body-match)
  "Assert on the supplied RESPONSE.

CALL should be an `elnode-test-call', something that can make a
response.  Assertions are done by checking the specified values
of the other parameters to this function.

If STATUS-CODE is not nil we assert that the RESPONSE status-code
is equal to the STATUS-CODE.

If HEADER-NAME is present then we assert that the RESPONSE has
the header and that its value is the same as the HEADER-VALUE.
If HEADER-VALUE is `nil' then we assert that the HEADER-NAME is
NOT present.

If HEADER-LIST is present then we assert that all those headers
are present and `equal' to the value.

If HEADER-LIST-MATCH is present then we assert that all those
headers are present and `equal' to the value.

If BODY-MATCH is present then it is a regex used to match the
whole body of the RESPONSE."
  (let ((status-codev (make-symbol "status-codev"))
        (header-namev (make-symbol "header-namev"))
        (header-valuev (make-symbol "header-valuev"))
        (header-listv (make-symbol "header-listv"))
        (header-list-matchv (make-symbol "header-list-match"))
        (body-matchv (make-symbol "body-matchv"))
        (responsev (make-symbol "responsev")))
    `(let ((,responsev ,call)
           (,status-codev ,status-code)
           (,header-namev ,header-name)
           (,header-valuev ,header-value)
           (,header-listv ,header-list)
           (,header-list-matchv ,header-list-match)
           (,body-matchv ,body-match))
       (when ,status-codev
         (should
          (equal
           ,status-codev
           (plist-get ,responsev :status))))
       (when (or ,header-namev ,header-listv ,header-list-matchv)
         (let ((hdr (plist-get ,responsev :header)))
           (when ,header-namev
             (if ,header-valuev
                 (should
                  (equal
                   ,header-valuev
                   (assoc-default ,header-namev hdr)))
                 ;; Else we want to ensure the header isn't there
                 (should
                  (eq nil (assoc-default ,header-namev hdr)))))
           (when ,header-listv
             (loop for reqd-hdr in ,header-listv
                do (should
                    (equal
                     (assoc-default (car reqd-hdr) hdr)
                     (cdr reqd-hdr)))))
           (when ,header-list-matchv
             (loop for reqd-hdr in ,header-list-matchv
                do (should
                    (>=
                     (string-match
                      (cdr reqd-hdr)
                      (assoc-default (car reqd-hdr) hdr)) 0))))))
       (when ,body-matchv
         (should-match
          ,body-matchv
          (plist-get ,responsev :result-string))))))


(defmacro* assert-elnode-response (call
                                   &key
                                   status-code
                                   header-name
                                   header-value
                                   header-list
                                   header-list-match
                                   body-match)
  "Assert on the supplied RESPONSE.

CALL should be an `elnode-test-call', something that can make a
response.  Assertions are done by checking the specified values
of the other parameters to this function.

If STATUS-CODE is not nil we assert that the RESPONSE status-code
is equal to the STATUS-CODE.

If HEADER-NAME is present then we assert that the RESPONSE has
the header and that its value is the same as the HEADER-VALUE.
If HEADER-VALUE is `nil' then we assert that the HEADER-NAME is
NOT present.

If HEADER-LIST is present then we assert that all those headers
are present and `equal' to the value.

If HEADER-LIST-MATCH is present then we assert that all those
headers are present and `equal' to the value.

If BODY-MATCH is present then it is a regex used to match the
whole body of the RESPONSE."
  (let ((status-codev (make-symbol "status-codev"))
        (header-namev (make-symbol "header-namev"))
        (header-valuev (make-symbol "header-valuev"))
        (header-listv (make-symbol "header-listv"))
        (header-list-matchv (make-symbol "header-list-match"))
        (body-matchv (make-symbol "body-matchv"))
        (responsev (make-symbol "responsev")))
    `(let ((,responsev ,call)
           (,status-codev ,status-code)
           (,header-namev ,header-name)
           (,header-valuev ,header-value)
           (,header-listv ,header-list)
           (,header-list-matchv ,header-list-match)
           (,body-matchv ,body-match))
       (when ,status-codev
         (assert
          (equal
           ,status-codev
           (plist-get ,responsev :status))))
       (when (or ,header-namev ,header-listv ,header-list-matchv)
         (let ((hdr (plist-get ,responsev :header)))
           (when ,header-namev
             (if ,header-valuev
                 (assert
                  (equal
                   ,header-valuev
                   (assoc-default ,header-namev hdr)))
                 ;; Else we want to ensure the header isn't there
                 (assert
                  (eq nil (assoc-default ,header-namev hdr)))))
           (when ,header-listv
             (loop for reqd-hdr in ,header-listv
                do (assert
                    (equal
                     (assoc-default (car reqd-hdr) hdr)
                     (cdr reqd-hdr)))))
           (when ,header-list-matchv
             (loop for reqd-hdr in ,header-list-matchv
                do (assert
                    (>=
                     (string-match
                      (cdr reqd-hdr)
                      (assoc-default (car reqd-hdr) hdr)) 0))))))
       (when ,body-matchv
         (assert
          (string-match ,body-matchv (plist-get ,responsev :result-string))))
       ,responsev)))

(provide 'elnode-testsupport)

;;; elnode-testsupport.el ends here
