(require 'org-trello-query)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-query--compute-url ()
  (should (equal (format "%s%s" orgtrello-query--trello-url "/uri")            (orgtrello-query--compute-url orgtrello-query--trello-url "/uri")))
  (should (equal (format "%s%s" orgtrello-query--trello-url "/uri/other")      (orgtrello-query--compute-url orgtrello-query--trello-url "/uri/other")))
  (should (equal (format "some-server/uri/some/other")          (orgtrello-query--compute-url "some-server" "/uri/some/other"))))

(ert-deftest test-orgtrello-query--authentication-params ()
  (should
   (equal '((key . :org-trello-consumer-key) (token . :org-trello-access-token))
          (let ((org-trello-consumer-key :org-trello-consumer-key)
                (org-trello-access-token :org-trello-access-token))
            (orgtrello-query--authentication-params)))))

(ert-deftest test-orgtrello-query--http-parse ()
  (should (equal '("some-output with unicode bytes ἀ ἃ ἄ ἅ ἆ ἇ Ἀ Ἁ Ἂ Ἃ Ἄ Ἅ Ἆ Ἇ")
                 (with-mock
                   (mock (buffer-string) => "[\"some-output with unicode bytes ἀ ἃ ἄ ἅ ἆ ἇ Ἀ Ἁ Ἂ Ἃ Ἄ Ἅ Ἆ Ἇ\"]")
                   (orgtrello-query--http-parse))))
  (should (equal '("bytes антикор") ;; i have no idea what this means so please, reader, don't take it personally
                 (with-mock
                   (mock (buffer-string) => "[\"bytes \320\260\320\275\321\202\320\270\320\272\320\276\321\200\"]")
                   (orgtrello-query--http-parse)))))

(ert-deftest test-orgtrello-query--get ()
  ;; not synced, default callbacks, etc... no authentication
  (should (equal
           '(deferred:$
              (request-deferred "http://server/some-uri"
                                :type "GET"
                                :params '((:a 1)
                                          (:b 2))
                                :parser 'orgtrello-query--http-parse)
              (deferred:nextc it orgtrello-query--standard-success-callback)
              (deferred:error it orgtrello-query--standard-error-callback))
           (let ((server "http://server/")
                 (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                              (:method . "GET")
                                                              (:params (:a 1) (:b 2))
                                                              (:sync)))))
             (orgtrello-query--get server query-map))))
  ;; not synced, specific callbacks + authentication
  (should (equal
           '(deferred:$
              (request-deferred "http://server/some-uri"
                                :type "GET"
                                :params '((key . :consumer-key)
                                          (token . :access-token)
                                          (:c 3)
                                          (:d 4))
                                :parser 'orgtrello-query--http-parse)
              (deferred:nextc it :success-cbk)
              (deferred:error it :error-cbk))
           (let ((server "http://server/")
                 (org-trello-consumer-key :consumer-key)
                 (org-trello-access-token :access-token)
                 (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                              (:method . "GET")
                                                              (:params (:c 3) (:d 4))
                                                              (:sync)))))
             (orgtrello-query--get server query-map :success-cbk :error-cbk 'with-auth))))
  ;; sync query, default callbacks
  (should (equal :result-synced-1
                 (with-mock
                   (mock (request "http://server/some-uri"
                                  :sync    t
                                  :type    "GET"
                                  :params  '((:c 3)
                                             (:d 4))
                                  :parser  'orgtrello-query--http-parse
                                  :success 'orgtrello-query--standard-success-callback
                                  :error   'orgtrello-query--standard-error-callback) => :result-synced-1)
                   (let ((server "http://server/")
                         (org-trello-consumer-key :consumer-key)
                         (org-trello-access-token :access-token)
                         (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                                      (:method . "GET")
                                                                      (:params (:c 3) (:d 4))
                                                                      (:sync . 'sync)))))
                     (orgtrello-query--get server query-map)))))
  ;; sync query, specific-callbacks with authentication
  (should (equal :result-synced-2
                 (with-mock
                   (mock (request "http://server/some-uri"
                                  :sync    t
                                  :type    "GET"
                                  :params  '((key . :consumer-key)
                                             (token . :access-token)
                                             (:c 3)
                                             (:d 4))
                                  :parser  'orgtrello-query--http-parse
                                  :success :success-cbk
                                  :error   :error-cbk) => :result-synced-2)
                   (let ((server "http://server/")
                         (org-trello-consumer-key :consumer-key)
                         (org-trello-access-token :access-token)
                         (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                                      (:method . "GET")
                                                                      (:params (:c 3) (:d 4))
                                                                      (:sync . 'sync)))))
                     (orgtrello-query--get server query-map :success-cbk :error-cbk 'with-auth))))))

(ert-deftest test-orgtrello-query--post-or-put ()
  ;; not synced, default callbacks, etc... no authentication
  (should (equal
           '(deferred:$
              (request-deferred "http://server/some-uri"
                                :type "POST"
                                :params '((key)
                                          (token))
                                :headers '(("Content-type" . "application/json"))
                                :data "{\"a\":1,\"b\":2}"
                                :parser 'orgtrello-query--http-parse)
              (deferred:nextc it :success-cbx)
              (deferred:error it :error-cbx))
           (with-mock
             (mock (json-encode '((:a . 1) (:b . 2))) => "{\"a\":1,\"b\":2}")
             (let ((server "http://server/")
                   (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                                (:method . "POST")
                                                                (:params (:a . 1) (:b . 2))
                                                                (:sync)))))
               (orgtrello-query--post-or-put server query-map :success-cbx :error-cbx 'with-auth)))))
  ;; not synced, specific callbacks + authentication
  (should (equal
           '(deferred:$
              (request-deferred "http://server/some-uri"
                                :type "PUT"
                                :params '((key . :consumer-key)
                                          (token . :access-token))
                                :headers '(("Content-type" . "application/json"))
                                :data "{\"c\":3,\"d\":4}"
                                :parser 'orgtrello-query--http-parse)
              (deferred:nextc it :success-cbk)
              (deferred:error it :error-cbk))
           (with-mock
             (mock (json-encode '((:c . 3) (:d . 4))) => "{\"c\":3,\"d\":4}")
             (let ((server "http://server/")
                   (org-trello-consumer-key :consumer-key)
                   (org-trello-access-token :access-token)
                   (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                                (:method . "PUT")
                                                                (:params (:c . 3) (:d . 4))
                                                                (:sync)))))
               (orgtrello-query--post-or-put server query-map :success-cbk :error-cbk 'with-auth)))))
  ;; sync query, default callbacks
  (should (equal :result-post-or-put-synced-no-auth
                 (with-mock
                   (mock (json-encode '((:c . 3) (:d . 4))) => "{\"c\":3,\"d\":4}")
                   (mock (request "http://server/some-uri"
                                  :sync t
                                  :type "POST"
                                  :params nil
                                  :headers  '(("Content-type" . "application/json"))
                                  :data "{\"c\":3,\"d\":4}"
                                  :parser 'orgtrello-query--http-parse
                                  :success 'orgtrello-query--standard-success-callback
                                  :error 'orgtrello-query--standard-error-callback)
                         => :result-post-or-put-synced-no-auth)
                   (let ((server "http://server/")
                         (org-trello-consumer-key :consumer-key)
                         (org-trello-access-token :access-token)
                         (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                                      (:method . "POST")
                                                                      (:params (:c . 3) (:d . 4))
                                                                      (:sync . 'sync)))))
                     (orgtrello-query--post-or-put server query-map)))))
  ;; sync query, specific-callbacks with authentication
  (should (equal :result-post-or-put-synced-with-auth
                 (with-mock
                   (mock (json-encode '((:c . 3) (:d . 4))) => "{\"c\":3,\"d\":4}")
                   (mock (request "http://server/some-uri"
                                  :sync t
                                  :type "PUT"
                                  :params '((key . :consumer-key)
                                            (token . :access-token))
                                  :headers '(("Content-type" . "application/json"))
                                  :data "{\"c\":3,\"d\":4}"
                                  :parser 'orgtrello-query--http-parse
                                  :success :success-cbk
                                  :error :error-cbk) => :result-post-or-put-synced-with-auth)
                   (let ((server "http://server/")
                         (org-trello-consumer-key :consumer-key)
                         (org-trello-access-token :access-token)
                         (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                                      (:method . "PUT")
                                                                      (:params (:c . 3) (:d . 4))
                                                                      (:sync . 'sync)))))
                     (orgtrello-query--post-or-put server query-map :success-cbk :error-cbk 'with-auth))))))

(ert-deftest test-orgtrello-query--delete ()
  ;; not synced, default callbacks, etc... no authentication
  (should (equal
           '(deferred:$
              (request-deferred "http://server/some-uri"
                                :type "DELETE"
                                :params '((key)
                                          (token)))
              (deferred:nextc it :success-cbx)
              (deferred:error it :error-cbx))
           (let ((server "http://server/")
                 (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                              (:method . "DELETE")
                                                              (:params (:a . 1) (:b . 2))
                                                              (:sync)))))
             (orgtrello-query--delete server query-map :success-cbx :error-cbx 'with-auth))))
  ;; not synced, specific callbacks + authentication
  (should (equal
           '(deferred:$
              (request-deferred "http://server/some-uri"
                                :type "DELETE"
                                :params '((key . :consumer-key)
                                          (token . :access-token)))
              (deferred:nextc it :success-cbk)
              (deferred:error it :error-cbk))
           (let ((server "http://server/")
                 (org-trello-consumer-key :consumer-key)
                 (org-trello-access-token :access-token)
                 (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                              (:method . "DELETE")
                                                              (:params (:c . 3) (:d . 4))
                                                              (:sync)))))
             (orgtrello-query--delete server query-map :success-cbk :error-cbk 'with-auth))))
  ;; sync query, default callbacks
  (should (equal :result-delete-synced-no-auth
                 (with-mock
                   (mock (request "http://server/some-uri"
                                  :sync t
                                  :type "DELETE"
                                  :params nil
                                  :success 'orgtrello-query--standard-success-callback
                                  :error 'orgtrello-query--standard-error-callback)
                         => :result-delete-synced-no-auth)
                   (let ((server "http://server/")
                         (org-trello-consumer-key :consumer-key)
                         (org-trello-access-token :access-token)
                         (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                                      (:method . "DELETE")
                                                                      (:params (:c . 3) (:d . 4))
                                                                      (:sync . 'sync)))))
                     (orgtrello-query--delete server query-map)))))
  ;; sync query, specific-callbacks with authentication
  (should (equal :result-delete-synced-with-auth
                 (with-mock
                   (mock (request "http://server/some-uri"
                                  :sync t
                                  :type "DELETE"
                                  :params '((key . :consumer-key) (token . :access-token))
                                  :success :success-cbk
                                  :error :error-cbk) => :result-delete-synced-with-auth)
                   (let ((server "http://server/")
                         (org-trello-consumer-key :consumer-key)
                         (org-trello-access-token :access-token)
                         (query-map (orgtrello-hash-make-properties '((:uri . "some-uri")
                                                                      (:method . "DELETE")
                                                                      (:params (:c . 3) (:d . 4))
                                                                      (:sync . 'sync)))))
                     (orgtrello-query--delete server query-map :success-cbk :error-cbk 'with-auth))))))

(ert-deftest test-orgtrello-query-http ()
  (should (equal '(:server :query-map :success-cbk-fn :error-cbk-fn :auth-p)
                 (with-mock
                   (mock (orgtrello-data-entity-method :query-map) => :entity-method)
                   (mock (orgtrello-query--dispatch-http-query :entity-method)
                         => (lambda (server query-map success-cbk-fn error-cbk-fn auth-p)
                              (list server query-map success-cbk-fn error-cbk-fn auth-p)))
                   (orgtrello-query-http :server :query-map nil :success-cbk-fn :error-cbk-fn :auth-p))))
  (should (eq :res-with-synced-query
              (with-mock
                (mock (orgtrello-data-entity-method :query-map)                                                        => :entity-method)
                (mock (orgtrello-query--dispatch-http-query :entity-method)                                            =>
                      (lambda (server query-map success-cbk-fn error-cbk-fn auth-p)
                        (make-request-response :data :res-with-synced-query)))
                (mock (orgtrello-data-put-entity-sync 'sync :query-map)                                                => :updated-query-map)
                (orgtrello-query-http :server :query-map 'sync :success-cbk-fn :error-cbk-fn :auth-p)))))

(ert-deftest test-orgtrello-query--dispatch-http-query ()
  (should (equal 'orgtrello-query--get         (orgtrello-query--dispatch-http-query "GET")))
  (should (equal 'orgtrello-query--post-or-put (orgtrello-query--dispatch-http-query "POST")))
  (should (equal 'orgtrello-query--post-or-put (orgtrello-query--dispatch-http-query "PUT")))
  (should (equal 'orgtrello-query--delete      (orgtrello-query--dispatch-http-query "DELETE"))))

(ert-deftest test-orgtrello-query-http-trello ()
  (should (equal :result
                 (with-mock
                   (mock (orgtrello-query-http orgtrello-query--trello-url :query-map :sync :success-callback :error-callback 'with-authentication) => :result)
                   (orgtrello-query-http-trello :query-map :sync :success-callback :error-callback)))))

(ert-deftest test-orgtrello-query--standard-error-callback ()
  (should (equal "org-trello - Detailed response: [cl-struct-request-response nil nil nil \"some error thrown\" nil nil nil nil nil nil nil nil nil]"
                 (let ((orgtrello-log-level orgtrello-log-debug))
                   (orgtrello-query--standard-error-callback :response (make-request-response :error-thrown "some error thrown"))))))

(ert-deftest test-orgtrello-query--standard-success-callback ()
  (string= "org-trello - Data: \"w00t\""
           (let ((orgtrello-log-level orgtrello-log-debug))
             (orgtrello-query--standard-success-callback :response (make-request-response :data "w00t")))))

(provide 'org-trello-query-test)
;;; org-trello-query-test.el ends here
