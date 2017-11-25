(require 'org-trello-action)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-action-reload-setup ()
  (should (equal '(("foo" . "10") ("bar" . "20"))
                 (orgtrello-tests-with-temp-buffer
                  ":PROPERTIES:
#+PROPERTY: foo 10
#+PROPERTY: bar 20
:END

* heading
"
                  (let ((org-file-properties))
                    (orgtrello-action-reload-setup)
                    org-file-properties)))))

(ert-deftest test-orgtrello-action--execute-controls ()
  (should (equal '(:ok) (orgtrello-action--execute-controls '((lambda (e) :ok)))))
  (should (equal '(:ok "ko") (orgtrello-action--execute-controls '((lambda (e) :ok)
                                                                   (lambda (e) "ko")))))
  (should (equal '(:ok) (orgtrello-action--execute-controls '((lambda (a) :ok)) 'args)))
  (should (equal '(:ok "ko") (orgtrello-action--execute-controls '((lambda (a) :ok)
                                                                   (lambda (a) "ko")) 'arg0))))

(ert-deftest test-orgtrello-action--filter-error-messages ()
  (should (equal '("error0" "error1") (orgtrello-action--filter-error-messages '("error0" :ok "error1"))))
  (should (equal nil                  (orgtrello-action--filter-error-messages '(:ok :ok :ok)))))

(ert-deftest test-orgtrello-action--compute-error-message ()
  (should (equal "- message 1\n- message 2\n" (orgtrello-action--compute-error-message '("message 1" "message 2")))))

(ert-deftest test-orgtrello-action-controls-or-actions-then-do ()
  ;; with no control the action function is direcly executed
  (should (equal "some-result"
                 (orgtrello-action-controls-or-actions-then-do nil (lambda () "some-result"))))
  ;; with all controls ok, the action function is executed
  (should (equal "some-result"
                 (with-mock
                   (mock (control0 nil) => :ok)
                   (mock (control1 nil) => :ok)
                   (orgtrello-action-controls-or-actions-then-do '(control0 control1) (lambda () "some-result")))))

  ;; with all controls ok and the no logs flag, the action function is executed
  (should (equal "some-result"
                 (with-mock
                   (mock (control0 nil) => :ok)
                   (mock (control1 nil) => :ok)
                   (orgtrello-action-controls-or-actions-then-do '(control0 control1) (lambda () "some-result") 'no-logs))))
  ;; ;; with a problem in controls, the action function is not executed and the logs are returned
  (should (equal "org-trello - List of errors:\n - some error message from control 1\n- some other error message from control 2\n"
                 (with-mock
                   (mock (control0 nil)            => :ok)
                   (mock (control1-that-fails nil) => "some error message from control 1")
                   (mock (control2-that-fails nil) => "some other error message from control 2")
                   (orgtrello-action-controls-or-actions-then-do '(control0 control1-that-fails control2-that-fails) 'some-uncalled-function-because-control-fail))))
  ;; ;; with a problem in controls, the action function is not executed and the logs are not returned
  (should (equal nil
                 (with-mock
                   (mock (control0 nil)            => :ok)
                   (mock (control1-that-fails nil) => "some error message from control 1")
                   (mock (control2-that-fails nil) => "some other error message from control 2")
                   (orgtrello-action-controls-or-actions-then-do '(control0 control1-that-fails control2-that-fails) 'some-uncalled-function-because-control-fail 'no-logs)))))

(ert-deftest test-orgtrello-action-functional-controls-then-do ()
  ;; technical tests
  ;; with no controls, the action is executed
  (should (equal "some-result"
                 (orgtrello-action-functional-controls-then-do nil 'entity-not-really-used (lambda (entity-not-used args-not-used) "some-result") 'arg-not-really-used)))
  (should (equal "some-result"
                 ;; with controls ok, the action function is executed
                 (with-mock
                   (mock (control0 'entity-not-really-used) => :ok)
                   (mock (control1 'entity-not-really-used) => :ok)
                   (orgtrello-action-functional-controls-then-do '(control0 control1) 'entity-not-really-used (lambda (entity-not-used args-not-used) "some-result") 'arg-not-really-used))))
  ;; with some controls ko, the action function is not executed and the logs are returned
  (should (equal "org-trello - List of errors:\n - control1 failed!\n- control2 failed!\n"
                 (with-mock
                   (mock (control0-that-fails 'entity-not-really-used) => "control1 failed!")
                   (mock (control1            'entity-not-really-used) => :ok)
                   (mock (control2-that-fails 'entity-not-really-used) => "control2 failed!")
                   (orgtrello-action-functional-controls-then-do '(control0-that-fails control1 control2-that-fails)
                                                                 'entity-not-really-used
                                                                 (lambda (entity-not-used args-not-used) "some-result") 'arg-not-really-used))))
  ;; real functional use cases
  (should (equal "org-trello - List of errors:
 - Wrong level. Do not deal with entity other than card/checklist/item!
"
                 (orgtrello-action-functional-controls-then-do
                  '(orgtrello-controller--right-level-p)
                  (orgtrello-data-make-hierarchy (orgtrello-data-make-hash-org :users 4 :kwd :name nil :due :position :buffer-name :desc :tags :unknown))
                  (lambda (entity s) (format "%S %s" entity s))
                  "- hello")))

  (should (equal "#s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8 data (:current #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8 data (:buffername :buffer-name :position :position :level 3 :keyword :kwd :name :name :id nil :due :due :member-ids :users :desc :desc :tags :tags :unknown-properties :unknown)) :parent nil :grandparent nil)) - hello"
                 (orgtrello-action-functional-controls-then-do
                  '(orgtrello-controller--right-level-p)
                  (orgtrello-data-make-hierarchy (orgtrello-data-make-hash-org :users 3 :kwd :name nil :due :position :buffer-name :desc :tags :unknown))
                  (lambda (entity s) (format "%S %s" entity s))
                  "- hello")))

  (should (equal "org-trello - List of errors:
 - Cannot synchronize the card - missing mandatory name. Skip it...
"
                 (orgtrello-action-functional-controls-then-do
                  '(orgtrello-controller--mandatory-name-ok-p)
                  (orgtrello-data-make-hierarchy (orgtrello-data-make-hash-org :users 1 :kwd nil :level :due :position :buffer-name :desc :tags :unknown))
                  (lambda (entity s) (format "%S %s" entity s))
                  "- hello")))

  (should (equal "#s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8 data (:current #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8 data (:buffername :buffer-name :position :position :level 3 :keyword :kwd :name \"name\" :id :level :due :due :member-ids :users :desc :desc :tags :tags :unknown-properties :unknown)) :parent nil :grandparent nil)) - hello"
                 (orgtrello-action-functional-controls-then-do
                  '(orgtrello-controller--right-level-p)
                  (orgtrello-data-make-hierarchy (orgtrello-data-make-hash-org :users 3 :kwd "name" :level :due :position :buffer-name :desc :tags :unknown))
                  (lambda (entity s) (format "%S %s" entity s))
                  "- hello")))
  (should (equal "org-trello - List of errors:
 - Entity must be synchronized with trello first!
"
                 (orgtrello-action-functional-controls-then-do
                  '(orgtrello-controller--right-level-p orgtrello-controller--already-synced-p)
                  (orgtrello-data-make-hierarchy (orgtrello-data-make-hash-org :users 1 :kwd :name nil :due :position :buffer-name :desc :tags :unknown))
                  (lambda (entity s) (format "%S %s" entity s))
                  "- hello")))
  (should (equal "#s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8 data (:current #s(hash-table size 65 test equal rehash-size 1.5 rehash-threshold 0.8 data (:buffername :buffer-name :position :position :level 1 :keyword :kwd :name :name :id \"some-id\" :due :due :member-ids :users :desc :desc :tags :tags :unknown-properties :unknown)) :parent nil :grandparent nil)) - hello"

                 (orgtrello-action-functional-controls-then-do
                  '(orgtrello-controller--right-level-p orgtrello-controller--already-synced-p)
                  (orgtrello-data-make-hierarchy (orgtrello-data-make-hash-org :users 1 :kwd :name "some-id" :due :position :buffer-name :desc :tags :unknown))
                  (lambda (entity s) (format "%S %s" entity s))
                  "- hello"))))

(ert-deftest test-orgtrello-action-msg-controls-or-actions-then-do ()
  ;; the execution goes fine and we return the result from the wrapped call to 'orgtrello-action-controls-or-actions-then-do
  (should (equal :some-result
                 (with-mock
                   (mock (orgtrello-action-controls-or-actions-then-do :control-or-action-fns :fn-to-execute nil) => :some-result)
                   (orgtrello-action-msg-controls-or-actions-then-do "some-msg" :control-or-action-fns :fn-to-execute))))
  ;; log nothing, execution goes fine, we save the buffer, reload the setup and return the result from the wrapped call to 'orgtrello-action-controls-or-actions-then-do
  (should (equal :some-result
                 (with-mock
                   (mock (orgtrello-action-controls-or-actions-then-do :control-or-action-fns :fn-to-execute 'no-log) => :some-result)
                   (orgtrello-action-msg-controls-or-actions-then-do "some-msg" :control-or-action-fns :fn-to-execute 'no-log)))))

(ert-deftest test-orgtrello-action--too-deep-level ()
  (should (string= "Your arborescence depth is too deep. We only support up to depth 3.
Level 1 - card\nLevel 2 - checklist\nLevel 3 - items"
                   (orgtrello-action--too-deep-level nil))))

(provide 'org-trello-action-test)
;;; org-trello-action-test.el ends here
