(ert-deftest prodigy-service-port-test ()
  (should (= (prodigy-service-port (ht (:port 1234))) 1234))
  (should (= (prodigy-service-port (ht (:args '("-p" "1234")))) 1234))
  (should (= (prodigy-service-port (ht (:args '("-p" "12345")))) 12345))
  (should-not (prodigy-service-port (ht (:args '("-p" "123456")))))
  (should-not (prodigy-service-port (ht-create))))

(ert-deftest prodigy-define-service-test/no-name ()
  (should-error
   (prodigy-define-service
    :command "command"
    :cwd "cwd")))

(ert-deftest prodigy-define-service-test/no-cwd ()
  (should-error
   (prodigy-define-service
    :name "name"
    :command "command")))

(ert-deftest prodigy-define-service-test/no-command ()
  (should-error
   (prodigy-define-service
    :name "name"
    :cwd "cwd")))
