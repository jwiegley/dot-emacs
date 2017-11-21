(require 'org-trello-hash)
(require 'ert)
(require 'el-mock)
(require 'dash)

(ert-deftest test-orgtrello-hash-empty-hash ()
  (should (eq 0
              (hash-table-count (orgtrello-hash-empty-hash)))))

(ert-deftest test-orgtrello-hash-init-map-from ()
  (should (eq 0
              (hash-table-count (orgtrello-hash-init-map-from nil))))

  (should (equal :data (orgtrello-hash-init-map-from :data))))

(ert-deftest test-orgtrello-hash-make-properties ()
  (should (eq 0
              (hash-table-count (orgtrello-hash-make-properties nil))))
  (should (and
           (eq 1
               (hash-table-count (orgtrello-hash-make-properties '((:id . :a)))))
           (eq :a
               (gethash :id
                        (orgtrello-hash-make-properties '((:id . :a)))))
           (eq nil
               (gethash :unknown
                        (orgtrello-hash-make-properties '((:id . :a)))))))
  (should (and
           (eq 2
               (hash-table-count (orgtrello-hash-make-properties '((:id-1 . (:b))
                                                                   (:id-2 :c :d)))))
           (equal '(:b)
                  (gethash :id-1
                           (orgtrello-hash-make-properties '((:id-1 . (:b))
                                                             (:id-2 :c :d)))))
           (equal '(:c :d)
                  (gethash :id-2
                           (orgtrello-hash-make-properties '((:id-1 . (:b))
                                                             (:id-2 :c :d)))))
           (eq nil
               (gethash :unknown
                        (orgtrello-hash-make-properties '((:id-1 . (:b))
                                                          (:id-2 :c :d))))))))

(ert-deftest test-orgtrello-hash-make-transpose-properties ()
  (should (eq 0
              (hash-table-count (orgtrello-hash-make-transpose-properties nil))))
  (should (orgtrello-tests-hash-equal
           (orgtrello-hash-make-properties '(((:b) . :id-1)
                                             ((:c :d) . :id-2)))
           (orgtrello-hash-make-transpose-properties '((:id-1 . (:b))
                                                       (:id-2 :c :d))))))

(ert-deftest test-orgtrello-hash-gethash-data ()
  (should (equal "some-method" (orgtrello-hash-gethash-data :method (orgtrello-hash-make-properties '((:method . "some-method"))))))
  (should (equal nil           (orgtrello-hash-gethash-data :method (orgtrello-hash-make-properties '((:inexistant . "some-method"))))))
  (should (equal nil           (orgtrello-hash-gethash-data :key nil)))
  (should (equal :value        (orgtrello-hash-gethash-data :key (orgtrello-hash-make-properties '((:key . :value))))))
  (should (equal nil           (orgtrello-hash-gethash-data :key (orgtrello-hash-make-properties '((:other-key . :value))))))
  (should (equal nil           (orgtrello-hash-gethash-data :key (orgtrello-hash-make-properties '((:key . nil)))))))

(ert-deftest test-orgtrello-hash-puthash-data ()
  (should (equal nil
                 (orgtrello-hash-puthash-data :key :value nil)))
  (should (eq :value-1 (->> (orgtrello-hash-empty-hash)
                            (orgtrello-hash-puthash-data :key :value-1)
                            (orgtrello-hash-gethash-data :key))))
  (should (eq :value-2 (->> (orgtrello-hash-make-properties '((:1 . :2) (:key . :other-value)))
                            (orgtrello-hash-puthash-data :key :value-2)
                            (orgtrello-hash-gethash-data :key)))))

(ert-deftest test-orgtrello-hash-keys ()
  (should (equal '(:a :b :c)
                 (orgtrello-hash-keys (orgtrello-hash-make-properties '((:a . :1)
                                                                        (:b . :2)
                                                                        (:c . :3))))))
  (should-not (orgtrello-hash-keys (orgtrello-hash-empty-hash))))

(ert-deftest test-orgtrello-hash-values ()
  (should (equal '(:1 :2 :3)
                 (orgtrello-hash-values (orgtrello-hash-make-properties '((:a . :1)
                                                                          (:b . :2)
                                                                          (:c . :3))))))
  (should-not (orgtrello-hash-values (orgtrello-hash-empty-hash))))

(provide 'org-trello-hash-test)
;;; org-trello-hash-test.el ends here
