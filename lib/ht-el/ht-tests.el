(require 'ert)
(require 'ht)

(ert-deftest ht-test-ht ()
  (let ((test-table (ht (1 2) ("foo" (1+ 2)))))
    (should (and (member 1 (ht-keys test-table))
                 (member "foo" (ht-keys test-table))
                 (member 2 (ht-values test-table))
                 (member 3 (ht-values test-table))))))

(ert-deftest ht-test-create ()
  (should (hash-table-p (ht-create))))

(ert-deftest ht-test-set-then-get ()
  (let ((test-table (ht-create)))
    (ht-set test-table "foo" "bar")
    (should (equal (ht-get test-table "foo") "bar"))))

(ert-deftest ht-test-get-default ()
  (let ((test-table (ht-create)))
    (should (equal (ht-get test-table "foo" "default") "default"))))

(ert-deftest ht-test-update ()
  (let ((test-table (ht ("foo" 1))))
    (ht-update test-table (ht ("bar" 2)))
    (should
     (equal
      (list "bar" "foo")
      (sort (ht-keys test-table) 'string<)))))

(ert-deftest ht-test-merge ()
  (let ((table1 (ht ("foo" 1)))
        (table2 (ht ("bar" 2))))
    (should
     (equal
      (list "bar" "foo")
      (sort (ht-keys (ht-merge table1 table2)) 'string<)))))

(ert-deftest ht-test-create-non-default-test ()
  (let ((test-table (ht-create 'eq)))
    (should (equal (hash-table-test test-table) 'eq))))

(ert-deftest ht-test-remove ()
  (let ((test-table (ht-create)))
    (ht-set test-table "foo" "bar")
    (ht-remove test-table "foo")
    (should (equal (ht-get test-table "foo") nil))))

(ert-deftest ht-test-clear ()
  (let ((test-table (ht-create)))
    (ht-set test-table "foo" "bar")
    (ht-set test-table "biz" "baz")
    (ht-clear test-table)
    (should (equal (ht-items test-table) nil))))

(ert-deftest ht-test-keys ()
  (let ((test-table (ht-create)))
    (ht-set test-table "foo" "bar")
    (should (equal (ht-keys test-table) (list "foo")))))

(ert-deftest ht-test-values ()
  (let ((test-table (ht-create)))
    (ht-set test-table "foo" "bar")
    (should (equal (ht-values test-table) (list "bar")))))

(ert-deftest ht-test-items ()
  (let ((test-table (ht-create)))
    (ht-set test-table "key1" "value1")
    (should (equal (ht-items test-table) '(("key1" "value1"))))))

(ert-deftest ht-test-map ()
  (let ((total 0))
    (ht-map
     (lambda (key value) (setq total (+ total value)))
     (ht ("foo" 1) ("bar" 2)))
    (should
     (equal total 3))))

(ert-deftest ht-test-map-returns-list ()
  (should
   (equal
    (sort
     (ht-map
      (lambda (key value) (+ 1 value))
      (ht ("foo" 1) ("bar" 2)))
     '<)
    (list 2 3))))

(ert-deftest ht-test-amap ()
  (let ((total 0))
    (ht-amap
     (setq total (+ total value))
     (ht ("foo" 1) ("bar" 2)))
    (should
     (equal total 3))))

(ert-deftest ht-test-each ()
  (let ((total 0))
    (ht-each
     (lambda (key value) (setq total (+ total value)))
     (ht ("foo" 1) ("bar" 2)))
    (should
     (equal total 3))))

(ert-deftest ht-test-aeach ()
  (let ((total 0))
    (ht-aeach
     (setq total (+ total value))
     (ht ("foo" 1) ("bar" 2)))
    (should
     (equal total 3))))

(ert-deftest ht-test-aeach-nil ()
  "ht-aeach should return nil"
  (let ((total 0))
    (should
     (equal
      (ht-aeach
       (setq total (+ total value))
       (ht ("foo" 1) ("bar" 2)))
      nil))))

(ert-deftest ht-test-from-alist ()
  (let* ((alist '(("key1" . "value1")))
         (test-table (ht-from-alist alist)))
    (should (equal (ht-items test-table) '(("key1" "value1"))))))

(ert-deftest ht-test-from-alist-masked-values ()
  (let* ((alist '(("key1" . "value1") ("key1" . "value2")))
         (test-table (ht-from-alist alist)))
    (should (equal (ht-items test-table) '(("key1" "value1"))))))

(ert-deftest ht-test-from-plist ()
  (let* ((plist '("key1" "value1"))
         (test-table (ht-from-plist plist)))
    (should (equal (ht-items test-table) '(("key1" "value1"))))))

(ert-deftest ht-test-to-alist ()
  (let* ((alist '(("key1" . "value1") ("key2" . "value2")))
         (test-table (ht-from-alist alist)))
    (should (or (equal (ht-to-alist test-table) alist)
                (equal (ht-to-alist test-table) (reverse alist))))))

(ert-deftest ht-test-to-plist ()
  (let* ((test-table (ht-create)))
    (ht-set test-table "foo" "bar")
    (should (equal (ht-to-plist test-table) '("foo" "bar")))))

(ert-deftest ht-test-p ()
  "Ensure `ht-p' only returns t for hash-tables."
  (should (ht-p (ht)))
  (should-not (ht-p nil)))

(ert-deftest ht-test-contains-p ()
  (should (ht-contains-p (ht ("key" nil)) "key"))
  (should-not (ht-contains-p (ht) "key")))

(defun ht-run-tests ()
  (interactive)
  (ert-run-tests-interactively "ht-test-"))
