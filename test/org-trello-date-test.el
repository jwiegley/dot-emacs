(require 'org-trello-date)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-date-convert-org-date-to-trello-date ()
  (should (string= "2013-07-29T13:00:00.000Z"
                   (orgtrello-date-convert-org-date-to-trello-date "2013-07-29 mon. 14:00")))
  (should (string= "2013-07-29T13:00:00.000Z"
                   (orgtrello-date-convert-org-date-to-trello-date "2013-07-29 14:00")))
  (should-not (orgtrello-date-convert-org-date-to-trello-date nil)))

(ert-deftest test-orgtrello-date--prepare-iso-8601 ()
  (should (string= "2015-08-30 14:00:00 GMT"
                   (orgtrello-date--prepare-iso-8601 "2015-08-30T14:00:00.000Z")))
  (should (string= "2013-07-29 12:00:00 GMT"
                   (orgtrello-date--prepare-iso-8601 "2013-07-29T12:00:00.000Z")))
  (should (string= "2013-07-29 12:00:00 GMT"
                   (orgtrello-date--prepare-iso-8601 "2013-07-29T12:00:00.000Z")))
  (should (string= "2015-09-22 23:45:00 GMT"
                   (orgtrello-date--prepare-iso-8601 "2015-09-22T23:45:00.000Z")))

  ;; does not know how to parse (not expected)
  (should-not (orgtrello-date--prepare-iso-8601 "2015-08-30 14:00:00")))

(ert-deftest test-orgtrello-date-convert-trello-date-to-org-date ()
  (should (string= "2015-08-30 Sun 15:00"
                   (orgtrello-date-convert-trello-date-to-org-date "2015-08-30T14:00:00.000Z")))
  (should (string= "2013-07-29 Mon 13:00"
                   (orgtrello-date-convert-trello-date-to-org-date "2013-07-29T12:00:00.000Z")))
  (should (string= "2015-09-23 Wed 00:45"
                   (orgtrello-date-convert-trello-date-to-org-date "2015-09-22T23:45:00.000Z")))
  (should-not (orgtrello-date-convert-trello-date-to-org-date nil)))

(provide 'org-trello-date-test)
;;; org-trello-date-test.el ends here
