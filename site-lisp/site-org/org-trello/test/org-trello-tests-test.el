(require 'ert)
(require 'el-mock)
(require 'org-trello-tests)

(ert-deftest test-hash-table-keys ()
  (should (equal '(:c :b :a)
                 (hash-table-keys (orgtrello-hash-make-properties '((:a . :1)
                                                                    (:b . :2)
                                                                    (:c . :3))))))
  (should-not (orgtrello-hash-keys (orgtrello-hash-empty-hash))))

(ert-deftest test-hash-table-values ()
  (should (equal '(:3 :2 :1)
                 (hash-table-values (orgtrello-hash-make-properties '((:a . :1)
                                                                      (:b . :2)
                                                                      (:c . :3)))))))

(ert-deftest test-orgtrello-tests-hash-equal ()
  (should (orgtrello-tests-hash-equal (orgtrello-hash-make-properties `((:name . "some other name") (:keyword "TODO")))
                                      (orgtrello-hash-make-properties `((:name . "some other name") (:keyword "TODO")))))
  (should (orgtrello-tests-hash-equal (orgtrello-hash-make-properties `((:keyword "TODO") (:name . "some other name") (:other "1" "2")))
                                      (orgtrello-hash-make-properties `((:name . "some other name") (:other "1" "2") (:keyword "TODO")))))
  (should (orgtrello-tests-hash-equal (orgtrello-hash-make-properties `((:buffername . " *temp*-321986")
                                                                        (:position . 85)
                                                                        (:level . 2)
                                                                        (:keyword . "TODO")
                                                                        (:name . "cbx")
                                                                        (:id . "456")
                                                                        (:due)
                                                                        (:member-ids . "")
                                                                        (:desc)
                                                                        (:tags)
                                                                        (:unknown-properties)))
                                      (orgtrello-hash-make-properties `((:buffername . " *temp*-321986")
                                                                        (:position . 85)
                                                                        (:level . 2)
                                                                        (:keyword . "TODO")
                                                                        (:name . "cbx")
                                                                        (:id . "456")
                                                                        (:due)
                                                                        (:member-ids . "")
                                                                        (:desc)
                                                                        (:tags)
                                                                        (:unknown-properties)))))
  (should (orgtrello-tests-hash-equal (orgtrello-hash-make-properties `((:buffername . " *temp*-321986")
                                                                        (:position . 85)
                                                                        (:level . 2)
                                                                        (:keyword . "TODO")
                                                                        (:name . "cbx")
                                                                        (:id . "456")
                                                                        (:due)
                                                                        (:member-ids . "")
                                                                        (:desc)
                                                                        (:tags)
                                                                        (:unknown-properties)
                                                                        (:parent . ,(orgtrello-hash-make-properties '((:buffername . " *temp*-321986")
                                                                                                                      (:position . 1)
                                                                                                                      (:level . 1)
                                                                                                                      (:keyword . "TODO")
                                                                                                                      (:name . "card title")
                                                                                                                      (:id . "123")
                                                                                                                      (:due)
                                                                                                                      (:member-ids . "")
                                                                                                                      (:desc . "")
                                                                                                                      (:tags)
                                                                                                                      (:unknown-properties)
                                                                                                                      (:parent))))))
                                      (orgtrello-hash-make-properties `((:buffername . " *temp*-321986")
                                                                        (:position . 85)
                                                                        (:level . 2)
                                                                        (:keyword . "TODO")
                                                                        (:name . "cbx")
                                                                        (:id . "456")
                                                                        (:due)
                                                                        (:member-ids . "")
                                                                        (:desc)
                                                                        (:tags)
                                                                        (:unknown-properties)
                                                                        (:parent . ,(orgtrello-hash-make-properties '((:buffername . " *temp*-321986")
                                                                                                                      (:position . 1)
                                                                                                                      (:level . 1)
                                                                                                                      (:keyword . "TODO")
                                                                                                                      (:name . "card title")
                                                                                                                      (:id . "123")
                                                                                                                      (:due)
                                                                                                                      (:member-ids . "")
                                                                                                                      (:desc . "")
                                                                                                                      (:tags)
                                                                                                                      (:unknown-properties)
                                                                                                                      (:parent))))))))
  (should-not (orgtrello-tests-hash-equal (orgtrello-hash-make-properties `((:buffername . " *temp*-321986")
                                                                            (:position . 85)
                                                                            (:level . 2)
                                                                            (:keyword . "TODO")
                                                                            (:name . "cbx")
                                                                            (:id . "456")
                                                                            (:due)
                                                                            (:member-ids . "")
                                                                            (:desc)
                                                                            (:tags)
                                                                            (:unknown-properties)
                                                                            (:parent . ,(orgtrello-hash-make-properties '((:buffername . " *temp*-321986")
                                                                                                                          (:position . 1)
                                                                                                                          (:level . 1)
                                                                                                                          (:keyword . "DONE")
                                                                                                                          (:name . "card title")
                                                                                                                          (:id . "123")
                                                                                                                          (:due)
                                                                                                                          (:member-ids . "")
                                                                                                                          (:desc . "")
                                                                                                                          (:tags)
                                                                                                                          (:unknown-properties)
                                                                                                                          (:parent))))))
                                          ;; keyword in the nested structure is not the same so should fail
                                          (orgtrello-hash-make-properties `((:buffername . " *temp*-321986")
                                                                            (:position . 85)
                                                                            (:level . 2)
                                                                            (:keyword . "TODO")
                                                                            (:name . "cbx")
                                                                            (:id . "456")
                                                                            (:due)
                                                                            (:member-ids . "")
                                                                            (:desc)
                                                                            (:tags)
                                                                            (:unknown-properties)
                                                                            (:parent . ,(orgtrello-hash-make-properties '((:buffername . " *temp*-321986")
                                                                                                                          (:position . 1)
                                                                                                                          (:level . 1)
                                                                                                                          (:keyword . "TODO")
                                                                                                                          (:name . "card title")
                                                                                                                          (:id . "123")
                                                                                                                          (:due)
                                                                                                                          (:member-ids . "")
                                                                                                                          (:desc . "")
                                                                                                                          (:tags)
                                                                                                                          (:unknown-properties)
                                                                                                                          (:parent))))))))
  (should-not (orgtrello-tests-hash-equal (orgtrello-hash-make-properties `((:name . "some other name") (:keyword "TODO")))
                                          (orgtrello-hash-make-properties `((:name . "some other name") (:keyword "DONE"))))))

(ert-deftest test-org-trello-mode-test ()
  (should (-every? (-partial #'eq t)
                   (with-mock
                     (mock (call-interactively 'org-trello-mode) => :starting-org-trello)
                     (org-trello-mode-test)
                     (list
                      (equal nil org-trello-mode-on-hook)
                      (equal nil org-trello-mode-off-hook)
                      (equal 'please-do-use-position-in-checksum-computation orgtrello-setup-use-position-in-checksum-computation)
                      (equal orgtrello-log-no-log orgtrello-log-level)
                      (equal t org-trello--mode-activated-p))))))

(ert-deftest test-orgtrello-tests-with-temp-buffer ()
  (should (string="line 1
line 2
line 3"
                  (orgtrello-tests-with-temp-buffer
                   "line 1
line 2
line 3"
                   (buffer-substring-no-properties (point-min) (point-max)))))

  (should (string= "line 3"
                   (orgtrello-tests-with-temp-buffer
                    "some content
line 2
line 3"
                    (buffer-substring-no-properties (point-at-bol) (point-at-eol))
                    0)))
  (should (string= "line 2"
                   (orgtrello-tests-with-temp-buffer
                    "line 1
line 2
line 3"
                    (buffer-substring-no-properties (point-at-bol) (point-at-eol)))))
  (should (string= "line 1"
                   (orgtrello-tests-with-temp-buffer
                    "line 1
line 2
line 3"
                    (buffer-substring-no-properties (point-at-bol) (point-at-eol))
                    -2))))

(ert-deftest test-orgtrello-tests-with-temp-buffer-and-return-buffer-content ()
  (should (string= "1
2
3
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "line 1
line 2
line 3
"
                    (replace-regexp "line " "" nil (point-min) (point-max))))))

(ert-deftest test-orgtrello-tests-with-temp-buffer-and-return-content-with-props ()
  (should (equal #("1
2
3
" 0 2 (line-prefix nil wrap-prefix nil)
2 4 (line-prefix nil wrap-prefix nil)
4 6 (line-prefix nil wrap-prefix nil))
                 (orgtrello-tests-with-temp-buffer-and-return-content-with-props
                  "line 1
line 2
line 3
"
                  (replace-regexp "line " "" nil (point-min) (point-max))))))


(ert-deftest test-orgtrello-tests-prepare-buffer ()
  (should (string= "* card
  description
  - [ ] cbx
    - [ ] item
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
description
- [ ] cbx
  - [ ] item
"
                    (orgtrello-tests-prepare-buffer)))))

(ert-deftest test-orgtrello-tests-with-temp-buffer-and-return-indented-content ()
  (should (string= "* card
  description
  - [X] cbx
    - [X] item
"
                   (orgtrello-tests-with-temp-buffer-and-return-indented-content
                    "* card
description
- [ ] cbx
  - [ ] item
"
                    (replace-regexp "\\[ \\]" "[X]" nil (point-min) (point-max))))))

(ert-deftest test-orgtrello-tests-with-org-buffer ()
  (should (eq 'headline
              (orgtrello-tests-with-org-buffer
               "* heading
"
               (progn
                 (goto-char (point-min))
                 (car (org-element-at-point)))))))

(provide 'org-trello-tests)
;;; org-trello-tests-test.el ends here
