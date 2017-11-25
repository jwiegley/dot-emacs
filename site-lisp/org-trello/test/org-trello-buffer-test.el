(require 'org-trello-buffer)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-buffer-global-properties-region ()
  (should (equal '(1 23)
                 (orgtrello-tests-with-temp-buffer
                  ":PROPERTIES:
1
2
:END:
"
                  (orgtrello-buffer-global-properties-region))))
  (should-not (orgtrello-tests-with-temp-buffer
               "something before
:PROPERTIES:
:END:
"
               (orgtrello-buffer-global-properties-region))))

(ert-deftest test-orgtrello-buffer-end-of-line ()
  (should (eq :moved
              (with-mock
                (mock (orgtrello-buffer-end-of-line-point) => :end-of-line)
                (mock (goto-char :end-of-line) => :moved)
                (orgtrello-buffer-end-of-line)))))

(ert-deftest test-orgtrello-buffer-org-map-entries ()
  (should (equal '(1 1)
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] item
* another card
"
                  (orgtrello-buffer-org-map-entries (-compose 'orgtrello-data-entity-level 'orgtrello-buffer-entity-metadata))))))

(ert-deftest test-orgtrello-buffer-compute-generic-checksum ()
  (should (eq :result-checksum
              (with-mock
                (mock (orgtrello-buffer--compute-string-for-checksum :region) => :string-for-checksum)
                (mock (orgtrello-buffer-checksum :string-for-checksum) => :result-checksum)
                (orgtrello-buffer-compute-generic-checksum (lambda () :region))))))

(ert-deftest test-orgtrello-buffer-get-overlay-at-pos ()
  (should (eq :overlay1
              (with-mock
                (mock (point-at-bol) => :point-at-bol)
                (mock (point-at-eol) => :point-at-eol)
                (mock (overlays-in :point-at-bol :point-at-eol) => '(:overlay1))
                (mock (overlay-get :overlay1 'invisible) => 'org-trello-cbx-property)
                (orgtrello-buffer-get-overlay-at-pos))))
  (should-not (with-mock
                (mock (point-at-bol) => :point-at-bol)
                (mock (point-at-eol) => :point-at-eol)
                (mock (overlays-in :point-at-bol :point-at-eol) => '(:overlay1))
                (mock (overlay-get :overlay1 'invisible) => 'something-else)
                (orgtrello-buffer-get-overlay-at-pos))))

(ert-deftest test-orgtrello-buffer-org-decorator ()
  (should (eq :done
              (with-mock
                (mock (orgtrello-buffer-indent-card-descriptions) => :indent-card-desc-done)
                (mock (orgtrello-buffer-indent-card-data) => :indent-card-data-done)
                (mock (orgtrello-entity-org-checkbox-p) => nil)
                (orgtrello-buffer-org-decorator (lambda () :done)))))
  (should (eq :done
              (with-mock
                (mock (orgtrello-buffer-indent-card-descriptions) => :indent-card-desc-done)
                (mock (orgtrello-buffer-indent-card-data) => :indent-card-data-done)
                (mock (orgtrello-entity-org-checkbox-p) => t)
                (mock (org-end-of-line) => :end-of-line-done)
                (orgtrello-buffer-org-decorator (lambda () :done))))))

(ert-deftest test-orgtrello-buffer-safe-entry-full-metadata ()
  (should (eq :full-meta
              (with-mock
                (mock (orgtrello-buffer-entry-get-full-metadata) => :full-meta)
                (orgtrello-buffer-safe-entry-full-metadata))))
  ;; not on an heading so throw error which is caught and then nil is returned
  (should-not
   (orgtrello-tests-with-temp-buffer
    "
* card"
    (orgtrello-buffer-safe-entry-full-metadata))))

(ert-deftest test-orgtrello-buffer--parent-metadata ()
  ;; on item, got back to checklist
  (should (orgtrello-data-entity-checklist-p
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checklist
    - [ ] item
"
            (orgtrello-buffer--parent-metadata))))
  ;; on checklist, got back to card
  (should (orgtrello-data-entity-card-p
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checklist
    - [ ] item
"
            (orgtrello-buffer--parent-metadata)
            -2)))
  ;; already on top, stay as is
  (should (orgtrello-data-entity-card-p
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checklist
    - [ ] item
"
            (orgtrello-buffer--parent-metadata)
            -3))))

(ert-deftest test-orgtrello-buffer--grandparent-metadata ()
  ;; on item, got back to card
  (should (orgtrello-data-entity-card-p
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checklist
    - [ ] item
"
            (orgtrello-buffer--grandparent-metadata))))

  ;; on checklist, got back to card
  (should (orgtrello-data-entity-card-p
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checklist
    - [ ] item
"
            (orgtrello-buffer--grandparent-metadata)
            -2)))
  ;; already on top, stay as is
  (should (orgtrello-data-entity-card-p
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checklist
    - [ ] item
"
            (orgtrello-buffer--grandparent-metadata)
            -3))))

(ert-deftest test-orgtrello-buffer-org-up-parent ()
  ;; on item, got back to checklist
  (should (string= "  - [ ] checklist"
                   (orgtrello-tests-with-temp-buffer
                    "* card
  - [ ] checklist
    - [ ] item
"
                    (progn
                      (orgtrello-buffer-org-up-parent)
                      (buffer-substring-no-properties (point-at-bol) (point-at-eol))))))
  ;; on checklist, got back to card
  (should (string= "* card"
                   (orgtrello-tests-with-temp-buffer
                    "* card
  - [ ] checklist
    - [ ] item
"
                    (progn
                      (orgtrello-buffer-org-up-parent)
                      (buffer-substring-no-properties (point-at-bol) (point-at-eol)))
                    -2)))
  ;; already on top, stay as is
  (should (string= "* card"
                   (orgtrello-tests-with-temp-buffer
                    "* card
  - [ ] checklist
    - [ ] item
"
                    (progn
                      (orgtrello-buffer-org-up-parent)
                      (buffer-substring-no-properties (point-at-bol) (point-at-eol)))
                    -3))))

(ert-deftest test-orgtrello-buffer-install-overlays () ;; not a real test, merely a check nothing breaks...
  (should (string= "* card
  - [ ] checklist :PROPERTIES: {\"id\": \"123\"}
    - [ ] item  :PROPERTIES: {\"id\": \"456\"}
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
  - [ ] checklist :PROPERTIES: {\"id\": \"123\"}
    - [ ] item  :PROPERTIES: {\"id\": \"456\"}
"
                    (orgtrello-buffer-install-overlays)))))

(ert-deftest test-orgtrello-buffer-org-return ()
  (should (eq :result
              (with-mock
                (mock (orgtrello-buffer-org-decorator 'org-return) => :result)
                (orgtrello-buffer-org-return)))))

(ert-deftest test-orgtrello-buffer-org-ctrl-c-ret ()
  (should (eq :result
              (with-mock
                (mock (orgtrello-buffer-org-decorator 'org-ctrl-c-ret) => :result)
                (orgtrello-buffer-org-ctrl-c-ret)))))

(ert-deftest test-orgtrello-buffer-card-entry-get ()
  (should (string= "123"
                   (orgtrello-tests-with-temp-buffer
                    "* card
:PROPERTIES:
:orgtrello-id: 123
:END:"
                    (orgtrello-buffer-card-entry-get (point) "orgtrello-id"))))
  (should-not
   (orgtrello-tests-with-temp-buffer
    "* card
:PROPERTIES:
:END:"
    (orgtrello-buffer-card-entry-get (point) "orgtrello-id"))))

(ert-deftest test-orgtrello-buffer-org-entity-metadata ()
  (should (equal '(1 1 "TODO" nil "card title" nil)
                 (orgtrello-tests-with-temp-buffer
                  "* TODO card title
:PROPERTIES:
:orgtrello-id: 123
:orgtrello-checksum: checksum
:unknown: something
:END
  description here
"
                  (orgtrello-buffer-org-entity-metadata)))))

(ert-deftest test-orgtrello-buffer-compute-overlay-size ()
  (should (eq 10
              (with-mock
                (mock (orgtrello-buffer-get-overlay-at-pos) => :o)
                (mock (overlay-end :o) => 15)
                (mock (overlay-start :o) => 5)
                (orgtrello-buffer-compute-overlay-size))))
  (should-not (with-mock
                (mock (orgtrello-buffer-get-overlay-at-pos) => nil)
                (orgtrello-buffer-compute-overlay-size))))

(ert-deftest test-orgtrello-buffer-end-of-line-point ()
  (should (eq 7
              (orgtrello-tests-with-temp-buffer
               "* card\n"
               (orgtrello-buffer-end-of-line-point))))
  (should (eq 26
              (orgtrello-tests-with-temp-buffer
               "* card
  - [ ] checklist \n"
               (orgtrello-buffer-end-of-line-point))))
  (should (eq 10
              (with-mock
                (mock (save-excursion * *) => 15)
                (mock (orgtrello-entity-org-checkbox-p) => t)
                (mock (orgtrello-buffer-compute-overlay-size) => 4)
                (orgtrello-buffer-end-of-line-point)))))

(ert-deftest test-orgtrello-buffer-org-map-entities-without-params ()
  (should (equal '(("local-card-checksum-1" "local-checklist-checksum-1" "local-item-checksum-1")
                   nil
                   ("local-card-checksum-2")
                   ("local-card-checksum-3"))
                 (orgtrello-tests-with-temp-buffer
                  "* card
:PROPERTIES:
:orgtrello-id: card-id-1
:orgtrello-local-checksum: local-card-checksum-1
:END:
  - [ ] checklist :PROPERTIES: {\"orgtrello-id\": \"checklist-id-1\",\"orgtrello-local-checksum\":\"local-checklist-checksum-1\"}
    - [ ] item :PROPERTIES: {\"orgtrello-id\": \"item-id-1\",\"orgtrello-local-checksum\":\"local-item-checksum-1\"}
** COMMENT
:PROPERTIES:
:orgtrello-id: comment-id-1
:orgtrello-local-checksum: local-comment-checksum-1
:END:
this comment will be ignored
* card 2
:PROPERTIES:
:orgtrello-id: card-id-2
:orgtrello-local-checksum: local-card-checksum-2
:END:
* card 3
:PROPERTIES:
:orgtrello-id: card-id-3
:orgtrello-local-checksum: local-card-checksum-3
:END:
"
                  (orgtrello-buffer-org-map-entities-without-params 'orgtrello-buffer-get-local-checksum)))))

(ert-deftest test-orgtrello-buffer-org-get-property ()
  (should (eq :id-to-find (orgtrello-buffer-org-get-property :id '((:id . :id-to-find))))))

(ert-deftest test-orgtrello-buffer-archive-cards ()
  (should (equal '(:archive-done nil :archive-done)
                 (orgtrello-tests-with-temp-buffer
                  "* card to archive
:PROPERTIES:
:orgtrello-id: card-id
:END:
* not to archive
:PROPERTIES:
:orgtrello-id: yet-another-card-id
:END:
* another card to archive
:PROPERTIES:
:orgtrello-id: other-card-id
:END:
"
                  (with-mock
                    (mock (org-archive-subtree) => :archive-done)
                    (orgtrello-buffer-archive-cards (list (orgtrello-hash-make-properties '((:id . "card-id")))
                                                          (orgtrello-hash-make-properties '((:id . "other-card-id"))))))))))

(ert-deftest test-orgtrello-buffer-set-usernames-assigned-property ()
  (should (string= "* card
  :PROPERTIES:
  :orgtrello-users: user1,user2
  :END:
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
"
                    (orgtrello-buffer-set-usernames-assigned-property "user1,user2")))))

(ert-deftest test-orgtrello-buffer-get-usernames-assigned-property ()
  (should (string= "user1,user2,user3"
                   (orgtrello-tests-with-temp-buffer
                    "* card
:PROPERTIES:
:orgtrello-users: user1,user2,user3
:END:"
                    (orgtrello-buffer-get-usernames-assigned-property)))))

(ert-deftest test-orgtrello-buffer-remove-overlays ()
  (should (eq :result-remove-overlays
              (with-mock
                (mock (remove-overlays :point-min
                                       :point-max
                                       'invisible
                                       'org-trello-cbx-property) => :result-remove-overlays)
                (orgtrello-buffer-remove-overlays :point-min :point-max))))
  (should (eq :result-remove-overlays
              (with-mock
                (mock (point-min) => :point-min)
                (mock (point-max) => :point-max)
                (mock (remove-overlays :point-min
                                       :point-max
                                       'invisible
                                       'org-trello-cbx-property) => :result-remove-overlays)
                (orgtrello-buffer-remove-overlays)))))

(ert-deftest test-orgtrello-buffer--set-marker ()
  (should (string=
           "* new card
  :PROPERTIES:
  :orgtrello-id: new-id
  :END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* new card
"
            (orgtrello-buffer--set-marker "new-id")))))

(ert-deftest test-orgtrello-buffer-set-marker-if-not-present ()
  (should (string=
           "* card
:PROPERTIES:
:orgtrello-id: set-the-marker-to-notify-id-not-yet-set
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:END:
"
            (orgtrello-buffer-set-marker-if-not-present
             (orgtrello-hash-make-properties '((:id . "new-id")))
             "set-the-marker-to-notify-id-not-yet-set"))))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
:PROPERTIES:
:orgtrello-id: marker-already-set-so-nothing-done
:END:
"
               (orgtrello-buffer-set-marker-if-not-present
                (orgtrello-hash-make-properties '((:id . "marker-already-set-so-nothing-done")))
                "marker-already-set-so-nothing-done"))))

(ert-deftest test-orgtrello-buffer-build-org-entities ()
  ;; full buffer
  (should (-every? (-partial #'eq t)
                   (orgtrello-tests-with-temp-buffer
                    "* TODO card title
:PROPERTIES:
:orgtrello-id: 123
:orgtrello-checksum: check
:END:

  - [ ] cbx :PROPERTIES: {\"orgtrello-id\":\"456\"}
    - [X] cbx itm :PROPERTIES: {\"orgtrello-id\":\"789\"}
"
    (-let* ((buf (buffer-name (current-buffer)))
            ((entities adjacencies)
             (orgtrello-buffer-build-org-entities buf))
            (entity-card (orgtrello-hash-make-properties `((:buffername . ,buf)
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
                                                           (:parent))))
            (entity-cbx (orgtrello-hash-make-properties `((:buffername . ,buf)
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
                                                          (:parent . ,entity-card))))
            (entity-cbx-item (orgtrello-hash-make-properties `((:buffername . ,buf)
                                                               (:position . 133)
                                                               (:level . 3)
                                                               (:keyword . "DONE")
                                                               (:name . "cbx itm")
                                                               (:id . "789")
                                                               (:due)
                                                               (:member-ids . "")
                                                               (:desc)
                                                               (:tags)
                                                               (:unknown-properties)
                                                               (:parent . ,entity-cbx)))))
      (list
       (orgtrello-tests-hash-equal
        entities
        (orgtrello-hash-make-properties
         `(("123" . ,entity-card)
           ("456" . ,entity-cbx)
           ("789" . ,entity-cbx-item))))
       (orgtrello-tests-hash-equal
        adjacencies
        (orgtrello-hash-make-properties '(("123" "456")
                                          ("456" "789")))))))))
  ;; with narrow to region
  (should (-every? (-partial #'eq t)
                   (orgtrello-tests-with-temp-buffer
                    "* TODO card title
:PROPERTIES:
:orgtrello-id: 123
:orgtrello-checksum: check
:END:
* another card we do not care about here
** COMMENT, user date
"
                    (-let* ((buf (buffer-name (current-buffer)))
                            ((entities adjacencies)
                             (orgtrello-buffer-build-org-entities buf (point-min) 84))
                            (entity-card (orgtrello-hash-make-properties `((:buffername . ,buf)
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
                                                                           (:parent)))))
                      (list
                       (orgtrello-tests-hash-equal
                        entities
                        (orgtrello-hash-make-properties
                         `(("123" . ,entity-card))))
                       (orgtrello-tests-hash-equal
                        adjacencies
                        (orgtrello-hash-make-properties '(("123"))))))))))

(ert-deftest test-orgtrello-buffer-build-org-card-structure ()
  (should (-every? (-partial #'eq t)
                   (orgtrello-tests-with-temp-buffer
                    "* TODO card title
:PROPERTIES:
:orgtrello-id: 123
:orgtrello-checksum: check
:END:

  - [ ] cbx :PROPERTIES: {\"orgtrello-id\":\"456\"}
    - [X] cbx itm :PROPERTIES: {\"orgtrello-id\":\"789\"}
"
    (-let* ((buf (buffer-name (current-buffer)))
            ((entities adjacencies)
             (orgtrello-buffer-build-org-card-structure buf))
            (entity-card (orgtrello-hash-make-properties `((:buffername . ,buf)
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
                                                           (:parent))))
            (entity-cbx (orgtrello-hash-make-properties `((:buffername . ,buf)
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
                                                          (:parent . ,entity-card))))
            (entity-cbx-item (orgtrello-hash-make-properties `((:buffername . ,buf)
                                                               (:position . 133)
                                                               (:level . 3)
                                                               (:keyword . "DONE")
                                                               (:name . "cbx itm")
                                                               (:id . "789")
                                                               (:due)
                                                               (:member-ids . "")
                                                               (:desc)
                                                               (:tags)
                                                               (:unknown-properties)
                                                               (:parent . ,entity-cbx)))))
      (list
       (orgtrello-tests-hash-equal
        entities
        (orgtrello-hash-make-properties
         `(("123" . ,entity-card)
           ("456" . ,entity-cbx)
           ("789" . ,entity-cbx-item))))
       (orgtrello-tests-hash-equal
        adjacencies
        (orgtrello-hash-make-properties '(("123" "456")
                                          ("456" "789"))))))))))

(ert-deftest test-orgtrello-buffer--put-entities ()
  (should
   (-every? (-partial #'eq t)
            (-let ((entities (orgtrello-buffer--put-entities
                              (orgtrello-hash-make-properties `((:current . ,(orgtrello-hash-make-properties '((:id . "card-id-2"))))))
                              (orgtrello-hash-empty-hash))))
              (list
               (orgtrello-tests-hash-equal (gethash "card-id-2" entities) (orgtrello-hash-make-properties '((:id . "card-id-2"))))
               (eq 1 (hash-table-count entities)))))))

(ert-deftest test-orgtrello-buffer--put-card-with-adjacency ()
  (should
   (-every? (-partial #'eq t)
            (-let (((entities adjacencies) (orgtrello-buffer--put-card-with-adjacency
                                            (orgtrello-hash-make-properties `((:current . ,(orgtrello-hash-make-properties '((:id . "card-id"))))))
                                            (orgtrello-hash-empty-hash)
                                            :adjacencies)))
              (list
               (orgtrello-tests-hash-equal (gethash "card-id" entities) (orgtrello-hash-make-properties '((:id . "card-id"))))
               (eq 1 (hash-table-count entities))
               (eq adjacencies :adjacencies))))))

(ert-deftest test-orgtrello-buffer-clean-region ()
  (should (string= ""
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
  description
  - [ ] checklist
    - [ ] item
"
                    (orgtrello-buffer-clean-region (point-min) (point-max)))))
  (should (string= "* card"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
  description
  - [ ] checklist
    - [ ] item
"
                    (orgtrello-buffer-clean-region 7 (point-max))))))

(ert-deftest test-orgtrello-buffer-write-local-card-checksum-at-point ()
  (should (eq :result-card-checksum
              (with-mock
                (mock (orgtrello-buffer--write-checksum-at-pt 'orgtrello-buffer-card-checksum) => :result-card-checksum)
                (orgtrello-buffer-write-local-card-checksum-at-point)))))

(ert-deftest test-orgtrello-buffer-write-local-checklist-checksum-at-point ()
  (should (eq :result-checklist-checksum
              (with-mock
                (mock (orgtrello-buffer--write-checksum-at-pt 'orgtrello-buffer-checklist-checksum) => :result-checklist-checksum)
                (orgtrello-buffer-write-local-checklist-checksum-at-point)))))

(ert-deftest test-orgtrello-buffer-write-local-item-checksum-at-point ()
  (should (eq :result-item-checksum
              (with-mock
                (mock (orgtrello-buffer--write-checksum-at-pt 'orgtrello-buffer-item-checksum) => :result-item-checksum)
                (orgtrello-buffer-write-local-item-checksum-at-point)))))

(ert-deftest test-orgtrello-buffer-write-local-comment-checksum-at-point ()
  (should (eq :result-comment-checksum
              (with-mock
                (mock (orgtrello-buffer--write-checksum-at-pt 'orgtrello-buffer-comment-checksum) => :result-comment-checksum)
                (orgtrello-buffer-write-local-comment-checksum-at-point)))))

(ert-deftest test-orgtrello-buffer--write-checksum-at-pt ()
  (should (string= "* card
  :PROPERTIES:
  :orgtrello-local-checksum: dummy-checksum-whatever-the-input
  :END:
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
"
                    (orgtrello-buffer--write-checksum-at-pt (lambda () "dummy-checksum-whatever-the-input")))))
  (should (string= "- [ ] checklist :PROPERTIES: {\"orgtrello-local-checksum\":\"dummy-checksum-whatever-the-input\"}"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "- [ ] checklist"
                    (orgtrello-buffer--write-checksum-at-pt (lambda () "dummy-checksum-whatever-the-input"))))))

(ert-deftest test-orgtrello-buffer--write-card-description ()
  (should (string= "  some description"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    ""
                    (orgtrello-buffer--write-card-description "some description"))))
  (should-not (orgtrello-buffer--write-card-description nil)))

(ert-deftest test-orgtrello-buffer--write-comment-at-point ()
  (should (string=
           "
** COMMENT foobar, another-date-2
:PROPERTIES:
:orgtrello-id: comment-id-2
:orgtrello-local-checksum: 87e8512614a1e6ce4cf3b4814c89e0a42f01e448968638a6fd83b6ebdbd8eb83
:END:
  foo bar comment
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            ""
            (orgtrello-buffer--write-comment-at-point (orgtrello-hash-make-properties '((:comment-user . "foobar")
                                                                                        (:comment-date . "another-date-2")
                                                                                        (:comment-id   . "comment-id-2")
                                                                                        (:comment-text . "foo bar comment"))))))))

(ert-deftest test-orgtrello-buffer--write-comments-at-point ()
  (should (string=
           "
** COMMENT author, another-date
:PROPERTIES:
:orgtrello-id: comment-id
:orgtrello-local-checksum: ded0efd43d7371b5346b43d61792f896b261aacbb64c8a25c749aaf8e761c2c5
:END:
  yet another comment

** COMMENT foobar, another-date-2
:PROPERTIES:
:orgtrello-id: comment-id-2
:orgtrello-local-checksum: 8628459c72e9ae77754bfba52cf83fbf8c8447ae1cb7f89b134ec269fbde0011
:END:
  foo bar comment

"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            ""
            (orgtrello-buffer--write-comments-at-point (list (orgtrello-hash-make-properties '((:comment-user . "author")
                                                                                               (:comment-date . "another-date")
                                                                                               (:comment-id   . "comment-id")
                                                                                               (:comment-text . "yet another comment")))
                                                             (orgtrello-hash-make-properties '((:comment-user . "foobar")
                                                                                               (:comment-date . "another-date-2")
                                                                                               (:comment-id   . "comment-id-2")
                                                                                               (:comment-text . "foo bar comment"))))))))
  (should-not (orgtrello-buffer--write-comments-at-point nil)))

(ert-deftest test-orgtrello-buffer--write-comments ()
  (should (string=
           "
** COMMENT ardumont, some-date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: 3042a0c47942d4fcebd3f227a9762510295e57b6af490fb1c59db74949bb9ba4
:END:
  some comment

"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            ""
            (orgtrello-buffer--write-comments (orgtrello-hash-make-properties `((:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                                      (:comment-date . "some-date")
                                                                                                                                      (:comment-id   . "some-comment-id")
                                                                                                                                      (:comment-text . "some comment"))))))))))))


(ert-deftest test-orgtrello-buffer-update-property-member-ids ()
  (should (string=
           ":PROPERTIES:
#+PROPERTY: orgtrello-user-user1 123
#+PROPERTY: orgtrello-user-user2 456
#+PROPERTY: orgtrello-user-user3 789
:END:
* some card
  :PROPERTIES:
  :orgtrello-users: user3,user2
  :END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            ":PROPERTIES:
#+PROPERTY: orgtrello-user-user1 123
#+PROPERTY: orgtrello-user-user2 456
#+PROPERTY: orgtrello-user-user3 789
:END:
* some card
"
            (orgtrello-buffer-update-property-member-ids (orgtrello-hash-make-properties '((:member-ids . "orgtrello-user-user3,orgtrello-user-user2"))))))))

(ert-deftest test-orgtrello-buffer-org-file-get-property ()
  (should (eq :result
              (with-mock
                (mock (orgtrello-buffer-org-file-properties) => '((entry . :result)))
                (orgtrello-buffer-org-file-get-property 'entry)))))

(ert-deftest test-orgtrello-buffer-org-file-properties ()
  (should (eq :something
              (let ((org-file-properties :something))
                (orgtrello-buffer-org-file-properties)))))

(ert-deftest test-orgtrello-buffer-labels ()
  (should (equal '((":orange" "range")
                   (":green" "green label with & char")
                   (":red" "red")
                   (":blue" "blue")
                   (":purple" "violet")
                   (":sky" nil)
                   (":black" nil)
                   (":pink" nil)
                   (":lime" nil)
                   (":yellow" "yello")
                   (":grey" nil))
                 (orgtrello-tests-with-temp-buffer
                  ":PROPERTIES:
#+PROPERTY: :green green label with & char
#+PROPERTY: :yellow yello
#+PROPERTY: :orange range
#+PROPERTY: :red red
#+PROPERTY: :purple violet
#+PROPERTY: :blue blue
#+PROPERTY: orgtrello-user-me ardumont
"
                  (orgtrello-buffer-labels)))))

(ert-deftest test-orgtrello-buffer-org-entry-put ()
  (should (string= "* card
  :PROPERTIES:
  :something: with-value
  :END:
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
"
                    (orgtrello-buffer-org-entry-put (point-min) "something" "with-value"))))
  (should (string=
           "* card
:PROPERTIES:
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:something: with-value
:END:
"
            (orgtrello-buffer-org-entry-put (point-min) "something" nil))))
  (should (string=
           "* card
:PROPERTIES:
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:something: with-value
:END:
"
            (orgtrello-buffer-org-entry-put (point-min) "something" "")))))

(ert-deftest test-orgtrello-buffer--extract-comment-description-at-point ()
  (should (string=
           "  This is the description
  foo
  bar
"
           (orgtrello-tests-with-temp-buffer
            "* card
** COMMENT user, 2015-08-19T09:01:56.577Z
:PROPERTIES:
:END:
  This is the description
  foo
  bar
"
            (progn
              (goto-char (point-min))
              (orgtrello-buffer--extract-comment-description-at-point))))))

(ert-deftest test-orgtrello-buffer--extract-description-at-point ()
  (should (string=
           "card's description\non multiple\nlines"
           (orgtrello-tests-with-temp-buffer
            "* card
:PROPERTIES:
:END:
  card's description
  on multiple
  lines
** COMMENT user, 2015-08-19T09:01:56.577Z
:PROPERTIES:
:END:
  This is the description
  foo
  bar
"
            (progn
              (goto-char (point-min))
              (orgtrello-buffer--extract-description-at-point)))))
  (should (string=
           "  This is the description
  foo
  bar
"
           (orgtrello-tests-with-temp-buffer
            "* card
** COMMENT user, 2015-08-19T09:01:56.577Z
:PROPERTIES:
:END:
  This is the description
  foo
  bar
"
            (progn
              (goto-char (point-min))
              (forward-line)
              (orgtrello-buffer--extract-description-at-point))))))

(ert-deftest test-orgtrello-buffer-indent-region ()
  (should (string=
           "   something to indent with 3 spaces\n   on all string"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "something to indent with 3 spaces
on all string"
            (orgtrello-buffer-indent-region 3 `(,(point-min) ,(point-max))))))
  (should (string=
           "  already indented by 2 spaces on the first string\nso the second one won't be"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "  already indented by 2 spaces on the first string
so the second one won't be"
            (orgtrello-buffer-indent-region 2 `(,(point-min) ,(point-max)))))))

(ert-deftest test-orgtrello-buffer-indent-card-descriptions ()
  (should (string=
           "* card
  description not indented
  but this will be after function call.
* card 2
  another description which will be indented
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
description not indented
but this will be after function call.
* card 2
another description which will be indented
"
            (orgtrello-buffer-indent-card-descriptions))))
  ;; not indented
  (should (string=
           "* card
description not indented
but this will be after function call.
* card 2
another description which will be indented
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
description not indented
but this will be after function call.
* card 2
another description which will be indented
"
            (let ((org-trello--mode-activated-p))
              (orgtrello-buffer-indent-card-descriptions))))))

(ert-deftest  test-orgtrello-buffer-get-usernames-assigned-property ()
  (should (string= "user1,user2,user3"
                   (orgtrello-tests-with-temp-buffer
                    "* card
:PROPERTIES:
:orgtrello-users: user1,user2,user3
:END:
  description
"
                    (orgtrello-buffer-get-usernames-assigned-property)))))

(ert-deftest test-orgtrello-buffer--usernames-to-id ()
  (should (equal '("1" "2")
                 (orgtrello-buffer--usernames-to-id (orgtrello-hash-make-properties '(("orgtrello-user-user1" . "1")
                                                                                      ("orgtrello-user-user2" . "2")))
                                                    '("user1" "user2"))))
  (should-not (orgtrello-buffer--usernames-to-id (orgtrello-hash-make-properties '(("user1" . "1")
                                                                                   ("user2" . "2")))
                                                 nil))
  (should-not (orgtrello-buffer--usernames-to-id nil nil))
  (should-error (orgtrello-buffer--usernames-to-id nil '("1"))
                :type 'wrong-type-argument))

(ert-deftest test-orgtrello-buffer--user-ids-assigned-to-current-card ()
  (should (string= "123,456"
                   (orgtrello-tests-with-temp-buffer
                    "* card
:PROPERTIES:
:orgtrello-users: user1,user2
:END:
  description
"
                    (let ((org-trello--label-key-user-prefix "ot-u-")
                          (org-trello--hmap-users-name-id (orgtrello-hash-make-properties '(("ot-u-user1" . "123") ("ot-u-user2" . "456")))))
                      (orgtrello-buffer--user-ids-assigned-to-current-card))))))

(ert-deftest test-orgtrello-buffer-org-entry-get ()
  (should (string= "card-id-123"
                   (orgtrello-tests-with-temp-buffer
                    "* card
:PROPERTIES:
:org-id: card-id-123
:END:"
                    (orgtrello-buffer-org-entry-get (point-min) "org-id"))))
  (should (string= "checklist-id-456"
                   (orgtrello-tests-with-temp-buffer
                    "- [ ] checklist :PROPERTIES: {\"cbx-id\":\"checklist-id-456\"}
"
                    (orgtrello-buffer-org-entry-get (point-min) "cbx-id"))))
  (should (string= "item-id-789"
                   (orgtrello-tests-with-temp-buffer
                    "  - [ ] item :PROPERTIES: {\"itm-id\":\"item-id-789\"}
"
                    (orgtrello-buffer-org-entry-get (point-min) "itm-id")))))

(ert-deftest test-orgtrello-buffer-extract-identifier ()
  (should (string= "card-id-321"
                   (orgtrello-tests-with-temp-buffer
                    "* card
:PROPERTIES:
:orgtrello-id: card-id-321
:END:"
                    (orgtrello-buffer-extract-identifier (point-min)))))
  (should (string= "checklist-id-654"
                   (orgtrello-tests-with-temp-buffer
                    "- [ ] checklist :PROPERTIES: {\"orgtrello-id\":\"checklist-id-654\"}
"
                    (orgtrello-buffer-extract-identifier (point-min)))))
  (should (string= "item-id-987"
                   (orgtrello-tests-with-temp-buffer
                    "  - [ ] item :PROPERTIES: {\"orgtrello-id\":\"item-id-987\"}
"
                    (orgtrello-buffer-extract-identifier (point-min))))))

(ert-deftest test-orgtrello-buffer-indent-card-data ()
  ;; indentation
  (should (string= "* card0
  - [ ] check1
    - [ ] item1
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card0
- [ ] check1
  - [ ] item1
"
                    (orgtrello-buffer-indent-card-data))))
  ;; not indented because no org-trello activated
  (should (string= "* card0
- [ ] check1
  - [ ] item1
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card0
- [ ] check1
  - [ ] item1
"
                    (let (org-trello--mode-activated-p)
                      (orgtrello-buffer-indent-card-data))))))

(ert-deftest test-orgtrello-buffer--extract-metadata ()
  (should (equal '(1 1 nil nil "card" nil)
                 (orgtrello-tests-with-temp-buffer
                  "* card
:PROPERTIES:
:orgtrello-id: abc
:orgtrello-users: user1,user2
:END:
"
                  (orgtrello-buffer--extract-metadata))))
  (should (equal '(-1 nil "DONE" nil "checklist title" nil)
                 (orgtrello-tests-with-temp-buffer
                  "* card
- [X] checklist title
"
                  (orgtrello-buffer--extract-metadata)))))

(ert-deftest test-orgtrello-buffer-set-property ()
  ;; card, comment
  (should (string= "* card
  :PROPERTIES:
  :orgtrello-id: card-id-abc
  :END:"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card"
                    (orgtrello-buffer-set-property "orgtrello-id" "card-id-abc"))))
  (should (string= "* card
  :PROPERTIES:
  :orgtrello-id: card-id-abc2
  :orgtrello-checksum: card-checksum
  :END:"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
  :PROPERTIES:
  :orgtrello-id: card-id-abc
  :END:"
                    (progn
                      (orgtrello-buffer-set-property "orgtrello-checksum" "card-checksum")
                      (orgtrello-buffer-set-property "orgtrello-id" "card-id-abc2")))))
  ;; checkbox (checklist/item)
  (should (string= "- [ ] checklist :PROPERTIES: {\"orgtrello-id\":\"checklist-id\"}"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "- [ ] checklist"
                    (orgtrello-buffer-set-property "orgtrello-id" "checklist-id"))))
  (should (string= "- [ ] checklist :PROPERTIES: {\"orgtrello-id\":\"checklist-id2\",\"orgtrello-checksum\":\"checklist-checksum\"}"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "- [ ] checklist :PROPERTIES: {\"orgtrello-id\":\"checklist-id\"}"
                    (progn
                      (orgtrello-buffer-set-property "orgtrello-id" "checklist-id2")
                      (orgtrello-buffer-set-property "orgtrello-checksum" "checklist-checksum")))))
  )

(ert-deftest test-orgtrello-buffer--compute-entity-to-org-entry-fn ()
  (should
   (equal 'orgtrello-buffer--compute-card-to-org-entry
          (with-mock
            (mock (orgtrello-data-entity-card-p :entity) => t)
            (orgtrello-buffer--compute-entity-to-org-entry-fn :entity))))
  (should
   (equal 'orgtrello-buffer--compute-checklist-to-org-entry
          (with-mock
            (mock (orgtrello-data-entity-card-p :entity) => nil)
            (mock (orgtrello-data-entity-checklist-p :entity) => t)
            (orgtrello-buffer--compute-entity-to-org-entry-fn :entity))))
  (should
   (equal 'orgtrello-buffer--compute-item-to-org-entry
          (with-mock
            (mock (orgtrello-data-entity-card-p :entity) => nil)
            (mock (orgtrello-data-entity-checklist-p :entity) => nil)
            (mock (orgtrello-data-entity-item-p :entity) => t)
            (orgtrello-buffer--compute-entity-to-org-entry-fn :entity)))))

(ert-deftest test-orgtrello-buffer-compute-entity-to-org-entry ()
  (should
   (equal :some-output
          (with-mock
            (mock (orgtrello-buffer--compute-entity-to-org-entry-fn :entity) => (lambda (entity) :some-output))
            (orgtrello-buffer-compute-entity-to-org-entry :entity)))))

(ert-deftest test-orgtrello-buffer--compute-card-to-org-entry ()
  (should
   (string= "* IN-PROGRESS card-name                                                 orange,purple
DEADLINE: <2015-08-30 Sun 15:00>\n"
            (orgtrello-buffer--compute-card-to-org-entry
             (orgtrello-hash-make-properties '((:name . "card-name")
                                               (:keyword . "IN-PROGRESS")
                                               (:due . "2015-08-30T14:00:00.000Z")
                                               (:tags . "orange,purple")))))))

(ert-deftest test-orgtrello-buffer--compute-checklist-to-org-entry ()
  (should (equal "  - [-] name\n" (orgtrello-buffer--compute-checklist-to-org-entry (orgtrello-hash-make-properties `((:name . "name")))))))

(ert-deftest test-orgtrello-buffer--compute-item-to-org-entry ()
  (should (equal "    - [X] name\n" (orgtrello-buffer--compute-item-to-org-entry (orgtrello-hash-make-properties `((:name . "name") (:keyword . "complete"))))))
  (should (equal "    - [ ] name\n" (orgtrello-buffer--compute-item-to-org-entry (orgtrello-hash-make-properties `((:name . "name") (:keyword . "incomplete")))))))

(ert-deftest test-orgtrello-buffer--extract-card-description-at-point ()
  (should (string= "llo there"
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
   DEADLINE: <2014-04-01T00:00:00.000Z>
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
hello there
"
                                                     (orgtrello-buffer--extract-card-description-at-point))))

  (should (string= "hello there"
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
    - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
    - [X] Common-Lisp :PROPERTIES: {\"orgtrello-id\":\"52c94518b2c5b28e37012ba4\"}"
                                                     (orgtrello-buffer--extract-card-description-at-point))))

  (should (string= "\nhello there\n"
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:

  hello there

  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
    - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
    - [X] Common-Lisp :PROPERTIES: {\"orgtrello-id\":\"52c94518b2c5b28e37012ba4\"}"
                                                     (orgtrello-buffer--extract-card-description-at-point))))

  (should (string= ""
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES" (orgtrello-buffer--extract-card-description-at-point))))

  (should (string= ""
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}"
                                                     (orgtrello-buffer--extract-card-description-at-point))))
  (should (string= "One Paragraph\n\nAnother Paragraph"
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
  DEADLINE: <2014-04-01T00:00:00.000Z>
  :PROPERTIES:
  :orgtrello-id: 52c945143004d4617c012528
  :END:
  One Paragraph

  Another Paragraph
"
                                                     (orgtrello-buffer--extract-card-description-at-point))))
  (should (string= "hello there"
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
 :PROPERTIES:
 :orgtrello-id: 52c945143004d4617c012528
 :END:
  hello there
"
                                                     (orgtrello-buffer--extract-card-description-at-point))))

  (should (string= "hello there"
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
 :PROPERTIES:
 :orgtrello-id: 52c945143004d4617c012528
    :END:
  hello there
  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
    - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
    - [X] Common-Lisp :PROPERTIES: {\"orgtrello-id\":\"52c94518b2c5b28e37012ba4\"}"
                                                     (orgtrello-buffer--extract-card-description-at-point))))

  (should (string= "\nhello there\n"
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
  :PROPERTIES:
         :orgtrello-id: 52c945143004d4617c012528
  :END:

  hello there

  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
    - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
    - [X] Common-Lisp :PROPERTIES: {\"orgtrello-id\":\"52c94518b2c5b28e37012ba4\"}"
                                                     (orgtrello-buffer--extract-card-description-at-point))))

  (should (string= ""
                   (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
  :PROPERTIES:
 :orgtrello-id: 52c945143004d4617c012528
:END:
  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}"
                                                     (orgtrello-buffer--extract-card-description-at-point)))))

(ert-deftest test-orgtrello-buffer-board-id ()
  (should (equal
           "this-is-the-board-id"
           (orgtrello-tests-with-org-buffer
            (format ":PROPERTIES:\n#+PROPERTY: %s this-is-the-board-id\n:END:\n* card\n" org-trello--property-board-id)
            (orgtrello-buffer-board-id)))))

(ert-deftest test-orgtrello-buffer-board-name ()
  (should (equal "this-is-the-board-name"
                 (orgtrello-tests-with-org-buffer
                  (format ":PROPERTIES:\n#+PROPERTY: %s this-is-the-board-name\n:END:\n* card\n" org-trello--property-board-name)
                  (orgtrello-buffer-board-name)))))

(ert-deftest test-orgtrello-buffer-me ()
  (should (equal "this-is-the-user"
                 (orgtrello-tests-with-org-buffer
                  (format ":PROPERTIES:\n#+PROPERTY: %s this-is-the-user\n:END:\n* card\n" org-trello--property-user-me)
                  (orgtrello-buffer-me)))))

(ert-deftest test-orgtrello-buffer-write-card-header ()
  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
* TODO some card name
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :END:
  some description"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
"

                  (orgtrello-buffer-write-card-header "some-card-id" (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                                                       (:member-ids . "ardumont,dude")
                                                                                                       (:comments . 'no-longer-exploited-here-comments)
                                                                                                       (:desc . "some description")
                                                                                                       (:level . ,org-trello--card-level)
                                                                                                       (:name . "some card name"))))

                  0)))

  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
* TODO some card name                                                   :red:green:
DEADLINE: <dummy-date-with-right-locale>
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :END:
  some description"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
"
                  (with-mock
                    (mock (orgtrello-date-convert-trello-date-to-org-date "2015-09-22T23:45:00.000Z") => "dummy-date-with-right-locale")
                    (orgtrello-buffer-write-card-header "some-card-id" (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                                                         (:member-ids . "ardumont,dude")
                                                                                                         (:comments . 'no-longer-exploited-here-comments)
                                                                                                         (:tags . ":red:green:")
                                                                                                         (:desc . "some description")
                                                                                                         (:level . ,org-trello--card-level)
                                                                                                         (:name . "some card name")
                                                                                                         (:due . "2015-09-22T23:45:00.000Z")))))
                  0))))

(ert-deftest test-orgtrello-buffer-write-checklist-header ()
  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO some old card name
  :PROPERTIES:
  :orgtrello-id: some-id
  :orgtrello-users: ardumont,dude
  :orgtrello-card-comments:
  :END:
  some old description
  - [ ] some old checklist name
  - [-] some checklist name
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO some old card name
  :PROPERTIES:
  :orgtrello-id: some-id
  :orgtrello-users: ardumont,dude
  :orgtrello-card-comments:
  :END:
  some old description
  - [ ] some old checklist name\n"
                  (orgtrello-buffer-write-checklist-header "some-id" (orgtrello-hash-make-properties `((:keyword . "DONE")
                                                                                                        (:level . ,org-trello--checklist-level)
                                                                                                        (:name . "some checklist name"))))
                  0))))

(ert-deftest test-orgtrello-buffer-write-card ()
  ;; no previous card on buffer
  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
* TODO some card name                                                   :red:green:
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :orgtrello-local-checksum: local-card-checksum-456
  :orgtrello-id: some-card-id
  :END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"local-checkbox-checksum-456\"}
    - [X] some item name :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"local-item-checksum-456\"}
    - [ ] some other item name :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"local-item-checksum-456\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"local-checkbox-checksum-456\"}

** COMMENT ardumont, some-date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: local-comment-checksum-456
:END:
  some comment

"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
"
                  (with-mock
                    (mock (orgtrello-buffer-card-checksum) => "local-card-checksum-456")
                    (mock (orgtrello-buffer-checklist-checksum) => "local-checkbox-checksum-456")
                    (mock (orgtrello-buffer-item-checksum) => "local-item-checksum-456")
                    (mock (orgtrello-buffer-comment-checksum) => "local-comment-checksum-456")
                    (orgtrello-buffer-write-card "some-card-id"
                                                 (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                                   (:member-ids . "ardumont,dude")
                                                                                   (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                                         (:comment-date . "some-date")
                                                                                                                                         (:comment-id   . "some-comment-id")
                                                                                                                                         (:comment-text . "some comment")))))
                                                                                   (:tags . ":red:green:")
                                                                                   (:desc . "some description")
                                                                                   (:level . ,org-trello--card-level)
                                                                                   (:name . "some card name")
                                                                                   (:id . "some-card-id")))
                                                 (orgtrello-hash-make-properties `(("some-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-checklist-id")
                                                                                                                                             (:name . "some checklist name")
                                                                                                                                             (:level . ,org-trello--checklist-level))))
                                                                                   ("some-other-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-other-checklist-id")
                                                                                                                                                   (:name . "some other checklist name")
                                                                                                                                                   (:level . ,org-trello--checklist-level))))
                                                                                   ("some-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-item-id")
                                                                                                                                         (:name . "some item name")
                                                                                                                                         (:level . ,org-trello--item-level)
                                                                                                                                         (:keyword . "DONE"))))
                                                                                   ("some-other-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-other-item-id")
                                                                                                                                               (:name . "some other item name")
                                                                                                                                               (:level . ,org-trello--item-level)
                                                                                                                                               (:keyword . "TODO"))))))

                                                 (orgtrello-hash-make-properties `(("some-other-checklist-id" . ())
                                                                                   ("some-checklist-id" . ("some-item-id" "some-other-item-id"))
                                                                                   ("some-card-id" . ("some-checklist-id" "some-other-checklist-id"))))))
                  0)))

  ;; with previous cards on buffer
  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
* TODO task A
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :orgtrello-id: card-id-a
  :orgtrello-local-checksum: local-card-checksum-a
  :END:
  description A

** COMMENT ardumont, some-date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: local-comment-checksum-a
:END:
  some comment

** COMMENT ben, 10/01/2202
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-local-checksum: local-comment-checksum-a
:END:
  comment text

* TODO task B
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :orgtrello-id: card-id-b
  :orgtrello-local-checksum: local-card-checksum-b
  :END:
  description B

** COMMENT tony, 10/10/2014
:PROPERTIES:
:orgtrello-id: some-com-id
:orgtrello-local-checksum: local-comment-checksum-b
:END:
  some text

"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
"
                  (progn
                    (with-mock
                      (mock (orgtrello-buffer-card-checksum) => "local-card-checksum-a")
                      (mock (orgtrello-buffer-comment-checksum) => "local-comment-checksum-a")
                      (orgtrello-buffer-write-card "card-id-a"
                                                   (orgtrello-hash-make-properties
                                                    `((:keyword . "TODO")
                                                      (:desc . "description A")
                                                      (:level . ,org-trello--card-level)
                                                      (:name . "task A")
                                                      (:id . "card-id-a")
                                                      (:member-ids . "ardumont,dude")
                                                      (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                            (:comment-date . "some-date")
                                                                                                            (:comment-id   . "some-comment-id")
                                                                                                            (:comment-text . "some comment")))
                                                                          (orgtrello-hash-make-properties '((:comment-user . "ben")
                                                                                                            (:comment-date . "10/01/2202")
                                                                                                            (:comment-id   . "some-id")
                                                                                                            (:comment-text . "comment text")))))))
                                                   (orgtrello-hash-make-properties `())
                                                   (orgtrello-hash-make-properties `())))
                    (with-mock
                      (mock (orgtrello-buffer-card-checksum) => "local-card-checksum-b")
                      (mock (orgtrello-buffer-comment-checksum) => "local-comment-checksum-b")
                      (orgtrello-buffer-write-card "card-id-b"
                                                   (orgtrello-hash-make-properties
                                                    `((:keyword . "TODO")
                                                      (:desc . "description B")
                                                      (:level . ,org-trello--card-level)
                                                      (:name . "task B")
                                                      (:id . "card-id-b")
                                                      (:member-ids . "ardumont,dude")
                                                      (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "tony")
                                                                                                            (:comment-date . "10/10/2014")
                                                                                                            (:comment-id   . "some-com-id")
                                                                                                            (:comment-text . "some text")))))))
                                                   (orgtrello-hash-make-properties `())
                                                   (orgtrello-hash-make-properties `()))))
                  0))))

(ert-deftest test-orgtrello-controller-sync-buffer-with-trello-cards ()
  ;; successive writes on buffer with indentation
  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO task A
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :orgtrello-id: card-id-a
  :orgtrello-local-checksum: local-card-checksum
  :END:


** COMMENT ardumont, some-date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: local-comment-checksum
:END:
  some comment

** COMMENT ben, 10/01/2202
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-local-checksum: local-comment-checksum
:END:
  comment text

* TODO task B
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :orgtrello-id: card-id-b
  :orgtrello-local-checksum: local-card-checksum
  :END:


** COMMENT tony, 10/10/2014
:PROPERTIES:
:orgtrello-id: some-com-id
:orgtrello-local-checksum: local-comment-checksum
:END:
  some text

"
                 (orgtrello-tests-with-temp-buffer-and-return-indented-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

"
                  (progn
                    (with-mock
                      (mock (orgtrello-buffer-card-checksum) => "local-card-checksum")
                      (mock (orgtrello-buffer-comment-checksum) => "local-comment-checksum")
                      (orgtrello-controller-sync-buffer-with-trello-cards (buffer-name)
                                                                          `(,(orgtrello-hash-make-properties
                                                                              `((:keyword . "TODO")
                                                                                (:desc . "")
                                                                                (:level . ,org-trello--card-level)
                                                                                (:name . "task A")
                                                                                (:id . "card-id-a")
                                                                                (:member-ids . "ardumont-id,dude-id")
                                                                                (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                                      (:comment-date . "some-date")
                                                                                                                                      (:comment-id   . "some-comment-id")
                                                                                                                                      (:comment-text . "some comment")))
                                                                                                    (orgtrello-hash-make-properties '((:comment-user . "ben")
                                                                                                                                      (:comment-date . "10/01/2202")
                                                                                                                                      (:comment-id   . "some-id")
                                                                                                                                      (:comment-text . "comment text")))))))
                                                                            ,(orgtrello-hash-make-properties
                                                                              `((:keyword . "TODO")
                                                                                (:desc . "")
                                                                                (:level . ,org-trello--card-level)
                                                                                (:name . "task B")
                                                                                (:id . "card-id-b")
                                                                                (:member-ids . "ardumont-id,dude-id")
                                                                                (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "tony")
                                                                                                                                      (:comment-date . "10/10/2014")
                                                                                                                                      (:comment-id   . "some-com-id")
                                                                                                                                      (:comment-text . "some text")))))))))))
                  0))))

(ert-deftest test-orgtrello-buffer-write-checklist ()
  ;; Simple case
  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO some card name
  :PROPERTIES:
  :orgtrello-id: some-card-id
  :orgtrello-users: ardumont,dude
  :orgtrello-card-comments: ardumont: some comment
  :orgtrello-local-checksum: 1234-card-checksum
  :END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"1234-checklist-checksum\"}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO some card name
  :PROPERTIES:
  :orgtrello-id: some-card-id
  :orgtrello-users: ardumont,dude
  :orgtrello-card-comments: ardumont: some comment
  :END:
  some description
"
                  (with-mock
                    (mock (orgtrello-buffer-checklist-checksum) => "1234-checklist-checksum")
                    (mock (orgtrello-buffer-card-checksum) => "1234-card-checksum")
                    (orgtrello-buffer-write-checklist "some-checklist-id"
                                                      (orgtrello-hash-make-properties `(("some-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-checklist-id")
                                                                                                                                                  (:name . "some checklist name")
                                                                                                                                                  (:level . ,org-trello--checklist-level))))))
                                                      (orgtrello-hash-make-properties `(("some-checklist-id" . nil)))))
                  0)))
  ;; a little more complicated case
  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO some card name
  :PROPERTIES:
  :orgtrello-id: some-card-id
  :orgtrello-users: ardumont,dude
  :orgtrello-card-comments: ardumont: some comment
  :orgtrello-local-checksum: card-checksum-654321
  :END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-654321\"}
    - [X] some item name :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"item-checksum-654321\"}
    - [ ] some other item name :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"item-checksum-654321\"}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO some card name
  :PROPERTIES:
  :orgtrello-id: some-card-id
  :orgtrello-users: ardumont,dude
  :orgtrello-card-comments: ardumont: some comment
  :END:
  some description
"
                  (with-mock
                    (mock (orgtrello-buffer-item-checksum) => "item-checksum-654321")
                    (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-654321")
                    (mock (orgtrello-buffer-card-checksum) => "card-checksum-654321")
                    (orgtrello-buffer-write-checklist "some-checklist-id"
                                                      (orgtrello-hash-make-properties `(("some-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-checklist-id")
                                                                                                                                                  (:name . "some checklist name")
                                                                                                                                                  (:level . ,org-trello--checklist-level))))
                                                                                        ("some-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-item-id")
                                                                                                                                              (:name . "some item name")
                                                                                                                                              (:level . ,org-trello--item-level)
                                                                                                                                              (:keyword . "DONE"))))
                                                                                        ("some-other-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-other-item-id")
                                                                                                                                                    (:name . "some other item name")
                                                                                                                                                    (:level . ,org-trello--item-level)
                                                                                                                                                    (:keyword . "TODO"))))))
                                                      (orgtrello-hash-make-properties `(("some-checklist-id" . ("some-item-id" "some-other-item-id"))))))
                  0))))

(ert-deftest test-orgtrello-buffer-write-item ()
  (should (equal ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO some card name
  :PROPERTIES:
  :orgtrello-id: some-card-id
  :orgtrello-users: ardumont,dude
  :orgtrello-card-comments: ardumont: some comment
  :orgtrello-local-checksum: card-checksum-135
  :END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-135\"}
    - [X] some item name :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"item-checksum-135\"}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:

* TODO some card name
  :PROPERTIES:
  :orgtrello-id: some-card-id
  :orgtrello-users: ardumont,dude
  :orgtrello-card-comments: ardumont: some comment
  :END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
"
                  (with-mock
                    (mock (orgtrello-buffer-item-checksum) => "item-checksum-135")
                    (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-135")
                    (mock (orgtrello-buffer-card-checksum) => "card-checksum-135")
                    (orgtrello-buffer-write-item "some-item-id"
                                                 (orgtrello-hash-make-properties `(("some-item-id" . ,(orgtrello-hash-make-properties `((:id . "some-item-id")
                                                                                                                                        (:name . "some item name")
                                                                                                                                        (:level . ,org-trello--item-level)
                                                                                                                                        (:keyword . "DONE"))))))))
                  0))))

(ert-deftest test-orgtrello-buffer-write-entity ()
  ;; card
  (should (equal "
* DONE some card name                                                   :red:green:
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  "\n"
                  (orgtrello-buffer-write-entity "some-card-id" (orgtrello-hash-make-properties `((:keyword . "DONE")
                                                                                                  (:tags . ":red:green:")
                                                                                                  (:desc . "some description")
                                                                                                  (:level . ,org-trello--card-level)
                                                                                                  (:name . "some card name"))))
                  0)))
  ;; checklist
  (should (equal "* some content
  - [-] some checklist name
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  "* some content
"
                  (orgtrello-buffer-write-entity "some-checklist-id" (orgtrello-hash-make-properties `((:keyword . "DONE")
                                                                                                       (:level . ,org-trello--checklist-level)
                                                                                                       (:name . "some checklist name"))))
                  0)))
  ;; item
  (should (equal "* some content
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item name
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  "* some content
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
"
                  (orgtrello-buffer-write-entity "some-item-id" (orgtrello-hash-make-properties `((:keyword . "DONE")
                                                                                                  (:level . ,org-trello--item-level)
                                                                                                  (:name . "some item name"))))
                  0))))

(ert-deftest test-orgtrello-buffer--compute-item-to-org-checkbox ()
  (should (equal "  - [X] name\n" (orgtrello-buffer--compute-item-to-org-checkbox "name" 2 "complete")))
  (should (equal "    - [X] name\n" (orgtrello-buffer--compute-item-to-org-checkbox "name" 3 "complete")))
  (should (equal "  - [X] name\n" (orgtrello-buffer--compute-item-to-org-checkbox "name" 2 "complete")))
  (should (equal "    - [ ] name\n" (orgtrello-buffer--compute-item-to-org-checkbox "name" 3 "incomplete"))))

(ert-deftest test-orgtrello-buffer--private-compute-card-to-org-entry ()
  (should (equal "* TODO name                                                             :some-tags:\nDEADLINE: <date>\n"
                 (with-mock
                   (mock (orgtrello-date-convert-trello-date-to-org-date "some-date") => "date")
                   (orgtrello-buffer--private-compute-card-to-org-entry "name" "TODO" "some-date" ":some-tags:"))))
  (should (equal "* DONE name\n"
                 (orgtrello-buffer--private-compute-card-to-org-entry "name" "DONE" nil nil)))
  (should (equal "* name\n"
                 (orgtrello-buffer--private-compute-card-to-org-entry "name" nil nil nil)))
  (should (equal "* IN-P name                                                             :tag,tag2:\n"
                 (orgtrello-buffer--private-compute-card-to-org-entry "name" "IN-P" nil ":tag,tag2:"))))

(ert-deftest test-orgtrello-buffer--compute-due-date ()
  (should (equal "DEADLINE: <date-formatted>\n"
                 (with-mock
                   (mock (orgtrello-date-convert-trello-date-to-org-date "some-date") => "date-formatted")
                   (orgtrello-buffer--compute-due-date "some-date"))))
  (should (equal "" (orgtrello-buffer--compute-due-date nil))))

(ert-deftest test-orgtrello-buffer--serialize-tags ()
  (should (equal "" (orgtrello-buffer--serialize-tags "* card name" nil)))
  (should (equal "" (orgtrello-buffer--serialize-tags "* card name" "")))
  (should (equal "                                                             :red:green:" (orgtrello-buffer--serialize-tags "* card name" ":red:green:")))
  (should (equal "                                                     :red:green:blue:" (orgtrello-buffer--serialize-tags "* another card name" ":red:green:blue:")))
  (should (equal " :red:green:blue:" (orgtrello-buffer--serialize-tags "* this is another card name with an extremely long label name, more than 72 chars" ":red:green:blue:"))))

(ert-deftest test-orgtrello-buffer--compute-marker-from-entry ()
  (should (equal "id"                                                        (orgtrello-buffer--compute-marker-from-entry (orgtrello-data-make-hash-org :users :level :kwd :name      "id"  :due :position :buffername :desc :tags :unknown))))
  (should (equal "orgtrello-marker-2a0b98e652ce6349a0659a7a8eeb3783ffe9a11a" (orgtrello-buffer--compute-marker-from-entry (orgtrello-data-make-hash-org :users :level :kwd "some-name" nil :due 1234      "buffername" :desc :tags :unknown))))
  (should (equal "orgtrello-marker-6c59c5dcf6c83edaeb3f4923bfd929a091504bb3" (orgtrello-buffer--compute-marker-from-entry (orgtrello-data-make-hash-org :users :level :kwd "some-name" nil :due 4321      "some-other-buffername" :desc :tags :unknown)))))

(ert-deftest test-orgtrello-buffer--compute-level-into-spaces ()
  (should (equal 2 (orgtrello-buffer--compute-level-into-spaces 2)))
  (should (equal 4 (orgtrello-buffer--compute-level-into-spaces nil)))
  (should (equal 4 (orgtrello-buffer--compute-level-into-spaces 'any))))

(ert-deftest test-orgtrello-buffer--compute-checklist-to-org-checkbox ()
  (should (equal "  - [X] name\n" (orgtrello-buffer--compute-checklist-to-org-checkbox "name" 2 "complete")))
  (should (equal "    - [X] name\n" (orgtrello-buffer--compute-checklist-to-org-checkbox "name" 3 "complete")))
  (should (equal "  - [X] name\n" (orgtrello-buffer--compute-checklist-to-org-checkbox "name" 2 "complete")))
  (should (equal "    - [-] name\n" (orgtrello-buffer--compute-checklist-to-org-checkbox "name" 3 "incomplete"))))

(ert-deftest test-orgtrello-buffer--compute-state-checkbox ()
  (should (equal "[X]" (orgtrello-buffer--compute-state-checkbox "complete")))
  (should (equal "[-]" (orgtrello-buffer--compute-state-checkbox "incomplete"))))

(ert-deftest test-orgtrello-buffer--dispatch-create-entities-map-with-adjacency ()
  (should (equal 'orgtrello-buffer--put-card-with-adjacency      (orgtrello-buffer--dispatch-create-entities-map-with-adjacency (orgtrello-data-make-hash-org :users org-trello--card-level nil nil nil nil nil nil nil :tags :unknown))))
  (should (equal 'orgtrello-backend--put-entities-with-adjacency (orgtrello-buffer--dispatch-create-entities-map-with-adjacency (orgtrello-data-make-hash-org :users org-trello--checklist-level nil nil nil nil nil nil nil :tags :unknown))))
  (should (equal 'orgtrello-backend--put-entities-with-adjacency (orgtrello-buffer--dispatch-create-entities-map-with-adjacency (orgtrello-data-make-hash-org :users org-trello--item-level nil nil nil nil nil nil nil :tags :unknown)))))

(ert-deftest test-orgtrello-buffer--to-orgtrello-metadata ()
  (should (equal "some name :orgtrello-id-identifier:"  (gethash :name       (orgtrello-buffer--to-orgtrello-metadata '(:unknown "" "" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal "IN PROGRESS"                          (gethash :keyword    (orgtrello-buffer--to-orgtrello-metadata '(:unknown "" "" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal 0                                      (gethash :level      (orgtrello-buffer--to-orgtrello-metadata '(:unknown "" "" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal :id                                    (gethash :id         (orgtrello-buffer--to-orgtrello-metadata '(:unknown "" "" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal :due                                   (gethash :due        (orgtrello-buffer--to-orgtrello-metadata '(:unknown "" "" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal :point                                 (gethash :position   (orgtrello-buffer--to-orgtrello-metadata '(:unknown "" "" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal "1,2,3"                                (gethash :member-ids (orgtrello-buffer--to-orgtrello-metadata '(:unknown "" "1,2,3" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal :desc                                  (gethash :desc       (orgtrello-buffer--to-orgtrello-metadata '(:unknown :desc "1,2,3" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal :unknown                               (gethash :unknown-properties (orgtrello-buffer--to-orgtrello-metadata '(:unknown :desc "1,2,3" "buffer-name.org" :point :id :due 0 1 "IN PROGRESS" nil "some name :orgtrello-id-identifier:" nil)))))
  (should (equal :default (let ((org-trello--org-keyword-trello-list-names '(:default :other-keywords-we-do-not-care)))
                            (gethash :keyword (orgtrello-buffer--to-orgtrello-metadata '(:unknown "" "" "buffer-name.org" :point :id :due 0 1 nil nil "some name :orgtrello-id-identifier:" nil)))))))

(ert-deftest test-orgtrello-buffer-entry-get-full-metadata ()
  ;; on card
  (should (equal nil    (->> (orgtrello-tests-with-temp-buffer "* card" (orgtrello-buffer-entry-get-full-metadata))
                             (orgtrello-data-parent))))
  (should (equal nil    (->> (orgtrello-tests-with-temp-buffer "* card" (orgtrello-buffer-entry-get-full-metadata))
                             (orgtrello-data-grandparent))))
  (should (equal "card" (->> (orgtrello-tests-with-temp-buffer "* card" (orgtrello-buffer-entry-get-full-metadata))
                             (orgtrello-data-current)
                             orgtrello-data-entity-name)))
  ;; on checklist
  (should (equal "card"      (->> (orgtrello-tests-with-temp-buffer "* card\n  - [ ] checklist\n" (orgtrello-buffer-entry-get-full-metadata))
                                  (orgtrello-data-parent)
                                  orgtrello-data-entity-name)))
  (should (equal nil         (->> (orgtrello-tests-with-temp-buffer "* card\n  - [ ] checklist\n" (orgtrello-buffer-entry-get-full-metadata))
                                  (orgtrello-data-grandparent))))
  (should (equal "checklist" (->> (orgtrello-tests-with-temp-buffer "* card\n  - [ ] checklist\n" (orgtrello-buffer-entry-get-full-metadata))
                                  (orgtrello-data-current)
                                  orgtrello-data-entity-name)))
  ;; on item
  (should (equal "checklist" (->> (orgtrello-tests-with-temp-buffer "* card\n  - [ ] checklist\n    - [ ] item\n" (orgtrello-buffer-entry-get-full-metadata))
                                  (orgtrello-data-parent)
                                  orgtrello-data-entity-name)))
  (should (equal "card"      (->> (orgtrello-tests-with-temp-buffer "* card\n  - [ ] checklist\n    - [ ] item\n" (orgtrello-buffer-entry-get-full-metadata))
                                  (orgtrello-data-grandparent)
                                  orgtrello-data-entity-name)))
  (should (equal "item"      (->> (orgtrello-tests-with-temp-buffer "* card\n  - [ ] checklist\n    - [ ] item\n" (orgtrello-buffer-entry-get-full-metadata))
                                  (orgtrello-data-current)
                                  orgtrello-data-entity-name))))

(ert-deftest test-orgtrello-buffer-entity-metadata ()
  ;; card
  (let ((h-values (orgtrello-tests-with-temp-buffer ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont some-user-id
#+PROPERTY: orgtrello-user-dude some-user-id2
:END:

* TODO card title
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-users: ardumont,dude
:END:
  some description\n"
                                                    (progn (orgtrello-entity-back-to-card)
                                                           (orgtrello-buffer-entity-metadata)))))
    (should (equal 1                                                             (orgtrello-data-entity-level h-values)))
    (should (equal nil                                                           (orgtrello-data-entity-tags h-values)))
    (should (equal "card title"                                                  (orgtrello-data-entity-name h-values)))
    (should (equal "some-id"                                                     (orgtrello-data-entity-id h-values)))
    (should (equal nil                                                           (orgtrello-data-entity-due h-values)))
    (should (equal "some description"                                            (orgtrello-data-entity-description h-values)))
    (should (equal "some-user-id,some-user-id2"                                  (orgtrello-data-entity-member-ids h-values)))
    (should (equal "TODO"                                                        (orgtrello-data-entity-keyword h-values)))
    (should (equal nil                                                           (orgtrello-data-entity-unknown-properties h-values))))
  ;; comment
  (let ((h-values (orgtrello-tests-with-temp-buffer ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont some-user-id
#+PROPERTY: orgtrello-user-dude some-user-id2
:END:

* TODO card title
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-users: ardumont,dude
:END:
  some description\n
** COMMENT, user date
:PROPERTIES:
:orgtrello-id: some-comment-id
:END:
the comment is here, the other are trello's metadata
this comment can be multiline
and contains text
nothing enforces the content of the description
"
                                                    (progn (orgtrello-entity-back-to-card)
                                                           (orgtrello-buffer-entity-metadata)))))
    (should (equal "some-comment-id"                                             (orgtrello-data-entity-id h-values)))
    (should (equal "the comment is here, the other are trello's metadata
this comment can be multiline
and contains text
nothing enforces the content of the description
"                                 (orgtrello-data-entity-description h-values)))))

(ert-deftest test-orgtrello-buffer-compute-marker ()
  (should (equal "orgtrello-marker-2a0b98e652ce6349a0659a7a8eeb3783ffe9a11a" (orgtrello-buffer-compute-marker "buffername" "some-name" 1234)))
  (should (equal "orgtrello-marker-6c59c5dcf6c83edaeb3f4923bfd929a091504bb3" (orgtrello-buffer-compute-marker "some-other-buffername" "some-name" 4321))))

(ert-deftest test-orgtrello-buffer--filter-out-known-properties ()
  (should (equal '(("some-unknown-thingy" . "some value"))
                 (orgtrello-buffer--filter-out-known-properties '(("orgtrello-id" . "orgtrello-marker-08677ec948991d1e5a25ab6b813d8eba03fac20f")
                                                                   ("orgtrello-users" . "some user")
                                                                   ("some-unknown-thingy" . "some value")
                                                                   ("CATEGORY" . "TESTS-simple"))))))

(ert-deftest test-orgtrello-buffer-org-unknown-drawer-properties ()
  (should (equal
           '(("some-unknown-thingy" . "some value"))
           (orgtrello-tests-with-temp-buffer
            "* TODO Joy of FUN(ctional) LANGUAGES
DEADLINE: <2014-05-17 Sat>
:PROPERTIES:
:orgtrello-id: orgtrello-marker-08677ec948991d1e5a25ab6b813d8eba03fac20f
:some-unknown-thingy: some value
:orgtrello-users: ardumont
:orgtrello-unknown-key-prefixed-by-orgtrello: some unknown value that will be filtered
:END:
"
            (orgtrello-buffer-org-unknown-drawer-properties)))))

(ert-deftest test-orgtrello-buffer-update-properties-unknown ()
  (should (equal
           "* TODO Joy of FUN(ctional) LANGUAGES
DEADLINE: <2014-05-17 Sat>
:PROPERTIES:
:orgtrello-id: orgtrello-marker-08677ec948991d1e5a25ab6b813d8eba03fac20f
:property0: value0
:property1: value1
:property2: value2
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* TODO Joy of FUN(ctional) LANGUAGES
DEADLINE: <2014-05-17 Sat>
:PROPERTIES:
:orgtrello-id: orgtrello-marker-08677ec948991d1e5a25ab6b813d8eba03fac20f
:END:
"
            (orgtrello-buffer-update-properties-unknown '(("property0" . "value0")
                                                           ("property1" . "value1")
                                                           ("property2" . "value2")))))))

(ert-deftest test-orgtrello-buffer-overwrite-card ()
  ;; No previous content on buffer
  (should (equal "* TODO some card name                                                   :red:green:
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :orgtrello-local-checksum: local-card-checksum-567
  :orgtrello-id: some-card-id
  :END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"local-checkbox-checksum-567\"}
    - [X] some item name :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"local-item-checksum-567\"}
    - [ ] some other item name :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"local-item-checksum-567\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"local-checkbox-checksum-567\"}

** COMMENT ardumont, some-date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: local-comment-checksum-567
:END:
  some comment

"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  "" ;; no previous content on buffer
                  (with-mock
                    (mock (orgtrello-buffer-card-checksum) => "local-card-checksum-567")
                    (mock (orgtrello-buffer-checklist-checksum) => "local-checkbox-checksum-567")
                    (mock (orgtrello-buffer-item-checksum) => "local-item-checksum-567")
                    (mock (orgtrello-buffer-comment-checksum) => "local-comment-checksum-567")
                    (let* ((card (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                   (:member-ids . "ardumont,dude")
                                                                   (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                         (:comment-date . "some-date")
                                                                                                                         (:comment-id   . "some-comment-id")
                                                                                                                         (:comment-text . "some comment")))))
                                                                   (:tags . ":red:green:")
                                                                   (:desc . "some description")
                                                                   (:level . ,org-trello--card-level)
                                                                   (:name . "some card name")
                                                                   (:id . "some-card-id"))))
                           (entities (orgtrello-hash-make-properties `(("some-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-checklist-id")
                                                                                                                                 (:name . "some checklist name")
                                                                                                                                 (:level . ,org-trello--checklist-level))))
                                                                       ("some-other-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-other-checklist-id")
                                                                                                                                       (:name . "some other checklist name")
                                                                                                                                       (:level . ,org-trello--checklist-level))))
                                                                       ("some-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-item-id")
                                                                                                                             (:name . "some item name")
                                                                                                                             (:level . ,org-trello--item-level)
                                                                                                                             (:keyword . "DONE"))))
                                                                       ("some-other-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-other-item-id")
                                                                                                                                   (:name . "some other item name")
                                                                                                                                   (:level . ,org-trello--item-level)
                                                                                                                                   (:keyword . "TODO")))))))
                           (entities-adj (orgtrello-hash-make-properties `(("some-other-checklist-id" . ())
                                                                           ("some-checklist-id" . ("some-item-id" "some-other-item-id"))
                                                                           ("some-card-id" . ("some-checklist-id" "some-other-checklist-id"))))))
                      (orgtrello-buffer-overwrite-card '(1 2) card entities entities-adj))))))
  ;; Multiple cards present at point. Overwrite given previous region card with updated data.
  (should (equal "* TODO some card name                                                   :red:green:
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :orgtrello-local-checksum: local-card-checksum-567
  :orgtrello-id: some-card-id
  :END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"local-checklist-checksum-567\"}
    - [X] some item name :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"local-item-checksum-567\"}
    - [ ] some other item name :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"local-item-checksum-567\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"local-checklist-checksum-567\"}

** COMMENT ardumont, some-date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: local-comment-checksum-567
:END:
  some comment


* IN-PROGRESS another card
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ,
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* IN-PROGRESS another card
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
"
                  (with-mock
                    (mock (orgtrello-buffer-card-checksum) => "local-card-checksum-567")
                    (mock (orgtrello-buffer-checklist-checksum) => "local-checklist-checksum-567")
                    (mock (orgtrello-buffer-item-checksum) => "local-item-checksum-567")
                    (mock (orgtrello-buffer-comment-checksum) => "local-comment-checksum-567")
                    (let* ((card (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                   (:member-ids . "ardumont,dude")
                                                                   (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                         (:comment-date . "some-date")
                                                                                                                         (:comment-id   . "some-comment-id")
                                                                                                                         (:comment-text . "some comment")))))
                                                                   (:tags . ":red:green:")
                                                                   (:desc . "some description")
                                                                   (:level . ,org-trello--card-level)
                                                                   (:name . "some card name")
                                                                   (:id . "some-card-id"))))
                           (entities (orgtrello-hash-make-properties `(("some-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-checklist-id")
                                                                                                                                 (:name . "some checklist name")
                                                                                                                                 (:level . ,org-trello--checklist-level))))
                                                                       ("some-other-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-other-checklist-id")
                                                                                                                                       (:name . "some other checklist name")
                                                                                                                                       (:level . ,org-trello--checklist-level))))
                                                                       ("some-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-item-id")
                                                                                                                             (:name . "some item name")
                                                                                                                             (:level . ,org-trello--item-level)
                                                                                                                             (:keyword . "DONE"))))
                                                                       ("some-other-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-other-item-id")
                                                                                                                                   (:name . "some other item name")
                                                                                                                                   (:level . ,org-trello--item-level)
                                                                                                                                   (:keyword . "TODO")))))))
                           (entities-adj (orgtrello-hash-make-properties `(("some-other-checklist-id" . ())
                                                                           ("some-checklist-id" . ("some-item-id" "some-other-item-id"))
                                                                           ("some-card-id" . ("some-checklist-id" "some-other-checklist-id"))))))
                      (orgtrello-buffer-overwrite-card '(1 469) card entities entities-adj)))
                  -5))))

(ert-deftest test-orgtrello-buffer-get-card-local-checksum ()
  "Retrieve the card's checksum."
  (should (equal
           "123"
           (orgtrello-tests-with-temp-buffer "* card
:PROPERTIES:
:orgtrello-local-checksum: 123
:END:"
                                             (orgtrello-buffer-get-card-local-checksum))))
  (should (equal
           nil
           (orgtrello-tests-with-temp-buffer "* card"
                                             (orgtrello-buffer-get-card-local-checksum)))))

(ert-deftest test-orgtrello-buffer-write-local-checksum-at-pt ()
  ;; Write checklist's local checksum at the current position.
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-098
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-098\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"

           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-098")
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-098")
                                                                         (orgtrello-buffer-write-local-checksum-at-pt))
                                                                       -5)))
  ;; checklist - Write local checksum's item at the current position.
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-098876
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-098876\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"item-checksum-098876\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"

           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-item-checksum) => "item-checksum-098876")
                                                                         (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-098876")
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-098876")
                                                                         (orgtrello-buffer-write-local-checksum-at-pt))
                                                                       -4)))
  ;; Write local card checksum at the current position.
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card
  :PROPERTIES:
  :orgtrello-local-checksum: card-checksum-987
  :END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-987")
                                                                         (orgtrello-buffer-write-local-checksum-at-pt)))))

  ;; checklist - Write local checksum at the current position for card's comment.
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-123
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
** COMMENT ardumont, date
   :PROPERTIES:
   :orgtrello-local-checksum: comment-checksum-123
   :END:
  some comment
* another card"

           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
** COMMENT ardumont, date
  some comment
* another card"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-comment-checksum) => "comment-checksum-123")
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-123")
                                                                         (orgtrello-buffer-write-local-checksum-at-pt))
                                                                       -2))))

(ert-deftest test-orgtrello-buffer-org-delete-property ()
  ;; On a checklist
  (should (equal "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                                                             (orgtrello-buffer-org-delete-property "orgtrello-id"))))
  ;; on checklist without property
  (should (equal "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {}
"
                                                                             (orgtrello-buffer-org-delete-property "orgtrello-id"))))
  ;; On an item with property to delete
  (should (equal "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                                                             (orgtrello-buffer-org-delete-property "orgtrello-id")
                                                                             -2)))

  ;; On an item with no previous property to delete
  (should (equal "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                                                             (orgtrello-buffer-org-delete-property "orgtrello-id")
                                                                             -2)))
  ;; On a card.
  (should (equal "* TODO some card name
:PROPERTIES:
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                                                             (orgtrello-buffer-org-delete-property "orgtrello-id")
                                                                             -5)))

  ;; On a card - no previous property.
  (should (equal "* TODO some card name
:PROPERTIES:
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                                                             (orgtrello-buffer-org-delete-property "orgtrello-id")
                                                                             -5))))

(ert-deftest test-orgtrello-buffer-write-local-checksum-at-pt-checklist ()
  ;; on a checklist without checksum yet
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-876
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-876\"}
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-876")
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-876")
                                                                         (orgtrello-buffer-write-local-checksum-at-pt))
                                                                       -1)))
  ;; already with a checksum
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-543
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-543\"}
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\"}
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-543")
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-543")
                                                                         (orgtrello-buffer-write-local-checksum-at-pt))
                                                                       -1))))

(ert-deftest test-orgtrello-buffer-write-local-checksum-at-pt-card ()
  ;; card + current checklist checksum updated
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-432
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist names :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-432\"}
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist names :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-432")
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-432")
                                                                         (orgtrello-buffer-write-local-checksum-at-pt))
                                                                       -1))))

(ert-deftest test-orgtrello-buffer-write-local-item-checksum-at-point ()
  "The local checksum changes if modifications."
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"item-checksum-43210\"}
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-item-checksum) => "item-checksum-43210")
                                                                         (orgtrello-buffer-write-local-item-checksum-at-point))
                                                                       -1))))

(ert-deftest test-orgtrello-buffer-write-local-comment-checksum-at-point ()
  ;; The local checksum changes if modifications.
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
** COMMENT user, date
:PROPERTIES:
:orgtrello-local-checksum: comment-checksum-10324
:END:
  some comment
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
** COMMENT user, date
:PROPERTIES:
:END:
  some comment
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-comment-checksum) => "comment-checksum-10324")
                                                                         (orgtrello-buffer-write-local-comment-checksum-at-point))
                                                                       -1))))

(ert-deftest test-orgtrello-buffer-get-checkbox-local-checksum-checklist ()
  ;; The local checksum does not change if no modification.
  (should (equal
           nil
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist names :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                             (orgtrello-buffer-get-checkbox-local-checksum)
                                             -1)))
  (should (equal
           "bar"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\", \"orgtrello-local-checksum\":\"bar\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\", \"orgtrello-local-checksum\":\"foo\"}
"
                                             (orgtrello-buffer-get-checkbox-local-checksum)
                                             -2)))
  ;; Retrieve the local checksum from item.
  (should (equal
           "foo"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\", \"orgtrello-local-checksum\":\"foo\"}
"
                                             (orgtrello-buffer-get-checkbox-local-checksum)
                                             -1)))
  ;; Works also on card but it is not intended to!
  (should (equal
           "foobar"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: foobar
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\", \"orgtrello-local-checksum\":\"bar\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\", \"orgtrello-local-checksum\":\"foo\"}
"
                                             (orgtrello-buffer-get-checkbox-local-checksum)
                                             -3))))


(ert-deftest test-orgtrello-buffer-compute-checksum ()
  ;; Compute the checksum of the card.
  (should (equal
           "card-checksum"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: foobar
:END:
  some description
  - [-] some checklist name
    - [ ] some other item"
                                             (with-mock
                                               (mock (orgtrello-buffer-card-checksum) => "card-checksum")
                                               (orgtrello-buffer-compute-checksum))
                                             -10)))

  ;; Compute the checksum of the checklist.
  (should (equal
           "checklist-checksum"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: foobar
:END:
  some description
  - [-] some checklist name
    - [ ] some other item"
                                             (with-mock
                                               (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum")
                                               (orgtrello-buffer-compute-checksum))
                                             -1)))

  ;; Compute the checksum of the item.
  (should (equal
           "item-checksum"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: foobar
:END:
  some description
  - [-] some checklist name
    - [ ] some other item
"
                                             (with-mock
                                               (mock (orgtrello-buffer-item-checksum) => "item-checksum")
                                               (orgtrello-buffer-compute-checksum))
                                             -1)))
  ;; Compute the checksum of the item.
  (should (equal
           "comment-checksum"
           (orgtrello-tests-with-temp-buffer "* card
** COMMENT ardumont, date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: foobar
:END:
  some comment
"
                                             (with-mock
                                               (mock (orgtrello-buffer-comment-checksum) => "comment-checksum")
                                               (orgtrello-buffer-compute-checksum))))))

(ert-deftest test-orgtrello-buffer-get-local-checksum ()
  ;; The local checksum does not change if no modification.
  (should (equal
           nil
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist names :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                             (orgtrello-buffer-get-local-checksum)
                                             -1)))
  (should (equal
           "bar"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\", \"orgtrello-local-checksum\":\"bar\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\", \"orgtrello-local-checksum\":\"foo\"}
"
                                             (orgtrello-buffer-get-local-checksum)
                                             -2)))
  ;; Retrieve the local checksum from item.
  (should (equal
           "foo"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: blah
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\", \"orgtrello-local-checksum\":\"foo\"}
"
                                             (orgtrello-buffer-get-local-checksum)
                                             -1)))
  ;; Works also on card but it is not intended to!
  (should (equal
           "foobar"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: foobar
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\", \"orgtrello-local-checksum\":\"bar\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\", \"orgtrello-local-checksum\":\"foo\"}
"
                                             (orgtrello-buffer-get-local-checksum)
                                             -3))))

(ert-deftest test-orgtrello-buffer-write-properties-at-pt ()
  ;; Update card property's id + card checksum computation and update.
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-321
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: foobar
:END:
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-321")
                                                                         (orgtrello-buffer-write-properties-at-pt "some-id")))))
  ;; Update checkbox property's id + compute checksum at point and set it.
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-321
:END:
  - [ ] new checkbox :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-321\"}
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: foobar
:END:
  - [ ] new checkbox
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-321")
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-321")
                                                                         (orgtrello-buffer-write-properties-at-pt "some-checklist-id"))
                                                                       -1)))
  ;; Update checkbox property's id + compute checksum at point and set it.
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: card-checksum-321
:END:
  - [ ] new checkbox :PROPERTIES: {\"orgtrello-local-checksum\":\"checklist-checksum-321\"}
    - [ ] new item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"item-checksum-321\"}
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: foobar
:END:
  - [ ] new checkbox
    - [ ] new item
"
                                                                       (with-mock
                                                                         (mock (orgtrello-buffer-item-checksum) => "item-checksum-321")
                                                                         (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-321")
                                                                         (mock (orgtrello-buffer-card-checksum) => "card-checksum-321")
                                                                         (orgtrello-buffer-write-properties-at-pt "some-item-id"))
                                                                       -1))))


(ert-deftest test-orgtrello-buffer-checksum ()
  (should (string= "cabc552bfc3fb1fe64933c9b6a5eb41c8f81cd969e0c8add55870c0afb87c63c"
                   (orgtrello-buffer-checksum "some simple text")))
  (should (string= "b6132893c37102ca9d2f2323e057aa9e0573bdd9fb1a48141a469b8407552ac7"
                   (orgtrello-buffer-checksum "some simple text\nwith-multiple\nlines"))))

(ert-deftest test-orgtrello-buffer-delete-property-from-entry ()
  ;; remove only the property
  (should (string= "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"aabbcc\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"ddeeff\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"gghhii\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"jjkkll\"}
* another card"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: some-local-checksum
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"aabbcc\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"ddeeff\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"gghhii\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"jjkkll\"}
* another card"
                                                                               (orgtrello-buffer-delete-property-from-entry "orgtrello-local-checksum")))))

(ert-deftest test-orgtrello-buffer-delete-property ()
  (should (string= "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name
    - [X] some item
    - [ ] some other item
  - [-] some other checklist name
* another card"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: some-local-checksum
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"aabbcc\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"ddeeff\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"gghhii\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"jjkkll\"}
* another card"
                                                                               (orgtrello-buffer-delete-property "orgtrello-local-checksum")
                                                                               -1))))

(ert-deftest test-orgtrello-buffer--compute-string-for-checksum ()
  "Compute the region to checksum on an entity."
  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name
    - [X] some item
    - [ ] some other item
  - [-] some other checklist name


1"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"
                                             (let ((orgtrello-setup-use-position-in-checksum-computation 'please-do-use-position-in-checksumt))
                                               (orgtrello-buffer--compute-string-for-checksum (orgtrello-entity-card-region)))
                                             -5)))

  (should (equal
           "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name
    - [X] some item
    - [ ] some other item
  - [-] some other checklist name

"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"
                                             (let ((orgtrello-setup-use-position-in-checksum-computation nil))
                                               (orgtrello-buffer--compute-string-for-checksum (orgtrello-entity-card-region)))
                                             -5)))

  ;; checklist
  (should (equal
           "  - [-] some other checklist name
482"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: a058272445d320995bd4c677dd35c0924ff65ce7640cbe7cae21d6ea39ff32c6
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [X] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                             (orgtrello-buffer--compute-string-for-checksum (orgtrello-entity-compute-checklist-region))
                                             -1)))
  (should (equal
           "    - [X] some other item
405"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: a058272445d320995bd4c677dd35c0924ff65ce7640cbe7cae21d6ea39ff32c6
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [X] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                             (orgtrello-buffer--compute-string-for-checksum (orgtrello-entity-compute-item-region))
                                             -2))))

(ert-deftest test-orgtrello-buffer-card-checksum ()
  ;; Compute the checksum of a card.
  (should (equal
           "2a71e11a34c8778629d2e1c36f9efdec3e81a0013bd56c649e88e4d91fd91d3a"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"
                                             (orgtrello-buffer-card-checksum)
                                             -5)))
  ;; A card with a checksum should give the same checksum if nothing has changed.
  (should (equal
           "2a71e11a34c8778629d2e1c36f9efdec3e81a0013bd56c649e88e4d91fd91d3a"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: 2a71e11a34c8778629d2e1c36f9efdec3e81a0013bd56c649e88e4d91fd91d3a
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"
                                             (orgtrello-buffer-card-checksum)
                                             -5)))
  ;; A modified card with a checksum should give another checksum.
  (should (equal
           "c3875e3e92a0aa7df37b97e58b2c30ade2a84235e7c8303a29e22bcde93d3847"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: 2a71e11a34c8778629d2e1c36f9efdec3e81a0013bd56c649e88e4d91fd91d3a
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [X] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* another card"
                                             (orgtrello-buffer-card-checksum)
                                             -5))))


(ert-deftest test-orgtrello-buffer-checklist-checksum ()
  ;; A checklist gives a checksum when asked politely.
  (should (equal
           "a9a2d45c6d406ef5bd9f8654f663ed8df222b030893d8a00cfdc37a6b3431378"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: a058272445d320995bd4c677dd35c0924ff65ce7640cbe7cae21d6ea39ff32c6
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [X] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}
"
                                             (orgtrello-buffer-checklist-checksum)
                                             -1)))
  ;; A checklist gives a checksum when asked politely - does not take `'orgtrello-local-checksum`' property into account.
  ;; checksum-not-modified-gives-same-checksum
  (should (equal
           "a9a2d45c6d406ef5bd9f8654f663ed8df222b030893d8a00cfdc37a6b3431378"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: a058272445d320995bd4c677dd35c0924ff65ce7640cbe7cae21d6ea39ff32c6
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [X] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\", \"orgtrello-local-checksum\":\"a9a2d45c6d406ef5bd9f8654f663ed8df222b030893d8a00cfdc37a6b3431378\"}
"
                                             (orgtrello-buffer-checklist-checksum)
                                             -1)))
  ;; A checklist checksum takes into account its items. If items change then the checkbox's checksum is updated.
  ;; checksum-updates-so-new-checksum
  (should (equal
           "4abd37301df93d3de1c4cd66a6cd0fe0e2a2115968511d554dd422477ab085f4"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: dcae7ad96da00965d3f63eb9104fa676d9ee0d2cedc69b1fd865d0f8c2a0b3f5
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
"
                                             (orgtrello-buffer-checklist-checksum)
                                             -2)))
  (should (equal
           "38797826a0d514e63129ad8d7563d59a5f8c6008c9335cc9213eee0124dd254d"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: a058272445d320995bd4c677dd35c0924ff65ce7640cbe7cae21d6ea39ff32c6
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [ ] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
"
                                             (orgtrello-buffer-checklist-checksum)
                                             -2))))

(ert-deftest test-orgtrello-buffer-item-checksum ()
  "An item's checksum"
  (should (equal
           "66c919bd5d8d258feed09d6af2ada061e6abb0aed934534ad77b2f858d156bb0"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: a058272445d320995bd4c677dd35c0924ff65ce7640cbe7cae21d6ea39ff32c6
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
"
                                             (orgtrello-buffer-item-checksum)
                                             -1)))
  ;; An item's checksum does not change even if there is already a checksum computed.
  ;; checksum-not-modified-so-same-checksum
  (should (equal
           "66c919bd5d8d258feed09d6af2ada061e6abb0aed934534ad77b2f858d156bb0"
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: e7dc2fd6842e823786868235b6b33cb4cad4b75f73fed32bdb3df1dc54ef0418
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\", \"orgtrello-local-checksum\":\"66c919bd5d8d258feed09d6af2ada061e6abb0aed934534ad77b2f858d156bb0\"}
"
                                             (orgtrello-buffer-item-checksum)
                                             -1)))  )

(ert-deftest test-orgtrello-buffer-comment-checksum ()
  ;; A comment's checksum
  (should (equal
           "e4d969d8287880e52f02d216131a70cffd91cee0eba5c6ed866fdfcf0a8afc95"
           (orgtrello-tests-with-temp-buffer "** COMMENT ardumont,date
:PROPERTIES:
:orgtrello-id: some-comment-id
:END:
  some comment
"
                                             (orgtrello-buffer-comment-checksum)
                                             -1)))
  ;; A comment's checksum is not modified if no updates on it
  (should (equal
           "e4d969d8287880e52f02d216131a70cffd91cee0eba5c6ed866fdfcf0a8afc95"
           (orgtrello-tests-with-temp-buffer "** COMMENT ardumont,date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: e4d969d8287880e52f02d216131a70cffd91cee0eba5c6ed866fdfcf0a8afc95
:END:
  some comment
"
                                             (orgtrello-buffer-comment-checksum)
                                             -1)))
  ;; A comment's checksum is modified if checksum's values changed
  (should (equal
           "41d89d3b85c121ee47d2e1e8ee7c070767c542e17ad9899ecd7c995543c7366c"
           (orgtrello-tests-with-temp-buffer "** COMMENT ardumont,date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: e4d969d8287880e52f02d216131a70cffd91cee0eba5c6ed866fdfcf0a8afc95
:END:
  some slightly modified comment
generates another checksum
"
                                             (orgtrello-buffer-comment-checksum)))))

(ert-deftest test-orgtrello-buffer-checklist-beginning-pt ()
  "Determine the beginning of the checklist."
  (should (equal
           262
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: a058272445d320995bd4c677dd35c0924ff65ce7640cbe7cae21d6ea39ff32c6
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\", \"orgtrello-local-checksum\":\"d5503e92e8880ddb839c42e31e8ead17a70f09d39f069fbfd9956424984047fc\"}
"
                                             (orgtrello-buffer-checklist-beginning-pt)
                                             -1)))

  (should (equal
           262
           (orgtrello-tests-with-temp-buffer "* TODO some card name
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-users: ardumont,dude
:orgtrello-card-comments: ardumont: some comment
:orgtrello-local-checksum: a058272445d320995bd4c677dd35c0924ff65ce7640cbe7cae21d6ea39ff32c6
:END:
  some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\", \"orgtrello-local-checksum\":\"d5503e92e8880ddb839c42e31e8ead17a70f09d39f069fbfd9956424984047fc\"}
"
                                             (orgtrello-buffer-checklist-beginning-pt)
                                             -2))))

(ert-deftest test-orgtrello-buffer-filtered-kwds ()
  (should (equal
           '("TODO" "IN-PROGRESS" "DONE" "PENDING" "DELEGATED" "FAILED" "CANCELLED")
           (orgtrello-tests-with-temp-buffer
            ":PROPERTIES:
#+PROPERTY: board-name api test board
#+PROPERTY: board-id abc
#+PROPERTY: CANCELLED def
#+PROPERTY: FAILED ijk
#+PROPERTY: DELEGATED lmn
#+PROPERTY: PENDING opq
#+PROPERTY: DONE rst
#+PROPERTY: IN-PROGRESS uvw
#+PROPERTY: TODO xyz
#+TODO: TODO IN-PROGRESS DONE | PENDING DELEGATED FAILED CANCELLED
#+PROPERTY: orgtrello-user-orgmode 888
#+PROPERTY: orgtrello-user-ardumont 999
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:"
            (orgtrello-buffer-filtered-kwds)))))

(ert-deftest test-orgtrello-buffer-org-file-properties ()
  (should (equal
           '(("board-name" . "api test board")
             ("board-id" . "abc")
             ("CANCELLED" . "def")
             ("FAILED" . "ijk")
             ("DELEGATED" . "lmn")
             ("PENDING" . "opq")
             ("DONE" . "rst")
             ("IN-PROGRESS" . "uvw")
             ("TODO" . "xyz")
             ("orgtrello-user-orgmode" . "888")
             ("orgtrello-user-ardumont" . "999")
             (":yellow" . "yellow label")
             (":red" . "red label")
             (":purple" . "this is the purple label")
             (":orange" . "orange label")
             (":green" . "green label with & char")
             ("orgtrello-user-me" . "ardumont"))
           (orgtrello-tests-with-temp-buffer
            ":PROPERTIES:
#+PROPERTY: board-name api test board
#+PROPERTY: board-id abc
#+PROPERTY: CANCELLED def
#+PROPERTY: FAILED ijk
#+PROPERTY: DELEGATED lmn
#+PROPERTY: PENDING opq
#+PROPERTY: DONE rst
#+PROPERTY: IN-PROGRESS uvw
#+PROPERTY: TODO xyz
#+TODO: TODO IN-PROGRESS DONE | PENDING DELEGATED FAILED CANCELLED
#+PROPERTY: orgtrello-user-orgmode 888
#+PROPERTY: orgtrello-user-ardumont 999
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:"
            (orgtrello-buffer-org-file-properties)))))

(ert-deftest test-orgtrello-buffer--serialize-comment ()
  (should (equal "\n** COMMENT tony, 10/10/2013\n:PROPERTIES:\n:orgtrello-id: comment-id\n:END:\n  hello, this is a comment!\n"
                 (orgtrello-buffer--serialize-comment (orgtrello-hash-make-properties '((:comment-user . "tony")
                                                                                         (:comment-date . "10/10/2013")
                                                                                         (:comment-id   . "comment-id")
                                                                                         (:comment-text . "hello, this is a comment!")))))))

(ert-deftest test-orgtrello-buffer-trim-input-comment ()
  (should (string= "text as is"
                   (orgtrello-buffer-trim-input-comment "# hello, some comment\n# ignore this also\ntext as is")))
  (should (string= "text as is\nwith lines"
                   (orgtrello-buffer-trim-input-comment "# hello, some comment\n# ignore this also\ntext as is\nwith lines\n")))
  (should (string= "line 1     \nline 2"
                   (orgtrello-buffer-trim-input-comment "# comment line\n# another comment line\nline 1     \nline 2\n\n\n"))))

(ert-deftest test-orgtrello-buffer--prepare-comment ()
  (should (string= "  a\n  b\n  c"
                   (orgtrello-buffer--prepare-comment "a\nb\nc")))
  (should (string= "  \n  a\n  b\n  c\n  "
                   (orgtrello-buffer--prepare-comment "\na\nb\nc\n"))))

(ert-deftest test-orgtrello-buffer-colors ()
  (should (equal '(":orange" ":green" ":red" ":blue" ":purple" ":sky" ":black" ":pink" ":lime" ":yellow" ":grey")
                 (orgtrello-buffer-colors))))

(provide 'org-trello-buffer-test)
;;; org-trello-buffer-test.el ends here
