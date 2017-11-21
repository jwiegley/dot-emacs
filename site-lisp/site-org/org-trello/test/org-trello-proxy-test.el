(require 'org-trello-proxy)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-proxy--getting-back-to-headline ()
  (should (equal :result
                 (with-mock
                   (mock (orgtrello-buffer-compute-entity-to-org-entry :data) => :org-entity)
                   (mock (orgtrello-proxy--getting-back-to-marker :org-entity) => :result)
                   (orgtrello-proxy--getting-back-to-headline :data)))))

(ert-deftest test-orgtrello-proxy--compute-pattern-search-from-marker ()
  (should (equal :anything (orgtrello-proxy--compute-pattern-search-from-marker :anything)))
  (should (equal 'x (orgtrello-proxy--compute-pattern-search-from-marker 'x))))

(ert-deftest test-orgtrello-proxy--getting-back-to-marker ()
  (should
   (equal 17 (orgtrello-tests-with-temp-buffer
              "blablablabla\nxyz\nhello\n"
              (progn
                (orgtrello-proxy--getting-back-to-marker "xyz")
                (point))))))

(ert-deftest test-orgtrello-proxy--get-back-to-marker ()
    (should (equal :result
                   (with-mock
                     (mock (orgtrello-proxy--getting-back-to-marker :marker) => nil)
                     (mock (orgtrello-proxy--getting-back-to-headline :data) => :result)
                     (orgtrello-proxy--get-back-to-marker :marker :data))))
    (should (equal :ok
                   (with-mock
                     (mock (orgtrello-proxy--getting-back-to-marker :marker) => :ok)
                     (orgtrello-proxy--get-back-to-marker :marker :data)))))

(ert-deftest test-orgtrello-proxy--compute-sync-next-level ()
  (should (equal '(2)
                 (with-mock
                   (mock (orgtrello-data-get-children :entity :entities-adjacencies) => '(:child-id0))
                   (mock (orgtrello-data-get-entity :child-id0 :entities-adjacencies) => :full-entity-0)
                   (mock (orgtrello-proxy-sync-entity :full-entity-0 :entities-adjacencies) => '(+ 1 1))
                   (orgtrello-proxy--compute-sync-next-level :entity :entities-adjacencies)))))

(ert-deftest test-orgtrello-proxy--update-entities-adjacencies ()
  (-every?
   (-partial 'eq t)
   (-let* ((old-entity (orgtrello-hash-make-properties '((:id . :potential-marker-id)
                                                         (:parent . :some-parent))))
           (entity-synced (orgtrello-hash-make-properties '((:id . :new-trello-id))))
           (entities (orgtrello-hash-make-properties `((:potential-marker-id . ,old-entity))))
           (adjacencies (orgtrello-hash-make-properties `((:potential-marker-id :checklist-id0 :checklist-id1))))
           (entities-adjacencies (list entities adjacencies))
           ((updated-synced-entity updated-entities updated-adjacencies) (orgtrello-proxy--update-entities-adjacencies old-entity entity-synced entities-adjacencies)))
     (list
      (orgtrello-tests-hash-equal
       (orgtrello-hash-make-properties '((:id . :new-trello-id)
                                         (:parent . :some-parent)))
       updated-synced-entity)
      (orgtrello-tests-hash-equal
       (orgtrello-hash-make-properties `((:potential-marker-id . ,old-entity)
                                         (:new-trello-id . ,updated-synced-entity)
                                         (:checklist-id0)
                                         (:checklist-id1)))
       updated-entities)
      (orgtrello-tests-hash-equal
       (orgtrello-hash-make-properties `((:potential-marker-id :checklist-id0 :checklist-id1)
                                         (:new-trello-id :checklist-id0 :checklist-id1)))
       updated-adjacencies)))))

(ert-deftest test-orgtrello-proxy--standard-post-or-put-success-callback ()
  ;; should update the marker with the id returned from trello
  (should (string=
           "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 55d07e8ada66fd9de074b82e
:orgtrello-local-checksum: 0face23ee36812bb4ef1321e2567196080b80dc2c6ffd9a19734433b34836303
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: orgtrello-marker-blah
:END:
"
            (let* ((entity (orgtrello-hash-make-properties `((:id . "orgtrello-marker-blah")
                                                             (:buffername . ,(current-buffer))
                                                             (:name . "Joy of FUN(ctional) LANGUAGES"))))
                   (entities-adjacencies (list (orgtrello-hash-empty-hash) (orgtrello-hash-empty-hash)))
                   (entity-synced (orgtrello-hash-make-properties '((:id . "55d07e8ada66fd9de074b82e"))))
                   (response (make-request-response :data entity-synced)))
              (apply (orgtrello-proxy--standard-post-or-put-success-callback entity entities-adjacencies) (list response))))))
  (should (string=
           "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 55d07e8ada66fd9de074b82e
:orgtrello-local-checksum: 0face23ee36812bb4ef1321e2567196080b80dc2c6ffd9a19734433b34836303
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 55d07e8ada66fd9de074b82e
:END:
"
            (let* ((entity (orgtrello-hash-make-properties `((:id . "55d07e8ada66fd9de074b82e")
                                                             (:buffername . ,(current-buffer))
                                                             (:name . "Joy of FUN(ctional) LANGUAGES"))))
                   (entities-adjacencies (list (orgtrello-hash-empty-hash) (orgtrello-hash-empty-hash)))
                   (entity-synced (orgtrello-hash-make-properties '((:id . "55d07e8ada66fd9de074b82e")
                                                                    (:name . "Joy of FUN(ctional) LANGUAGES"))))
                   (response (make-request-response :data entity-synced)))
              (apply (orgtrello-proxy--standard-post-or-put-success-callback entity entities-adjacencies) (list response)))))))

(ert-deftest test-orgtrello-proxy--retrieve-state-of-card ()
  (should (equal org-trello--todo
                 (orgtrello-proxy--retrieve-state-of-card (orgtrello-hash-make-properties `((:keyword . ,org-trello--todo))))))
  (should (equal org-trello--todo
                 (orgtrello-proxy--retrieve-state-of-card (orgtrello-hash-make-properties `((:something-else))))))
  (should (equal :something-else
                 (orgtrello-proxy--retrieve-state-of-card (orgtrello-hash-make-properties `((:keyword . :something-else))))))
  (should (equal org-trello--todo
                 (orgtrello-proxy--retrieve-state-of-card (orgtrello-hash-empty-hash))))
  (should (equal org-trello--todo
                 (orgtrello-proxy--retrieve-state-of-card nil))))

(ert-deftest test-orgtrello-proxy--checks-before-sync-card ()
  (should (equal :ok
                 (orgtrello-proxy--checks-before-sync-card
                  (orgtrello-hash-make-properties `((:name . :name-so-ok)
                                                    (:keyword . :something-else))))))
  ;; missing name
  (should (string= "Cannot synchronize the card - missing mandatory name. Skip it..."
                   (orgtrello-proxy--checks-before-sync-card
                    (orgtrello-hash-make-properties `((:name)))))))

(ert-deftest test-orgtrello-proxy--checks-before-sync-checklist ()
  (should (string= "Cannot synchronize the checklist - missing mandatory name. Skip it..."
                   (orgtrello-proxy--checks-before-sync-checklist
                    (orgtrello-hash-make-properties `((:name)))
                    :card)))
  (should (string= "Cannot synchronize the checklist - the card must be synchronized first. Skip it..."
                   (orgtrello-proxy--checks-before-sync-checklist
                    (orgtrello-hash-make-properties `((:name . :checklist-name-so-ok)
                                                      (:keyword . :something-else)))
                    (orgtrello-hash-make-properties `((:id))))))
  (should (equal :ok
                 (orgtrello-proxy--checks-before-sync-checklist
                  (orgtrello-hash-make-properties `((:name . :checklist-name-so-ok)
                                                    (:keyword . :something-else)))
                  (orgtrello-hash-make-properties `((:id . "orgtrello-id-card-id-so-ok")
                                                    (:keyword . :something-else)))))))

(ert-deftest test-orgtrello-proxy-map-dispatch-delete ()
  (should (equal 'orgtrello-proxy--card-delete      (gethash org-trello--card-level orgtrello-proxy--map-fn-dispatch-delete)))
  (should (equal 'orgtrello-proxy--checklist-delete (gethash org-trello--checklist-level orgtrello-proxy--map-fn-dispatch-delete)))
  (should (equal 'orgtrello-proxy--item-delete      (gethash org-trello--item-level orgtrello-proxy--map-fn-dispatch-delete))))

(ert-deftest test-orgtrello-proxy--compute-delete-query-request ()
  (should (equal :res
                 (with-mock
                   (mock (orgtrello-proxy--compute-dispatch-fn :entity orgtrello-proxy--map-fn-dispatch-delete) => :res)
                   (orgtrello-proxy--compute-delete-query-request :entity)))))

(ert-deftest test-orgtrello-proxy--delete-entity-region ()
  (should (equal 'orgtrello-proxy--delete-card-region
                 (with-mock
                   (mock (orgtrello-data-entity-card-p :entity) => t)
                   (orgtrello-proxy--delete-entity-region :entity))))
  (should (equal 'orgtrello-proxy--delete-checkbox-checklist-region
                 (with-mock
                   (mock (orgtrello-data-entity-card-p :entity) => nil)
                   (mock (orgtrello-data-entity-checklist-p :entity) => t)
                   (orgtrello-proxy--delete-entity-region :entity))))
  (should (equal 'orgtrello-proxy--delete-checkbox-item-region
                 (with-mock
                   (mock (orgtrello-data-entity-card-p :entity) => nil)
                   (mock (orgtrello-data-entity-checklist-p :entity) => nil)
                   (mock (orgtrello-data-entity-item-p :entity) => t)
                   (orgtrello-proxy--delete-entity-region :entity)))))

(ert-deftest test-orgtrello-proxy--standard-delete-success-callback ()
  ;; card deleted!
  (should (string=
           "* card not to be touched
  - [ ] checklist not to be touched
    - [ ] item not to be touched
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card not to be touched
  - [ ] checklist not to be touched
    - [ ] item not to be touched
* TODO card and content to be deleted
:PROPERTIES:
:orgtrello-id: 55d07e8ada66fd9de074b82e
:END:
  description
  - [ ] checklist
    - [ ] item
"
            (let* ((entity (orgtrello-hash-make-properties `((:id . "55d07e8ada66fd9de074b82e")
                                                             (:buffername . ,(current-buffer))
                                                             (:level . 1)))))
              (apply (orgtrello-proxy--standard-delete-success-callback entity) (list :response-is-not-used))))))
  ;; checklist deleted!
  (should (string=
           "* card not to be touched
  - [ ] checklist not to be touched
    - [ ] item not to be touched
* TODO card not to be touched
:PROPERTIES:
:orgtrello-id: 55d07e8ada66fd9de074b82e
:orgtrello-local-checksum: 84ab4c1e2bb3b1579abba176f191bdd0da9c26afc918d3ece452ccd2137de09b
:END:
  description
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card not to be touched
  - [ ] checklist not to be touched
    - [ ] item not to be touched
* TODO card not to be touched
:PROPERTIES:
:orgtrello-id: 55d07e8ada66fd9de074b82e
:END:
  description
  - [ ] checklist and content to be deleted :PROPERTIES: {\"orgtrello-id\":\"44d07e8ada66fd9de074b82e\"}
    - [ ] item
"
            (let* ((entity (orgtrello-hash-make-properties `((:id . "44d07e8ada66fd9de074b82e")
                                                             (:buffername . ,(current-buffer))
                                                             (:level . 2)))))
              (apply (orgtrello-proxy--standard-delete-success-callback entity) (list :response-is-not-used))))))
  ;; item deleted!
  (should (string=
           "* card not to be touched
  - [ ] checklist not to be touched
    - [ ] item not to be touched
* TODO card not to be touched
:PROPERTIES:
:orgtrello-id: 55d07e8ada66fd9de074b82e
:END:
  description
  - [ ] checklist :PROPERTIES: {\"orgtrello-local-checksum\":\"b4dda9762d94c205a98abec2fb03fa04a409c75d03cc1cd66840177ce5abe0e4\"}
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card not to be touched
  - [ ] checklist not to be touched
    - [ ] item not to be touched
* TODO card not to be touched
:PROPERTIES:
:orgtrello-id: 55d07e8ada66fd9de074b82e
:END:
  description
  - [ ] checklist
    - [ ] item to be deleted :PROPERTIES: {\"orgtrello-id\":\"33d07e8ada66fd9de074b82e\"}
"
            (let* ((entity (orgtrello-hash-make-properties `((:id . "33d07e8ada66fd9de074b82e")
                                                             (:buffername . ,(current-buffer))
                                                             (:level . 3)))))
              (apply (orgtrello-proxy--standard-delete-success-callback entity) (list :response-is-not-used)))))))

(ert-deftest test-orgtrello-proxy--card-delete ()
  "Deal with the deletion query of a CARD-META."
  (should (equal :delete-card-done
                 (with-mock
                   (mock (orgtrello-data-entity-id :card-meta) => :id)
                   (mock (orgtrello-api-delete-card :id) => :delete-card-done)
                   (orgtrello-proxy--card-delete :card-meta)))))

(ert-deftest test-orgtrello-proxy--checklist-delete ()
  (should (equal :delete-checklist-done
                 (with-mock
                   (mock (orgtrello-data-entity-id :checklist-meta) => :id)
                   (mock (orgtrello-api-delete-checklist :id) => :delete-checklist-done)
                   (orgtrello-proxy--checklist-delete :checklist-meta)))))

(ert-deftest test-orgtrello-proxy--item-delete ()
  (should (equal :delete-item-done
                 (let ((item-meta (orgtrello-hash-make-properties `((:id . "item-id")
                                                                    (:parent . ,(orgtrello-hash-make-properties '((:id . "checklist-id"))))))))
                   (with-mock
                     (mock (orgtrello-api-delete-item "checklist-id" "item-id") => :delete-item-done)
                     (orgtrello-proxy--item-delete item-meta))))))

(ert-deftest test-orgtrello-proxy--delete-region ()
  (should (equal :delete-region-done
                 (with-mock
                   (mock (orgtrello-buffer-remove-overlays :start :end) => :remove-overlays-done)
                   (mock (delete-region :start :end) => :delete-region-done)
                   (orgtrello-proxy--delete-region :start :end)))))

(ert-deftest test-orgtrello-proxy--card ()
  (should (equal 'orgtrello-proxy--card      (gethash org-trello--card-level orgtrello-proxy--map-fn-dispatch-create-update)))
  (should (equal 'orgtrello-proxy--checklist (gethash org-trello--checklist-level orgtrello-proxy--map-fn-dispatch-create-update)))
  (should (equal 'orgtrello-proxy--item      (gethash org-trello--item-level orgtrello-proxy--map-fn-dispatch-create-update))))

(ert-deftest test-orgtrello-proxy--checklist ()
  (should (equal :checklist-query-add
                 (with-mock
                   (mock (orgtrello-api-add-checklist "card-id" :checklist-name :checklist-pos) => :checklist-query-add)
                   (orgtrello-proxy--checklist (orgtrello-hash-make-properties `((:id)
                                                                                 (:name . :checklist-name)
                                                                                 (:position . :checklist-pos)
                                                                                 (:parent . ,(orgtrello-hash-make-properties '((:id . "card-id"))))))))))
  (should (equal :checklist-query-update
                 (with-mock
                   (mock (orgtrello-api-update-checklist "checklist-id" :checklist-name :checklist-pos) => :checklist-query-update)
                   (orgtrello-proxy--checklist (orgtrello-hash-make-properties `((:id . "checklist-id")
                                                                                 (:name . :checklist-name)
                                                                                 (:position . :checklist-pos)
                                                                                 (:parent . ,(orgtrello-hash-make-properties '((:id . "card-id"))))))))))
  (should (equal :error-msg
                 (with-mock
                   (mock (orgtrello-data-parent :checklist-meta) => :card-meta)
                   (mock (orgtrello-proxy--checks-before-sync-checklist :checklist-meta :card-meta) => :error-msg)
                   (orgtrello-proxy--checklist :checklist-meta)))))

(ert-deftest test-orgtrello-proxy--compute-state ()
  (should (equal "complete" (orgtrello-proxy--compute-state org-trello--done)))
  (should (equal "incomplete" (orgtrello-proxy--compute-state "anything-else"))))

(ert-deftest test-orgtrello-proxy--compute-check ()
  (should (equal t   (orgtrello-proxy--compute-check org-trello--done)))
  (should (equal nil (orgtrello-proxy--compute-check "anything-else"))))

(ert-deftest test-orgtrello-proxy--checks-before-sync-item ()
  (should
   (equal "Cannot synchronize the item - missing mandatory name. Skip it..."
          (orgtrello-proxy--checks-before-sync-item
           (orgtrello-hash-make-properties '((:id . :item-id)))
           :checklist-meta
           :card-meta)))
  (should
   (equal "Cannot synchronize the item - the checklist must be synchronized first. Skip it..."
          (orgtrello-proxy--checks-before-sync-item
           (orgtrello-hash-make-properties '((:name . :item-name)))
           (orgtrello-hash-make-properties '((:id)))
           :card-meta)))
  (should
   (equal "Cannot synchronize the item - the card must be synchronized first. Skip it..."
          (orgtrello-proxy--checks-before-sync-item
           (orgtrello-hash-make-properties '((:name . :item-name)))
           (orgtrello-hash-make-properties '((:id . "checklist-id")))
           (orgtrello-hash-make-properties '((:id))))))
  (should
   (equal :ok
          (orgtrello-proxy--checks-before-sync-item
           (orgtrello-hash-make-properties '((:name . :item-name)))
           (orgtrello-hash-make-properties '((:id . "checklist-id")))
           (orgtrello-hash-make-properties '((:id . "id")))))))

(ert-deftest test-orgtrello-proxy--item ()
  (should (equal :query-item-update
                 (let* ((card-meta (orgtrello-hash-make-properties '((:id . "card-id"))))
                        (checklist-meta (orgtrello-hash-make-properties `((:id . "checklist-id")
                                                                          (:parent . ,card-meta))))
                        (item-meta (orgtrello-hash-make-properties `((:id . "item-id")
                                                                     (:name . :item-name)
                                                                     (:keyword . :item-kwd)
                                                                     (:position . :item-pos)
                                                                     (:parent . ,checklist-meta)))))
                   (with-mock
                     (mock (orgtrello-proxy--checks-before-sync-item item-meta checklist-meta card-meta) => :ok)
                     (mock (orgtrello-proxy--compute-state :item-kwd) => :item-state)
                     (mock (orgtrello-api-update-item "card-id"
                                                      "checklist-id"
                                                      "item-id"
                                                      :item-name
                                                      :item-state
                                                      :item-pos) => :query-item-update)
                     (orgtrello-proxy--item item-meta)))))
  (should (equal :query-item-add
                 (let* ((card-meta (orgtrello-hash-make-properties '((:id . "card-id"))))
                        (checklist-meta (orgtrello-hash-make-properties `((:id . "checklist-id")
                                                                          (:parent . ,card-meta))))
                        (item-meta (orgtrello-hash-make-properties `((:name . :item-name)
                                                                     (:keyword . :item-kwd)
                                                                     (:position . :item-pos)
                                                                     (:parent . ,checklist-meta)))))
                   (with-mock
                     (mock (orgtrello-proxy--checks-before-sync-item item-meta checklist-meta card-meta) => :ok)
                     (mock (orgtrello-proxy--compute-check :item-kwd) => :item-check)
                     (mock (orgtrello-api-add-items "checklist-id"
                                                    :item-name
                                                    :item-check
                                                    :item-pos) => :query-item-add)
                     (orgtrello-proxy--item item-meta)))))
  (should (equal :error-msg
                 (let* ((card-meta (orgtrello-hash-make-properties '((:id . "card-id"))))
                        (checklist-meta (orgtrello-hash-make-properties `((:id . "checklist-id")
                                                                          (:parent . ,card-meta))))
                        (item-meta (orgtrello-hash-make-properties `((:name . :item-name)
                                                                     (:parent . ,checklist-meta)))))
                   (with-mock
                     (mock (orgtrello-proxy--checks-before-sync-item item-meta checklist-meta card-meta) => :error-msg)
                     (orgtrello-proxy--item item-meta))))))

(ert-deftest test-orgtrello-proxy--compute-dispatch-fn ()
  (should (equal :result-with-card-fn
                 (let ((entity (orgtrello-hash-make-properties '((:level . :card-level)))))
                   (orgtrello-proxy--compute-dispatch-fn
                    entity
                    (orgtrello-hash-make-properties '((:card-level . (lambda (entity) :result-with-card-fn))
                                                      (:checklist-level . :checklist-fn)))))))
  (should (equal :result-with-checklist-fn
                 (let ((entity (orgtrello-hash-make-properties '((:level . :checklist-level)))))
                   (orgtrello-proxy--compute-dispatch-fn
                    entity
                    (orgtrello-hash-make-properties '((:card-level . :card-fn)
                                                      (:checklist-level . (lambda (checklist) :result-with-checklist-fn))))))))
  (should (string= "Your arborescence depth is too deep. We only support up to depth 3.
Level 1 - card
Level 2 - checklist
Level 3 - items"
                   (let ((entity (orgtrello-hash-make-properties '((:level . :unknown)))))
                     (orgtrello-proxy--compute-dispatch-fn
                      entity
                      (orgtrello-hash-make-properties '((:card-level . :card-fn)
                                                        (:checklist-level . :checklist-fn))))))))

(ert-deftest test-orgtrello-proxy--card ()
  (should (equal :error-msg
                 (with-mock
                   (mock (orgtrello-proxy--checks-before-sync-card :card-meta) => :error-msg)
                   (orgtrello-proxy--card :card-meta))))
  (should (equal :query-update-card
                 (with-mock
                   (mock (orgtrello-proxy--checks-before-sync-card :card-meta) => :ok)
                   (mock (orgtrello-proxy--retrieve-state-of-card :card-meta) => :card-kwd)
                   (mock (orgtrello-buffer-org-file-get-property :card-kwd) => :list-id)
                   (mock (orgtrello-data-entity-id :card-meta) => :card-id)
                   (mock (orgtrello-data-entity-name :card-meta) => :card-name)
                   (mock (orgtrello-data-entity-due :card-meta) => :card-due)
                   (mock (orgtrello-data-entity-description :card-meta) => :card-desc)
                   (mock (orgtrello-data-entity-member-ids :card-meta) => :card-user-ids-assigned)
                   (mock (orgtrello-data-entity-tags :card-meta) => :card-tags)
                   (mock (orgtrello-proxy--tags-to-labels :card-tags) => :card-labels)
                   (mock (orgtrello-data-entity-position :card-meta) => :card-pos)
                   (mock (orgtrello-api-move-card
                          :card-id
                          :list-id
                          :card-name
                          :card-due
                          :card-user-ids-assigned
                          :card-desc
                          :card-labels
                          :card-pos) => :query-update-card)
                   (orgtrello-proxy--card :card-meta))))
  (should (equal :query-add-card
                 (with-mock
                   (mock (orgtrello-proxy--checks-before-sync-card :card-meta) => :ok)
                   (mock (orgtrello-proxy--retrieve-state-of-card :card-meta) => :card-kwd)
                   (mock (orgtrello-buffer-org-file-get-property :card-kwd) => :list-id)
                   (mock (orgtrello-data-entity-id :card-meta) => nil)
                   (mock (orgtrello-data-entity-name :card-meta) => :card-name)
                   (mock (orgtrello-data-entity-due :card-meta) => :card-due)
                   (mock (orgtrello-data-entity-description :card-meta) => :card-desc)
                   (mock (orgtrello-data-entity-member-ids :card-meta) => :card-user-ids-assigned)
                   (mock (orgtrello-data-entity-tags :card-meta) => :card-tags)
                   (mock (orgtrello-proxy--tags-to-labels :card-tags) => :card-labels)
                   (mock (orgtrello-data-entity-position :card-meta) => :card-pos)
                   (mock (orgtrello-api-add-card
                          :card-name
                          :list-id
                          :card-due
                          :card-user-ids-assigned
                          :card-desc
                          :card-labels
                          :card-pos) => :query-add-card)
                   (orgtrello-proxy--card :card-meta)))))

(ert-deftest test-orgtrello-proxy--tags-to-labels ()
  (should (string= "a,b,c" (orgtrello-proxy--tags-to-labels ":a:b:c")))
  (should (string= "a,b,c" (orgtrello-proxy--tags-to-labels "a:b:c")))
  (should (string= "a," (orgtrello-proxy--tags-to-labels ":a:")))
  (should (string= "a," (orgtrello-proxy--tags-to-labels "a:")))
  (should (string= ""  (orgtrello-proxy--tags-to-labels nil))))

(ert-deftest test-orgtrello-proxy--compute-sync-query-request ()
  (should (equal :res
                 (with-mock
                   (mock (orgtrello-proxy--compute-dispatch-fn :entity
                                                               orgtrello-proxy--map-fn-dispatch-create-update) => :res)
                   (orgtrello-proxy--compute-sync-query-request :entity)))))

(ert-deftest test-orgtrello-proxy--cleanup-meta ()
  ;; should clean up since it's not an id
  (should (equal :done
                 (with-mock
                   (mock (orgtrello-data-entity-id :entity) => nil)
                   (mock (orgtrello-cbx-org-delete-property org-trello--label-key-id) => :done)
                   (orgtrello-proxy--cleanup-meta :entity))))
  ;; should not clean up since it's an id
  (should-not (with-mock
                (mock (orgtrello-data-entity-id :entity) => :id)
                (orgtrello-proxy--cleanup-meta :entity))))

(ert-deftest test-orgtrello-proxy-delete-entity ()
  (should (equal :not-a-query
                 (with-mock
                   (mock (orgtrello-proxy--compute-delete-query-request :entity) => :not-a-query)
                   (mock (hash-table-p :not-a-query) => nil)
                   (mock (orgtrello-log-msg orgtrello-log-error :not-a-query) => :not-a-query)
                   (orgtrello-proxy-delete-entity :entity))))
  (should (equal :result
                 (with-mock
                   (mock (orgtrello-proxy--compute-delete-query-request :entity) => :query-map)
                   (mock (hash-table-p :query-map) => t)
                   (mock (orgtrello-proxy--standard-delete-success-callback :entity) => :success-cbk)
                   (mock (orgtrello-query-http-trello :query-map
                                                      nil
                                                      :success-cbk
                                                      *) => :result)
                   (orgtrello-proxy-delete-entity :entity)))))

(ert-deftest test-orgtrello-proxy-sync-entity ()
  ;; not a query so fails
  (should (equal :not-a-query
                 (with-mock
                   (mock (orgtrello-proxy--compute-sync-query-request :entity) => :not-a-query)
                   (mock (hash-table-p :not-a-query) => nil)
                   (mock (orgtrello-proxy--cleanup-meta :entity) => :done)
                   (mock (orgtrello-log-msg orgtrello-log-error :not-a-query) => :not-a-query)
                   (orgtrello-proxy-sync-entity :entity :entities-adjacencies))))
  ;; success call to api
  (should (equal :result
                 (with-mock
                   (mock (orgtrello-proxy--compute-sync-query-request :entity) => :query-map)
                   (mock (hash-table-p :query-map) => t)
                   (mock (orgtrello-proxy--standard-post-or-put-success-callback :entity :entities-adjacencies) => :success-cbk)
                   (mock (orgtrello-query-http-trello :query-map
                                                      nil
                                                      :success-cbk
                                                      *) => :result)
                   (orgtrello-proxy-sync-entity :entity :entities-adjacencies)))))

(ert-deftest test-orgtrello-proxy--delete-card-region ()
  (should
   (string= "* card not deleted
"
            (orgtrello-tests-with-temp-buffer-and-return-buffer-content
             "* card not deleted
* card to delete
  - [ ] checklist
    - [ ] item"
             (orgtrello-proxy--delete-card-region)
             -1)))
  (should
   (string= "* card to delete
  - [ ] checklist
    - [ ] item"
            (orgtrello-tests-with-temp-buffer-and-return-buffer-content
             "* card not deleted
* card to delete
  - [ ] checklist
    - [ ] item"
             (orgtrello-proxy--delete-card-region)
             -4))))

(ert-deftest test-orgtrello-proxy--delete-checkbox-checklist-region ()
  ;; destroy the checklist and children up to the buffer's end
  (should (string= "* card 1
* card 2
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card 1
* card 2
  - [ ] checklist
    - [ ] item"
                    (orgtrello-proxy--delete-checkbox-checklist-region)
                    -1)))
  ;; will delete the checklist and its children up to the next checklist
  (should (string= "* card 1
* card 2
  - [ ] checklist 2
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card 1
* card 2
  - [ ] checklist 1
    - [ ] item
  - [ ] checklist 2
"
                    (orgtrello-proxy--delete-checkbox-checklist-region)
                    -3)))

  (ert-deftest test-orgtrello-proxy--delete-checkbox-item-region ()
    (should (string= "* card 1
* card 2
  - [ ] checklist
"
                     (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                      "* card 1
* card 2
  - [ ] checklist
    - [ ] item
"
                      (orgtrello-proxy--delete-checkbox-item-region)

                      -1)))))

(ert-deftest test-orgtrello-proxy--execute-async-computations ()
  (should (equal '(deferred:$
                    (deferred:parallel (+ 1 1) (+ 1 2))
                    (deferred:error it (lambda nil (orgtrello-log-msg orgtrello-log-error :log-ko)))
                    (deferred:nextc it (lambda nil (orgtrello-log-msg orgtrello-log-debug :log-ok))))
                 (orgtrello-proxy--execute-async-computations '((+ 1 1) (+ 1 2)) :log-ok :log-ko))))

(ert-deftest test-orgtrello-proxy-execute-async-computations ()
  (should (equal 11
                 (with-mock
                   (mock (orgtrello-proxy--execute-async-computations :1 :2 :3) => '(+ 1 10))
                   (orgtrello-proxy-execute-async-computations :1 :2 :3)))))

(provide 'org-trello-proxy-test)
;;; org-trello-proxy-test.el ends here
