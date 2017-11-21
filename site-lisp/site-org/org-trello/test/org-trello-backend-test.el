(require 'org-trello-backend)
(require 'dash-functional)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-backend-add-entity-to-entities ()
  (should (let ((entity (orgtrello-hash-make-properties '((:id . :entity-id) (:prop0 . :prop0-val)))))
            (orgtrello-tests-hash-equal
             (orgtrello-hash-make-properties `((:entity-id . ,entity)))
             (let ((entities (orgtrello-hash-empty-hash)))
               (orgtrello-backend-add-entity-to-entities entity entities)))))
  ;; add to non empty map
  (should (let ((entity (orgtrello-hash-make-properties '((:id . :entity-id) (:prop0 . :prop0-val))))
                (entity2 (orgtrello-hash-make-properties '((:id . :entity-id2) (:prop1 . :prop1-val)))))
            (orgtrello-tests-hash-equal
             (orgtrello-hash-make-properties `((:entity-id . ,entity) (:entity-id2 . ,entity2)))
             (let ((entities (orgtrello-hash-make-properties `((:entity-id2 . ,entity2)))))
               (orgtrello-backend-add-entity-to-entities entity entities)))))
  ;; update existing entity in place
  (should (let ((entity-v1 (orgtrello-hash-make-properties '((:id . :entity-id) (:prop0 . :val0))))
                (entity-v2 (orgtrello-hash-make-properties '((:id . :entity-id) (:prop0 . :val1))))
                (entity2 (orgtrello-hash-make-properties '((:id . :entity-id2) (:prop1 . :prop1-val)))))
            (orgtrello-tests-hash-equal
             (orgtrello-hash-make-properties `((:entity-id . ,entity-v2) (:entity-id2 . ,entity2)))
             (let ((entities (orgtrello-hash-make-properties `((:entity-id . ,entity-v1) (:entity-id2 . ,entity2)))))
               (orgtrello-backend-add-entity-to-entities entity-v2 entities))))))

(ert-deftest test-orgtrello-backend--add-entity-to-adjacency ()
  ;; empty adjacency list
  (should (orgtrello-tests-hash-equal
           (orgtrello-hash-make-properties '((:parent-id . (:entity-id))))
           (let ((entity (orgtrello-hash-make-properties '((:id . :entity-id))))
                 (parent-entity (orgtrello-hash-make-properties '((:id . :parent-id))))
                 (adjacency (orgtrello-hash-empty-hash)))
             (orgtrello-backend--add-entity-to-adjacency entity parent-entity adjacency))))
  ;; add to existing list
  (should (orgtrello-tests-hash-equal
           (orgtrello-hash-make-properties '((:parent-id . (:entity-id2 :entity-id))))
           (let ((entity (orgtrello-hash-make-properties '((:id . :entity-id))))
                 (parent-entity (orgtrello-hash-make-properties '((:id . :parent-id))))
                 (adjacencies (orgtrello-hash-make-properties '((:parent-id . (:entity-id2))))))
             (orgtrello-backend--add-entity-to-adjacency entity parent-entity adjacencies)))))

(ert-deftest test-orgtrello-backend--compute-items-from-checklist ()
  (should
   (-every? (-partial #'eq t)
            (-let* (;; given
                    (item-0 (orgtrello-hash-make-properties '((:id . :item-id-0)
                                                              (:position . 1))))
                    (item-1 (orgtrello-hash-make-properties '((:id . :item-id-1)
                                                              (:position . 2))))
                    (item-2 (orgtrello-hash-make-properties '((:id . :item-id-2)
                                                              (:position . 0))))
                    (checklist (orgtrello-hash-make-properties `((:id . :checklist-id)
                                                                 (:items . (,item-1
                                                                            ,item-0
                                                                            ,item-2)))))
                    ;; when
                    ((actual-output-entities actual-output-adjacencies)
                     (orgtrello-backend--compute-items-from-checklist
                      checklist
                      (orgtrello-hash-make-properties `((:checklist-id . ,checklist)))
                      (orgtrello-hash-empty-hash)))
                    ;; then
                    (expected-output-entities
                     (orgtrello-hash-make-properties `((:checklist-id . ,checklist)
                                                       (:item-id-0 . ,item-0)
                                                       (:item-id-1 . ,item-1)
                                                       (:item-id-2 . ,item-2))))
                    (expected-output-adjacencies
                     (orgtrello-hash-make-properties '((:checklist-id :item-id-2
                                                                      :item-id-0
                                                                      :item-id-1)))))
              (list
               (orgtrello-tests-hash-equal expected-output-entities actual-output-entities)
               (orgtrello-tests-hash-equal expected-output-adjacencies actual-output-adjacencies))))))

(ert-deftest test-orgtrello-backend--put-entities-with-adjacency ()
  (should
   (equal (list :updated-entities-map :updated-adjacencies-map)
          (with-mock
            (mock (orgtrello-backend-add-entity-to-entities :current-entity :entities-map) => :updated-entities-map)
            (mock (orgtrello-backend--add-entity-to-adjacency :current-entity
                                                              :parent-entity
                                                              :adjacency-map) => :updated-adjacencies-map)
            (let ((meta (orgtrello-hash-make-properties '((:current . :current-entity)
                                                          (:parent . :parent-entity)
                                                          (:grand-parent . :is-not-used)))))
              (orgtrello-backend--put-entities-with-adjacency meta :entities-map :adjacency-map))))))

(ert-deftest test-orgtrello-backend--compute-org-trello-checklists-from-card ()
  (should
   (-every? (-partial #'eq t)
            (-let* ((item-0 (orgtrello-hash-make-properties '((:id . :item-id-0)
                                                              (:position . 1))))
                    (item-1 (orgtrello-hash-make-properties '((:id . :item-id-1)
                                                              (:position . 3))))
                    (item-2 (orgtrello-hash-make-properties '((:id . :item-id-2)
                                                              (:position . 2))))
                    (checklist-1 (orgtrello-hash-make-properties `((:id . :checklist-id-1)
                                                                   (:position . 0)
                                                                   (:items . (,item-0
                                                                              ,item-1)))))
                    (checklist-2 (orgtrello-hash-make-properties `((:id . :checklist-id-2)
                                                                   (:position . 1)
                                                                   (:items . (,item-2)))))
                    (checklist-3 (orgtrello-hash-make-properties '((:id . :checklist-id-3)
                                                                   (:position . 2)
                                                                   (:items . ()))))
                    (trello-card (orgtrello-hash-make-properties `((:id . :card-id)
                                                                   (:checklists . (,checklist-1
                                                                                   ,checklist-2
                                                                                   ,checklist-3)))))
                    (ents (orgtrello-hash-empty-hash))
                    (adjs (orgtrello-hash-empty-hash))
                    ((actual-output-entities actual-output-adjacencies)
                     (orgtrello-backend--compute-org-trello-checklists-from-card trello-card ents adjs))
                    (expected-output-entities
                     (orgtrello-hash-make-properties `((:checklist-id-1 . ,checklist-1)
                                                       (:item-id-0 . ,item-0)
                                                       (:item-id-1 . ,item-1)
                                                       (:checklist-id-2 . ,checklist-2)
                                                       (:item-id-2 . ,item-2)
                                                       (:checklist-id-3 . ,checklist-3))))
                    (expected-output-adjacencies
                     (orgtrello-hash-make-properties '((:card-id :checklist-id-1 :checklist-id-2 :checklist-id-3)
                                                       (:checklist-id-1 :item-id-0 :item-id-1)
                                                       (:checklist-id-2 :item-id-2)))))
              (list
               (orgtrello-tests-hash-equal expected-output-entities actual-output-entities)
               (orgtrello-tests-hash-equal expected-output-adjacencies actual-output-adjacencies))))))

(ert-deftest test-orgtrello-backend-compute-org-trello-card-from ()
  (-every? (-partial #'eq t)
           (-let* ((item-0 (orgtrello-hash-make-properties '((:id . :item-id-0)
                                                             (:position . 1))))
                   (item-1 (orgtrello-hash-make-properties '((:id . :item-id-1)
                                                             (:position . 3))))
                   (item-2 (orgtrello-hash-make-properties '((:id . :item-id-2)
                                                             (:position . 2))))
                   (checklist-1 (orgtrello-hash-make-properties `((:id . :checklist-id-1)
                                                                  (:position . 0)
                                                                  (:items . (,item-0
                                                                             ,item-1)))))
                   (checklist-2 (orgtrello-hash-make-properties `((:id . :checklist-id-2)
                                                                  (:position . 1)
                                                                  (:items . (,item-2)))))
                   (checklist-3 (orgtrello-hash-make-properties '((:id . :checklist-id-3)
                                                                  (:position . 2)
                                                                  (:items . ()))))
                   (trello-card-1 (orgtrello-hash-make-properties `((:id . :card-id-1)
                                                                    (:checklists . (,checklist-1
                                                                                    ,checklist-2
                                                                                    ,checklist-3)))))
                   (trello-card-2 (orgtrello-hash-make-properties '((:id . :card-id-2)
                                                                    (:checklists))))
                   ((actual-output-entities actual-output-adjacencies )
                    (orgtrello-backend-compute-org-trello-card-from `(,trello-card-1 ,trello-card-2)))
                   (expected-output-entities
                    (orgtrello-hash-make-properties `((:checklist-id-1 . ,checklist-1)
                                                      (:item-id-0 . ,item-0)
                                                      (:item-id-1 . ,item-1)
                                                      (:checklist-id-2 . ,checklist-2)
                                                      (:item-id-2 . ,item-2)
                                                      (:checklist-id-3 . ,checklist-3)
                                                      (:card-id-1 . ,trello-card-1)
                                                      (:card-id-2 . ,trello-card-2))))
                   (expected-output-adjacencies
                    (orgtrello-hash-make-properties '((:card-id-1 :checklist-id-1 :checklist-id-2 :checklist-id-3)
                                                      (:checklist-id-1 :item-id-0 :item-id-1)
                                                      (:checklist-id-2 :item-id-2)))))
             (list
              (orgtrello-tests-hash-equal expected-output-entities actual-output-entities)
              (orgtrello-tests-hash-equal expected-output-adjacencies actual-output-adjacencies)))))

(provide 'org-trello-backend-test)
;;; org-trello-backend-test.el ends here
