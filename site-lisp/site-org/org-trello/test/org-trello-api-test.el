(require 'org-trello-api)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-api-make-query ()
  (should (equal :some-method (gethash :method (orgtrello-api-make-query :some-method :some-uri))))
  (should (equal :some-uri    (gethash :uri    (orgtrello-api-make-query :some-method :some-uri))))
  (should (equal nil          (gethash :params (orgtrello-api-make-query :some-method :some-uri)))))

(ert-deftest test-orgtrello-api-get-boards ()
  (should (equal "GET"                 (gethash :method (orgtrello-api-get-boards))))
  (should (equal "/members/me/boards"  (gethash :uri    (orgtrello-api-get-boards))))
  (should (equal '(("lists" . "open")) (gethash :params (orgtrello-api-get-boards))))

  (should (equal "GET"                                     (gethash :method (orgtrello-api-get-boards "open"))))
  (should (equal "/members/me/boards"                      (gethash :uri    (orgtrello-api-get-boards "open"))))
  (should (equal '(("filter" . "open") ("lists" . "open")) (gethash :params (orgtrello-api-get-boards "open")))))

(ert-deftest test-orgtrello-api-get-board ()
  (should (equal "GET"                                                (gethash :method (orgtrello-api-get-board :id))))
  (should (equal "/boards/:id"                                        (gethash :uri    (orgtrello-api-get-board :id))))
  (should (equal '(("memberships" . "active")
                   ("memberships_member" . "true")
                   ("lists" . "open")
                   ("fields" . "name,memberships,closed")
                   ("labels" . "all")
                   ("label_fields" . "name,color"))
                 (gethash :params (orgtrello-api-get-board :id)))))

(ert-deftest test-orgtrello-api-get-cards ()
  (should (equal "GET"                                                                                                        (gethash :method (orgtrello-api-get-cards :board-id))))
  (should (equal "/boards/:board-id/cards"                                                                                    (gethash :uri    (orgtrello-api-get-cards :board-id))))
  (should (equal '(("actions" . "commentCard") ("fields" . "closed,desc,due,idBoard,idChecklists,idList,idMembers,name,pos")) (gethash :params (orgtrello-api-get-cards :board-id)))))

(ert-deftest test-orgtrello-api-get-full-cards ()
  (should (equal "GET"
                 (gethash :method (orgtrello-api-get-full-cards :board-id))))
  (should (equal "/boards/:board-id/cards"
                 (gethash :uri    (orgtrello-api-get-full-cards :board-id))))
  (should (equal '(("actions" . "commentCard")
                   ("checklists" . "all") ("filter" . "open")
                   ("fields" . "closed,desc,due,idBoard,idList,idMembers,labels,name,pos"))
                 (gethash :params (orgtrello-api-get-full-cards :board-id)))))

(ert-deftest test-orgtrello-api-get-full-card ()
  (should (equal "GET"
                 (gethash :method (orgtrello-api-get-full-card :card-id))))
  (should (equal "/cards/:card-id"
                 (gethash :uri    (orgtrello-api-get-full-card :card-id))))
  (should (equal '(("actions" . "commentCard")
                   ("action_fields" . "data,date")
                   ("checklists" . "all")
                   ("action_memberCreator_fields" . "username")
                   ("fields" . "closed,dateLastActivity,desc,due,idList,idMembers,labels,name,pos"))
                 (gethash :params (orgtrello-api-get-full-card :card-id)))))

(ert-deftest test-orgtrello-api-get-archived-cards ()
  (should (equal "GET"
                 (gethash :method (orgtrello-api-get-archived-cards :board-id))))
  (should (equal "/boards/:board-id/cards"
                 (gethash :uri    (orgtrello-api-get-archived-cards :board-id))))
  (should (equal '(("filter" . "closed")
                   ("fields" . "closed,desc,due,idBoard,idList,idMembers,labels,name,pos"))
                 (gethash :params (orgtrello-api-get-archived-cards :board-id)))))

(ert-deftest test-orgtrello-api-get-card ()
  (should (equal "GET"                                                                                                  (gethash :method (orgtrello-api-get-card :card-id))))
  (should (equal "/cards/:card-id"                                                                                      (gethash :uri    (orgtrello-api-get-card :card-id))))
  (should (equal '(("actions" . "commentCard")
                   ("action_fields" . "data")
                   ("action_memberCreator_fields" . "username")
                   ("fields" . "closed,dateLastActivity,desc,due,idChecklists,idList,idMembers,labels,name,pos"))
                 (gethash :params (orgtrello-api-get-card :card-id)))))

(ert-deftest test-orgtrello-api-delete-card ()
  (should (equal "DELETE"           (gethash :method (orgtrello-api-delete-card :card-id))))
  (should (equal "/cards/:card-id" (gethash :uri    (orgtrello-api-delete-card :card-id))))
  (should (equal nil               (gethash :params (orgtrello-api-delete-card :card-id)))))

(ert-deftest test-orgtrello-api-close-list ()
  (should (equal "PUT"                    (gethash :method (orgtrello-api-close-list :list-id))))
  (should (equal "/lists/:list-id/closed" (gethash :uri    (orgtrello-api-close-list :list-id))))
  (should (equal '(("value" . "true"))       (gethash :params (orgtrello-api-close-list :list-id)))))

(ert-deftest test-orgtrello-api-open-list ()
  (should (equal "PUT"                    (gethash :method (orgtrello-api-open-list :list-id))))
  (should (equal "/lists/:list-id/closed" (gethash :uri    (orgtrello-api-open-list :list-id))))
  (should (equal '(("value" . "false"))     (gethash :params (orgtrello-api-open-list :list-id)))))

(ert-deftest test-orgtrello-api-add-list ()
  (should (equal "POST"                      (gethash :method (orgtrello-api-add-list "list-name" "board-id"))))
  (should (equal "/lists/"                   (gethash :uri    (orgtrello-api-add-list "list-name" "board-id"))))
  (should (equal '(("name" . "list-name")
                   ("idBoard" . "board-id")) (gethash :params (orgtrello-api-add-list "list-name" "board-id")))))

(ert-deftest test-orgtrello-api-add-card ()
  (should (equal "POST"                                                              (gethash :method (orgtrello-api-add-card :name-card :id-list "due-date"))))
  (should (equal "/cards/"                                                           (gethash :uri    (orgtrello-api-add-card :name-card :id-list "due-date"))))
  (should (equal '(("due" . "due-date") ("name" . :name-card) ("idList" . :id-list)) (gethash :params (orgtrello-api-add-card :name-card :id-list "due-date"))))
  (should (equal "POST"                                                              (gethash :method (orgtrello-api-add-card :name-card :id-list "due-date" "idmember0,idmember1"))))
  (should (equal "/cards/"                                                           (gethash :uri    (orgtrello-api-add-card :name-card :id-list "due-date" "idmember0,idmember1"))))
  (should (equal '(("due" . "due-date") ("idMembers" . "idmember0,idmember1") ("name" . :name-card) ("idList" . :id-list))
                 (gethash :params (orgtrello-api-add-card :name-card :id-list "due-date" "idmember0,idmember1"))))
  (should (equal "POST"                                                                                                    (gethash :method (orgtrello-api-add-card :name-card :id-list nil nil :description))))
  (should (equal "/cards/"                                                                                                 (gethash :uri    (orgtrello-api-add-card :name-card :id-list nil nil :description))))
  (should (equal '(("desc" . :description) ("name" . :name-card) ("idList" . :id-list))                                    (gethash :params (orgtrello-api-add-card :name-card :id-list nil nil :description))))
  (should (equal "POST"                                                              (gethash :method (orgtrello-api-add-card :name-card :id-list nil nil nil :labels))))
  (should (equal "/cards/"                                                           (gethash :uri    (orgtrello-api-add-card :name-card :id-list nil nil nil :labels))))
  (should (equal '(("labels" . :labels) ("name" . :name-card) ("idList" . :id-list)) (gethash :params (orgtrello-api-add-card :name-card :id-list nil nil nil :labels)))))

(ert-deftest test-orgtrello-api-move-card ()
  (should (equal "PUT"                                             (gethash :method (orgtrello-api-move-card :id-card :id-list "name-card"))))
  (should (equal "/cards/:id-card"                                 (gethash :uri    (orgtrello-api-move-card :id-card :id-list "name-card"))))
  (should (equal '(("due". "") ("name"   . "name-card") ("idList" . :id-list)) (gethash :params (orgtrello-api-move-card :id-card :id-list "name-card"))))

  (should (equal "PUT"                                     (gethash :method (orgtrello-api-move-card :id-card :id-list :name))))
  (should (equal "/cards/:id-card"                         (gethash :uri    (orgtrello-api-move-card :id-card :id-list :name))))
  (should (equal '(("due". "") ("name" . :name) ("idList" . :id-list)) (gethash :params (orgtrello-api-move-card :id-card :id-list :name))))

  (should (equal "PUT"                    (gethash :method (orgtrello-api-move-card :id-card :id-list))))
  (should (equal "/cards/:id-card"        (gethash :uri    (orgtrello-api-move-card :id-card :id-list))))
  (should (equal '(("due" . "") ("idList" . :id-list)) (gethash :params (orgtrello-api-move-card :id-card :id-list))))

  (should (equal "PUT"                                        (gethash :method (orgtrello-api-move-card :id-card :id-list nil :due-date))))
  (should (equal "/cards/:id-card"                            (gethash :uri    (orgtrello-api-move-card :id-card :id-list nil :due-date))))
  (should (equal '(("due" . :due-date) ("idList" . :id-list)) (gethash :params (orgtrello-api-move-card :id-card :id-list nil :due-date))))

  (should (equal "PUT"                                                         (gethash :method (orgtrello-api-move-card :id-card :id-list :name :due-date))))
  (should (equal "/cards/:id-card"                                             (gethash :uri    (orgtrello-api-move-card :id-card :id-list :name :due-date))))
  (should (equal '(("due" . :due-date) ("name" . :name) ("idList" . :id-list)) (gethash :params (orgtrello-api-move-card :id-card :id-list :name :due-date))))

  (should (equal "PUT"                                                                                 (gethash :method (orgtrello-api-move-card :id-card :id-list "name-card" nil "idmember0,idmember1"))))
  (should (equal "/cards/:id-card"                                                                     (gethash :uri    (orgtrello-api-move-card :id-card :id-list "name-card" nil "idmember0,idmember1"))))
  (should (equal '(("due". "") ("idMembers" . "idmember0,idmember1") ("name" . "name-card") ("idList" . :id-list)) (gethash :params (orgtrello-api-move-card :id-card :id-list "name-card" nil "idmember0,idmember1"))))

  (should (equal "PUT"                                            (gethash :method (orgtrello-api-move-card :id-card :id-list nil nil nil :description nil))))
  (should (equal "/cards/:id-card"                                (gethash :uri    (orgtrello-api-move-card :id-card :id-list nil nil nil :description nil))))
  (should (equal '(("desc" . :description) ("due" . "") ("idList" . :id-list)) (gethash :params (orgtrello-api-move-card :id-card :id-list nil nil nil :description nil)))))

(ert-deftest test-orgtrello-api-add-checklist ()
  (should (equal "POST"                                         (gethash :method (orgtrello-api-add-checklist "id-card" "name-checklist" "pos"))))
  (should (equal "/cards/id-card/checklists"                    (gethash :uri    (orgtrello-api-add-checklist "id-card" "name-checklist" "pos"))))
  (should (equal '(("name" . "name-checklist") ("pos" . "pos")) (gethash :params (orgtrello-api-add-checklist "id-card" "name-checklist" "pos")))))

(ert-deftest test-orgtrello-api-update-checklist ()
  (should (equal "PUT"                                          (gethash :method (orgtrello-api-update-checklist :id-checklist "name-checklist" "pos"))))
  (should (equal "/checklists/:id-checklist"                    (gethash :uri    (orgtrello-api-update-checklist :id-checklist "name-checklist" "pos"))))
  (should (equal '(("name" . "name-checklist") ("pos" . "pos")) (gethash :params (orgtrello-api-update-checklist :id-checklist "name-checklist" "pos")))))

(ert-deftest test-orgtrello-api-delete-checklist ()
  (should (equal "DELETE"                    (gethash :method (orgtrello-api-delete-checklist :id-checklist))))
  (should (equal "/checklists/:id-checklist" (gethash :uri    (orgtrello-api-delete-checklist :id-checklist))))
  (should (equal nil                         (gethash :params (orgtrello-api-delete-checklist :id-checklist)))))

(ert-deftest test-orgtrello-api-get-checklist ()
  (should (equal "GET"                                                                     (gethash :method (orgtrello-api-get-checklist :checklist-id))))
  (should (equal "/checklists/:checklist-id"                                               (gethash :uri    (orgtrello-api-get-checklist :checklist-id))))
  (should (equal '(("fields" . "name,pos,idCard") ("checkItem_fields" . "name,pos,state")) (gethash :params (orgtrello-api-get-checklist :checklist-id))))

  (should (equal '(("checkItems" . "none") ("fields" . "name,pos,idCard") ("checkItem_fields" . "name,pos,state"))
                 (gethash :params (orgtrello-api-get-checklist :checklist-id 'no-items)))))

(ert-deftest test-orgtrello-api-add-items ()
  (should (equal "POST"                                     (gethash :method (orgtrello-api-add-items :checklist-id "item-name" t))))
  (should (equal "/checklists/:checklist-id/checkItems"     (gethash :uri    (orgtrello-api-add-items :checklist-id "item-name" t))))
  (should (equal '(("checked" . t) ("name"  . "item-name")) (gethash :params (orgtrello-api-add-items :checklist-id "item-name" t))))

  (should (equal "POST"                                 (gethash :method (orgtrello-api-add-items :checklist-id "item-name"))))
  (should (equal "/checklists/:checklist-id/checkItems" (gethash :uri    (orgtrello-api-add-items :checklist-id "item-name"))))
  (should (equal '(("name"  . "item-name"))             (gethash :params (orgtrello-api-add-items :checklist-id "item-name"))))

  (should (equal "POST"                                 (gethash :method (orgtrello-api-add-items :checklist-id "item-name" nil))))
  (should (equal "/checklists/:checklist-id/checkItems" (gethash :uri    (orgtrello-api-add-items :checklist-id "item-name" nil))))
  (should (equal '(("name"  . "item-name"))             (gethash :params (orgtrello-api-add-items :checklist-id "item-name" nil)))))

(ert-deftest test-orgtrello-api-update-item ()
  (should (equal "PUT"                                                        (gethash :method (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name "incomplete"))))
  (should (equal "/cards/:card-id/checklist/:checklist-id/checkItem/:item-id" (gethash :uri    (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name "incomplete"))))
  (should (equal '(("state" ."incomplete") ("name"  . :item-name))            (gethash :params (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name "incomplete"))))

  (should (equal "PUT"                                                        (gethash :method (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name))))
  (should (equal "/cards/:card-id/checklist/:checklist-id/checkItem/:item-id" (gethash :uri    (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name))))
  (should (equal '(("name"  . :item-name))                                    (gethash :params (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name))))

  (should (equal "PUT"                                                        (gethash :method (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name nil))))
  (should (equal "/cards/:card-id/checklist/:checklist-id/checkItem/:item-id" (gethash :uri    (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name nil))))
  (should (equal '(("name"  . :item-name))                                    (gethash :params (orgtrello-api-update-item :card-id :checklist-id :item-id :item-name nil)))))

(ert-deftest test-orgtrello-api-delete-item ()
  (should (equal "DELETE"                                        (gethash :method (orgtrello-api-delete-item :checklist-id :item-id))))
  (should (equal "/checklists/:checklist-id/checkItems/:item-id" (gethash :uri    (orgtrello-api-delete-item :checklist-id :item-id)))))

(ert-deftest test-orgtrello-api-get-item ()
  (should (equal "GET"                                           (gethash :method (orgtrello-api-get-item :checklist-id :item-id))))
  (should (equal "/checklists/:checklist-id/checkItems/:item-id" (gethash :uri    (orgtrello-api-get-item :checklist-id :item-id))))
  (should (equal '(("fields" . "name,pos,state"))                (gethash :params (orgtrello-api-get-item :checklist-id :item-id)))))

(ert-deftest test-orgtrello-api-get-me ()
  (should (equal "GET"         (gethash :method (orgtrello-api-get-me))))
  (should (equal "/members/me" (gethash :uri (orgtrello-api-get-me)))))

(ert-deftest test-orgtrello-api--deal-with-optional-value ()
  (should (equal nil                    (orgtrello-api--deal-with-optional-value nil nil nil)))
  (should (equal nil                    (orgtrello-api--deal-with-optional-value nil :a nil)))
  (should (equal :existing-list         (orgtrello-api--deal-with-optional-value nil :a :existing-list)))
  (should (equal :existing-list         (orgtrello-api--deal-with-optional-value nil nil :existing-list)))
  (should (equal '(:value-a)            (orgtrello-api--deal-with-optional-value :a :value-a nil)))
  (should (equal '(:value-a :value-b)   (orgtrello-api--deal-with-optional-value :a :value-a '(:value-b))))
  (should (equal '(nil :value-b) (orgtrello-api--deal-with-optional-value :a nil '(:value-b)))))

(ert-deftest test-orgtrello-api--deal-with-optional-values ()
  (should (equal nil                    (orgtrello-api--deal-with-optional-values '((nil . nil)) nil)))
  (should (equal nil                    (orgtrello-api--deal-with-optional-values '((nil . :a)) nil)))
  (should (equal :existing-list         (orgtrello-api--deal-with-optional-values '((nil . :a)) :existing-list)))
  (should (equal :existing-list         (orgtrello-api--deal-with-optional-values '((nil . nil)) :existing-list)))

  (should (equal '(:value-a)            (orgtrello-api--deal-with-optional-values '((:a . :value-a)) nil)))
  (should (equal '(:value-a :value-b)   (orgtrello-api--deal-with-optional-values '((:a . :value-a)) '(:value-b))))
  (should (equal '(nil :value-b)        (orgtrello-api--deal-with-optional-values '((:a . nil)) '(:value-b))))

  (should (equal nil                           (orgtrello-api--deal-with-optional-values '((nil . nil) (nil . nil)) nil)))
  (should (equal nil                           (orgtrello-api--deal-with-optional-values '((nil . :a)  (nil . :a)) nil)))
  (should (equal :existing-list                (orgtrello-api--deal-with-optional-values '((nil . :a) (nil . :a)) :existing-list)))
  (should (equal :existing-list                (orgtrello-api--deal-with-optional-values '((nil . nil) (nil . nil)) :existing-list)))

  (should (equal '(:value-c :value-a)          (orgtrello-api--deal-with-optional-values '((:a . :value-a) (:c . :value-c)) nil)))
  (should (equal '(:value-c :value-a :value-b) (orgtrello-api--deal-with-optional-values '((:a . :value-a) (:c . :value-c)) '(:value-b))))
  (should (equal '(nil nil :value-b)           (orgtrello-api--deal-with-optional-values '((:a . nil) (:c . nil)) '(:value-b)))))

(ert-deftest test-orgtrello-api-add-board ()
  (should (equal "POST"                      (gethash :method (orgtrello-api-add-board ":some-board"))))
  (should (equal "/boards"                   (gethash :uri    (orgtrello-api-add-board ":some-board"))))
  (should (equal '(("name" . ":some-board")) (gethash :params (orgtrello-api-add-board ":some-board"))))

  (should (equal "POST"                           (gethash :method (orgtrello-api-add-board "some-board" "some-description"))))
  (should (equal "/boards"                        (gethash :uri    (orgtrello-api-add-board "some-board" "some-description"))))
  (should (equal '(("desc" . "some-description")
                   ("name" . "some-board")) (gethash :params (orgtrello-api-add-board "some-board" "some-description")))))

(ert-deftest test-orgtrello-api-add-card-comment ()
  (should (equal "POST"                             (gethash :method (orgtrello-api-add-card-comment :card-id "some comment text"))))
  (should (equal "/cards/:card-id/actions/comments" (gethash :uri    (orgtrello-api-add-card-comment :card-id "some comment text"))))
  (should (equal '(("text" . "some comment text"))  (gethash :params (orgtrello-api-add-card-comment :card-id "some comment text")))))

(ert-deftest test-orgtrello-api-get-lists ()
  (should (equal "GET"                     (gethash :method (orgtrello-api-get-lists :board-id))))
  (should (equal "/boards/:board-id/lists" (gethash :uri    (orgtrello-api-get-lists :board-id))))
  (should (equal nil                       (gethash :params (orgtrello-api-get-lists :board-id)))))

(ert-deftest test-orgtrello-api-get-members ()
  (should (equal "GET"                       (gethash :method (orgtrello-api-get-members :board-id))))
  (should (equal "/boards/:board-id/members" (gethash :uri    (orgtrello-api-get-members :board-id))))
  (should (equal nil                         (gethash :params (orgtrello-api-get-members :board-id)))))

(ert-deftest test-orgtrello-api-archive-card ()
  (should (equal "PUT"                    (gethash :method (orgtrello-api-archive-card :card-id))))
  (should (equal "/cards/:card-id/closed" (gethash :uri    (orgtrello-api-archive-card :card-id))))
  (should (equal '(("value" . "true"))    (gethash :params (orgtrello-api-archive-card :card-id)))))

(ert-deftest test-orgtrello-api-unarchive-card ()
  (should (equal "PUT"                    (gethash :method (orgtrello-api-unarchive-card :card-id))))
  (should (equal "/cards/:card-id/closed" (gethash :uri    (orgtrello-api-unarchive-card :card-id))))
  (should (equal '(("value" . "false"))   (gethash :params (orgtrello-api-unarchive-card :card-id)))))

(ert-deftest test-orgtrello-api-do ()
  (should (equal "PUT"                      (gethash :method (orgtrello-api-do "/boards/%s/closed" :board-id))))
  (should (equal "/boards/:board-id/closed" (gethash :uri    (orgtrello-api-do "/boards/%s/closed" :board-id))))
  (should (equal '(("value" . "true"))      (gethash :params (orgtrello-api-do "/boards/%s/closed" :board-id))))

  (should (equal "PUT"                      (gethash :method (orgtrello-api-do "/boards/%s/closed" :board-id 'undo))))
  (should (equal "/boards/:board-id/closed" (gethash :uri    (orgtrello-api-do "/boards/%s/closed" :board-id 'undo))))
  (should (equal '(("value" . "false"))     (gethash :params (orgtrello-api-do "/boards/%s/closed" :board-id 'undo)))))

(ert-deftest test-orgtrello-api-close-board ()
  (should (equal "PUT"                      (gethash :method (orgtrello-api-close-board :board-id))))
  (should (equal "/boards/:board-id/closed" (gethash :uri    (orgtrello-api-close-board :board-id))))
  (should (equal '(("value" . "true"))      (gethash :params (orgtrello-api-close-board :board-id)))))

(ert-deftest test-orgtrello-api-open-board ()
  (should (equal "PUT"                      (gethash :method (orgtrello-api-open-board :board-id))))
  (should (equal "/boards/:board-id/closed" (gethash :uri    (orgtrello-api-open-board :board-id))))
  (should (equal '(("value" . "false"))     (gethash :params (orgtrello-api-open-board :board-id)))))

(ert-deftest test-orgtrello-api-delete-card-comment ()
  (should (equal "DELETE"                                       (gethash :method (orgtrello-api-delete-card-comment :card-id :comment-id))))
  (should (equal "/cards/:card-id/actions/:comment-id/comments" (gethash :uri    (orgtrello-api-delete-card-comment :card-id :comment-id))))
  (should (equal nil                                            (gethash :params (orgtrello-api-delete-card-comment :card-id :comment-id)))))

(ert-deftest test-orgtrello-api-update-card-comment ()
  (should (equal "PUT"                                          (gethash :method (orgtrello-api-update-card-comment :card-id :comment-id :comment-text))))
  (should (equal "/cards/:card-id/actions/:comment-id/comments" (gethash :uri    (orgtrello-api-update-card-comment :card-id :comment-id :comment-text))))
  (should (equal '(("text" . :comment-text))                    (gethash :params (orgtrello-api-update-card-comment :card-id :comment-id :comment-text)))))

(provide 'org-trello-api-test)
;;; org-trello-api-test.el ends here
