(require 'org-trello-controller)
(require 'ert)
(require 'el-mock)

(ert-deftest test-org-trello-close-board ()
  (should (eq :close-board-done
              (with-mock
                (mock (org-trello--apply-deferred '(org-trello-log-light-checks-and-do
                                                    "Close board"
                                                    orgtrello-controller-do-close-board)) => :close-board-done)
                (org-trello-close-board)))))

(ert-deftest test-orgtrello-controller-do-close-board ()
  (should (eq :close-board-done
              (with-mock
                (mock (orgtrello-deferred-eval-computation
                       nil
                       '('orgtrello-controller--fetch-boards
                         'orgtrello-controller--fetch-user-logged-in
                         'orgtrello-controller--choose-board-id
                         'orgtrello-controller--close-board)
                       "Close board according to your wishes buffer...") => :close-board-done)
                (orgtrello-controller-do-close-board)))))

(ert-deftest test-orgtrello-controller--close-board ()
  (should (equal '(:board-id :some :other)
                 (with-mock
                   (mock (orgtrello-api-close-board :board-id) => :query-close)
                   (mock (orgtrello-query-http-trello :query-close 'sync) => :query-done)
                   (orgtrello-controller--close-board '(:board-id :some :other))))))

(ert-deftest test-orgtrello-controller-toggle-assign-user ()
  (should (eq :user-assigned-or-not-done
              (with-mock
                (mock (orgtrello-setup-users) => :usernames-id-name)
                (mock (orgtrello-controller--usernames :usernames-id-name) => :usernames-list)
                (mock (orgtrello-input-read-string-completion "Users to assign (TAB to complete): " :usernames-list) => :chosen-user)
                (mock (orgtrello-controller--toggle-assign-unassign-user :chosen-user) => :user-assigned-or-not-done)
                (orgtrello-controller-toggle-assign-user)))))

(ert-deftest test-orgtrello-controller--usernames ()
  (should (equal '("dude0" "dude1")
                 (orgtrello-controller--usernames (orgtrello-hash-make-properties '(("some-dude-id" . "orgtrello-user-me")
                                                                                    ("some-dude0-id" . "orgtrello-user-dude0")
                                                                                    ("some-dude1-id" . "orgtrello-user-dude1"))))))
  (should-error (orgtrello-controller--usernames nil)
                :type 'wrong-type-argument))

(ert-deftest test-orgtrello-controller--remove-prefix-usernames ()
  (should (equal
           '("dude0" "dude1" "dude2")
           (orgtrello-controller--remove-prefix-usernames '("orgtrello-user-dude0" "orgtrello-user-dude1" "dude2"))))
  (should-not (orgtrello-controller--remove-prefix-usernames nil)))

(ert-deftest test-orgtrello-controller--toggle-assign-unassign-user ()
  ;; already present, it disappears
  (should (string=
           "* card
:PROPERTIES:
:orgtrello-users: user2
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:orgtrello-users: user,user2
:END:
"
            (orgtrello-controller--toggle-assign-unassign-user "user"))))
  ;; not present, it's added
  (should (string=
           "* card
:PROPERTIES:
:orgtrello-users: user
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:END:
"
            (orgtrello-controller--toggle-assign-unassign-user "user")))))

(ert-deftest test-orgtrello-controller-toggle-assign-unassign-oneself ()
  (should (string=
           "* card
:PROPERTIES:
:orgtrello-users: user2
:END:
"
           (let ((org-trello--user-logged-in "user"))
             (orgtrello-tests-with-temp-buffer-and-return-buffer-content
              "* card
:PROPERTIES:
:orgtrello-users: user,user2
:END:
"
              (orgtrello-controller-toggle-assign-unassign-oneself)))))

  (should (string=
           "* card
:PROPERTIES:
:orgtrello-users: user
:END:
"
           (let ((org-trello--user-logged-in "user"))
             (orgtrello-tests-with-temp-buffer-and-return-buffer-content
              "* card
:PROPERTIES:
:END:
"
              (orgtrello-controller-toggle-assign-unassign-oneself))))))


(ert-deftest test-orgtrello-controller--unassign-user ()
  ;; present, this removes the user entry
  (should (string=
           "* card
:PROPERTIES:
:orgtrello-users: user2
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:orgtrello-users: user,user2
:END:
"
            (orgtrello-controller--unassign-user "user" '("user" "user2")))))
  ;; no more entries, does nothing
  (should (string=
           "* card
:PROPERTIES:
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:END:
"
            (orgtrello-controller--unassign-user "user" nil)))))

(ert-deftest test-orgtrello-controller--assign-user ()
  ;; not present, so assign it add it
  (should (string=
           "* card
:PROPERTIES:
:orgtrello-users: user,user2
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:orgtrello-users: user,user2
:END:
"
            (orgtrello-controller--assign-user "user" '("user2")))))
  ;; already present, it's still added
  (should (string=
           "* card
:PROPERTIES:
:orgtrello-users: user,user2
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:orgtrello-users: user,user2
:END:
"
            (orgtrello-controller--assign-user "user" '("user" "user2")))))
  ;; already present, order in list changes the output
  (should (string=
           "* card
:PROPERTIES:
:orgtrello-users: user2,user
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
:PROPERTIES:
:orgtrello-users: user,user2
:END:
"
            (orgtrello-controller--assign-user "user" '("user2" "user")))))
  ;; no other user, assign it initializes the properties
  (should (string=
           "* card
  :PROPERTIES:
  :orgtrello-users: user
  :END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            "* card
"
            (orgtrello-controller--assign-user "user" nil)))))


(ert-deftest test-orgtrello-controller--users-assigned ()
  (should (equal '("user" "user3" "user2")

                 (orgtrello-tests-with-temp-buffer
                  "* card
  :PROPERTIES:
  :orgtrello-users: user,user3,user2
  :END:
"
                  (orgtrello-controller--users-assigned)))))

(ert-deftest test-orgtrello-controller-do-create-board-and-install-metadata ()
  (should (eq :create-board-done
              (with-mock
                (mock (orgtrello-buffer-filtered-kwds) => :org-keywords)
                (mock (current-buffer) => :buffer-name)
                (mock (orgtrello-deferred-eval-computation
                       '(:org-keywords :buffer-name)
                       '('orgtrello-controller--input-new-board-information
                         'orgtrello-controller--create-new-board
                         'orgtrello-controller--fetch-user-logged-in
                         'orgtrello-controller--close-board-default-lists
                         'orgtrello-controller--create-user-lists-to-board
                         'orgtrello-controller--fetch-board-information
                         'orgtrello-controller--update-buffer-with-board-metadata
                         'orgtrello-controller--save-buffer-and-reload-setup)
                       "Create board and install metadata...") => :create-board-done)
                (orgtrello-controller-do-create-board-and-install-metadata)))))

(ert-deftest test-orgtrello-controller--compute-board-lists-hash-name-id ()
  (should (equal '("#+PROPERTY: done 456" "#+PROPERTY: todo 123")
                 (orgtrello-controller--compute-board-lists-hash-name-id (orgtrello-hash-make-properties '(("todo" . "123")
                                                                                                           ("done" . "456")))))))

(ert-deftest test-orgtrello-controller--compute-keyword-separation ()
  (should (string= "todo"
                   (orgtrello-controller--compute-keyword-separation "todo")))
  (should (string= "| done"
                   (orgtrello-controller--compute-keyword-separation "done")))
  (should (string= "| DONE"
                   (orgtrello-controller--compute-keyword-separation "DONE"))))

(ert-deftest test-orgtrello-controller--fetch-user-logged-in ()
  (should (equal '(:user-entity :boards :buffer-name)
                 (with-mock
                   (mock (orgtrello-api-get-me) => :user-me)
                   (mock (orgtrello-query-http-trello :user-me 'sync) => :user-entity)
                   (orgtrello-controller--fetch-user-logged-in '(:boards :buffer-name))))))

(ert-deftest test-orgtrello-controller-do-update-board-metadata ()
  (should (eq :update-board-done
              (with-mock
                (mock (current-buffer) => :buffer-name)
                (mock (orgtrello-buffer-board-id) => :board-id)
                (mock (orgtrello-buffer-me) => :user-me)
                (mock (orgtrello-deferred-eval-computation
                       '(:board-id :user-me :buffer-name)
                       '('orgtrello-controller--fetch-board-information
                         'orgtrello-controller--update-buffer-with-board-metadata
                         'orgtrello-controller--save-buffer-and-reload-setup)
                       "Update board metadata...") => :update-board-done)
                (orgtrello-controller-do-update-board-metadata)))))

(ert-deftest test-orgtrello-controller--do-sync-card-comment ()
  (should (eq :sync-comment-done
              (with-mock
                (mock (orgtrello-deferred-eval-computation
                       '("card-id" "comment-id" "comment-desc" :buffer-name)
                       '('orgtrello-controller--update-card-comment)
                       "Synchronizing comment...") => :sync-comment-done)
                (orgtrello-controller--do-sync-card-comment (orgtrello-hash-make-properties `((:parent . ,(orgtrello-hash-make-properties '((:id . "card-id"))))
                                                                                              (:current . ,(orgtrello-hash-make-properties '((:id . "comment-id")
                                                                                                                                             (:desc . "comment-desc" )))))) :buffer-name))))
  (should (string= "org-trello - No comment to sync - skip."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (orgtrello-controller--do-sync-card-comment (orgtrello-hash-make-properties `((:parent . ,(orgtrello-hash-make-properties '((:id . ""))))
                                                                                                     (:current . ,(orgtrello-hash-make-properties '((:id)))))) :buffer-name)))))
  (should (string= "org-trello - No comment to sync - skip."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (orgtrello-controller--do-sync-card-comment (orgtrello-hash-make-properties `((:parent . ,(orgtrello-hash-make-properties '((:id . "123"))))
                                                                                                     (:current . ,(orgtrello-hash-make-properties '((:id . "")))))) :buffer-name)))))
  (should (string= "org-trello - No comment to sync - skip."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (orgtrello-controller--do-sync-card-comment (orgtrello-hash-make-properties `((:parent . ,(orgtrello-hash-make-properties '((:id))))
                                                                                                     (:current . ,(orgtrello-hash-make-properties '((:id)))))) :buffer-name))))))


(ert-deftest test-orgtrello-controller--update-card-comment ()
  (should (equal '(:update-done :card-id :comment-id :comment-text)
                 (with-mock
                   (mock (orgtrello-api-update-card-comment :card-id :comment-id :comment-text) => :api-query-update)
                   (mock (orgtrello-query-http-trello :api-query-update 'sync) => :update-done)
                   (orgtrello-controller--update-card-comment '(:card-id :comment-id :comment-text))))))

(ert-deftest test-orgtrello-controller--create-user-lists-to-board ()
  (should (equal '(:board-id :user :board :1 :2 :org-keywords)
                 (with-mock
                   (mock (orgtrello-data-entity-id :board) => :board-id)
                   (mock (orgtrello-controller--create-lists-according-to-keywords :board-id :org-keywords) => :do-not-care-about-the-result)
                   (orgtrello-controller--create-user-lists-to-board '(:user :board :1 :2 :org-keywords))))))

(ert-deftest test-orgtrello-controller--close-board-default-lists ()
  (should (equal '(:user :board :1 :2)
                 (with-mock
                   (mock (orgtrello-data-entity-id :board) => :board-id)
                   (mock (orgtrello-controller--list-board-lists :board-id) => :lists-to-close)
                   (mock (mapcar 'orgtrello-data-entity-id :lists-to-close) => :list-ids-to-close)
                   (mock (orgtrello-controller--close-lists :list-ids-to-close) => :close-lists-done)
                   (orgtrello-controller--close-board-default-lists '(:user :board :1 :2))))))

(ert-deftest test-orgtrello-controller--create-new-board ()
  (should (equal '(:board-created :board-name :board-desc)
                 (with-mock
                   (mock (orgtrello-controller--create-board :board-name :board-desc) => :board-created)
                   (orgtrello-controller--create-new-board '(:board-name :board-desc))))))

(ert-deftest test-orgtrello-controller--input-new-board-information ()
  (should (equal '(:board-name :board-desc :org-keywords :buffername)
                 (with-mock
                   (mock (orgtrello-input-read-not-empty "Please, input desired board name: ") => :board-name)
                   (mock (orgtrello-input-read-string "Please, input board description (empty for none): ") => :board-desc)
                   (orgtrello-controller--input-new-board-information '(:org-keywords :buffername))))))

(ert-deftest test-orgtrello-controller-do-install-board-and-lists ()
  (should (eq :install-board-and-lists-computation
              (with-mock
                (mock (current-buffer) => :buffername)
                (mock (orgtrello-deferred-eval-computation
                       '(:buffername)
                       '('orgtrello-controller--fetch-boards
                         'orgtrello-controller--fetch-user-logged-in
                         'orgtrello-controller--choose-board-id
                         'orgtrello-controller--fetch-board-information
                         'orgtrello-controller--update-buffer-with-board-metadata
                         'orgtrello-controller--save-buffer-and-reload-setup)
                       "Install board metadata in buffer...") => :install-board-and-lists-computation)
                (orgtrello-controller-do-install-board-and-lists)))))

(ert-deftest test-orgtrello-controller--save-buffer-and-reload-setup ()
  (should (eq :reload-setup-done
              (with-mock
                (mock (orgtrello-buffer-save-buffer :buffer-name) => :save-done)
                (mock (orgtrello-action-reload-setup) => :reload-setup-done)
                (orgtrello-controller--save-buffer-and-reload-setup '(:1 :2 :3 :4 :buffer-name))))))

(ert-deftest test-orgtrello-controller--update-buffer-with-board-metadata ()
  (should (equal '(:board :board-id :user-logged-in)
                 (with-mock
                   (mock (orgtrello-data-entity-memberships :board) => :memberships)
                   (mock (orgtrello-controller--compute-user-properties :memberships) => :members)
                   (mock (orgtrello-controller--compute-user-properties-hash :members) => :board-members)
                   (mock (orgtrello-data-entity-name :board) => :board-name)
                   (mock (orgtrello-data-entity-lists :board) => :board-lists)
                   (mock (orgtrello-data-entity-labels :board) => :board-labels)
                   (mock (orgtrello-controller-do-write-board-metadata :board-id
                                                                       :board-name
                                                                       :user-logged-in
                                                                       :board-lists
                                                                       :board-labels
                                                                       :board-members) => :update-buffer-done)
                   (orgtrello-controller--update-buffer-with-board-metadata '(:board :board-id :user-logged-in)))))
  ;; user-logged-in could be a hashtable
  (should (equal '(:board :board-id :user-logged-in)
                 (with-mock
                   (mock (orgtrello-data-entity-memberships :board) => :memberships)
                   (mock (orgtrello-controller--compute-user-properties :memberships) => :members)
                   (mock (orgtrello-controller--compute-user-properties-hash :members) => :board-members)
                   (mock (orgtrello-data-entity-name :board) => :board-name)
                   (mock (orgtrello-data-entity-lists :board) => :board-lists)
                   (mock (orgtrello-data-entity-labels :board) => :board-labels)
                   (mock (hash-table-p :user-logged-in) => t)
                   (mock (orgtrello-data-entity-username :user-logged-in) => :user-name)
                   (mock (orgtrello-controller-do-write-board-metadata :board-id
                                                                       :board-name
                                                                       :user-name
                                                                       :board-lists
                                                                       :board-labels
                                                                       :board-members) => :update-buffer-done)
                   (orgtrello-controller--update-buffer-with-board-metadata '(:board :board-id :user-logged-in))))))

(ert-deftest test-orgtrello-controller--fetch-boards ()
  (should (equal '(:boards :buffername)
                 (with-mock
                   (mock (orgtrello-controller--list-boards) => :boards)
                   (orgtrello-controller--fetch-boards '(:buffername))))))

(ert-deftest test-orgtrello-controller--choose-board-id ()
  (should (equal '(:board-id-selected :user :boards :buffername)
                 (with-mock
                   (mock (orgtrello-controller--name-id :boards) => :boards-name-id)
                   (mock (orgtrello-controller-choose-board :boards-name-id) => :board-id-selected)
                   (orgtrello-controller--choose-board-id '(:user :boards :buffername))))))

(ert-deftest test-orgtrello-controller--fetch-board-information ()
  (should (equal '(:board-info :board-id :user :boards :buffername)
                 (with-mock
                   (mock (orgtrello-api-get-board :board-id) => :api-query-board)
                   (mock (orgtrello-query-http-trello :api-query-board 'sync) => :board-info)
                   (orgtrello-controller--fetch-board-information '(:board-id :user :boards :buffername))))))

(ert-deftest test-orgtrello-controller--do-delete-card-comment ()
  (should (eq :deletion-done
              (with-mock
                (mock (orgtrello-entity-comment-region) => :comment-region)
                (mock (orgtrello-deferred-eval-computation
                       '("card-id" "comment-id" :comment-region)
                       '('orgtrello-controller--delete-card-comment-from-data
                         'orgtrello-controller--delete-comment-region-from-data)
                       "Comment deletion...") => :deletion-done)
                (orgtrello-controller--do-delete-card-comment (orgtrello-hash-make-properties `((:parent . ,(orgtrello-hash-make-properties '((:id . "card-id"))))
                                                                                                (:current . ,(orgtrello-hash-make-properties '((:id . "comment-id")))))) :buffer-name))))
  (should (string= "org-trello - No comment to delete - skip."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (orgtrello-controller--do-delete-card-comment (orgtrello-hash-make-properties `((:parent . ,(orgtrello-hash-make-properties '((:id . ""))))
                                                                                                       (:current . ,(orgtrello-hash-make-properties '((:id)))))) :buffer-name)))))
  (should (string= "org-trello - No comment to delete - skip."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (orgtrello-controller--do-delete-card-comment (orgtrello-hash-make-properties `((:parent . ,(orgtrello-hash-make-properties '((:id . "123"))))
                                                                                                       (:current . ,(orgtrello-hash-make-properties '((:id . "")))))) :buffer-name)))))
  (should (string= "org-trello - No comment to delete - skip."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (orgtrello-controller--do-delete-card-comment (orgtrello-hash-make-properties `((:parent . ,(orgtrello-hash-make-properties '((:id))))
                                                                                                       (:current . ,(orgtrello-hash-make-properties '((:id)))))) :buffer-name))))))

(ert-deftest test-orgtrello-controller--delete-card-comment-from-data ()
  (should (equal '(:result-query :card-id :comment-id)
                 (with-mock
                   (mock (orgtrello-api-delete-card-comment :card-id :comment-id) => :api-query)
                   (mock (orgtrello-query-http-trello :api-query 'sync) => :result-query)
                   (orgtrello-controller--delete-card-comment-from-data '(:card-id :comment-id))))))

(ert-deftest test-orgtrello-controller--delete-comment-region-from-data ()
  (should (eq :delete-done
              (with-mock
                (mock (delete-region :region-start :region-end) => :delete-done)
                (orgtrello-controller--delete-comment-region-from-data '(:res :card-id :comment-id (:region-start :region-end)))))))

(ert-deftest test-orgtrello-controller-do-install-key-and-token ()
  ;; file not existing
  (should (eq :result-install
              (with-mock
                (mock (orgtrello-input-read-not-empty "Trello login account (you need to be logged accordingly in trello.com as we cannot check this for you): ") => "user")
                (mock (orgtrello-controller-config-file "user") => :some-file)
                (mock (file-exists-p :some-file) => nil)
                (mock (orgtrello-deferred-eval-computation
                       '("user")
                       '('orgtrello-controller--open-access-token-consumer-key-url
                         'orgtrello-controller--open-ask-permissions-url
                         'orgtrello-controller--read-access-token
                         'orgtrello-controller--install-key-and-token-login-from-data)
                       "Install key and token...") => :result-install)
                (orgtrello-controller-do-install-key-and-token))))
  ;; file already existing
  (should (string= "org-trello - Configuration for user user already existing (file :some-file), skipping."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (mock (orgtrello-input-read-string "Trello login account (you need to be logged accordingly in trello.com as we cannot check this for you): ") => "user")
                       (mock (orgtrello-controller-config-file "user") => :some-file)
                       (mock (file-exists-p :some-file) => t)
                       (orgtrello-controller-do-install-key-and-token))))))

(ert-deftest test-orgtrello-controller--open-access-token-consumer-key-url ()
  (should (eq :data
              (with-mock
                (mock (orgtrello-setup-compute-url "/1/appKey/generate") => :url)
                (mock (browse-url :url) => :done)
                (orgtrello-controller--open-access-token-consumer-key-url :data)))))

(ert-deftest test-orgtrello-controller--open-ask-permissions-url ()
  (should (equal '("consumer-key" :user-login)
                 (with-mock
                   (mock (orgtrello-input-read-not-empty "Consumer key: ") => " consumer-key ")
                   (mock (browse-url "https://trello.com/1/authorize?response_type=token&name=org-trello&scope=read,write&expiration=never&key=consumer-key") => :done)
                   (orgtrello-controller--open-ask-permissions-url '(:user-login))))))

(ert-deftest test-orgtrello-controller--read-access-token ()
  (should (equal '("access-token" :consumer-key :user-login)
                 (with-mock
                   (mock (orgtrello-input-read-not-empty "Access token: ") => " access-token ")
                   (orgtrello-controller--read-access-token '(:consumer-key :user-login))))))

(ert-deftest test-orgtrello-controller--install-key-and-token-login-from-data ()
  (should (eq :do-install
              (with-mock
                (mock (orgtrello-controller--do-install-config-file :user-login :consumer-key :access-token 'do-ask-for-overwrite) => :do-install)
                (orgtrello-controller--install-key-and-token-login-from-data '(:access-token :consumer-key :user-login))))))

(ert-deftest test-orgtrello-controller-kill-buffer-and-write-new-comment ()
  (should (eq :result-write-new-comment
              (with-mock
                (mock (orgtrello-deferred-eval-computation
                       '(:card-id :buffer-name :point "Add comment to card ':card-id'...")
                       '('orgtrello-controller--extract-comment-and-close-popup
                         'orgtrello-controller--add-comment-to-card
                         'orgtrello-controller--sync-card-from-trello-with-data)
                       "Add comment to card ':card-id'...") => :result-write-new-comment)
                (orgtrello-controller-kill-buffer-and-write-new-comment :card-id :buffer-name :point)))))

(ert-deftest test-orgtrello-controller-sync-card-from-trello ()
  (should (eq :result-sync-card
              (with-mock
                (mock (point) => :point-start)
                (mock (orgtrello-entity-card-at-pt) => t)
                (mock (orgtrello-buffer-entry-get-full-metadata) => :card-fullmeta)
                (mock (orgtrello-data-current :card-fullmeta) => :card-meta)
                (mock (orgtrello-data-entity-name :card-meta) => :card-name)
                (mock (format "Sync trello card '%s' to buffer '%s'..." :card-name :buffer-name) => "do something...")
                (mock (orgtrello-deferred-eval-computation
                       '(:card-meta :buffer-name :card-name :point-start)
                       '('orgtrello-controller--retrieve-full-card
                         'orgtrello-controller--sync-buffer-with-trello-card
                         'orgtrello-controller--after-sync-buffer-with-trello-card)
                       "do something...") => :result-sync-card)
                (orgtrello-controller-sync-card-from-trello :full-meta :buffer-name))))
  (should (eq :result-sync-card-2
              (with-mock
                (mock (point) => :point-start)
                (mock (orgtrello-entity-card-at-pt) => nil)
                (mock (orgtrello-entity-back-to-card) => :back-done)
                (mock (orgtrello-buffer-entry-get-full-metadata) => :card-fullmeta)
                (mock (orgtrello-data-current :card-fullmeta) => :card-meta)
                (mock (orgtrello-data-entity-name :card-meta) => :card-name)
                (mock (format "Sync trello card '%s' to buffer '%s'..." :card-name :buffer-name) => "do something...")
                (mock (orgtrello-deferred-eval-computation
                       '(:card-meta :buffer-name :card-name :point-start)
                       '('orgtrello-controller--retrieve-full-card
                         'orgtrello-controller--sync-buffer-with-trello-card
                         'orgtrello-controller--after-sync-buffer-with-trello-card)
                       "do something...") => :result-sync-card-2)
                (orgtrello-controller-sync-card-from-trello :full-meta :buffer-name)))))

(ert-deftest test-orgtrello-controller-do-archive-card ()
  (should (eq :result-archive
              (with-mock
                (mock (point) => :point-start)
                (mock (orgtrello-data-current :full-meta) => :card-meta)
                (mock (orgtrello-data-entity-name :card-meta) => :card-name)
                (mock (format * *) => "do archive something...")
                (mock (orgtrello-deferred-eval-computation
                       (list :card-meta :card-name :buffer-name :point-start)
                       '('orgtrello-controller--archive-that-card
                         'orgtrello-controller--sync-buffer-with-archive)
                       "do archive something...") => :result-archive)
                (orgtrello-controller-do-archive-card :full-meta :buffer-name)))))

(ert-deftest test-orgtrello-controller-check-trello-connection ()
  (should (eq :check-connection-done
              (with-mock
                (mock (orgtrello-deferred-eval-computation nil
                                                           '('orgtrello-controller--fetch-user-logged-in
                                                             'orgtrello-controller--check-user-account)
                                                           "Checking trello connection..."
                                                           'no-success-log) => :check-connection-done)
                (orgtrello-controller-check-trello-connection)))))

(ert-deftest test-orgtrello-controller-do-sync-buffer-from-trello ()
  (should (eq :result-sync-buffer-from-trello
              (with-mock
                (mock (current-buffer) => :buffer)
                (mock (orgtrello-buffer-board-name) => :board-name)
                (mock (point) => :point-start)
                (mock (orgtrello-buffer-board-id) => :board-id)
                (mock (format * * *) => "do something...")
                (mock (orgtrello-deferred-eval-computation
                       '(:board-id :buffer :board-name :point-start)
                       '('orgtrello-controller--retrieve-archive-cards
                         'orgtrello-controller--retrieve-full-cards
                         'orgtrello-controller--sync-buffer-with-archived-and-trello-cards
                         'orgtrello-controller--after-sync-buffer-with-trello-cards
                         (orgtrello-controller-log-success "do something..."))
                       "do something...") => :result-sync-buffer-from-trello)
                (orgtrello-controller-do-sync-buffer-from-trello)))))

(ert-deftest test-orgtrello-controller--do-install-config-file ()
  (should (string= "(setq org-trello-consumer-key \"consumer-key\"\n      org-trello-access-token \"access-token\")\n"
                   (let ((orgtrello-temp-file (make-temp-file "/tmp/org-trello-user-config-file-temp")))
                     (with-mock
                       (mock (orgtrello-controller-config-file "user") => orgtrello-temp-file)
                       (orgtrello-controller--do-install-config-file "user" "consumer-key" "access-token"))
                     (let ((buffer-content (with-temp-buffer
                                             (insert-file-contents orgtrello-temp-file)
                                             (buffer-substring-no-properties (point-min) (point-max)))))
                       (delete-file orgtrello-temp-file)
                       buffer-content)))))

(ert-deftest test-orgtrello-controller-close-popup ()
  (should (eq :result-done
              (with-mock
                (mock (current-buffer) => :current-buffer)
                (mock (jump-to-register *) => :done)
                (mock (kill-buffer :current-buffer) => :done)
                (mock (define-key org-mode-map * *) => :done)
                (mock (jump-to-register orgtrello-controller-register) => :done)
                (mock (pop-to-buffer :buffer-name) => :done)
                (mock (goto-char :point) => :result-done)
                (orgtrello-controller-close-popup :buffer-name :point)))))

(ert-deftest test-orgtrello-controller-do-show-board-labels ()
  (should (eq :result-show-popup
              (with-mock
                (mock (orgtrello-buffer-labels) => :buffer-labels)
                (mock (orgtrello-data-format-labels :buffer-labels) => :buffer-content-with-labels)
                (mock (orgtrello-buffer-pop-up-with-content "Labels" :buffer-content-with-labels) => :result-show-popup)
                (orgtrello-controller-do-show-board-labels)))))

(ert-deftest test-orgtrello-controller-jump-to-card ()
  (should (eq :result-jump-2
              (with-mock
                (mock (orgtrello-buffer-entry-get-full-metadata) =>
                      (orgtrello-hash-make-properties `((:current . ,(orgtrello-hash-make-properties '((:level . 3)
                                                                                                       (:id . "item-id"))))
                                                        (:grandparent . ,(orgtrello-hash-make-properties '((:level . 1)
                                                                                                           (:id . "card-id-2")))))))
                (mock (browse-url "https://trello.com/c/card-id-2") => :result-jump-2)
                (orgtrello-controller-jump-to-card))))
  (should (eq :result-jump-1
              (with-mock
                (mock (orgtrello-buffer-entry-get-full-metadata) =>
                      (orgtrello-hash-make-properties `((:current . ,(orgtrello-hash-make-properties '((:level . 2)
                                                                                                       (:id . "item-id"))))
                                                        (:parent . ,(orgtrello-hash-make-properties '((:level . 1)
                                                                                                      (:id . "card-id-1")))))))
                (mock (browse-url "https://trello.com/c/card-id-1") => :result-jump-1)
                (orgtrello-controller-jump-to-card))))
  (should (eq :result-jump
              (with-mock
                (mock (orgtrello-buffer-entry-get-full-metadata) =>
                      (orgtrello-hash-make-properties `((:current . ,(orgtrello-hash-make-properties '((:level . 1)
                                                                                                       (:id . "card-id")))))))
                (mock (browse-url "https://trello.com/c/card-id") => :result-jump)
                (orgtrello-controller-jump-to-card))))
  (should-not
   (with-mock
     (mock (orgtrello-buffer-entry-get-full-metadata) => (orgtrello-hash-make-properties `((:current . ,(orgtrello-hash-make-properties '((:level . 1)
                                                                                                                                          (:id)))))))
     (orgtrello-controller-jump-to-card))))

(ert-deftest test-orgtrello-controller-do-write-board-metadata ()
  (should (eq :result-write
              (with-mock
                (mock (orgtrello-controller--name-id :board-lists) => :board-lists-hname-id)
                (mock (orgtrello-hash-keys :board-lists-hname-id) => :board-list-keywords)
                (mock (orgtrello-controller-do-cleanup-from-buffer) => :done)
                (mock (orgtrello-controller--update-orgmode-file-with-properties
                       :board-name
                       :board-id
                       :board-lists-hname-id
                       :board-users-name-id
                       :user-logged-in
                       :board-labels
                       :board-list-keywords) => :result-write)
                (orgtrello-controller-do-write-board-metadata
                 :board-id
                 :board-name
                 :user-logged-in
                 :board-lists
                 :board-labels
                 :board-users-name-id)))))

(ert-deftest test-orgtrello-controller-do-cleanup-from-buffer ()
  ;; should not break when nothing is present
  (should-not (orgtrello-tests-with-temp-buffer
               ""
               (orgtrello-controller-do-cleanup-from-buffer)))
  (should (string= "#+title: dummy sample to sync with trello
#+author: Antoine R. Dumont

* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-local-checksum: 890
:orgtrello-id: 123
:END:
  hello description
  - with many
  - lines

  - including

  - blanks lines
  - lists
  - with start or dash  are now possible
    - indentation too

  - [-] LISP family :PROPERTIES: {\"orgtrello-id\":\"456\",\"orgtrello-local-checksum\":\"5102037e8960abd7ffab6983ede9a0744779a85e36072ad27dbe85e1a038f9eb\"}
    - [X] Emacs-Lisp :PROPERTIES: {\"orgtrello-id\":\"789\",\"orgtrello-local-checksum\":\"7e573221fc50afd48d52c6575845a282b7c48091e616ee48214436cb3e49a09b\"}
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    ":PROPERTIES:
#+PROPERTY: board-name api test board
#+PROPERTY: board-id abc
#+PROPERTY: CANCELLED def
#+PROPERTY: FAILED ghi
#+PROPERTY: DELEGATED jkl
#+PROPERTY: PENDING mno
#+PROPERTY: DONE pqr
#+PROPERTY: IN-PROGRESS tuv
#+PROPERTY: TODO wxy
#+TODO: TODO IN-PROGRESS | DONE PENDING DELEGATED FAILED CANCELLED
#+PROPERTY: orgtrello-user-antoineromaindumont z01
#+PROPERTY: orgtrello-user-orgmode 234
#+PROPERTY: orgtrello-user-ardumont 567
#+PROPERTY: :green green label with & char
#+PROPERTY: :yellow yello
#+PROPERTY: :orange range
#+PROPERTY: :red red
#+PROPERTY: :purple violet
#+PROPERTY: :blue blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
#+title: dummy sample to sync with trello
#+author: Antoine R. Dumont

* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-local-checksum: 890
:orgtrello-id: 123
:END:
  hello description
  - with many
  - lines

  - including

  - blanks lines
  - lists
  - with start or dash  are now possible
    - indentation too

  - [-] LISP family :PROPERTIES: {\"orgtrello-id\":\"456\",\"orgtrello-local-checksum\":\"5102037e8960abd7ffab6983ede9a0744779a85e36072ad27dbe85e1a038f9eb\"}
    - [X] Emacs-Lisp :PROPERTIES: {\"orgtrello-id\":\"789\",\"orgtrello-local-checksum\":\"7e573221fc50afd48d52c6575845a282b7c48091e616ee48214436cb3e49a09b\"}
"
                    (orgtrello-controller-do-cleanup-from-buffer))))
  (should (string= "#+title: dummy sample to sync with trello
#+author: Antoine R. Dumont

* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:END:
  hello description
  - with many
  - lines

  - including

  - blanks lines
  - lists
  - with start or dash  are now possible
    - indentation too

  - [-] LISP family
    - [X] Emacs-Lisp
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    ":PROPERTIES:
#+PROPERTY: board-name api test board
#+PROPERTY: board-id abc
#+PROPERTY: CANCELLED def
#+PROPERTY: FAILED ghi
#+PROPERTY: DELEGATED jkl
#+PROPERTY: PENDING mno
#+PROPERTY: DONE pqr
#+PROPERTY: IN-PROGRESS tuv
#+PROPERTY: TODO wxy
#+TODO: TODO IN-PROGRESS | DONE PENDING DELEGATED FAILED CANCELLED
#+PROPERTY: orgtrello-user-antoineromaindumont z01
#+PROPERTY: orgtrello-user-orgmode 234
#+PROPERTY: orgtrello-user-ardumont 567
#+PROPERTY: :green green label with & char
#+PROPERTY: :yellow yello
#+PROPERTY: :orange range
#+PROPERTY: :red red
#+PROPERTY: :purple violet
#+PROPERTY: :blue blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
#+title: dummy sample to sync with trello
#+author: Antoine R. Dumont

* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-local-checksum: 890
:orgtrello-id: 123
:orgtrello-users: bla
:END:
  hello description
  - with many
  - lines

  - including

  - blanks lines
  - lists
  - with start or dash  are now possible
    - indentation too

  - [-] LISP family :PROPERTIES: {\"orgtrello-id\":\"456\",\"orgtrello-local-checksum\":\"5102037e8960abd7ffab6983ede9a0744779a85e36072ad27dbe85e1a038f9eb\"}
    - [X] Emacs-Lisp :PROPERTIES: {\"orgtrello-id\":\"789\",\"orgtrello-local-checksum\":\"7e573221fc50afd48d52c6575845a282b7c48091e616ee48214436cb3e49a09b\"}
"
                    (orgtrello-controller-do-cleanup-from-buffer 'global)))))

(ert-deftest test-orgtrello-controller-do-sync-card-comment ()
  (should (eq :result-delete-card-comment
              (with-mock
                (mock (orgtrello-entity-back-to-card) => :back)
                (mock (current-buffer) => :buffer)
                (mock (orgtrello-buffer-safe-entry-full-metadata) => :entity)
                (mock (orgtrello-action-functional-controls-then-do
                       '(orgtrello-controller--on-entity-p
                         orgtrello-controller--right-level-p
                         orgtrello-controller--already-synced-p)
                       :entity
                       'orgtrello-controller--do-sync-card-comment
                       :buffer) => :result-delete-card-comment)
                (orgtrello-controller-do-sync-card-comment)))))

(ert-deftest test-orgtrello-controller-do-delete-card-comment ()
  (should (eq :result-delete-card-comment
              (with-mock
                (mock (current-buffer) => :buffer)
                (mock (orgtrello-buffer-safe-entry-full-metadata) => :entity)
                (mock (orgtrello-action-functional-controls-then-do
                       '(orgtrello-controller--on-entity-p
                         orgtrello-controller--right-level-p
                         orgtrello-controller--already-synced-p)
                       :entity
                       'orgtrello-controller--do-delete-card-comment
                       :buffer) => :result-delete-card-comment)
                (orgtrello-controller-do-delete-card-comment)))))

(ert-deftest test-orgtrello-controller-do-add-card-comment ()
  (should (eq :card-added
              (with-mock
                (mock (orgtrello-entity-back-to-card) => :back)
                (mock (orgtrello-buffer-entity-metadata) => (orgtrello-hash-make-properties '((:id . "card-id"))))
                (mock (orgtrello-controller-add-comment "card-id") => :card-added)
                (orgtrello-controller-do-add-card-comment))))
  (should (string= "org-trello - Card not synchronized so cannot add comment - skip."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (mock (orgtrello-entity-back-to-card) => :back)
                       (mock (orgtrello-buffer-entity-metadata) => (orgtrello-hash-make-properties '((:id))))
                       (orgtrello-controller-do-add-card-comment)))))
  (should (string= "org-trello - Card not synchronized so cannot add comment - skip."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (mock (orgtrello-entity-back-to-card) => :back)
                       (mock (orgtrello-buffer-entity-metadata) => (orgtrello-hash-make-properties '((:id . ""))))
                       (orgtrello-controller-do-add-card-comment))))))

(ert-deftest test-orgtrello-controller--extract-comment-and-close-popup ()
  (should (equal '("some comment trimmed from popup's comment" :card-id :buffer-name :point :prefix-log)
                 (with-mock
                   (mock (buffer-string) => "some comment trimmed from popup's comment")
                   (mock (orgtrello-controller-close-popup :buffer-name :point) => :popup-closed)
                   (orgtrello-controller--extract-comment-and-close-popup '(:card-id :buffer-name :point :prefix-log))))))

(ert-deftest test-orgtrello-controller--sync-card-from-trello-with-data ()
  (should (eq :data
              (with-mock
                (mock (orgtrello-controller-checks-then-sync-card-from-trello) => :result-sync-card)
                (orgtrello-controller--sync-card-from-trello-with-data :data)))))

(ert-deftest test-orgtrello-controller--add-comment-to-card ()
  (should (equal (list :result-query :comment :card-id)
                 (with-mock
                   (mock (orgtrello-api-add-card-comment :card-id :comment) => :query-add-card)
                   (mock (orgtrello-query-http-trello :query-add-card 'sync) => :result-query)
                   (orgtrello-controller--add-comment-to-card '(:comment :card-id))))))

(ert-deftest test-orgtrello-controller-delete-setup ()
  (should (string= "org-trello - Cleanup done!"
                   (with-mock
                     (mock (orgtrello-controller-do-cleanup-from-buffer t) => :done)
                     (orgtrello-controller-delete-setup)))))

(ert-deftest test-orgtrello-controller--properties-compute-users-ids ()
  (should (equal '("#+PROPERTY: orgtrello-user-user2 456" "#+PROPERTY: orgtrello-user-user1 123")
                 (orgtrello-controller--properties-compute-users-ids (orgtrello-hash-make-properties '(("user1" . "123")
                                                                                                       ("user2" . "456"))))))
  (should-not (orgtrello-controller--properties-compute-users-ids (orgtrello-hash-empty-hash))))

(ert-deftest test-orgtrello-controller-log-success ()
  (should (string= "org-trello - do something... DONE."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (funcall (orgtrello-controller-log-success "do something..."))))))

(ert-deftest test-orgtrello-controller--archive-that-card ()
  (should (equal '(:archive-result :card-meta :card-name)
                 (with-mock
                   (mock (orgtrello-data-entity-id :card-meta) => :id)
                   (mock (orgtrello-api-archive-card :id) => :query-archive-card)
                   (mock (orgtrello-query-http-trello :query-archive-card 'sync) => :archive-result)
                   (orgtrello-controller--archive-that-card '(:card-meta :card-name))))))

(ert-deftest test-orgtrello-controller--sync-buffer-with-archive ()
  (should (eq :archive-and-save-done
              (orgtrello-tests-with-temp-buffer
               "* card
"
               (let ((orgtrello-log-level orgtrello-log-info)
                     (buf (current-buffer)))
                 (with-mock
                   (mock (org-archive-subtree) => :archive-done)
                   (mock (orgtrello-buffer-save-buffer buf) => :archive-and-save-done)
                   (orgtrello-controller--sync-buffer-with-archive `(:trello-archive-card
                                                                     :card-meta
                                                                     "card"
                                                                     ,buf
                                                                     ,(point-min)))))))))

(ert-deftest test-orgtrello-controller-checks-and-do-archive-card ()
  ;; on card
  (should (string= :archive-result
                   (orgtrello-tests-with-temp-buffer
                    "* card
"
                    (with-mock
                      (mock (orgtrello-buffer-entry-get-full-metadata) => :card-meta)
                      (mock (orgtrello-action-functional-controls-then-do
                             '(orgtrello-controller--right-level-p
                               orgtrello-controller--already-synced-p)
                             :card-meta
                             'orgtrello-controller-do-archive-card
                             (current-buffer)) => :archive-result)
                      (orgtrello-controller-checks-and-do-archive-card)))))
  ;; when on checklist
  (should (string= :archive-result
                   (orgtrello-tests-with-temp-buffer
                    "* card
  - [ ] checklist
"
                    (with-mock
                      (mock (orgtrello-buffer-entry-get-full-metadata) => :card-meta)
                      (mock (orgtrello-action-functional-controls-then-do
                             '(orgtrello-controller--right-level-p
                               orgtrello-controller--already-synced-p)
                             :card-meta
                             'orgtrello-controller-do-archive-card
                             (current-buffer)) => :archive-result)
                      (orgtrello-controller-checks-and-do-archive-card))))))

(ert-deftest test-orgtrello-controller-log-error ()
  (should (string= "org-trello - do something... FAILED. Error code: foo-bar"
                   (funcall (orgtrello-controller-log-error "do something..." "Error code: %s-%s") "foo" "bar"))))

(ert-deftest test-orgtrello-controller--after-sync-buffer-with-trello-card ()
  (should (equal :sync-buffer-with-trello-card-done
                 (let ((orgtrello-log-level orgtrello-log-info))
                   (with-mock
                     (mock (orgtrello-buffer-save-buffer :buffer-name) => :done)
                     (mock (goto-char :point-start) => :sync-buffer-with-trello-card-done)
                     (orgtrello-controller--after-sync-buffer-with-trello-card '(:full-card :card-meta :buffer-name :card-name :point-start)))))))

(ert-deftest test-orgtrello-controller--retrieve-full-card ()
  (should (equal '(:full-card :card-meta :buffer-name :card-name :point-start)
                 (with-mock
                   (mock (orgtrello-data-entity-id :card-meta) => :card-id)
                   (mock (orgtrello-api-get-full-card :card-id) => :query-get-full-card)
                   (mock (orgtrello-query-http-trello :query-get-full-card 'sync) => :full-card)
                   (orgtrello-controller--retrieve-full-card '(:card-meta :buffer-name :card-name :point-start))))))

(ert-deftest test-orgtrello-controller--sync-buffer-with-trello-card ()
  (should (equal '(:trello-card :card-meta :buffer-name)
                 (with-mock
                   (mock (orgtrello-data-to-org-trello-card :trello-card) => :org-card)
                   (mock (orgtrello-controller-compute-and-overwrite-card :buffer-name  :org-card) => :done)
                   (orgtrello-controller--sync-buffer-with-trello-card '(:trello-card :card-meta :buffer-name))))))

(ert-deftest test-orgtrello-controller--check-user-account ()
  (should (string= "org-trello - Account user configured! Everything is ok!"
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (orgtrello-controller--check-user-account (list (orgtrello-hash-make-properties '((:username . "user"))))))))
  (should (string= "org-trello - There is a problem with your credentials.
Make sure you used M-x org-trello-install-key-and-token and this installed correctly the consumer-key and access-token.
See http://org-trello.github.io/trello-setup.html#credentials for more information."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (orgtrello-controller--check-user-account nil)))))

(ert-deftest test-orgtrello-controller--retrieve-archive-cards ()
  (should (equal '(:archive-cards :board-id :buffer-name :board-name :point-start)
                 (with-mock
                   (mock (orgtrello-api-get-archived-cards :board-id) => :query-archive-cards)
                   (mock (orgtrello-query-http-trello :query-archive-cards 'sync) => :archive-cards)
                   (orgtrello-controller--retrieve-archive-cards '(:board-id :buffer-name :board-name :point-start))))))

(ert-deftest test-orgtrello-controller--retrieve-full-cards ()
  (should (equal '(:cards :archive-cards :board-id :buffer-name :board-name :point-start)
                 (with-mock
                   (mock (orgtrello-api-get-full-cards :board-id) => :query-cards)
                   (mock (orgtrello-query-http-trello :query-cards 'sync) => :cards)
                   (orgtrello-controller--retrieve-full-cards '(:archive-cards :board-id :buffer-name :board-name :point-start))))))

(ert-deftest test-orgtrello-controller--sync-buffer-with-archived-and-trello-cards ()
  (should (equal '(:trello-cards :archive-cards :board-id :buffer-name :board-name :point-start)
                 (let ((orgtrello-log-level orgtrello-log-info))
                   (with-mock
                     (mock (orgtrello-buffer-archive-cards :archive-cards) => :done)
                     (mock (mapcar #'orgtrello-data-to-org-trello-card :trello-cards) => :org-cards)
                     (mock (orgtrello-controller-sync-buffer-with-trello-cards :buffer-name :org-cards) => :result-sync-from)
                     (orgtrello-controller--sync-buffer-with-archived-and-trello-cards '(:trello-cards :archive-cards :board-id :buffer-name :board-name :point-start)))))))

(ert-deftest test-orgtrello-controller--after-sync-buffer-with-trello-cards ()
  (should (equal :after-sync-done
                 (let ((orgtrello-log-level orgtrello-log-info))
                   (with-mock
                     (mock (orgtrello-buffer-save-buffer :buffer-name) => :done)
                     (mock (goto-char :point-start) => :after-sync-done)
                     (orgtrello-controller--after-sync-buffer-with-trello-cards '(:cards :archive-cards :board-id :buffer-name :board-name :point-start)))))))

(ert-deftest test-orgtrello-controller--map-cards-to-computations ()
  (should (equal '(:computation) ;; only card0 computation mapped
                 (let* ((card0 (orgtrello-hash-make-properties '((:id . "123")
                                                                 (:level . 1)
                                                                 (:name . "card has a name"))))
                        ;; card1 won't be elected cause it got no name
                        (card1 (orgtrello-hash-make-properties '((:id . "456")
                                                                 (:level . 1))))
                        ;; checklist are not elected
                        (checklist (orgtrello-hash-make-properties '((:id . "789")
                                                                     (:level . 2))))
                        ;; item neither
                        (item (orgtrello-hash-make-properties '((:id . "012")
                                                                (:level . 3))))
                        (entities (orgtrello-hash-make-properties `(("123" . ,card0)
                                                                    ("456" . ,card1)
                                                                    ("789" . ,checklist)
                                                                    ("012" . ,item))))
                        (adjacencies (orgtrello-hash-make-properties '(("123")
                                                                       ("456")
                                                                       ("789")
                                                                       ("012"))))
                        (entities-adjacencies (list entities adjacencies)))
                   (with-mock
                     (mock (orgtrello-proxy-sync-entity card0 entities-adjacencies) => :computation)
                     (orgtrello-controller--map-cards-to-computations entities-adjacencies))))))

(ert-deftest test-orgtrello-controller-execute-sync-entity-structure ()
  ;; some cards to sync
  (should (eq :result-synced
              (with-mock
                (mock (orgtrello-controller--map-cards-to-computations :entities-adj) => :computations)
                (mock (orgtrello-proxy-execute-async-computations
                       :computations
                       "card(s) sync ok!"
                       "FAILURE! cards(s) sync KO!") => :result-synced)
                (orgtrello-controller-execute-sync-entity-structure :entities-adj))))
  ;; nothing to sync
  (should (let ((orgtrello-log-level orgtrello-log-info))
            (equal "org-trello - No card(s) to sync."
                   (with-mock
                     (mock (orgtrello-controller--map-cards-to-computations :entities-adj) => nil)
                     (orgtrello-controller-execute-sync-entity-structure :entities-adj))))))

(ert-deftest test-orgtrello-controller--convention-property-name ()
  (should (string= "-bla-bli-blo-" (orgtrello-controller--convention-property-name " bla bli blo ")))
  (should (string= "some-made-up-name-with-parenthesis" (orgtrello-controller--convention-property-name "some made-up name with (parenthesis)"))))

(ert-deftest test-orgtrello-controller-prepare-buffer ()
  (should (eq :prepared-buffer-done
              (with-mock
                (mock (orgtrello-setup-org-trello-on-p) => t)
                (mock (orgtrello-buffer-install-overlays) => :done)
                (mock (orgtrello-buffer-indent-card-descriptions) => :done)
                (mock (orgtrello-buffer-indent-card-data) => :prepared-buffer-done)
                (orgtrello-controller-prepare-buffer))))
  (should-not
   (with-mock
     (mock (orgtrello-setup-org-trello-on-p))
     (orgtrello-controller-prepare-buffer))))

(ert-deftest test-orgtrello-controller-mode-on-hook-fn ()
  (should-not
   (let ((org-trello--mode-activated-p))
     (with-mock
       (mock (add-to-invisibility-spec '(org-trello-cbx-property)))
       (mock (orgtrello-controller-setup-properties))
       (mock (add-hook 'before-save-hook 'orgtrello-controller-prepare-buffer))
       (mock (orgtrello-controller-prepare-buffer))
       (mock (run-hooks 'org-trello-mode-hook))
       (orgtrello-controller-mode-on-hook-fn)))))

(ert-deftest test-orgtrello-controller-mode-off-hook-fn ()
  (should-not
   (let ((org-trello--mode-activated-p t))
     (with-mock
       (mock (remove-from-invisibility-spec '(org-trello-cbx-property)) => :done)
       (mock (remove-hook 'before-save-hook 'orgtrello-controller-prepare-buffer) => :done)
       (mock (orgtrello-buffer-remove-overlays) => :done)
       (orgtrello-controller-mode-off-hook-fn)))))

(ert-deftest test-orgtrello-controller-jump-to-board ()
  (should (eq :browsed-url
              (orgtrello-tests-with-temp-buffer
               ":PROPERTIES:
#+PROPERTY: board-id 123
:END:
"
               (with-mock
                 (mock (browse-url "https://trello.com/b/123") => :browsed-url)
                 (orgtrello-controller-jump-to-board))))))

(ert-deftest test-orgtrello-controller-do-unassign-me ()
  (should (string= "
:PROPERTIES:
#+PROPERTY: orgtrello-user-user1 foo
#+PROPERTY: orgtrello-user-user2 bar
#+PROPERTY: orgtrello-user-user3 foobar
#+PROPERTY: orgtrello-user-me user2
:END:
* card
  :PROPERTIES:
  :END:
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "
:PROPERTIES:
#+PROPERTY: orgtrello-user-user1 foo
#+PROPERTY: orgtrello-user-user2 bar
#+PROPERTY: orgtrello-user-user3 foobar
#+PROPERTY: orgtrello-user-me user2
:END:
* card
  :PROPERTIES:
  :orgtrello-users: user2
  :END:
"
                    (orgtrello-controller-do-unassign-me))))
  (should (string= "
:PROPERTIES:
#+PROPERTY: orgtrello-user-user1 foo
#+PROPERTY: orgtrello-user-user2 bar
#+PROPERTY: orgtrello-user-user3 foobar
#+PROPERTY: orgtrello-user-me user2
:END:
* card
  :PROPERTIES:
  :orgtrello-users: user1
  :END:
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "
:PROPERTIES:
#+PROPERTY: orgtrello-user-user1 foo
#+PROPERTY: orgtrello-user-user2 bar
#+PROPERTY: orgtrello-user-user3 foobar
#+PROPERTY: orgtrello-user-me user2
:END:
* card
  :PROPERTIES:
  :orgtrello-users: user2,user1
  :END:
"
                    (orgtrello-controller-do-unassign-me)))))

(ert-deftest test-orgtrello-controller-do-assign-me ()
  (should (string= "
:PROPERTIES:
#+PROPERTY: orgtrello-user-user1 foo
#+PROPERTY: orgtrello-user-user2 bar
#+PROPERTY: orgtrello-user-user3 foobar
#+PROPERTY: orgtrello-user-me user2
:END:
* card
  :PROPERTIES:
  :orgtrello-users: user2
  :END:
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "
:PROPERTIES:
#+PROPERTY: orgtrello-user-user1 foo
#+PROPERTY: orgtrello-user-user2 bar
#+PROPERTY: orgtrello-user-user3 foobar
#+PROPERTY: orgtrello-user-me user2
:END:
* card
"
                    (orgtrello-controller-do-assign-me))))
  (should (string= "
:PROPERTIES:
#+PROPERTY: orgtrello-user-user1 foo
#+PROPERTY: orgtrello-user-user2 bar
#+PROPERTY: orgtrello-user-user3 foobar
#+PROPERTY: orgtrello-user-me user2
:END:
* card
  :PROPERTIES:
  :orgtrello-users: user2,user1
  :END:
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "
:PROPERTIES:
#+PROPERTY: orgtrello-user-user1 foo
#+PROPERTY: orgtrello-user-user2 bar
#+PROPERTY: orgtrello-user-user3 foobar
#+PROPERTY: orgtrello-user-me user2
:END:
* card
  :PROPERTIES:
  :orgtrello-users: user1
  :END:
"
                    (orgtrello-controller-do-assign-me)))))

(ert-deftest test-orgtrello-controller--cleanup-org-entries ()
  (should (string= "* card
:PROPERTIES:
:orgtrello-id: id
:END:
  - [ ] checklist :PROPERTIES: {\"orgtrello-id\":\"123\"}
    - [ ] item :PROPERTIES: {\"orgtrello-id\":\"456\"}
"
                   (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                    "* card
:PROPERTIES:
:orgtrello-id: id
:END:
  - [ ] checklist :PROPERTIES: {\"orgtrello-id\":\"123\"}
    - [ ] item :PROPERTIES: {\"orgtrello-id\":\"456\"}
"
                    (orgtrello-controller--cleanup-org-entries)))))

(ert-deftest test-orgtrello-controller-sync-card-to-trello ()
  (should (eq :result-no-sync-needed
              (with-mock
                (mock (orgtrello-buffer-card-checksum) => "same-checksum")
                (mock (orgtrello-log-msg
                       orgtrello-log-info
                       "Card already synchronized, nothing to do!") => :result-no-sync-needed)
                (orgtrello-tests-with-temp-buffer
                 "* card
:PROPERTIES:
:orgtrello-id: 123
:orgtrello-local-checksum: same-checksum
:END:
  description"
                 (orgtrello-controller-sync-card-to-trello (orgtrello-buffer-entry-get-full-metadata) (current-buffer))
                 -6))))
  (should (eq :result-sync
              (with-mock
                (mock (orgtrello-buffer-card-checksum) => "checksum")
                (mock (orgtrello-controller-execute-sync-entity-structure *) => :result-sync)
                (orgtrello-tests-with-temp-buffer
                 ":PROPERTIES:
#+PROPERTY: board-name board
:END:
* card
:PROPERTIES:
:orgtrello-id: 123
:orgtrello-local-checksum: old-checksum
:END:
  description
"
                 (orgtrello-controller-sync-card-to-trello (orgtrello-buffer-entry-get-full-metadata) (current-buffer))
                 -6)))))

(ert-deftest test-orgtrello-controller-delete-card ()
  (should (eq
           2
           (with-mock
             (mock (orgtrello-proxy-delete-entity *) => '(+ 1 1))
             (orgtrello-tests-with-temp-buffer
              "* card
:PROPERTIES:
:orgtrello-id: 55d77b041fd32d11d99eb787
:END:
  description
  - [ ] cbx
    - [ ] item
* another card
"
              (progn
                (goto-char (point-min))
                (orgtrello-controller-delete-card (orgtrello-buffer-entry-get-full-metadata) (current-buffer))))))))

(ert-deftest test-orgtrello-controller-do-delete-entities ()
  (should (equal :result-do-delete-entities-with-no-check
                 (with-mock
                   (mock (org-map-entries 'orgtrello-controller--do-delete-card t 'file) => :result-do-delete-entities-with-no-check)
                   (orgtrello-controller-do-delete-entities))))
  (should (equal :result-do-delete-entities-with-check
                 (let ((orgtrello-with-check-on-sensible-actions t))
                   (with-mock
                     (mock (orgtrello-input-confirm "Do you want to delete all cards? ") => t)
                     (mock (org-map-entries 'orgtrello-controller--do-delete-card t 'file) => :result-do-delete-entities-with-check)
                     (orgtrello-controller-do-delete-entities)))))
  (should-not (let ((orgtrello-with-check-on-sensible-actions t))
                (with-mock
                  (mock (orgtrello-input-confirm "Do you want to delete all cards? ") => nil)
                  (orgtrello-controller-do-delete-entities)))))

(ert-deftest test-orgtrello-controller--do-delete-card ()
  (should (equal :result-do-delete-card
                 (with-mock
                   (mock (orgtrello-entity-card-at-pt) => t)
                   (mock (orgtrello-controller-checks-then-delete-simple) => :result-do-delete-card)
                   (orgtrello-controller--do-delete-card))))
  ;; do nothing
  (should-not
   (with-mock
     (mock (orgtrello-entity-card-at-pt) => nil)
     (orgtrello-controller--do-delete-card))))

(ert-deftest test-orgtrello-controller--sync-buffer-with-trello-data ()
  (should (string=
           ":PROPERTIES:
#+PROPERTY: orgtrello-user-ardumont ardumont-id
#+PROPERTY: orgtrello-user-dude dude-id
:END:
* TODO some card name                                                   :red:green:
  :PROPERTIES:
  :orgtrello-users: ardumont,dude
  :orgtrello-local-checksum: card-checksum
  :orgtrello-id: some-card-id
  :END:
  some description
  - [-] some cbx name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"cbx-checksum\"}
    - [X] some it name :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"item-checksum\"}
    - [ ] some other item name :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"item-checksum\"}
  - [-] some other cbx name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"cbx-checksum\"}

** COMMENT ardumont, some-date
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: comment-checksum
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
     (mock (orgtrello-buffer-card-checksum) => "card-checksum")
     (mock (orgtrello-buffer-checklist-checksum) => "cbx-checksum")
     (mock (orgtrello-buffer-item-checksum) => "item-checksum")
     (mock (orgtrello-buffer-comment-checksum) => "comment-checksum")
     (orgtrello-controller--sync-buffer-with-trello-data
      (list (orgtrello-hash-make-properties
             `(("some-card-id" .  ,(orgtrello-hash-make-properties `((:keyword . "TODO")
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
               ("some-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-cbx-id")
                                                                         (:name . "some cbx name")
                                                                         (:level . ,org-trello--checklist-level))))
               ("some-other-checklist-id" . ,(orgtrello-hash-make-properties `((:id . "some-other-cbx-id")
                                                                               (:name . "some other cbx name")
                                                                               (:level . ,org-trello--checklist-level))))
               ("some-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-it-id")
                                                                     (:name . "some it name")
                                                                     (:level . ,org-trello--item-level)
                                                                     (:keyword . "DONE"))))
               ("some-other-item-id"  . ,(orgtrello-hash-make-properties `((:id . "some-other-it-id")
                                                                           (:name . "some other item name")
                                                                           (:level . ,org-trello--item-level)
                                                                           (:keyword . "TODO"))))))
            (orgtrello-hash-make-properties
             `(("some-other-checklist-id")
               ("some-checklist-id" "some-item-id" "some-other-item-id")
               ("some-card-id" "some-checklist-id" "some-other-checklist-id"))))))))))

(ert-deftest test-orgtrello-controller-do-sync-buffer-to-trello ()
  (should (equal :result
                 (with-mock
                   (mock (orgtrello-buffer-board-name) => :buffer-board-name)
                   (mock (current-buffer) => :buffer)
                   (mock (orgtrello-buffer-build-org-entities :buffer) => :entities)
                   (mock (orgtrello-controller-execute-sync-entity-structure :entities) => :result)
                   (orgtrello-controller-do-sync-buffer-to-trello)))))

(ert-deftest test-orgtrello-controller--create-lists-according-to-keywords ()
  (should (orgtrello-tests-hash-equal
           (orgtrello-hash-make-properties '((:todo . "todo-list-id")))
           (with-mock
             (mock (orgtrello-api-add-list :todo :board-id 1) => :query-add-list)
             (mock (orgtrello-query-http-trello :query-add-list 'sync) => (orgtrello-hash-make-properties '((:id . "todo-list-id"))))
             (orgtrello-controller--create-lists-according-to-keywords :board-id '(:todo))))))

(ert-deftest test-orgtrello-controller--close-lists ()
  (should (equal
           :result-comp-close-lists
           (with-mock
             (mock (orgtrello-api-close-list :list-id0) => :query-close-list-id-0)
             (mock (orgtrello-query-http-trello :query-close-list-id-0 nil * *) => :async-computation-0)
             (mock (orgtrello-proxy-execute-async-computations
                    '(:async-computation-0)
                    "List(s) closed."
                    "FAILURE - Problem during closing list.") => :result-comp-close-lists)
             (orgtrello-controller--close-lists '(:list-id0))))))

(ert-deftest test-orgtrello-controller--create-board ()
  (should (eq :result
              (with-mock
                (mock (orgtrello-api-add-board :board-name :board-description) => :query-create)
                (mock (orgtrello-query-http-trello :query-create 'sync) => :result)
                (orgtrello-controller--create-board :board-name :board-description)))))

(ert-deftest test-orgtrello-controller--update-orgmode-file-with-properties ()
  (should (string=
           ":PROPERTIES:
#+PROPERTY: board-name board's name or title
#+PROPERTY: board-id board-id
#+PROPERTY: done list-id-789
#+PROPERTY: in-progress-2 list-id-456
#+PROPERTY: todo-1 list-id-123
#+TODO: todo-1 in-progress-2 | done
#+PROPERTY: orgtrello-user-orgtrello-user-user3 789
#+PROPERTY: orgtrello-user-orgtrello-user-user2 456
#+PROPERTY: orgtrello-user-orgtrello-user-user1 123
#+PROPERTY: :green green label
#+PROPERTY: :red red label
#+PROPERTY: orgtrello-user-me user3
:END:
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            ""
            (orgtrello-controller--update-orgmode-file-with-properties
             "board's name or title"
             "board-id"
             (orgtrello-hash-make-properties '(("todo-1" . "list-id-123")
                                               ("in-progress-2" . "list-id-456")
                                               ("done" . "list-id-789")))
             (orgtrello-hash-make-properties '(("orgtrello-user-user1" . "123")
                                               ("orgtrello-user-user2" . "456")
                                               ("orgtrello-user-user3" . "789")))
             "user3"
             (list
              (orgtrello-hash-make-properties '((:color . "red")
                                                (:name . "red label")))
              (orgtrello-hash-make-properties '((:color . "green")
                                                (:name . "green label"))))
             'do-delete-the-todo-line)))))

(ert-deftest test-orgtrello-controller--properties-compute-todo-keywords-as-string ()
  (should (string= "#+TODO: list-id-1 list-id-2 list-id-3"
                   (orgtrello-controller--properties-compute-todo-keywords-as-string
                    (orgtrello-hash-make-properties '(("list-id-1" . "123")
                                                      ("list-id-2" . "456")
                                                      ("list-id-3" . "789")))))))

(ert-deftest test-orgtrello-controller--remove-properties-file ()
  (should (string=
           "#+title: dummy sample to sync with trello
#+author: Antoine R. Dumont"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
            ":PROPERTIES:
#+PROPERTY: board-name test board api
#+PROPERTY: board-id board-id-1
#+PROPERTY: CAN list-1-id
#+PROPERTY: FAI list-2-id
#+PROPERTY: DEL list-3-id
#+PROPERTY: PEN list-4-id
#+PROPERTY: DON list-5-id
#+PROPERTY: INP list-6-id
#+PROPERTY: TOD list-7-id
#+TODO: TODO IN-PROGRESS | DONE PENDING DELEGATED FAILED CANCELLED
#+PROPERTY: orgtrello-user-user2 456
#+PROPERTY: :green green label with & char
#+PROPERTY: :yellow yello
#+PROPERTY: :orange range
#+PROPERTY: :red red
#+PROPERTY: :purple violet
#+PROPERTY: :blue blue
#+PROPERTY: :green another one
#+PROPERTY: orgtrello-user-me user2
:END:
#+title: dummy sample to sync with trello
#+author: Antoine R. Dumont"
            (orgtrello-controller--remove-properties-file
             '("TOD" "INP" "DON" "PEN" "DEL" "FAI" "CAN")
             (orgtrello-hash-make-properties '(("orgtrello-user-user1" . "123")
                                               ("orgtrello-user-user2" . "456")
                                               ("orgtrello-user-user3" . "789")
                                               ("orgtrello-user-me" . "user2")))
             "user2"
             'do-delete-the-todo-line)))))

(ert-deftest test-orgtrello-controller--compute-hash-name-id-to-list ()
  (should (equal '("#+PROPERTY: orgtrello-user-user3 451"
                   "#+PROPERTY: orgtrello-user-user2 341"
                   "#+PROPERTY: orgtrello-user-user1 231")
                 (orgtrello-controller--compute-hash-name-id-to-list (orgtrello-hash-make-properties '(("user1" . "231")
                                                                                                       ("user2" . "341")
                                                                                                       ("orgtrello-user-user3" . "451")))))))

(ert-deftest test-orgtrello-controller-checks-then-sync-card-to-trello ()
  (should (eq :result-sync
              (with-mock
                (mock (current-buffer) => :buffer)
                (mock (orgtrello-buffer-safe-entry-full-metadata) => :entity)
                (mock (orgtrello-action-functional-controls-then-do
                       '(orgtrello-controller--on-entity-p
                         orgtrello-controller--right-level-p
                         orgtrello-controller--mandatory-name-ok-p)
                       :entity
                       'orgtrello-controller-sync-card-to-trello
                       :buffer) => :result-sync)
                (orgtrello-controller-checks-then-sync-card-to-trello)))))

(ert-deftest test-orgtrello-controller-checks-then-delete-simple ()
  (should (eq :result-delete
              (with-mock
                (mock (current-buffer) => :buffer)
                (mock (orgtrello-buffer-safe-entry-full-metadata) => :entity)
                (mock (orgtrello-action-functional-controls-then-do
                       '(orgtrello-controller--on-entity-p
                         orgtrello-controller--right-level-p
                         orgtrello-controller--already-synced-p)
                       :entity
                       'orgtrello-controller-delete-card
                       :buffer) => :result-delete)
                (orgtrello-controller-checks-then-delete-simple)))))

(ert-deftest test-orgtrello-controller-checks-then-sync-card-from-trello ()
  (should (eq :result-sync-from
              (with-mock
                (mock (current-buffer) => :buffer)
                (mock (orgtrello-buffer-safe-entry-full-metadata) => :entity)
                (mock (orgtrello-action-functional-controls-then-do
                       '(orgtrello-controller--on-entity-p
                         orgtrello-controller--right-level-p
                         orgtrello-controller--already-synced-p)
                       :entity
                       'orgtrello-controller-sync-card-from-trello
                       :buffer) => :result-sync-from)
                (orgtrello-controller-checks-then-sync-card-from-trello)))))

(ert-deftest test-orgtrello-controller--delete-buffer-property ()
  (should (equal "* card
:PROPERTIES:
:END:
"
                 (orgtrello-tests-with-temp-buffer-and-return-buffer-content
                  "* card
:PROPERTIES:
:prop: blah
:END:
"
                  (orgtrello-controller--delete-buffer-property ":prop:")))))

(ert-deftest test-orgtrello-controller-setup-properties ()
  (should
   (-every? (-partial 'eq t)
            (orgtrello-tests-with-temp-buffer
             ":PROPERTIES:
#+PROPERTY: board-name test board
#+PROPERTY: board-id identifier-for-the-board
#+PROPERTY: CANCELLED cancelled-list-id
#+PROPERTY: FAILED failed-list-id
#+PROPERTY: DELEGATED deletegated-list-id
#+PROPERTY: PENDING pending-list-id
#+PROPERTY: DONE done-list-id
#+PROPERTY: IN-PROGRESS in-progress-list-id
#+PROPERTY: TODO todo-list-id
#+TODO: TODO IN-PROGRESS | DONE PENDING DELEGATED FAILED CANCELLED
#+PROPERTY: orgtrello-user-user1 user1-id
#+PROPERTY: orgtrello-user-user2 user2-id
#+PROPERTY: orgtrello-user-user3 user3-id
#+PROPERTY: :green green label with & char
#+PROPERTY: :yellow yello
#+PROPERTY: :orange range
#+PROPERTY: :red red
#+PROPERTY: :purple violet
#+PROPERTY: :blue blue
#+PROPERTY: orgtrello-user-me user1
:END:
"
             (let ((org-tag-alist nil)
                   (org-trello--user-logged-in))
               (orgtrello-controller-setup-properties)
               (list
                (equal org-trello--org-keyword-trello-list-names '("TODO" "IN-PROGRESS" "DONE" "PENDING" "DELEGATED" "FAILED" "CANCELLED"))
                (orgtrello-tests-hash-equal
                 org-trello--hmap-list-orgkeyword-id-name
                 (orgtrello-hash-make-properties
                  '(("todo-list-id" . "TODO")
                    ("in-progress-list-id" . "IN-PROGRESS")
                    ("done-list-id" . "DONE")
                    ("pending-list-id" . "PENDING")
                    ("deletegated-list-id" . "DELEGATED")
                    ("failed-list-id" . "FAILED")
                    ("cancelled-list-id" . "CANCELLED"))))
                (orgtrello-tests-hash-equal
                 org-trello--hmap-users-id-name
                 (orgtrello-hash-make-properties
                  '(("user1-id" . "orgtrello-user-user1")
                    ("user2-id" . "orgtrello-user-user2")
                    ("user3-id" . "orgtrello-user-user3")
                    ("user1" . "orgtrello-user-me"))))
                (orgtrello-tests-hash-equal
                 org-trello--hmap-users-name-id
                 (orgtrello-hash-make-properties
                  '(("orgtrello-user-user1" . "user1-id")
                    ("orgtrello-user-user2" . "user2-id")
                    ("orgtrello-user-user3" . "user3-id")
                    ("orgtrello-user-me" . "user1"))))
                (string= org-trello--user-logged-in "user1")
                (equal org-tag-alist (nreverse
                                      '(("red" . ?r)
                                        ("green" . ?g)
                                        ("yellow" . ?y)
                                        ("blue" . ?b)
                                        ("purple" . ?p)
                                        ("orange" . ?o))))))))))

(ert-deftest test-orgtrello-controller-control-properties ()
  ;; ok
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  ":PROPERTIES:
#+PROPERTY: board-name test board
#+PROPERTY: board-id identifier-for-the-board
#+PROPERTY: CANCELLED cancelled-list-id
#+PROPERTY: FAILED failed-list-id
#+PROPERTY: DELEGATED deletegated-list-id
#+PROPERTY: PENDING pending-list-id
#+PROPERTY: DONE done-list-id
#+PROPERTY: IN-PROGRESS in-progress-list-id
#+PROPERTY: TODO todo-list-id
:END:
"
                  (orgtrello-controller-control-properties :args-not-used))))
  ;; missing board id
  (should (string= "Setup problem.
Either you did not connect your org-mode buffer with a trello board, to correct this:
  * attach to a board through C-c o I or M-x org-trello-install-board-metadata
  * or create a board from scratch with C-c o b or M-x org-trello-create-board-and-install-metadata).
Either your org-mode's todo keyword list and your trello board lists are not named the same way (which they must).
For this, connect to trello and rename your board's list according to your org-mode's todo list.
Also, you can specify on your org-mode buffer the todo list you want to work with, for example: #+TODO: TODO DOING | DONE FAIL (hit C-c C-c to refresh the setup)"
                   (orgtrello-tests-with-temp-buffer
                    ":PROPERTIES:
#+PROPERTY: board-name test board
#+PROPERTY: CANCELLED cancelled-list-id
#+PROPERTY: FAILED failed-list-id
#+PROPERTY: DELEGATED deletegated-list-id
#+PROPERTY: PENDING pending-list-id
#+PROPERTY: DONE done-list-id
#+PROPERTY: IN-PROGRESS in-progress-list-id
#+PROPERTY: TODO todo-list-id
:END:
"
                    (orgtrello-controller-control-properties :args-not-used))))
  ;; missing one list id
  (should (string= "Setup problem.
Either you did not connect your org-mode buffer with a trello board, to correct this:
  * attach to a board through C-c o I or M-x org-trello-install-board-metadata
  * or create a board from scratch with C-c o b or M-x org-trello-create-board-and-install-metadata).
Either your org-mode's todo keyword list and your trello board lists are not named the same way (which they must).
For this, connect to trello and rename your board's list according to your org-mode's todo list.
Also, you can specify on your org-mode buffer the todo list you want to work with, for example: #+TODO: TODO DOING | DONE FAIL (hit C-c C-c to refresh the setup)"
                   (orgtrello-tests-with-temp-buffer
                    ":PROPERTIES:
#+PROPERTY: board-name test board
#+PROPERTY: board-id identifier-for-the-board
#+PROPERTY: CANCELLED cancelled-list-id
"
                    (orgtrello-controller-control-properties :args-not-used)))))

(ert-deftest test-orgtrello-controller-migrate-user-setup ()
  ;; nothing to do
  (should (equal :ok
                 (with-mock
                   (mock (file-exists-p org-trello--old-config-dir) => nil)
                   (orgtrello-controller-migrate-user-setup :args-not-used))))
  (should (equal :ok
                 (let ((*consumer-key* :consumer-key)
                       (*access-token* :access-token)
                       (org-trello--old-config-dir :config-dir)
                       (org-trello--old-config-file :config-file))
                   (with-mock
                     (mock (file-exists-p org-trello--old-config-dir) => t)
                     (mock (orgtrello-buffer-me) => :user-logged-in)
                     (mock (load org-trello--old-config-file) => :done)
                     (mock (orgtrello-controller--do-install-config-file
                            :user-logged-in
                            :consumer-key
                            :access-token) => :done)
                     (mock (delete-directory org-trello--old-config-dir 'with-contents) => :done)
                     (orgtrello-controller-migrate-user-setup :args-not-used)))))
  ;; current setup
  (should (equal :ok
                 (let ((*consumer-key* nil)
                       (org-trello--old-config-dir :config-dir)
                       (org-trello--old-config-file :config-file)
                       (org-trello-consumer-key :org-trello-consumer-key)
                       (org-trello-access-token :org-trello-access-token))
                   (with-mock
                     (mock (file-exists-p org-trello--old-config-dir) => t)
                     (mock (orgtrello-buffer-me) => :user-logged-in-2)
                     (mock (load org-trello--old-config-file) => :done)
                     (mock (orgtrello-controller--do-install-config-file :user-logged-in-2 :org-trello-consumer-key :org-trello-access-token) => :done)
                     (mock (delete-directory org-trello--old-config-dir 'with-contents) => :done)
                     (orgtrello-controller-migrate-user-setup :args-not-used))))))

(ert-deftest test-orgtrello-controller-config-file ()
  (should (string= "~/.emacs.d/.trello/tony.el"
                   (let ((org-trello--config-file "~/.emacs.d/.trello/%s.el"))
                     (orgtrello-controller-config-file "tony"))))
  (should (string= "~/.emacs.d/.trello/user.el"
                   (with-mock
                     (mock (orgtrello-setup-user-logged-in) => "user")
                     (let ((org-trello--config-file "~/.emacs.d/.trello/%s.el"))
                       (orgtrello-controller-config-file))))))

(ert-deftest test-orgtrello-controller-user-config-files ()
  (should (equal :list
                 (with-mock
                   (mock (file-exists-p org-trello--config-dir) => t)
                   (mock (directory-files org-trello--config-dir 'full-name "^.*\.el") => :list)
                   (orgtrello-controller-user-config-files))))
  (should-not (with-mock
                (mock (file-exists-p *) => nil)
                (orgtrello-controller-user-config-files))))

(ert-deftest test-orgtrello-controller--on-entity-p ()
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--on-entity-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--on-entity-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] item"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--on-entity-p))))
  (should (equal "You need to be on an org-trello entity (card/checklist/item) for this action to occur!"
                 (orgtrello-tests-with-temp-buffer
                  "** not on a card
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--on-entity-p)))))

(ert-deftest test-orgtrello-controller--right-level-p ()
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--right-level-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--right-level-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] item"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--right-level-p))))
  (should (equal "Wrong level. Do not deal with entity other than card/checklist/item!"
                 (orgtrello-tests-with-temp-buffer
                  "** not on a card
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--right-level-p)))))

(ert-deftest test-orgtrello-controller--already-synced-p ()
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
:PROPERTIES:
:orgtrello-id: 123
:END:"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--already-synced-p))))
  (should (equal "Entity must be synchronized with trello first!"
                 (orgtrello-tests-with-temp-buffer
                  "* card"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--already-synced-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
:PROPERTIES:
:orgtrello-id: 123
:END:
  - [ ] checklist :PROPERTIES: {\"orgtrello-id\":\"123\"}"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      (orgtrello-controller--already-synced-p)))))
  (should (equal "Entity must be synchronized with trello first!"
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--already-synced-p))))

  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
:PROPERTIES:
:orgtrello-id: 123
:END:
  - [ ] checklist :PROPERTIES: {\"orgtrello-id\":\"456\"}
    - [ ] item :PROPERTIES: {\"orgtrello-id\":\"123456\"}
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--already-synced-p))))
  (should (equal "Entity must be synchronized with trello first!"
                 (orgtrello-tests-with-temp-buffer
                  "* card
:PROPERTIES:
:orgtrello-id: 123
:END:
  - [ ] checklist
    - [ ] item
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--already-synced-p)))))

(ert-deftest test-orgtrello-controller--entity-mandatory-name-ok-p ()
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card with a name
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-data-current
                      orgtrello-controller--entity-mandatory-name-ok-p))))
  (should (equal "Cannot synchronize the card - missing mandatory name. Skip it..."
                 (orgtrello-tests-with-temp-buffer
                  "* \n"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-data-current
                      orgtrello-controller--entity-mandatory-name-ok-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-data-current
                      orgtrello-controller--entity-mandatory-name-ok-p))))

  (should (equal "Cannot synchronize the checklist - missing mandatory name. Skip it..."
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] \n"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-data-current
                      orgtrello-controller--entity-mandatory-name-ok-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] item
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-data-current
                      orgtrello-controller--entity-mandatory-name-ok-p))))
  (should (equal "Cannot synchronize the item - missing mandatory name. Skip it..."
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] \n"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-data-current
                      orgtrello-controller--entity-mandatory-name-ok-p)))))

(ert-deftest test-orgtrello-controller--mandatory-name-ok-p ()
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card with a name
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--mandatory-name-ok-p))))
  (should (equal "Cannot synchronize the card - missing mandatory name. Skip it..."
                 (orgtrello-tests-with-temp-buffer
                  "* \n"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--mandatory-name-ok-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--mandatory-name-ok-p))))

  (should (equal "Cannot synchronize the checklist - missing mandatory name. Skip it..."
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] \n"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--mandatory-name-ok-p))))
  (should (equal :ok
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] item
"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-controller--mandatory-name-ok-p))))
  (should (equal "Cannot synchronize the item - missing mandatory name. Skip it..."
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] \n"
                  (-> (orgtrello-buffer-safe-entry-full-metadata)
                      orgtrello-data-current
                      orgtrello-controller--entity-mandatory-name-ok-p)))))

(ert-deftest test-orgtrello-controller--compute-data-from-entity-meta ()
  (let* ((entry   (orgtrello-data-make-hash-org :member-ids :some-level :some-keyword :some-name "some-id" :some-due :some-point :some-buffername :desc :tags :unknown)))
    (should (equal (orgtrello-data-entity-id entry)          "some-id"))
    (should (equal (orgtrello-data-entity-name entry)        :some-name))
    (should (equal (orgtrello-data-entity-keyword entry)     :some-keyword))
    (should (equal (orgtrello-data-entity-level entry)       :some-level))
    (should (equal (orgtrello-data-entity-due entry)         :some-due))
    (should (equal (orgtrello-data-entity-position entry)    :some-point))
    (should (equal (orgtrello-data-entity-buffername entry)  :some-buffername))
    (should (equal (orgtrello-data-entity-member-ids entry)  :member-ids))
    (should (equal (orgtrello-data-entity-tags entry)        :tags))
    (should (equal (orgtrello-data-entity-description entry) :desc))
    (should (equal (orgtrello-data-entity-unknown-properties entry) :unknown))))

(ert-deftest test-orgtrello-controller--name-id ()
  (let* ((entities (orgtrello-data-parse-data [((id . "id")
                                                (shortUrl . "https://trello.com/b/ePrdEnzC")
                                                (name . "testing board"))
                                               ((id . "another-id")
                                                (shortUrl . "https://trello.com/b/ePrdEnzC")
                                                (name . "testing board 2"))
                                               ((id . "yet-another-id")
                                                (shortUrl . "https://trello.com/b/ePrdEnzC")
                                                (name . "testing board 3"))]))
         (hashtable-result (orgtrello-controller--name-id entities))
         (hashtable-expected (make-hash-table :test 'equal)))
    (orgtrello-hash-puthash-data "testing board" "id" hashtable-expected)
    (orgtrello-hash-puthash-data "testing board 2" "another-id"  hashtable-expected)
    (orgtrello-hash-puthash-data "testing board 3" "yet-another-id"  hashtable-expected)
    (should (equal (gethash "testing board" hashtable-result) (gethash "testing board" hashtable-expected)))
    (should (equal (gethash "testing board 2" hashtable-result) (gethash "testing board 2" hashtable-expected)))
    (should (equal (gethash "testing board 3" hashtable-result) (gethash "testing board 3" hashtable-expected)))
    (should (equal (hash-table-count hashtable-result) (hash-table-count hashtable-expected)))))

(ert-deftest test-orgtrello-controller--compute-user-properties ()
  (should (orgtrello-tests-hash-equal
           (orgtrello-hash-make-properties '((:username . "ardumont")
                                             (:full-name . "Antoine R. Dumont")
                                             (:id . "4f2baa2f72b7c1293501cad3")))
           (car (orgtrello-controller--compute-user-properties
                 (list (orgtrello-hash-make-properties
                        `((:member . ,(orgtrello-hash-make-properties '((:username . "ardumont")
                                                                        (:full-name . "Antoine R. Dumont")
                                                                        (:id . "4f2baa2f72b7c1293501cad3"))))
                          (:id . "51d99bbc1e1d8988390047f6")))
                       (orgtrello-hash-make-properties `((:member . ,(orgtrello-hash-make-properties '((:username . "orgmode")
                                                                                                       (:full-name . "org trello")
                                                                                                       (:id . "5203a0c833fc36360800177f"))))
                                                         (:id . "524855ff8193aec160002cfa"))))))))
  (should (orgtrello-tests-hash-equal
           (orgtrello-hash-make-properties '((:username . "orgmode")
                                             (:full-name . "org trello")
                                             (:id . "5203a0c833fc36360800177f")))
           (cadr (orgtrello-controller--compute-user-properties
                  (list (orgtrello-hash-make-properties
                         `((:member . ,(orgtrello-hash-make-properties '((:username . "ardumont")
                                                                         (:full-name . "Antoine R. Dumont")
                                                                         (:id . "4f2baa2f72b7c1293501cad3"))))
                           (:id . "51d99bbc1e1d8988390047f6")))
                        (orgtrello-hash-make-properties
                         `((:member . ,(orgtrello-hash-make-properties '((:username . "orgmode")
                                                                         (:full-name . "org trello")
                                                                         (:id . "5203a0c833fc36360800177f"))))
                           (:id . "524855ff8193aec160002cfa")))))))))

(ert-deftest test-orgtrello-controller--compute-user-properties-hash ()
  (should (orgtrello-tests-hash-equal
           (orgtrello-hash-make-properties '(("ardumont" . "4f2baa2f72b7c1293501cad3")
                                             ("orgmode" . "5203a0c833fc36360800177f")))
           (orgtrello-controller--compute-user-properties-hash
            (list (orgtrello-hash-make-properties '((:username . "ardumont")
                                                    (:full-name . "Antoine R. Dumont")
                                                    (:id . "4f2baa2f72b7c1293501cad3")))
                  (orgtrello-hash-make-properties '((:username . "orgmode")
                                                    (:full-name . "org trello")
                                                    (:id . "5203a0c833fc36360800177f"))))))))

(ert-deftest test-orgtrello-controller--list-user-entries ()
  (should (equal
           '(("orgtrello-user-ardumont" . "4f2baa2f72b7c1293501cad3")
             ("orgtrello-user-orgmode" . "5203a0c833fc36360800177f"))
           (orgtrello-controller--list-user-entries '(("board-name" . "api test board")
                                                      ("board-id" . "51d99bbc1e1d8988390047f2")
                                                      ("TODO" . "51d99bbc1e1d8988390047f3")
                                                      ("IN-PROGRESS" . "51d99bbc1e1d8988390047f4")
                                                      ("DONE" . "51d99bbc1e1d8988390047f5")
                                                      ("PENDING" . "51e53898ea3d1780690015ca")
                                                      ("DELEGATED" . "51e538a89c05f1e25c0027c6")
                                                      ("FAIL" . "51e538a26f75d07902002d25")
                                                      ("CANCELLED" . "51e538e6c7a68fa0510014ee")
                                                      ("orgtrello-user-ardumont" . "4f2baa2f72b7c1293501cad3")
                                                      ("orgtrello-user-orgmode" . "5203a0c833fc36360800177f"))))))

(ert-deftest test-orgtrello-controller--add-user ()
  (should (equal '("a" "b" "c") (orgtrello-controller--add-user "a" '("a" "b" "c"))))
  (should (equal '("a" "b" "c") (orgtrello-controller--add-user "a" '("b" "c")))))

(ert-deftest test-orgtrello-controller--remove-user ()
  (should (equal '("b")     (orgtrello-controller--remove-user "a" '("a" "b"))))
  (should (equal '("a" "b") (orgtrello-controller--remove-user "c" '("a" "b"))))
  (should (equal nil        (orgtrello-controller--remove-user "c" nil)))
  (should (equal nil        (orgtrello-controller--remove-user nil nil)))
  (should (equal '("a")     (orgtrello-controller--remove-user nil '("a")))))

(ert-deftest test-orgtrello-controller-compute-property ()
  (should (equal "#+PROPERTY: test "      (orgtrello-controller-compute-property "test")))
  (should (equal "#+PROPERTY: test value" (orgtrello-controller-compute-property "test" "value"))))

(ert-deftest test-orgtrello-controller--compute-metadata ()
  (should (equal '(":PROPERTIES:"
                   "#+PROPERTY: board-name some-board-name"
                   "#+PROPERTY: board-id some-board-id"
                   "#+PROPERTY: DONE done-id"
                   "#+PROPERTY: TODO todo-id"
                   ""
                   "#+PROPERTY: orgtrello-user-some-other-user some-other-user-id"
                   "#+PROPERTY: orgtrello-user-user user-id"
                   "#+PROPERTY: :green green label"
                   "#+PROPERTY: :red red label"
                   "#+PROPERTY: orgtrello-user-me user"
                   ":END:")
                 (orgtrello-controller--compute-metadata
                  "some-board-name"
                  "some-board-id"
                  (orgtrello-hash-make-properties '(("TODO" . "todo-id") ("DONE" . "done-id")))
                  (orgtrello-hash-make-properties '(("user" . "user-id") ("some-other-user" . "some-other-user-id")))
                  "user"
                  (list
                   (orgtrello-hash-make-properties '((:color . "red")
                                                     (:name . "red label")))
                   (orgtrello-hash-make-properties '((:color . "green")
                                                     (:name . "green label")))))))
  (should (equal '(":PROPERTIES:"
                   "#+PROPERTY: board-name some-board-name"
                   "#+PROPERTY: board-id some-board-id"
                   "#+PROPERTY: DONE done-id-2"
                   "#+PROPERTY: TODO todo-id-2"
                   ""
                   "#+PROPERTY: orgtrello-user-some-other-user some-other-user-id-2"
                   "#+PROPERTY: orgtrello-user-user user-id-2"
                   "#+PROPERTY: :green green label"
                   "#+PROPERTY: :red red label"
                   "#+PROPERTY: orgtrello-user-me user-logged-in"
                   ":END:")
                 (let ((org-trello--user-logged-in "user-logged-in"))
                   (orgtrello-controller--compute-metadata
                    "some-board-name"
                    "some-board-id"
                    (orgtrello-hash-make-properties '(("TODO" . "todo-id-2") ("DONE" . "done-id-2")))
                    (orgtrello-hash-make-properties '(("user" . "user-id-2") ("some-other-user" . "some-other-user-id-2")))
                    nil
                    (list
                     (orgtrello-hash-make-properties '((:color . "red")
                                                       (:name . "red label")))
                     (orgtrello-hash-make-properties '((:color . "green")
                                                       (:name . "green label")))))))))

(ert-deftest test-orgtrello-controller--properties-labels ()
  (should (equal
           '("#+PROPERTY: :black" "#+PROPERTY: :orange" "#+PROPERTY: :grey grey label" "#+PROPERTY: :green green label" "#+PROPERTY: :red red label")
           (orgtrello-controller--properties-labels `(,(orgtrello-hash-make-properties '((:color . "red")
                                                                                         (:name . "red label")))
                                                      ,(orgtrello-hash-make-properties '((:color . "green")
                                                                                         (:name . "green label")))
                                                      ,(orgtrello-hash-make-properties '((:color . nil)
                                                                                         (:name . "grey label")))
                                                      ,(orgtrello-hash-make-properties '((:color . "orange")
                                                                                         (:name . "")))
                                                      ,(orgtrello-hash-make-properties '((:color . "black"))))))))

(ert-deftest test-orgtrello-controller-load-keys ()
  (should (equal :ok
                 (with-mock
                   (mock (orgtrello-controller-config-file) => :some-config-file)
                   (mock (file-exists-p :some-config-file)   => t)
                   (mock (load :some-config-file)            => t)
                   (orgtrello-controller-load-keys))))
  (should (equal "Setup problem - Problem during credentials loading (consumer-key and read/write access-token) - C-c o i or M-x org-trello-install-key-and-token"
                 (with-mock
                   (mock (orgtrello-controller-config-file) => :some-config-file)
                   (mock (file-exists-p :some-config-file)   => nil)
                   (orgtrello-controller-load-keys))))
  (should (equal "Setup problem - Problem during credentials loading (consumer-key and read/write access-token) - C-c o i or M-x org-trello-install-key-and-token"
                 (with-mock
                   (mock (orgtrello-controller-config-file) => :some-config-file)
                   (mock (file-exists-p :some-config-file)   => t)
                   (mock (load :some-config-file)            => nil)
                   (orgtrello-controller-load-keys)))))

(ert-deftest test-orgtrello-controller-control-keys ()
  (should (equal :ok
                 (let ((org-trello-consumer-key "some-consumer-key")
                       (org-trello-access-token "some-access-token"))
                   (orgtrello-controller-control-keys))))
  (should (equal "Setup problem - You need to install the consumer-key and the read/write access-token - C-c o i or M-x org-trello-install-key-and-token"
                 (let ((org-trello-consumer-key "some-consumer-key")
                       (org-trello-access-token nil))
                   (orgtrello-controller-control-keys))))
  (should (equal "Setup problem - You need to install the consumer-key and the read/write access-token - C-c o i or M-x org-trello-install-key-and-token"
                 (let ((org-trello-consumer-key nil)
                       (org-trello-access-token "some-access-token"))
                   (orgtrello-controller-control-keys)))))

(ert-deftest test-orgtrello-controller-choose-board ()
  (should (equal :id-board0
                 (with-mock
                   (mock (orgtrello-hash-keys *) => :boards)
                   (mock (orgtrello-input-read-string-completion
                          "Board to install (TAB to complete): "
                          :boards) => "board0-name")
                   (orgtrello-controller-choose-board (orgtrello-hash-make-properties '(("board0-name" . :id-board0) ("board1-name" . :id-board1)))))))
  (should (equal :id-board1
                 (with-mock
                   (mock (orgtrello-hash-keys *) => :boards)
                   (mock (orgtrello-input-read-string-completion
                          "Board to install (TAB to complete): "
                          :boards) => "board1-name")
                   (orgtrello-controller-choose-board (orgtrello-hash-make-properties '(("board0-name" . :id-board0) ("board1-name" . :id-board1))))))))

(ert-deftest test-orgtrello-controller--choose-account ()
  (should (equal "account0"
                 (with-mock
                   (mock (orgtrello-input-read-string-completion
                          "Select org-trello account (TAB to complete): "
                          '("account0" "account1")) => "account0")
                   (orgtrello-controller--choose-account '("account0" "account1")))))
  (should (equal "account1"
                 (with-mock
                   (mock (orgtrello-input-read-string-completion
                          "Select org-trello account (TAB to complete): "
                          '("account0" "account1")) => "account1")
                   (orgtrello-controller--choose-account '("account0" "account1"))))))

(ert-deftest test-orgtrello-controller--list-boards ()
  (should (equal t
                 (orgtrello-tests-hash-equal
                  (orgtrello-hash-make-properties '((:id . "id0")
                                                    (:name . "name0")
                                                    (:closed . nil)))
                  (car (with-mock
                         (mock (orgtrello-api-get-boards "open")          => :query)
                         (mock (orgtrello-query-http-trello :query 'sync) => (list (orgtrello-hash-make-properties '((:id . "id0") (:name . "name0") (:closed)))
                                                                                   (orgtrello-hash-make-properties '((:id . "id1") (:name . "name1") (:closed)))
                                                                                   (orgtrello-hash-make-properties '((:id . "id1") (:name . "name1") (:closed . t)))))
                         (orgtrello-controller--list-boards))))))
  (should (equal
           t
           (orgtrello-tests-hash-equal
            (orgtrello-hash-make-properties '((:id . "id1")
                                              (:name . "name1")
                                              (:closed . nil)))
            (cadr (with-mock
                    (mock (orgtrello-api-get-boards "open")          => :query)
                    (mock (orgtrello-query-http-trello :query 'sync) => (list (orgtrello-hash-make-properties '((:id . "id0") (:name . "name0") (:closed)))
                                                                              (orgtrello-hash-make-properties '((:id . "id1") (:name . "name1") (:closed)))
                                                                              (orgtrello-hash-make-properties '((:id . "id1") (:name . "name1") (:closed . t)))))
                    (orgtrello-controller--list-boards)))))))

(ert-deftest test-orgtrello-controller--list-board-lists ()
  (should (equal :some-result
                 (with-mock
                   (mock (orgtrello-api-get-lists :board-id)        => :query)
                   (mock (orgtrello-query-http-trello :query 'sync) => :some-result)
                   (orgtrello-controller--list-board-lists :board-id)))))

(ert-deftest test-orgtrello-controller--hmap-id-name ()
  (should (equal t
                 (orgtrello-tests-hash-equal (orgtrello-hash-make-properties '(("786" . "CANCELLED")
                                                                               ("456" . "FAILED")
                                                                               ("ijk" . "DONE")
                                                                               ("abc" . "TODO")))
                                             (orgtrello-controller--hmap-id-name '("CANCELLED" "FAILED" "DONE" "TODO")
                                                                                '(("board-name" . "some board")
                                                                                  ("board-id" . "10223")
                                                                                  ("CANCELLED" . "786")
                                                                                  ("FAILED" . "456")
                                                                                  ("DELEGATED" . "123")
                                                                                  ("PENDING" . "efg")
                                                                                  ("DONE" . "ijk")
                                                                                  ("IN-PROGRESS" . "def")
                                                                                  ("TODO" . "abc"))))))
  (should (equal t
                 (orgtrello-tests-hash-equal (orgtrello-hash-empty-hash)
                                             (orgtrello-controller--hmap-id-name '("CANCELLED" "FAILED" "DONE" "TODO")
                                                                                '()))))
  (should (equal t
                 (orgtrello-tests-hash-equal (orgtrello-hash-empty-hash)
                                             (orgtrello-controller--hmap-id-name '()
                                                                                '(("board-name" . "some board"))))))
  (should (equal t
                 (orgtrello-tests-hash-equal (orgtrello-hash-empty-hash)
                                             (orgtrello-controller--hmap-id-name '()
                                                                                '())))))

(ert-deftest test-orgtrello-controller-compute-and-overwrite-card ()
  (should (equal
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
#+PROPERTY: orgtrello-user-dude 888
#+PROPERTY: orgtrello-user-ardumont 999
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
* TODO updated card title                                               :orange:red:green:
  :PROPERTIES:
  :orgtrello-users: dude,ardumont
  :orgtrello-local-checksum: local-card-checksum-678
  :orgtrello-id: some-card-id
  :END:
  updated description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"local-checklist-checksum-678\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"local-item-checksum-678\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"local-item-checksum-678\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"local-checklist-checksum-678\"}

** COMMENT ardumont, 10/10/2010
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: local-comment-checksum-678
:END:
  some comment

** COMMENT tony, 11/10/2010
:PROPERTIES:
:orgtrello-id: some-comment-id2
:orgtrello-local-checksum: local-comment-checksum-678
:END:
  some second comment


* other card name
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
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
#+PROPERTY: orgtrello-user-dude 888
#+PROPERTY: orgtrello-user-ardumont 999
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
* TODO some card name                                                   :orange:
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-card-comments: ardumont: some comment
:END:
some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* other card name
"
            (with-mock
              (mock (orgtrello-buffer-card-checksum) => "local-card-checksum-678")
              (mock (orgtrello-buffer-checklist-checksum) => "local-checklist-checksum-678")
              (mock (orgtrello-buffer-item-checksum) => "local-item-checksum-678")
              (mock (orgtrello-buffer-comment-checksum) => "local-comment-checksum-678")
              (let* ((trello-card (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                    (:member-ids . "888,999")
                                                                    (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                          (:comment-date . "10/10/2010")
                                                                                                                          (:comment-id   . "some-comment-id")
                                                                                                                          (:comment-text . "some comment")))
                                                                                        (orgtrello-hash-make-properties '((:comment-user . "tony")
                                                                                                                          (:comment-date . "11/10/2010")
                                                                                                                          (:comment-id   . "some-comment-id2")
                                                                                                                          (:comment-text . "some second comment")))))
                                                                    (:tags . ":red:green:")
                                                                    (:desc . "updated description")
                                                                    (:level . 1)
                                                                    (:name . "updated card title")
                                                                    (:id . "some-card-id")))))
                (orgtrello-controller-compute-and-overwrite-card (current-buffer) trello-card)))
            -2))))

(ert-deftest test-orgtrello-controller-sync-buffer-with-trello-cards-cards-already-present ()
  (should (equal
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
#+PROPERTY: orgtrello-user-dude 8881
#+PROPERTY: orgtrello-user-ardumont 9991
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
* TODO updated card title                                               :orange:red:green:
  :PROPERTIES:
  :orgtrello-users: dude,ardumont
  :orgtrello-local-checksum: card-checksum-12
  :orgtrello-id: some-card-id
  :END:
  updated description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-12\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"item-checksum-12\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"item-checksum-12\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-12\"}

** COMMENT ardumont, 10/10/2010
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: comment-checksum-12
:END:
  some comment

** COMMENT tony, 11/10/2010
:PROPERTIES:
:orgtrello-id: some-comment-id2
:orgtrello-local-checksum: comment-checksum-12
:END:
  some second comment

* TODO other card name
  :PROPERTIES:
  :orgtrello-id: some-new-marker
  :orgtrello-local-checksum: card-checksum-12
  :END:

"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
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
#+PROPERTY: orgtrello-user-dude 8881
#+PROPERTY: orgtrello-user-ardumont 9991
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
* TODO some card name                                                   :orange:
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-card-comments: ardumont: some comment
:END:
some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* other card name
"
            (with-mock
              (mock (orgtrello-buffer--compute-marker-from-entry *) => "some-new-marker")
              (mock (orgtrello-buffer-card-checksum) => "card-checksum-12")
              (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-12")
              (mock (orgtrello-buffer-item-checksum) => "item-checksum-12")
              (mock (orgtrello-buffer-comment-checksum) => "comment-checksum-12")
              (let* ((trello-card0 (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                     (:member-ids . "8881,9991")
                                                                     (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                           (:comment-date . "10/10/2010")
                                                                                                                           (:comment-id   . "some-comment-id")
                                                                                                                           (:comment-text . "some comment")))
                                                                                         (orgtrello-hash-make-properties '((:comment-user . "tony")
                                                                                                                           (:comment-date . "11/10/2010")
                                                                                                                           (:comment-id   . "some-comment-id2")
                                                                                                                           (:comment-text . "some second comment")))))
                                                                     (:tags . ":red:green:")
                                                                     (:desc . "updated description")
                                                                     (:level . ,org-trello--card-level)
                                                                     (:name . "updated card title")
                                                                     (:id . "some-card-id")))))
                (orgtrello-controller-sync-buffer-with-trello-cards (current-buffer) (list trello-card0))))))))

(ert-deftest test-orgtrello-controller-sync-buffer-with-trello-cards-with-multiple-cards ()
  "Overwrite card"
  (should (equal
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
#+PROPERTY: orgtrello-user-dude 8882
#+PROPERTY: orgtrello-user-ardumont 9992
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
* TODO updated card title                                               :orange:red:green:
  :PROPERTIES:
  :orgtrello-users: dude,ardumont
  :orgtrello-local-checksum: card-checksum-1234
  :orgtrello-id: some-card-id
  :END:
  updated description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-1234\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"item-checksum-1234\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"item-checksum-1234\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-1234\"}

** COMMENT ardumont, 10/10/2010
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: comment-checksum-1234
:END:
  some comment

** COMMENT tony, 11/10/2010
:PROPERTIES:
:orgtrello-id: some-comment-id2
:orgtrello-local-checksum: comment-checksum-1234
:END:
  some second comment

* TODO other card name                                                  :green:
  :PROPERTIES:
  :orgtrello-users: dude
  :orgtrello-id: some-card-id2
  :orgtrello-local-checksum: card-checksum-1234
  :END:
  this is a description
* TODO other card name
  :PROPERTIES:
  :orgtrello-id: some-new-marker
  :orgtrello-local-checksum: card-checksum-1234
  :END:

"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
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
#+PROPERTY: orgtrello-user-dude 8882
#+PROPERTY: orgtrello-user-ardumont 9992
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
* TODO some card name                                                   :orange:
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-card-comments: ardumont: some comment
:END:
some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* other card name
"
            (with-mock
              (mock (orgtrello-buffer--compute-marker-from-entry *) => "some-new-marker")
              (mock (orgtrello-buffer-card-checksum) => "card-checksum-1234")
              (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-1234")
              (mock (orgtrello-buffer-item-checksum) => "item-checksum-1234")
              (mock (orgtrello-buffer-comment-checksum) => "comment-checksum-1234")
              (let* ((trello-card0 (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                     (:member-ids . "8882,9992")
                                                                     (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                           (:comment-date . "10/10/2010")
                                                                                                                           (:comment-id   . "some-comment-id")
                                                                                                                           (:comment-text . "some comment")))
                                                                                         (orgtrello-hash-make-properties '((:comment-user . "tony")
                                                                                                                           (:comment-date . "11/10/2010")
                                                                                                                           (:comment-id   . "some-comment-id2")
                                                                                                                           (:comment-text . "some second comment")))))
                                                                     (:tags . ":red:green:")
                                                                     (:desc . "updated description")
                                                                     (:level . ,org-trello--card-level)
                                                                     (:name . "updated card title")
                                                                     (:id . "some-card-id"))))
                     (trello-card1 (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                     (:member-ids . "8882")
                                                                     (:comments . nil)
                                                                     (:tags . ":green:")
                                                                     (:desc . "this is a description")
                                                                     (:level . ,org-trello--card-level)
                                                                     (:name . "other card name")
                                                                     (:id . "some-card-id2")))))
                (orgtrello-controller-sync-buffer-with-trello-cards (current-buffer) (list trello-card0 trello-card1))))))))

(ert-deftest test-orgtrello-controller-sync-buffer-with-trello-cards ()
  "Overwrite multiple cards."
  (should (equal
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
#+PROPERTY: orgtrello-user-dude 8883
#+PROPERTY: orgtrello-user-ardumont 9993
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
* TODO updated card title                                               :orange:red:green:
  :PROPERTIES:
  :orgtrello-users: dude,ardumont
  :orgtrello-local-checksum: card-checksum-123456
  :orgtrello-id: some-card-id
  :END:
  updated description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-123456\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\",\"orgtrello-local-checksum\":\"item-checksum-123456\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\",\"orgtrello-local-checksum\":\"item-checksum-123456\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\",\"orgtrello-local-checksum\":\"checklist-checksum-123456\"}

** COMMENT ardumont, 10/10/2010
:PROPERTIES:
:orgtrello-id: some-comment-id
:orgtrello-local-checksum: comment-checksum-123456
:END:
  some comment

** COMMENT tony, 11/10/2010
:PROPERTIES:
:orgtrello-id: some-comment-id2
:orgtrello-local-checksum: comment-checksum-123456
:END:
  some second comment

* DONE other card name                                                  :green:
  :PROPERTIES:
  :orgtrello-users: dude
  :orgtrello-id: some-card-id2
  :orgtrello-local-checksum: card-checksum-123456
  :END:
  this is a description
"
           (orgtrello-tests-with-temp-buffer-and-return-buffer-content
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
#+PROPERTY: orgtrello-user-dude 8883
#+PROPERTY: orgtrello-user-ardumont 9993
#+PROPERTY: :yellow yellow label
#+PROPERTY: :red red label
#+PROPERTY: :purple this is the purple label
#+PROPERTY: :orange orange label
#+PROPERTY: :green green label with & char
#+PROPERTY: :blue
#+PROPERTY: orgtrello-user-me ardumont
:END:
* TODO some card name                                                   :orange:
:PROPERTIES:
:orgtrello-id: some-card-id
:orgtrello-card-comments: ardumont: some comment
:END:
some description
  - [-] some checklist name :PROPERTIES: {\"orgtrello-id\":\"some-checklist-id\"}
    - [X] some item :PROPERTIES: {\"orgtrello-id\":\"some-item-id\"}
    - [ ] some other item :PROPERTIES: {\"orgtrello-id\":\"some-other-item-id\"}
  - [-] some other checklist name :PROPERTIES: {\"orgtrello-id\":\"some-other-checklist-id\"}

* other card name
:PROPERTIES:
:orgtrello-id: some-card-id2
:END:
"
            (with-mock
              (mock (orgtrello-buffer-card-checksum) => "card-checksum-123456")
              (mock (orgtrello-buffer-checklist-checksum) => "checklist-checksum-123456")
              (mock (orgtrello-buffer-item-checksum) => "item-checksum-123456")
              (mock (orgtrello-buffer-comment-checksum) => "comment-checksum-123456")
              (let* ((trello-card0 (orgtrello-hash-make-properties `((:keyword . "TODO")
                                                                     (:member-ids . "8883,9993")
                                                                     (:comments . ,(list (orgtrello-hash-make-properties '((:comment-user . "ardumont")
                                                                                                                           (:comment-date . "10/10/2010")
                                                                                                                           (:comment-id   . "some-comment-id")
                                                                                                                           (:comment-text . "some comment")))
                                                                                         (orgtrello-hash-make-properties '((:comment-user . "tony")
                                                                                                                           (:comment-date . "11/10/2010")
                                                                                                                           (:comment-id   . "some-comment-id2")
                                                                                                                           (:comment-text . "some second comment")))))
                                                                     (:tags . ":red:green:")
                                                                     (:desc . "updated description")
                                                                     (:level . ,org-trello--card-level)
                                                                     (:name . "updated card title")
                                                                     (:id . "some-card-id"))))
                     (trello-card1 (orgtrello-hash-make-properties `((:keyword . "DONE")
                                                                     (:member-ids . "8883")
                                                                     (:tags . ":green:")
                                                                     (:desc . "this is a description")
                                                                     (:level . ,org-trello--card-level)
                                                                     (:name . "other card name")
                                                                     (:id . "some-card-id2")))))
                (orgtrello-controller-sync-buffer-with-trello-cards (current-buffer) (list trello-card0 trello-card1))))))))

(ert-deftest test-orgtrello-controller-user-account-from-config-file ()
  (should (string= "config" (orgtrello-controller-user-account-from-config-file "/home/user/.emacs.d/.trello/config.el")))
  (should (string= "ardumont" (orgtrello-controller-user-account-from-config-file "/home/user/.emacs.d/.trello/ardumont.el"))))

(ert-deftest test-orgtrello-controller-list-user-accounts ()
  (should (equal '("ardumont" "config" "orgmode")
                 (orgtrello-controller-list-user-accounts '("/home/user/.emacs.d/.trello/ardumont.el" "/home/user/.emacs.d/.trello/config.el" "/home/user/.emacs.d/.trello/orgmode.el"))))
  (should (equal '("foobar")
                 (orgtrello-controller-list-user-accounts '("/home/user/.emacs.d/.trello/foobar.el")))))


(ert-deftest test-orgtrello-controller-set-account ()
  (should (equal :ok
                 (with-mock
                  (mock (orgtrello-buffer-me) => "some-account")
                  (orgtrello-controller-set-account))))
  (should (equal :ok
                 (with-mock
                  (mock (orgtrello-buffer-me) => nil)
                  (mock (orgtrello-controller-user-config-files) => :some-config-file)
                  (mock (orgtrello-controller-list-user-accounts :some-config-file) => '(account0))
                  (orgtrello-controller-set-account))))
  (should (equal :ok
                 (with-mock
                  (mock (orgtrello-buffer-me) => nil)
                  (mock (orgtrello-controller-user-config-files) => :some-config-file)
                  (mock (orgtrello-controller-list-user-accounts :some-config-file) => '(:account0 :account1))
                  (mock (orgtrello-controller--choose-account '(:account0 :account1)) => :account0)
                  (orgtrello-controller-set-account)))))

(provide 'org-trello-controller-test)
;;; org-trello-controller-test.el ends here
