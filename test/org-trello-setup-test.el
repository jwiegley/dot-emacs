(require 'org-trello-setup)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-setup-users ()
  (should (eq :something
              (let ((org-trello--hmap-users-id-name :something))
                (orgtrello-setup-users))))
  (should-not (let ((org-trello--hmap-users-id-name))
                (orgtrello-setup-users))))

(ert-deftest test-orgtrello-setup-org-trello-on-p ()
  (should (eq t
              (let ((major-mode 'org-mode)
                    (org-trello--mode-activated-p t))
                (orgtrello-setup-org-trello-on-p))))
  (should-not (let ((major-mode 'other-mode)
                    (org-trello--mode-activated-p t))
                (orgtrello-setup-org-trello-on-p)))
  (should-not (let ((major-mode 'org-mode)
                    (org-trello--mode-activated-p))
                (orgtrello-setup-org-trello-on-p)))
  (should-not (let ((major-mode 'other-mode)
                    (org-trello--mode-activated-p))
                (orgtrello-setup-org-trello-on-p))))

(ert-deftest test-orgtrello-setup-install-local-keybinding-map ()
  (should (equal '((lambda nil (interactive)) (lambda nil (interactive)))
                 (orgtrello-setup-install-local-keybinding-map "C-c o"
                                                               "C-c x"
                                                               '(((lambda () (interactive)) "a" "description command a")
                                                                 ((lambda () (interactive)) "b" "description command b"))))))

(ert-deftest test-orgtrello-setup-set-binding ()
  (should (string=
           "C-c x"
           (let ((org-trello-current-prefix-keybinding "C-c a"))
             (with-mock
               (mock (orgtrello-setup-install-local-keybinding-map
                      "C-c a"
                      "C-c x"
                      org-trello-interactive-command-binding-couples) => :new-binding-set)
               (orgtrello-setup-set-binding 'org-trello-current-prefix-keybinding "C-c x")))))
  (should (string=
           "C-c y"
           (let ((org-trello-default-prefix-keybinding "C-c X"))
             (with-mock
               (mock (orgtrello-setup-install-local-keybinding-map
                      "C-c X"
                      "C-c y"
                      org-trello-interactive-command-binding-couples) => :new-binding-set)
               (orgtrello-setup-set-binding 'org-trello-unbound-var "C-c y")))))
  (should-not (orgtrello-setup-set-binding 'org-trello-current-prefix-keybinding nil)))

(ert-deftest test-orgtrello-setup-remove-local-keybinding-map ()
  (should (equal
           '(:result-defined-binding)
           (with-mock
             (mock (kbd "C-c X z") => :binding)
             (mock (define-key org-trello-mode-map :binding nil) => :result-defined-binding)
             (orgtrello-setup-remove-local-keybinding-map "C-c X" '(('command-fn "z" "doc description")))))))

(ert-deftest test-orgtrello-setup-help-describing-bindings-template ()
  (should (string= "C-c o a - M-x some-action - some-description
C-c o 2 - M-x action2 - some other description"
                   (orgtrello-setup-help-describing-bindings-template
                    "C-c o"
                    '((some-action "a" "some-description")
                      (action2 "2" "some other description")))))
  (should (string=
           "C-c z v - M-x org-trello-version - Display the current version installed.
C-c z i - M-x org-trello-install-key-and-token - Install the keys and the access-token.
C-c z I - M-x org-trello-install-board-metadata - Select the board and attach the todo, doing and done list.
C-c z u - M-x org-trello-update-board-metadata - Update the buffer's trello board metadata.
C-c z b - M-x org-trello-create-board-and-install-metadata - Create interactively a board and attach the newly created trello board with the current org file.
C-c z d - M-x org-trello-check-setup - Check that the setup is ok. If everything is ok, will simply display 'Setup ok!'.
C-c z D - M-x org-trello-delete-setup - Clean up the org buffer from all org-trello informations.
C-c z c - M-x org-trello-sync-card - Create/Update a complete card.
C-c z s - M-x org-trello-sync-buffer - Synchronize the org-mode file to the trello board (org-mode -> trello). With prefix C-u, sync-from-trello (org-mode <- trello).
C-c z A - M-x org-trello-archive-cards - Archive all DONE cards.
C-c z g - M-x org-trello-abort-sync - Abort synchronization activities.
C-c z k - M-x org-trello-kill-entity - Kill the entity (and its arborescence tree) from the trello board and the org buffer.
C-c z K - M-x org-trello-kill-cards - Kill all the entities (and their arborescence tree) from the trello board and the org buffer.
C-c z a - M-x org-trello-toggle-assign-me - Toggle assign oneself to the card. If not assigned, assign and vice versa.
C-c z t - M-x org-trello-toggle-assign-user - Toggle assign one user to a card. If not assigned, assign and vice versa.
C-c z C - M-x org-trello-add-card-comment - Add a comment to the card. With C-u modifier, remove the current card's comment.
C-c z U - M-x org-trello-sync-comment - Sync a comment to trello. With C-u modifier, remove the current card's comment.
C-c z l - M-x org-trello-show-board-labels - Display the board's labels in a pop-up buffer.
C-c z j - M-x org-trello-jump-to-trello-card - Jump to card in browser.
C-c z J - M-x org-trello-jump-to-trello-board - Open the browser to your current trello board.
C-c z B - M-x org-trello-bug-report - Prepare a bug report message. With C-u modifier, opens a new issue in org-trello's github tracker too.
C-c z h - M-x org-trello-help-describing-bindings - This help message."
           (orgtrello-setup-help-describing-bindings-template
            "C-c z"
            org-trello-interactive-command-binding-couples))))

(ert-deftest test-orgtrello-setup-compute-url ()
  (should (string= "https://trello.com/some-uri"
                   (orgtrello-setup-compute-url "/some-uri"))))

(ert-deftest test-orgtrello-setup-startup-message ()
  (should (equal "Hello master, help is `M-x org-trello-help-describing-bindings RET' or `C-c o h'."
                 (orgtrello-setup-startup-message "C-c o"))))

(ert-deftest test-orgtrello-setup-remove-local-prefix-mode-keybinding ()
  (should (equal :res
                 (with-mock
                   (mock (orgtrello-setup-remove-local-keybinding-map
                          :keybinding
                          org-trello-interactive-command-binding-couples) => :res)
                   (orgtrello-setup-remove-local-prefix-mode-keybinding :keybinding)))))

(ert-deftest test-orgtrello-setup-install-local-prefix-mode-keybinding ()
  (should (equal :res
                 (with-mock
                   (mock (orgtrello-setup-install-local-keybinding-map
                          :keybinding
                          :keybinding
                          org-trello-interactive-command-binding-couples) => :res)
                   (orgtrello-setup-install-local-prefix-mode-keybinding :keybinding)))))

(ert-deftest test-orgtrello-setup-user-logged-in ()
  (should (equal :user-bar
                 (let ((org-trello--user-logged-in :user-bar))
                   (orgtrello-setup-user-logged-in)))))

(ert-deftest test-orgtrello-setup-set-user-logged-in ()
  (should (equal
           '(:user-foobar
             :new-user
             :new-user)
           (let ((org-trello--user-logged-in :user-foobar))
             `(,(orgtrello-setup-user-logged-in)
               ,(orgtrello-setup-set-user-logged-in :new-user)
               ,(orgtrello-setup-user-logged-in))))))

(ert-deftest test-orgtrello-setup-display-current-buffer-setup ()
  (should (equal
           (list :users-id-name :1
                 :users-name-id :2
                 :user-logged-in :3
                 :org-keyword-trello-list-names :4
                 :org-keyword-id-name :5)
           (let ((org-trello--hmap-users-id-name :1)
                 (org-trello--hmap-users-name-id :2)
                 (org-trello--user-logged-in :3)
                 (org-trello--org-keyword-trello-list-names :4)
                 (org-trello--hmap-list-orgkeyword-id-name :5))
             (orgtrello-setup-display-current-buffer-setup)))))

(provide 'org-trello-setup-test)
;;; org-trello-setup-test.el ends here
