(require 'org-trello)
(require 'ert)
(require 'el-mock)

(ert-deftest test-org-trello-clean-org-trello-data ()
  (should (eq :cleanup-done
              (with-mock
                (mock (orgtrello-controller-do-cleanup-from-buffer 'global) => :cleanup-done)
                (org-trello-clean-org-trello-data)))))

(ert-deftest test-org-trello-apply ()
  (should (eq :result-apply-deferred
              (with-mock
                (mock (current-buffer) => :buffer)
                (mock (orgtrello-deferred-eval-computation
                       '((:computation :prefix-log) :buffer :nolog-p :prefix-log)
                       '('org-trello--apply-deferred-with-data
                         'org-trello--after-apply)
                       :prefix-log) => :result-apply-deferred)
                (org-trello-apply ' (:computation :prefix-log) :save-buffer-p :nolog-p)))))

(ert-deftest test-org-trello--after-apply ()
  ;; should save and log
  (should (string= "org-trello - do something... DONE."
                   (let ((orgtrello-log-level orgtrello-log-info))
                     (with-mock
                       (mock (orgtrello-buffer-save-buffer :buffer-to-save) => :done)
                       (org-trello--after-apply '(:result-comp :comp :buffer-to-save nil "do something..."))))))
  ;; do nothing
  (should-not (org-trello--after-apply '(:result-comp :comp nil 'no-log "do something..."))))

(ert-deftest test-org-trello--apply-deferred-with-data ()
  (should (equal '(:result-computation :computation :buffer-to-save :nolog-flag :prefix-log)
                 (with-mock
                   (mock (org-trello--apply-deferred-with-quit :computation) => :result-computation)
                   (org-trello--apply-deferred-with-data '(:computation :buffer-to-save :nolog-flag :prefix-log))))))

(ert-deftest test-org-trello--apply-deferred ()
  (should (equal 11
                 (org-trello--apply-deferred '((lambda (a b) (+ a b)) 1 10)))))

(ert-deftest test-org-trello--apply-deferred-with-quit ()
  (should (equal 30
                 (org-trello--apply-deferred-with-quit '((lambda (a b) (+ a b)) 10 20)))))

(ert-deftest test-org-trello-version ()
  (should (string= "org-trello - version: xyz"
                   (let ((org-trello--version "xyz"))
                     (org-trello-version)))))

(ert-deftest test-org-trello-abort-sync ()
  (should (equal :cancel-done
                 (with-mock
                   (mock (deferred:clear-queue) => :clear)
                   (mock (orgtrello-log-msg orgtrello-log-info "Cancel actions done!") => :cancel-done)
                   (org-trello-abort-sync)))))

(ert-deftest test-org-trello-log-strict-checks-and-do ()
  (should (equal :res
                 (with-mock
                   (mock (orgtrello-action-msg-controls-or-actions-then-do
                          :action-label
                          '(orgtrello-controller-migrate-user-setup
                            orgtrello-controller-set-account
                            orgtrello-controller-load-keys
                            orgtrello-controller-control-keys
                            orgtrello-controller-setup-properties
                            orgtrello-controller-control-properties)
                          :action-fn) => :res)
                   (org-trello-log-strict-checks-and-do :action-label :action-fn)))))

(ert-deftest test-org-trello-log-light-checks-and-do ()
  (should (equal :res
                 (with-mock
                   (mock (orgtrello-action-msg-controls-or-actions-then-do
                          :action-label
                          nil
                          :action-fn) => :res)
                   (org-trello-log-light-checks-and-do :action-label :action-fn 'no-check))))
  (should (equal :res2
                 (with-mock
                   (mock (orgtrello-action-msg-controls-or-actions-then-do
                          :action-label
                          '(orgtrello-controller-migrate-user-setup
                            orgtrello-controller-set-account
                            orgtrello-controller-load-keys
                            orgtrello-controller-control-keys
                            orgtrello-controller-setup-properties)
                          :action-fn) => :res2)
                   (org-trello-log-light-checks-and-do :action-label :action-fn)))))

(ert-deftest test-org-trello-add-card-comment ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello-apply '(org-trello-log-strict-checks-and-do
                                             "Remove current comment at point"
                                             orgtrello-controller-do-delete-card-comment)) => :res)
                   (org-trello-add-card-comment 'from))))
  (should (equal :res2
                 (with-mock
                   (mock (org-trello-apply '(org-trello-log-strict-checks-and-do
                                             "Add card comment"
                                             orgtrello-controller-do-add-card-comment)) => :res2)
                   (org-trello-add-card-comment)))))

(ert-deftest test-org-trello-delete-card-comment ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-strict-checks-and-do "Remove current comment at point" orgtrello-controller-do-delete-card-comment)) => :res)
                   (org-trello-delete-card-comment)))))

(ert-deftest test-org-trello-show-board-labels ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello-apply '(org-trello-log-strict-checks-and-do "Display current board's labels" orgtrello-controller-do-show-board-labels)) => :res)
                   (org-trello-show-board-labels)))))

(ert-deftest test-org-trello-sync-card ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred
                          '(org-trello-log-strict-checks-and-do "Request 'sync entity with structure from trello" orgtrello-controller-checks-then-sync-card-from-trello)) => :res)
                   (org-trello-sync-card 'from))))
  (should (equal :res2
                 (with-mock
                   (mock (org-trello--apply-deferred
                          '(org-trello-log-strict-checks-and-do "Request 'sync entity with structure to trello" orgtrello-controller-checks-then-sync-card-to-trello)) => :res2)
                   (org-trello-sync-card)))))

(ert-deftest test-org-trello-sync-comment ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-strict-checks-and-do "Remove current comment at point" orgtrello-controller-do-delete-card-comment)) => :res)
                   (org-trello-sync-comment 'from))))
  (should (equal :res2
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-strict-checks-and-do "Sync comment to trello" orgtrello-controller-do-sync-card-comment)) => :res2)
                   (org-trello-sync-comment)))))

(ert-deftest test-org-trello-sync-buffer ()
  (should
   (equal :res
          (with-mock
            (mock (org-trello--apply-deferred
                   '(org-trello-log-strict-checks-and-do "Request 'sync org buffer from trello board'" orgtrello-controller-do-sync-buffer-from-trello)) => :res)
            (org-trello-sync-buffer 'from))))
  (should
   (equal :res2
          (with-mock
            (mock (org-trello--apply-deferred '(org-trello-log-strict-checks-and-do "Request 'sync org buffer to trello board'" orgtrello-controller-do-sync-buffer-to-trello)) => :res2)
            (org-trello-sync-buffer)))))

(ert-deftest test-org-trello-kill-entity ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-strict-checks-and-do "Delete all cards" orgtrello-controller-do-delete-entities)) => :res)
                   (org-trello-kill-entity 'from))))
  (should (equal :res2
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-strict-checks-and-do "Delete entity at point (card/checklist/item)" orgtrello-controller-checks-then-delete-simple)) => :res2)
                   (org-trello-kill-entity)))))

(ert-deftest test-org-trello-kill-cards ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-strict-checks-and-do "Delete Cards" orgtrello-controller-do-delete-entities)) => :res)
                   (org-trello-kill-cards)))))

(ert-deftest test-org-trello-archive-card ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-strict-checks-and-do "Archive card at point..." orgtrello-controller-checks-and-do-archive-card)) => :res)
                   (org-trello-archive-card)))))

(ert-deftest test-org-trello-archive-cards ()
  (should (equal :res
                 (with-mock
                   (mock (org-map-entries 'org-trello-archive-card "/DONE" 'file) => :res)
                   (org-trello-archive-cards)))))

(ert-deftest test-org-trello-install-key-and-token ()
  (should (equal :res
                 (with-mock
                   (mock (orgtrello-controller-do-install-key-and-token) => :res)
                   (org-trello-install-key-and-token)))))

(ert-deftest test-org-trello-install-board-metadata ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-light-checks-and-do "Install boards and lists" orgtrello-controller-do-install-board-and-lists)) => :res)
                   (org-trello-install-board-metadata)))))

(ert-deftest test-org-trello-update-board-metadata ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-light-checks-and-do "Update board information" orgtrello-controller-do-update-board-metadata)) => :res)
                   (org-trello-update-board-metadata)))))

(ert-deftest test-org-trello-jump-to-trello-card ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello-apply '(org-trello-log-strict-checks-and-do "Jump to board" orgtrello-controller-jump-to-board)) => :res)
                   (org-trello-jump-to-trello-card 'from))))
  (should (equal :res2
                 (with-mock
                   (mock (org-trello-apply '(org-trello-log-strict-checks-and-do "Jump to card" orgtrello-controller-jump-to-card)) => :res2)
                   (org-trello-jump-to-trello-card)))))

(ert-deftest test-org-trello-jump-to-trello-board ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello-apply '(org-trello-log-strict-checks-and-do "Jump to board" orgtrello-controller-jump-to-board)) => :res)
                   (org-trello-jump-to-trello-board)))))

(ert-deftest test-org-trello-assign-me ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello-apply
                          '(org-trello-log-light-checks-and-do "Unassign me from card" orgtrello-controller-do-unassign-me)
                          'do-save-buffer-after-computation) => :res)
                   (org-trello-assign-me 'unassign))))
  (should (equal :res2
                 (with-mock
                   (mock (org-trello-apply
                          '(org-trello-log-light-checks-and-do "Assign myself to card" orgtrello-controller-do-assign-me)
                          'do-save-buffer-after-computation) => :res2)
                   (org-trello-assign-me)))))

(ert-deftest test-org-trello-toggle-assign-me ()
  (should (equal :res-toggle-assign-me
                 (with-mock
                   (mock (org-trello-apply
                          '(org-trello-log-light-checks-and-do "Toggle assign me to card" orgtrello-controller-toggle-assign-unassign-oneself)
                          'do-save-buffer-after-computation) => :res-toggle-assign-me)
                   (org-trello-toggle-assign-me)))))

(ert-deftest test-org-trello-toggle-assign-user ()
  (should (equal :res-user-assigned
                 (with-mock
                   (mock (org-trello-apply
                          '(org-trello-log-light-checks-and-do "Toggle assign one user to a card" orgtrello-controller-toggle-assign-user)
                          'do-save-buffer-after-computation) => :res-user-assigned)
                   (org-trello-toggle-assign-user)))))

(ert-deftest test-org-trello-check-setup ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello-apply '(org-trello-log-strict-checks-and-do "Checking setup." orgtrello-controller-check-trello-connection) nil 'no-log) => :res)
                   (org-trello-check-setup)))))

(ert-deftest test-org-trello-delete-setup ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello-apply
                          '(org-trello-log-strict-checks-and-do "Delete current org-trello setup" orgtrello-controller-delete-setup)
                          'do-save-buffer-after-computation) => :res)
                   (org-trello-delete-setup)))))

(ert-deftest test-org-trello-help-describing-bindings ()
  (should (equal :result-help
                 (let ((org-trello-current-prefix-keybinding "C-c z"))
                   (with-mock
                     (mock (orgtrello-setup-help-describing-bindings-template
                            org-trello-current-prefix-keybinding
                            org-trello-interactive-command-binding-couples) => :something)
                     (mock (org-trello-apply `(message :something) nil 'no-log) => :result-help)
                     (org-trello-help-describing-bindings))))))

(ert-deftest test-org-trello-create-board-and-install-metadata ()
  (should (equal :res
                 (with-mock
                   (mock (org-trello--apply-deferred '(org-trello-log-light-checks-and-do "Create board and lists" orgtrello-controller-do-create-board-and-install-metadata)) => :res)
                   (org-trello-create-board-and-install-metadata)))))

(ert-deftest test-org-trello--bug-report ()
  (should (string= "Please:
- Describe your problem with clarity and conciceness (cf. https://www.gnu.org/software/emacs/manual/html_node/emacs/Understanding-Bug-Reporting.html)
- Explicit your installation choice (melpa, marmalade, el-get, tarball, git clone...).
- Activate `'trace`' in logs for more thorough output in *Message* buffer: (custom-set-variables '(orgtrello-log-level orgtrello-log-trace)).
- A scrambled sample (of the user's and board's ids) of your org-trello buffer with problems.
- Report the following message trace inside your issue.

System information:
- system-type: system-type
- locale-coding-system: locale-coding-system
- emacs-version: emacs-version
- org version: org-version
- org-trello version: org-trello-version
- org-trello path: /path/to/org-trello
- request-backend: curl
- kill-whole-line: something"
                   (let ((system-type "system-type")
                         (locale-coding-system "locale-coding-system")
                         (org-trello--version "org-trello-version")
                         (request-backend "curl")
                         (kill-whole-line 'something))
                     (with-mock
                       (mock (emacs-version) => "emacs-version")
                       (mock (org-version) => "org-version")
                       (mock (find-library-name "org-trello") => "/path/to/org-trello")
                       (org-trello--bug-report))))))

(ert-deftest test-org-trello-bug-report ()
  (should (equal :res
                 (with-mock
                   (mock (browse-url "https://github.com/org-trello/org-trello/issues/new") => :opened)
                   (mock (org-trello--bug-report) => :message)
                   (mock (orgtrello-log-msg orgtrello-log-info :message) => :res)
                   (org-trello-bug-report 'browse))))
  (should (equal :res
                 (with-mock
                   (mock (org-trello--bug-report) => :message2)
                   (mock (orgtrello-log-msg orgtrello-log-info :message2) => :res)
                   (org-trello-bug-report)))))

(provide 'org-trello-test)
