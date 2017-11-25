(require 'org-trello-input)

(ert-deftest test-orgtrello-input-ido-read-string-completion ()
  (should (eq :res-with-ido
              (let ((org-trello-input-completion-mechanism 'default))
                (with-mock
                  (mock (ido-completing-read :prompt :choices nil 'do-match) => :res-with-ido)
                  (orgtrello-input-read-string-completion :prompt :choices))))))

(if (boundp 'helm-comp-read)
    (ert-deftest test-orgtrello-input-helm-read-string-completion ()
      (should (eq :res-with-helm
                  (let ((org-trello-input-completion-mechanism 'other))
                    (with-mock
                      (mock (helm-comp-read :prompt :choices) => :res-with-helm)
                      (orgtrello-input-read-string-completion :prompt :choices)))))))

(ert-deftest test-orgtrello-input-read-not-empty ()
  (should (equal "something"
                 (with-mock
                   (mock (read-string "prompt: ") => " something ")
                   (orgtrello-input-read-not-empty "prompt: ")))))

(ert-deftest test-orgtrello-input-read-string ()
  (should (equal :something
                 (with-mock
                   (mock (read-string "prompt: ") => :something)
                   (orgtrello-input-read-string "prompt: ")))))

(ert-deftest test-orgtrello-input-confirm ()
  (should (equal 'y
                 (with-mock
                   (mock (y-or-n-p "prompt: ") => 'y)
                   (orgtrello-input-confirm "prompt: "))))
  (should-not (with-mock
                (mock (y-or-n-p "prompt: ") => nil)
                (orgtrello-input-confirm "prompt: "))))
