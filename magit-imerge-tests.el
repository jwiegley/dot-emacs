;;; magit-imerge-tests.el --- tests for Magit

;; Copyright (C) 2017  Kyle Meyer
;;
;; License: GPLv3

;;; Code:

(require 'cl-lib)
(require 'dash)
(require 'ert)

(require 'magit)
(require 'magit-imerge)

;; Modified from magit-tests.el.
(defmacro magit-imerge-with-test-repository (&rest body)
  (declare (indent 0) (debug t))
  (let ((dir (make-symbol "dir")))
    `(let ((,dir (file-name-as-directory (make-temp-file "magit-imerge-" t)))
           (process-environment process-environment))
       (push "GIT_AUTHOR_NAME=A U Thor" process-environment)
       (push "GIT_AUTHOR_EMAIL=a.u.thor@example.com" process-environment)
       (push "GIT_EDITOR=cat" process-environment)
       (condition-case err
           (cl-flet ((modify (file &optional content)
                             (write-region
                              (insert (or content
                                          (make-temp-name "content")))
                              nil file)))
             (cl-letf (((symbol-function #'message) (lambda (&rest _))))
               (let ((default-directory ,dir)
                     (magit-list-refs-sortby nil)
                     (inhibit-magit-refresh t))
                 (magit-git "init" ".")
                 (magit-git "commit" "-m" "root" "--allow-empty")
                 ;; Branch "a" .
                 (magit-git "checkout" "-b" "a")
                 (modify "foo")
                 (magit-git "add" "foo")
                 (magit-git "commit" "-m" "add foo")
                 (modify "foo")
                 (magit-git "add" "foo")
                 (magit-git "commit" "-m" "update foo")
                 ;; Branch "b", which doesn't have conflicts with "a".
                 (magit-git "checkout" "-b" "b" "master")
                 (modify "bar")
                 (magit-git "add" "bar")
                 (magit-git "commit" "-m" "add bar")
                 (modify "bar")
                 (magit-git "add" "bar")
                 (magit-git "commit" "-m" "update bar")
                 ;; Branch "c", which does have conflicts with "a".
                 (magit-git "checkout" "-b" "c" "master")
                 (modify "foo")
                 (magit-git "add" "foo")
                 (magit-git "commit" "-m" "add foo on c")
                 (modify "foo")
                 (magit-git "add" "foo")
                 (magit-git "commit" "-m" "update foo on c")
                 (modify "foo")
                 (magit-git "add" "foo")
                 (magit-git "commit" "-m" "update foo on c, again")
                 (magit-git "checkout" "master")
                 ,@body)))
         (error (message "Keeping test directory:\n  %s" ,dir)
                (signal (car err) (cdr err))))
       (delete-directory ,dir t))))

(defun magit-imerge-tests-wait ()
  (while (and magit-this-process
              (eq (process-status magit-this-process) 'run))
    (sleep-for 0.01)))

(ert-deftest magit-imerge-names ()
  (magit-imerge-with-test-repository
    (should-not (magit-imerge-names))
    (magit-git "checkout" "a")
    (magit-git "imerge" "merge" "b")
    (should (equal (magit-imerge-names) (list "b")))
    (magit-git "checkout" "b")
    (magit-git "imerge" "merge" "a")
    (should (equal (magit-imerge-names) (list "a" "b")))
    (magit-git "imerge" "continue" "--name=b")
    (magit-git "imerge" "finish")
    (should (equal (magit-imerge-names) (list "a")))
    (magit-git "checkout" "a")
    (magit-git "imerge" "merge" "--name=foo/ctoa" "c")
    (should (equal (magit-imerge-names) (list "a" "foo/ctoa")))))

(ert-deftest magit-imerge-state ()
  (magit-imerge-with-test-repository
    (should-not (magit-imerge-state "null"))
    (magit-git "checkout" "a")
    (magit-git "imerge" "merge" "b")
    (let ((state (magit-imerge-state "b")))
      (should (equal (cdr (assq 'tip1 state)) "a"))
      (should (equal (cdr (assq 'tip2 state)) "b"))
      (should (equal (cdr (assq 'goal state)) "merge"))
      (should (equal (cdr (assq 'branch state)) "a")))
    (magit-git "checkout" "a")
    (magit-git "imerge" "rebase" "--name=aonc" "--branch=new" "c")
    (let ((state (magit-imerge-state "aonc")))
      (should (equal (cdr (assq 'tip1 state)) "c"))
      (should (equal (cdr (assq 'tip2 state)) "a"))
      (should (equal (cdr (assq 'goal state)) "rebase"))
      (should (equal (cdr (assq 'branch state)) "new")))))

(ert-deftest magit-imerge-current-name ()
  (magit-imerge-with-test-repository
    (should-not (magit-imerge-current-name))
    (magit-git "checkout" "a")
    (magit-git "imerge" "merge" "b")
    (should (equal (magit-imerge-current-name) "b"))
    (magit-git "checkout" "a")
    (magit-git "imerge" "rebase" "--name=aonc" "--branch=new" "c")
    (should (equal (magit-imerge-current-name) "aonc"))))

(ert-deftest magit-imerge-merge ()
  (magit-imerge-with-test-repository
    (magit-git "checkout" "a")
    (magit-imerge-merge "b")
    (magit-imerge-tests-wait)
    (let ((state (magit-imerge-state "b")))
      (should state)
      (should (equal (cdr (assq 'tip1 state)) "a"))
      (should (equal (cdr (assq 'tip2 state)) "b"))
      (should (equal (cdr (assq 'goal state)) "merge"))
      (should (equal (cdr (assq 'branch state)) "a")))
    (magit-git "checkout" "a")
    (magit-imerge-merge "c" (list "--name=cmerge"
                                  "--goal=full"
                                  "--branch=new"))
    (magit-imerge-tests-wait)
    (let ((state (magit-imerge-state "cmerge")))
      (should state)
      (should (equal (cdr (assq 'goal state)) "full"))
      (should (equal (cdr (assq 'branch state)) "new")))))

(ert-deftest magit-imerge-rebase ()
  (magit-imerge-with-test-repository
    (magit-git "checkout" "a")
    (magit-imerge-rebase "b")
    (magit-imerge-tests-wait)
    (let ((state (magit-imerge-state "a")))
      (should state)
      (should (equal (cdr (assq 'tip1 state)) "b"))
      (should (equal (cdr (assq 'tip2 state)) "a"))
      (should (equal (cdr (assq 'goal state)) "rebase"))
      (should (equal (cdr (assq 'branch state)) "a")))
    (magit-git "checkout" "a")
    (magit-imerge-rebase "c" (list "--name=aonc"
                                   "--goal=full"
                                   "--branch=new"))
    (magit-imerge-tests-wait)
    (let ((state (magit-imerge-state "aonc")))
      (should state)
      (should (equal (cdr (assq 'goal state)) "full"))
      (should (equal (cdr (assq 'branch state)) "new")))))

(ert-deftest magit-imerge-revert:commit ()
  (magit-imerge-with-test-repository
    (magit-git "checkout" "a")
    (magit-imerge-revert "a^")
    (magit-imerge-tests-wait)
    (let ((state (magit-imerge-state "a")))
      (should state)
      (should (equal (cdr (assq 'tip1 state)) "a"))
      (should (equal (cdr (assq 'goal state)) "revert"))
      (should (equal (cdr (assq 'branch state)) "a")))))

(ert-deftest magit-imerge-revert:range ()
  (magit-imerge-with-test-repository
    (magit-git "checkout" "c")
    (magit-imerge-revert "HEAD~3..HEAD~1")
    (magit-imerge-tests-wait)
    (let ((state (magit-imerge-state "c")))
      (should state)
      (should (equal (cdr (assq 'tip1 state)) "c"))
      (should (equal (cdr (assq 'goal state)) "revert"))
      (should (equal (cdr (assq 'branch state)) "c")))))

(ert-deftest magit-imerge-drop:commit ()
  (magit-imerge-with-test-repository
    (magit-git "checkout" "a")
    (magit-imerge-drop "a^")
    (magit-imerge-tests-wait)
    (let ((state (magit-imerge-state "a")))
      (should state)
      (should (equal (cdr (assq 'tip1 state)) "a"))
      (should (equal (cdr (assq 'base (cdr (assq 'goalopts state))))
                     (magit-rev-parse "a~2")))
      (should (equal (cdr (assq 'goal state)) "drop"))
      (should (equal (cdr (assq 'branch state)) "a")))))

(ert-deftest magit-imerge-drop:range ()
  (magit-imerge-with-test-repository
    (magit-git "checkout" "c")
    (magit-imerge-drop "HEAD~3..HEAD~1")
    (magit-imerge-tests-wait)
    (let ((state (magit-imerge-state "c")))
      (should state)
      (should (equal (cdr (assq 'tip1 state)) "c"))
      (should (equal (cdr (assq 'base (cdr (assq 'goalopts state))))
                     (magit-rev-parse "c~3")))
      (should (equal (cdr (assq 'goal state)) "drop"))
      (should (equal (cdr (assq 'branch state)) "c")))))

(ert-deftest magit-imerge-abort ()
  (magit-imerge-with-test-repository
    (magit-git "checkout" "a")
    (magit-imerge-merge "c")
    (magit-imerge-tests-wait)
    (should (magit-anything-unmerged-p))
    (should (equal (magit-get-current-branch) "imerge/c"))
    (let ((magit-no-confirm '(abort-merge)))
      (magit-imerge-abort))
    (magit-imerge-tests-wait)
    (should-not (magit-anything-unmerged-p))
    (should (equal (magit-get-current-branch) "a"))))

(ert-deftest magit-imerge-finish ()
  (magit-imerge-with-test-repository
    (magit-git "checkout" "a")
    (magit-imerge-merge "b")
    (magit-imerge-tests-wait)
    (magit-imerge-finish (list "--branch=new" "--goal=rebase"))
    (magit-imerge-tests-wait)
    (should (equal (magit-get-current-branch) "new"))
    (should-not (magit-rev-verify "HEAD^2"))))

(provide 'magit-imerge-tests)
;;; magit-imerge-tests.el ends here
