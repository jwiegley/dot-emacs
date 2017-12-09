(ert-deftest message ()
  ""
  (should
   (string=
    (paradox--format-message 'question '(1) '(1 2))
    "Install 1 package, and Delete 2 packages? "))
  (should
   (string=
    (paradox--format-message 'question nil '(1 2))
    "Delete 2 packages? "))
  (should
   (string=
    (paradox--format-message 'question '(1) nil)
    "Install 1 package? "))
  (should
   (string=
    (paradox--format-message nil '(1) '(1 2))
    "Installed 1 package, and Deleted 2 packages."))
  (should
   (string=
    (paradox--format-message nil nil '(1 2))
    "Deleted 2 packages."))
  (should
   (string=
    (paradox--format-message nil '(1) nil)
    "Installed 1 package.")))

(ert-deftest sanity ()
  ""
  (let ((paradox-github-token t))
    (should (progn (paradox-list-packages nil) t)))
  (let ((paradox-github-token "okokok"))
    (should-error (progn (paradox-list-packages nil) t))))
