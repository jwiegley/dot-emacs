(ert-deftest org-cliplink-elide-string-test ()
  (should (not (org-cliplink-elide-string nil 0)))
  (let ((max-length 5))
    (should (equal "test" (org-cliplink-elide-string "test" max-length)))
    (should (equal "hello" (org-cliplink-elide-string "hello" max-length)))
    (should (equal "tr..." (org-cliplink-elide-string "trinitrotoluene" max-length))))
  (let ((max-length 3))
    (should (equal "..." (org-cliplink-elide-string "hello" max-length)))))

(ert-deftest org-cliplink-straight-string-test ()
  (should (not (org-cliplink-straight-string nil)))
  (should (equal (org-cliplink-straight-string "   hello    world   ")
                 "hello world")))

(ert-deftest org-cliplink-join-string-test ()
  (should (equal "foo bar buzz"
                 (org-cliplink-join-string (list "foo" "bar" "buzz")))))
