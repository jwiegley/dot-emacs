(require 'org-trello-utils)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-utils-replace-in-string ()
  (should (equal "something-to-be-replaced" (orgtrello-utils-replace-in-string " " "-" "something to be replaced")))
  (should (equal "something-to-be-replaced" (orgtrello-utils-replace-in-string "###" "-" "something###to###be###replaced"))))

(ert-deftest test-orgtrello-utils-symbol ()
  (should (equal ""      (orgtrello-utils-symbol " "  0)))
  (should (equal "*"     (orgtrello-utils-symbol "*"  1)))
  (should (equal "****"  (orgtrello-utils-symbol "**" 2)))
  (should (equal "   "   (orgtrello-utils-symbol " "  3))))

(ert-deftest test-orgtrello-utils-space ()
  (should (equal ""    (orgtrello-utils-space 0)))
  (should (equal " "   (orgtrello-utils-space 1)))
  (should (equal "  "  (orgtrello-utils-space 2)))
  (should (equal "   " (orgtrello-utils-space 3))))

(provide 'org-trello-utils-test)
;;; org-trello-utils-test.el ends here
