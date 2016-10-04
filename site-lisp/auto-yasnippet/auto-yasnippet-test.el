(require 'ert)

(ert-deftest aya--parse ()
  (should (equal (aya--parse "public void `Foo'TestMethod(`Type' param1, `Type' param2)")
                 '("public void "
                   (1 . "Foo")
                   "TestMethod("
                   (2 . "Type")
                   " param1, "
                   (2 . "Type")
                   " param2)")))
  (should (equal (aya--parse "public void ~FooTestMethod(`Type' param1, `Type' param2)")
                 '("public void "
                   (1 . "FooTestMethod")
                   "("
                   (2 . "Type")
                   " param1, "
                   (2 . "Type")
                   " param2)"))))
(ert-deftest aya--maybe-append-newline ()
  (should (equal (let ((aya-create-with-newline t))
                   (aya--maybe-append-newline "snippet"))
                 "snippet\n"))
  (should (equal (let ((aya-create-with-newline nil))
                   (aya--maybe-append-newline "snippet"))
                 "snippet"))
  (should (equal (let ((aya-create-with-newline t))
                   (aya--maybe-append-newline "snippet\n"))
                 "snippet\n"))
  (should (equal (let ((aya-create-with-newline nil))
                   (aya--maybe-append-newline "snippet\n"))
                 "snippet\n")))
