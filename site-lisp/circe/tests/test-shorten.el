;; -*-lexical-binding: t-*-

(require 'shorten)

(describe "The `shorten-one' function"
  (it "should shorten to a single character"
    (expect (let ((lst (list "foo" "bar" "baz" "quux")))
              (shorten-one (car lst) lst))
            :to-equal "f"))

  (it "should shorten to two characters"
    (expect (let ((lst (list "foo" "fig")))
              (shorten-one (car lst) lst))
            :to-equal "fo"))

  (it "should shorten to three characters"
    (expect (let ((lst (list "foo" "fig" "foot")))
              (shorten-one (car lst) lst))
            :to-equal "foo"))

  (it "should support a component validation function"
    (expect (let ((shorten-validate-component-function
                   (lambda (x) (> (length x) 1)))
                  (lst (list "foo" "bar" "baz" "quux")))
              (shorten-one (car lst) lst))
            :to-equal "fo")))

(describe "The `shorten-make-tree' function"
  ;; This is a terrible description.
  (it "should make trees"
    (expect (shorten-make-tree (list "foo"))
            :to-equal '(("foo" nil "foo" nil)))
    (expect  (let ((shorten-split-function
                    (lambda (s) (split-string s "-"))))
               (shorten-make-tree (list "foo" "bar")))
             :to-equal '(("bar" nil "bar" nil)
                         ("foo" nil "foo" nil)))
    (expect (let ((shorten-split-function
                   (lambda (s) (split-string s "-"))))
              (shorten-make-tree (list "foo" "foo-bar")))
            :to-equal '(("foo" nil "foo"
                         ("bar" nil "foo-bar" nil))))
    (expect (shorten-make-tree (list))
            :to-equal nil)
    (expect (shorten-make-tree (list "foo-bar" "foo"))
            :to-equal '(("foo" nil "foo"
                         ("-" nil nil
                          ("bar" nil "foo-bar" nil)))))))

(describe "The `shorten-walk' function"
  (it "should return the empty list for a an empty tree"
    (expect (shorten-walk '())
            :to-equal nil))
  (it "should return an alist for a single word"
    (expect (shorten-walk '(("foo" nil "foo" nil)))
            :to-equal '(("foo" . "f")))))

(describe "The `shorten-strings' function"
  ;; Another terrible name.
  (it "should work"
    (expect (shorten-strings (list))
            :to-equal nil)
    (expect (shorten-strings (list "foo"))
            :to-equal '(("foo" . "f")))
    (expect (shorten-strings (list "foo" "bar"))
            :to-equal '(("foo" . "f") ("bar" . "b")))
    (expect (shorten-strings (list "foo" "foo-bar"))
            :to-equal '(("foo-bar" . "f-b") ("foo" . "f")))
    (expect (shorten-strings (list "fo" "f"))
            :to-equal '(("fo" . "fo") ("f" . "f")))
    (expect (shorten-strings (list "foo-foo" "foo-bar" "foo-baz" "foo-quux"
                                   "bar-foo" "bar-bar" "bar-baz" "bar-quux"))
            :to-equal '(("foo-foo" . "f-f")
                        ("foo-bar" . "f-bar")
                        ("foo-baz" . "f-baz")
                        ("foo-quux" . "f-q")
                        ("bar-foo" . "b-f")
                        ("bar-bar" . "b-bar")
                        ("bar-baz" . "b-baz")
                        ("bar-quux" . "b-q")))))

(defun shorten-tests-tail-count-join-function (lst tail-count)
  (concat (shorten-join lst)
          "{" (number-to-string tail-count) "}"))

(describe "The `shorten-strings-tail-count' function"
  ;; More terrible names
  (it "should work"
    (let ((shorten-join-function #'shorten-tests-tail-count-join-function))
      (expect (shorten-strings (list "foo" "foo-bar"))
              :to-equal `(("foo-bar" . "f-b{1}")
                          ("foo" . "f{0}")))
      (expect (shorten-strings (list "foo" "foo-bar" "foo-bar-baz"))
              :to-equal `(("foo-bar-baz" . "f-b-b{1}")
                          ("foo-bar" . "f-b{0}")
                          ("foo" . "f{0}"))))))
