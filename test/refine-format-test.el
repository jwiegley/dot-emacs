(require 'ert)
(require 'refine)

(defvar x nil)

(ert-deftest refine-format-symbol ()
  (should (equal (refine--pretty-format 'x) "'x")))

(ert-deftest refine-format-builtin-symbol ()
  (should (equal (refine--pretty-format nil) "nil"))
  (should (equal (refine--pretty-format t) "t")))

(ert-deftest refine-format-colon-symbol ()
  (should (equal (refine--pretty-format :x) ":x")))

(ert-deftest refine-format-value-empty-list ()
  "We should show a sensible value for an empty list."
  (should
   (equal-including-properties
    (refine--format-with-index nil)
    (propertize "nil" 'refine-index 'empty))))

(ert-deftest refine-format-value-t ()
  "We should be able to show 't."
  (should
   (equal (refine--format-with-index t) "t")))

(ert-deftest refine-format-value-symbols ()
  "We should be able to format arbitrary symbols."
  (should
   (equal-including-properties
    (refine--format-with-index 'foo)
    (propertize "'foo" 'refine-index 'scalar))))

(ert-deftest refine-format-value-numbers ()
  "We should be able to format arbitrary numbers."
  (should
   (equal-including-properties
    (refine--format-with-index 1)
    (propertize "1" 'refine-index 'scalar))))

(ert-deftest refine-format-value-string ()
  "Refine isn't very useful for strings, but we should show
something sensible."
  (should
   (equal-including-properties
    (refine--format-with-index "foo")
    (propertize "\"foo\"" 'refine-index 'scalar))))

(ert-deftest refine-format-string ()
  (should (equal (refine--pretty-format "abc\"def") "\"abc\\\"def\"")))

(ert-deftest refine-format-multiline-string ()
  "When formatting multiline strings, we should indent subsequent lines.
This ensures that vertical text lines up (the \" adds an offset)."
  (should (equal (refine--pretty-format "abc\ndef") "\"abc\n def\"")))

(ert-deftest refine-format-dotted-list ()
  (should (equal (refine--pretty-format (cons 1 2)) "'(1 . 2)")))

(ert-deftest refine-describe-dotted-list ()
  (should (equal (refine--describe 'x (cons 1 2) nil)
                 "x is a global variable. Its current value is a pair:")))

(ert-deftest refine-describe-nil ()
  (should (equal (refine--describe 'x nil nil)
                 "x is a global variable. Its current value is nil:")))

(ert-deftest refine-describe-t ()
  (should (equal (refine--describe 'x t nil)
                 "x is a global variable. Its current value is a symbol:")))

(ert-deftest refine-describe-number ()
  (should (equal (refine--describe 'x 1 nil)
                 "x is a global variable. Its current value is a number:")))

(ert-deftest refine-describe-single-element-list ()
  (should
   (equal (refine--describe 'x (list 'foo) nil)
          "x is a global variable. Its current value is a list containing 1
value:")))
