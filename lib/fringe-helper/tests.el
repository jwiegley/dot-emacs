(require 'ert)
(require 'fringe-helper)

(ert-deftest fringe-helper-convert-test ()
  (should (equal [0 15 240 255]
                 (fringe-helper-convert "........" "....XXXX"
                                        "XXXX...." "XXXXXXXX"))))
