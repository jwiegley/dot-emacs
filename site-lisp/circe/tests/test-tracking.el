;;; Automated tests for tracking.el

(require 'tracking)

(describe "The `tracking-shorten' function"
  (it "should retain text properties"
    (expect (text-properties-at
             0
             (car (tracking-shorten
                   (list (propertize (buffer-name) 'face 'foo)))))
            :to-equal '(face foo))))
