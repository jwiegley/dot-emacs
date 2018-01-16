(require 'f)

(defvar ht-test/test-path
  (f-parent (f-this-file)))

(defvar ht-test/root-path
  (f-parent ht-test/test-path))

(require 'ert)
(require 'ht (f-expand "ht" ht-test/root-path))
