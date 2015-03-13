(require 'f)

(defvar prodigy-test/test-path
  (f-parent (f-this-file)))

(defvar prodigy-test/root-path
  (f-parent prodigy-test/test-path))

(require 'ert)
(require 'prodigy (f-expand "prodigy" prodigy-test/root-path))
